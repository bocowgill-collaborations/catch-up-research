/*
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
*/

#include <algorithm>
#include <array>
#include <bit>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <limits>
#include <optional>
#include <random>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#include <utility>
#include <vector>

#include <sys/resource.h>

namespace catch_up_search {

constexpr std::uint32_t kFormatVersion = 1;
constexpr std::array<char, 8> kMagic = {'C', 'A', 'T', 'C', 'H', 'U', 'P', '1'};
constexpr const char* kSoftwareVersion = "catch-up-exact/1";

enum class Outcome : std::int8_t { loss = -1, draw = 0, win = 1 };

const char* outcomeName(Outcome outcome) {
  switch (outcome) {
    case Outcome::loss:
      return "loss";
    case Outcome::draw:
      return "draw";
    case Outcome::win:
      return "win";
  }
  throw std::logic_error("invalid outcome");
}

char outcomeLetter(Outcome outcome) {
  switch (outcome) {
    case Outcome::loss:
      return 'L';
    case Outcome::draw:
      return 'D';
    case Outcome::win:
      return 'W';
  }
  throw std::logic_error("invalid outcome");
}

Outcome negate(Outcome outcome) {
  return static_cast<Outcome>(-static_cast<std::int8_t>(outcome));
}

Outcome best(Outcome left, Outcome right) {
  return static_cast<std::int8_t>(left) < static_cast<std::int8_t>(right) ? right : left;
}

std::uint64_t triangular(unsigned gameSize) {
  return static_cast<std::uint64_t>(gameSize) * (gameSize + 1) / 2;
}

std::uint64_t maskCount(unsigned gameSize) {
  if (gameSize > 32) {
    throw std::invalid_argument("game size must be at most 32");
  }
  return std::uint64_t{1} << gameSize;
}

std::uint32_t fullMask(unsigned gameSize) {
  return static_cast<std::uint32_t>(maskCount(gameSize) - 1);
}

unsigned counterForBit(std::uint32_t bit) {
  return std::countr_zero(bit) + 1;
}

std::uint64_t maxResidentBytes() {
  rusage usage{};
  if (getrusage(RUSAGE_SELF, &usage) != 0) {
    return 0;
  }
#if defined(__APPLE__)
  return static_cast<std::uint64_t>(usage.ru_maxrss);
#else
  return static_cast<std::uint64_t>(usage.ru_maxrss) * 1024;
#endif
}

double mebibytes(std::uint64_t bytes) {
  return static_cast<double>(bytes) / (1024.0 * 1024.0);
}

class MaskData {
 public:
  explicit MaskData(unsigned gameSize)
      : gameSize_(gameSize), sums_(maskCount(gameSize), 0) {
    for (std::uint64_t wideMask = 1; wideMask < sums_.size(); ++wideMask) {
      const auto mask = static_cast<std::uint32_t>(wideMask);
      const std::uint32_t bit = mask & (0U - mask);
      const std::uint32_t rest = mask ^ bit;
      const std::uint64_t sum = static_cast<std::uint64_t>(sums_[rest]) + counterForBit(bit);
      if (sum > std::numeric_limits<std::uint16_t>::max()) {
        throw std::overflow_error("mask sum does not fit the checked storage type");
      }
      sums_[mask] = static_cast<std::uint16_t>(sum);
    }
  }

  unsigned gameSize() const { return gameSize_; }
  std::uint16_t sum(std::uint32_t mask) const { return sums_.at(mask); }
  const std::vector<std::uint16_t>& sums() const { return sums_; }

 private:
  unsigned gameSize_;
  std::vector<std::uint16_t> sums_;
};

// A transparent semantic oracle. Its state keeps both absolute scores and the special-opening flag.
class AbsoluteAtomicSolver {
 public:
  explicit AbsoluteAtomicSolver(unsigned gameSize) : masks_(gameSize) {}

  Outcome gameValue() {
    return value(fullMask(masks_.gameSize()), 0, 0, true);
  }

  Outcome value(std::uint32_t remaining, std::uint16_t currentScore,
                std::uint16_t opponentScore, bool firstMove) {
    const std::uint64_t key = packKey(remaining, currentScore, opponentScore, firstMove);
    if (const auto found = cache_.find(key); found != cache_.end()) {
      ++cacheHits_;
      return found->second;
    }
    ++states_;
    Outcome result = Outcome::loss;
    if (remaining == 0) {
      result = currentScore == opponentScore
                   ? Outcome::draw
                   : (currentScore > opponentScore ? Outcome::win : Outcome::loss);
    } else if (static_cast<std::uint64_t>(currentScore) + masks_.sum(remaining) <
               opponentScore) {
      // The mover takes everything, remains strictly behind, and loses.
      result = Outcome::loss;
    } else {
      result = Outcome::loss;
      std::uint32_t moves = remaining;
      while (moves != 0) {
        const std::uint32_t bit = moves & (0U - moves);
        moves ^= bit;
        const unsigned counter = counterForBit(bit);
        const std::uint32_t childMask = remaining ^ bit;
        const std::uint64_t enlarged = static_cast<std::uint64_t>(currentScore) + counter;
        if (enlarged > std::numeric_limits<std::uint16_t>::max()) {
          throw std::overflow_error("score does not fit the checked storage type");
        }
        const auto nextCurrent = static_cast<std::uint16_t>(enlarged);
        const Outcome candidate =
            firstMove || nextCurrent >= opponentScore
                ? negate(value(childMask, opponentScore, nextCurrent, false))
                : value(childMask, nextCurrent, opponentScore, false);
        result = best(result, candidate);
        ++movesConsidered_;
      }
    }
    cache_.emplace(key, result);
    return result;
  }

  std::uint64_t states() const { return states_; }
  std::uint64_t movesConsidered() const { return movesConsidered_; }
  std::uint64_t cacheHits() const { return cacheHits_; }

 private:
  static std::uint64_t packKey(std::uint32_t remaining, std::uint16_t currentScore,
                               std::uint16_t opponentScore, bool firstMove) {
    std::uint64_t key = remaining;
    key = (key << 16) | currentScore;
    key = (key << 16) | opponentScore;
    return (key << 1) | static_cast<unsigned>(firstMove);
  }

  MaskData masks_;
  std::unordered_map<std::uint64_t, Outcome> cache_;
  std::uint64_t states_ = 0;
  std::uint64_t movesConsidered_ = 0;
  std::uint64_t cacheHits_ = 0;
};

struct TurnAction {
  std::uint32_t selected;
  unsigned finalCounter;

  bool operator==(const TurnAction&) const = default;
};

// A logically separate solver whose edges are whole, legally completed turns.
class TurnBoundarySolver {
 public:
  explicit TurnBoundarySolver(unsigned gameSize) : masks_(gameSize) {}

  Outcome gameValue() { return value(fullMask(masks_.gameSize()), 0); }

  Outcome value(std::uint32_t remaining, unsigned deficit) {
    const std::uint64_t key = (static_cast<std::uint64_t>(remaining) << 6) | deficit;
    if (const auto found = cache_.find(key); found != cache_.end()) {
      ++cacheHits_;
      return found->second;
    }
    ++states_;
    Outcome result;
    if (remaining == 0) {
      result = deficit == 0 ? Outcome::draw : Outcome::loss;
    } else if (masks_.sum(remaining) < deficit) {
      result = Outcome::loss;
    } else {
      result = Outcome::loss;
      for (const TurnAction& action : legalActions(remaining, deficit)) {
        const unsigned overshoot = masks_.sum(action.selected) - deficit;
        result = best(result, negate(value(remaining ^ action.selected, overshoot)));
        ++actionsConsidered_;
      }
    }
    cache_.emplace(key, result);
    return result;
  }

  std::vector<TurnAction> legalActions(std::uint32_t remaining, unsigned deficit) const {
    std::vector<TurnAction> result;
    if (remaining == 0 || masks_.sum(remaining) < deficit) {
      return result;
    }
    if (deficit == 0) {
      std::uint32_t moves = remaining;
      while (moves != 0) {
        const std::uint32_t bit = moves & (0U - moves);
        moves ^= bit;
        result.push_back({bit, counterForBit(bit)});
      }
      return result;
    }
    for (std::uint32_t action = remaining; action != 0;
         action = (action - 1) & remaining) {
      const unsigned largest = 32 - std::countl_zero(action);
      const unsigned actionSum = masks_.sum(action);
      // The largest counter is a final-pick witness exactly when this holds.
      if (deficit <= actionSum && actionSum - largest < deficit) {
        result.push_back({action, largest});
      }
    }
    std::sort(result.begin(), result.end(),
              [](const TurnAction& left, const TurnAction& right) {
                return left.selected < right.selected;
              });
    return result;
  }

  const std::unordered_map<std::uint64_t, Outcome>& cache() const { return cache_; }
  const MaskData& masks() const { return masks_; }
  std::uint64_t states() const { return states_; }
  std::uint64_t actionsConsidered() const { return actionsConsidered_; }
  std::uint64_t cacheHits() const { return cacheHits_; }

 private:
  MaskData masks_;
  std::unordered_map<std::uint64_t, Outcome> cache_;
  std::uint64_t states_ = 0;
  std::uint64_t actionsConsidered_ = 0;
  std::uint64_t cacheHits_ = 0;
};

std::vector<std::uint32_t> orderedSequenceActions(std::uint32_t remaining, unsigned deficit,
                                                  const MaskData& masks) {
  std::unordered_set<std::uint32_t> found;
  if (remaining == 0 || masks.sum(remaining) < deficit) {
    return {};
  }
  if (deficit == 0) {
    std::uint32_t moves = remaining;
    while (moves != 0) {
      const std::uint32_t bit = moves & (0U - moves);
      moves ^= bit;
      found.insert(bit);
    }
  } else {
    const auto visit = [&](auto&& self, std::uint32_t available, std::uint32_t selected,
                           unsigned selectedSum) -> void {
      std::uint32_t moves = available;
      while (moves != 0) {
        const std::uint32_t bit = moves & (0U - moves);
        moves ^= bit;
        const unsigned nextSum = selectedSum + counterForBit(bit);
        const std::uint32_t nextSelected = selected | bit;
        if (nextSum >= deficit) {
          found.insert(nextSelected);
        } else {
          self(self, available ^ bit, nextSelected, nextSum);
        }
      }
    };
    visit(visit, remaining, 0, 0);
  }
  std::vector<std::uint32_t> result(found.begin(), found.end());
  std::sort(result.begin(), result.end());
  return result;
}

std::uint32_t reverseBits32(std::uint32_t value) {
  value = ((value >> 1) & 0x55555555U) | ((value & 0x55555555U) << 1);
  value = ((value >> 2) & 0x33333333U) | ((value & 0x33333333U) << 2);
  value = ((value >> 4) & 0x0f0f0f0fU) | ((value & 0x0f0f0f0fU) << 4);
  value = ((value >> 8) & 0x00ff00ffU) | ((value & 0x00ff00ffU) << 8);
  return (value >> 16) | (value << 16);
}

std::uint32_t lowBits(unsigned width) {
  return width == 32 ? std::numeric_limits<std::uint32_t>::max()
                     : ((std::uint32_t{1} << width) - 1);
}

std::uint32_t reverseLow(std::uint32_t value, unsigned width) {
  return reverseBits32(value & lowBits(width)) >> (32 - width);
}

std::uint64_t reverseBits64(std::uint64_t value) {
  value = ((value >> 1) & 0x5555555555555555ULL) |
          ((value & 0x5555555555555555ULL) << 1);
  value = ((value >> 2) & 0x3333333333333333ULL) |
          ((value & 0x3333333333333333ULL) << 2);
  value = ((value >> 4) & 0x0f0f0f0f0f0f0f0fULL) |
          ((value & 0x0f0f0f0f0f0f0f0fULL) << 4);
  value = ((value >> 8) & 0x00ff00ff00ff00ffULL) |
          ((value & 0x00ff00ff00ff00ffULL) << 8);
  value = ((value >> 16) & 0x0000ffff0000ffffULL) |
          ((value & 0x0000ffff0000ffffULL) << 16);
  return (value >> 32) | (value << 32);
}

std::uint64_t lowBits64(unsigned width) {
  return width == 64 ? std::numeric_limits<std::uint64_t>::max()
                     : ((std::uint64_t{1} << width) - 1);
}

std::uint64_t reverseLow64(std::uint64_t value, unsigned width) {
  return reverseBits64(value & lowBits64(width)) >> (64 - width);
}

struct ExactStats {
  std::uint64_t states = 0;
  std::uint64_t moves = 0;
  double elapsedSeconds = 0;
  double peakMemoryMiB = 0;
};

// Exact bottom-up recurrence. Each bit of winBits[mask] or drawBits[mask] is one deficit.
class PackedExactTable {
 public:
  explicit PackedExactTable(unsigned gameSize)
      : PackedExactTable(gameSize, checkedPackedCount(gameSize)) {}

  void solve() {
    const auto started = std::chrono::steady_clock::now();
    const std::uint32_t deficits = lowBits(gameSize_ + 1);
    drawBits_[0] = 1;
    stats_.states = gameSize_ + 1;
    for (std::uint32_t mask = 1; mask < winBits_.size(); ++mask) {
      std::uint32_t anyWin = 0;
      std::uint32_t anyDraw = 0;
      std::uint32_t moves = mask;
      while (moves != 0) {
        const std::uint32_t bit = moves & (0U - moves);
        moves ^= bit;
        const unsigned counter = counterForBit(bit);
        const std::uint32_t child = mask ^ bit;
        const std::uint32_t childWin = winBits_[child];
        const std::uint32_t childDraw = drawBits_[child];
        const std::uint32_t childLoss = deficits & ~(childWin | childDraw);
        // d <= counter: the turn ends, so reflect deficit counter-d and negate.
        // d > counter: the same mover continues at deficit d-counter.
        const std::uint32_t candidateWin =
            reverseLow(childLoss, counter + 1) | ((childWin & ~1U) << counter);
        const std::uint32_t candidateDraw =
            reverseLow(childDraw, counter + 1) | ((childDraw & ~1U) << counter);
        anyWin |= candidateWin;
        anyDraw |= candidateDraw;
      }
      const unsigned activeTop = std::min<unsigned>(gameSize_, masks_.sum(mask));
      const std::uint32_t active = lowBits(activeTop + 1);
      winBits_[mask] = anyWin & active;
      drawBits_[mask] = ~anyWin & anyDraw & active;
      stats_.states += gameSize_ + 1;
      stats_.moves += static_cast<std::uint64_t>(std::popcount(mask)) * (activeTop + 1);
    }
    stats_.elapsedSeconds = std::chrono::duration<double>(
                                      std::chrono::steady_clock::now() - started)
                                      .count();
    stats_.peakMemoryMiB = mebibytes(maxResidentBytes());
  }

  Outcome outcome(std::uint32_t mask, unsigned deficit) const {
    if (deficit > gameSize_) {
      if (mask == 0 && deficit == 0) {
        return Outcome::draw;
      }
      return Outcome::loss;
    }
    const std::uint32_t bit = std::uint32_t{1} << deficit;
    if ((winBits_.at(mask) & bit) != 0) {
      return Outcome::win;
    }
    if ((drawBits_.at(mask) & bit) != 0) {
      return Outcome::draw;
    }
    return Outcome::loss;
  }

  Outcome gameValue() const { return outcome(fullMask(gameSize_), 0); }

  std::vector<std::pair<unsigned, Outcome>> openingValues() const {
    std::vector<std::pair<unsigned, Outcome>> result;
    const std::uint32_t initial = fullMask(gameSize_);
    for (unsigned opening = 1; opening <= gameSize_; ++opening) {
      const std::uint32_t bit = std::uint32_t{1} << (opening - 1);
      result.emplace_back(opening, negate(outcome(initial ^ bit, opening)));
    }
    return result;
  }

  bool verifyScalar(unsigned requestedThreads, double* elapsedSeconds = nullptr) const {
    const auto started = std::chrono::steady_clock::now();
    const unsigned threadCount = std::max(1U, requestedThreads);
    const std::uint64_t maskCount = winBits_.size();
    std::vector<std::thread> threads;
    std::vector<std::optional<std::string>> errors(threadCount);
    const auto worker = [&](unsigned threadIndex) {
      const std::uint64_t begin = maskCount * threadIndex / threadCount;
      const std::uint64_t end = maskCount * (threadIndex + 1) / threadCount;
      for (std::uint64_t wideMask = begin; wideMask < end; ++wideMask) {
        const auto mask = static_cast<std::uint32_t>(wideMask);
        for (unsigned deficit = 0; deficit <= gameSize_; ++deficit) {
          Outcome expected;
          if (mask == 0) {
            expected = deficit == 0 ? Outcome::draw : Outcome::loss;
          } else if (masks_.sum(mask) < deficit) {
            expected = Outcome::loss;
          } else {
            expected = Outcome::loss;
            std::uint32_t moves = mask;
            while (moves != 0) {
              const std::uint32_t bit = moves & (0U - moves);
              moves ^= bit;
              const unsigned counter = counterForBit(bit);
              const unsigned childDeficit =
                  counter < deficit ? deficit - counter : counter - deficit;
              Outcome candidate = outcome(mask ^ bit, childDeficit);
              if (deficit <= counter) {
                candidate = negate(candidate);
              }
              expected = best(expected, candidate);
            }
          }
          const Outcome actual = outcome(mask, deficit);
          if (expected != actual) {
            std::ostringstream message;
            message << "scalar verification failed at mask=" << mask
                    << ", deficit=" << deficit << ": expected " << outcomeName(expected)
                    << ", found " << outcomeName(actual);
            errors[threadIndex] = message.str();
            return;
          }
        }
      }
    };
    for (unsigned index = 0; index < threadCount; ++index) {
      threads.emplace_back(worker, index);
    }
    for (auto& thread : threads) {
      thread.join();
    }
    if (elapsedSeconds != nullptr) {
      *elapsedSeconds =
          std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count();
    }
    for (const auto& error : errors) {
      if (error.has_value()) {
        std::cerr << *error << '\n';
        return false;
      }
    }
    return true;
  }

  void save(const std::string& path) const {
    std::ofstream output(path, std::ios::binary | std::ios::trunc);
    if (!output) {
      throw std::runtime_error("cannot open exact-table output: " + path);
    }
    output.write(kMagic.data(), kMagic.size());
    write32(output, kFormatVersion);
    write32(output, gameSize_);
    write64(output, winBits_.size());
    for (std::uint32_t value : winBits_) {
      write32(output, value);
    }
    for (std::uint32_t value : drawBits_) {
      write32(output, value);
    }
    if (!output) {
      throw std::runtime_error("failed while writing exact table: " + path);
    }
  }

  static PackedExactTable load(const std::string& path) {
    std::ifstream input(path, std::ios::binary);
    if (!input) {
      throw std::runtime_error("cannot open exact table: " + path);
    }
    std::array<char, 8> magic{};
    input.read(magic.data(), magic.size());
    if (magic != kMagic) {
      throw std::runtime_error("exact table has the wrong magic bytes");
    }
    const std::uint32_t version = read32(input);
    if (version != kFormatVersion) {
      throw std::runtime_error("unsupported exact-table version");
    }
    const unsigned gameSize = read32(input);
    PackedExactTable table(gameSize);
    const std::uint64_t count = read64(input);
    if (count != table.winBits_.size()) {
      throw std::runtime_error("exact table has the wrong mask count");
    }
    for (auto& value : table.winBits_) {
      value = read32(input);
    }
    for (auto& value : table.drawBits_) {
      value = read32(input);
    }
    if (input.peek() != std::char_traits<char>::eof()) {
      throw std::runtime_error("exact table has trailing bytes");
    }
    return table;
  }

  unsigned gameSize() const { return gameSize_; }
  const ExactStats& stats() const { return stats_; }

 private:
  PackedExactTable(unsigned gameSize, std::uint64_t count)
      : gameSize_(gameSize), masks_(gameSize), winBits_(count, 0), drawBits_(count, 0) {}

  static std::uint64_t checkedPackedCount(unsigned gameSize) {
    if (gameSize > 31) {
      throw std::invalid_argument("32-bit packed tables support game sizes at most 31");
    }
    return maskCount(gameSize);
  }

  static void write32(std::ostream& output, std::uint32_t value) {
    for (unsigned shift = 0; shift < 32; shift += 8) {
      output.put(static_cast<char>((value >> shift) & 0xff));
    }
  }

  static void write64(std::ostream& output, std::uint64_t value) {
    for (unsigned shift = 0; shift < 64; shift += 8) {
      output.put(static_cast<char>((value >> shift) & 0xff));
    }
  }

  static std::uint32_t read32(std::istream& input) {
    std::uint32_t value = 0;
    for (unsigned shift = 0; shift < 32; shift += 8) {
      const int byte = input.get();
      if (byte == std::char_traits<char>::eof()) {
        throw std::runtime_error("truncated exact table");
      }
      value |= static_cast<std::uint32_t>(byte) << shift;
    }
    return value;
  }

  static std::uint64_t read64(std::istream& input) {
    std::uint64_t value = 0;
    for (unsigned shift = 0; shift < 64; shift += 8) {
      const int byte = input.get();
      if (byte == std::char_traits<char>::eof()) {
        throw std::runtime_error("truncated exact table");
      }
      value |= static_cast<std::uint64_t>(byte) << shift;
    }
    return value;
  }

  unsigned gameSize_;
  MaskData masks_;
  std::vector<std::uint32_t> winBits_;
  std::vector<std::uint32_t> drawBits_;
  ExactStats stats_;
};

// The N=32 frontier needs 33 deficit bits, so it uses a separate 64-bit table representation.
class WideExactTable {
 public:
  WideExactTable()
      : masks_(kGameSize), winBits_(maskCount(kGameSize), 0),
        drawBits_(maskCount(kGameSize), 0) {}

  void solve() {
    const auto started = std::chrono::steady_clock::now();
    const std::uint64_t deficits = lowBits64(kGameSize + 1);
    drawBits_[0] = 1;
    stats_.states = kGameSize + 1;
    for (std::uint64_t wideMask = 1; wideMask < winBits_.size(); ++wideMask) {
      const auto mask = static_cast<std::uint32_t>(wideMask);
      std::uint64_t anyWin = 0;
      std::uint64_t anyDraw = 0;
      std::uint32_t moves = mask;
      while (moves != 0) {
        const std::uint32_t bit = moves & (0U - moves);
        moves ^= bit;
        const unsigned counter = counterForBit(bit);
        const std::uint32_t child = mask ^ bit;
        const std::uint64_t childWin = winBits_[child];
        const std::uint64_t childDraw = drawBits_[child];
        const std::uint64_t childLoss = deficits & ~(childWin | childDraw);
        const std::uint64_t candidateWin =
            reverseLow64(childLoss, counter + 1) | ((childWin & ~1ULL) << counter);
        const std::uint64_t candidateDraw =
            reverseLow64(childDraw, counter + 1) | ((childDraw & ~1ULL) << counter);
        anyWin |= candidateWin;
        anyDraw |= candidateDraw;
      }
      const unsigned activeTop = std::min<unsigned>(kGameSize, masks_.sum(mask));
      const std::uint64_t active = lowBits64(activeTop + 1);
      winBits_[mask] = anyWin & active;
      drawBits_[mask] = ~anyWin & anyDraw & active;
      stats_.states += kGameSize + 1;
      stats_.moves += static_cast<std::uint64_t>(std::popcount(mask)) * (activeTop + 1);
    }
    stats_.elapsedSeconds = std::chrono::duration<double>(
                                      std::chrono::steady_clock::now() - started)
                                      .count();
    stats_.peakMemoryMiB = mebibytes(maxResidentBytes());
  }

  Outcome outcome(std::uint32_t mask, unsigned deficit) const {
    if (deficit > kGameSize) {
      return Outcome::loss;
    }
    const std::uint64_t bit = std::uint64_t{1} << deficit;
    if ((winBits_.at(mask) & bit) != 0) {
      return Outcome::win;
    }
    if ((drawBits_.at(mask) & bit) != 0) {
      return Outcome::draw;
    }
    return Outcome::loss;
  }

  Outcome gameValue() const { return outcome(fullMask(kGameSize), 0); }

  std::vector<std::pair<unsigned, Outcome>> openingValues() const {
    std::vector<std::pair<unsigned, Outcome>> result;
    const std::uint32_t initial = fullMask(kGameSize);
    for (unsigned opening = 1; opening <= kGameSize; ++opening) {
      const std::uint32_t bit = std::uint32_t{1} << (opening - 1);
      result.emplace_back(opening, negate(outcome(initial ^ bit, opening)));
    }
    return result;
  }

  bool verifyScalar(unsigned requestedThreads, double* elapsedSeconds = nullptr) const {
    const auto started = std::chrono::steady_clock::now();
    const unsigned threadCount = std::max(1U, requestedThreads);
    const std::uint64_t count = maskCount(kGameSize);
    std::vector<std::thread> threads;
    std::vector<std::optional<std::string>> errors(threadCount);
    const auto worker = [&](unsigned threadIndex) {
      const std::uint64_t begin = count * threadIndex / threadCount;
      const std::uint64_t end = count * (threadIndex + 1) / threadCount;
      for (std::uint64_t wideMask = begin; wideMask < end; ++wideMask) {
        const auto mask = static_cast<std::uint32_t>(wideMask);
        for (unsigned deficit = 0; deficit <= kGameSize; ++deficit) {
          Outcome expected;
          if (mask == 0) {
            expected = deficit == 0 ? Outcome::draw : Outcome::loss;
          } else if (masks_.sum(mask) < deficit) {
            expected = Outcome::loss;
          } else {
            expected = Outcome::loss;
            std::uint32_t moves = mask;
            while (moves != 0) {
              const std::uint32_t bit = moves & (0U - moves);
              moves ^= bit;
              const unsigned counter = counterForBit(bit);
              const unsigned childDeficit =
                  counter < deficit ? deficit - counter : counter - deficit;
              Outcome candidate = outcome(mask ^ bit, childDeficit);
              if (deficit <= counter) {
                candidate = negate(candidate);
              }
              expected = best(expected, candidate);
            }
          }
          const Outcome actual = outcome(mask, deficit);
          if (expected != actual) {
            std::ostringstream message;
            message << "wide scalar verification failed at mask=" << mask
                    << ", deficit=" << deficit << ": expected " << outcomeName(expected)
                    << ", found " << outcomeName(actual);
            errors[threadIndex] = message.str();
            return;
          }
        }
      }
    };
    for (unsigned index = 0; index < threadCount; ++index) {
      threads.emplace_back(worker, index);
    }
    for (auto& thread : threads) {
      thread.join();
    }
    if (elapsedSeconds != nullptr) {
      *elapsedSeconds =
          std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count();
    }
    for (const auto& error : errors) {
      if (error.has_value()) {
        std::cerr << *error << '\n';
        return false;
      }
    }
    return true;
  }

  unsigned gameSize() const { return kGameSize; }
  const ExactStats& stats() const { return stats_; }

 private:
  static constexpr unsigned kGameSize = 32;
  MaskData masks_;
  std::vector<std::uint64_t> winBits_;
  std::vector<std::uint64_t> drawBits_;
  ExactStats stats_;
};

struct MonteCarloState {
  std::uint64_t remaining;
  unsigned deficit;
};

struct MonteCarloEdge {
  unsigned counter;
  std::uint32_t child;
  int perspectiveSign;
};

struct MonteCarloNode {
  MonteCarloState state;
  std::uint64_t unexpanded;
  std::vector<MonteCarloEdge> edges;
  std::uint64_t visits = 0;
  double valueSum = 0;
};

class MonteCarloSearch {
 public:
  MonteCarloSearch(unsigned gameSize, std::uint64_t seed)
      : gameSize_(gameSize), random_(seed) {
    if (gameSize == 0 || gameSize > 57) {
      throw std::invalid_argument("MCTS game size must be between 1 and 57");
    }
    root_ = ensureNode({(std::uint64_t{1} << gameSize) - 1, 0});
  }

  void run(std::uint64_t simulations) {
    const auto started = std::chrono::steady_clock::now();
    std::vector<std::uint32_t> pathNodes;
    std::vector<int> pathSigns;
    pathNodes.reserve(gameSize_ + 1);
    pathSigns.reserve(gameSize_);
    for (std::uint64_t simulation = 0; simulation < simulations; ++simulation) {
      pathNodes.clear();
      pathSigns.clear();
      std::uint32_t nodeIndex = root_;
      pathNodes.push_back(nodeIndex);
      double reward = 0;
      while (true) {
        const MonteCarloState state = nodes_[nodeIndex].state;
        if (const auto terminal = terminalReward(state); terminal.has_value()) {
          reward = *terminal;
          break;
        }
        if (nodes_[nodeIndex].unexpanded != 0) {
          const std::uint64_t bit = randomBit(nodes_[nodeIndex].unexpanded);
          nodes_[nodeIndex].unexpanded ^= bit;
          const unsigned counter = std::countr_zero(bit) + 1;
          const bool continues = counter < state.deficit;
          const MonteCarloState childState{
              state.remaining ^ bit,
              continues ? state.deficit - counter : counter - state.deficit};
          const std::uint32_t child = ensureNode(childState);
          const int sign = continues ? 1 : -1;
          nodes_[nodeIndex].edges.push_back({counter, child, sign});
          pathSigns.push_back(sign);
          pathNodes.push_back(child);
          reward = rollout(childState);
          break;
        }
        const MonteCarloEdge edge = selectEdge(nodeIndex);
        pathSigns.push_back(edge.perspectiveSign);
        nodeIndex = edge.child;
        pathNodes.push_back(nodeIndex);
      }
      for (std::size_t offset = pathNodes.size(); offset > 0; --offset) {
        MonteCarloNode& node = nodes_[pathNodes[offset - 1]];
        ++node.visits;
        node.valueSum += reward;
        if (offset > 1) {
          reward *= pathSigns[offset - 2];
        }
      }
    }
    elapsedSeconds_ += std::chrono::duration<double>(
                           std::chrono::steady_clock::now() - started)
                           .count();
  }

  void report(std::uint64_t simulations, std::uint64_t seed,
              const std::string& command) const {
    const MonteCarloNode& root = nodes_[root_];
    std::vector<MonteCarloEdge> openings = root.edges;
    std::sort(openings.begin(), openings.end(),
              [](const MonteCarloEdge& left, const MonteCarloEdge& right) {
                return left.counter < right.counter;
              });
    std::cout << "software=" << kSoftwareVersion << '\n';
    std::cout << "command=" << command << '\n';
    std::cout << "N=" << gameSize_ << '\n';
    std::cout << "status=heuristic_mcts\n";
    std::cout << "simulations=" << simulations << '\n';
    std::cout << "seed=" << seed << '\n';
    std::cout << "nodes=" << nodes_.size() << '\n';
    std::cout << "elapsed_seconds=" << std::fixed << std::setprecision(6)
              << elapsedSeconds_ << '\n';
    std::cout << "root_empirical_mean=" << std::setprecision(8)
              << (root.visits == 0 ? 0 : root.valueSum / root.visits) << '\n';
    std::cout << "opening_estimates=";
    for (std::size_t index = 0; index < openings.size(); ++index) {
      const MonteCarloEdge& edge = openings[index];
      const MonteCarloNode& child = nodes_[edge.child];
      const double parentMean = child.visits == 0
                                    ? 0
                                    : edge.perspectiveSign * child.valueSum / child.visits;
      std::cout << (index == 0 ? "" : ",") << edge.counter << ':' << child.visits << ':'
                << std::setprecision(6) << parentMean;
    }
    std::cout << '\n';
    std::cout << "warning=MCTS estimates are not game values or certificates\n";
  }

 private:
  std::uint64_t key(MonteCarloState state) const {
    return (state.remaining << 6) | state.deficit;
  }

  std::uint32_t ensureNode(MonteCarloState state) {
    const std::uint64_t stateKey = key(state);
    if (const auto found = index_.find(stateKey); found != index_.end()) {
      return found->second;
    }
    if (nodes_.size() == std::numeric_limits<std::uint32_t>::max()) {
      throw std::overflow_error("MCTS node index exhausted");
    }
    const auto newIndex = static_cast<std::uint32_t>(nodes_.size());
    nodes_.push_back({state, state.remaining, {}, 0, 0});
    index_.emplace(stateKey, newIndex);
    return newIndex;
  }

  unsigned remainingSum(std::uint64_t mask) const {
    unsigned sum = 0;
    while (mask != 0) {
      const std::uint64_t bit = mask & (0ULL - mask);
      mask ^= bit;
      sum += std::countr_zero(bit) + 1;
    }
    return sum;
  }

  std::optional<double> terminalReward(MonteCarloState state) const {
    if (state.remaining == 0) {
      return state.deficit == 0 ? 0.0 : -1.0;
    }
    if (remainingSum(state.remaining) < state.deficit) {
      return -1.0;
    }
    return std::nullopt;
  }

  std::uint64_t randomBit(std::uint64_t mask) {
    unsigned choice = random_() % std::popcount(mask);
    while (choice != 0) {
      mask &= mask - 1;
      --choice;
    }
    return mask & (0ULL - mask);
  }

  double rollout(MonteCarloState state) {
    int rootSign = 1;
    while (true) {
      if (const auto terminal = terminalReward(state); terminal.has_value()) {
        return rootSign * *terminal;
      }
      const std::uint64_t bit = randomBit(state.remaining);
      const unsigned counter = std::countr_zero(bit) + 1;
      state.remaining ^= bit;
      if (counter < state.deficit) {
        state.deficit -= counter;
      } else {
        state.deficit = counter - state.deficit;
        rootSign = -rootSign;
      }
    }
  }

  MonteCarloEdge selectEdge(std::uint32_t nodeIndex) const {
    const MonteCarloNode& node = nodes_[nodeIndex];
    const double logarithm = std::log(static_cast<double>(std::max<std::uint64_t>(1, node.visits)));
    double bestScore = -std::numeric_limits<double>::infinity();
    const MonteCarloEdge* selected = nullptr;
    for (const MonteCarloEdge& edge : node.edges) {
      const MonteCarloNode& child = nodes_[edge.child];
      const double exploitation =
          edge.perspectiveSign * child.valueSum / static_cast<double>(child.visits);
      const double exploration =
          1.4142135623730951 * std::sqrt(logarithm / static_cast<double>(child.visits));
      const double score = exploitation + exploration;
      if (selected == nullptr || bestScore < score) {
        bestScore = score;
        selected = &edge;
      }
    }
    if (selected == nullptr) {
      throw std::logic_error("MCTS selection reached a node with no edge");
    }
    return *selected;
  }

  unsigned gameSize_;
  std::mt19937_64 random_;
  std::unordered_map<std::uint64_t, std::uint32_t> index_;
  std::vector<MonteCarloNode> nodes_;
  std::uint32_t root_ = 0;
  double elapsedSeconds_ = 0;
};

void require(bool condition, const std::string& message) {
  if (!condition) {
    throw std::runtime_error(message);
  }
}

void testMoveGenerator() {
  constexpr unsigned gameSize = 7;
  TurnBoundarySolver boundary(gameSize);
  const MaskData masks(gameSize);
  for (std::uint32_t remaining = 0; remaining <= fullMask(gameSize); ++remaining) {
    for (unsigned deficit = 0; deficit <= masks.sum(remaining) + 1; ++deficit) {
      const auto actions = boundary.legalActions(remaining, deficit);
      std::vector<std::uint32_t> optimized;
      for (const TurnAction& action : actions) {
        optimized.push_back(action.selected);
        require((action.selected & (std::uint32_t{1} << (action.finalCounter - 1))) != 0,
                "completed-turn witness is absent from its action");
        if (deficit == 0) {
          require(std::popcount(action.selected) == 1,
                  "a tied completed turn must be a singleton");
        } else {
          require(masks.sum(action.selected ^
                            (std::uint32_t{1} << (action.finalCounter - 1))) < deficit &&
                      deficit <= masks.sum(action.selected),
                  "completed-turn final-pick witness is invalid");
        }
      }
      const auto atomic = orderedSequenceActions(remaining, deficit, masks);
      require(optimized == atomic,
              "completed-turn generator disagrees with ordered atomic sequences");
    }
  }
}

void testIndependentSolvers() {
  for (unsigned gameSize = 1; gameSize <= 10; ++gameSize) {
    AbsoluteAtomicSolver atomic(gameSize);
    TurnBoundarySolver boundary(gameSize);
    PackedExactTable packed(gameSize);
    packed.solve();
    require(atomic.gameValue() == boundary.gameValue(),
            "absolute and turn-boundary root solvers disagree at N=" +
                std::to_string(gameSize));
    require(packed.gameValue() == boundary.gameValue(),
            "packed and turn-boundary root solvers disagree at N=" +
                std::to_string(gameSize));
    const std::uint64_t total = triangular(gameSize);
    for (std::uint32_t remaining = 0; remaining <= fullMask(gameSize); ++remaining) {
      const std::uint64_t picked = total - boundary.masks().sum(remaining);
      for (unsigned deficit = 0; deficit <= gameSize; ++deficit) {
        if (picked < deficit || (picked - deficit) % 2 != 0) {
          continue;
        }
        const auto current = static_cast<std::uint16_t>((picked - deficit) / 2);
        const auto opponent = static_cast<std::uint16_t>((picked + deficit) / 2);
        const bool isRoot = remaining == fullMask(gameSize) && deficit == 0;
        const Outcome atomicOutcome = atomic.value(remaining, current, opponent, isRoot);
        const Outcome boundaryOutcome = boundary.value(remaining, deficit);
        require(atomicOutcome == boundaryOutcome,
                "absolute and turn-boundary solvers disagree on a consistent state");
        require(packed.outcome(remaining, deficit) == boundaryOutcome,
                "packed and turn-boundary solvers disagree on a consistent state");
      }
    }
  }
}

void testRandomConsistentStates() {
  constexpr unsigned gameSize = 12;
  const MaskData masks(gameSize);
  AbsoluteAtomicSolver atomic(gameSize);
  TurnBoundarySolver boundary(gameSize);
  std::mt19937_64 random(0x43415443485550ULL);
  unsigned checked = 0;
  while (checked < 40) {
    std::uint32_t remaining = random() & fullMask(gameSize);
    if (std::popcount(remaining) > 9) {
      continue;
    }
    const std::uint64_t picked = triangular(gameSize) - masks.sum(remaining);
    const unsigned deficit = random() % (gameSize + 1);
    if (picked < deficit || (picked - deficit) % 2 != 0) {
      continue;
    }
    const auto current = static_cast<std::uint16_t>((picked - deficit) / 2);
    const auto opponent = static_cast<std::uint16_t>((picked + deficit) / 2);
    require(atomic.value(remaining, current, opponent, false) ==
                boundary.value(remaining, deficit),
            "independent solvers disagree on a random internally consistent state");
    ++checked;
  }
}

void testTerminalAndTransitionCases() {
  AbsoluteAtomicSolver atomic(4);
  TurnBoundarySolver boundary(4);
  require(atomic.value(0, 5, 5, false) == Outcome::draw, "empty tied terminal failed");
  require(atomic.value(0, 4, 5, false) == Outcome::loss, "empty loss terminal failed");
  require(atomic.value(1, 0, 2, false) == Outcome::loss, "take-all terminal failed");
  require(boundary.value(0, 0) == Outcome::draw, "boundary empty draw failed");
  require(boundary.value(0, 1) == Outcome::loss, "boundary empty loss failed");
  require(boundary.value(1, 2) == Outcome::loss, "boundary take-all terminal failed");
  require(boundary.legalActions(1U << 2, 0) ==
              std::vector<TurnAction>{{1U << 2, 3}},
          "tied starts must have singleton turns");
  require(boundary.legalActions((1U << 0) | (1U << 2), 2) ==
              std::vector<TurnAction>({{1U << 2, 3}, {(1U << 0) | (1U << 2), 3}}),
          "exact-catch and overshoot actions failed");
}

void testPackedBitOperations() {
  std::mt19937_64 random(0x5041434b45444249ULL);
  for (unsigned width = 1; width <= 32; ++width) {
    for (unsigned sample = 0; sample < 100; ++sample) {
      const std::uint32_t value = random();
      require(reverseLow64(value, width) == reverseLow(value, width),
              "32-bit and 64-bit packed reversal disagree");
    }
  }
  for (unsigned bit = 0; bit < 33; ++bit) {
    require(reverseLow64(std::uint64_t{1} << bit, 33) ==
                (std::uint64_t{1} << (32 - bit)),
            "33-bit packed reversal failed");
  }
}

const std::array<Outcome, 18> kPublished = {
    Outcome::draw, Outcome::draw, Outcome::win,  Outcome::win,  Outcome::draw,
    Outcome::draw, Outcome::loss, Outcome::loss, Outcome::draw, Outcome::draw,
    Outcome::win,  Outcome::loss, Outcome::draw, Outcome::draw, Outcome::win,
    Outcome::loss, Outcome::draw, Outcome::draw};

void testPublishedRegression() {
  std::cout << "published regression:";
  for (unsigned gameSize = 3; gameSize <= 20; ++gameSize) {
    PackedExactTable table(gameSize);
    table.solve();
    const Outcome actual = table.gameValue();
    require(actual == kPublished[gameSize - 3],
            "published regression failed at N=" + std::to_string(gameSize));
    std::cout << ' ' << gameSize << ':' << outcomeLetter(actual);
    if (gameSize <= 12) {
      TurnBoundarySolver boundary(gameSize);
      require(boundary.gameValue() == actual,
              "turn-boundary solver disagrees with packed solver at N=" +
                  std::to_string(gameSize));
    }
  }
  std::cout << '\n';
}

void runSelfTest() {
  const auto started = std::chrono::steady_clock::now();
  testPackedBitOperations();
  std::cout << "32-bit and 64-bit packed transition primitives: pass\n";
  testTerminalAndTransitionCases();
  std::cout << "terminal, exact-catch, overshoot, tied-start, and take-all tests: pass\n";
  testMoveGenerator();
  std::cout << "completed-turn subsets equal exhaustive ordered sequences through 7 counters: pass\n";
  testIndependentSolvers();
  std::cout << "absolute-score, completed-turn, and packed solvers agree on every internally "
               "consistent state through N=10: pass\n";
  testRandomConsistentStates();
  std::cout << "40 deterministic random internally consistent N=12 states: pass\n";
  testPublishedRegression();
  std::cout << "all self-tests passed in " << std::fixed << std::setprecision(3)
            << std::chrono::duration<double>(std::chrono::steady_clock::now() - started).count()
            << " s\n";
}

unsigned defaultThreadCount() {
  const unsigned detected = std::thread::hardware_concurrency();
  return detected == 0 ? 1 : detected;
}

template <typename Table>
void printExactReport(const Table& table, const std::string& command) {
  const ExactStats& stats = table.stats();
  std::cout << "software=" << kSoftwareVersion << '\n';
  std::cout << "command=" << command << '\n';
  std::cout << "N=" << table.gameSize() << '\n';
  std::cout << "T_N=" << triangular(table.gameSize()) << '\n';
  std::cout << "status=exact\n";
  std::cout << "root_value=" << outcomeName(table.gameValue()) << '\n';
  std::cout << "states_evaluated=" << stats.states << '\n';
  std::cout << "atomic_moves_considered=" << stats.moves << '\n';
  std::cout << "cache_hits=0 (bottom-up table)\n";
  std::cout << "elapsed_seconds=" << std::fixed << std::setprecision(6)
            << stats.elapsedSeconds << '\n';
  std::cout << "peak_memory_mib=" << std::fixed << std::setprecision(3)
            << stats.peakMemoryMiB << '\n';
  std::cout << "opening_values=";
  for (const auto& [opening, outcome] : table.openingValues()) {
    std::cout << (opening == 1 ? "" : ",") << opening << ':' << outcomeLetter(outcome);
  }
  std::cout << '\n';
}

unsigned parseUnsigned(const std::string& text) {
  std::size_t consumed = 0;
  const unsigned long parsed = std::stoul(text, &consumed);
  if (consumed != text.size() || parsed > std::numeric_limits<unsigned>::max()) {
    throw std::invalid_argument("invalid unsigned integer: " + text);
  }
  return static_cast<unsigned>(parsed);
}

std::string commandLine(int argc, char** argv) {
  std::ostringstream result;
  for (int index = 0; index < argc; ++index) {
    if (index != 0) {
      result << ' ';
    }
    result << argv[index];
  }
  return result.str();
}

void usage(const char* executable) {
  std::cerr << "usage:\n"
            << "  " << executable << " --self-test\n"
            << "  " << executable
            << " --solve N [--save TABLE] [--verify] [--threads COUNT]\n"
            << "  " << executable << " --mcts N SIMULATIONS SEED\n"
            << "  " << executable << " --verify-table TABLE [--threads COUNT]\n";
}

int run(int argc, char** argv) {
  if (argc < 2) {
    usage(argv[0]);
    return 2;
  }
  const std::string mode = argv[1];
  if (mode == "--self-test") {
    require(argc == 2, "--self-test takes no additional arguments");
    runSelfTest();
    return 0;
  }
  if (mode == "--solve") {
    require(argc >= 3, "--solve requires N");
    const unsigned gameSize = parseUnsigned(argv[2]);
    std::optional<std::string> savePath;
    bool verify = false;
    unsigned threads = defaultThreadCount();
    for (int index = 3; index < argc; ++index) {
      const std::string argument = argv[index];
      if (argument == "--save") {
        require(index + 1 < argc, "--save requires a path");
        savePath = argv[++index];
      } else if (argument == "--verify") {
        verify = true;
      } else if (argument == "--threads") {
        require(index + 1 < argc, "--threads requires a count");
        threads = parseUnsigned(argv[++index]);
      } else {
        throw std::invalid_argument("unknown argument: " + argument);
      }
    }
    if (gameSize == 32) {
      require(!savePath.has_value(), "saving the 68 GiB N=32 table is intentionally disabled");
      WideExactTable table;
      table.solve();
      printExactReport(table, commandLine(argc, argv));
      if (verify) {
        double elapsed = 0;
        require(table.verifyScalar(threads, &elapsed), "wide scalar verification failed");
        std::cout << "independent_scalar_verification=pass\n";
        std::cout << "verification_threads=" << threads << '\n';
        std::cout << "verification_seconds=" << std::fixed << std::setprecision(6) << elapsed
                  << '\n';
      }
      return 0;
    }
    PackedExactTable table(gameSize);
    table.solve();
    printExactReport(table, commandLine(argc, argv));
    if (savePath.has_value()) {
      table.save(*savePath);
      std::cout << "table_saved=" << *savePath << '\n';
    }
    if (verify) {
      double elapsed = 0;
      require(table.verifyScalar(threads, &elapsed), "scalar verification failed");
      std::cout << "independent_scalar_verification=pass\n";
      std::cout << "verification_threads=" << threads << '\n';
      std::cout << "verification_seconds=" << std::fixed << std::setprecision(6) << elapsed
                << '\n';
    }
    return 0;
  }
  if (mode == "--mcts") {
    require(argc == 5, "--mcts requires N, SIMULATIONS, and SEED");
    const unsigned gameSize = parseUnsigned(argv[2]);
    const std::uint64_t simulations = std::stoull(argv[3]);
    const std::uint64_t seed = std::stoull(argv[4]);
    MonteCarloSearch search(gameSize, seed);
    search.run(simulations);
    search.report(simulations, seed, commandLine(argc, argv));
    return 0;
  }
  if (mode == "--verify-table") {
    require(argc >= 3, "--verify-table requires a path");
    unsigned threads = defaultThreadCount();
    for (int index = 3; index < argc; ++index) {
      const std::string argument = argv[index];
      if (argument == "--threads") {
        require(index + 1 < argc, "--threads requires a count");
        threads = parseUnsigned(argv[++index]);
      } else {
        throw std::invalid_argument("unknown argument: " + argument);
      }
    }
    PackedExactTable table = PackedExactTable::load(argv[2]);
    double elapsed = 0;
    require(table.verifyScalar(threads, &elapsed), "scalar verification failed");
    std::cout << "software=" << kSoftwareVersion << '\n';
    std::cout << "table=" << argv[2] << '\n';
    std::cout << "N=" << table.gameSize() << '\n';
    std::cout << "root_value=" << outcomeName(table.gameValue()) << '\n';
    std::cout << "independent_scalar_verification=pass\n";
    std::cout << "verification_threads=" << threads << '\n';
    std::cout << "verification_seconds=" << std::fixed << std::setprecision(6) << elapsed
              << '\n';
    return 0;
  }
  usage(argv[0]);
  return 2;
}

}  // namespace catch_up_search

int main(int argc, char** argv) {
  try {
    return catch_up_search::run(argc, argv);
  } catch (const std::exception& error) {
    std::cerr << "error: " << error.what() << '\n';
    return 1;
  }
}
