/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Adjudication.History

/-!
# Flat natural-number chess data

The fixed position format stores seven metadata words followed by 64 rank-major cells.
The final equality guard rejects every noncanonical input, including invalid finite codes.
All reconstruction and validation are executable and retain unchecked raw chess data.
-/

@[expose] public section
namespace Chess.Compilation.Data

/-- White is zero and black is one. -/
def encodeColor : Color → Nat
  | .white => 0
  | .black => 1

/-- Decode a color candidate; the enclosing canonicality check rejects other codes. -/
def colorOfNat : Nat → Color
  | 1 => .black
  | _ => .white

/-- Piece-kind codes are king, queen, rook, bishop, knight, pawn. -/
def encodeKind : PieceKind → Nat
  | .king => 0
  | .queen => 1
  | .rook => 2
  | .bishop => 3
  | .knight => 4
  | .pawn => 5

/-- Empty is zero; a piece has code `1 + 6 * color + kind`. -/
def encodeCell : Option Piece → Nat
  | none => 0
  | some piece => 1 + 6 * encodeColor piece.color + encodeKind piece.kind

/-- Decode a cell candidate; invalid cell codes become empty before validation. -/
def cellOfNat : Nat → Option Piece
  | 1 => some ⟨.white, .king⟩
  | 2 => some ⟨.white, .queen⟩
  | 3 => some ⟨.white, .rook⟩
  | 4 => some ⟨.white, .bishop⟩
  | 5 => some ⟨.white, .knight⟩
  | 6 => some ⟨.white, .pawn⟩
  | 7 => some ⟨.black, .king⟩
  | 8 => some ⟨.black, .queen⟩
  | 9 => some ⟨.black, .rook⟩
  | 10 => some ⟨.black, .bishop⟩
  | 11 => some ⟨.black, .knight⟩
  | 12 => some ⟨.black, .pawn⟩
  | _ => none

/-- A boolean uses precisely zero or one. -/
def encodeBool (value : Bool) : Nat := if value then 1 else 0

/-- Zero means no en-passant target; a square has code `1 + file + 8 * rank`. -/
def encodeTarget : Option Square → Nat
  | none => 0
  | some square => 1 + square.file.val + 8 * square.rank.val

/-- Decode a square candidate; invalid target codes become `none` before validation. -/
def targetOfNat (word : Nat) : Option Square :=
  if word = 0 then none
  else if bound : word - 1 < 64 then
    some ⟨⟨(word - 1) % 8, Nat.mod_lt _ (by decide)⟩,
      ⟨(word - 1) / 8, by omega⟩⟩
  else none

/-- Rank-major, file-fast cells: index `8 * rank + file`. -/
def encodeBoard (board : Exec.Board) : List Nat :=
  List.ofFn fun index : Fin 64 ↦
    encodeCell board[index.val / 8][index.val % 8]

/-- Reconstruct all 64 cells. Missing words are temporary empty candidates. -/
def boardOfWords (words : List Nat) : Exec.Board :=
  Vector.ofFn fun rank ↦ Vector.ofFn fun file ↦
    cellOfNat (words[8 * rank.val + file.val]?.getD 0)

/-- Encode all raw fields in the fixed 71-word format. -/
def encodePosition (position : Exec.Position) : List Nat :=
  [encodeColor position.turn,
    encodeBool position.castlingRights.whiteKingside,
    encodeBool position.castlingRights.whiteQueenside,
    encodeBool position.castlingRights.blackKingside,
    encodeBool position.castlingRights.blackQueenside,
    encodeTarget position.enPassantTarget, position.halfmoveClock] ++ encodeBoard position.board

/-- Decode exactly one canonical position, rejecting every malformed or trailing word. -/
def decodePosition (words : List Nat) : Option Exec.Position :=
  match words with
  | turn :: wk :: wq :: bk :: bq :: ep :: clock :: cells =>
    let candidate : Exec.Position :=
      { board := boardOfWords cells
        turn := colorOfNat turn
        castlingRights := ⟨wk == 1, wq == 1, bk == 1, bq == 1⟩
        enPassantTarget := targetOfNat ep
        halfmoveClock := clock }
    if encodePosition candidate = words then some candidate else none
  | _ => none

@[simp] theorem cellOfNat_encodeCell (cell : Option Piece) :
    cellOfNat (encodeCell cell) = cell := by
  cases cell with
  | none => rfl
  | some piece => cases piece with | mk color kind => cases color <;> cases kind <;> rfl

@[simp] theorem colorOfNat_encodeColor (color : Color) :
    colorOfNat (encodeColor color) = color := by
  cases color <;> rfl

@[simp] theorem boolOfNat_encodeBool (value : Bool) : (encodeBool value == 1) = value := by
  cases value <;> rfl

@[simp] theorem targetOfNat_encodeTarget (target : Option Square) :
    targetOfNat (encodeTarget target) = target := by
  cases target with
  | none => rfl
  | some square =>
    rcases square with ⟨file, rank⟩
    simp only [targetOfNat, encodeTarget, Nat.add_eq_zero_iff, one_ne_zero,
      Fin.val_eq_zero_iff, Fin.isValue, false_and, mul_eq_zero, OfNat.ofNat_ne_zero,
      false_or, ↓reduceIte, show 1 + file.val + 8 * rank.val - 1 < 64 by omega,
      ↓reduceDIte, Option.some.injEq, Square.mk.injEq]
    exact ⟨Fin.ext (by dsimp; omega), Fin.ext (by dsimp; omega)⟩

@[simp] theorem boardOfWords_encodeBoard (board : Exec.Board) :
    boardOfWords (encodeBoard board) = board := by
  apply Vector.ext
  intro rank hr
  apply Vector.ext
  intro file hf
  simp only [boardOfWords, Vector.getElem_ofFn, encodeBoard, List.getElem?_ofFn]
  simp only [show 8 * rank + file < 64 by omega, ↓reduceDIte, Option.getD_some,
    cellOfNat_encodeCell, show (8 * rank + file) / 8 = rank by omega,
    show (8 * rank + file) % 8 = file by omega]

@[simp] theorem decode_encodePosition (position : Exec.Position) :
    decodePosition (encodePosition position) = some position := by
  rcases position with ⟨board, turn, ⟨wk, wq, bk, bq⟩, target, clock⟩
  simp [encodePosition, decodePosition]

/-- Successful decoding characterizes precisely the image of the encoder. -/
theorem decodePosition_eq_some_iff (words : List Nat) (position : Exec.Position) :
    decodePosition words = some position ↔ encodePosition position = words := by
  constructor
  · intro h
    unfold decodePosition at h
    split at h <;> aesop
  · rintro rfl
    exact decode_encodePosition _

@[simp] theorem encodeBoard_length (board : Exec.Board) : (encodeBoard board).length = 64 := by
  simp [encodeBoard]

@[simp] theorem encodePosition_length (position : Exec.Position) :
    (encodePosition position).length = 71 := by
  simp [encodePosition]

/-- Consecutive 71-word positions, with list order unchanged. -/
def encodePositions : List Exec.Position → List Nat
  | [] => []
  | position :: positions => encodePosition position ++ encodePositions positions

/-- Parse exactly the stated number of complete positions and consume every word. -/
def decodePositions : Nat → List Nat → Option (List Exec.Position)
  | 0, words => if words = [] then some [] else none
  | n + 1, words => do
    let position ← decodePosition (words.take 71)
    let positions ← decodePositions n (words.drop 71)
    pure (position :: positions)

/-- History length, current position, then prior positions newest first. -/
def encodeGame (game : Adjudication.Game) : List Nat :=
  game.previous.length :: (encodePosition game.current ++ encodePositions game.previous)

/-- Parse a game candidate with its explicit history count. -/
def gameOfWords : List Nat → Option Adjudication.Game
  | [] => none
  | count :: body => do
    let current ← decodePosition (body.take 71)
    let previous ← decodePositions count (body.drop 71)
    pure ⟨current, previous⟩

/-- Parse an entire game and reject every noncanonical representation. -/
def decodeGame (words : List Nat) : Option Adjudication.Game :=
  match gameOfWords words with
  | none => none
  | some candidate => if encodeGame candidate = words then some candidate else none

@[simp] theorem decode_encodePositions (positions : List Exec.Position) :
    decodePositions positions.length (encodePositions positions) = some positions := by
  induction positions with
  | nil => rfl
  | cons position positions ih =>
    simp only [List.length_cons, encodePositions, decodePositions]
    simp only [← encodePosition_length position, List.take_left, List.drop_left,
      decode_encodePosition, ih, pure]
    rfl

@[simp] theorem decode_encodeGame (game : Adjudication.Game) :
    decodeGame (encodeGame game) = some game := by
  rcases game with ⟨current, previous⟩
  simp only [encodeGame, decodeGame, gameOfWords]
  simp only [← encodePosition_length current, List.take_left, List.drop_left,
    decode_encodePosition, decode_encodePositions]
  dsimp
  simp only [↓reduceIte]

/-- Successful game decoding is equivalent to exact re-encoding, including full history. -/
theorem decodeGame_eq_some_iff (words : List Nat) (game : Adjudication.Game) :
    decodeGame words = some game ↔ encodeGame game = words := by
  constructor
  · intro h
    unfold decodeGame at h
    split at h <;> aesop
  · rintro rfl
    exact decode_encodeGame _

/-- The game format has one length word and one 71-word block per retained position. -/
@[simp] theorem encodePositions_length (positions : List Exec.Position) :
    (encodePositions positions).length = 71 * positions.length := by
  induction positions with
  | nil => rfl
  | cons position positions ih => simp [encodePositions, ih, Nat.mul_add, Nat.add_comm]

@[simp] theorem encodeGame_length (game : Adjudication.Game) :
    (encodeGame game).length = 1 + 71 * (game.previous.length + 1) := by
  simp [encodeGame, Nat.mul_add, Nat.add_comm]

/-- Re-encode any successfully decoded position without changing a word. -/
theorem encode_decodePosition {words : List Nat} {position : Exec.Position}
    (success : decodePosition words = some position) : encodePosition position = words :=
  (decodePosition_eq_some_iff words position).mp success

/-- Re-encode any successfully decoded game without changing a word. -/
theorem encode_decodeGame {words : List Nat} {game : Adjudication.Game}
    (success : decodeGame words = some game) : encodeGame game = words :=
  (decodeGame_eq_some_iff words game).mp success

/-- The stored history count is exact, including repeated equal prior positions. -/
theorem decodeGame_history_count {count : Nat} {body : List Nat} {game : Adjudication.Game}
    (success : decodeGame (count :: body) = some game) : game.previous.length = count := by
  exact (List.cons.inj (encode_decodeGame success)).1

/-- Every accepted game body has one current block plus the stated number of prior blocks. -/
theorem decodeGame_body_length {count : Nat} {body : List Nat} {game : Adjudication.Game}
    (success : decodeGame (count :: body) = some game) : body.length = 71 * (count + 1) := by
  have length := congrArg List.length (encode_decodeGame success)
  have count_eq := decodeGame_history_count success
  simp only [encodeGame_length, List.length_cons] at length
  omega

/-- A wrong history count, truncated block, or trailing word forces rejection. -/
theorem decodeGame_wrong_length (count : Nat) (body : List Nat)
    (length : body.length ≠ 71 * (count + 1)) : decodeGame (count :: body) = none := by
  cases result : decodeGame (count :: body) with
  | none => rfl
  | some game => exact False.elim (length (decodeGame_body_length result))

/-- Distinct raw positions have distinct serializations. -/
theorem encodePosition_injective : Function.Injective encodePosition := by
  intro first second equal
  have decoded := congrArg decodePosition equal
  simpa only [decode_encodePosition, Option.some.injEq] using decoded

/-- Distinct full histories have distinct serializations. -/
theorem encodeGame_injective : Function.Injective encodeGame := by
  intro first second equal
  have decoded := congrArg decodeGame equal
  simpa only [decode_encodeGame, Option.some.injEq] using decoded

/-- Every incorrect position length is rejected. -/
theorem decodePosition_wrong_length (words : List Nat) (length : words.length ≠ 71) :
    decodePosition words = none := by
  cases result : decodePosition words with
  | none => rfl
  | some position =>
    have equal := congrArg List.length (encode_decodePosition result)
    simp only [encodePosition_length] at equal
    exact False.elim (length equal.symm)

/-- All pieces, including empty cells, have codes at most twelve. -/
theorem encodeCell_le_twelve (cell : Option Piece) : encodeCell cell ≤ 12 := by
  cases cell with
  | none => decide
  | some piece => cases piece with | mk color kind => cases color <;> cases kind <;> decide

/-- Every emitted board word is a valid cell code. -/
theorem encodeBoard_cells (board : Exec.Board) : ∀ cell ∈ encodeBoard board, cell ≤ 12 := by
  simp only [encodeBoard, List.mem_ofFn]
  rintro cell ⟨index, rfl⟩
  exact encodeCell_le_twelve _

/-- The side-to-move code has precisely the prescribed finite range. -/
theorem encodeColor_le_one (color : Color) : encodeColor color ≤ 1 := by
  cases color <;> decide

/-- Castling-right words have precisely the prescribed finite range. -/
theorem encodeBool_le_one (value : Bool) : encodeBool value ≤ 1 := by
  cases value <;> decide

/-- The target code is zero or one of the 64 squares. -/
theorem encodeTarget_le_sixty_four (target : Option Square) : encodeTarget target ≤ 64 := by
  cases target with
  | none => decide
  | some square => simp only [encodeTarget]; omega

/-- The complete finite-code and length requirements; the clock is unrestricted. -/
def ValidPositionWords : List Nat → Prop
  | turn :: wk :: wq :: bk :: bq :: ep :: _clock :: cells =>
    turn ≤ 1 ∧ wk ≤ 1 ∧ wq ≤ 1 ∧ bk ≤ 1 ∧ bq ≤ 1 ∧ ep ≤ 64 ∧
      cells.length = 64 ∧ ∀ cell ∈ cells, cell ≤ 12
  | _ => False

/-- Every raw position emits valid metadata and exactly 64 valid cells. -/
theorem encodePosition_valid (position : Exec.Position) :
    ValidPositionWords (encodePosition position) := by
  simpa [encodePosition, ValidPositionWords, encodeColor_le_one, encodeBool_le_one,
    encodeTarget_le_sixty_four] using encodeBoard_cells position.board

/-- Any successful parse satisfies all metadata, cell-code, and length checks. -/
theorem decodePosition_valid {words : List Nat} {position : Exec.Position}
    (success : decodePosition words = some position) : ValidPositionWords words := by
  rw [← encode_decodePosition success]
  exact encodePosition_valid position

/-- Malformed finite codes and board lengths are rejected rather than normalized. -/
theorem decodePosition_invalid (words : List Nat) (invalid : ¬ValidPositionWords words) :
    decodePosition words = none := by
  cases result : decodePosition words with
  | none => rfl
  | some position => exact False.elim (invalid (decodePosition_valid result))

/-- Exact initial position data, including every board cell. -/
def initialPositionWords : List Nat :=
  [0, 1, 1, 1, 1, 0, 0,
   3, 5, 4, 2, 1, 4, 5, 3,
   6, 6, 6, 6, 6, 6, 6, 6,
   0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0,
   12, 12, 12, 12, 12, 12, 12, 12,
   9, 11, 10, 8, 7, 10, 11, 9]

/-- The initial game has no previous positions. -/
def initialGameWords : List Nat := 0 :: initialPositionWords

@[simp] theorem encode_initialPosition : encodePosition Exec.initial = initialPositionWords := by
  rfl

@[simp] theorem encode_initialGame :
    encodeGame Adjudication.Game.initial = initialGameWords := by
  rfl

@[simp] theorem initialPositionWords_length : initialPositionWords.length = 71 := by rfl

@[simp] theorem initialGameWords_length : initialGameWords.length = 72 := by rfl

@[simp] theorem decode_initialPosition :
    decodePosition initialPositionWords = some Exec.initial := by
  rw [← encode_initialPosition, decode_encodePosition]

@[simp] theorem decode_initialGame :
    decodeGame initialGameWords = some Adjudication.Game.initial := by
  rw [← encode_initialGame, decode_encodeGame]

end Chess.Compilation.Data
