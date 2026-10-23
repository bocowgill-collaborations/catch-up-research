# What exact computation can reuse

The repository already proves the normalized evaluator correct. A separate packed or bottom-up implementation still needs its own correspondence argument or independently checked certificates. The observations below explain existing mathematics; they do not certify an optimized implementation.

## A small state description

After the one-pick opening, use remaining counters `R` and the acting player's nonnegative deficit `d`. For a legal pick `x`:

| Condition | New deficit | Perspective |
| --- | --- | --- |
| x < d | d-x | Same player continues |
| x >= d | x-d | Players swap; negate the child outcome |

Equality ends the turn. Empty support draws only at deficit zero. If the remaining sum is smaller than the deficit, the acting player loses. Filling smaller supports before larger ones terminates because each pick removes a counter. Maximizing the three outcomes preserves the stated objective; maximizing final score margin is a different specification.

The existing correspondence theorems are in [Executable](../CatchUp/Executable.lean) and [Reference](../CatchUp/Reference.lean). [ReachableBounds](../CatchUp/ReachableBounds.lean) proves `R` stays inside the original interval and `d <= N`, giving `(N+1)*2^N` possible normalized labels before other restrictions.

## Parity can save storage

Let `T=N(N+1)/2` be the fixed original total and `s=sum(R)`. The [proved reachability invariant](../CatchUp/Earlier/Parity.lean) is:

```text
(d+s) mod 2 = T mod 2.
```

Consequently `R` and `T mod 2` determine the parity of `d`. With `k=floor(d/2)`, arithmetic recovers:

```text
d = 2*k + ((T+s) mod 2).
```

This suggests at most `floor(N/2)+1` deficit rows. It does **not** identify arbitrary neighboring deficits: with remaining `{1}`, deficit zero wins and deficit one draws, even though both have `floor(d/2)=0`. The original-total parity must be fixed when decoding and when sharing caches. Not every table label has to be reachable.

The parity module also proves that odd `d+s` excludes draw. In a fixed odd-total game this permits a one-bit outcome representation; even-total games require all three outcomes, which fit in two bits. This concerns table data, not the size of a formal proof or the state count of a binary Turing machine. A checker must still validate transitions, decoding and terminal cells, including the empty-support cell whose decoded deficit might be one rather than zero.

## Reproduction should answer a specific question

[Von Stengel's public 2019 report](https://www.lse.ac.uk/Mathematics/assets/documents/Events-Archive/CGO-PhD/PhD-Seminar-on-Combinatorics-2019-update.pdf#page=5) describes analysis through N=34 using an 8 GB laptop, 37 GB virtual memory and 28 hours. These are reported historical resources, not a measured requirement or runtime prediction for a current implementation. No large replay of that computation has run here.

Useful steps are to locate source code and retained results, audit the rules and outcome objective, and reproduce small calibration cases against the existing evaluator. A full historical rerun is optional and needs a concrete purpose and budget. Reading a result table, reproducing it numerically, and checking a strategy certificate in Lean provide different levels of assurance. See [computation and evidence](../computation/) and the [source guide](sources.md).
