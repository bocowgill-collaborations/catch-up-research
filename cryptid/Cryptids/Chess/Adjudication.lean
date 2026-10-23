/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Adjudication.Outcomes

/-!
# Exact executable chess history and adjudication

Full histories, repetition and optional claims, exact dead positions, automatic results, and
complete legal action sets refine the frozen reference. The finite graph search is total but
may be astronomically expensive. This module does not evaluate strategic game values.
-/
