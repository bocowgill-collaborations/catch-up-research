/-
Copyright 2026 The Cryptids Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Cryptids.Chess.Exec.Moves

/-!
# Executable chess move rules

The public M2 API gives concrete encodings, constructive legality decisions, a duplicate-free
complete move list, and full unchecked updates, with refinement on all raw positions. It does
not adjudicate game histories or claims. The frozen reference aggregate is left unchanged.
-/
