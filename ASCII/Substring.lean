/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ASCII.String

namespace ASCII

/-- ASCII substring type -/
protected structure Substring where
  /-- Underlying string -/
  data  : ASCII.String
  /-- Start position -/
  start : Nat
  /-- Stop position -/
  stop  : Nat
  /-- Validity condition -/
  valid : start ≤ stop ∧ stop ≤ data.length

/-- Length of a substring -/
abbrev Substring.length (s : ASCII.Substring) := s.stop - s.start

instance : GetElem ASCII.Substring Nat ASCII.Char fun s i => i < s.length where
  getElem s i h :=
    have : s.start + i < s.data.length := by
      rw [Nat.add_comm]
      apply Nat.lt_of_lt_of_le _ s.valid.2
      exact Nat.add_lt_of_lt_sub h
    s.data[s.start + i]

instance : Stream ASCII.Substring ASCII.Char where
  next? s :=
    if h : s.start < s.stop then
      have valid := ⟨Nat.succ_le_of_lt h, s.valid.2⟩
      some (s[0]'(Nat.zero_lt_sub_of_lt h), {s with start := s.start+1, valid})
    else
      none
