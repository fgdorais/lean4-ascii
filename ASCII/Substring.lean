/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ASCII.String

namespace ASCII

structure Substring where
  data : String
  start : Nat
  stop : Nat
  valid : start ≤ stop ∧ stop ≤ data.length

abbrev Substring.length (s : Substring) := s.stop - s.start

instance : GetElem Substring Nat Char fun s i => i < s.length where
  getElem s i h :=
    have : s.start + i < s.data.length := by
      rw [Nat.add_comm]
      apply Nat.lt_of_lt_of_le _ s.valid.2
      exact Nat.add_lt_of_lt_sub h
    s.data[s.start + i]

instance : Stream Substring Char where
  next? s :=
    if h : s.start < s.stop then
      have valid := ⟨Nat.succ_le_of_lt h, s.valid.2⟩
      some (s[0]'(Nat.zero_lt_sub_of_lt h), {s with start := s.start+1, valid})
    else
      none
