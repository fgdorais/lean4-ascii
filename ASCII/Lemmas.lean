/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ASCII.Char
import ASCII.String

namespace ASCII

/-! # Char Lemmas -/

namespace Char

theorem toNat_eq_iff_ofNatAux_eq (c : Char) (n : Nat) (hn : n < 128) :
    c.toNat = n ↔ ofNatAux n hn = c := by
  simp only [toNat, ofNatAux]
  constructor
  · intro h; cases h; ext; simp only [dif_pos c.toNat_lt, UInt8.toNat]
  · intro h; cases h; simp only [dif_pos hn, ofNatAux, UInt8.toNat]

theorem toNat_ofNatAux (n : Nat) (hn : n < 128) : toNat (ofNatAux n hn) = n := by
  rw [toNat_eq_iff_ofNatAux_eq]

theorem ofNatAux_toNat (c : Char) : ofNatAux c.toNat c.toNat_lt = c := by
  rw [← toNat_eq_iff_ofNatAux_eq]

theorem toNat_eq_iff_ofNat_eq (c : Char) (n : Nat) (hn : n < 128) :
    c.toNat = n ↔ ofNat n = c := by
  rw [ofNat, dif_pos hn]; exact toNat_eq_iff_ofNatAux_eq ..

theorem toNat_ofNat (n : Nat) (hn : n < 128) : toNat (ofNat n) = n := by
  rw [toNat_eq_iff_ofNat_eq]; exact hn

theorem ofNat_toNat (c : Char) : ofNat c.toNat = c := by
  rw [← toNat_eq_iff_ofNat_eq]; exact c.toNat_lt

/-! ### Unicode Conversion -/

theorem toUnicode_eq_iff_ofUnicode_eq (c : Char) (u : Unicode.Char) (hu : u.isASCII) :
    c.toUnicode = u ↔ ofUnicode u hu = c := by
  simp only [Char.toUnicode, ofUnicode]
  constructor
  · intro h; cases h
    simp [_root_.Char.isASCII, _root_.Char.toNat] at hu
    have hlt : c.toNat < 256 := by apply Nat.lt_trans hu; decide
    ext; simp [Nat.mod_eq_of_lt hlt]
  · intro h; cases h
    simp [_root_.Char.isASCII, _root_.Char.toNat] at hu
    have hlt : u.val.toNat < 256 := by apply Nat.lt_trans hu; decide
    ext; simp [Nat.mod_eq_of_lt hlt]

theorem toUnicode_ofUnicode (u : Unicode.Char) (hu : u.isASCII) :
    Char.toUnicode (ofUnicode u hu) = u := by
  rw [toUnicode_eq_iff_ofUnicode_eq]

theorem ofUnicode_toUnicode (c : Char) :
    ofUnicode c.toUnicode c.toUnicode_isASCII = c := by
  rw [← toUnicode_eq_iff_ofUnicode_eq]

theorem ofUnicode?_eq_ofUnicode (u : Unicode.Char) (hu : u.isASCII) :
    ofUnicode? u = some (ofUnicode u hu) := by simp [ofUnicode?, dif_pos hu]

theorem ofUnicode!_eq_ofUnicode (u : Unicode.Char) (hu : u.isASCII) :
    ofUnicode! u = ofUnicode u hu := by simp [ofUnicode!, dif_pos hu]

/-! ### Case Conversion -/

theorem isLower_iff (c : Char) : c.isLower ↔ 97 ≤ c.toNat ∧ c.toNat ≤ 122 := by
  simp [isLower]; rfl

theorem isUpper_iff (c : Char) : c.isUpper ↔ 65 ≤ c.toNat ∧ c.toNat ≤ 90 := by
  simp [isUpper]; rfl

theorem not_isUpper_of_isLower {c : Char} : c.isLower → ¬ c.isUpper := by
  simp only [isLower_iff, isUpper_iff]
  intro ⟨hl, _⟩ ⟨_, hu⟩
  apply Nat.lt_irrefl c.toNat
  apply Nat.lt_of_le_of_lt hu
  apply Nat.lt_of_lt_of_le _ hl
  decide

theorem not_isLower_of_isUpper {c : Char} : c.isUpper → ¬ c.isLower :=
  flip not_isUpper_of_isLower

theorem not_isUpper_toLower (c : Char) : ¬ c.toLower.isUpper := by
  simp [-not_and, toLower, isUpper_iff]
  split
  · next h =>
    simp [-not_and, toNat_ofNatAux]
    intro h'
    absurd h'.2
    apply Nat.not_le_of_gt
    apply Nat.lt_of_lt_of_le _ <| Nat.add_le_add_right h.1 32
    decide
  · assumption

theorem not_isLower_toUpper (c : Char) : ¬ c.toUpper.isLower := by
  simp [-not_and, toUpper, isLower_iff]
  split
  · next h =>
    simp [-not_and, toNat_ofNatAux]
    intro h'
    absurd h'.1
    apply Nat.not_le_of_gt
    apply Nat.lt_of_le_of_lt (Nat.sub_le_sub_right h.2 32)
    decide
  · assumption

theorem toUpper_eq_self_of_not_isLower {c : Char} (h : ¬ c.isLower) : c.toUpper = c := by
  simp [toUpper]; intro; contradiction

theorem toLower_eq_self_of_not_isUpper {c : Char} (h : ¬ c.isUpper) : c.toLower = c := by
  simp [toLower]; intro; contradiction

theorem toLower_toLower (c : Char) : c.toLower.toLower = c.toLower :=
  toLower_eq_self_of_not_isUpper <| not_isUpper_toLower _

theorem toUpper_toUpper (c : Char) : c.toUpper.toUpper = c.toUpper :=
  toUpper_eq_self_of_not_isLower <| not_isLower_toUpper _

end Char
