/-
Copyright © 2024 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ASCII.Char
import ASCII.String

namespace ASCII

/-! # Char Lemmas -/

namespace Char

theorem toNat_eq_iff_ofNatAux_eq (c : ASCII.Char) (n : Nat) (hn : n < 128) :
    c.toNat = n ↔ ofNatAux n hn = c := by
  simp only [toNat, ofNatAux]
  constructor
  · intro h; cases h; ext; simp only [dif_pos c.toNat_lt, UInt8.toNat]
  · intro h; cases h; simp only [dif_pos hn, ofNatAux, UInt8.toNat]

theorem toNat_ofNatAux (n : Nat) (hn : n < 128) : toNat (ofNatAux n hn) = n := by
  rw [toNat_eq_iff_ofNatAux_eq]

theorem ofNatAux_toNat (c : ASCII.Char) : ofNatAux c.toNat c.toNat_lt = c := by
  rw [← toNat_eq_iff_ofNatAux_eq]

theorem toNat_eq_iff_ofNat_eq (c : ASCII.Char) (n : Nat) (hn : n < 128) :
    c.toNat = n ↔ ofNat n = c := by
  rw [ofNat, dif_pos hn]; exact toNat_eq_iff_ofNatAux_eq ..

theorem toNat_ofNat (n : Nat) (hn : n < 128) : toNat (ofNat n) = n := by
  rw [toNat_eq_iff_ofNat_eq]; exact hn

theorem ofNat_toNat (c : ASCII.Char) : ofNat c.toNat = c := by
  rw [← toNat_eq_iff_ofNat_eq]; exact c.toNat_lt

/-! ### Unicode Conversion -/

theorem toUnicode_eq_iff_ofUnicode_eq (c : ASCII.Char) (u : Unicode.Char) (hu : u.isASCII) :
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

theorem ofUnicode_toUnicode (c : ASCII.Char) :
    ofUnicode c.toUnicode c.toUnicode_isASCII = c := by
  rw [← toUnicode_eq_iff_ofUnicode_eq]

theorem ofUnicode?_eq_ofUnicode (u : Unicode.Char) (hu : u.isASCII) :
    ofUnicode? u = some (ofUnicode u hu) := by simp [ofUnicode?, dif_pos hu]

theorem ofUnicode!_eq_ofUnicode (u : Unicode.Char) (hu : u.isASCII) :
    ofUnicode! u = ofUnicode u hu := by simp [ofUnicode!, dif_pos hu]

/-! ### Case Conversion -/

theorem isLower_iff (c : ASCII.Char) : c.isLower ↔ 97 ≤ c.toNat ∧ c.toNat ≤ 122 := by
  simp [isLower]; rfl

theorem isUpper_iff (c : ASCII.Char) : c.isUpper ↔ 65 ≤ c.toNat ∧ c.toNat ≤ 90 := by
  simp [isUpper]; rfl

theorem not_isUpper_of_isLower {c : ASCII.Char} : c.isLower → ¬ c.isUpper := by
  simp only [isLower_iff, isUpper_iff]
  intro ⟨hl, _⟩ ⟨_, hu⟩
  apply Nat.lt_irrefl c.toNat
  apply Nat.lt_of_le_of_lt hu
  apply Nat.lt_of_lt_of_le _ hl
  decide

theorem not_isLower_of_isUpper {c : ASCII.Char} : c.isUpper → ¬ c.isLower :=
  flip not_isUpper_of_isLower

theorem not_isUpper_toLower (c : ASCII.Char) : ¬ c.toLower.isUpper := by
  simp [-not_and, toLower, isUpper_iff]
  split
  · next h =>
    simp [-not_and, toNat_ofNatAux]
    intro h'
    absurd h'.2
    apply Nat.not_le_of_gt
    apply Nat.lt_of_lt_of_le _ h.1
    decide
  · assumption

theorem not_isLower_toUpper (c : ASCII.Char) : ¬ c.toUpper.isLower := by
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

theorem toUpper_eq_self_of_not_isLower {c : ASCII.Char} (h : ¬ c.isLower) : c.toUpper = c := by
  simp [toUpper]; intro; contradiction

theorem toLower_eq_self_of_not_isUpper {c : ASCII.Char} (h : ¬ c.isUpper) : c.toLower = c := by
  simp [toLower]; intro; contradiction

theorem toLower_toLower (c : ASCII.Char) : c.toLower.toLower = c.toLower :=
  toLower_eq_self_of_not_isUpper <| not_isUpper_toLower _

theorem toUpper_toUpper (c : ASCII.Char) : c.toUpper.toUpper = c.toUpper :=
  toUpper_eq_self_of_not_isLower <| not_isLower_toUpper _

end Char

/-! # String Lemmas -/

namespace String

@[simp] theorem mkEmpty_eq (cap : Nat) : mkEmpty cap = a#"" := rfl

@[simp] theorem append_eq (s t : ASCII.String) : append s t = s ++ t := rfl

/-! ### toByteArray -/

@[simp] theorem toByteArray_nil : a#"".toByteArray = ByteArray.empty := rfl

@[simp] theorem toByteArray_push (s : ASCII.String) (c : ASCII.Char) :
    (s.push c).toByteArray = s.toByteArray.push c.toByte := rfl

@[simp] theorem toByteArray_append (s t : ASCII.String) :
    (s ++ t).toByteArray = s.toByteArray ++ t.toByteArray := rfl

@[simp] theorem toByteArray_extract (s : ASCII.String) (start stop : Nat) :
    (s.extract start stop).toByteArray = s.toByteArray.extract start stop := rfl

/-! ### length -/

@[simp] theorem length_nil : a#"".length = 0 := rfl

@[simp] theorem length_push (s : ASCII.String) (c : ASCII.Char) :
    (s.push c).length = s.length + 1 := by
  simp [length]

theorem length_append (s t : ASCII.String) : (s ++ t).length = s.length + t.length := by
  simp [length, ByteArray.size_append]

theorem length_extract (s : ASCII.String) (start stop : Nat) :
    (s.extract start stop).length = min stop s.length - start := by
  simp [length, ByteArray.size_extract]

/-! ### append -/

@[simp] theorem append_nil (s : ASCII.String) : s ++ a#"" = s := by
  ext; simp

@[simp] theorem nil_append (t : ASCII.String) : a#"" ++ t = t := by
  ext; simp

theorem append_assoc (s t u : ASCII.String) : (s ++ t) ++ u = s ++ (t ++ u) := by
  ext; simp [Array.append_assoc]

theorem append_push (s t : ASCII.String) (c : ASCII.Char) : s ++ t.push c = (s ++ t).push c := by
  ext; simp [Array.push_eq_append_singleton, Array.append_assoc]

/-! ### get -/

@[simp] theorem toByte_get (s : ASCII.String) (i : Nat) (h : i < s.length) :
    s[i].toByte = s.toByteArray[i] := rfl

theorem get_push_lt (s : ASCII.String) (c : ASCII.Char) (i : Nat) (h : i < s.length)
    (h' : i < (s.push c).length := length_push .. ▸ Nat.lt_trans h (Nat.lt_succ_self _)) :
    (s.push c)[i] = s[i] := by
  ext; simp [ByteArray.get_push_lt, h]

theorem get_push_eq (s : ASCII.String) (c : ASCII.Char) : (s.push c)[s.length] = c := by
  ext; simp

theorem get_append_left {s t : ASCII.String} {i : Nat} (hlt : i < s.length)
    (h : i < (s ++ t).length := length_append .. ▸ Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _)) :
    (s ++ t)[i] = s[i] := by
  ext; simp [ByteArray.get_append_left hlt]

theorem get_append_right {s t : ASCII.String} {i : Nat} (hle : s.length ≤ i) (h : i < (s ++ t).length)
    (h' : i - s.length < t.length := Nat.sub_lt_left_of_lt_add hle (length_append .. ▸ h)) :
    (s ++ t)[i] = t[i - s.length] := by
  ext; simp [length, ByteArray.get_append_right hle]

theorem get_extract {s : ASCII.String} {start stop} (h : i < (s.extract start stop).length)
    (h' : start + i < s.length := ByteArray.get_extract_aux h) :
    (s.extract start stop)[i] = s[start + i] := by
  ext; simp

end String
