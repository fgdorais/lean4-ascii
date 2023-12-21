/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std

/-- Abbreviation for `Char` to avoid using the root prefix -/
protected abbrev Unicode.Char := _root_.Char

/-- Abbreviation for `String` to avoid using the root prefix -/
protected abbrev Unicode.String := _root_.String

/-- Test whether Unicode character is an ASCII character -/
def Char.isASCII (c : Char) : Bool := c.toNat < 128

/-- Test whether Unicode string is an ASCII string -/
def String.isASCII (s : String) : Bool := s.all Char.isASCII

-- TODO: Move to Std

theorem UInt8.toNat_lt (x : UInt8) : x.toNat < 2 ^ 8 := x.val.isLt

@[simp] theorem UInt8.toUInt16_toNat (x : UInt8) : x.toUInt16.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

@[simp] theorem UInt8.toUInt32_toNat (x : UInt8) : x.toUInt32.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

@[simp] theorem UInt8.toUInt64_toNat (x : UInt8) : x.toUInt64.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

theorem UInt16.toNat_lt (x : UInt16) : x.toNat < 2 ^ 16 := x.val.isLt

@[simp] theorem UInt16.toUInt32_toNat (x : UInt16) : x.toUInt32.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

@[simp] theorem UInt16.toUInt64_toNat (x : UInt16) : x.toUInt64.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

theorem UInt32.toNat_lt (x : UInt32) : x.toNat < 2 ^ 32 := x.val.isLt

@[simp] theorem UInt32.toUInt64_toNat (x : UInt32) : x.toUInt64.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt (by decide))

theorem UInt64.toNat_lt (x : UInt64) : x.toNat < 2 ^ 64 := x.val.isLt

theorem USize.size_eq : USize.size = 2 ^ System.Platform.numBits := by
  have : 1 ≤ 2 ^ System.Platform.numBits := Nat.succ_le_of_lt (Nat.pow_two_pos _)
  rw [USize.size, Nat.succ_eq_add_one, Nat.sub_eq, Nat.sub_add_cancel this]

theorem USize.le_size : 2 ^ 32 ≤ USize.size := by
  rw [size_eq]
  apply Nat.pow_le_pow_of_le_right (by decide)
  cases System.Platform.numBits_eq <;> simp_arith [*]

theorem USize.size_le : USize.size ≤ 2 ^ 64 := by
  rw [size_eq]
  apply Nat.pow_le_pow_of_le_right (by decide)
  cases System.Platform.numBits_eq <;> simp_arith [*]

theorem USize.toNat_lt (x : USize) : x.toNat < 2 ^ System.Platform.numBits := by
  rw [←USize.size_eq]; exact x.val.isLt

@[simp] theorem USize.toUInt64_toNat (x : USize) : x.toUInt64.toNat = x.toNat := by
  simp only [USize.toUInt64, UInt64.toNat]; rfl

@[simp] theorem UInt32.toUSize_toNat (x : UInt32) : x.toUSize.toNat = x.toNat :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le x.toNat_lt USize.le_size)
