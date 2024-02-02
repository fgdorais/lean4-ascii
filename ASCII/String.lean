/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ASCII.Char

namespace ASCII

structure String where
  /-- Underlying byte data -/
  toByteArray : ByteArray
  /-- Validity -/
  valid (i) {h : i < toByteArray.size} : toByteArray[i] < 128

namespace String

/-- Empty string with specific capacity -/
def mkEmpty (size : Nat) : ASCII.String where
  toByteArray := .mkEmpty size
  valid := by intros; contradiction

/-- Empty string -/
abbrev empty : ASCII.String := mkEmpty 0

instance : Inhabited String where
  default := .empty

/-- Length of a string -/
abbrev length (s : ASCII.String) := s.toByteArray.size

@[ext] protected theorem ext : {s t : ASCII.String} → s.toByteArray = t.toByteArray → s = t
  | ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

instance : GetElem String Nat Char fun s i => i < s.length where
  getElem s i h := ⟨s.toByteArray.get ⟨i, h⟩, s.valid i⟩

/-- Append a character `c` at the end of string `s` -/
def push (s : String) (c : Char) : String where
  toByteArray := s.toByteArray.push c.toByte
  valid i h := by
    if hlt : i < s.toByteArray.size then
      rw [ByteArray.get_push_lt _ _ _ hlt]
      exact s.valid i
    else
      have heq : i = s.toByteArray.size := by
        apply Nat.le_antisymm
        · apply Nat.le_of_lt_succ
          rwa [ByteArray.size_push] at h
        · exact Nat.le_of_not_gt hlt
      cases heq
      rw [ByteArray.get_push_eq]
      exact c.valid

/-- Append a string `t` at the end of string `s` -/
def append (s t : String) : String where
  toByteArray := s.toByteArray ++ t.toByteArray
  valid i h := by
    simp [getElem_fin, ByteArray.getElem_eq_data_getElem, ByteArray.append_data]
    if hlt : i < s.toByteArray.size then
      rw [Array.get_append_left]; exact s.valid (h:=hlt)
    else
      have hle : s.toByteArray.size ≤ i := Nat.le_of_not_gt hlt
      have h : i - s.toByteArray.size < t.toByteArray.size :=
        Nat.sub_lt_left_of_lt_add hle (ByteArray.size_append .. ▸ h)
      rw [Array.get_append_right (hle:=hle) (hlt:=h)]
      exact t.valid (i - s.toByteArray.size)

/-- Extract a substring from string `s` -/
def extract (s : String) (start stop : Nat) : String where
  toByteArray := s.toByteArray.extract start stop
  valid i h := by rw [ByteArray.get_extract]; exact s.valid (start + i)

/-- Coercion from ASCII string to Unicode string -/
@[coe, extern "lean_string_from_utf8_unchecked"]
def toUnicode (s : @&ASCII.String) : Unicode.String :=
  loop 0 (Nat.zero_le _) ""
where
  loop (i : Nat) (hi : i ≤ s.length) (r : Unicode.String) :=
    if h : i = s.length then r else
      have hi : i < s.length := Nat.lt_of_le_of_ne hi h
      loop (i + 1) (Nat.succ_le_of_lt hi) (r.push s[i])
termination_by s.length - i

instance : Coe ASCII.String Unicode.String where
  coe := String.toUnicode

instance : ToString ASCII.String where
  toString s := s.toUnicode

/-- Coerce a Unicode string into an ASCII string -/
@[extern "lean_string_to_utf8"]
def ofUnicode (s : @&Unicode.String) (h : s.isASCII) : ASCII.String :=
  loop s.data (String.all_eq .. ▸ h) (mkEmpty s.length)
where
  loop (cs : List Unicode.Char) (h : cs.all Char.isASCII) (acc : ASCII.String) : ASCII.String :=
    match cs with
    | [] => acc
    | c :: cs =>
      have h := Bool.and_eq_true _ _ ▸ List.all_cons ▸ h
      loop cs h.2 (acc.push (c.toASCII h.1))
alias _root_.String.toASCII := ofUnicode

@[inherit_doc String.ofUnicode]
def ofUnicode? (s : Unicode.String) : Option ASCII.String :=
  if h : s.isASCII then some (.ofUnicode s h) else none
alias _root_.String.toASCII? := ofUnicode?

@[inherit_doc String.ofUnicode]
def ofUnicode! (s : Unicode.String) : ASCII.String :=
  if h : s.isASCII then .ofUnicode s h else panic! "characters out of ASCII range"
alias _root_.String.toASCII! := ofUnicode!

open Lean Parser in
/-- Syntax for ASCII string -/
macro "a" noWs s:strLit : term =>
  if s.getString.isASCII then
    `(String.toASCII $s rfl)
  else
    Lean.Macro.throwError "expected ASCII string"

instance : Repr ASCII.String where
  reprPrec s _ := s!"a{repr s.toUnicode}"
