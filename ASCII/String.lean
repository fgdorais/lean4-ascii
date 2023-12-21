import ASCII.Char

namespace ASCII

structure String where
  toByteArray : ByteArray
  valid (i : Fin toByteArray.size) : toByteArray[i] < 128

/-- Empty string -/
def String.empty : ASCII.String where
  toByteArray := .empty
  valid := (nomatch.)

instance : Inhabited String where
  default := .empty

/-- Length of a string -/
abbrev String.length (s : ASCII.String) := s.toByteArray.size

instance : GetElem String Nat Char fun s i => i < s.length where
  getElem s i h := ⟨s.toByteArray.get ⟨i, h⟩, s.valid ⟨i, h⟩⟩

/-- Coercion from ASCII string to Unicode string -/
@[coe, extern "lean_string_from_utf8_unchecked"]
def String.toUnicode (s : ASCII.String) : Unicode.String :=
  loop 0 (Nat.zero_le _) ""
where
  loop (i : Nat) (hi : i ≤ s.length) (r : Unicode.String) :=
    if h : i = s.length then r else
      have hi : i < s.length := Nat.lt_of_le_of_ne hi h
      loop (i + 1) (Nat.succ_le_of_lt hi) (r.push s[i])
termination_by loop => s.length - i

instance : Coe ASCII.String Unicode.String where
  coe := String.toUnicode

/-- Coerce a Unicode string into an ASCII string -/
@[extern "lean_string_to_utf8"]
opaque String.ofUnicode (s : Unicode.String) (h : s.isASCII) : ASCII.String
alias _root_.String.toASCII := String.ofUnicode

@[inherit_doc String.ofUnicode]
def String.ofUnicode? (s : Unicode.String) : Option ASCII.String :=
  if h : s.isASCII then some (.ofUnicode s h) else none
alias _root_.String.toASCII? := String.ofUnicode?

@[inherit_doc String.ofUnicode]
def String.ofUnicode! (s : Unicode.String) : ASCII.String :=
  if h : s.isASCII then .ofUnicode s h else panic! "characters out of ASCII range"
alias _root_.String.toASCII! := String.ofUnicode!

end ASCII

open Lean Parser in
/-- Syntax for ASCII string -/
syntax (name:=asciiStrLit) "a" noWs strLit : term

macro_rules
  | `(a$s) =>
    if s.getString.isASCII then
      `(String.toASCII! $s)
    else
      Lean.Macro.throwError "expected ASCII character"

instance : Repr ASCII.String where
  reprPrec s _ := s!"a{repr s.toUnicode}"