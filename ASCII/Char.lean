/-
Copyright © 2023 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ASCII.Prelude

namespace ASCII

/-- ASCII character type -/
structure Char where
  /-- Byte value -/
  toByte : UInt8
  /-- Validity: only 7 bits -/
  valid : toByte < 128
deriving DecidableEq

instance : Inhabited ASCII.Char := ⟨⟨0, Nat.zero_lt_succ _⟩⟩

namespace Char

@[ext]
protected theorem ext : {a b : Char} → a.toByte = b.toByte → a = b
  | ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

/-- Underlying ASCII code point as a `Nat` -/
abbrev toNat (c : Char) := c.toByte.toNat

theorem toNat_lt (c : Char) : c.toNat < 128 := c.valid

/-- Pack a `Nat` into an ASCII character -/
@[extern "lean_uint8_of_nat"]
def ofNatAux (n : @&Nat) (h : n < 128) : Char := ⟨⟨n, Nat.lt_trans h (of_decide_eq_true rfl)⟩, h⟩

/-- Convert a `Nat` into an ASCII character

  Returns `ASCII.nul` if the `Nat` does not encode a valid ASCII character. -/
@[noinline, match_pattern]
def ofNat (n : Nat) : Char := if h : n < 128 then ofNatAux n h else default

/-- Coerce an ASCII character into a Unicode character -/
@[coe, extern "lean_uint8_to_uint32"]
protected def toUnicode (c : @&Char) : Unicode.Char where
  val := c.toByte.toUInt32
  valid := Or.inl <| c.toByte.toUInt32_toNat ▸ Nat.lt_trans c.toNat_lt (of_decide_eq_true rfl)

instance : Coe ASCII.Char Unicode.Char := ⟨ASCII.Char.toUnicode⟩

/-- Coerce a Unicode character into an ASCII character -/
@[extern "lean_uint32_to_uint8"]
def ofUnicode (c : @&Unicode.Char) (h : c.isASCII) : ASCII.Char where
  toByte := c.val.toUInt8
  valid :=
    have h128 : c.toNat < 128 := of_decide_eq_true h
    have h256 : c.toNat < 256 := Nat.lt_trans h128 (of_decide_eq_true rfl)
    show c.toNat % 256 < 128 by rw [Nat.mod_eq_of_lt h256]; exact h128
alias _root_.Char.toASCII := ofUnicode

@[inherit_doc ofUnicode]
def ofUnicode? (c : Unicode.Char) : Option ASCII.Char :=
  if h : c.isASCII then ofUnicode c h else none
alias _root_.Char.toASCII? := ofUnicode?

@[inherit_doc ofUnicode]
def ofUnicode! (c : Unicode.Char) : ASCII.Char :=
  if h : c.isASCII then ofUnicode c h else panic! "character not in ASCII range"
alias _root_.Char.toASCII! := ofUnicode!

instance : Repr ASCII.Char where
  reprPrec char prec :=
    Repr.addAppParen
      (Std.Format.group
        (Std.Format.nest (if prec >= max_prec then 1 else 2)
          (Std.Format.text "ASCII.Char.ofNat" ++
            Std.Format.line ++
            reprArg char.toNat)))
      prec

instance : ToString ASCII.Char where
  toString char := char.toUnicode.toString

/-! ## Character Properties -/

/-- Control character -/
@[inline] def isCntrl (c : Char) :=
  c.toByte < 32 || c.toByte == 127

/-- Spacing character -/
@[inline] def isSpace (c : Char) :=
  c.toByte == 32 || 9 ≤ c.toByte && c.toByte ≤ 13

/-- Blank character -/
@[inline] def isBlank (c : Char) :=
  c.toByte == 32 || c.toByte == 9

/-- Decimal digit -/
@[inline] def isDigit (c : Char) :=
  48 ≤ c.toByte && c.toByte ≤ 57

/-- Hexadecimal digit -/
@[inline] def isXDigit (c : Char) :=
  48 ≤ c.toByte && (c.toByte ≤ 57 ||
    65 ≤ c.toByte && (c.toByte ≤ 70 ||
      97 ≤ c.toByte && c.toByte ≤ 102))

/-- Lowercase letter -/
@[inline] def isLower (c : Char) :=
  97 ≤ c.toByte && c.toByte ≤ 122

/-- Uppercase letter -/
@[inline] def isUpper (c : Char) :=
  65 ≤ c.toByte && c.toByte ≤ 90

/-- Alphabetic letter -/
@[inline] def isAlpha (c : Char) :=
  65 ≤ c.toByte && (c.toByte ≤ 90 ||
    97 ≤ c.toByte && c.toByte ≤ 122)

/-- Alphabetic letter or decimal digit -/
@[inline] def isAlnum (c : Char) :=
  48 ≤ c.toByte && (c.toByte ≤ 57 ||
    65 ≤ c.toByte && (c.toByte ≤ 90 ||
      97 ≤ c.toByte && c.toByte ≤ 122))

/-- Punctuation character -/
@[inline] def isPunct (c : Char) :=
  33 ≤ c.toByte && (c.toByte ≤ 47 ||
    58 ≤ c.toByte && (c.toByte ≤ 64 ||
      91 ≤ c.toByte && (c.toByte ≤ 96 ||
        123 ≤ c.toByte && c.toByte ≤ 126)))

/-- Graphical character -/
@[inline] def isGraph (c : Char) :=
  0x21 ≤ c.toByte && c.toByte ≤ 0x7E

/-- Printable character -/
@[inline] def isPrint (c : Char) :=
  0x20 ≤ c.toByte && c.toByte ≤ 0x7E

/-! ## Case Conversion -/

def toLower (c : Char) : Char :=
  if h : c.isUpper then
    have h : c.toNat + 32 < 128 := by
      simp [isUpper] at h
      have hr : c.toNat ≤ 90 := h.2
      apply Nat.add_lt_of_lt_sub
      apply Nat.lt_of_le_of_lt hr
      decide
    .ofNatAux _ h
  else c

def toUpper (c : Char) : Char :=
  if h : c.isLower then
    have h : c.toNat - 32 < 128 := by
      simp [isLower] at h
      have hl : 97 ≤ c.toNat := h.1
      apply Nat.sub_lt_left_of_lt_add
      · apply Nat.le_trans _ hl; decide
      · apply Nat.lt_of_lt_of_le c.toNat_lt _; decide
    .ofNatAux _ h
  else c

/-! ## Control Characters -/

/-- Null character (ASCII NUL) -/
protected def nul : Char := ⟨0x00, of_decide_eq_true rfl⟩

/-- Start of Heading (ASCII SOH) -/
protected def soh : Char := ⟨0x01, of_decide_eq_true rfl⟩

/-- Start of Text (ASCII STX) -/
protected def stx : Char := ⟨0x02, of_decide_eq_true rfl⟩

/-- End of Text (ASCII ETX) -/
protected def etx : Char := ⟨0x03, of_decide_eq_true rfl⟩

/-- End of Transmission (ASCII EOT) -/
protected def eot : Char := ⟨0x04, of_decide_eq_true rfl⟩

/-- Enquiry (ASCII ENQ) -/
protected def enq : Char := ⟨0x05, of_decide_eq_true rfl⟩

/-- Acknowledge (ASCII ACK) -/
protected def ack : Char := ⟨0x06, of_decide_eq_true rfl⟩

/-- Bell, Alert (ASCII BEL) -/
protected def bel : Char := ⟨0x07, of_decide_eq_true rfl⟩

/-- Backspace (ASCII BS) -/
protected def bs  : Char := ⟨0x08, of_decide_eq_true rfl⟩

/-- Horizontal Tab (ASCII HT) -/
protected def ht  : Char := ⟨0x09, of_decide_eq_true rfl⟩

/-- Line Feed (ASCII LF) -/
protected def lf  : Char := ⟨0x0A, of_decide_eq_true rfl⟩

/-- Vertical Tab (ASCII VT) -/
protected def vt  : Char := ⟨0x0B, of_decide_eq_true rfl⟩

/-- Form Feed (ASCII FF) -/
protected def ff  : Char := ⟨0x0C, of_decide_eq_true rfl⟩

/-- Carriage Return (ASCII CR) -/
protected def cr  : Char := ⟨0x0D, of_decide_eq_true rfl⟩

/-- Shift Out (ASCII SO) -/
protected def so  : Char := ⟨0x0E, of_decide_eq_true rfl⟩

/-- Shift In (ASCII SI) -/
protected def si  : Char := ⟨0x0F, of_decide_eq_true rfl⟩

/-- Data Link Escape (ASCII DLE) -/
protected def dle : Char := ⟨0x10, of_decide_eq_true rfl⟩

/-- Device Control One (ASCII DC1, ASCII XON) -/
protected def dc1 : Char := ⟨0x11, of_decide_eq_true rfl⟩
protected alias xon := Char.dc1

/-- Device Control Two (ASCII DC2) -/
protected def dc2 : Char := ⟨0x12, of_decide_eq_true rfl⟩

/-- Device Control Three (ASCII DC3, ASCII XOFF) -/
protected def dc3 : Char := ⟨0x13, of_decide_eq_true rfl⟩
protected alias xoff := Char.dc3

/-- Device Control Four (ASCII DC4) -/
protected def dc4 : Char := ⟨0x14, of_decide_eq_true rfl⟩

/-- Negative Acknowledge (ASCII NAK) -/
protected def nak : Char := ⟨0x15, of_decide_eq_true rfl⟩

/-- Synchronous Idle (ASCII SYN) -/
protected def syn : Char := ⟨0x16, of_decide_eq_true rfl⟩

/-- End of Transmission Block (ASCII ETB) -/
protected def etb : Char := ⟨0x17, of_decide_eq_true rfl⟩

/-- Cancel (ASCII CAN) -/
protected def can : Char := ⟨0x18, of_decide_eq_true rfl⟩

/-- End of medium (ASCII EM) -/
protected def em  : Char := ⟨0x19, of_decide_eq_true rfl⟩

/-- Substitute (ASCII SUB) -/
protected def sub : Char := ⟨0x1A, of_decide_eq_true rfl⟩

/-- Escape (ASCII ESC) -/
protected def esc : Char := ⟨0x1B, of_decide_eq_true rfl⟩

/-- File Separator (ASCII FS) -/
protected def fs  : Char := ⟨0x1C, of_decide_eq_true rfl⟩

/-- Group Separator (ASCII GS) -/
protected def gs  : Char := ⟨0x1D, of_decide_eq_true rfl⟩

/-- Record Separator (ASCII RS) -/
protected def rs  : Char := ⟨0x1E, of_decide_eq_true rfl⟩

/-- Unit Separator (ASCII US) -/
protected def us  : Char := ⟨0x1F, of_decide_eq_true rfl⟩

/-- Space (ASCII SP) -/
protected def sp  : Char := ⟨0x20, of_decide_eq_true rfl⟩

/-- Delete (ASCII DEL) -/
protected def del : Char := ⟨0x7F, of_decide_eq_true rfl⟩
