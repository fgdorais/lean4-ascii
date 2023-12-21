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
deriving DecidableEq, Repr

instance : Inhabited ASCII.Char := ⟨⟨0, Nat.zero_lt_succ _⟩⟩

namespace Char

@[ext]
protected theorem ext : {a b : Char} → a.toByte = b.toByte → a = b
  | ⟨_,_⟩, ⟨_,_⟩, rfl => rfl

/-- Underlying ASCII code point as a `Nat` -/
abbrev toNat (c : Char) := c.toByte.toNat

theorem toNat_lt (c : Char) : c.toNat < 128 := c.valid

/-- Coerce an ASCII character into a Unicode character -/
@[coe, extern "lean_uint8_to_uint32"]
protected def toUnicode (c : Char) : Unicode.Char where
  val := c.toByte.toUInt32
  valid := Or.inl <| c.toByte.toUInt32_toNat ▸ Nat.lt_trans c.toNat_lt (by decide)

instance : Coe ASCII.Char Unicode.Char := ⟨ASCII.Char.toUnicode⟩

/-- Coerce a Unicode character into an ASCII character -/
@[extern "lean_uint32_to_uint8"]
def ofUnicode (c : Unicode.Char) (h : c.isASCII) : ASCII.Char where
  toByte := c.val.toUInt8
  valid :=
    have h128 : c.toNat < 128 := of_decide_eq_true h
    have h256 : c.toNat < 256 := Nat.lt_trans h128 (by decide)
    show c.toNat % 256 < 128 by rw [Nat.mod_eq_of_lt h256]; exact h128
alias _root_.Char.toASCII := ofUnicode

@[inherit_doc ofUnicode]
def ofUnicode? (c : Unicode.Char) : Option ASCII.Char :=
  if h : c.isASCII then some (.ofUnicode c h) else none
alias _root_.Char.toASCII? := ofUnicode?

@[inherit_doc ofUnicode]
def ofUnicode! (c : Unicode.Char) : ASCII.Char :=
  if h : c.isASCII then .ofUnicode c h else panic! "character not in ASCII range"
alias _root_.Char.toASCII! := ofUnicode!

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

/-! ## Special Characters -/

/-- Null character (ASCII NUL) -/
protected def nul : Char := ⟨0x00, by decide⟩

/-- Start of Heading (ASCII SOH) -/
protected def soh : Char := ⟨0x01, by decide⟩

/-- Start of Text (ASCII STX) -/
protected def stx : Char := ⟨0x02, by decide⟩

/-- End of Text (ASCII ETX) -/
protected def etx : Char := ⟨0x03, by decide⟩

/-- End of Transmission (ASCII EOT) -/
protected def eot : Char := ⟨0x04, by decide⟩

/-- Enquiry (ASCII ENQ) -/
protected def enq : Char := ⟨0x05, by decide⟩

/-- Acknowledge (ASCII ACK) -/
protected def ack : Char := ⟨0x06, by decide⟩

/-- Bell, Alert (ASCII BEL) -/
protected def bel : Char := ⟨0x07, by decide⟩

/-- Backspace (ASCII BS) -/
protected def bs  : Char := ⟨0x08, by decide⟩

/-- Horizontal Tab (ASCII HT) -/
protected def ht  : Char := ⟨0x09, by decide⟩

/-- Line Feed (ASCII LF) -/
protected def lf  : Char := ⟨0x0A, by decide⟩

/-- Vertical Tab (ASCII VT) -/
protected def vt  : Char := ⟨0x0B, by decide⟩

/-- Form Feed (ASCII FF) -/
protected def ff  : Char := ⟨0x0C, by decide⟩

/-- Carriage Return (ASCII CR) -/
protected def cr  : Char := ⟨0x0D, by decide⟩

/-- Shift Out (ASCII SO) -/
protected def so  : Char := ⟨0x0E, by decide⟩

/-- Shift In (ASCII SI) -/
protected def si  : Char := ⟨0x0F, by decide⟩

/-- Data Link Escape (ASCII DLE) -/
protected def dle : Char := ⟨0x10, by decide⟩

/-- Device Control One (ASCII DC1, ASCII XON) -/
protected def dc1 : Char := ⟨0x11, by decide⟩
protected alias xon := Char.dc1

/-- Device Control Two (ASCII DC2) -/
protected def dc2 : Char := ⟨0x12, by decide⟩

/-- Device Control Three (ASCII DC3, ASCII XOFF) -/
protected def dc3 : Char := ⟨0x13, by decide⟩
protected alias xoff := Char.dc3

/-- Device Control Four (ASCII DC4) -/
protected def dc4 : Char := ⟨0x14, by decide⟩

/-- Negative Acknowledge (ASCII NAK) -/
protected def nak : Char := ⟨0x15, by decide⟩

/-- Synchronous Idle (ASCII SYN) -/
protected def syn : Char := ⟨0x16, by decide⟩

/-- End of Transmission Block (ASCII ETB) -/
protected def etb : Char := ⟨0x17, by decide⟩

/-- Cancel (ASCII CAN) -/
protected def can : Char := ⟨0x18, by decide⟩

/-- End of medium (ASCII EM) -/
protected def em  : Char := ⟨0x19, by decide⟩

/-- Substitute (ASCII SUB) -/
protected def sub : Char := ⟨0x1A, by decide⟩

/-- Escape (ASCII ESC) -/
protected def esc : Char := ⟨0x1B, by decide⟩

/-- File Separator (ASCII FS) -/
protected def fs  : Char := ⟨0x1C, by decide⟩

/-- Group Separator (ASCII GS) -/
protected def gs  : Char := ⟨0x1D, by decide⟩

/-- Record Separator (ASCII RS) -/
protected def rs  : Char := ⟨0x1E, by decide⟩

/-- Unit Separator (ASCII US) -/
protected def us  : Char := ⟨0x1F, by decide⟩

/-- Space (ASCII SP) -/
protected def sp  : Char := ⟨0x20, by decide⟩

/-- Delete (ASCII DEL) -/
protected def del : Char := ⟨0x7F, by decide⟩
