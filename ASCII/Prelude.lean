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
