-- A module that provides only syntax: a scenario file uses the notation, and no constant of
-- this module reaches the environment of that file.
module

public section

/-! # A module that provides a notation -/

/-- A notation that expands to a numeral, so its expansion names no constant of this module. -/
notation "unneededImportAuxOne" => 1
