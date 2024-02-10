
set_option autoImplicit true
example : False → α := nofun
example : False → α := by nofun
example : ¬ False := nofun
example : ¬ False := by nofun
example : ¬ ¬ 0 = 0 := nofun

example (h : False) : α := nomatch h

example (h : Nat → False) : Nat := nomatch h 1

def ComplicatedEmpty : Bool → Type
  | false => Empty
  | true => PEmpty

example (h : ComplicatedEmpty b) : α := nomatch b, h
example (h : Nat → ComplicatedEmpty b) : α := nomatch b, h 1
