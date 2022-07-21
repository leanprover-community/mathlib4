import Mathlib.Tactic.Inhabit

-- Most basic test (prop)
noncomputable example {p : Prop} [Nonempty p] : Inhabited p := by
  inhabit p
  assumption

-- Most basic test (nonprop)
noncomputable example {α : Type} [Nonempty α] : Inhabited α := by
  inhabit α
  assumption

-- Confirms inhabit can handle higher type universes
noncomputable example {α : Type 3} [Nonempty α] : Inhabited α := by
  inhabit α
  assumption

-- Confirms that inhabit can find Nonempty instances even if they're in the local context
noncomputable example {α : Type} : Nonempty α → Inhabited α := by
  intro nonempty_α
  inhabit α
  assumption

-- Confirms that inhabit assigns to the correct name when given one
noncomputable example {p : Prop} [Nonempty p] : Inhabited p := by
  inhabit p_inhabited : p
  exact p_inhabited

axiom α : Type
axiom a : α
instance : Nonempty α := Nonempty.intro a

-- Confirms that inhabit can find Nonempty instances that aren't in the local context
noncomputable example : Inhabited α := by
  inhabit α
  assumption
