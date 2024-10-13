import Mathlib.Tactic.Inhabit

universe u

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

-- Test for the issue that required generalizing `nonempty_to_inhabited` to `Sort`.
section Unique

structure Unique (α : Sort u) extends Inhabited α where
  uniq : ∀ a : α, a = default

/-- Construct `unique` from `inhabited` and `subsingleton`. Making this an instance would create
a loop in the class inheritance graph. -/
abbrev Unique.mk' (α : Sort u) [h₁ : Inhabited α] [Subsingleton α] : Unique α :=
  { h₁ with uniq := fun _ => Subsingleton.elim _ _ }

noncomputable example {α : Sort u} [Subsingleton α] [Nonempty α] : Unique α := by
  inhabit α
  exact Unique.mk' α

end Unique

axiom α : Type
axiom a : α
instance : Nonempty α := Nonempty.intro a

-- Confirms that inhabit can find Nonempty instances that aren't in the local context
noncomputable example : Inhabited α := by
  inhabit α
  assumption
