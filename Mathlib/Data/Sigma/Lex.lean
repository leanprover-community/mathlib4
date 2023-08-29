/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Sigma.Basic
import Mathlib.Order.RelClasses

#align_import data.sigma.lex from "leanprover-community/mathlib"@"41cf0cc2f528dd40a8f2db167ea4fb37b8fde7f3"

/-!
# Lexicographic order on a sigma type

This defines the lexicographical order of two arbitrary relations on a sigma type and proves some
lemmas about `PSigma.Lex`, which is defined in core Lean.

Given a relation in the index type and a relation on each summand, the lexicographical order on the
sigma type relates `a` and `b` if their summands are related or they are in the same summand and
related by the summand's relation.

## See also

Related files are:
* `Combinatorics.CoLex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Sigma.Order`: Lexicographic order on `Σ i, α i` per say.
* `Data.PSigma.Order`: Lexicographic order on `Σ' i, α i`.
* `Data.Prod.Lex`: Lexicographic order on `α × β`. Can be thought of as the special case of
  `Sigma.Lex` where all summands are the same
-/


namespace Sigma

variable {ι : Type*} {α : ι → Type*} {r r₁ r₂ : ι → ι → Prop} {s s₁ s₂ : ∀ i, α i → α i → Prop}
  {a b : Σ i, α i}

/-- The lexicographical order on a sigma type. It takes in a relation on the index type and a
relation for each summand. `a` is related to `b` iff their summands are related or they are in the
same summand and are related through the summand's relation. -/
inductive Lex (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) : ∀ _ _ : Σ i, α i, Prop
  | left {i j : ι} (a : α i) (b : α j) : r i j → Lex r s ⟨i, a⟩ ⟨j, b⟩
  | right {i : ι} (a b : α i) : s i a b → Lex r s ⟨i, a⟩ ⟨i, b⟩
#align sigma.lex Sigma.Lex

theorem lex_iff : Lex r s a b ↔ r a.1 b.1 ∨ ∃ h : a.1 = b.1, s b.1 (h.rec a.2) b.2 := by
  constructor
  -- ⊢ Lex r s a b → r a.fst b.fst ∨ ∃ h, s b.fst (h ▸ a.snd) b.snd
  · rintro (⟨a, b, hij⟩ | ⟨a, b, hab⟩)
    -- ⊢ r { fst := i✝, snd := a }.fst { fst := j✝, snd := b }.fst ∨ ∃ h, s { fst :=  …
    · exact Or.inl hij
      -- 🎉 no goals
    · exact Or.inr ⟨rfl, hab⟩
      -- 🎉 no goals
  · obtain ⟨i, a⟩ := a
    -- ⊢ (r { fst := i, snd := a }.fst b.fst ∨ ∃ h, s b.fst (h ▸ { fst := i, snd := a …
    obtain ⟨j, b⟩ := b
    -- ⊢ (r { fst := i, snd := a }.fst { fst := j, snd := b }.fst ∨ ∃ h, s { fst := j …
    dsimp only
    -- ⊢ (r i j ∨ ∃ h, s j (h ▸ a) b) → Lex r s { fst := i, snd := a } { fst := j, sn …
    rintro (h | ⟨rfl, h⟩)
    -- ⊢ Lex r s { fst := i, snd := a } { fst := j, snd := b }
    · exact Lex.left _ _ h
      -- 🎉 no goals
    · exact Lex.right _ _ h
      -- 🎉 no goals
#align sigma.lex_iff Sigma.lex_iff

instance Lex.decidable (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) [DecidableEq ι]
    [DecidableRel r] [∀ i, DecidableRel (s i)] : DecidableRel (Lex r s) := fun _ _ =>
  decidable_of_decidable_of_iff lex_iff.symm
#align sigma.lex.decidable Sigma.Lex.decidable

theorem Lex.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ i, α i}
    (h : Lex r₁ s₁ a b) : Lex r₂ s₂ a b := by
  obtain ⟨a, b, hij⟩ | ⟨a, b, hab⟩ := h
  -- ⊢ Lex r₂ s₂ { fst := i✝, snd := a } { fst := j✝, snd := b }
  · exact Lex.left _ _ (hr _ _ hij)
    -- 🎉 no goals
  · exact Lex.right _ _ (hs _ _ _ hab)
    -- 🎉 no goals
#align sigma.lex.mono Sigma.Lex.mono

theorem Lex.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) {a b : Σ i, α i} (h : Lex r₁ s a b) :
    Lex r₂ s a b :=
  h.mono hr $ fun _ _ _ => id
#align sigma.lex.mono_left Sigma.Lex.mono_left

theorem Lex.mono_right (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ i, α i} (h : Lex r s₁ a b) :
    Lex r s₂ a b :=
  h.mono (fun _ _ => id) hs
#align sigma.lex.mono_right Sigma.Lex.mono_right

theorem lex_swap : Lex (Function.swap r) s a b ↔ Lex r (fun i => Function.swap (s i)) b a := by
  constructor <;>
  -- ⊢ Lex (Function.swap r) s a b → Lex r (fun i => Function.swap (s i)) b a
    · rintro (⟨a, b, h⟩ | ⟨a, b, h⟩)
      -- ⊢ Lex r (fun i => Function.swap (s i)) { fst := j✝, snd := b } { fst := i✝, sn …
      -- ⊢ Lex (Function.swap r) s { fst := j✝, snd := b } { fst := i✝, snd := a }
      -- 🎉 no goals
      exacts [Lex.left _ _ h, Lex.right _ _ h]
      -- 🎉 no goals
#align sigma.lex_swap Sigma.lex_swap

instance [∀ i, IsRefl (α i) (s i)] : IsRefl _ (Lex r s) :=
  ⟨fun ⟨_, _⟩ => Lex.right _ _ $ refl _⟩

instance [IsIrrefl ι r] [∀ i, IsIrrefl (α i) (s i)] : IsIrrefl _ (Lex r s) :=
  ⟨by
    rintro _ (⟨a, b, hi⟩ | ⟨a, b, ha⟩)
    -- ⊢ False
    · exact irrefl _ hi
      -- 🎉 no goals
    · exact irrefl _ ha
      -- 🎉 no goals
      ⟩

instance [IsTrans ι r] [∀ i, IsTrans (α i) (s i)] : IsTrans _ (Lex r s) :=
  ⟨by
    rintro _ _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩) (⟨_, c, hk⟩ | ⟨_, c, hc⟩)
    · exact Lex.left _ _ (_root_.trans hij hk)
      -- 🎉 no goals
    · exact Lex.left _ _ hij
      -- 🎉 no goals
    · exact Lex.left _ _ hk
      -- 🎉 no goals
    · exact Lex.right _ _ (_root_.trans hab hc)⟩
      -- 🎉 no goals

instance [IsSymm ι r] [∀ i, IsSymm (α i) (s i)] : IsSymm _ (Lex r s) :=
  ⟨by
    rintro _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩)
    -- ⊢ Lex r s { fst := j✝, snd := b } { fst := i✝, snd := a }
    · exact Lex.left _ _ (symm hij)
      -- 🎉 no goals
    · exact Lex.right _ _ (symm hab)
      -- 🎉 no goals
      ⟩

attribute [local instance] IsAsymm.isIrrefl

instance [IsAsymm ι r] [∀ i, IsAntisymm (α i) (s i)] : IsAntisymm _ (Lex r s) :=
  ⟨by
    rintro _ _ (⟨a, b, hij⟩ | ⟨a, b, hab⟩) (⟨_, _, hji⟩ | ⟨_, _, hba⟩)
    · exact (asymm hij hji).elim
      -- 🎉 no goals
    · exact (irrefl _ hij).elim
      -- 🎉 no goals
    · exact (irrefl _ hji).elim
      -- 🎉 no goals
    · exact ext rfl (heq_of_eq $ antisymm hab hba)⟩
      -- 🎉 no goals

instance [IsTrichotomous ι r] [∀ i, IsTotal (α i) (s i)] : IsTotal _ (Lex r s) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩
    -- ⊢ Lex r s { fst := i, snd := a } { fst := j, snd := b } ∨ Lex r s { fst := j,  …
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (Lex.left _ _ hij)
      -- 🎉 no goals
    · obtain hab | hba := total_of (s i) a b
      -- ⊢ Lex r s { fst := i, snd := a } { fst := i, snd := b } ∨ Lex r s { fst := i,  …
      · exact Or.inl (Lex.right _ _ hab)
        -- 🎉 no goals
      · exact Or.inr (Lex.right _ _ hba)
        -- 🎉 no goals
    · exact Or.inr (Lex.left _ _ hji)⟩
      -- 🎉 no goals

instance [IsTrichotomous ι r] [∀ i, IsTrichotomous (α i) (s i)] : IsTrichotomous _ (Lex r s) :=
  ⟨by
    rintro ⟨i, a⟩ ⟨j, b⟩
    -- ⊢ Lex r s { fst := i, snd := a } { fst := j, snd := b } ∨ { fst := i, snd := a …
    obtain hij | rfl | hji := trichotomous_of r i j
    · exact Or.inl (Lex.left _ _ hij)
      -- 🎉 no goals
    · obtain hab | rfl | hba := trichotomous_of (s i) a b
      · exact Or.inl (Lex.right _ _ hab)
        -- 🎉 no goals
      · exact Or.inr (Or.inl rfl)
        -- 🎉 no goals
      · exact Or.inr (Or.inr $ Lex.right _ _ hba)
        -- 🎉 no goals
    · exact Or.inr (Or.inr $ Lex.left _ _ hji)⟩
      -- 🎉 no goals

end Sigma

/-! ### `PSigma` -/


namespace PSigma

variable {ι : Sort*} {α : ι → Sort*} {r r₁ r₂ : ι → ι → Prop} {s s₁ s₂ : ∀ i, α i → α i → Prop}

theorem lex_iff {a b : Σ' i, α i} :
    Lex r s a b ↔ r a.1 b.1 ∨ ∃ h : a.1 = b.1, s b.1 (h.rec a.2) b.2 := by
  constructor
  -- ⊢ Lex r s a b → r a.fst b.fst ∨ ∃ h, s b.fst (h ▸ a.snd) b.snd
  · rintro (⟨a, b, hij⟩ | ⟨i, hab⟩)
    -- ⊢ r { fst := a₁✝, snd := a }.fst { fst := a₂✝, snd := b }.fst ∨ ∃ h, s { fst : …
    · exact Or.inl hij
      -- 🎉 no goals
    · exact Or.inr ⟨rfl, hab⟩
      -- 🎉 no goals
  · obtain ⟨i, a⟩ := a
    -- ⊢ (r { fst := i, snd := a }.fst b.fst ∨ ∃ h, s b.fst (h ▸ { fst := i, snd := a …
    obtain ⟨j, b⟩ := b
    -- ⊢ (r { fst := i, snd := a }.fst { fst := j, snd := b }.fst ∨ ∃ h, s { fst := j …
    dsimp only
    -- ⊢ (r i j ∨ ∃ h, s j (h ▸ a) b) → Lex r s { fst := i, snd := a } { fst := j, sn …
    rintro (h | ⟨rfl, h⟩)
    -- ⊢ Lex r s { fst := i, snd := a } { fst := j, snd := b }
    · exact Lex.left _ _ h
      -- 🎉 no goals
    · exact Lex.right _ h
      -- 🎉 no goals
#align psigma.lex_iff PSigma.lex_iff

instance Lex.decidable (r : ι → ι → Prop) (s : ∀ i, α i → α i → Prop) [DecidableEq ι]
    [DecidableRel r] [∀ i, DecidableRel (s i)] : DecidableRel (Lex r s) := fun _ _ =>
  decidable_of_decidable_of_iff lex_iff.symm
#align psigma.lex.decidable PSigma.Lex.decidable

theorem Lex.mono {r₁ r₂ : ι → ι → Prop} {s₁ s₂ : ∀ i, α i → α i → Prop}
  (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ' i, α i}
    (h : Lex r₁ s₁ a b) : Lex r₂ s₂ a b := by
  obtain ⟨a, b, hij⟩ | ⟨i, hab⟩ := h
  -- ⊢ Lex r₂ s₂ { fst := a₁✝, snd := a } { fst := a₂✝, snd := b }
  · exact Lex.left _ _ (hr _ _ hij)
    -- 🎉 no goals
  · exact Lex.right _ (hs _ _ _ hab)
    -- 🎉 no goals
#align psigma.lex.mono PSigma.Lex.mono

theorem Lex.mono_left {r₁ r₂ : ι → ι → Prop} {s : ∀ i, α i → α i → Prop}
    (hr : ∀ a b, r₁ a b → r₂ a b) {a b : Σ' i, α i} (h : Lex r₁ s a b) : Lex r₂ s a b :=
  h.mono hr $ fun _ _ _ => id
#align psigma.lex.mono_left PSigma.Lex.mono_left

theorem Lex.mono_right {r : ι → ι → Prop} {s₁ s₂ : ∀ i, α i → α i → Prop}
    (hs : ∀ i a b, s₁ i a b → s₂ i a b) {a b : Σ' i, α i} (h : Lex r s₁ a b) : Lex r s₂ a b :=
  h.mono (fun _ _ => id) hs
#align psigma.lex.mono_right PSigma.Lex.mono_right

end PSigma
