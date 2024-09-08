/-
Copyright (c) 2024 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

import Mathlib.Init.Set
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite

/-!
On page 2 of the paper
`An Algebraic Weak Factorisation System on 01-Substitution Sets: A Constructive Proof`
by ANDREW SWAN, JLA 2016,
Perm(𝔸) is the set of all finite permutations of 𝔸, i.e.,
the set of permutations π such that π a = a for all but finitely many a.
We show that Perm(𝔸) is closed under composition and contains the identity.
-/

/-- The set of all finite permutations of A, i.e.,
the set of permutations π such that π a = a for all but finitely many a. -/
def FinPerm (A : Type) : Set (A → A) := λ f ↦ Function.Bijective f ∧ Finite ({a | f a ≠ a})

/-- Perm(A) is closed under composition. -/
theorem FinPerm_comp {A : Type} (f g : FinPerm A) : (f.1 ∘ g.1) ∈ FinPerm A :=
  ⟨Function.Bijective.comp f.2.1 g.2.1, by
    have hf := f.2.2
    have hg := g.2.2
    have hf' : Finite ({a | f.1 (g.1 a) ≠ g.1 a}) := by
      let G : {a | f.1 (g.1 a) ≠ g.1 a} → {a | f.1 a ≠ a} := λ a ↦ ⟨g.1 a, a.2⟩
      exact Finite.of_injective G
        (fun _ _ h => SetCoe.ext <| g.2.1.1 <| congrArg Subtype.val h)
    have h₀: { a | (f.1 ∘ g.1) a ≠ a}
           ⊆ { a | g.1 a ≠ a} ∪ {a | f.1 (g.1 a) ≠ g.1 a} := by
      intro a h
      contrapose h
      simp_all only [ne_eq, Set.coe_setOf, Set.mem_union, Set.mem_setOf_eq, not_or, not_not,
        Function.comp_apply]
      exact  h.1 ▸ h.2
    exact Finite.Set.subset _ h₀⟩

/-- The identity is a finite permutation. -/
theorem id_FinPerm {A : Type} : id ∈ FinPerm A :=
  ⟨Function.bijective_id, by
    simp only [id_eq, ne_eq, not_true_eq_false, Set.setOf_false]
    apply Finite.of_fintype⟩
