/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.Group.UniqueProds
import Mathlib.Data.Finsupp.Lex
import Mathlib.Order.Extension.Linear
import Mathlib.LinearAlgebra.Basis.VectorSpace

#align_import algebra.monoid_algebra.no_zero_divisors from "leanprover-community/mathlib"@"3e067975886cf5801e597925328c335609511b1a"

/-!
# Variations on non-zero divisors in `AddMonoidAlgebra`s

This file studies the interaction between typeclass assumptions on two Types `R` and `A` and
whether `AddMonoidAlgebra R A` has non-zero zero-divisors.  For some background on related
questions, see [Kaplansky's Conjectures](https://en.wikipedia.org/wiki/Kaplansky%27s_conjectures),
especially the *zero divisor conjecture*.

_Conjecture._
Let `K` be a field, and `G` a torsion-free group. The group ring `K[G]` does not contain
nontrivial zero divisors, that is, it is a domain.

We formalize in this file the well-known result that if `R` is a field and `A` is a left-ordered
group, then `R[A]` contains no non-zero zero-divisors.  Some of these assumptions can be trivially
weakened: below we mention what assumptions are sufficient for the proofs in this file.

##  Main results

* `NoZeroDivisors.of_left_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add right cancel semigroup with strictly monotone
  left addition, then `AddMonoidAlgebra R A` has no non-zero zero-divisors.
* `NoZeroDivisors.of_right_ordered` shows that if `R` is a semiring with no non-zero
  zero-divisors, `A` is a linearly ordered, add left cancel semigroup with strictly monotone
  right addition, then `AddMonoidAlgebra R A` has no non-zero zero-divisors.

The conditions on `A` imposed in `NoZeroDivisors.of_left_ordered` are sometimes referred to as
`left-ordered`.
The conditions on `A` imposed in `NoZeroDivisors.of_right_ordered` are sometimes referred to as
`right-ordered`.

These conditions are sufficient, but not necessary.  As mentioned above, *Kaplansky's Conjecture*
asserts that `A` being torsion-free may be enough.
-/


namespace AddMonoidAlgebra

open Finsupp

instance {L σ : Type*} [LinearOrder σ] [LinearOrder L] [AddGroup L]
    [ContravariantClass L L (· + ·) (· ≤ ·)]
    [CovariantClass L L (Function.swap (· + ·)) (· ≤ ·)] :
    UniqueSums (σ →₀ L) := show UniqueSums ((Lex (σ →₀ L))) from
  { uniqueAdd_of_nonempty := fun {A B} A0 B0 => by
      refine ⟨_, A.max'_mem A0, _, B.max'_mem B0, ?_⟩
      intros a b aA bB
      exact (add_eq_add_iff_eq_and_eq (A.le_max' a aA) (B.le_max' b bB)).mp }

variable {R A : Type*} [Semiring R]

/-- The coefficient of a monomial in a product `f * g` that can be reached in at most one way
as a product of monomials in the supports of `f` and `g` is a product. -/
theorem mul_apply_add_eq_mul_of_uniqueAdd [Add A] {f g : AddMonoidAlgebra R A} {a0 b0 : A}
    (h : UniqueAdd f.support g.support a0 b0) :
    (f * g) (a0 + b0) = f a0 * g b0 := by
  classical
  simp_rw [mul_apply, sum, ← Finset.sum_product']
  refine' (Finset.sum_eq_single (a0, b0) _ _).trans (if_pos rfl) <;> simp_rw [Finset.mem_product]
  · refine fun ab hab hne => if_neg (fun he => hne <| Prod.ext ?_ ?_)
    exacts [(h hab.1 hab.2 he).1, (h hab.1 hab.2 he).2]
  · refine fun hnmem => ite_eq_right_iff.mpr (fun _ => ?_)
    rcases not_and_or.mp hnmem with af | bg
    · rw [not_mem_support_iff.mp af, zero_mul]
    · rw [not_mem_support_iff.mp bg, mul_zero]

instance {A : Type*} [NoZeroDivisors R] [Add A] [UniqueSums A] :
    NoZeroDivisors (AddMonoidAlgebra R A) where
  eq_zero_or_eq_zero_of_mul_eq_zero := fun {a b} ab => by
    contrapose! ab
    obtain ⟨da, a0, db, b0, h⟩ := UniqueSums.uniqueAdd_of_nonempty
      (support_nonempty_iff.mpr ab.1) (support_nonempty_iff.mpr ab.2)
    refine support_nonempty_iff.mp ⟨da + db, ?_⟩
    rw [mem_support_iff] at a0 b0 ⊢
    exact mul_apply_add_eq_mul_of_uniqueAdd h ▸ mul_ne_zero a0 b0

/- TODO: MonoidAlgebra versions -/

/-- The proof goes via the equivalence `R ≃ₗ[ℚ] (Basis.ofVectorSpaceIndex ℚ R) →₀ ℚ`,
i.e. choosing a basis.
Once we have a basis, we use the Lexicographic order on the coordinates and all the instances
that `ℚ` already has.
-/
instance {R : Type*} [AddCommGroup R] [Module ℚ R] : UniqueSums R :=
  -- We first setup the relevant instances on (Basis.ofVectorSpaceIndex ℚ R) →₀ ℚ
  -- Endow it with the "trivial" PartialOrder `(· = ·)`
  let _ : PartialOrder (Basis.ofVectorSpaceIndex ℚ R) :=
  { le := (· = ·)
    le_refl := fun a ↦ rfl
    le_trans := fun _ _ _ => Eq.trans
    le_antisymm := fun a b ab _ => ab }
  -- Extend arbitrarily the trivial order to a `LinearOrder`
  let _ : LinearOrder ((Basis.ofVectorSpaceIndex ℚ R)) :=
    show LinearOrder (LinearExtension (Basis.ofVectorSpaceIndex ℚ R)) from inferInstance
  -- `r` is the equivalence of `R` with its "coordinates"
  let r := (Basis.ofVectorSpace ℚ R).repr
  UniqueSums.addHom_image_of_injective r r.injective inferInstance

end AddMonoidAlgebra
