/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Hom.End
public import Mathlib.Algebra.MonoidAlgebra.Defs

/-!
# Division of `AddMonoidAlgebra` by monomials

This file is most important for when `G = ℕ` (polynomials) or `G = σ →₀ ℕ` (multivariate
polynomials).

In order to apply in maximal generality (such as for `LaurentPolynomial`s), this uses
`∃ d, g' = g + d` in many places instead of `g ≤ g'`.

## Main definitions

* `AddMonoidAlgebra.divOf x g`: divides `x` by the monomial `AddMonoidAlgebra.of k G g`
* `AddMonoidAlgebra.modOf x g`: the remainder upon dividing `x` by the monomial
  `AddMonoidAlgebra.of k G g`.

## Main results

* `AddMonoidAlgebra.divOf_add_modOf`, `AddMonoidAlgebra.modOf_add_divOf`: `divOf` and
  `modOf` are well-behaved as quotient and remainder operators.

## Implementation notes

`∃ d, g' = g + d` is used as opposed to some other permutation up to commutativity in order to match
the definition of `semigroupDvd`. The results in this file could be duplicated for
`MonoidAlgebra` by using `g ∣ g'`, but this can't be done automatically, and in any case is not
likely to be very useful.

-/

@[expose] public section


variable {k G : Type*} [Semiring k]

namespace AddMonoidAlgebra

section

variable [AddCommMonoid G]

/-- Divide by `of' k G g`, discarding terms not divisible by this. -/
noncomputable def divOf [IsCancelAdd G] (x : k[G]) (g : G) : k[G] where
  -- note: comapping by `+ g` has the effect of subtracting `g` from every element in
  -- the support, and discarding the elements of the support from which `g` can't be subtracted.
  -- If `G` is an additive group, such as `ℤ` when used for `LaurentPolynomial`,
  -- then no discarding occurs.
  coeff := x.coeff.comapDomain (g + ·) (add_right_injective g).injOn

local infixl:70 " /ᵒᶠ " => divOf

section divOf
variable [IsCancelAdd G]

@[simp] lemma coeff_divOf (g : G) (x : k[G]) (g' : G) : (x /ᵒᶠ g).coeff g' = x.coeff (g + g') := rfl

@[deprecated (since := "2025-12-08")] alias divOf_apply := coeff_divOf

@[simp]
theorem support_coeff_divOf (g : G) (x : k[G]) :
    (x /ᵒᶠ g).coeff.support = x.coeff.support.preimage (g + ·) (add_right_injective g).injOn :=
  rfl

@[deprecated (since := "2025-12-08")] alias support_divOf := support_coeff_divOf

@[simp]
theorem zero_divOf (g : G) : (0 : k[G]) /ᵒᶠ g = 0 := by ext; simp

@[simp]
theorem divOf_zero (x : k[G]) : x /ᵒᶠ 0 = x := by ext; simp

theorem add_divOf (x y : k[G]) (g : G) : (x + y) /ᵒᶠ g = x /ᵒᶠ g + y /ᵒᶠ g := by ext; simp

theorem divOf_add (x : k[G]) (a b : G) : x /ᵒᶠ (a + b) = x /ᵒᶠ a /ᵒᶠ b := by ext; simp [add_assoc]

/-- A bundled version of `AddMonoidAlgebra.divOf`. -/
@[simps]
noncomputable def divOfHom : Multiplicative G →* AddMonoid.End k[G] where
  toFun g :=
    { toFun := fun x => divOf x g.toAdd
      map_zero' := zero_divOf _
      map_add' := fun x y => add_divOf x y g.toAdd }
  map_one' := AddMonoidHom.ext divOf_zero
  map_mul' g₁ g₂ :=
    AddMonoidHom.ext fun _x =>
      (congr_arg _ (add_comm g₁.toAdd g₂.toAdd)).trans
        (divOf_add _ _ _)

theorem of'_mul_divOf (a : G) (x : k[G]) : of' k G a * x /ᵒᶠ a = x := by
  ext; simp only [of'_apply, coeff_divOf, coeff_single_mul_add, one_mul]

theorem mul_of'_divOf (x : k[G]) (a : G) : x * of' k G a /ᵒᶠ a = x := by
  ext; simp only [of'_apply, coeff_divOf, add_comm a, coeff_mul_single_add, mul_one]

theorem of'_divOf (a : G) : of' k G a /ᵒᶠ a = 1 := by
  simpa only [one_mul] using mul_of'_divOf (1 : k[G]) a

end divOf

/-- The remainder upon division by `of' k G g`. -/
noncomputable def modOf (x : k[G]) (g : G) : k[G] :=
  letI := Classical.decPred fun g₁ => ∃ g₂, g₁ = g + g₂
  .ofCoeff <| x.coeff.filter fun g₁ => ¬∃ g₂, g₁ = g + g₂

local infixl:70 " %ᵒᶠ " => modOf

@[simp]
theorem coeff_modOf_of_not_exists_add (x : k[G]) (g : G) (g' : G) (h : ¬∃ d, g' = g + d) :
    (x %ᵒᶠ g).coeff g' = x.coeff g' := by
  classical exact Finsupp.filter_apply_pos _ _ h

@[simp]
theorem coeff_modOf_of_exists_add (x : k[G]) (g : G) (g' : G) (h : ∃ d, g' = g + d) :
    (x %ᵒᶠ g).coeff g' = 0 := by
  classical exact Finsupp.filter_apply_neg _ _ <| by rwa [Classical.not_not]

@[simp]
theorem coeff_modOf_add_self (x : k[G]) (g : G) (d : G) : (x %ᵒᶠ g).coeff (d + g) = 0 :=
  coeff_modOf_of_exists_add _ _ _ ⟨_, add_comm _ _⟩

theorem coeff_modOf_self_add (x : k[G]) (g : G) (d : G) : (x %ᵒᶠ g).coeff (g + d) = 0 :=
  coeff_modOf_of_exists_add _ _ _ ⟨_, rfl⟩

theorem of'_mul_modOf (g : G) (x : k[G]) : of' k G g * x %ᵒᶠ g = 0 := by
  ext g'
  simp only [of'_apply, coeff_zero, Finsupp.coe_zero, Pi.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  · rw [coeff_modOf_self_add]
  · rw [coeff_modOf_of_not_exists_add _ _ _ h, coeff_single_mul_of_forall_add_ne]
    simpa [eq_comm] using h

theorem mul_of'_modOf (x : k[G]) (g : G) : x * of' k G g %ᵒᶠ g = 0 := by
  ext g'
  simp only [of'_apply, coeff_zero, Finsupp.zero_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  · rw [coeff_modOf_self_add]
  · rw [coeff_modOf_of_not_exists_add _ _ _ h, coeff_mul_single_of_forall_add_ne]
    simpa [eq_comm, add_comm] using h

theorem of'_modOf (g : G) : of' k G g %ᵒᶠ g = 0 := by
  simpa only [one_mul] using mul_of'_modOf (1 : k[G]) g

theorem divOf_add_modOf [IsCancelAdd G] (x : k[G]) (g : G) :
    of' k G g * (x /ᵒᶠ g) + x %ᵒᶠ g = x := by
  ext g'
  dsimp only [coeff_add, of'_apply, Finsupp.add_apply]
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  · rw [coeff_modOf_self_add, add_zero, coeff_single_mul_add, one_mul, coeff_divOf]
  · rw [coeff_modOf_of_not_exists_add x _ _ h, coeff_single_mul_of_forall_add_ne, zero_add]
    simpa [eq_comm] using h

theorem modOf_add_divOf [IsCancelAdd G] (x : k[G]) (g : G) :
    x %ᵒᶠ g + of' k G g * (x /ᵒᶠ g) = x := by
  rw [add_comm, divOf_add_modOf]

theorem of'_dvd_iff_modOf_eq_zero [IsCancelAdd G] {x : k[G]} {g : G} :
    of' k G g ∣ x ↔ x %ᵒᶠ g = 0 := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [of'_mul_modOf]
  · intro h
    rw [← divOf_add_modOf x g, h, add_zero]
    exact dvd_mul_right _ _

end

end AddMonoidAlgebra
