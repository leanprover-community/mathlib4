/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.Finsupp.Order

#align_import algebra.monoid_algebra.division from "leanprover-community/mathlib"@"72c366d0475675f1309d3027d3d7d47ee4423951"

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


variable {k G : Type*} [Semiring k]

namespace AddMonoidAlgebra

section

variable [AddCancelCommMonoid G]

/-- Divide by `of' k G g`, discarding terms not divisible by this. -/
noncomputable def divOf (x : AddMonoidAlgebra k G) (g : G) : AddMonoidAlgebra k G :=
  -- note: comapping by `+ g` has the effect of subtracting `g` from every element in
  -- the support, and discarding the elements of the support from which `g` can't be subtracted.
  -- If `G` is an additive group, such as `ℤ` when used for `LaurentPolynomial`,
  -- then no discarding occurs.
  @Finsupp.comapDomain.addMonoidHom _ _ _ _ ((· + ·) g) (add_right_injective g) x
#align add_monoid_algebra.div_of AddMonoidAlgebra.divOf

local infixl:70 " /ᵒᶠ " => divOf

@[simp]
theorem divOf_apply (g : G) (x : AddMonoidAlgebra k G) (g' : G) : (x /ᵒᶠ g) g' = x (g + g') :=
  rfl
#align add_monoid_algebra.div_of_apply AddMonoidAlgebra.divOf_apply

@[simp]
theorem support_divOf (g : G) (x : AddMonoidAlgebra k G) :
    (x /ᵒᶠ g).support =
      x.support.preimage ((· + ·) g) (Function.Injective.injOn (add_right_injective g) _) :=
  rfl
#align add_monoid_algebra.support_div_of AddMonoidAlgebra.support_divOf

@[simp]
theorem zero_divOf (g : G) : (0 : AddMonoidAlgebra k G) /ᵒᶠ g = 0 :=
  map_zero _
#align add_monoid_algebra.zero_div_of AddMonoidAlgebra.zero_divOf

@[simp]
theorem divOf_zero (x : AddMonoidAlgebra k G) : x /ᵒᶠ 0 = x := by
  refine Finsupp.ext fun _ => ?_  -- porting note: `ext` doesn't work
  -- ⊢ ↑(x /ᵒᶠ 0) x✝ = ↑x x✝
  simp only [AddMonoidAlgebra.divOf_apply, zero_add]
  -- 🎉 no goals
#align add_monoid_algebra.div_of_zero AddMonoidAlgebra.divOf_zero

theorem add_divOf (x y : AddMonoidAlgebra k G) (g : G) : (x + y) /ᵒᶠ g = x /ᵒᶠ g + y /ᵒᶠ g :=
  map_add _ _ _
#align add_monoid_algebra.add_div_of AddMonoidAlgebra.add_divOf

theorem divOf_add (x : AddMonoidAlgebra k G) (a b : G) : x /ᵒᶠ (a + b) = x /ᵒᶠ a /ᵒᶠ b := by
  refine Finsupp.ext fun _ => ?_  -- porting note: `ext` doesn't work
  -- ⊢ ↑(x /ᵒᶠ (a + b)) x✝ = ↑(x /ᵒᶠ a /ᵒᶠ b) x✝
  simp only [AddMonoidAlgebra.divOf_apply, add_assoc]
  -- 🎉 no goals
#align add_monoid_algebra.div_of_add AddMonoidAlgebra.divOf_add

/-- A bundled version of `AddMonoidAlgebra.divOf`. -/
@[simps]
noncomputable def divOfHom : Multiplicative G →* AddMonoid.End (AddMonoidAlgebra k G) where
  toFun g :=
    { toFun := fun x => divOf x (Multiplicative.toAdd g)
      map_zero' := zero_divOf _
      map_add' := fun x y => add_divOf x y (Multiplicative.toAdd g) }
  map_one' := AddMonoidHom.ext divOf_zero
  map_mul' g₁ g₂ :=
    AddMonoidHom.ext fun _x =>
      (congr_arg _ (add_comm (Multiplicative.toAdd g₁) (Multiplicative.toAdd g₂))).trans
        (divOf_add _ _ _)
#align add_monoid_algebra.div_of_hom AddMonoidAlgebra.divOfHom

theorem of'_mul_divOf (a : G) (x : AddMonoidAlgebra k G) : of' k G a * x /ᵒᶠ a = x := by
  refine Finsupp.ext fun _ => ?_  -- porting note: `ext` doesn't work
  -- ⊢ ↑(of' k G a * x /ᵒᶠ a) x✝ = ↑x x✝
  rw [AddMonoidAlgebra.divOf_apply, of'_apply, single_mul_apply_aux, one_mul]
  -- ⊢ ∀ (a_1 : G), a + a_1 = a + x✝ ↔ a_1 = x✝
  intro c
  -- ⊢ a + c = a + x✝ ↔ c = x✝
  exact add_right_inj _
  -- 🎉 no goals
#align add_monoid_algebra.of'_mul_div_of AddMonoidAlgebra.of'_mul_divOf

theorem mul_of'_divOf (x : AddMonoidAlgebra k G) (a : G) : x * of' k G a /ᵒᶠ a = x := by
  refine Finsupp.ext fun _ => ?_  -- porting note: `ext` doesn't work
  -- ⊢ ↑(x * of' k G a /ᵒᶠ a) x✝ = ↑x x✝
  rw [AddMonoidAlgebra.divOf_apply, of'_apply, mul_single_apply_aux, mul_one]
  -- ⊢ ∀ (a_1 : G), a_1 + a = a + x✝ ↔ a_1 = x✝
  intro c
  -- ⊢ c + a = a + x✝ ↔ c = x✝
  rw [add_comm]
  -- ⊢ a + c = a + x✝ ↔ c = x✝
  exact add_right_inj _
  -- 🎉 no goals
#align add_monoid_algebra.mul_of'_div_of AddMonoidAlgebra.mul_of'_divOf

theorem of'_divOf (a : G) : of' k G a /ᵒᶠ a = 1 := by
  simpa only [one_mul] using mul_of'_divOf (1 : AddMonoidAlgebra k G) a
  -- 🎉 no goals
#align add_monoid_algebra.of'_div_of AddMonoidAlgebra.of'_divOf

/-- The remainder upon division by `of' k G g`. -/
noncomputable def modOf (x : AddMonoidAlgebra k G) (g : G) : AddMonoidAlgebra k G :=
  x.filter fun g₁ => ¬∃ g₂, g₁ = g + g₂
#align add_monoid_algebra.mod_of AddMonoidAlgebra.modOf

local infixl:70 " %ᵒᶠ " => modOf

@[simp]
theorem modOf_apply_of_not_exists_add (x : AddMonoidAlgebra k G) (g : G) (g' : G)
    (h : ¬∃ d, g' = g + d) : (x %ᵒᶠ g) g' = x g' :=
  Finsupp.filter_apply_pos _ _ h
#align add_monoid_algebra.mod_of_apply_of_not_exists_add AddMonoidAlgebra.modOf_apply_of_not_exists_add

@[simp]
theorem modOf_apply_of_exists_add (x : AddMonoidAlgebra k G) (g : G) (g' : G)
    (h : ∃ d, g' = g + d) : (x %ᵒᶠ g) g' = 0 :=
  Finsupp.filter_apply_neg _ _ <| by rwa [Classical.not_not]
                                     -- 🎉 no goals
#align add_monoid_algebra.mod_of_apply_of_exists_add AddMonoidAlgebra.modOf_apply_of_exists_add

@[simp]
theorem modOf_apply_add_self (x : AddMonoidAlgebra k G) (g : G) (d : G) : (x %ᵒᶠ g) (d + g) = 0 :=
  modOf_apply_of_exists_add _ _ _ ⟨_, add_comm _ _⟩
#align add_monoid_algebra.mod_of_apply_add_self AddMonoidAlgebra.modOf_apply_add_self

-- @[simp] -- Porting note: simp can prove this
theorem modOf_apply_self_add (x : AddMonoidAlgebra k G) (g : G) (d : G) : (x %ᵒᶠ g) (g + d) = 0 :=
  modOf_apply_of_exists_add _ _ _ ⟨_, rfl⟩
#align add_monoid_algebra.mod_of_apply_self_add AddMonoidAlgebra.modOf_apply_self_add

theorem of'_mul_modOf (g : G) (x : AddMonoidAlgebra k G) : of' k G g * x %ᵒᶠ g = 0 := by
  refine Finsupp.ext fun g' => ?_  -- porting note: `ext g'` doesn't work
  -- ⊢ ↑(of' k G g * x %ᵒᶠ g) g' = ↑0 g'
  rw [Finsupp.zero_apply]
  -- ⊢ ↑(of' k G g * x %ᵒᶠ g) g' = 0
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  -- ⊢ ↑(of' k G g * x %ᵒᶠ g) (g + d) = 0
  · rw [modOf_apply_self_add]
    -- 🎉 no goals
  · rw [modOf_apply_of_not_exists_add _ _ _ h, of'_apply, single_mul_apply_of_not_exists_add _ _ h]
    -- 🎉 no goals
#align add_monoid_algebra.of'_mul_mod_of AddMonoidAlgebra.of'_mul_modOf

theorem mul_of'_modOf (x : AddMonoidAlgebra k G) (g : G) : x * of' k G g %ᵒᶠ g = 0 := by
  refine Finsupp.ext fun g' => ?_  -- porting note: `ext g'` doesn't work
  -- ⊢ ↑(x * of' k G g %ᵒᶠ g) g' = ↑0 g'
  rw [Finsupp.zero_apply]
  -- ⊢ ↑(x * of' k G g %ᵒᶠ g) g' = 0
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  -- ⊢ ↑(x * of' k G g %ᵒᶠ g) (g + d) = 0
  · rw [modOf_apply_self_add]
    -- 🎉 no goals
  · rw [modOf_apply_of_not_exists_add _ _ _ h, of'_apply, mul_single_apply_of_not_exists_add]
    -- ⊢ ¬∃ d, g' = d + g
    simpa only [add_comm] using h
    -- 🎉 no goals
#align add_monoid_algebra.mul_of'_mod_of AddMonoidAlgebra.mul_of'_modOf

theorem of'_modOf (g : G) : of' k G g %ᵒᶠ g = 0 := by
  simpa only [one_mul] using mul_of'_modOf (1 : AddMonoidAlgebra k G) g
  -- 🎉 no goals
#align add_monoid_algebra.of'_mod_of AddMonoidAlgebra.of'_modOf

theorem divOf_add_modOf (x : AddMonoidAlgebra k G) (g : G) :
    of' k G g * (x /ᵒᶠ g) + x %ᵒᶠ g = x := by
  refine Finsupp.ext fun g' => ?_  -- porting note: `ext` doesn't work
  -- ⊢ ↑(of' k G g * (x /ᵒᶠ g) + x %ᵒᶠ g) g' = ↑x g'
  rw [Finsupp.add_apply] -- porting note: changed from `simp_rw` which can't see through the type
  -- ⊢ ↑(of' k G g * (x /ᵒᶠ g)) g' + ↑(x %ᵒᶠ g) g' = ↑x g'
  obtain ⟨d, rfl⟩ | h := em (∃ d, g' = g + d)
  -- ⊢ ↑(of' k G g * (x /ᵒᶠ g)) (g + d) + ↑(x %ᵒᶠ g) (g + d) = ↑x (g + d)
  swap
  -- ⊢ ↑(of' k G g * (x /ᵒᶠ g)) g' + ↑(x %ᵒᶠ g) g' = ↑x g'
  · rw [modOf_apply_of_not_exists_add x _ _ h, of'_apply, single_mul_apply_of_not_exists_add _ _ h,
      zero_add]
  · rw [modOf_apply_self_add, add_zero]
    -- ⊢ ↑(of' k G g * (x /ᵒᶠ g)) (g + d) = ↑x (g + d)
    rw [of'_apply, single_mul_apply_aux _ _ _, one_mul, divOf_apply]
    -- ⊢ ∀ (a : G), g + a = g + d ↔ a = d
    intro a
    -- ⊢ g + a = g + d ↔ a = d
    exact add_right_inj _
    -- 🎉 no goals
#align add_monoid_algebra.div_of_add_mod_of AddMonoidAlgebra.divOf_add_modOf

theorem modOf_add_divOf (x : AddMonoidAlgebra k G) (g : G) : x %ᵒᶠ g + of' k G g * (x /ᵒᶠ g) = x :=
  by rw [add_comm, divOf_add_modOf]
     -- 🎉 no goals
#align add_monoid_algebra.mod_of_add_div_of AddMonoidAlgebra.modOf_add_divOf

theorem of'_dvd_iff_modOf_eq_zero {x : AddMonoidAlgebra k G} {g : G} :
    of' k G g ∣ x ↔ x %ᵒᶠ g = 0 := by
  constructor
  -- ⊢ of' k G g ∣ x → x %ᵒᶠ g = 0
  · rintro ⟨x, rfl⟩
    -- ⊢ of' k G g * x %ᵒᶠ g = 0
    rw [of'_mul_modOf]
    -- 🎉 no goals
  · intro h
    -- ⊢ of' k G g ∣ x
    rw [← divOf_add_modOf x g, h, add_zero]
    -- ⊢ of' k G g ∣ of' k G g * (x /ᵒᶠ g)
    exact dvd_mul_right _ _
    -- 🎉 no goals
#align add_monoid_algebra.of'_dvd_iff_mod_of_eq_zero AddMonoidAlgebra.of'_dvd_iff_modOf_eq_zero

end

end AddMonoidAlgebra
