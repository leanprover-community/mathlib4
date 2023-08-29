/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Module.Equiv
import Mathlib.LinearAlgebra.Prod

#align_import algebra.star.module from "leanprover-community/mathlib"@"aa6669832974f87406a3d9d70fc5707a60546207"

/-!
# The star operation, bundled as a star-linear equiv

We define `starLinearEquiv`, which is the star operation bundled as a star-linear map.
It is defined on a star algebra `A` over the base ring `R`.

This file also provides some lemmas that need `Algebra.Module.Basic` imported to prove.

## TODO

- Define `starLinearEquiv` for noncommutative `R`. We only the commutative case for now since,
  in the noncommutative case, the ring hom needs to reverse the order of multiplication. This
  requires a ring hom of type `R →+* Rᵐᵒᵖ`, which is very undesirable in the commutative case.
  One way out would be to define a new typeclass `IsOp R S` and have an instance `IsOp R R`
  for commutative `R`.
- Also note that such a definition involving `Rᵐᵒᵖ` or `is_op R S` would require adding
  the appropriate `RingHomInvPair` instances to be able to define the semilinear
  equivalence.
-/


section SmulLemmas

variable {R M : Type*}

@[simp]
theorem star_nat_cast_smul [Semiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M] (n : ℕ)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_nat_cast_smul (starAddEquiv : M ≃+ M) R R n x
#align star_nat_cast_smul star_nat_cast_smul

@[simp]
theorem star_int_cast_smul [Ring R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : ℤ)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_int_cast_smul (starAddEquiv : M ≃+ M) R R n x
#align star_int_cast_smul star_int_cast_smul

@[simp]
theorem star_inv_nat_cast_smul [DivisionSemiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M]
    (n : ℕ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
  map_inv_nat_cast_smul (starAddEquiv : M ≃+ M) R R n x
#align star_inv_nat_cast_smul star_inv_nat_cast_smul

@[simp]
theorem star_inv_int_cast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M]
    (n : ℤ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
  map_inv_int_cast_smul (starAddEquiv : M ≃+ M) R R n x
#align star_inv_int_cast_smul star_inv_int_cast_smul

@[simp]
theorem star_rat_cast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : ℚ)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_rat_cast_smul (starAddEquiv : M ≃+ M) _ _ _ x
#align star_rat_cast_smul star_rat_cast_smul

@[simp]
theorem star_rat_smul {R : Type*} [AddCommGroup R] [StarAddMonoid R] [Module ℚ R] (x : R) (n : ℚ) :
    star (n • x) = n • star x :=
  map_rat_smul (starAddEquiv : R ≃+ R) _ _
#align star_rat_smul star_rat_smul

end SmulLemmas

/-- If `A` is a module over a commutative `R` with compatible actions,
then `star` is a semilinear equivalence. -/
@[simps]
def starLinearEquiv (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] : A ≃ₗ⋆[R] A :=
  { starAddEquiv with
    toFun := star
    map_smul' := star_smul }
#align star_linear_equiv starLinearEquiv

variable (R : Type*) (A : Type*) [Semiring R] [StarSemigroup R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A]

/-- The self-adjoint elements of a star module, as a submodule. -/
def selfAdjoint.submodule : Submodule R A :=
  { selfAdjoint A with smul_mem' := fun _ _ => (IsSelfAdjoint.all _).smul }
#align self_adjoint.submodule selfAdjoint.submodule

/-- The skew-adjoint elements of a star module, as a submodule. -/
def skewAdjoint.submodule : Submodule R A :=
  { skewAdjoint A with smul_mem' := skewAdjoint.smul_mem }
#align skew_adjoint.submodule skewAdjoint.submodule

variable {A} [Invertible (2 : R)]

/-- The self-adjoint part of an element of a star module, as a linear map. -/
@[simps]
def selfAdjointPart : A →ₗ[R] selfAdjoint A where
  toFun x :=
    ⟨(⅟ 2 : R) • (x + star x), by
      simp only [selfAdjoint.mem_iff, star_smul, add_comm, StarAddMonoid.star_add, star_inv',
        star_bit0, star_one, star_star, star_invOf (2 : R), star_trivial]⟩
  map_add' x y := by
    ext
    -- ⊢ ↑((fun x => { val := ⅟2 • (x + star x), property := (_ : ⅟2 • (x + star x) ∈ …
    simp [add_add_add_comm]
    -- 🎉 no goals
  map_smul' r x := by
    ext
    -- ⊢ ↑(AddHom.toFun { toFun := fun x => { val := ⅟2 • (x + star x), property := ( …
    simp [← mul_smul, show ⅟ 2 * r = r * ⅟ 2 from Commute.invOf_left <| (2 : ℕ).cast_commute r]
    -- 🎉 no goals
#align self_adjoint_part selfAdjointPart

/-- The skew-adjoint part of an element of a star module, as a linear map. -/
@[simps]
def skewAdjointPart : A →ₗ[R] skewAdjoint A where
  toFun x :=
    ⟨(⅟ 2 : R) • (x - star x), by
      simp only [skewAdjoint.mem_iff, star_smul, star_sub, star_star, star_trivial, ← smul_neg,
        neg_sub]⟩
  map_add' x y := by
    ext
    -- ⊢ ↑((fun x => { val := ⅟2 • (x - star x), property := (_ : ⅟2 • (x - star x) ∈ …
    simp only [sub_add, ← smul_add, sub_sub_eq_add_sub, star_add, AddSubgroup.coe_mk,
      AddSubgroup.coe_add]
  map_smul' r x := by
    ext
    -- ⊢ ↑(AddHom.toFun { toFun := fun x => { val := ⅟2 • (x - star x), property := ( …
    simp [← mul_smul, ← smul_sub,
      show r * ⅟ 2 = ⅟ 2 * r from Commute.invOf_right <| (2 : ℕ).commute_cast r]
#align skew_adjoint_part skewAdjointPart

theorem StarModule.selfAdjointPart_add_skewAdjointPart (x : A) :
    (selfAdjointPart R x : A) + skewAdjointPart R x = x := by
  simp only [smul_sub, selfAdjointPart_apply_coe, smul_add, skewAdjointPart_apply_coe,
    add_add_sub_cancel, invOf_two_smul_add_invOf_two_smul]
#align star_module.self_adjoint_part_add_skew_adjoint_part StarModule.selfAdjointPart_add_skewAdjointPart

theorem IsSelfAdjoint.coe_selfAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    (selfAdjointPart R x : A) = x := by
  rw [selfAdjointPart_apply_coe, hx.star_eq, smul_add, invOf_two_smul_add_invOf_two_smul]
  -- 🎉 no goals

theorem IsSelfAdjoint.selfAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    selfAdjointPart R x = ⟨x, hx⟩ :=
  Subtype.eq (hx.coe_selfAdjointPart_apply R)

-- porting note: todo: make it a `simp`
theorem selfAdjointPart_comp_subtype_selfAdjoint :
    (selfAdjointPart R).comp (selfAdjoint.submodule R A).subtype = .id :=
  LinearMap.ext fun x ↦ x.2.selfAdjointPart_apply R

theorem IsSelfAdjoint.skewAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    skewAdjointPart R x = 0 := Subtype.eq <| by
  rw [skewAdjointPart_apply_coe, hx.star_eq, sub_self, smul_zero, ZeroMemClass.coe_zero]
  -- 🎉 no goals

-- porting note: todo: make it a `simp`
theorem skewAdjointPart_comp_subtype_selfAdjoint :
    (skewAdjointPart R).comp (selfAdjoint.submodule R A).subtype = 0 :=
  LinearMap.ext fun x ↦ x.2.skewAdjointPart_apply R

-- porting note: todo: make it a `simp`
theorem selfAdjointPart_comp_subtype_skewAdjoint :
    (selfAdjointPart R).comp (skewAdjoint.submodule R A).subtype = 0 :=
  LinearMap.ext fun ⟨x, (hx : _ = _)⟩ ↦ Subtype.eq <| by simp [hx]
                                                         -- 🎉 no goals

-- porting note: todo: make it a `simp`
theorem skewAdjointPart_comp_subtype_skewAdjoint :
    (skewAdjointPart R).comp (skewAdjoint.submodule R A).subtype = .id :=
  LinearMap.ext fun ⟨x, (hx : _ = _)⟩ ↦ Subtype.eq <| by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, skewAdjointPart_apply_coe, hx,
      sub_neg_eq_add, smul_add, invOf_two_smul_add_invOf_two_smul]; rfl
                                                                    -- 🎉 no goals

variable (A)

/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a linear equivalence. -/
-- Porting note: This attribute causes a `timeout at 'whnf'`.
-- @[simps!]
def StarModule.decomposeProdAdjoint : A ≃ₗ[R] selfAdjoint A × skewAdjoint A := by
  refine LinearEquiv.ofLinear ((selfAdjointPart R).prod (skewAdjointPart R))
    (LinearMap.coprod ((selfAdjoint.submodule R A).subtype) (skewAdjoint.submodule R A).subtype)
    ?_ (LinearMap.ext <| StarModule.selfAdjointPart_add_skewAdjointPart R)
  ext <;> simp
          -- 🎉 no goals
          -- 🎉 no goals
          -- 🎉 no goals
          -- 🎉 no goals
#align star_module.decompose_prod_adjoint StarModule.decomposeProdAdjoint

@[simp]
theorem algebraMap_star_comm {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A]
    [StarSemigroup A] [Algebra R A] [StarModule R A] (r : R) :
    algebraMap R A (star r) = star (algebraMap R A r) := by
  simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]
  -- 🎉 no goals
#align algebra_map_star_comm algebraMap_star_comm
