/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Frédéric Dupuis
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Module.LinearMap.Star
public import Mathlib.Algebra.Module.Rat
public import Mathlib.LinearAlgebra.Prod

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

@[expose] public section


section SMulLemmas

variable {R M : Type*}

@[simp]
theorem star_natCast_smul [Semiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M] (n : ℕ)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_natCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
theorem star_intCast_smul [Ring R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : ℤ)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_intCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
theorem star_inv_natCast_smul [DivisionSemiring R] [AddCommMonoid M] [Module R M] [StarAddMonoid M]
    (n : ℕ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
  map_inv_natCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
theorem star_inv_intCast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M]
    (n : ℤ) (x : M) : star ((n⁻¹ : R) • x) = (n⁻¹ : R) • star x :=
  map_inv_intCast_smul (starAddEquiv : M ≃+ M) R R n x

@[simp]
theorem star_ratCast_smul [DivisionRing R] [AddCommGroup M] [Module R M] [StarAddMonoid M] (n : ℚ)
    (x : M) : star ((n : R) • x) = (n : R) • star x :=
  map_ratCast_smul (starAddEquiv : M ≃+ M) _ _ _ x

/-!
Per the naming convention, these two lemmas call `(q • ·)` `nnrat_smul` and `rat_smul` respectively,
rather than `nnqsmul` and `qsmul` because the latter are reserved to the actions coming from
`DivisionSemiring` and `DivisionRing`. We provide aliases with `nnqsmul` and `qsmul` for
discoverability.
-/

/-- Note that this lemma holds for an arbitrary `ℚ≥0`-action, rather than merely one coming from a
`DivisionSemiring`. We keep both the `nnqsmul` and `nnrat_smul` naming conventions for
discoverability. See `star_nnqsmul`. -/
@[simp high]
lemma star_nnrat_smul [AddCommMonoid R] [StarAddMonoid R] [Module ℚ≥0 R] (q : ℚ≥0) (x : R) :
    star (q • x) = q • star x := map_nnrat_smul (starAddEquiv : R ≃+ R) _ _

/-- Note that this lemma holds for an arbitrary `ℚ`-action, rather than merely one coming from a
`DivisionRing`. We keep both the `qsmul` and `rat_smul` naming conventions for discoverability.
See `star_qsmul`. -/
@[simp high] lemma star_rat_smul [AddCommGroup R] [StarAddMonoid R] [Module ℚ R] (q : ℚ) (x : R) :
    star (q • x) = q • star x :=
  map_rat_smul (starAddEquiv : R ≃+ R) _ _

/-- Note that this lemma holds for an arbitrary `ℚ≥0`-action, rather than merely one coming from a
`DivisionSemiring`. We keep both the `nnqsmul` and `nnrat_smul` naming conventions for
discoverability. See `star_nnrat_smul`. -/
alias star_nnqsmul := star_nnrat_smul

/-- Note that this lemma holds for an arbitrary `ℚ`-action, rather than merely one coming from a
`DivisionRing`. We keep both the `qsmul` and `rat_smul` naming conventions for
discoverability. See `star_rat_smul`. -/
alias star_qsmul := star_rat_smul

instance StarAddMonoid.toStarModuleNNRat [AddCommMonoid R] [Module ℚ≥0 R] [StarAddMonoid R] :
    StarModule ℚ≥0 R where star_smul := star_nnrat_smul

instance StarAddMonoid.toStarModuleRat [AddCommGroup R] [Module ℚ R] [StarAddMonoid R] :
    StarModule ℚ R where star_smul := star_rat_smul

end SMulLemmas

/-- If `A` is a module over a commutative `R` with compatible actions,
then `star` is a semilinear equivalence. -/
@[simps]
def starLinearEquiv (R : Type*) {A : Type*} [CommSemiring R] [StarRing R] [AddCommMonoid A]
    [StarAddMonoid A] [Module R A] [StarModule R A] : A ≃ₗ⋆[R] A :=
  { starAddEquiv with
    toFun := star
    map_smul' := star_smul }

section SelfSkewAdjoint

variable (R : Type*) (A : Type*) [Semiring R] [StarMul R] [TrivialStar R] [AddCommGroup A]
  [Module R A] [StarAddMonoid A] [StarModule R A]

/-- The self-adjoint elements of a star module, as a submodule. -/
def selfAdjoint.submodule : Submodule R A :=
  { selfAdjoint A with smul_mem' := fun _ _ => (IsSelfAdjoint.all _).smul }

/-- The skew-adjoint elements of a star module, as a submodule. -/
def skewAdjoint.submodule : Submodule R A :=
  { skewAdjoint A with smul_mem' := skewAdjoint.smul_mem }

variable {A} [Invertible (2 : R)]

/-- The self-adjoint part of an element of a star module, as a linear map. -/
@[simps]
def selfAdjointPart : A →ₗ[R] selfAdjoint A where
  toFun x :=
    ⟨(⅟2 : R) • (x + star x), by
      rw [selfAdjoint.mem_iff, star_smul, star_trivial, star_add, star_star, add_comm]⟩
  map_add' x y := by
    ext
    simp [add_add_add_comm]
  map_smul' r x := by
    ext
    simp [← mul_smul, show ⅟2 * r = r * ⅟2 from Commute.invOf_left <| (2 : ℕ).cast_commute r]

/-- The skew-adjoint part of an element of a star module, as a linear map. -/
@[simps]
def skewAdjointPart : A →ₗ[R] skewAdjoint A where
  toFun x :=
    ⟨(⅟2 : R) • (x - star x), by
      simp only [skewAdjoint.mem_iff, star_smul, star_sub, star_star, star_trivial, ← smul_neg,
        neg_sub]⟩
  map_add' x y := by
    ext
    simp only [sub_add, ← smul_add, sub_sub_eq_add_sub, star_add, AddSubgroup.coe_add]
  map_smul' r x := by
    ext
    simp [← mul_smul, ← smul_sub,
      show r * ⅟2 = ⅟2 * r from Commute.invOf_right <| (2 : ℕ).commute_cast r]

theorem StarModule.selfAdjointPart_add_skewAdjointPart (x : A) :
    (selfAdjointPart R x : A) + skewAdjointPart R x = x := by
  simp only [smul_sub, selfAdjointPart_apply_coe, smul_add, skewAdjointPart_apply_coe,
    add_add_sub_cancel, invOf_two_smul_add_invOf_two_smul]

theorem IsSelfAdjoint.coe_selfAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    (selfAdjointPart R x : A) = x := by
  rw [selfAdjointPart_apply_coe, hx.star_eq, smul_add, invOf_two_smul_add_invOf_two_smul]

theorem IsSelfAdjoint.selfAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    selfAdjointPart R x = ⟨x, hx⟩ :=
  Subtype.ext (hx.coe_selfAdjointPart_apply R)

@[simp]
theorem selfAdjointPart_comp_subtype_selfAdjoint :
    (selfAdjointPart R).comp (selfAdjoint.submodule R A).subtype = .id :=
  LinearMap.ext fun x ↦ x.2.selfAdjointPart_apply R

theorem IsSelfAdjoint.skewAdjointPart_apply {x : A} (hx : IsSelfAdjoint x) :
    skewAdjointPart R x = 0 := Subtype.ext <| by
  rw [skewAdjointPart_apply_coe, hx.star_eq, sub_self, smul_zero, ZeroMemClass.coe_zero]

@[simp]
theorem skewAdjointPart_comp_subtype_selfAdjoint :
    (skewAdjointPart R).comp (selfAdjoint.submodule R A).subtype = 0 :=
  LinearMap.ext fun x ↦ x.2.skewAdjointPart_apply R

@[simp]
theorem selfAdjointPart_comp_subtype_skewAdjoint :
    (selfAdjointPart R).comp (skewAdjoint.submodule R A).subtype = 0 :=
  LinearMap.ext fun ⟨x, (hx : _ = _)⟩ ↦ Subtype.ext <| by simp [hx]

@[simp]
theorem skewAdjointPart_comp_subtype_skewAdjoint :
    (skewAdjointPart R).comp (skewAdjoint.submodule R A).subtype = .id :=
  LinearMap.ext fun ⟨x, (hx : _ = _)⟩ ↦ Subtype.ext <| by
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, skewAdjointPart_apply_coe, hx,
      sub_neg_eq_add, smul_add, invOf_two_smul_add_invOf_two_smul]; rfl

variable (A)

/-- The decomposition of elements of a star module into their self- and skew-adjoint parts,
as a linear equivalence. -/
@[simps!]
def StarModule.decomposeProdAdjoint : A ≃ₗ[R] selfAdjoint A × skewAdjoint A := by
  refine LinearEquiv.ofLinear ((selfAdjointPart R).prod (skewAdjointPart R))
    (LinearMap.coprod ((selfAdjoint.submodule R A).subtype) (skewAdjoint.submodule R A).subtype)
    ?_ (LinearMap.ext <| StarModule.selfAdjointPart_add_skewAdjointPart R)
  ext x <;> dsimp only [Submodule.subtype, selfAdjoint.submodule, skewAdjoint.submodule] <;> simp

end SelfSkewAdjoint

section algebraMap

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A]
variable [StarMul A] [Algebra R A] [StarModule R A]

@[simp]
theorem algebraMap_star_comm (r : R) : algebraMap R A (star r) = star (algebraMap R A r) := by
  simp only [Algebra.algebraMap_eq_smul_one, star_smul, star_one]

variable (A) in
protected lemma IsSelfAdjoint.algebraMap {r : R} (hr : IsSelfAdjoint r) :
    IsSelfAdjoint (algebraMap R A r) := by
  simpa using! congr(algebraMap R A $(hr.star_eq))

lemma isSelfAdjoint_algebraMap_iff {r : R} (h : Function.Injective (algebraMap R A)) :
    IsSelfAdjoint (algebraMap R A r) ↔ IsSelfAdjoint r :=
  ⟨fun hr ↦ h <| algebraMap_star_comm r (A := A) ▸ hr.star_eq, IsSelfAdjoint.algebraMap A⟩

end algebraMap

theorem IsIdempotentElem.star_iff {R : Type*} [Mul R] [StarMul R] {a : R} :
    IsIdempotentElem (star a) ↔ IsIdempotentElem a := by
  simp [IsIdempotentElem, ← star_mul]

alias ⟨_, IsIdempotentElem.star⟩ := IsIdempotentElem.star_iff
