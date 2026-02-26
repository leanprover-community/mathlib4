/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.TensorProduct
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Intrinsic star operation on `E →ₗ[R] F`

This file defines the star operation on linear maps: `(star f) x = star (f (star x))`.
This corresponds to a map being star-preserving, i.e., a map is self-adjoint iff it
is star-preserving.

## Implementation notes

**Note** that in the case of when `E = F` for a finite-dimensional Hilbert space, this `star`
is mathematically distinct from the global instance on `E →ₗ[𝕜] E` where
`star := LinearMap.adjoint`.
For that reason, the intrinsic star operation is scoped to `IntrinsicStar`.
-/

@[expose] public section

variable {R E F : Type*} [Semiring R] [InvolutiveStar R]
  [AddCommMonoid E] [Module R E] [StarAddMonoid E] [StarModule R E]
  [AddCommMonoid F] [Module R F] [StarAddMonoid F] [StarModule R F]

namespace LinearMap

/-- The intrinsic star operation on linear maps `E →ₗ F` defined by
`(star f) x = star (f (star x))`. -/
def intrinsicStar : Star (E →ₗ[R] F) where
  star f :=
  { toFun x := star (f (star x))
    map_add' _ _ := by simp
    map_smul' _ _ := by simp }

scoped[IntrinsicStar] attribute [instance] LinearMap.intrinsicStar

open scoped IntrinsicStar

@[simp] theorem intrinsicStar_apply (f : E →ₗ[R] F) (x : E) : (star f) x = star (f (star x)) := rfl

/-- The involutive intrinsic star structure on linear maps. -/
def intrinsicInvolutiveStar : InvolutiveStar (E →ₗ[R] F) where
  star_involutive x := by ext; simp

scoped[IntrinsicStar] attribute [instance] LinearMap.intrinsicInvolutiveStar

/-- The intrinsic star additive monoid structure on linear maps. -/
def intrinsicStarAddMonoid : StarAddMonoid (E →ₗ[R] F) where
  star_add x y := by ext; simp

scoped[IntrinsicStar] attribute [instance] LinearMap.intrinsicStarAddMonoid

/-- A linear map is self-adjoint (with respect to the intrinsic star) iff it is star-preserving. -/
theorem IntrinsicStar.isSelfAdjoint_iff_map_star (f : E →ₗ[R] F) :
    IsSelfAdjoint f ↔ ∀ x, f (star x) = star (f x) := by
  simp_rw [IsSelfAdjoint, LinearMap.ext_iff, intrinsicStar_apply, star_eq_iff_star_eq, eq_comm]

@[deprecated (since := "2025-12-09")]
alias isSelfAdjoint_iff_map_star := IntrinsicStar.isSelfAdjoint_iff_map_star

/-- A star-preserving linear map is self-adjoint (with respect to the intrinsic star). -/
@[simp]
protected theorem _root_.IntrinsicStar.StarHomClass.isSelfAdjoint {S : Type*} [FunLike S E F]
    [LinearMapClass S R E F] [StarHomClass S E F] {f : S} : IsSelfAdjoint (f : E →ₗ[R] F) :=
  IntrinsicStar.isSelfAdjoint_iff_map_star _ |>.mpr (map_star f)

@[deprecated (since := "2025-12-09")]
alias _root_.StarHomClass.isSelfAdjoint := _root_.IntrinsicStar.StarHomClass.isSelfAdjoint

variable {G : Type*} [AddCommMonoid G] [Module R G] [StarAddMonoid G] [StarModule R G]

theorem intrinsicStar_comp (f : E →ₗ[R] F) (g : G →ₗ[R] E) :
    star (f ∘ₗ g) = star f ∘ₗ star g := by ext; simp

@[simp] theorem intrinsicStar_id : star (LinearMap.id (R := R) (M := E)) = LinearMap.id := by
  ext; simp
@[simp] theorem intrinsicStar_zero : star (0 : E →ₗ[R] F) = 0 := by ext; simp

section NonUnitalNonAssocSemiring
variable {R' E : Type*} [CommSemiring R'] [StarRing R']
  [NonUnitalNonAssocSemiring E] [StarRing E] [Module R E] [Module R' E]
  [StarModule R E] [StarModule R' E] [SMulCommClass R E E] [IsScalarTower R E E]

theorem intrinsicStar_mulLeft (x : E) : star (mulLeft R x) = mulRight R (star x) := by ext; simp

theorem intrinsicStar_mulRight (x : E) : star (mulRight R x) = mulLeft R (star x) := by
  rw [star_eq_iff_star_eq, intrinsicStar_mulLeft, star_star]

theorem intrinsicStar_mul' [SMulCommClass R' E E] [IsScalarTower R' E E] :
    star (mul' R' E) = mul' R' E ∘ₗ TensorProduct.comm R' E E :=
  TensorProduct.ext' fun _ _ ↦ by simp

end NonUnitalNonAssocSemiring

variable [SMulCommClass R R F] in
lemma intrinsicStarModule : StarModule R (E →ₗ[R] F) where
  star_smul _ _ := by ext; simp

scoped[IntrinsicStar] attribute [instance] LinearMap.intrinsicStarModule

section CommSemiring
variable {R E F G H : Type*} [CommSemiring R] [StarRing R]
  [AddCommMonoid E] [StarAddMonoid E] [Module R E] [StarModule R E]
  [AddCommMonoid F] [StarAddMonoid F] [Module R F] [StarModule R F]
  [AddCommMonoid G] [StarAddMonoid G] [Module R G] [StarModule R G]
  [AddCommMonoid H] [StarAddMonoid H] [Module R H] [StarModule R H]

theorem _root_.TensorProduct.intrinsicStar_map (f : E →ₗ[R] F) (g : G →ₗ[R] H) :
    star (TensorProduct.map f g) = TensorProduct.map (star f) (star g) :=
  TensorProduct.ext' fun _ _ ↦ by simp

theorem intrinsicStar_lTensor (f : F →ₗ[R] G) : star (lTensor E f) = lTensor E (star f) := by
  simp [lTensor, TensorProduct.intrinsicStar_map]

theorem intrinsicStar_rTensor (f : E →ₗ[R] F) : star (rTensor G f) = rTensor G (star f) := by
  simp [rTensor, TensorProduct.intrinsicStar_map]

theorem intrinsicStar_eq_comp (f : E →ₗ[R] F) :
    star f = (starLinearEquiv R).toLinearMap ∘ₛₗ f ∘ₛₗ (starLinearEquiv R).toLinearMap := rfl

theorem IntrinsicStar.starLinearEquiv_eq_arrowCongr :
    starLinearEquiv R (A := E →ₗ[R] F) = (starLinearEquiv R).arrowCongr (starLinearEquiv R) := rfl

end CommSemiring

section starAddMonoidSemiring
variable {S : Type*} [Semiring S] [StarAddMonoid S] [StarModule S S] [Module S E] [StarModule S E]

@[simp] theorem intrinsicStar_toSpanSingleton (a : E) :
    star (toSpanSingleton S E a) = toSpanSingleton S E (star a) := by ext; simp

theorem intrinsicStar_smulRight [Module S F] [StarModule S F] (f : E →ₗ[S] S) (x : F) :
    star (f.smulRight x) = (star f).smulRight (star x) := by ext; simp

end starAddMonoidSemiring

end LinearMap

section matrix
variable {R m n : Type*} [CommSemiring R] [StarRing R] [Fintype m] [DecidableEq m]

open scoped IntrinsicStar

namespace LinearMap

theorem toMatrix'_intrinsicStar (f : (m → R) →ₗ[R] (n → R)) :
    (star f).toMatrix' = f.toMatrix'.map star := by
  ext; simp

/-- A linear map `f : (m → R) →ₗ (n → R)` is self-adjoint (with respect to the intrinsic star)
iff its corresponding matrix `f.toMatrix'` has all self-adjoint elements.
So star-preserving maps correspond to their matrices containing only self-adjoint elements. -/
theorem IntrinsicStar.isSelfAdjoint_iff_toMatrix' (f : (m → R) →ₗ[R] (n → R)) :
    IsSelfAdjoint f ↔ ∀ i j, IsSelfAdjoint (f.toMatrix' i j) := by
  simp [IsSelfAdjoint, ← toMatrix'.injective.eq_iff, toMatrix'_intrinsicStar, ← Matrix.ext_iff]

end LinearMap

namespace Matrix

theorem intrinsicStar_toLin' (A : Matrix n m R) : star A.toLin' = (A.map star).toLin' := by
  simp [← LinearMap.toMatrix'.injective.eq_iff, LinearMap.toMatrix'_intrinsicStar]

/-- Given a matrix `A`, `A.toLin'` is self-adjoint (with respect to the intrinsic star)
iff all its elements are self-adjoint. -/
theorem IntrinsicStar.isSelfAdjoint_toLin'_iff (A : Matrix n m R) :
    IsSelfAdjoint A.toLin' ↔ ∀ i j, IsSelfAdjoint (A i j) := by
  simp [IsSelfAdjoint, intrinsicStar_toLin', ← ext_iff]

end Matrix
end matrix

namespace Module.End

open scoped IntrinsicStar

/-- Intrinsic star operation for `(End R E)ˣ`. -/
def Units.intrinsicStar : Star (End R E)ˣ where
  star f := by
    refine ⟨star f, star (f⁻¹ : (End R E)ˣ), ?_, ?_⟩
    all_goals
      rw [mul_eq_comp, ← LinearMap.intrinsicStar_comp]
      simp [← mul_eq_comp, one_eq_id]

scoped[IntrinsicStar] attribute [instance] Module.End.Units.intrinsicStar

theorem IsUnit.intrinsicStar {f : End R E} (hf : IsUnit f) : IsUnit (star f) :=
  have ⟨u, hu⟩ := hf
  hu ▸ (star u).isUnit

open Module.End in
@[simp] theorem isUnit_intrinsicStar_iff {f : End R E} : IsUnit (star f) ↔ IsUnit f :=
  ⟨fun h ↦ star_star f ▸ h.intrinsicStar, fun h ↦ h.intrinsicStar⟩

section eigenspace
variable {R V : Type*} [CommRing R] [InvolutiveStar R] [AddCommGroup V] [StarAddMonoid V]
  [Module R V] [StarModule R V]

open LinearMap

theorem mem_eigenspace_intrinsicStar_iff (f : End R V) (α : R) (x : V) :
    x ∈ (star f).eigenspace α ↔ star x ∈ f.eigenspace (star α) := by
  simp_rw [mem_eigenspace_iff, intrinsicStar_apply, star_eq_iff_star_eq, star_smul, eq_comm]

@[simp]
theorem spectrum_intrinsicStar (f : End R V) : spectrum R (star f) = star (spectrum R f) := by
  ext x
  simp_rw [Set.mem_star, spectrum.mem_iff, not_iff_not, Algebra.algebraMap_eq_smul_one]
  rw [← isUnit_intrinsicStar_iff, star_sub, star_star, star_smul, one_eq_id, intrinsicStar_id]

end eigenspace
end Module.End
