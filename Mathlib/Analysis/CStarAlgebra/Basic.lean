/-
Copyright (c) 2021 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Algebra.Star.Pi
public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Data.Real.Star
public import Mathlib.Topology.Algebra.Module.Star

/-!
# Normed star rings and algebras

A normed star group is a normed group with a compatible `star` which is isometric.

A C⋆-ring is a normed star group that is also a ring and that verifies the stronger
condition `‖x‖^2 ≤ ‖x⋆ * x‖` for all `x` (which actually implies equality). If a C⋆-ring is also
a star algebra, then it is a C⋆-algebra.

Note that the type classes corresponding to C⋆-algebras are defined in
`Mathlib/Analysis/CStarAlgebra/Classes`.

## TODO

- Show that `‖x⋆ * x‖ = ‖x‖^2` is equivalent to `‖x⋆ * x‖ = ‖x⋆‖ * ‖x‖`, which is used as the
  definition of C⋆-algebras in some sources (e.g. Wikipedia).

-/

@[expose] public section

assert_not_exists ContinuousLinearMap.hasOpNorm

open Topology

local postfix:max "⋆" => star

/-- A normed star group is a normed group with a compatible `star` which is isometric. -/
class NormedStarGroup (E : Type*) [SeminormedAddCommGroup E] [StarAddMonoid E] : Prop where
  norm_star_le : ∀ x : E, ‖x⋆‖ ≤ ‖x‖

variable {𝕜 E α : Type*}

section NormedStarGroup

variable [SeminormedAddCommGroup E] [StarAddMonoid E] [NormedStarGroup E]

@[simp]
lemma norm_star (x : E) : ‖x⋆‖ = ‖x‖ :=
  le_antisymm (NormedStarGroup.norm_star_le x) (by simpa using NormedStarGroup.norm_star_le x⋆)

@[simp]
theorem nnnorm_star (x : E) : ‖star x‖₊ = ‖x‖₊ :=
  Subtype.ext <| norm_star _

/-- The `star` map in a normed star group is a normed group homomorphism. -/
def starNormedAddGroupHom : NormedAddGroupHom E E :=
  { starAddEquiv with bound' := ⟨1, fun _ => le_trans (norm_star _).le (one_mul _).symm.le⟩ }

/-- The `star` map in a normed star group is an isometry -/
theorem star_isometry : Isometry (star : E → E) :=
  show Isometry starAddEquiv from
    AddMonoidHomClass.isometry_of_norm starAddEquiv (show ∀ x, ‖x⋆‖ = ‖x‖ from norm_star)

instance (priority := 100) NormedStarGroup.to_continuousStar : ContinuousStar E :=
  ⟨star_isometry.continuous⟩

noncomputable
instance [NormedField 𝕜] [NormedSpace 𝕜 E] [Star 𝕜] [TrivialStar 𝕜] [StarModule 𝕜 E] :
    NormedSpace 𝕜 (selfAdjoint E) where
  norm_smul_le _ _ := norm_smul_le _ (_ : E)

end NormedStarGroup

instance RingHomIsometric.starRingEnd [NormedCommRing E] [StarRing E] [NormedStarGroup E] :
    RingHomIsometric (starRingEnd E) :=
  ⟨@norm_star _ _ _ _⟩

/-- A C⋆-ring is a normed star ring that satisfies the stronger condition `‖x‖ ^ 2 ≤ ‖x⋆ * x‖`
for every `x`. Note that this condition actually implies equality, as is shown in
`norm_star_mul_self` below. -/
class CStarRing (E : Type*) [NonUnitalNormedRing E] [StarRing E] : Prop where
  norm_mul_self_le : ∀ x : E, ‖x‖ * ‖x‖ ≤ ‖x⋆ * x‖

instance : CStarRing ℝ where
  norm_mul_self_le x := by
    simp only [Real.norm_eq_abs, abs_mul_abs_self, star, id, norm_mul, le_refl]

namespace CStarRing

section NonUnital

lemma of_le_norm_mul_star_self
    [NonUnitalNormedRing E] [StarRing E]
    (h : ∀ x : E, ‖x‖ * ‖x‖ ≤ ‖x * x⋆‖) : CStarRing E :=
  have : NormedStarGroup E :=
    { norm_star_le x := by
        obtain (hx | hx) := eq_zero_or_norm_pos x⋆
        · simp [hx]
        · refine le_of_mul_le_mul_right ?_ hx
          simpa [sq, mul_comm ‖x⋆‖] using h x⋆ |>.trans <| norm_mul_le _ _ }
  ⟨star_involutive.surjective.forall.mpr <| by simpa⟩

variable [NonUnitalNormedRing E] [StarRing E] [CStarRing E]

-- see Note [lower instance priority]
/-- In a C⋆-ring, star preserves the norm. -/
instance (priority := 100) to_normedStarGroup : NormedStarGroup E where
  norm_star_le x := by
    obtain (hx | hx) := eq_zero_or_norm_pos x⋆
    · simp [hx]
    · refine le_of_mul_le_mul_right ?_ hx
      simpa using norm_mul_self_le (x := x⋆) |>.trans <| norm_mul_le _ _

theorem norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x‖ * ‖x‖ :=
  le_antisymm ((norm_mul_le _ _).trans (by rw [norm_star])) (CStarRing.norm_mul_self_le x)

theorem norm_self_mul_star {x : E} : ‖x * x⋆‖ = ‖x‖ * ‖x‖ := by
  nth_rw 1 [← star_star x]
  simp only [norm_star_mul_self, norm_star]

theorem norm_star_mul_self' {x : E} : ‖x⋆ * x‖ = ‖x⋆‖ * ‖x‖ := by rw [norm_star_mul_self, norm_star]

theorem nnnorm_self_mul_star {x : E} : ‖x * x⋆‖₊ = ‖x‖₊ * ‖x‖₊ :=
  Subtype.ext norm_self_mul_star

theorem nnnorm_star_mul_self {x : E} : ‖x⋆ * x‖₊ = ‖x‖₊ * ‖x‖₊ :=
  Subtype.ext norm_star_mul_self

lemma _root_.IsSelfAdjoint.norm_mul_self {x : E} (hx : IsSelfAdjoint x) :
    ‖x * x‖ = ‖x‖ ^ 2 := by
  simpa [sq, hx.star_eq] using CStarRing.norm_star_mul_self (x := x)

lemma _root_.IsSelfAdjoint.nnnorm_mul_self {x : E} (hx : IsSelfAdjoint x) :
    ‖x * x‖₊ = ‖x‖₊ ^ 2 :=
  Subtype.ext hx.norm_mul_self

@[simp]
theorem star_mul_self_eq_zero_iff (x : E) : x⋆ * x = 0 ↔ x = 0 := by
  rw [← norm_eq_zero, norm_star_mul_self]
  exact mul_self_eq_zero.trans norm_eq_zero

theorem star_mul_self_ne_zero_iff (x : E) : x⋆ * x ≠ 0 ↔ x ≠ 0 := by
  simp only [Ne, star_mul_self_eq_zero_iff]

@[simp]
theorem mul_star_self_eq_zero_iff (x : E) : x * x⋆ = 0 ↔ x = 0 := by
  simpa only [star_eq_zero, star_star] using @star_mul_self_eq_zero_iff _ _ _ _ (star x)

theorem mul_star_self_ne_zero_iff (x : E) : x * x⋆ ≠ 0 ↔ x ≠ 0 := by
  simp only [Ne, mul_star_self_eq_zero_iff]

end NonUnital

section ProdPi

variable {ι R₁ R₂ : Type*} {R : ι → Type*}
variable [NonUnitalNormedRing R₁] [StarRing R₁] [CStarRing R₁]
variable [NonUnitalNormedRing R₂] [StarRing R₂] [CStarRing R₂]
variable [∀ i, NonUnitalNormedRing (R i)] [∀ i, StarRing (R i)]

/-- This instance exists to short circuit type class resolution because of problems with
inference involving Π-types. -/
instance _root_.Pi.starRing' : StarRing (∀ i, R i) :=
  inferInstance

variable [Fintype ι] [∀ i, CStarRing (R i)]

instance _root_.Prod.cstarRing : CStarRing (R₁ × R₂) where
  norm_mul_self_le x := by
    dsimp only [norm]
    simp only [Prod.fst_mul, Prod.fst_star, Prod.snd_mul, Prod.snd_star, norm_star_mul_self, ← sq]
    rw [le_sup_iff]
    rcases le_total ‖x.fst‖ ‖x.snd‖ with (h | h) <;> simp [h]

instance _root_.Pi.cstarRing : CStarRing (∀ i, R i) where
  norm_mul_self_le x := by
    refine le_of_eq (Eq.symm ?_)
    simp only [norm, Pi.mul_apply, Pi.star_apply, nnnorm_star_mul_self, ← sq]
    norm_cast
    exact
      (Finset.comp_sup_eq_sup_comp_of_is_total (fun x : NNReal => x ^ 2)
          (fun x y h => by simpa only [sq] using mul_le_mul' h h) (by simp)).symm

instance _root_.Pi.cstarRing' : CStarRing (ι → R₁) :=
  Pi.cstarRing

end ProdPi

namespace MulOpposite

instance {E : Type*} [NonUnitalNormedRing E] [StarRing E] [CStarRing E] : CStarRing Eᵐᵒᵖ where
  norm_mul_self_le x := CStarRing.norm_self_mul_star (x := MulOpposite.unop x) |>.symm.le

end MulOpposite

section Unital


variable [NormedRing E] [StarRing E] [CStarRing E]

theorem norm_one [Nontrivial E] : ‖(1 : E)‖ = 1 := by
  have : 0 < ‖(1 : E)‖ := norm_pos_iff.mpr one_ne_zero
  rw [← mul_left_inj' this.ne', ← norm_star_mul_self, mul_one, star_one, one_mul]

-- see Note [lower instance priority]
instance (priority := 100) [Nontrivial E] : NormOneClass E :=
  ⟨norm_one⟩

theorem norm_coe_unitary [Nontrivial E] (U : unitary E) : ‖(U : E)‖ = 1 := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, one_pow 2, sq, ← CStarRing.norm_star_mul_self,
    Unitary.coe_star_mul_self, CStarRing.norm_one]

@[simp]
theorem norm_of_mem_unitary [Nontrivial E] {U : E} (hU : U ∈ unitary E) : ‖U‖ = 1 :=
  norm_coe_unitary ⟨U, hU⟩

@[simp]
theorem norm_coe_unitary_mul (U : unitary E) (A : E) : ‖(U : E) * A‖ = ‖A‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp [sq, ← CStarRing.norm_star_mul_self, mul_assoc, ← mul_assoc (U : E)⋆]

@[simp]
theorem norm_unitary_smul (U : unitary E) (A : E) : ‖U • A‖ = ‖A‖ :=
  norm_coe_unitary_mul U A

theorem norm_mem_unitary_mul {U : E} (A : E) (hU : U ∈ unitary E) : ‖U * A‖ = ‖A‖ :=
  norm_coe_unitary_mul ⟨U, hU⟩ A

@[simp]
theorem norm_mul_coe_unitary (A : E) (U : unitary E) : ‖A * U‖ = ‖A‖ := by
  simpa [← norm_star (A * U)] using norm_coe_unitary_mul (star U) (star A)

theorem norm_mul_mem_unitary (A : E) {U : E} (hU : U ∈ unitary E) : ‖A * U‖ = ‖A‖ :=
  norm_mul_coe_unitary A ⟨U, hU⟩

end Unital

end CStarRing

section SelfAdjoint

variable [NormedRing E] [StarRing E] [CStarRing E]

theorem IsSelfAdjoint.nnnorm_pow_two_pow {x : E} (hx : IsSelfAdjoint x) (n : ℕ) :
    ‖x ^ 2 ^ n‖₊ = ‖x‖₊ ^ 2 ^ n := by
  induction n with
  | zero => simp only [pow_zero, pow_one]
  | succ k hk =>
    rw [pow_succ', pow_mul', sq, (hx.pow (2 ^ k)).nnnorm_mul_self, hk, pow_mul']

theorem IsSelfAdjoint.norm_pow_two_pow {x : E} (hx : IsSelfAdjoint x) (n : ℕ) :
    ‖x ^ 2 ^ n‖ = ‖x‖ ^ 2 ^ n :=
  congr($(hx.nnnorm_pow_two_pow n))

end SelfAdjoint

theorem IsStarProjection.norm_le [NonUnitalNormedRing E] [StarRing E] [CStarRing E]
    (e : E) (he : IsStarProjection e) : ‖e‖ ≤ 1 := by
  suffices ‖e‖ * (‖e‖ - 1) = 0 by grind [sub_eq_zero]
  simp [mul_sub, ← CStarRing.norm_star_mul_self, he.isSelfAdjoint.star_eq, he.isIdempotentElem.eq]

section starₗᵢ

variable [CommSemiring 𝕜] [StarRing 𝕜]
variable [SeminormedAddCommGroup E] [StarAddMonoid E] [NormedStarGroup E]
variable [Module 𝕜 E] [StarModule 𝕜 E]

variable (𝕜) in
/-- `star` bundled as a linear isometric equivalence -/
def starₗᵢ : E ≃ₗᵢ⋆[𝕜] E :=
  { starAddEquiv with
    map_smul' := star_smul
    norm_map' := norm_star }

@[simp]
theorem coe_starₗᵢ : (starₗᵢ 𝕜 : E → E) = star :=
  rfl

theorem starₗᵢ_apply {x : E} : starₗᵢ 𝕜 x = star x :=
  rfl

@[simp]
theorem starₗᵢ_toContinuousLinearEquiv :
    (starₗᵢ 𝕜 : E ≃ₗᵢ⋆[𝕜] E).toContinuousLinearEquiv = (starL 𝕜 : E ≃L⋆[𝕜] E) :=
  ContinuousLinearEquiv.ext rfl

end starₗᵢ

namespace StarSubalgebra

example {𝕜 A : Type*} [NormedField 𝕜] [StarRing 𝕜] [SeminormedRing A] [StarRing A]
    [NormedAlgebra 𝕜 A] [StarModule 𝕜 A] (S : StarSubalgebra 𝕜 A) :
    NormedAlgebra 𝕜 S := by infer_instance

instance to_cstarRing {R A} [CommRing R] [StarRing R] [NormedRing A] [StarRing A] [CStarRing A]
    [Algebra R A] [StarModule R A] (S : StarSubalgebra R A) : CStarRing S where
  norm_mul_self_le x := @CStarRing.norm_mul_self_le A _ _ _ x

end StarSubalgebra
