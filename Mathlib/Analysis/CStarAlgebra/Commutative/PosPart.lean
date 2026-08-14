/-
Copyright (c) 2026 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/

module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.CStarAlgebra.Fuglede
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Topology.ContinuousMap.StarOrdered
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.RCLike.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range

/-! # monotonicity of `a ↦ a⁺` on commuting elements in a C⋆-algebra -/

open scoped CStarAlgebra ComplexOrder

public section

section ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] (f : C(X, ℝ))

/-- This lemma is perhaps a bit deceptive because the `⁺`,`⁻` that appear on the right and on the
left come from entirely different instances. On the left-hand side, the `⁺`,`⁻` come from the
continuous functional calculus on the C⋆-algebra `C(X, ℂ)`. On the right-hand side, the `⁺`,`⁻`
come from the fact that `C(X, ℝ)` is lattice and an additive group. -/
private lemma ContinuousMap.realToRCLike_posPart_negPart :
    (f.realToRCLike ℂ)⁺ = f⁺.realToRCLike ℂ ∧ (f.realToRCLike ℂ)⁻ = f⁻.realToRCLike ℂ := by
  refine CFC.posPart_negPart_unique ?_ ?_ ?_ ?_ <;> simp_rw [← realToRCLikeStarAlgHom_apply]
  · simp only [← map_sub, posPart_sub_negPart]
  · rw [← map_mul, ← map_zero (realToRCLikeStarAlgHom X ℂ)]
    congr!
    ext x
    obtain hx | hx := le_total 0 (f x)
    · simpa [negPart_def] using Or.inr hx
    · simpa [posPart_def] using Or.inl hx
  · simpa [← realToRCLikeStarAlgHom_apply] using realToRCLike_monotone X ℂ (posPart_nonneg f)
  · simpa [← realToRCLikeStarAlgHom_apply] using realToRCLike_monotone X ℂ (negPart_nonneg f)

lemma ContinuousMap.realToRCLike_posPart : (f.realToRCLike ℂ)⁺ = f⁺.realToRCLike ℂ :=
  f.realToRCLike_posPart_negPart.1

lemma ContinuousMap.realToRCLike_negPart : (f.realToRCLike ℂ)⁻ = f⁻.realToRCLike ℂ :=
  f.realToRCLike_posPart_negPart.2

end ContinuousMap

section Comm

variable (A : Type*) [NonUnitalCommCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open ContinuousMap WeakDual in
protected lemma CStarAlgebra.posPart_mono : Monotone (fun a : A ↦ a⁺) := by
  let φ : A →⋆ₙₐ[ℂ] C(characterSpace ℂ A⁺¹, ℂ) :=
    .comp (gelfandStarTransform A⁺¹) (Unitization.inrNonUnitalStarAlgHom ℂ A)
  have hφ : Isometry φ :=
    StarAlgEquiv.isometry (gelfandStarTransform (A⁺¹)) |>.comp <| Unitization.isometry_inr
  intro a b hab
  simp only
  by_cases ha : IsSelfAdjoint a
  · have hb := ha.of_ge hab
    have key₁ {a : A} (ha : IsSelfAdjoint a) : φ a⁺ = (φ a)⁺ :=
      φ.restrictScalars ℝ |>.map_cfcₙ _ a (hφ := hφ.continuous)
    rw [← NonUnitalStarAlgHom.map_le_map_iff φ hφ.injective, key₁ ha, key₁ hb]
    have := realToRCLike_monotone _ ℂ <| posPart_mono <| rclikeToReal_monotone _ _ <|
      OrderHomClass.mono φ hab
    simpa [← realToRCLike_posPart, IsSelfAdjoint.realToRCLike_rclikeToReal, ha.map φ, hb.map φ]
  · simp [CFC.posPart_def, cfcₙ_apply_of_not_predicate, ha, mt (IsSelfAdjoint.of_le hab) ha]

protected lemma CStarAlgebra.negPart_anti : Antitone (fun a : A ↦ a⁻) := by
  simpa [Function.comp_def] using
    CStarAlgebra.posPart_mono A |>.comp_antitone monotone_id.neg

end Comm

section NonComm

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

instance NonUnitalStarSubalgebra.starOrderedRing (S : NonUnitalStarSubalgebra ℂ A)
    [hS : IsClosed (S : Set A)] : StarOrderedRing S :=
  .of_nonneg_iff' add_le_add_right fun x ↦ by
    refine ⟨?_, ?_⟩
    · intro (hx : 0 ≤ (x : A))
      use ⟨CFC.sqrt (x : A), cfcₙ_nnreal_mem _ x.2⟩
      ext
      simp only [MulMemClass.coe_mul, StarMemClass.coe_star]
      rw [CFC.sqrt_nonneg (x : A) |>.star_eq, CFC.sqrt_mul_sqrt_self ..]
    · rintro ⟨s, hs⟩
      simp [← Subtype.coe_le_coe, hs]

instance StarSubalgebra.starOrderedRing {A : Type*} [CStarAlgebra A] [PartialOrder A]
    [StarOrderedRing A] (S : StarSubalgebra ℂ A) [hS : IsClosed (S : Set A)] :
    StarOrderedRing S :=
  S.toNonUnitalStarSubalgebra.starOrderedRing

open NonUnitalStarAlgebra in
open scoped IsMulCommutative in
protected lemma CStarAlgebra.Commute.posPart_mono {a b : A} (hab : Commute a b) (hle : a ≤ b)
    (ha : IsSelfAdjoint a := by cfc_tac) (hb : IsSelfAdjoint b := by cfc_tac) :
    a⁺ ≤ b⁺ := by
  have := CStarAlgebra.isMulCommutative_nonUnital_adjoin_pair hab
  have : IsClosed ((adjoin ℂ {a, b}).topologicalClosure : Set A) :=
    NonUnitalStarSubalgebra.isClosed_topologicalClosure _
  let a' : (adjoin ℂ {a, b}).topologicalClosure :=
    ⟨a, subset_closure <| subset_adjoin _ _ <| by simp⟩
  let b' : (adjoin ℂ {a, b}).topologicalClosure :=
    ⟨b, subset_closure <| subset_adjoin _ _ <| by simp⟩
  replace hle : a' ≤ b' := hle
  have : a'⁺ ≤ b'⁺ := CStarAlgebra.posPart_mono _ hle
  simp_rw [← Subtype.coe_le_coe, ← NonUnitalStarSubalgebraClass.subtype_apply,
    CFC.posPart_def] at this
  have ha' : IsSelfAdjoint a' := Subtype.ext ha.star_eq
  have hb' : IsSelfAdjoint b' := Subtype.ext hb.star_eq
  rwa [NonUnitalStarAlgHomClass.map_cfcₙ .., NonUnitalStarAlgHomClass.map_cfcₙ ..] at this

protected lemma CStarAlgebra.Commute.negPart_anti {a b : A} (hab : Commute a b) (hle : a ≤ b)
    (ha : IsSelfAdjoint a := by cfc_tac) (hb : IsSelfAdjoint b := by cfc_tac) :
    b⁻ ≤ a⁻ := by
  rw [← CFC.posPart_neg, ← CFC.posPart_neg]
  exact CStarAlgebra.Commute.posPart_mono (by simpa using hab.symm) (by simpa)

end NonComm
