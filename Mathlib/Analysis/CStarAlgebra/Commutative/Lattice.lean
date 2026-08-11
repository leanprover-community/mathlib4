module

public import Mathlib.Analysis.CStarAlgebra.GelfandDuality
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.CStarAlgebra.Spectrum
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Topology.ContinuousMap.StarOrdered
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
public import Mathlib.Analysis.RCLike.ContinuousMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range


public section

lemma IsSelfAdjoint.of_map {F A B : Type*} [AddCancelMonoid A] [AddMonoid B]
    [StarAddMonoid A] [StarAddMonoid B]
    [FunLike F A B] [StarHomClass F A B] [AddMonoidHomClass F A B] (f : F)
    {x : A} (hx : IsSelfAdjoint (f x)) (hf : Function.Injective f) :
    IsSelfAdjoint x := by
  have : star x + x = x + x := hf <| by simp [map_star, hx.star_eq]
  simpa

open CStarAlgebra in
lemma IsSelfAdjoint.map_quasispectrum_real {F A B : Type*}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]
    {a : A} (ha : IsSelfAdjoint a) (φ : F) (hφ : Function.Injective φ) :
    quasispectrum ℝ (φ a) = quasispectrum ℝ a := by
  replace hφ : Function.Injective (φ : A →⋆ₙₐ[ℂ] B) := hφ
  simpa [Unitization.starMap_inr, ← Unitization.quasispectrum_eq_spectrum_inr']
    using (ha.inr ℂ).map_spectrum_real _ (Unitization.starMap_injective hφ)

section

variable {F A B : Type*}
    [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    [NonUnitalCStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

/-- A non-unital star monomorphism between C⋆-algebras is an order embedding. -/
def StarAlgHom.orderEmbedding (φ : A →⋆ₙₐ[ℂ] B) (hφ : Function.Injective φ) :
    A ↪o B where
  toFun := φ
  inj' := hφ
  map_rel_iff' := by
    intros a b
    simp only [Function.Embedding.coeFn_mk]
    refine ⟨?_, (OrderHomClass.mono φ ·)⟩
    rw [← sub_nonneg, ← sub_nonneg (a := b), ← map_sub φ]
    simp_rw [nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts, QuasispectrumRestricts.nnreal_iff]
    rintro ⟨h₁, h₂⟩
    have h_sa := h₁.of_map φ hφ
    exact ⟨h_sa, by rwa [← h_sa.map_quasispectrum_real φ hφ]⟩

/-- A non-unital star monomorphism between C⋆-algebras is an order embedding. -/
protected lemma StarAlgHom.map_le_map_iff (f : F) (hf : Function.Injective f) {x y : A} :
    f x ≤ f y ↔ x ≤ y :=
  (orderEmbedding (f : A →⋆ₙₐ[ℂ] B) hf).le_iff_le

protected lemma StarAlgHom.map_lt_map_iff (f : F) (hf : Function.Injective f) {x y : A} :
    f x < f y ↔ x < y :=
  (orderEmbedding (f : A →⋆ₙₐ[ℂ] B) hf).lt_iff_lt

end

section cfc_mem

open NNReal in
theorem cfcₙ_nnreal_mem {𝕜 A : Type*}
    [RCLike 𝕜] [NonUnitalRing A] [StarRing A] [Module ℝ A]
    [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [TopologicalSpace A]
    [ContinuousConstSMul ℝ A] [StarModule ℝ A] [IsTopologicalRing A]
    [ContinuousStar A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
    [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] [T2Space A]
    {S : Type*} [MulAction 𝕜 A] [SetLike S A]
    [NonUnitalSubringClass S A] [IsScalarTower ℝ 𝕜 A]
    [SMulMemClass S 𝕜 A] [StarMemClass S A] {s : S} [hs : IsClosed (s : Set A)]
    (f : ℝ≥0 → ℝ≥0) {a : A} (has : a ∈ s) :
    cfcₙ f a ∈ s := by
  by_cases ha : 0 ≤ a
  · rw [cfcₙ_nnreal_eq_real ..]
    exact cfcₙ_mem _ has
  · simp [cfcₙ_apply_of_not_predicate _ ha]

end cfc_mem

section Comm

variable {A : Type*} [NonUnitalCommCStarAlgebra A]

open scoped CStarAlgebra ComplexOrder
open WeakDual

private noncomputable def φ : A →⋆ₙₐ[ℂ] C(characterSpace ℂ A⁺¹, ℂ) :=
  .comp (gelfandStarTransform A⁺¹) (Unitization.inrNonUnitalStarAlgHom ℂ A)

private lemma isometry_φ : Isometry (φ (A := A)) :=
    StarAlgEquiv.isometry (gelfandStarTransform (A⁺¹)) |>.comp <| Unitization.isometry_inr

variable [PartialOrder A] [StarOrderedRing A]

example : Monotone (φ (A := A)) := OrderHomClass.monotone φ

section

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] (f : C(X, ℝ))

/-- This lemma is tricky, because the `⁺` that appears on the right and on the left come
from entirely different instances. -/
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

end

open ContinuousMap in
protected lemma CStarAlgebra.posPart_mono : Monotone (fun a : A ↦ a⁺) := by
  intro a b hab
  simp only
  by_cases ha : IsSelfAdjoint a
  · have hb := ha.of_ge hab
    have key₁ {a : A} (ha : IsSelfAdjoint a) : φ a⁺ = (φ a)⁺ :=
      φ.restrictScalars ℝ |>.map_cfcₙ _ a (hφ := isometry_φ.continuous)
    rw [← StarAlgHom.map_le_map_iff (φ (A := A)) isometry_φ.injective, key₁ ha, key₁ hb]
    have := realToRCLike_monotone _ ℂ <| posPart_mono <| rclikeToReal_monotone _ _ <|
      OrderHomClass.mono φ hab
    simpa [← realToRCLike_posPart, IsSelfAdjoint.realToRCLike_rclikeToReal, ha.map φ, hb.map φ]
  · simp [CFC.posPart_def, cfcₙ_apply_of_not_predicate, ha, mt (IsSelfAdjoint.of_le hab) ha]

protected lemma CStarAlgebra.negPart_anti : Antitone (fun a : A ↦ a⁻) := by
  simpa [Function.comp_def] using
    CStarAlgebra.posPart_mono (A := A) |>.comp_antitone monotone_id.neg

end Comm

variable {A : Type*} [NonUnitalCStarAlgebra A]


open NonUnitalStarAlgebra in
lemma CStarAlgebra.isMulCommutative_adjoin {s : Set A} (hs : ∀ x ∈ s, IsStarNormal x)
    (hs' : s.Pairwise Commute) :
    IsMulCommutative (adjoin ℂ s) := by
  apply NonUnitalStarAlgebra.isMulCommutative_adjoin
  · intro x hx y hy
    obtain (rfl | hxy) := eq_or_ne x y
    · rfl
    · exact hs' hx hy hxy
  · intro x hx y hy
    obtain (rfl | hxy) := eq_or_ne x y
    · exact (hs x hx).star_comm_self.symm.eq
    · exact (hs y hy).commute_star_right (hs' hx hy hxy) |>.eq

open NonUnitalStarAlgebra in
lemma CStarAlgebra.isMulCommutative_adjoin_pair {x y : A} (h : Commute x y)
    (hx : IsStarNormal x := by cfc_tac) (hy : IsStarNormal y := by cfc_tac) :
    IsMulCommutative (adjoin ℂ {x, y}) :=
  isMulCommutative_adjoin (by grind) (by grind [Set.Pairwise])

variable [PartialOrder A] [StarOrderedRing A]

instance (S : NonUnitalStarSubalgebra ℂ A) [hS : IsClosed (S : Set A)] :
    StarOrderedRing S :=
  .of_nonneg_iff' add_le_add_right fun x ↦ by
    refine ⟨?_, ?_⟩
    · intro (hx : 0 ≤ (x : A))
      use ⟨CFC.sqrt (x : A), cfcₙ_nnreal_mem _ x.2⟩
      ext
      simp only [MulMemClass.coe_mul, StarMemClass.coe_star]
      rw [CFC.sqrt_nonneg (x : A) |>.star_eq, CFC.sqrt_mul_sqrt_self ..]
    · rintro ⟨s, hs⟩
      simp [← Subtype.coe_le_coe, hs]

open NonUnitalStarAlgebra in
open scoped IsMulCommutative in
protected lemma CStarAlgebra.Commute.posPart_mono {a b : A} (hab : Commute a b) (hle : a ≤ b)
    (ha : IsSelfAdjoint a := by cfc_tac) (hb : IsSelfAdjoint b := by cfc_tac) :
    a⁺ ≤ b⁺ := by
  have := CStarAlgebra.isMulCommutative_adjoin_pair hab
  have : IsClosed ((adjoin ℂ {a, b}).topologicalClosure : Set A) :=
    NonUnitalStarSubalgebra.isClosed_topologicalClosure _
  let _ : NonUnitalCommCStarAlgebra (adjoin ℂ {a, b}).topologicalClosure :=
    {  mul_comm := by sorry } -- automatic from an open PR.
  let a' : (adjoin ℂ {a, b}).topologicalClosure :=
    ⟨a, subset_closure <| subset_adjoin _ _ <| by simp⟩
  let b' : (adjoin ℂ {a, b}).topologicalClosure :=
    ⟨b, subset_closure <| subset_adjoin _ _ <| by simp⟩
  replace hle : a' ≤ b' := hle
  have : a'⁺ ≤ b'⁺ := CStarAlgebra.posPart_mono hle
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
