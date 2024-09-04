/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique

/-! # The range of `cfcHom` is `elementalStarAlgebra`

This file establishes that the range of `cfcHom` is the `elementalStarAlgebra` when the scalar field
is `ℝ` or `ℂ`, and moreover this is also the range of `cfc`. This leads to an induction principle
for terms of the form `cfcHom ha f`, which can then be used to prove theorems such as `cfc_commute`.
We collect those theorems here also.

## Main declarations

+ `CFC.induction_on`: Induction principle for terms of the form `cfcHom ha f`.

-/

section prereq

-- this doesn't work any better ... :-(
@[elab_as_elim]
lemma cfc_cases' {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R] [MetricSpace R]
    [TopologicalSemiring R] [ContinuousStar R] [TopologicalSpace A] [Ring A]
    [StarRing A] [Algebra R A] [ContinuousFunctionalCalculus R p] {P : A → Prop} {a x : A}
    (hx : x ∈ Set.range (cfc (R := R) · a)) (h₀ : P 0)
    (haf : (hf : ContinuousOn (Classical.choose hx) (spectrum R a)) → (ha : p a) →
      P (cfcHom ha ⟨_, hf.restrict⟩)) :
    P x :=
  Classical.choose_spec hx ▸ cfc_cases P a _ h₀ haf

end prereq

section RCLike

variable {𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A]
variable [TopologicalSpace A] [StarModule 𝕜 A] [ContinuousFunctionalCalculus 𝕜 p]

variable (𝕜) in
theorem cfc_range {a : A} (ha : p a) :
    Set.range (cfc (R := 𝕜) · a) = (cfcHom ha (R := 𝕜)).range := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    by_cases hf : ContinuousOn f (spectrum 𝕜 a)
    · simpa only [cfc_apply f a, SetLike.mem_coe] using ⟨_, rfl⟩
    · simpa only [cfc_apply_of_not_continuousOn a hf] using zero_mem _
  · rintro ⟨f, rfl⟩
    classical
    let f' (x : 𝕜) : 𝕜 := if hx : x ∈ spectrum 𝕜 a then f ⟨x, hx⟩ else 0
    have hff' : f = Set.restrict (spectrum 𝕜 a) f'  := by ext; simp [f']
    have : ContinuousOn f' (spectrum 𝕜 a) :=
      continuousOn_iff_continuous_restrict.mpr (hff' ▸ map_continuous f)
    use f'
    simp only [cfc_apply f' a]
    congr!
    exact hff'.symm

variable [TopologicalRing A] [ContinuousStar A]

variable (𝕜) in
theorem cfcHom_range {a : A} (ha : p a) [CompactSpace (spectrum 𝕜 a)] :
    (cfcHom ha (R := 𝕜)).range = elementalStarAlgebra 𝕜 a := by
  rw [StarAlgHom.range_eq_map_top, ← polynomialFunctions.starClosure_topologicalClosure, ←
    StarSubalgebra.topologicalClosure_map _ _ (cfcHom_closedEmbedding ha (R := 𝕜)),
    polynomialFunctions.starClosure_eq_adjoin_X, StarAlgHom.map_adjoin]
  congr
  rw [Set.image_singleton, Polynomial.toContinuousMapOnAlgHom_apply,
    Polynomial.toContinuousMapOn_X_eq_restrict_id, cfcHom_id ha]

theorem CFC.induction_on (P : A → Prop) {a : A} (ha : p a)
    [CompactSpace (spectrum 𝕜 a)] (f : C(spectrum 𝕜 a, 𝕜))
    (self : P a) (star_self : P (star a)) (algebraMap : ∀ r : 𝕜, P (algebraMap 𝕜 A r))
    (add : ∀ g₁ g₂, P (cfcHom ha g₁) → P (cfcHom ha g₂) → P (cfcHom ha (R := 𝕜) (g₁ + g₂)))
    (mul : ∀ g₁ g₂, P (cfcHom ha g₁) → P (cfcHom ha g₂) → P (cfcHom ha (R := 𝕜) (g₁ * g₂)))
    (closure : ∀ s, (∀ g ∈ s, P (cfcHom ha g)) → ∀ g' ∈ closure s, P (cfcHom ha (R := 𝕜) g')) :
    P (cfcHom ha f) := by
  have hf : cfcHom ha f ∈ elementalStarAlgebra 𝕜 a := cfcHom_range 𝕜 ha ▸ Set.mem_range_self _
  refine elementalStarAlgebra.induction_on 𝕜 hf self star_self algebraMap ?_ ?_ ?_
  all_goals simp only [← cfcHom_range 𝕜 ha]
  · rintro - ⟨f, rfl⟩ - ⟨g, rfl⟩ hf hg
    simpa using add f g hf hg
  · rintro - ⟨f, rfl⟩ - ⟨g, rfl⟩ hf hg
    simpa using mul f g hf hg
  · show ∀ s ⊆ Set.range (cfcHom ha), _
    simpa only [Set.forall_subset_range_iff, Set.forall_mem_image,
      (cfcHom_closedEmbedding ha).closure_image_eq] using closure

open Topology in
open UniformOnFun in
theorem CFC.induction_on' {P : A → Prop} {a x : A}
    [CompactSpace (spectrum 𝕜 a)] (hx : x ∈ Set.range (cfc (R := 𝕜) · a))
    (self : P a) (star_self : P (star a)) (algebraMap : ∀ r : 𝕜, P (algebraMap 𝕜 A r))
    (add : ∀ g₁ g₂, ContinuousOn g₁ (spectrum 𝕜 a) → ContinuousOn g₂ (spectrum 𝕜 a) →
      P (cfc g₁ a) → P (cfc g₂ a) → P (cfc (g₁ + g₂) a))
    (mul : ∀ g₁ g₂, ContinuousOn g₁ (spectrum 𝕜 a) → ContinuousOn g₂ (spectrum 𝕜 a) →
      P (cfc g₁ a) → P (cfc g₂ a) → P (cfc (g₁ * g₂) a))
    (closure : ∀ s : Set (𝕜 → 𝕜), (∀ g ∈ s, ContinuousOn g (spectrum 𝕜 a) ∧ P (cfc g a)) →
      ∀ g' ∈ closure (ofFun {spectrum 𝕜 a} '' s), P (cfc (toFun {spectrum 𝕜 a} g') a)) :
    P x := by
  obtain ⟨f, rfl⟩ := hx
  refine cfc_cases P a f (by simpa using algebraMap 0) fun hf ha ↦ ?_
  have key₁ (g : C(spectrum 𝕜 a, 𝕜)) :
      ContinuousOn (Function.extend Subtype.val g (0 : 𝕜 → 𝕜)) (spectrum 𝕜 a) := by
    rw [continuousOn_iff_continuous_restrict]
    convert map_continuous g
    ext
    simp [Subtype.val_injective.extend_apply]
  have key₂ (g : C(spectrum 𝕜 a, 𝕜)) : g = ⟨_, (key₁ g).restrict⟩ := by
    ext
    simp [Subtype.val_injective.extend_apply]
  refine CFC.induction_on P ha _ self star_self algebraMap (fun g₁ g₂ ↦ ?add')
    (fun g₁ g₂ ↦ ?mul') (fun s hs g' hg' ↦ ?closure')
  case add' =>
    rw [key₂ (g₁ + g₂), key₂ g₁, key₂ g₂, ← cfc_apply _ a, ← cfc_apply _ a, ← cfc_apply _ a]
    convert add _ _ (key₁ g₁) (key₁ g₂) using 3
    refine cfc_congr fun x hx ↦ ?_
    lift x to spectrum 𝕜 a using hx
    simp [Subtype.val_injective.extend_apply]
  case mul' =>
    rw [key₂ (g₁ * g₂), key₂ g₁, key₂ g₂, ← cfc_apply _ a, ← cfc_apply _ a, ← cfc_apply _ a]
    convert mul _ _ (key₁ g₁) (key₁ g₂) using 3
    refine cfc_congr fun x hx ↦ ?_
    lift x to spectrum 𝕜 a using hx
    simp [Subtype.val_injective.extend_apply]
  case closure' =>
    specialize
      closure ((fun g : C(spectrum 𝕜 a, 𝕜) ↦ Function.extend Subtype.val g (0 : 𝕜 → 𝕜)) '' s) <| by
        rintro - ⟨g, hg, rfl⟩
        refine ⟨key₁ g, ?_⟩
        simp only [cfc_apply _ a ha (key₁ g), ← key₂ g]
        exact hs g hg
    specialize closure (ofFun {spectrum 𝕜 a} <| Function.extend Subtype.val g' (0 : 𝕜 → 𝕜))
    simp only [toFun_ofFun, cfc_apply _ a ha (key₁ g'), ← key₂ g'] at closure
    apply closure
    rw [Set.image_image]
    refine mem_closure_image ?_ hg'
    simp only [ContinuousAt, UniformOnFun.tendsto_iff_tendstoUniformlyOn, Set.mem_singleton_iff,
      toFun_ofFun, forall_eq, tendstoUniformlyOn_iff_tendstoUniformly_comp_coe, Function.comp_def,
      Subtype.val_injective.extend_apply]
    rw [← ContinuousMap.tendsto_iff_tendstoUniformly]
    exact Filter.tendsto_id

variable [T2Space A]

theorem commute_cfcHom {a b : A} (ha : p a) [CompactSpace (spectrum 𝕜 a)] (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : C(spectrum 𝕜 a, 𝕜)) :
    Commute (cfcHom ha f) b := by
  apply CFC.induction_on (P := fun x ↦ Commute x b) ha f hb₁ hb₂
    (Algebra.commute_algebraMap_left · _) (fun _ _ ↦ ?_) (fun _ _ ↦ ?_) (fun s hs g hg ↦ ?_)
  · simpa using Commute.add_left
  · simpa using Commute.mul_left
  · refine Set.EqOn.closure hs ?_ ?_ hg
    all_goals fun_prop

protected theorem IsSelfAdjoint.commute_cfcHom {a b : A} (ha : p a) [CompactSpace (spectrum 𝕜 a)]
    (ha' : IsSelfAdjoint a) (hb : Commute a b) (f : C(spectrum 𝕜 a, 𝕜)) :
    Commute (cfcHom ha f) b :=
  commute_cfcHom ha hb (ha'.star_eq.symm ▸ hb) f

theorem commute_cfc {a b : A} [CompactSpace (spectrum 𝕜 a)] (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : 𝕜 → 𝕜) :
    Commute (cfc f a) b :=
  cfc_cases (fun x ↦ Commute x b) a f (Commute.zero_left _)
    fun hf ha ↦ commute_cfcHom ha hb₁ hb₂ ⟨_, hf.restrict⟩

protected theorem IsSelfAdjoint.commute_cfc {a b : A} [CompactSpace (spectrum 𝕜 a)]
    (ha : IsSelfAdjoint a) (hb₁ : Commute a b) (f : 𝕜 → 𝕜) :
    Commute (cfc f a) b :=
  commute_cfc hb₁ (ha.star_eq.symm ▸ hb₁) f

end RCLike

section NonUnital

variable {𝕜 A : Type*} {p : A → Prop} [RCLike 𝕜] [NonUnitalRing A] [StarRing A] [Module 𝕜 A]
variable [SMulCommClass 𝕜 A A] [IsScalarTower 𝕜 A A]
variable [TopologicalSpace A] [NonUnitalContinuousFunctionalCalculus 𝕜 p]

variable (𝕜) in
theorem cfcₙ_range {a : A} (ha : p a) :
    Set.range (cfcₙ (R := 𝕜) · a) = NonUnitalStarAlgHom.range (cfcₙHom ha (R := 𝕜)) := by
  ext x
  constructor
  · rintro ⟨f, rfl⟩
    exact cfcₙ_cases (· ∈ NonUnitalStarAlgHom.range (cfcₙHom ha (R := 𝕜))) a f (zero_mem _)
      (by simp)
  · simp only [NonUnitalStarAlgHom.coe_range, Set.mem_range]
    rintro ⟨f, rfl⟩
    rw [cfcₙHom_eq_cfcₙ_extend 0]
    exact ⟨_, rfl⟩

--variable [TopologicalRing A] [ContinuousStar A]

--variable (𝕜) in
--theorem cfcₙHom_range {a : A} (ha : p a) [CompactSpace (quasispectrum 𝕜 a)] :
    --NonUnitalStarAlgHom.range (cfcₙHom ha (R := 𝕜)) = elementalStarAlgebra 𝕜 a := by
  --rw [StarAlgHom.range_eq_map_top, ← polynomialFunctions.starClosure_topologicalClosure, ←
    --StarSubalgebra.topologicalClosure_map _ _ (cfcHom_closedEmbedding ha (R := 𝕜)),
    --polynomialFunctions.starClosure_eq_adjoin_X, StarAlgHom.map_adjoin]
  --congr
  --rw [Set.image_singleton, Polynomial.toContinuousMapOnAlgHom_apply,
    --Polynomial.toContinuousMapOn_X_eq_restrict_id, cfcHom_id ha]

end NonUnital
