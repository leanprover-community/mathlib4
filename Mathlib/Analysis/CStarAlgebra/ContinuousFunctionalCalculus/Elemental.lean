/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Prereqs

/-! # The range of `cfcHom` is `elementalStarAlgebra`

This file establishes that the range of `cfcHom` is the `elementalStarAlgebra` when the scalar field
is `ℝ` or `ℂ`, and moreover this is also the range of `cfc`. This leads to an induction principle
for terms of the form `cfcHom ha f`, which can then be used to prove theorems such as `cfc_commute`.
We collect those theorems here also.

## Main declarations

+ `CFC.induction_on`: Induction principle for terms of the form `cfcHom ha f`.

## TODO

+ establish analogues for non-unital algebras

-/

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
  rw [StarAlgHom.range_eq_map_top, ← polynomialFunctions.starClosure_topologicalClosure,
    ← StarSubalgebra.topologicalClosure_map _ _ (cfcHom_closedEmbedding ha (R := 𝕜)),
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

-- Do we actually want this version?
open Topology UniformOnFun in
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

theorem commute_cfc {a b : A} [CompactSpace (spectrum 𝕜 a)] (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : 𝕜 → 𝕜) :
    Commute (cfc f a) b :=
  cfc_cases (fun x ↦ Commute x b) a f (Commute.zero_left _) fun hf ha ↦ by
    apply CFC.induction_on (P := fun x ↦ Commute x b) ha ⟨_, hf.restrict⟩ hb₁ hb₂
      (Algebra.commute_algebraMap_left · _) (fun _ _ ↦ ?_) (fun _ _ ↦ ?_) (fun s hs g hg ↦ ?_)
    · simpa using Commute.add_left
    · simpa using Commute.mul_left
    · refine Set.EqOn.closure hs ?_ ?_ hg
      all_goals fun_prop

protected theorem IsSelfAdjoint.commute_cfc {a b : A} [CompactSpace (spectrum 𝕜 a)]
    (ha : IsSelfAdjoint a) (hb₁ : Commute a b) (f : 𝕜 → 𝕜) : Commute (cfc f a) b :=
  commute_cfc hb₁ (ha.star_eq.symm ▸ hb₁) f

-- Move this to `Mathlib.Algebra.Star.Basic`, not necessary for this PR
theorem IsSelfAdjoint.commute_star_right {R : Type*} [Mul R] [StarMul R] {x : R}
    (hx : IsSelfAdjoint x) (y : R) : Commute x (star y) ↔ Commute x y := by
  simpa [hx.star_eq] using commute_star_star (x := x) (y := y)

-- Move this to `Mathlib.Algebra.Star.Basic`, not necessary for this PR
theorem IsSelfAdjoint.commute_star_left {R : Type*} [Mul R] [StarMul R] {x : R}
    (hx : IsSelfAdjoint x) (y : R) : Commute (star y) x ↔ Commute y x := by
  simpa [Commute.symm_iff (a := x)] using hx.commute_star_right y

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

local notation "σₙ" => quasispectrum

open ContinuousMapZero in
@[simp]
lemma cfcₙHom_id' {R A : Type*} {p : A → Prop} [CommSemiring R] [Nontrivial R] [StarRing R]
    [MetricSpace R] [TopologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A]
    [TopologicalSpace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A]
    [NonUnitalContinuousFunctionalCalculus R p] {a : A} (ha : p a) :
    (cfcₙHom ha) (.id rfl : C(σₙ R a, R)₀) = a :=
  cfcₙHom_id ha


open ContinuousMapZero NonUnitalStarSubalgebra in
theorem CFC.induction_on'' (P : A → Prop) {a : A} (ha : p a)
    [CompactSpace (σₙ 𝕜 a)] (f : C(σₙ 𝕜 a, 𝕜)₀)
    (self : P a) (star_self : P (star a))
    (smul : ∀ r : 𝕜, ∀ g, P (cfcₙHom ha g) → P (cfcₙHom ha (R := 𝕜) (r • g)))
    (add : ∀ g₁ g₂, P (cfcₙHom ha g₁) → P (cfcₙHom ha g₂) → P (cfcₙHom ha (R := 𝕜) (g₁ + g₂)))
    (mul : ∀ g₁ g₂, P (cfcₙHom ha g₁) → P (cfcₙHom ha g₂) → P (cfcₙHom ha (R := 𝕜) (g₁ * g₂)))
    (closure : ∀ s, (∀ g ∈ s, P (cfcₙHom ha g)) → ∀ g' ∈ closure s, P (cfcₙHom ha (R := 𝕜) g')) :
    P (cfcₙHom ha f) := by
  refine closure (NonUnitalStarAlgebra.adjoin 𝕜 {(ContinuousMapZero.id rfl : C(σₙ 𝕜 a, 𝕜)₀)})
    (fun f hf ↦ ?_) f <| by simp [(ContinuousMapZero.adjoin_id_dense (s := σₙ 𝕜 a) rfl).closure_eq]
  rw [SetLike.mem_coe, ← mem_toNonUnitalSubalgebra,
    NonUnitalStarAlgebra.adjoin_toNonUnitalSubalgebra] at hf
  induction hf using NonUnitalAlgebra.adjoin_induction' with
  | mem g hg =>
    simp only [Set.star_singleton, Set.union_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hg
    obtain (rfl | rfl) := hg
    all_goals simpa [map_star]
  | add g₁ _ g₂ _ hg₁ hg₂ => exact add _ _ hg₁ hg₂
  | zero => simpa using smul 0 (.id rfl) (by simpa)
  | mul g₁ _ g₂ _ hg₁ hg₂ => exact mul _ _ hg₁ hg₂
  | smul r g _ hg => exact smul r g hg

variable [T2Space A] [TopologicalRing A]

theorem commute_cfcₙ {a b : A} [CompactSpace (σₙ 𝕜 a)] (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : 𝕜 → 𝕜) :
    Commute (cfcₙ f a) b :=
  cfcₙ_cases (fun x ↦ Commute x b) a f (Commute.zero_left _) fun hf hf₀ ha ↦ by
    apply CFC.induction_on'' (P := fun x ↦ Commute x b) ha ⟨⟨_, hf.restrict⟩, hf₀⟩ hb₁ hb₂
      (fun _ _ ↦ ?_) (fun _ _ ↦ ?_) (fun _ _ ↦ ?_) (fun s hs g hg ↦ ?_)
    · simpa using (Commute.smul_left · _)
    · simpa using Commute.add_left
    · simpa using Commute.mul_left
    · refine Set.EqOn.closure hs ?_ ?_ hg
      all_goals fun_prop

protected theorem IsSelfAdjoint.commute_cfcₙ {a b : A} [CompactSpace (σₙ 𝕜 a)]
    (ha : IsSelfAdjoint a) (hb₁ : Commute a b) (f : 𝕜 → 𝕜) : Commute (cfcₙ f a) b :=
  commute_cfcₙ hb₁ (ha.star_eq.symm ▸ hb₁) f

variable [StarModule 𝕜 A] [TopologicalRing A] [ContinuousStar A] [ContinuousConstSMul 𝕜 A]

section foo₁

variable {F R A B : Type*} [CommSemiring R] [StarRing R]
variable [NonUnitalSemiring A] [StarRing A] [NonUnitalSemiring B] [StarRing B]
variable [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]
variable [Module R B]
variable [FunLike F A B] [NonUnitalAlgHomClass F R A B] [NonUnitalStarAlgHomClass F R A B]

open NonUnitalStarSubalgebra in
lemma NonUnitalStarAlgHom.range_eq_map_top (φ : F) :
    NonUnitalStarAlgHom.range φ = map φ (⊤ : NonUnitalStarSubalgebra R A) :=
  NonUnitalStarSubalgebra.ext fun x =>
    ⟨by rintro ⟨a, ha⟩; exact ⟨a, by simp, ha⟩, by rintro ⟨a, -, ha⟩; exact ⟨a, ha⟩⟩

end foo₁

section foo₂

theorem ContinuousMapZero.topologicalClosure_adjoin_id {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜} [Zero s]
    (h0 : (0 : s) = (0 : 𝕜)) [CompactSpace s] :
    (NonUnitalStarAlgebra.adjoin 𝕜 {ContinuousMapZero.id h0}).topologicalClosure = ⊤ :=
  SetLike.ext'_iff.mpr (ContinuousMapZero.adjoin_id_dense h0).closure_eq

end foo₂


open NonUnitalStarSubalgebra in
-- it would be nice if this were about non-unital star subalgebras, but we don't have
-- the topological closure of those yet.
variable (𝕜) in
theorem cfcₙHom_range {a : A} (ha : p a) [CompactSpace (σₙ 𝕜 a)] :
    NonUnitalStarAlgHom.range (cfcₙHom ha (R := 𝕜)) =
      (NonUnitalStarAlgebra.adjoin 𝕜 {a}).topologicalClosure := by
  rw [NonUnitalStarAlgHom.range_eq_map_top, ← ContinuousMapZero.topologicalClosure_adjoin_id rfl,
    ← topologicalClosure_map _ _ (cfcₙHom_closedEmbedding ha (R := 𝕜)),
    NonUnitalStarAlgHom.map_adjoin]
  congr!
  simp [cfcₙHom_id' ha]

open ContinuousMapZero

end NonUnital
