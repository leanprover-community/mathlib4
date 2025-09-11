import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.NonUnital
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.ContinuousMap.ContinuousSqrt
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.Algebra.NonUnitalStarAlgebra

/-! # range of the continuous functional calculus

This file contains results about the range of the continuous functional calculus, and consequences thereof.
-/

open Topology

open scoped CStarAlgebra

section CFCRangeCommute

theorem range_cfc (R : Type*) {A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
    [Algebra R A] [TopologicalSpace A] [StarModule R A] [ContinuousFunctionalCalculus R A p]
    {a : A} (ha : p a) : Set.range (cfc (R := R) · a) = (cfcHom ha (R := R)).range := by
  ext
  constructor
  all_goals rintro ⟨f, rfl⟩
  · exact cfc_cases _ a f (zero_mem _) fun hf ha ↦ ⟨_, rfl⟩
  · exact ⟨Subtype.val.extend f 0, cfcHom_eq_cfc_extend _ ha _ |>.symm⟩

section RCLike

variable (𝕜 : Type*) {A : Type*} {p : A → Prop} [RCLike 𝕜] [Ring A] [StarRing A] [Algebra 𝕜 A]
variable [TopologicalSpace A] [StarModule 𝕜 A] [ContinuousFunctionalCalculus 𝕜 A p]

-- `Topology.ContinuousMap.StoneWeierstrass`
open StarAlgebra in
lemma ContinuousMap.elemental_id_eq_top (s : Set 𝕜) [CompactSpace s] :
    elemental 𝕜 (ContinuousMap.restrict s (.id 𝕜)) = ⊤ := by
  rw [StarAlgebra.elemental, ← polynomialFunctions.starClosure_topologicalClosure,
    polynomialFunctions.starClosure_eq_adjoin_X]
  congr
  exact Polynomial.toContinuousMap_X_eq_id.symm

variable [IsTopologicalRing A] [ContinuousStar A]

open StarAlgebra

open scoped ContinuousFunctionalCalculus in
theorem range_cfcHom {a : A} (ha : p a) :
    (cfcHom ha (R := 𝕜)).range = elemental 𝕜 a := by
  rw [StarAlgHom.range_eq_map_top, ← ContinuousMap.elemental_id_eq_top, StarAlgebra.elemental,
    ← StarSubalgebra.topologicalClosure_map _ _ (cfcHom_isClosedEmbedding ha (R := 𝕜)).isClosedMap
      (cfcHom_continuous ha), StarAlgHom.map_adjoin]
  congr
  simpa using cfcHom_id ha

variable {𝕜}

theorem cfcHom_apply_mem_elemental {a : A} (ha : p a) (f : C(spectrum 𝕜 a, 𝕜)) :
    cfcHom ha f ∈ elemental 𝕜 a :=
  range_cfcHom 𝕜 ha ▸ ⟨f, rfl⟩

@[simp]
theorem cfc_apply_mem_elemental (f : 𝕜 → 𝕜) (a : A) :
    cfc f a ∈ elemental 𝕜 a :=
  cfc_cases _ a f (zero_mem _) fun hf ha ↦
    cfcHom_apply_mem_elemental ha ⟨_, hf.restrict⟩

variable [T2Space A]

open StarSubalgebra elemental in
protected theorem Commute.cfcHom {a b : A} (ha : p a) (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : C(spectrum 𝕜 a, 𝕜)) :
    Commute (cfcHom ha f) b :=
  have hb : b ∈ centralizer 𝕜 {a} := by simpa [mem_centralizer_iff] using ⟨hb₁.eq, hb₂.eq⟩
  le_centralizer_centralizer 𝕜 a (cfcHom_apply_mem_elemental ha f) b (.inl hb) |>.symm

protected theorem IsSelfAdjoint.commute_cfcHom {a b : A} (ha : p a)
    (ha' : IsSelfAdjoint a) (hb : Commute a b) (f : C(spectrum 𝕜 a, 𝕜)) :
    Commute (cfcHom ha f) b :=
  hb.cfcHom ha (ha'.star_eq.symm ▸ hb) f

/-- An element commutes with `cfc f a` if it commutes with both `a` and `star a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfc_real` or `Commute.cfc_nnreal` which don't require
the `Commute (star a) b` hypothesis. -/
protected theorem Commute.cfc {a b : A} (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : 𝕜 → 𝕜) :
    Commute (cfc f a) b :=
  cfc_cases (fun x ↦ Commute x b) a f (Commute.zero_left _)
    fun hf ha ↦ hb₁.cfcHom ha hb₂ ⟨_, hf.restrict⟩

/-- For `a` selfadjoint, an element commutes with `cfc f a` if it commutes with `a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfc_real` or `Commute.cfc_nnreal` which don't require
the `IsSelfAdjoint` hypothesis on `a` (due to the junk value `cfc f a = 0`). -/
protected theorem IsSelfAdjoint.commute_cfc {a b : A}
    (ha : IsSelfAdjoint a) (hb₁ : Commute a b) (f : 𝕜 → 𝕜) :
    Commute (cfc f a) b :=
  hb₁.cfc (ha.star_eq.symm ▸ hb₁) f

end RCLike

open scoped NNReal
variable {A : Type*} [Ring A] [StarRing A] [Algebra ℝ A]
variable [TopologicalSpace A] [StarModule ℝ A] [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [ContinuousStar A] [IsTopologicalRing A] [T2Space A]

/-- A version of `Commute.cfc` or `IsSelfAdjoint.commute_cfc` which does not require any interaction with `star`
when the base ring is `ℝ`. -/
protected theorem Commute.cfc_real {a b : A} (hb : Commute a b) (f : ℝ → ℝ) :
    Commute (cfc f a) b :=
  cfc_cases (fun x ↦ Commute x b) a f (Commute.zero_left _)
    fun hf ha ↦ by
      rw [← cfc_apply ..]
      exact hb.cfc (ha.star_eq.symm ▸ hb) _

variable [PartialOrder A] [NonnegSpectrumClass ℝ A] [StarOrderedRing A]

/-- A version of `Commute.cfc` or `IsSelfAdjoint.commute_cfc` which does not require any interaction with `star`
when the base ring is `ℝ≥0`. -/
protected theorem Commute.cfc_nnreal {a b : A} (hb : Commute a b) (f : ℝ≥0 → ℝ≥0) :
    Commute (cfc f a) b := by
  by_cases ha : 0 ≤ a
  · rw [cfc_nnreal_eq_real]
    exact hb.cfc_real _
  · simp [cfc_apply_of_not_predicate a ha]

-- can we put this next to `cfc_nnreal_eq_real`?
omit [StarModule ℝ A] [ContinuousStar A] in
lemma cfc_real_eq_nnreal (f : ℝ → ℝ) (a : A) (hf_nonneg : ∀ x ∈ spectrum ℝ a, 0 ≤ f x) (ha : 0 ≤ a := by cfc_tac) :
    cfc f a = cfc (fun x : ℝ≥0 ↦ (f x).toNNReal) a := by
  rw [cfc_nnreal_eq_real]
  refine cfc_congr fun x hx ↦ ?_
  rw [x.coe_toNNReal (spectrum_nonneg_of_nonneg ha hx), (f x).coe_toNNReal (hf_nonneg x hx)]

omit [StarModule ℝ A] [ContinuousStar A] in
lemma range_cfc_nnreal_eq_image_cfc_real (a : A) (ha : 0 ≤ a) :
    Set.range (cfc (R := ℝ≥0) · a) = (cfc (R := ℝ) · a) '' {f | ∀ x ∈ spectrum ℝ a, 0 ≤ f x}:= by
  ext
  constructor
  · rintro ⟨f, rfl⟩
    simp only [cfc_nnreal_eq_real f ha]
    exact ⟨_, fun _ _ ↦ by positivity, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    simp only [cfc_real_eq_nnreal f a hf]
    exact ⟨_, rfl⟩

lemma range_cfc_nnreal (a : A) (ha : 0 ≤ a) :
    Set.range (cfc (R := ℝ≥0) · a) = {x | x ∈ StarAlgebra.elemental ℝ a ∧ 0 ≤ x} := by
  rw [range_cfc_nnreal_eq_image_cfc_real a ha, Set.setOf_and, SetLike.setOf_mem_eq,
    ← range_cfcHom _ ha.isSelfAdjoint, ← range_cfc, Set.inter_comm, ← Set.image_preimage_eq_inter_range]
  refine Set.Subset.antisymm (Set.image_mono (fun _ ↦ cfc_nonneg)) ?_
  rintro _ ⟨f, hf, rfl⟩
  simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq, Set.mem_image] at hf ⊢
  obtain (⟨h₁, h₂⟩ | h | h) := by
    simpa only [not_and_or] using em (ContinuousOn f (spectrum ℝ a) ∧ IsSelfAdjoint a)
  · refine ⟨f, ?_, rfl⟩
    rwa [cfc_nonneg_iff f a] at hf
  · exact ⟨0, by simp, by simp [cfc_apply_of_not_continuousOn a h]⟩
  · exact ⟨0, by simp, by simp [cfc_apply_of_not_predicate a h]⟩

end CFCRangeCommute

section NonUnital

theorem range_cfcₙ (R : Type*) {A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R]
    [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Nontrivial R] [NonUnitalRing A]
    [StarRing A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [TopologicalSpace A]
    [StarModule R A] [NonUnitalContinuousFunctionalCalculus R A p] {a : A} (ha : p a) :
    Set.range (cfcₙ (R := R) · a) = NonUnitalStarAlgHom.range (cfcₙHom ha (R := R)) := by
  ext
  constructor
  all_goals rintro ⟨f, rfl⟩
  · exact cfcₙ_cases _ a f (zero_mem _) fun hf hf₀ ha ↦ ⟨_, rfl⟩
  · exact ⟨Subtype.val.extend f 0, cfcₙHom_eq_cfcₙ_extend _ ha _ |>.symm⟩

section RCLike

variable (𝕜 : Type*) {A : Type*} {p : A → Prop} [RCLike 𝕜] [NonUnitalRing A] [StarRing A]
variable [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A]
variable [TopologicalSpace A] [NonUnitalContinuousFunctionalCalculus 𝕜 A p]
variable [ContinuousConstSMul 𝕜 A] [StarModule 𝕜 A] [IsTopologicalRing A] [ContinuousStar A]

open NonUnitalStarAlgebra

-- `Topology.ContinuousMap.StoneWeierstrass`
lemma ContinuousMapZero.elemental_eq_top {𝕜 : Type*} [RCLike 𝕜] {s : Set 𝕜} [Zero s] (h0 : (0 : s) = (0 : 𝕜))
    [CompactSpace s] : elemental 𝕜 (ContinuousMapZero.id h0) = ⊤ :=
  SetLike.ext'_iff.mpr (adjoin_id_dense h0).closure_eq

---- REMOVE ME
-- missing lemma
lemma NonUnitalStarAlgHom.range_eq_map_top {F R A B : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A]
    [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarRing A] [StarModule R A]
    [NonUnitalNonAssocSemiring B] [Module R B] [Star B]
    [FunLike F A B] [NonUnitalAlgHomClass F R A B] [StarHomClass F A B] (φ : F) :
    NonUnitalStarAlgHom.range φ = NonUnitalStarSubalgebra.map φ ⊤ := by
  aesop


open scoped NonUnitalContinuousFunctionalCalculus in
theorem range_cfcₙHom {a : A} (ha : p a) :
    NonUnitalStarAlgHom.range (cfcₙHom ha (R := 𝕜)) = elemental 𝕜 a := by
  rw [NonUnitalStarAlgHom.range_eq_map_top, ← ContinuousMapZero.elemental_eq_top rfl,
    NonUnitalStarAlgebra.elemental, ← NonUnitalStarSubalgebra.topologicalClosure_map _
    (cfcₙHom_isClosedEmbedding ha (R := 𝕜)).isClosedMap (cfcₙHom_continuous ha),
    NonUnitalStarAlgHom.map_adjoin]
  congr
  simpa using cfcₙHom_id ha

variable {𝕜}

open scoped ContinuousMapZero

theorem cfcₙHom_apply_mem_elemental {a : A} (ha : p a) (f : C(quasispectrum 𝕜 a, 𝕜)₀) :
    cfcₙHom ha f ∈ elemental 𝕜 a :=
  range_cfcₙHom 𝕜 ha ▸ ⟨f, rfl⟩

theorem cfcₙ_apply_mem_elemental (f : 𝕜 → 𝕜) (a : A) :
    cfcₙ f a ∈ elemental 𝕜 a :=
  cfcₙ_cases _ a f (zero_mem _) fun hf hf₀ ha ↦
    cfcₙHom_apply_mem_elemental ha ⟨⟨_, hf.restrict⟩, hf₀⟩

variable [T2Space A]

open NonUnitalStarSubalgebra elemental in
protected theorem Commute.cfcₙHom {a b : A} (ha : p a) (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : C(quasispectrum 𝕜 a, 𝕜)₀) :
    Commute (cfcₙHom ha f) b :=
  have hb : b ∈ centralizer 𝕜 {a} := by simpa [mem_centralizer_iff] using ⟨hb₁.eq, hb₂.eq⟩
  le_centralizer_centralizer 𝕜 a (cfcₙHom_apply_mem_elemental ha f) b (.inl hb) |>.symm

protected theorem IsSelfAdjoint.commute_cfcₙHom {a b : A} (ha : p a)
    (ha' : IsSelfAdjoint a) (hb : Commute a b) (f : C(quasispectrum 𝕜 a, 𝕜)₀) :
    Commute (cfcₙHom ha f) b :=
  hb.cfcₙHom ha (ha'.star_eq.symm ▸ hb) f

/-- An element commutes with `cfcₙ f a` if it commutes with both `a` and `star a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfcₙ_real` or `Commute.cfcₙ_nnreal` which don't require
the `Commute (star a) b` hypothesis. -/
protected theorem Commute.cfcₙ {a b : A} (hb₁ : Commute a b)
    (hb₂ : Commute (star a) b) (f : 𝕜 → 𝕜) :
    Commute (cfcₙ f a) b :=
  cfcₙ_cases (fun x ↦ Commute x b) a f (Commute.zero_left _)
    fun hf hf₀ ha ↦ hb₁.cfcₙHom ha hb₂ ⟨⟨_, hf.restrict⟩, hf₀⟩

/-- For `a` selfadjoint, an element commutes with `cfcₙ f a` if it commutes with `a`.

If the base ring is `ℝ` or `ℝ≥0`, see `Commute.cfcₙ_real` or `Commute.cfcₙ_nnreal` which don't require
the `IsSelfAdjoint` hypothesis on `a` (due to the junk value `cfcₙ f a = 0`). -/
protected theorem IsSelfAdjoint.commute_cfcₙ {a b : A}
    (ha : IsSelfAdjoint a) (hb₁ : Commute a b) (f : 𝕜 → 𝕜) :
    Commute (cfcₙ f a) b :=
  hb₁.cfcₙ (ha.star_eq.symm ▸ hb₁) f

end RCLike

open scoped NNReal
variable {A : Type*} [NonUnitalRing A] [StarRing A] [Module ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
variable [TopologicalSpace A] [StarModule ℝ A] [NonUnitalContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [ContinuousStar A] [IsTopologicalRing A] [T2Space A] [ContinuousConstSMul ℝ A]

/-- A version of `Commute.cfcₙ` or `IsSelfAdjoint.commute_cfcₙ` which does not require any interaction with `star`
when the base ring is `ℝ`. -/
protected theorem Commute.cfcₙ_real {a b : A} (hb : Commute a b) (f : ℝ → ℝ) :
    Commute (cfcₙ f a) b :=
  cfcₙ_cases (fun x ↦ Commute x b) a f (Commute.zero_left _)
    fun hf hf0 ha ↦ by
      rw [← cfcₙ_apply ..]
      exact hb.cfcₙ (ha.star_eq.symm ▸ hb) _

variable [PartialOrder A] [NonnegSpectrumClass ℝ A] [StarOrderedRing A]

/-- A version of `Commute.cfcₙ` or `IsSelfAdjoint.commute_cfcₙ` which does not require any interaction with `star`
when the base ring is `ℝ≥0`. -/
protected theorem Commute.cfcₙ_nnreal {a b : A} (hb : Commute a b) (f : ℝ≥0 → ℝ≥0) :
    Commute (cfcₙ f a) b := by
  by_cases ha : 0 ≤ a
  · rw [cfcₙ_nnreal_eq_real]
    exact hb.cfcₙ_real _
  · simp [cfcₙ_apply_of_not_predicate a ha]

-- can we put this next to `cfc_nnreal_eq_real`?
omit [StarModule ℝ A] [ContinuousStar A] [ContinuousConstSMul ℝ A] in
lemma cfcₙ_real_eq_nnreal (f : ℝ → ℝ) (a : A) (hf_nonneg : ∀ x ∈ quasispectrum ℝ a, 0 ≤ f x)
    (ha : 0 ≤ a := by cfc_tac) :
    cfcₙ f a = cfcₙ (fun x : ℝ≥0 ↦ (f x).toNNReal) a := by
  rw [cfcₙ_nnreal_eq_real]
  refine cfcₙ_congr fun x hx ↦ ?_
  rw [x.coe_toNNReal (quasispectrum_nonneg_of_nonneg _ ha _ hx), (f x).coe_toNNReal (hf_nonneg x hx)]

omit [StarModule ℝ A] [ContinuousStar A] [ContinuousConstSMul ℝ A] in
lemma range_cfcₙ_nnreal_eq_image_cfcₙ_real (a : A) (ha : 0 ≤ a) :
    Set.range (cfcₙ (R := ℝ≥0) · a) = (cfcₙ (R := ℝ) · a) '' {f | ∀ x ∈ quasispectrum ℝ a, 0 ≤ f x}:= by
  ext
  constructor
  · rintro ⟨f, rfl⟩
    simp only [cfcₙ_nnreal_eq_real f ha]
    exact ⟨_, fun _ _ ↦ by positivity, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    simp only [cfcₙ_real_eq_nnreal f a hf]
    exact ⟨_, rfl⟩

lemma range_cfcₙ_nnreal (a : A) (ha : 0 ≤ a) :
    Set.range (cfcₙ (R := ℝ≥0) · a) = {x | x ∈ NonUnitalStarAlgebra.elemental ℝ a ∧ 0 ≤ x} := by
  rw [range_cfcₙ_nnreal_eq_image_cfcₙ_real a ha, Set.setOf_and, SetLike.setOf_mem_eq,
    ← range_cfcₙHom _ ha.isSelfAdjoint, ← range_cfcₙ, Set.inter_comm, ← Set.image_preimage_eq_inter_range]
  refine Set.Subset.antisymm (Set.image_mono (fun _ ↦ cfcₙ_nonneg)) ?_
  rintro _ ⟨f, hf, rfl⟩
  simp only [Set.preimage_setOf_eq, Set.mem_setOf_eq, Set.mem_image] at hf ⊢
  obtain (⟨h₁, h₂, h₃⟩ | h | h | h) := by
    simpa only [not_and_or] using
      em (ContinuousOn f (quasispectrum ℝ a) ∧ f 0 = 0 ∧ IsSelfAdjoint a)
  · refine ⟨f, ?_, rfl⟩
    rwa [cfcₙ_nonneg_iff f a] at hf
  · exact ⟨0, by simp, by simp [cfcₙ_apply_of_not_continuousOn a h]⟩
  · exact ⟨0, by simp, by simp [cfcₙ_apply_of_not_map_zero a h]⟩
  · exact ⟨0, by simp, by simp [cfcₙ_apply_of_not_predicate a h]⟩
