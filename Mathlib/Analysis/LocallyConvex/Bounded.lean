/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.GroupTheory.GroupAction.Pointwise
public import Mathlib.Analysis.LocallyConvex.Basic
public import Mathlib.Analysis.LocallyConvex.BalancedCoreHull
public import Mathlib.Analysis.Seminorm
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Von Neumann Boundedness

This file defines natural or von Neumann bounded sets and proves elementary properties.

## Main declarations

* `Bornology.IsVonNBounded`: A set `s` is von Neumann-bounded if every neighborhood of zero
  absorbs `s`.
* `Bornology.vonNBornology`: The bornology made of the von Neumann-bounded sets.

## Main results

* `Bornology.IsVonNBounded.of_topologicalSpace_le`: A coarser topology admits more
  von Neumann-bounded sets.
* `Bornology.IsVonNBounded.image`: A continuous linear image of a bounded set is bounded.
* `Bornology.isVonNBounded_iff_smul_tendsto_zero`: Given any sequence `ε` of scalars which tends
  to `𝓝[≠] 0`, we have that a set `S` is bounded if and only if for any sequence `x : ℕ → S`,
  `ε • x` tends to 0. This shows that bounded sets are completely determined by sequences, which is
  the key fact for proving that sequential continuity implies continuity for linear maps defined on
  a bornological space

## References

* [Bourbaki, *Topological Vector Spaces*][bourbaki1987]

-/

@[expose] public section


variable {𝕜 𝕜' E F ι : Type*}

open Set Filter Function
open scoped Topology Pointwise


namespace Bornology

section SeminormedRing

section Zero

variable (𝕜)
variable [SeminormedRing 𝕜] [SMul 𝕜 E] [Zero E]
variable [TopologicalSpace E]

/-- A set `s` is von Neumann bounded if every neighborhood of 0 absorbs `s`. -/
def IsVonNBounded (s : Set E) : Prop :=
  ∀ ⦃V⦄, V ∈ 𝓝 (0 : E) → Absorbs 𝕜 V s

variable (E)

@[simp]
theorem isVonNBounded_empty : IsVonNBounded 𝕜 (∅ : Set E) := fun _ _ => Absorbs.empty

variable {𝕜 E}

theorem isVonNBounded_iff (s : Set E) : IsVonNBounded 𝕜 s ↔ ∀ V ∈ 𝓝 (0 : E), Absorbs 𝕜 V s :=
  Iff.rfl

theorem _root_.Filter.HasBasis.isVonNBounded_iff {q : ι → Prop} {s : ι → Set E} {A : Set E}
    (h : (𝓝 (0 : E)).HasBasis q s) : IsVonNBounded 𝕜 A ↔ ∀ i, q i → Absorbs 𝕜 (s i) A := by
  refine ⟨fun hA i hi => hA (h.mem_of_mem hi), fun hA V hV => ?_⟩
  rcases h.mem_iff.mp hV with ⟨i, hi, hV⟩
  exact (hA i hi).mono_left hV

/-- Subsets of bounded sets are bounded. -/
theorem IsVonNBounded.subset {s₁ s₂ : Set E} (h : s₁ ⊆ s₂) (hs₂ : IsVonNBounded 𝕜 s₂) :
    IsVonNBounded 𝕜 s₁ := fun _ hV => (hs₂ hV).mono_right h

@[simp]
theorem isVonNBounded_union {s t : Set E} :
    IsVonNBounded 𝕜 (s ∪ t) ↔ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t := by
  simp only [IsVonNBounded, absorbs_union, forall_and]

/-- The union of two bounded sets is bounded. -/
theorem IsVonNBounded.union {s₁ s₂ : Set E} (hs₁ : IsVonNBounded 𝕜 s₁) (hs₂ : IsVonNBounded 𝕜 s₂) :
    IsVonNBounded 𝕜 (s₁ ∪ s₂) := isVonNBounded_union.2 ⟨hs₁, hs₂⟩

@[nontriviality]
theorem IsVonNBounded.of_boundedSpace [BoundedSpace 𝕜] {s : Set E} : IsVonNBounded 𝕜 s := fun _ _ ↦
  .of_boundedSpace

@[nontriviality]
theorem IsVonNBounded.of_subsingleton [Subsingleton E] {s : Set E} : IsVonNBounded 𝕜 s :=
  fun U hU ↦ .of_forall fun c ↦ calc
    s ⊆ univ := subset_univ s
    _ = c • U := .symm <| Subsingleton.eq_univ_of_nonempty <| (Filter.nonempty_of_mem hU).image _

@[simp]
theorem isVonNBounded_iUnion {ι : Sort*} [Finite ι] {s : ι → Set E} :
    IsVonNBounded 𝕜 (⋃ i, s i) ↔ ∀ i, IsVonNBounded 𝕜 (s i) := by
  simp only [IsVonNBounded, absorbs_iUnion, @forall_comm ι]

theorem isVonNBounded_biUnion {ι : Type*} {I : Set ι} (hI : I.Finite) {s : ι → Set E} :
    IsVonNBounded 𝕜 (⋃ i ∈ I, s i) ↔ ∀ i ∈ I, IsVonNBounded 𝕜 (s i) := by
  have _ := hI.to_subtype
  rw [biUnion_eq_iUnion, isVonNBounded_iUnion, Subtype.forall]

theorem isVonNBounded_sUnion {S : Set (Set E)} (hS : S.Finite) :
    IsVonNBounded 𝕜 (⋃₀ S) ↔ ∀ s ∈ S, IsVonNBounded 𝕜 s := by
  rw [sUnion_eq_biUnion, isVonNBounded_biUnion hS]

end Zero

section ContinuousAdd

variable [SeminormedRing 𝕜] [AddZeroClass E] [TopologicalSpace E] [ContinuousAdd E]
  [DistribSMul 𝕜 E] {s t : Set E}

protected theorem IsVonNBounded.add (hs : IsVonNBounded 𝕜 s) (ht : IsVonNBounded 𝕜 t) :
    IsVonNBounded 𝕜 (s + t) := fun U hU ↦ by
  rcases exists_open_nhds_zero_add_subset hU with ⟨V, hVo, hV, hVU⟩
  exact ((hs <| hVo.mem_nhds hV).add (ht <| hVo.mem_nhds hV)).mono_left hVU

end ContinuousAdd

section IsTopologicalAddGroup

variable [SeminormedRing 𝕜] [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [DistribMulAction 𝕜 E] {s t : Set E}

protected theorem IsVonNBounded.neg (hs : IsVonNBounded 𝕜 s) : IsVonNBounded 𝕜 (-s) := fun U hU ↦ by
  rw [← neg_neg U]
  exact (hs <| neg_mem_nhds_zero _ hU).neg_neg

@[simp]
theorem isVonNBounded_neg : IsVonNBounded 𝕜 (-s) ↔ IsVonNBounded 𝕜 s :=
  ⟨fun h ↦ neg_neg s ▸ h.neg, fun h ↦ h.neg⟩

alias ⟨IsVonNBounded.of_neg, _⟩ := isVonNBounded_neg

protected theorem IsVonNBounded.sub (hs : IsVonNBounded 𝕜 s) (ht : IsVonNBounded 𝕜 t) :
    IsVonNBounded 𝕜 (s - t) := by
  rw [sub_eq_add_neg]
  exact hs.add ht.neg

end IsTopologicalAddGroup

end SeminormedRing

section MultipleTopologies

variable [SeminormedRing 𝕜] [AddCommGroup E] [Module 𝕜 E]

/-- If a topology `t'` is coarser than `t`, then any set `s` that is bounded with respect to
`t` is bounded with respect to `t'`. -/
theorem IsVonNBounded.of_topologicalSpace_le {t t' : TopologicalSpace E} (h : t ≤ t') {s : Set E}
    (hs : @IsVonNBounded 𝕜 E _ _ _ t s) : @IsVonNBounded 𝕜 E _ _ _ t' s := fun _ hV =>
  hs <| (le_iff_nhds t t').mp h 0 hV

end MultipleTopologies

lemma isVonNBounded_iff_tendsto_smallSets_nhds {𝕜 E : Type*} [NormedDivisionRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {S : Set E} :
    IsVonNBounded 𝕜 S ↔ Tendsto (· • S : 𝕜 → Set E) (𝓝 0) (𝓝 0).smallSets := by
  rw [tendsto_smallSets_iff]
  refine forall₂_congr fun V hV ↦ ?_
  simp only [absorbs_iff_eventually_nhds_zero (mem_of_mem_nhds hV), mapsTo_iff_image_subset,
    image_smul]

alias ⟨IsVonNBounded.tendsto_smallSets_nhds, _⟩ := isVonNBounded_iff_tendsto_smallSets_nhds

lemma isVonNBounded_iff_absorbing_le {𝕜 E : Type*} [NormedDivisionRing 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] {S : Set E} :
    IsVonNBounded 𝕜 S ↔ Filter.absorbing 𝕜 S ≤ 𝓝 0 :=
  .rfl

lemma isVonNBounded_pi_iff {𝕜 ι : Type*} {E : ι → Type*} [NormedDivisionRing 𝕜]
    [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    {S : Set (∀ i, E i)} : IsVonNBounded 𝕜 S ↔ ∀ i, IsVonNBounded 𝕜 (eval i '' S) := by
  simp_rw [isVonNBounded_iff_tendsto_smallSets_nhds, nhds_pi, Filter.pi, smallSets_iInf,
    smallSets_comap_eq_comap_image, tendsto_iInf, tendsto_comap_iff, Function.comp_def,
    ← image_smul, image_image, eval, Pi.smul_apply, Pi.zero_apply]

section Image

variable {𝕜₁ 𝕜₂ : Type*} [NormedDivisionRing 𝕜₁] [NormedDivisionRing 𝕜₂] [AddCommGroup E]
  [Module 𝕜₁ E] [AddCommGroup F] [Module 𝕜₂ F] [TopologicalSpace E] [TopologicalSpace F]

/-- A continuous linear image of a bounded set is bounded. -/
protected theorem IsVonNBounded.image {σ : 𝕜₁ →+* 𝕜₂} [RingHomSurjective σ] [RingHomIsometric σ]
    {s : Set E} (hs : IsVonNBounded 𝕜₁ s) (f : E →SL[σ] F) : IsVonNBounded 𝕜₂ (f '' s) := by
  have : map σ (𝓝 0) = 𝓝 0 := by
    rw [σ.isometry.isEmbedding.map_nhds_eq, σ.surjective.range_eq, nhdsWithin_univ, map_zero]
  have hf₀ : Tendsto f (𝓝 0) (𝓝 0) := f.continuous.tendsto' 0 0 (map_zero f)
  simp only [isVonNBounded_iff_tendsto_smallSets_nhds, ← this, tendsto_map'_iff] at hs ⊢
  simpa only [comp_def, image_smul_setₛₗ] using hf₀.image_smallSets.comp hs

end Image

section sequence

theorem IsVonNBounded.smul_tendsto_zero [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
    {S : Set E} {ε : ι → 𝕜} {x : ι → E} {l : Filter ι}
    (hS : IsVonNBounded 𝕜 S) (hxS : ∀ᶠ n in l, x n ∈ S) (hε : Tendsto ε l (𝓝 0)) :
    Tendsto (ε • x) l (𝓝 0) :=
  (hS.tendsto_smallSets_nhds.comp hε).of_smallSets <| hxS.mono fun _ ↦ smul_mem_smul_set

variable [NontriviallyNormedField 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E] [ContinuousSMul 𝕜 E]

theorem isVonNBounded_of_smul_tendsto_zero {ε : ι → 𝕜} {l : Filter ι} [l.NeBot]
    (hε : ∀ᶠ n in l, ε n ≠ 0) {S : Set E}
    (H : ∀ x : ι → E, (∀ n, x n ∈ S) → Tendsto (ε • x) l (𝓝 0)) : IsVonNBounded 𝕜 S := by
  rw [(nhds_basis_balanced 𝕜 E).isVonNBounded_iff]
  by_contra! ⟨V, ⟨hV, hVb⟩, hVS⟩
  have : ∀ᶠ n in l, ∃ x : S, ε n • (x : E) ∉ V := by
    filter_upwards [hε] with n hn
    rw [absorbs_iff_norm] at hVS
    push Not at hVS
    rcases hVS ‖(ε n)⁻¹‖ with ⟨a, haε, haS⟩
    rcases Set.not_subset.mp haS with ⟨x, hxS, hx⟩
    refine ⟨⟨x, hxS⟩, fun hnx => ?_⟩
    rw [← Set.mem_inv_smul_set_iff₀ hn] at hnx
    exact hx (hVb.smul_mono haε hnx)
  rcases this.choice with ⟨x, hx⟩
  refine Filter.frequently_false l (Filter.Eventually.frequently ?_)
  filter_upwards [hx,
    (H (_ ∘ x) fun n => (x n).2).eventually (eventually_mem_set.mpr hV)] using fun n => id

/-- Given any sequence `ε` of scalars which tends to `𝓝[≠] 0`, we have that a set `S` is bounded
  if and only if for any sequence `x : ℕ → S`, `ε • x` tends to 0. This actually works for any
  indexing type `ι`, but in the special case `ι = ℕ` we get the important fact that convergent
  sequences fully characterize bounded sets. -/
theorem isVonNBounded_iff_smul_tendsto_zero {ε : ι → 𝕜} {l : Filter ι} [l.NeBot]
    (hε : Tendsto ε l (𝓝[≠] 0)) {S : Set E} :
    IsVonNBounded 𝕜 S ↔ ∀ x : ι → E, (∀ n, x n ∈ S) → Tendsto (ε • x) l (𝓝 0) :=
  ⟨fun hS _ hxS => hS.smul_tendsto_zero (Eventually.of_forall hxS) (le_trans hε nhdsWithin_le_nhds),
    isVonNBounded_of_smul_tendsto_zero (by exact hε self_mem_nhdsWithin)⟩

end sequence

/-- If a set is von Neumann bounded with respect to a smaller field,
then it is also von Neumann bounded with respect to a larger field.
See also `Bornology.IsVonNBounded.restrict_scalars` below. -/
theorem IsVonNBounded.extend_scalars [NontriviallyNormedField 𝕜]
    {E : Type*} [AddCommGroup E] [Module 𝕜 E]
    (𝕝 : Type*) [NontriviallyNormedField 𝕝] [NormedAlgebra 𝕜 𝕝]
    [Module 𝕝 E] [TopologicalSpace E] [ContinuousSMul 𝕝 E] [IsScalarTower 𝕜 𝕝 E]
    {s : Set E} (h : IsVonNBounded 𝕜 s) : IsVonNBounded 𝕝 s := by
  obtain ⟨ε, hε, hε₀⟩ : ∃ ε : ℕ → 𝕜, Tendsto ε atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ε n ≠ 0 := by
    simpa only [tendsto_nhdsWithin_iff] using exists_seq_tendsto (𝓝[≠] (0 : 𝕜))
  refine isVonNBounded_of_smul_tendsto_zero (ε := (ε · • 1)) (by simpa) fun x hx ↦ ?_
  have := h.smul_tendsto_zero (.of_forall hx) hε
  simpa only [Pi.smul_def', smul_one_smul]

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [TopologicalSpace E]

/-- The closure of a bounded set is bounded. -/
theorem IsVonNBounded.closure [T1Space E] [RegularSpace E] [ContinuousConstSMul 𝕜 E]
    {a : Set E} (ha : IsVonNBounded 𝕜 a) : IsVonNBounded 𝕜 (closure a) := by
  intro V hV
  rcases exists_mem_nhds_isClosed_subset hV with ⟨W, hW₁, hW₂, hW₃⟩
  specialize ha hW₁
  filter_upwards [ha] with b ha'
  grw [closure_mono ha', closure_smul₀ b]
  apply smul_set_mono
  grw [closure_subset_iff_isClosed.mpr hW₂, hW₃]

variable [ContinuousSMul 𝕜 E]

/-- Singletons are bounded. -/
theorem isVonNBounded_singleton (x : E) : IsVonNBounded 𝕜 ({x} : Set E) := fun _ hV =>
  (absorbent_nhds_zero hV).absorbs

@[simp]
theorem isVonNBounded_insert (x : E) {s : Set E} :
    IsVonNBounded 𝕜 (insert x s) ↔ IsVonNBounded 𝕜 s := by
  simp only [← singleton_union, isVonNBounded_union, isVonNBounded_singleton, true_and]

protected alias ⟨_, IsVonNBounded.insert⟩ := isVonNBounded_insert

/-- Finite sets are bounded. -/
theorem _root_.Set.Finite.isVonNBounded {s : Set E} (hs : s.Finite) :
    IsVonNBounded 𝕜 s := fun _ hV ↦
  (absorbent_nhds_zero hV).absorbs_finite hs

section ContinuousAdd

variable [ContinuousAdd E] {s t : Set E}

protected theorem IsVonNBounded.vadd (hs : IsVonNBounded 𝕜 s) (x : E) :
    IsVonNBounded 𝕜 (x +ᵥ s) := by
  rw [← singleton_vadd]
  -- TODO: dot notation timeouts in the next line
  exact IsVonNBounded.add (isVonNBounded_singleton x) hs

@[simp]
theorem isVonNBounded_vadd (x : E) : IsVonNBounded 𝕜 (x +ᵥ s) ↔ IsVonNBounded 𝕜 s :=
  ⟨fun h ↦ by simpa using h.vadd (-x), fun h ↦ h.vadd x⟩

theorem IsVonNBounded.of_add_right (hst : IsVonNBounded 𝕜 (s + t)) (hs : s.Nonempty) :
    IsVonNBounded 𝕜 t :=
  let ⟨x, hx⟩ := hs
  (isVonNBounded_vadd x).mp <| hst.subset <| image_subset_image2_right hx

theorem IsVonNBounded.of_add_left (hst : IsVonNBounded 𝕜 (s + t)) (ht : t.Nonempty) :
    IsVonNBounded 𝕜 s :=
  ((add_comm s t).subst hst).of_add_right ht

theorem isVonNBounded_add_of_nonempty (hs : s.Nonempty) (ht : t.Nonempty) :
    IsVonNBounded 𝕜 (s + t) ↔ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t :=
  ⟨fun h ↦ ⟨h.of_add_left ht, h.of_add_right hs⟩, and_imp.2 IsVonNBounded.add⟩

theorem isVonNBounded_add :
    IsVonNBounded 𝕜 (s + t) ↔ s = ∅ ∨ t = ∅ ∨ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t := by
  rcases s.eq_empty_or_nonempty with rfl | hs; · simp
  rcases t.eq_empty_or_nonempty with rfl | ht; · simp
  simp [hs.ne_empty, ht.ne_empty, isVonNBounded_add_of_nonempty hs ht]

@[simp]
theorem isVonNBounded_add_self : IsVonNBounded 𝕜 (s + s) ↔ IsVonNBounded 𝕜 s := by
  rcases s.eq_empty_or_nonempty with rfl | hs <;> simp [isVonNBounded_add_of_nonempty, *]

theorem IsVonNBounded.of_sub_left (hst : IsVonNBounded 𝕜 (s - t)) (ht : t.Nonempty) :
    IsVonNBounded 𝕜 s :=
  ((sub_eq_add_neg s t).subst hst).of_add_left ht.neg

end ContinuousAdd

section IsTopologicalAddGroup

variable [IsTopologicalAddGroup E] {s t : Set E}

theorem IsVonNBounded.of_sub_right (hst : IsVonNBounded 𝕜 (s - t)) (hs : s.Nonempty) :
    IsVonNBounded 𝕜 t :=
  (((sub_eq_add_neg s t).subst hst).of_add_right hs).of_neg

theorem isVonNBounded_sub_of_nonempty (hs : s.Nonempty) (ht : t.Nonempty) :
    IsVonNBounded 𝕜 (s - t) ↔ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t := by
  simp [sub_eq_add_neg, isVonNBounded_add_of_nonempty, hs, ht]

theorem isVonNBounded_sub :
    IsVonNBounded 𝕜 (s - t) ↔ s = ∅ ∨ t = ∅ ∨ IsVonNBounded 𝕜 s ∧ IsVonNBounded 𝕜 t := by
  simp [sub_eq_add_neg, isVonNBounded_add]

end IsTopologicalAddGroup

/-- The union of all bounded set is the whole space. -/
theorem sUnion_isVonNBounded_eq_univ : ⋃₀ setOf (IsVonNBounded 𝕜) = (Set.univ : Set E) :=
  Set.eq_univ_iff_forall.mpr fun x =>
    Set.mem_sUnion.mpr ⟨{x}, isVonNBounded_singleton _, Set.mem_singleton _⟩

@[deprecated (since := "2025-11-14")]
alias isVonNBounded_covers := sUnion_isVonNBounded_eq_univ

variable (𝕜 E)

-- See note [reducible non-instances]
/-- The von Neumann bornology defined by the von Neumann bounded sets.

Note that this is not registered as an instance, in order to avoid diamonds with the
metric bornology. -/
abbrev vonNBornology : Bornology E :=
  Bornology.ofBounded (setOf (IsVonNBounded 𝕜)) (isVonNBounded_empty 𝕜 E)
    (fun _ hs _ ht => hs.subset ht) (fun _ hs _ => hs.union) isVonNBounded_singleton

variable {E}

@[simp]
theorem isBounded_iff_isVonNBounded {s : Set E} :
    @IsBounded _ (vonNBornology 𝕜 E) s ↔ IsVonNBounded 𝕜 s :=
  isBounded_ofBounded_iff _

end NormedField

end Bornology

section IsUniformAddGroup

variable (𝕜) [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
variable [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]

theorem TotallyBounded.isVonNBounded {s : Set E} (hs : TotallyBounded s) :
    Bornology.IsVonNBounded 𝕜 s := by
  if h : ∃ x : 𝕜, 1 < ‖x‖ then
    letI : NontriviallyNormedField 𝕜 := ⟨h⟩
    rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero] at hs
    intro U hU
    have h : Filter.Tendsto (fun x : E × E => x.fst + x.snd) (𝓝 0) (𝓝 0) :=
      continuous_add.tendsto' _ _ (zero_add _)
    have h' := (nhds_basis_balanced 𝕜 E).prod (nhds_basis_balanced 𝕜 E)
    simp_rw [← nhds_prod_eq, id] at h'
    rcases h.basis_left h' U hU with ⟨x, hx, h''⟩
    rcases hs x.snd hx.2.1 with ⟨t, ht, hs⟩
    refine Absorbs.mono_right ?_ hs
    rw [ht.absorbs_biUnion]
    have hx_fstsnd : x.fst + x.snd ⊆ U := add_subset_iff.mpr fun z1 hz1 z2 hz2 ↦
      h'' <| mk_mem_prod hz1 hz2
    refine fun y _ => Absorbs.mono_left ?_ hx_fstsnd
    exact (absorbent_nhds_zero hx.1.1).vadd_absorbs hx.2.2.absorbs_self
  else
    haveI : BoundedSpace 𝕜 := ⟨Metric.isBounded_iff.2 ⟨1, by simp_all [dist_eq_norm]⟩⟩
    exact Bornology.IsVonNBounded.of_boundedSpace

end IsUniformAddGroup

variable (𝕜) in
theorem IsCompact.isVonNBounded [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E] {s : Set E}
    (hs : IsCompact s) : Bornology.IsVonNBounded 𝕜 s :=
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  hs.totallyBounded.isVonNBounded 𝕜

variable (𝕜) in
theorem Filter.Tendsto.isVonNBounded_range [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
    {f : ℕ → E} {x : E} (hf : Tendsto f atTop (𝓝 x)) : Bornology.IsVonNBounded 𝕜 (range f) :=
  letI := IsTopologicalAddGroup.rightUniformSpace E
  haveI := isUniformAddGroup_of_addCommGroup (G := E)
  hf.cauchySeq.totallyBounded_range.isVonNBounded 𝕜

variable (𝕜) in
protected theorem Bornology.IsVonNBounded.restrict_scalars_of_nontrivial
    [NormedField 𝕜] [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜'] [Nontrivial 𝕜']
    [Zero E] [TopologicalSpace E]
    [SMul 𝕜 E] [MulAction 𝕜' E] [IsScalarTower 𝕜 𝕜' E] {s : Set E}
    (h : IsVonNBounded 𝕜' s) : IsVonNBounded 𝕜 s := by
  intro V hV
  refine (h hV).restrict_scalars <| AntilipschitzWith.tendsto_cobounded (K := ‖(1 : 𝕜')‖₊⁻¹) ?_
  refine AntilipschitzWith.of_le_mul_nndist fun x y ↦ ?_
  rw [nndist_eq_nnnorm, nndist_eq_nnnorm, ← sub_smul, nnnorm_smul, ← div_eq_inv_mul,
    mul_div_cancel_right₀ _ (nnnorm_ne_zero_iff.2 one_ne_zero)]

variable (𝕜) in
protected theorem Bornology.IsVonNBounded.restrict_scalars
    [NormedField 𝕜] [NormedRing 𝕜'] [NormedAlgebra 𝕜 𝕜']
    [Zero E] [TopologicalSpace E]
    [SMul 𝕜 E] [MulActionWithZero 𝕜' E] [IsScalarTower 𝕜 𝕜' E] {s : Set E}
    (h : IsVonNBounded 𝕜' s) : IsVonNBounded 𝕜 s :=
  match subsingleton_or_nontrivial 𝕜' with
  | .inl _ =>
    have : Subsingleton E := MulActionWithZero.subsingleton 𝕜' E
    IsVonNBounded.of_subsingleton
  | .inr _ =>
    h.restrict_scalars_of_nontrivial _

section VonNBornologyEqMetric

namespace NormedSpace

section NormedField

variable (𝕜)
variable [NormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem isVonNBounded_of_isBounded {s : Set E} (h : Bornology.IsBounded s) :
    Bornology.IsVonNBounded 𝕜 s := by
  rcases h.subset_ball 0 with ⟨r, hr⟩
  rw [Metric.nhds_basis_ball.isVonNBounded_iff]
  rw [← ball_normSeminorm 𝕜 E] at hr ⊢
  exact fun ε hε ↦ ((normSeminorm 𝕜 E).ball_zero_absorbs_ball_zero hε).mono_right hr

variable (E)

theorem isVonNBounded_ball (r : ℝ) : Bornology.IsVonNBounded 𝕜 (Metric.ball (0 : E) r) :=
  isVonNBounded_of_isBounded _ Metric.isBounded_ball

theorem isVonNBounded_closedBall (r : ℝ) :
    Bornology.IsVonNBounded 𝕜 (Metric.closedBall (0 : E) r) :=
  isVonNBounded_of_isBounded _ Metric.isBounded_closedBall

end NormedField

variable (𝕜)
variable [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

theorem isVonNBounded_iff {s : Set E} : Bornology.IsVonNBounded 𝕜 s ↔ Bornology.IsBounded s := by
  refine ⟨fun h ↦ ?_, isVonNBounded_of_isBounded _⟩
  rcases (h (Metric.ball_mem_nhds 0 zero_lt_one)).exists_pos with ⟨ρ, hρ, hρball⟩
  rcases NormedField.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩
  specialize hρball a ha.le
  rw [← ball_normSeminorm 𝕜 E, Seminorm.smul_ball_zero (norm_pos_iff.1 <| hρ.trans ha),
    ball_normSeminorm] at hρball
  exact Metric.isBounded_ball.subset hρball

theorem isVonNBounded_iff' {s : Set E} :
    Bornology.IsVonNBounded 𝕜 s ↔ ∃ r : ℝ, ∀ x ∈ s, ‖x‖ ≤ r := by
  rw [NormedSpace.isVonNBounded_iff, isBounded_iff_forall_norm_le]

theorem image_isVonNBounded_iff {α : Type*} {f : α → E} {s : Set α} :
    Bornology.IsVonNBounded 𝕜 (f '' s) ↔ ∃ r : ℝ, ∀ x ∈ s, ‖f x‖ ≤ r := by
  simp_rw [isVonNBounded_iff', Set.forall_mem_image]

/-- In a normed space, the von Neumann bornology (`Bornology.vonNBornology`) is equal to the
metric bornology. -/
theorem vonNBornology_eq : Bornology.vonNBornology 𝕜 E = PseudoMetricSpace.toBornology := by
  rw [Bornology.ext_iff_isBounded]
  intro s
  rw [Bornology.isBounded_iff_isVonNBounded]
  exact isVonNBounded_iff _

theorem isBounded_iff_subset_smul_ball {s : Set E} :
    Bornology.IsBounded s ↔ ∃ a : 𝕜, s ⊆ a • Metric.ball (0 : E) 1 := by
  rw [← isVonNBounded_iff 𝕜]
  constructor
  · intro h
    rcases (h (Metric.ball_mem_nhds 0 zero_lt_one)).exists_pos with ⟨ρ, _, hρball⟩
    rcases NormedField.exists_lt_norm 𝕜 ρ with ⟨a, ha⟩
    exact ⟨a, hρball a ha.le⟩
  · rintro ⟨a, ha⟩
    exact ((isVonNBounded_ball 𝕜 E 1).image (a • (1 : E →L[𝕜] E))).subset ha

theorem isBounded_iff_subset_smul_closedBall {s : Set E} :
    Bornology.IsBounded s ↔ ∃ a : 𝕜, s ⊆ a • Metric.closedBall (0 : E) 1 := by
  constructor
  · rw [isBounded_iff_subset_smul_ball 𝕜]
    exact Exists.imp fun a ha => ha.trans <| Set.smul_set_mono <| Metric.ball_subset_closedBall
  · rw [← isVonNBounded_iff 𝕜]
    rintro ⟨a, ha⟩
    exact ((isVonNBounded_closedBall 𝕜 E 1).image (a • (1 : E →L[𝕜] E))).subset ha

end NormedSpace

end VonNBornologyEqMetric

section QuasiCompleteSpace

/-- A locally convex space is quasi-complete if every closed and von Neumann bounded set is
complete. -/
class QuasiCompleteSpace (𝕜 : Type*) (E : Type*) [Zero E] [UniformSpace E] [SeminormedRing 𝕜]
    [SMul 𝕜 E] : Prop where
  /-- A locally convex space is quasi-complete if every closed and von Neumann bounded set is
  complete. -/
  quasiComplete : ∀ ⦃s : Set E⦄, Bornology.IsVonNBounded 𝕜 s → IsClosed s → IsComplete s

variable {𝕜 : Type*} {E : Type*} [Zero E] [UniformSpace E] [SeminormedRing 𝕜] [SMul 𝕜 E]

/-- A complete space is quasi-complete with respect to any scalar ring. -/
instance [CompleteSpace E] : QuasiCompleteSpace 𝕜 E where
  quasiComplete _ _ := IsClosed.isComplete

/-- [Bourbaki, *Topological Vector Spaces*, III §1.6][bourbaki1987] -/
theorem isCompact_closure_of_totallyBounded_quasiComplete {E : Type*} {𝕜 : Type*} [NormedField 𝕜]
    [AddCommGroup E] [Module 𝕜 E] [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul 𝕜 E]
    [QuasiCompleteSpace 𝕜 E] {s : Set E} (hs : TotallyBounded s) : IsCompact (closure s) :=
  hs.closure.isCompact_of_isComplete
    (QuasiCompleteSpace.quasiComplete (TotallyBounded.isVonNBounded 𝕜 (TotallyBounded.closure hs))
    isClosed_closure)

end QuasiCompleteSpace
