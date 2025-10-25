/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.AffineSpace.Combination
import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Affine independence

This file defines affinely independent families of points.

## Main definitions

* `AffineIndependent` defines affinely independent families of points
  as those where no nontrivial weighted subtraction is `0`.  This is
  proved equivalent to two other formulations: linear independence of
  the results of subtracting a base point in the family from the other
  points in the family, or any equal affine combinations having the
  same weights.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/


noncomputable section

open Finset Function Module
open scoped Affine

section AffineIndependent

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*}

/-- An indexed family is said to be affinely independent if no
nontrivial weighted subtractions (where the sum of weights is 0) are
0. -/
def AffineIndependent (p : ι → P) : Prop :=
  ∀ (s : Finset ι) (w : ι → k),
    ∑ i ∈ s, w i = 0 → s.weightedVSub p w = (0 : V) → ∀ i ∈ s, w i = 0

/-- The definition of `AffineIndependent`. -/
theorem affineIndependent_def (p : ι → P) :
    AffineIndependent k p ↔
      ∀ (s : Finset ι) (w : ι → k),
        ∑ i ∈ s, w i = 0 → s.weightedVSub p w = (0 : V) → ∀ i ∈ s, w i = 0 :=
  Iff.rfl

/-- A family with at most one point is affinely independent. -/
theorem affineIndependent_of_subsingleton [Subsingleton ι] (p : ι → P) : AffineIndependent k p :=
  fun _ _ h _ i hi => Fintype.eq_of_subsingleton_of_sum_eq h i hi

/-- A family indexed by a `Fintype` is affinely independent if and
only if no nontrivial weighted subtractions over `Finset.univ` (where
the sum of the weights is 0) are 0. -/
theorem affineIndependent_iff_of_fintype [Fintype ι] (p : ι → P) :
    AffineIndependent k p ↔
      ∀ w : ι → k, ∑ i, w i = 0 → Finset.univ.weightedVSub p w = (0 : V) → ∀ i, w i = 0 := by
  constructor
  · exact fun h w hw hs i => h Finset.univ w hw hs i (Finset.mem_univ _)
  · intro h s w hw hs i hi
    rw [Finset.weightedVSub_indicator_subset _ _ (Finset.subset_univ s)] at hs
    rw [← Finset.sum_indicator_subset _ (Finset.subset_univ s)] at hw
    replace h := h ((↑s : Set ι).indicator w) hw hs i
    simpa [hi] using h

@[simp] lemma affineIndependent_vadd {p : ι → P} {v : V} :
    AffineIndependent k (v +ᵥ p) ↔ AffineIndependent k p := by
  simp +contextual [AffineIndependent, weightedVSub_vadd]

protected alias ⟨AffineIndependent.of_vadd, AffineIndependent.vadd⟩ := affineIndependent_vadd

@[simp] lemma affineIndependent_smul {G : Type*} [Group G] [DistribMulAction G V]
    [SMulCommClass G k V] {p : ι → V} {a : G} :
    AffineIndependent k (a • p) ↔ AffineIndependent k p := by
  simp +contextual [AffineIndependent,
    ← smul_comm (α := V) a, ← smul_sum, smul_eq_zero_iff_eq]

protected alias ⟨AffineIndependent.of_smul, AffineIndependent.smul⟩ := affineIndependent_smul

/-- A family is affinely independent if and only if the differences
from a base point in that family are linearly independent. -/
theorem affineIndependent_iff_linearIndependent_vsub (p : ι → P) (i1 : ι) :
    AffineIndependent k p ↔ LinearIndependent k fun i : { x // x ≠ i1 } => (p i -ᵥ p i1 : V) := by
  classical
    constructor
    · intro h
      rw [linearIndependent_iff']
      intro s g hg i hi
      set f : ι → k := fun x => if hx : x = i1 then -∑ y ∈ s, g y else g ⟨x, hx⟩ with hfdef
      let s2 : Finset ι := insert i1 (s.map (Embedding.subtype _))
      have hfg : ∀ x : { x // x ≠ i1 }, g x = f x := by grind
      rw [hfg]
      have hf : ∑ ι ∈ s2, f ι = 0 := by
        rw [Finset.sum_insert
            (Finset.notMem_map_subtype_of_not_property s (Classical.not_not.2 rfl)),
          Finset.sum_subtype_map_embedding fun x _ => (hfg x).symm]
        rw [hfdef]
        dsimp only
        rw [dif_pos rfl]
        exact neg_add_cancel _
      have hs2 : s2.weightedVSub p f = (0 : V) := by
        set f2 : ι → V := fun x => f x • (p x -ᵥ p i1) with hf2def
        set g2 : { x // x ≠ i1 } → V := fun x => g x • (p x -ᵥ p i1)
        have hf2g2 : ∀ x : { x // x ≠ i1 }, f2 x = g2 x := by
          simp only [g2, hf2def]
          refine fun x => ?_
          rw [hfg]
        rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s2 f p hf (p i1),
          Finset.weightedVSubOfPoint_insert, Finset.weightedVSubOfPoint_apply,
          Finset.sum_subtype_map_embedding fun x _ => hf2g2 x]
        exact hg
      exact h s2 f hf hs2 i (Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨i, hi, rfl⟩))
    · intro h
      rw [linearIndependent_iff'] at h
      intro s w hw hs i hi
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w p hw (p i1), ←
        s.weightedVSubOfPoint_erase w p i1, Finset.weightedVSubOfPoint_apply] at hs
      let f : ι → V := fun i => w i • (p i -ᵥ p i1)
      have hs2 : (∑ i ∈ (s.erase i1).subtype fun i => i ≠ i1, f i) = 0 := by
        rw [← hs]
        convert Finset.sum_subtype_of_mem f fun x => Finset.ne_of_mem_erase
      have h2 := h ((s.erase i1).subtype fun i => i ≠ i1) (fun x => w x) hs2
      simp_rw [Finset.mem_subtype] at h2
      have h2b : ∀ i ∈ s, i ≠ i1 → w i = 0 := fun i his hi =>
        h2 ⟨i, hi⟩ (Finset.mem_erase_of_ne_of_mem hi his)
      exact Finset.eq_zero_of_sum_eq_zero hw h2b i hi

/-- A set is affinely independent if and only if the differences from
a base point in that set are linearly independent. -/
theorem affineIndependent_set_iff_linearIndependent_vsub {s : Set P} {p₁ : P} (hp₁ : p₁ ∈ s) :
    AffineIndependent k (fun p => p : s → P) ↔
      LinearIndependent k (fun v => v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}) → V) := by
  rw [affineIndependent_iff_linearIndependent_vsub k (fun p => p : s → P) ⟨p₁, hp₁⟩]
  constructor
  · intro h
    have hv : ∀ v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}), (v : V) +ᵥ p₁ ∈ s \ {p₁} := fun v =>
      (vsub_left_injective p₁).mem_set_image.1 ((vadd_vsub (v : V) p₁).symm ▸ v.property)
    let f : (fun p : P => (p -ᵥ p₁ : V)) '' (s \ {p₁}) → { x : s // x ≠ ⟨p₁, hp₁⟩ } := fun x =>
      ⟨⟨(x : V) +ᵥ p₁, Set.mem_of_mem_diff (hv x)⟩, fun hx =>
        Set.notMem_of_mem_diff (hv x) (Subtype.ext_iff.1 hx)⟩
    convert h.comp f fun x1 x2 hx =>
        Subtype.ext (vadd_right_cancel p₁ (Subtype.ext_iff.1 (Subtype.ext_iff.1 hx)))
    ext v
    exact (vadd_vsub (v : V) p₁).symm
  · intro h
    let f : { x : s // x ≠ ⟨p₁, hp₁⟩ } → (fun p : P => (p -ᵥ p₁ : V)) '' (s \ {p₁}) := fun x =>
      ⟨((x : s) : P) -ᵥ p₁, ⟨x, ⟨⟨(x : s).property, fun hx => x.property (Subtype.ext hx)⟩, rfl⟩⟩⟩
    convert h.comp f fun x1 x2 hx =>
        Subtype.ext (Subtype.ext (vsub_left_cancel (Subtype.ext_iff.1 hx)))

/-- A set of nonzero vectors is linearly independent if and only if,
given a point `p₁`, the vectors added to `p₁` and `p₁` itself are
affinely independent. -/
theorem linearIndependent_set_iff_affineIndependent_vadd_union_singleton {s : Set V}
    (hs : ∀ v ∈ s, v ≠ (0 : V)) (p₁ : P) : LinearIndependent k (fun v => v : s → V) ↔
    AffineIndependent k (fun p => p : ({p₁} ∪ (fun v => v +ᵥ p₁) '' s : Set P) → P) := by
  rw [affineIndependent_set_iff_linearIndependent_vsub k
      (Set.mem_union_left _ (Set.mem_singleton p₁))]
  have h : (fun p => (p -ᵥ p₁ : V)) '' (({p₁} ∪ (fun v => v +ᵥ p₁) '' s) \ {p₁}) = s := by
    simp_rw [Set.union_diff_left, Set.image_diff (vsub_left_injective p₁), Set.image_image,
      Set.image_singleton, vsub_self, vadd_vsub, Set.image_id']
    exact Set.diff_singleton_eq_self fun h => hs 0 h rfl
  rw [h]

/-- A family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point
have equal `Set.indicator`. -/
theorem affineIndependent_iff_indicator_eq_of_affineCombination_eq (p : ι → P) :
    AffineIndependent k p ↔
      ∀ (s1 s2 : Finset ι) (w1 w2 : ι → k),
        ∑ i ∈ s1, w1 i = 1 →
          ∑ i ∈ s2, w2 i = 1 →
            s1.affineCombination k p w1 = s2.affineCombination k p w2 →
              Set.indicator (↑s1) w1 = Set.indicator (↑s2) w2 := by
  classical
    constructor
    · intro ha s1 s2 w1 w2 hw1 hw2 heq
      ext i
      by_cases hi : i ∈ s1 ∪ s2
      · rw [← sub_eq_zero]
        rw [← Finset.sum_indicator_subset w1 (s1.subset_union_left (s₂ := s2))] at hw1
        rw [← Finset.sum_indicator_subset w2 (s1.subset_union_right)] at hw2
        have hws : (∑ i ∈ s1 ∪ s2, (Set.indicator (↑s1) w1 - Set.indicator (↑s2) w2) i) = 0 := by
          simp [hw1, hw2]
        rw [Finset.affineCombination_indicator_subset w1 p (s1.subset_union_left (s₂ := s2)),
          Finset.affineCombination_indicator_subset w2 p s1.subset_union_right,
          ← @vsub_eq_zero_iff_eq V, Finset.affineCombination_vsub] at heq
        exact ha (s1 ∪ s2) (Set.indicator (↑s1) w1 - Set.indicator (↑s2) w2) hws heq i hi
      · simp_all
    · intro ha s w hw hs i0 hi0
      let w1 : ι → k := Function.update (Function.const ι 0) i0 1
      have hw1 : ∑ i ∈ s, w1 i = 1 := by
        rw [Finset.sum_update_of_mem hi0]
        simp only [Finset.sum_const_zero, add_zero, const_apply]
      have hw1s : s.affineCombination k p w1 = p i0 :=
        s.affineCombination_of_eq_one_of_eq_zero w1 p hi0 (Function.update_self ..)
          fun _ _ hne => Function.update_of_ne hne ..
      let w2 := w + w1
      have hw2 : ∑ i ∈ s, w2 i = 1 := by
        simp_all only [w2, Pi.add_apply, Finset.sum_add_distrib, zero_add]
      have hw2s : s.affineCombination k p w2 = p i0 := by
        simp_all only [w2, ← Finset.weightedVSub_vadd_affineCombination, zero_vadd]
      replace ha := ha s s w2 w1 hw2 hw1 (hw1s.symm ▸ hw2s)
      have hws : w2 i0 - w1 i0 = 0 := by
        rw [← Finset.mem_coe] at hi0
        rw [← Set.indicator_of_mem hi0 w2, ← Set.indicator_of_mem hi0 w1, ha, sub_self]
      simpa [w2] using hws

/-- A finite family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point are equal. -/
theorem affineIndependent_iff_eq_of_fintype_affineCombination_eq [Fintype ι] (p : ι → P) :
    AffineIndependent k p ↔ ∀ w1 w2 : ι → k, ∑ i, w1 i = 1 → ∑ i, w2 i = 1 →
    Finset.univ.affineCombination k p w1 = Finset.univ.affineCombination k p w2 → w1 = w2 := by
  rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq]
  constructor
  · intro h w1 w2 hw1 hw2 hweq
    simpa only [Set.indicator_univ, Finset.coe_univ] using h _ _ w1 w2 hw1 hw2 hweq
  · intro h s1 s2 w1 w2 hw1 hw2 hweq
    have hw1' : (∑ i, (s1 : Set ι).indicator w1 i) = 1 := by
      rwa [Finset.sum_indicator_subset _ (Finset.subset_univ s1)]
    have hw2' : (∑ i, (s2 : Set ι).indicator w2 i) = 1 := by
      rwa [Finset.sum_indicator_subset _ (Finset.subset_univ s2)]
    rw [Finset.affineCombination_indicator_subset w1 p (Finset.subset_univ s1),
      Finset.affineCombination_indicator_subset w2 p (Finset.subset_univ s2)] at hweq
    exact h _ _ hw1' hw2' hweq

variable {k}

/-- If we single out one member of an affine-independent family of points and affinely transport
all others along the line joining them to this member, the resulting new family of points is affine-
independent.

This is the affine version of `LinearIndependent.units_smul`. -/
theorem AffineIndependent.units_lineMap {p : ι → P} (hp : AffineIndependent k p) (j : ι)
    (w : ι → Units k) : AffineIndependent k fun i => AffineMap.lineMap (p j) (p i) (w i : k) := by
  rw [affineIndependent_iff_linearIndependent_vsub k _ j] at hp ⊢
  simp only [AffineMap.lineMap_vsub_left, AffineMap.coe_const, AffineMap.lineMap_same, const_apply]
  exact hp.units_smul fun i => w i

theorem AffineIndependent.indicator_eq_of_affineCombination_eq {p : ι → P}
    (ha : AffineIndependent k p) (s₁ s₂ : Finset ι) (w₁ w₂ : ι → k) (hw₁ : ∑ i ∈ s₁, w₁ i = 1)
    (hw₂ : ∑ i ∈ s₂, w₂ i = 1) (h : s₁.affineCombination k p w₁ = s₂.affineCombination k p w₂) :
    Set.indicator (↑s₁) w₁ = Set.indicator (↑s₂) w₂ :=
  (affineIndependent_iff_indicator_eq_of_affineCombination_eq k p).1 ha s₁ s₂ w₁ w₂ hw₁ hw₂ h

/-- An affinely independent family is injective, if the underlying
ring is nontrivial. -/
protected theorem AffineIndependent.injective [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) : Function.Injective p := by
  intro i j hij
  rw [affineIndependent_iff_linearIndependent_vsub _ _ j] at ha
  by_contra hij'
  refine ha.ne_zero ⟨i, hij'⟩ (vsub_eq_zero_iff_eq.mpr ?_)
  simp_all only [ne_eq]

/-- If a family is affinely independent, so is any subfamily given by
composition of an embedding into index type with the original
family. -/
theorem AffineIndependent.comp_embedding {ι2 : Type*} (f : ι2 ↪ ι) {p : ι → P}
    (ha : AffineIndependent k p) : AffineIndependent k (p ∘ f) := by
  classical
    intro fs w hw hs i0 hi0
    let fs' := fs.map f
    let w' i := if h : ∃ i2, f i2 = i then w h.choose else 0
    have hw' : ∀ i2 : ι2, w' (f i2) = w i2 := by
      intro i2
      have h : ∃ i : ι2, f i = f i2 := ⟨i2, rfl⟩
      have hs : h.choose = i2 := f.injective h.choose_spec
      simp_rw [w', dif_pos h, hs]
    have hw's : ∑ i ∈ fs', w' i = 0 := by
      rw [← hw, Finset.sum_map]
      simp [hw']
    have hs' : fs'.weightedVSub p w' = (0 : V) := by
      rw [← hs, Finset.weightedVSub_map]
      congr with i
      simp_all only [comp_apply]
    rw [← ha fs' w' hw's hs' (f i0) ((Finset.mem_map' _).2 hi0), hw']

/-- If a family is affinely independent, so is any subfamily indexed
by a subtype of the index type. -/
protected theorem AffineIndependent.subtype {p : ι → P} (ha : AffineIndependent k p) (s : Set ι) :
    AffineIndependent k fun i : s => p i :=
  ha.comp_embedding (Embedding.subtype _)

/-- If an indexed family of points is affinely independent, so is the
corresponding set of points. -/
protected theorem AffineIndependent.range {p : ι → P} (ha : AffineIndependent k p) :
    AffineIndependent k (fun x => x : Set.range p → P) := by
  let f : Set.range p → ι := fun x => x.property.choose
  have hf : ∀ x, p (f x) = x := fun x => x.property.choose_spec
  let fe : Set.range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert ha.comp_embedding fe
  ext
  simp [fe, hf]

theorem affineIndependent_equiv {ι' : Type*} (e : ι ≃ ι') {p : ι' → P} :
    AffineIndependent k (p ∘ e) ↔ AffineIndependent k p := by
  refine ⟨?_, AffineIndependent.comp_embedding e.toEmbedding⟩
  intro h
  have : p = p ∘ e ∘ e.symm.toEmbedding := by
    ext
    simp
  rw [this]
  exact h.comp_embedding e.symm.toEmbedding

/-- If a set of points is affinely independent, so is any subset. -/
protected theorem AffineIndependent.mono {s t : Set P}
    (ha : AffineIndependent k (fun x => x : t → P)) (hs : s ⊆ t) :
    AffineIndependent k (fun x => x : s → P) :=
  ha.comp_embedding (s.embeddingOfSubset t hs)

/-- If the range of an injective indexed family of points is affinely
independent, so is that family. -/
theorem AffineIndependent.of_set_of_injective {p : ι → P}
    (ha : AffineIndependent k (fun x => x : Set.range p → P)) (hi : Function.Injective p) :
    AffineIndependent k p :=
  ha.comp_embedding
    (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun _ _ h => hi (Subtype.mk_eq_mk.1 h)⟩ :
      ι ↪ Set.range p)

/-- If an affine combination of affinely independent points lies in the affine span of a subset
of those points, all weights outside that subset are zero. -/
lemma AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan {p : ι → P}
    (ha : AffineIndependent k p) {fs : Finset ι} {w : ι → k} (hw : ∑ i ∈ fs, w i = 1) {s : Set ι}
    (hm : fs.affineCombination k p w ∈ affineSpan k (p '' s)) {i : ι} (hifs : i ∈ fs)
    (his : i ∉ s) : w i = 0 := by
  obtain ⟨fs', w', hfs's, hw', he⟩ := eq_affineCombination_of_mem_affineSpan_image hm
  have hi' : (fs : Set ι).indicator w i = 0 := by
    rw [ha.indicator_eq_of_affineCombination_eq fs fs' w w' hw hw' he]
    exact Set.indicator_of_notMem (Set.notMem_subset hfs's his) w'
  rw [Set.indicator_apply_eq_zero] at hi'
  exact hi' (Finset.mem_coe.2 hifs)

lemma AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq {ι₂ : Type*}
    {p : ι → P} (ha : AffineIndependent k p) {s₁ : Finset ι} {s₂ : Finset ι₂} {w₁ : ι → k}
    {w₂ : ι₂ → k} (hw₁ : ∑ i ∈ s₁, w₁ i = 1) (hw₂ : ∑ i ∈ s₂, w₂ i = 1) (e : ι₂ ↪ ι)
    (h : s₂.affineCombination k (p ∘ e) w₂ = s₁.affineCombination k p w₁) :
    Set.indicator (s₂.map e) (extend e w₂ 0) = Set.indicator s₁ w₁ := by
  have hw₂e : extend e w₂ 0 ∘ e = w₂ := extend_comp e.injective _ _
  rw [← hw₂e, ← affineCombination_map] at h
  refine (ha.indicator_eq_of_affineCombination_eq s₁ (s₂.map e) _ _ hw₁ ?_ h.symm).symm
  rw [sum_map]
  convert hw₂ with i hi
  exact e.injective.extend_apply _ _ _

lemma AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype
    [Fintype ι] {ι₂ : Type*} [Fintype ι₂] {p : ι → P} (ha : AffineIndependent k p) {w₁ : ι → k}
    {w₂ : ι₂ → k} (hw₁ : ∑ i, w₁ i = 1) (hw₂ : ∑ i, w₂ i = 1) (e : ι₂ ↪ ι)
    (h : Finset.univ.affineCombination k (p ∘ e) w₂ = Finset.univ.affineCombination k p w₁) :
    Set.indicator (Set.range e) (extend e w₂ 0) = w₁ := by
  simpa using ha.indicator_extend_eq_of_affineCombination_comp_embedding_eq hw₁ hw₂ e h

section Composition

variable {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]

/-- If the image of a family of points in affine space under an affine transformation is affine-
independent, then the original family of points is also affine-independent. -/
theorem AffineIndependent.of_comp {p : ι → P} (f : P →ᵃ[k] P₂) (hai : AffineIndependent k (f ∘ p)) :
    AffineIndependent k p := by
  rcases isEmpty_or_nonempty ι with h | h
  · apply affineIndependent_of_subsingleton
  obtain ⟨i⟩ := h
  rw [affineIndependent_iff_linearIndependent_vsub k p i]
  simp_rw [affineIndependent_iff_linearIndependent_vsub k (f ∘ p) i, Function.comp_apply, ←
    f.linearMap_vsub] at hai
  exact LinearIndependent.of_comp f.linear hai

/-- The image of a family of points in affine space, under an injective affine transformation, is
affine-independent. -/
theorem AffineIndependent.map' {p : ι → P} (hai : AffineIndependent k p) (f : P →ᵃ[k] P₂)
    (hf : Function.Injective f) : AffineIndependent k (f ∘ p) := by
  rcases isEmpty_or_nonempty ι with h | h
  · apply affineIndependent_of_subsingleton
  obtain ⟨i⟩ := h
  rw [affineIndependent_iff_linearIndependent_vsub k p i] at hai
  simp_rw [affineIndependent_iff_linearIndependent_vsub k (f ∘ p) i, Function.comp_apply, ←
    f.linearMap_vsub]
  have hf' : LinearMap.ker f.linear = ⊥ := by rwa [LinearMap.ker_eq_bot, f.linear_injective_iff]
  exact LinearIndependent.map' hai f.linear hf'

/-- Injective affine maps preserve affine independence. -/
theorem AffineMap.affineIndependent_iff {p : ι → P} (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    AffineIndependent k (f ∘ p) ↔ AffineIndependent k p :=
  ⟨AffineIndependent.of_comp f, fun hai => AffineIndependent.map' hai f hf⟩

/-- Affine equivalences preserve affine independence of families of points. -/
theorem AffineEquiv.affineIndependent_iff {p : ι → P} (e : P ≃ᵃ[k] P₂) :
    AffineIndependent k (e ∘ p) ↔ AffineIndependent k p :=
  e.toAffineMap.affineIndependent_iff e.toEquiv.injective

/-- Affine equivalences preserve affine independence of subsets. -/
theorem AffineEquiv.affineIndependent_set_of_eq_iff {s : Set P} (e : P ≃ᵃ[k] P₂) :
    AffineIndependent k ((↑) : e '' s → P₂) ↔ AffineIndependent k ((↑) : s → P) := by
  have : e ∘ ((↑) : s → P) = ((↑) : e '' s → P₂) ∘ (e : P ≃ P₂).image s := rfl
  -- This used to be `rw`, but we need `erw` after https://github.com/leanprover/lean4/pull/2644
  erw [← e.affineIndependent_iff, this, affineIndependent_equiv]

end Composition

/-- If a family is affinely independent, and the spans of points
indexed by two subsets of the index type have a point in common, those
subsets of the index type have an element in common, if the underlying
ring is nontrivial. -/
theorem AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) {s1 s2 : Set ι} {p0 : P} (hp0s1 : p0 ∈ affineSpan k (p '' s1))
    (hp0s2 : p0 ∈ affineSpan k (p '' s2)) : ∃ i : ι, i ∈ s1 ∩ s2 := by
  rw [Set.image_eq_range] at hp0s1 hp0s2
  rw [mem_affineSpan_iff_eq_affineCombination, ←
    Finset.eq_affineCombination_subset_iff_eq_affineCombination_subtype] at hp0s1 hp0s2
  rcases hp0s1 with ⟨fs1, hfs1, w1, hw1, hp0s1⟩
  rcases hp0s2 with ⟨fs2, hfs2, w2, hw2, hp0s2⟩
  rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq] at ha
  replace ha := ha fs1 fs2 w1 w2 hw1 hw2 (hp0s1 ▸ hp0s2)
  have hnz : ∑ i ∈ fs1, w1 i ≠ 0 := hw1.symm ▸ one_ne_zero
  rcases Finset.exists_ne_zero_of_sum_ne_zero hnz with ⟨i, hifs1, hinz⟩
  simp_rw [← Set.indicator_of_mem (Finset.mem_coe.2 hifs1) w1, ha] at hinz
  use i, hfs1 hifs1
  exact hfs2 (Set.mem_of_indicator_ne_zero hinz)

/-- If a family is affinely independent, the spans of points indexed
by disjoint subsets of the index type are disjoint, if the underlying
ring is nontrivial. -/
theorem AffineIndependent.affineSpan_disjoint_of_disjoint [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) {s1 s2 : Set ι} (hd : Disjoint s1 s2) :
    Disjoint (affineSpan k (p '' s1) : Set P) (affineSpan k (p '' s2)) := by
  refine Set.disjoint_left.2 fun p0 hp0s1 hp0s2 => ?_
  obtain ⟨i, hi⟩ := ha.exists_mem_inter_of_exists_mem_inter_affineSpan hp0s1 hp0s2
  exact Set.disjoint_iff.1 hd hi

/-- If a family is affinely independent, a point in the family is in
the span of some of the points given by a subset of the index type if
and only if that point's index is in the subset, if the underlying
ring is nontrivial. -/
@[simp]
protected theorem AffineIndependent.mem_affineSpan_iff [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) (i : ι) (s : Set ι) : p i ∈ affineSpan k (p '' s) ↔ i ∈ s := by
  constructor
  · intro hs
    have h :=
      AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan ha hs
        (mem_affineSpan k (Set.mem_image_of_mem _ (Set.mem_singleton _)))
    rwa [← Set.nonempty_def, Set.inter_singleton_nonempty] at h
  · exact fun h => mem_affineSpan k (Set.mem_image_of_mem p h)

/-- If a family is affinely independent, a point in the family is not
in the affine span of the other points, if the underlying ring is
nontrivial. -/
theorem AffineIndependent.notMem_affineSpan_diff [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) (i : ι) (s : Set ι) : p i ∉ affineSpan k (p '' (s \ {i})) := by
  simp [ha]

@[deprecated (since := "2025-05-23")]
alias AffineIndependent.not_mem_affineSpan_diff := AffineIndependent.notMem_affineSpan_diff

theorem exists_nontrivial_relation_sum_zero_of_not_affine_ind {t : Finset V}
    (h : ¬AffineIndependent k ((↑) : t → V)) :
    ∃ f : V → k, ∑ e ∈ t, f e • e = 0 ∧ ∑ e ∈ t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  classical
    rw [affineIndependent_iff_of_fintype] at h
    simp only [exists_prop, not_forall] at h
    obtain ⟨w, hw, hwt, i, hi⟩ := h
    simp only [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w ((↑) : t → V) hw 0,
      vsub_eq_sub, Finset.weightedVSubOfPoint_apply, sub_zero] at hwt
    let f : ∀ x : V, x ∈ t → k := fun x hx => w ⟨x, hx⟩
    refine ⟨fun x => if hx : x ∈ t then f x hx else (0 : k), ?_, ?_, by use i; simp [f, hi]⟩
    on_goal 1 =>
      suffices (∑ e ∈ t, dite (e ∈ t) (fun hx => f e hx • e) fun _ => 0) = 0 by
        convert this
        rename V => x
        by_cases hx : x ∈ t <;> simp [hx]
    all_goals
      simp only [f, Finset.sum_dite_of_true fun _ h => h, Finset.mk_coe, hwt, hw]

variable {s : Finset ι} {w w₁ w₂ : ι → k} {p : ι → V}

/-- Viewing a module as an affine space modelled on itself, we can characterise affine independence
in terms of linear combinations. -/
theorem affineIndependent_iff {ι} {p : ι → V} :
    AffineIndependent k p ↔
      ∀ (s : Finset ι) (w : ι → k), s.sum w = 0 → ∑ e ∈ s, w e • p e = 0 → ∀ e ∈ s, w e = 0 :=
  forall₃_congr fun s w hw => by simp [s.weightedVSub_eq_linear_combination hw]

lemma AffineIndependent.eq_zero_of_sum_eq_zero (hp : AffineIndependent k p)
    (hw₀ : ∑ i ∈ s, w i = 0) (hw₁ : ∑ i ∈ s, w i • p i = 0) : ∀ i ∈ s, w i = 0 :=
  affineIndependent_iff.1 hp _ _ hw₀ hw₁

lemma AffineIndependent.eq_of_sum_eq_sum (hp : AffineIndependent k p)
    (hw : ∑ i ∈ s, w₁ i = ∑ i ∈ s, w₂ i) (hwp : ∑ i ∈ s, w₁ i • p i = ∑ i ∈ s, w₂ i • p i) :
    ∀ i ∈ s, w₁ i = w₂ i := by
  refine fun i hi ↦ sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero (w := w₁ - w₂) ?_ ?_ _ hi) <;>
    simpa [sub_mul, sub_smul, sub_eq_zero]

lemma AffineIndependent.eq_zero_of_sum_eq_zero_subtype {s : Finset V}
    (hp : AffineIndependent k ((↑) : s → V)) {w : V → k} (hw₀ : ∑ x ∈ s, w x = 0)
    (hw₁ : ∑ x ∈ s, w x • x = 0) : ∀ x ∈ s, w x = 0 := by
  rw [← sum_attach] at hw₀ hw₁
  exact fun x hx ↦ hp.eq_zero_of_sum_eq_zero hw₀ hw₁ ⟨x, hx⟩ (mem_univ _)

lemma AffineIndependent.eq_of_sum_eq_sum_subtype {s : Finset V}
    (hp : AffineIndependent k ((↑) : s → V)) {w₁ w₂ : V → k} (hw : ∑ i ∈ s, w₁ i = ∑ i ∈ s, w₂ i)
    (hwp : ∑ i ∈ s, w₁ i • i = ∑ i ∈ s, w₂ i • i) : ∀ i ∈ s, w₁ i = w₂ i := by
  refine fun i hi => sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero_subtype (w := w₁ - w₂) ?_ ?_ _ hi) <;>
    simpa [sub_mul, sub_smul, sub_eq_zero]

/-- Given an affinely independent family of points, a weighted subtraction lies in the
`vectorSpan` of two points given as affine combinations if and only if it is a weighted
subtraction with weights a multiple of the difference between the weights of the two points. -/
theorem weightedVSub_mem_vectorSpan_pair {p : ι → P} (h : AffineIndependent k p) {w w₁ w₂ : ι → k}
    {s : Finset ι} (hw : ∑ i ∈ s, w i = 0) (hw₁ : ∑ i ∈ s, w₁ i = 1)
    (hw₂ : ∑ i ∈ s, w₂ i = 1) :
    s.weightedVSub p w ∈
        vectorSpan k ({s.affineCombination k p w₁, s.affineCombination k p w₂} : Set P) ↔
      ∃ r : k, ∀ i ∈ s, w i = r * (w₁ i - w₂ i) := by
  rw [mem_vectorSpan_pair]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨r, hr⟩
    refine ⟨r, fun i hi => ?_⟩
    rw [s.affineCombination_vsub, ← s.weightedVSub_const_smul, ← sub_eq_zero, ← map_sub] at hr
    have hw' : (∑ j ∈ s, (r • (w₁ - w₂) - w) j) = 0 := by
      simp_rw [Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, ←
        Finset.smul_sum, hw, hw₁, hw₂, sub_self]
    have hr' := h s _ hw' hr i hi
    rw [eq_comm, ← sub_eq_zero, ← smul_eq_mul]
    exact hr'
  · rcases h with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    let w' i := r * (w₁ i - w₂ i)
    change ∀ i ∈ s, w i = w' i at hr
    rw [s.weightedVSub_congr hr fun _ _ => rfl, s.affineCombination_vsub, ←
      s.weightedVSub_const_smul]
    congr

/-- Given an affinely independent family of points, an affine combination lies in the
span of two points given as affine combinations if and only if it is an affine combination
with weights those of one point plus a multiple of the difference between the weights of the
two points. -/
theorem affineCombination_mem_affineSpan_pair {p : ι → P} (h : AffineIndependent k p)
    {w w₁ w₂ : ι → k} {s : Finset ι} (_ : ∑ i ∈ s, w i = 1) (hw₁ : ∑ i ∈ s, w₁ i = 1)
    (hw₂ : ∑ i ∈ s, w₂ i = 1) :
    s.affineCombination k p w ∈ line[k, s.affineCombination k p w₁, s.affineCombination k p w₂] ↔
      ∃ r : k, ∀ i ∈ s, w i = r * (w₂ i - w₁ i) + w₁ i := by
  rw [← vsub_vadd (s.affineCombination k p w) (s.affineCombination k p w₁),
    AffineSubspace.vadd_mem_iff_mem_direction _ (left_mem_affineSpan_pair _ _ _),
    direction_affineSpan, s.affineCombination_vsub, Set.pair_comm,
    weightedVSub_mem_vectorSpan_pair h _ hw₂ hw₁]
  · simp only [Pi.sub_apply, sub_eq_iff_eq_add]
  · simp_all only [Pi.sub_apply, Finset.sum_sub_distrib, sub_self]

end AffineIndependent

section DivisionRing

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*}

/-- An affinely independent set of points can be extended to such a
set that spans the whole space. -/
theorem exists_subset_affineIndependent_affineSpan_eq_top {s : Set P}
    (h : AffineIndependent k (fun p => p : s → P)) :
    ∃ t : Set P, s ⊆ t ∧ AffineIndependent k (fun p => p : t → P) ∧ affineSpan k t = ⊤ := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p₁, hp₁⟩)
  · have p₁ : P := AddTorsor.nonempty.some
    let hsv := Basis.ofVectorSpace k V
    have hsvi := hsv.linearIndependent
    have hsvt := hsv.span_eq
    rw [Basis.coe_ofVectorSpace] at hsvi hsvt
    have h0 : ∀ v : V, v ∈ Basis.ofVectorSpaceIndex k V → v ≠ 0 := by
      intro v hv
      simpa [hsv] using hsv.ne_zero ⟨v, hv⟩
    rw [linearIndependent_set_iff_affineIndependent_vadd_union_singleton k h0 p₁] at hsvi
    exact
      ⟨{p₁} ∪ (fun v => v +ᵥ p₁) '' _, Set.empty_subset _, hsvi,
        affineSpan_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt⟩
  · rw [affineIndependent_set_iff_linearIndependent_vsub k hp₁] at h
    let bsv := Basis.extend h
    have hsvi := bsv.linearIndependent
    have hsvt := bsv.span_eq
    rw [Basis.coe_extend] at hsvi hsvt
    rw [linearIndependent_subtype_iff] at hsvi h
    have hsv := h.subset_extend (Set.subset_univ _)
    have h0 : ∀ v : V, v ∈ h.extend (Set.subset_univ _) → v ≠ 0 := by
      intro v hv
      simpa [bsv] using bsv.ne_zero ⟨v, hv⟩
    rw [← linearIndependent_subtype_iff,
      linearIndependent_set_iff_affineIndependent_vadd_union_singleton k h0 p₁] at hsvi
    refine ⟨{p₁} ∪ (fun v => v +ᵥ p₁) '' h.extend (Set.subset_univ _), ?_, ?_⟩
    · refine Set.Subset.trans ?_ (Set.union_subset_union_right _ (Set.image_mono hsv))
      simp [Set.image_image]
    · use hsvi
      exact affineSpan_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt

variable (k V)

theorem exists_affineIndependent (s : Set P) :
    ∃ t ⊆ s, affineSpan k t = affineSpan k s ∧ AffineIndependent k ((↑) : t → P) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · exact ⟨∅, Set.empty_subset ∅, rfl, affineIndependent_of_subsingleton k _⟩
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := exists_linearIndependent k ((Equiv.vaddConst p).symm '' s)
  have hb₀ : ∀ v : V, v ∈ b → v ≠ 0 := fun v hv => hb₃.ne_zero (⟨v, hv⟩ : b)
  rw [linearIndependent_set_iff_affineIndependent_vadd_union_singleton k hb₀ p] at hb₃
  refine ⟨{p} ∪ Equiv.vaddConst p '' b, ?_, ?_, hb₃⟩
  · apply Set.union_subset (Set.singleton_subset_iff.mpr hp)
    rwa [← (Equiv.vaddConst p).subset_symm_image b s]
  · rw [Equiv.coe_vaddConst_symm, ← vectorSpan_eq_span_vsub_set_right k hp] at hb₂
    apply AffineSubspace.ext_of_direction_eq
    · have : Submodule.span k b = Submodule.span k (insert 0 b) := by simp
      simp only [direction_affineSpan, ← hb₂, Equiv.coe_vaddConst, Set.singleton_union,
        vectorSpan_eq_span_vsub_set_right k (Set.mem_insert p _), this]
      congr
      change (Equiv.vaddConst p).symm '' insert p (Equiv.vaddConst p '' b) = _
      rw [Set.image_insert_eq, ← Set.image_comp]
      simp
    · use p
      simp only [Equiv.coe_vaddConst, Set.singleton_union, Set.mem_inter_iff]
      exact ⟨mem_affineSpan k (Set.mem_insert p _), mem_affineSpan k hp⟩

variable {V}

/-- Two different points are affinely independent. -/
theorem affineIndependent_of_ne {p₁ p₂ : P} (h : p₁ ≠ p₂) : AffineIndependent k ![p₁, p₂] := by
  rw [affineIndependent_iff_linearIndependent_vsub k ![p₁, p₂] 0]
  let i₁ : { x // x ≠ (0 : Fin 2) } := ⟨1, by simp⟩
  have he' : ∀ i, i = i₁ := by
    rintro ⟨i, hi⟩
    ext
    fin_cases i
    · simp at hi
    · simp [i₁]
  haveI : Unique { x // x ≠ (0 : Fin 2) } := ⟨⟨i₁⟩, he'⟩
  apply linearIndependent_unique
  rw [he' default]
  simpa using h.symm

variable {k}

/-- If all but one point of a family are affinely independent, and that point does not lie in
the affine span of that family, the family is affinely independent. -/
theorem AffineIndependent.affineIndependent_of_notMem_span {p : ι → P} {i : ι}
    (ha : AffineIndependent k fun x : { y // y ≠ i } => p x)
    (hi : p i ∉ affineSpan k (p '' { x | x ≠ i })) : AffineIndependent k p := by
  classical
    intro s w hw hs
    let s' : Finset { y // y ≠ i } := s.subtype (· ≠ i)
    let p' : { y // y ≠ i } → P := fun x => p x
    by_cases his : i ∈ s ∧ w i ≠ 0
    · refine False.elim (hi ?_)
      let wm : ι → k := -(w i)⁻¹ • w
      have hms : s.weightedVSub p wm = (0 : V) := by simp [wm, hs]
      have hwm : ∑ i ∈ s, wm i = 0 := by simp [wm, ← Finset.mul_sum, hw]
      have hwmi : wm i = -1 := by simp [wm, his.2]
      let w' : { y // y ≠ i } → k := fun x => wm x
      have hw' : ∑ x ∈ s', w' x = 1 := by
        simp_rw [w', s', Finset.sum_subtype_eq_sum_filter]
        rw [← s.sum_filter_add_sum_filter_not (· ≠ i)] at hwm
        simpa only [not_not, Finset.filter_eq' _ i, if_pos his.1, sum_singleton, hwmi,
          add_neg_eq_zero] using hwm
      rw [← s.affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one hms his.1 hwmi, ←
        (Subtype.range_coe : _ = { x | x ≠ i }), ← Set.range_comp, ←
        s.affineCombination_subtype_eq_filter]
      exact affineCombination_mem_affineSpan hw' p'
    · rw [not_and_or, Classical.not_not] at his
      let w' : { y // y ≠ i } → k := fun x => w x
      have hw' : ∑ x ∈ s', w' x = 0 := by
        simp_rw [w', s', Finset.sum_subtype_eq_sum_filter]
        rw [Finset.sum_filter_of_ne, hw]
        rintro x hxs hwx rfl
        exact hwx (his.neg_resolve_left hxs)
      have hs' : s'.weightedVSub p' w' = (0 : V) := by
        simp_rw [w', s', p', Finset.weightedVSub_subtype_eq_filter]
        rw [Finset.weightedVSub_filter_of_ne, hs]
        rintro x hxs hwx rfl
        exact hwx (his.neg_resolve_left hxs)
      intro j hj
      by_cases hji : j = i
      · rw [hji] at hj
        exact hji.symm ▸ his.neg_resolve_left hj
      · exact ha s' w' hw' hs' ⟨j, hji⟩ (Finset.mem_subtype.2 hj)

@[deprecated (since := "2025-05-23")]
alias AffineIndependent.affineIndependent_of_not_mem_span :=
  AffineIndependent.affineIndependent_of_notMem_span

/-- If distinct points `p₁` and `p₂` lie in `s` but `p₃` does not, the three points are affinely
independent. -/
theorem affineIndependent_of_ne_of_mem_of_mem_of_notMem {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
    (hp₁p₂ : p₁ ≠ p₂) (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∉ s) :
    AffineIndependent k ![p₁, p₂, p₃] := by
  have ha : AffineIndependent k fun x : { x : Fin 3 // x ≠ 2 } => ![p₁, p₂, p₃] x := by
    rw [← affineIndependent_equiv (finSuccAboveEquiv (2 : Fin 3))]
    convert affineIndependent_of_ne k hp₁p₂
    ext x
    fin_cases x <;> rfl
  refine ha.affineIndependent_of_notMem_span ?_
  intro h
  refine hp₃ ((AffineSubspace.le_def' _ s).1 ?_ p₃ h)
  simp_rw [affineSpan_le, Set.image_subset_iff, Set.subset_def, Set.mem_preimage]
  intro x
  fin_cases x <;> simp +decide [hp₁, hp₂]

@[deprecated (since := "2025-05-23")]
alias affineIndependent_of_ne_of_mem_of_mem_of_not_mem :=
  affineIndependent_of_ne_of_mem_of_mem_of_notMem

/-- If distinct points `p₁` and `p₃` lie in `s` but `p₂` does not, the three points are affinely
independent. -/
theorem affineIndependent_of_ne_of_mem_of_notMem_of_mem {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
    (hp₁p₃ : p₁ ≠ p₃) (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∉ s) (hp₃ : p₃ ∈ s) :
    AffineIndependent k ![p₁, p₂, p₃] := by
  rw [← affineIndependent_equiv (Equiv.swap (1 : Fin 3) 2)]
  convert affineIndependent_of_ne_of_mem_of_mem_of_notMem hp₁p₃ hp₁ hp₃ hp₂ using 1
  ext x
  fin_cases x <;> rfl

@[deprecated (since := "2025-05-23")]
alias affineIndependent_of_ne_of_mem_of_not_mem_of_mem :=
  affineIndependent_of_ne_of_mem_of_notMem_of_mem

/-- If distinct points `p₂` and `p₃` lie in `s` but `p₁` does not, the three points are affinely
independent. -/
theorem affineIndependent_of_ne_of_notMem_of_mem_of_mem {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
    (hp₂p₃ : p₂ ≠ p₃) (hp₁ : p₁ ∉ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) :
    AffineIndependent k ![p₁, p₂, p₃] := by
  rw [← affineIndependent_equiv (Equiv.swap (0 : Fin 3) 2)]
  convert affineIndependent_of_ne_of_mem_of_mem_of_notMem hp₂p₃.symm hp₃ hp₂ hp₁ using 1
  ext x
  fin_cases x <;> rfl

@[deprecated (since := "2025-05-23")]
alias affineIndependent_of_ne_of_not_mem_of_mem_of_mem :=
  affineIndependent_of_ne_of_notMem_of_mem_of_mem

/-- If a family is affinely independent, we update any one point with a new point does not lie in
the affine span of that family, the new family is affinely independent. -/
theorem AffineIndependent.affineIndependent_update_of_notMem_affineSpan [DecidableEq ι]
    {p : ι → P} (ha : AffineIndependent k p) {i : ι} {p₀ : P}
    (hp₀ : p₀ ∉ affineSpan k (p '' {x | x ≠ i})) :
    AffineIndependent k (Function.update p i p₀) := by
  set f : ι → P := Function.update p i p₀ with hf
  have h₁ : (fun x : {x | x ≠ i} ↦ p x) = fun x : {x | x ≠ i} ↦ f x := by ext x; aesop
  have h₂ : p '' {x | x ≠ i} = f '' {x | x ≠ i} := Set.image_congr <| by simpa using congr_fun h₁
  replace ha : AffineIndependent k fun x : {x | x ≠ i} ↦ f x := h₁ ▸ AffineIndependent.subtype ha _
  exact AffineIndependent.affineIndependent_of_notMem_span ha <| by aesop

/-!
### Extending affinely independent families
-/

/-- Extending an affinely independent family with a point outside its affine span preserves
affine independence.

This uses `Option.elim` to extend `f : ι → P` to `Option ι → P` by designating `p` as the
value at `none`. -/
lemma AffineIndependent.option_extend
    {k : Type*} {V : Type*} {P : Type*}
    [DivisionRing k] [AddCommGroup V] [Module k V] [AddTorsor V P]
    {ι : Type*} [Nonempty ι]
    {f : ι → P} (hf : AffineIndependent k f)
    {p : P} (hp : p ∉ affineSpan k (Set.range f)) :
    AffineIndependent k (fun o : Option ι => o.elim p f) := by
  let f' : Option ι → P := fun o => o.elim p f

  have h_comp_eq : (fun x : {y : Option ι // y ≠ none} => f' x) =
      f ∘ (fun x => Option.get x.val (Option.ne_none_iff_isSome.mp x.prop)) := by
    ext ⟨x, hx⟩
    cases x with
    | some i => rfl
    | none => exact absurd rfl hx

  have h_sub : AffineIndependent k (fun x : {y : Option ι // y ≠ none} => f' x) := by
    rw [h_comp_eq]
    let e : {y : Option ι // y ≠ none} ↪ ι :=
      ⟨fun x => Option.get x.val (Option.ne_none_iff_isSome.mp x.prop),
       fun ⟨x, hx⟩ ⟨y, hy⟩ h_eq => by
         simp only [Subtype.mk.injEq]
         cases x with
         | some i =>
           cases y with
           | some j => simp_all
           | none => exact absurd rfl hy
         | none => exact absurd rfl hx⟩
    exact hf.comp_embedding e

  have h_not_mem : f' none ∉ affineSpan k (f' '' {x : Option ι | x ≠ none}) := by
    rw [Option.elim_image_some_eq_range]
    exact hp

  exact AffineIndependent.affineIndependent_of_notMem_span h_sub h_not_mem

end DivisionRing

section Ordered

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup V]
variable [Module k V] [AffineSpace V P] {ι : Type*}

/-- Given an affinely independent family of points, suppose that an affine combination lies in
the span of two points given as affine combinations, and suppose that, for two indices, the
coefficients in the first point in the span are zero and those in the second point in the span
have the same sign. Then the coefficients in the combination lying in the span have the same
sign. -/
theorem sign_eq_of_affineCombination_mem_affineSpan_pair {p : ι → P} (h : AffineIndependent k p)
    {w w₁ w₂ : ι → k} {s : Finset ι} (hw : ∑ i ∈ s, w i = 1) (hw₁ : ∑ i ∈ s, w₁ i = 1)
    (hw₂ : ∑ i ∈ s, w₂ i = 1)
    (hs :
      s.affineCombination k p w ∈ line[k, s.affineCombination k p w₁, s.affineCombination k p w₂])
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hi0 : w₁ i = 0) (hj0 : w₁ j = 0)
    (hij : SignType.sign (w₂ i) = SignType.sign (w₂ j)) :
    SignType.sign (w i) = SignType.sign (w j) := by
  rw [affineCombination_mem_affineSpan_pair h hw hw₁ hw₂] at hs
  rcases hs with ⟨r, hr⟩
  rw [hr i hi, hr j hj, hi0, hj0, add_zero, add_zero, sub_zero, sub_zero, sign_mul, sign_mul, hij]

/-- Given an affinely independent family of points, suppose that an affine combination lies in
the span of one point of that family and a combination of another two points of that family given
by `lineMap` with coefficient between 0 and 1. Then the coefficients of those two points in the
combination lying in the span have the same sign. -/
theorem sign_eq_of_affineCombination_mem_affineSpan_single_lineMap {p : ι → P}
    (h : AffineIndependent k p) {w : ι → k} {s : Finset ι} (hw : ∑ i ∈ s, w i = 1) {i₁ i₂ i₃ : ι}
    (h₁ : i₁ ∈ s) (h₂ : i₂ ∈ s) (h₃ : i₃ ∈ s) (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    {c : k} (hc0 : 0 < c) (hc1 : c < 1)
    (hs : s.affineCombination k p w ∈ line[k, p i₁, AffineMap.lineMap (p i₂) (p i₃) c]) :
    SignType.sign (w i₂) = SignType.sign (w i₃) := by
  classical
    rw [← s.affineCombination_affineCombinationSingleWeights k p h₁, ←
      s.affineCombination_affineCombinationLineMapWeights p h₂ h₃ c] at hs
    refine
      sign_eq_of_affineCombination_mem_affineSpan_pair h hw
        (s.sum_affineCombinationSingleWeights k h₁)
        (s.sum_affineCombinationLineMapWeights h₂ h₃ c) hs h₂ h₃
        (Finset.affineCombinationSingleWeights_apply_of_ne k h₁₂.symm)
        (Finset.affineCombinationSingleWeights_apply_of_ne k h₁₃.symm) ?_
    rw [Finset.affineCombinationLineMapWeights_apply_left h₂₃,
      Finset.affineCombinationLineMapWeights_apply_right h₂₃]
    simp_all only [sub_pos, sign_pos]

end Ordered
