/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Mathlib.Topology.LocallyFinite
public import Mathlib.Topology.Metrizable.Uniformity

import Mathlib.Data.Nat.Pairing
import Mathlib.SetTheory.Cardinal.Order
import Mathlib.Tactic.GCongr

/-!
# Discrete and sigma-discrete families of sets

A family of sets is discrete if every point has a neighborhood meeting at most one member of the
family. A family is sigma-discrete if its index type is covered by countably many sets on each of
which the restricted family is discrete. We also prove that every open cover of a
pseudometrizable space has an open sigma-discrete refinement.
-/

@[expose] public section

open ENNReal Filter Function Set TopologicalSpace Topology

variable {ι ι' X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : ι → Set X}

/-- A family of sets is discrete if every point has a neighborhood meeting at most one member of
the family. In particular, distinct members of a discrete family are disjoint. -/
def DiscreteFamily (f : ι → Set X) : Prop :=
  ∀ x, ∃ t ∈ 𝓝 x, {i | (f i ∩ t).Nonempty}.Subsingleton

theorem discreteFamily_of_subsingleton [Subsingleton ι] (f : ι → Set X) : DiscreteFamily f :=
  fun _ ↦ ⟨univ, univ_mem, Set.subsingleton_of_subsingleton⟩

theorem discreteFamily_empty : DiscreteFamily (fun _ : ι ↦ (∅ : Set X)) := by
  intro x
  exact ⟨univ, univ_mem, by simp⟩

namespace DiscreteFamily

/-- A discrete family is locally finite. -/
theorem locallyFinite (hf : DiscreteFamily f) : LocallyFinite f := fun x ↦ by
  rcases hf x with ⟨t, htx, ht⟩
  exact ⟨t, htx, ht.finite⟩

/-- At most one member of a discrete family contains any given point. -/
theorem point_subsingleton (hf : DiscreteFamily f) (x : X) :
    {i | x ∈ f i}.Subsingleton := by
  rcases hf x with ⟨t, htx, ht⟩
  exact ht.anti fun _ hi ↦ ⟨x, hi, mem_of_mem_nhds htx⟩

/-- Distinct members of a discrete family are disjoint. -/
theorem pairwiseDisjoint (hf : DiscreteFamily f) : Pairwise (Disjoint on f) := by
  rintro i j hij
  change Disjoint (f i) (f j)
  rw [Set.disjoint_left]
  intro x hxi hxj
  exact hij <| hf.point_subsingleton x hxi hxj

/-- Replacing every member of a discrete family by a subset preserves discreteness. -/
protected theorem subset (hf : DiscreteFamily f) (hg : ∀ i, g i ⊆ f i) :
    DiscreteFamily g := fun x ↦ by
  rcases hf x with ⟨t, htx, ht⟩
  exact ⟨t, htx, ht.anti fun i hi ↦ hi.mono <| inter_subset_inter_left _ (hg i)⟩

/-- Injectively reindexing a discrete family preserves discreteness. -/
theorem comp_injective {g : ι' → ι} (hf : DiscreteFamily f) (hg : Injective g) :
    DiscreteFamily (f ∘ g) := fun x ↦ by
  rcases hf x with ⟨t, htx, ht⟩
  refine ⟨t, htx, ?_⟩
  intro i hi j hj
  exact hg <| ht hi hj

/-- A surjective reindexing detects whether a family is discrete. -/
theorem of_comp_surjective {g : ι' → ι} (hg : Surjective g)
    (hfg : DiscreteFamily (f ∘ g)) : DiscreteFamily f := by
  simpa only [comp_def, surjInv_eq hg] using
    hfg.comp_injective (injective_surjInv hg)

/-- A family remains discrete when indexed by its range. -/
theorem on_range (hf : DiscreteFamily f) : DiscreteFamily ((↑) : range f → Set X) :=
  of_comp_surjective rangeFactorization_surjective hf

/-- Continuous preimages of a discrete family form a discrete family. -/
theorem preimage_continuous {g : Y → X} (hf : DiscreteFamily f) (hg : Continuous g) :
    DiscreteFamily (g ⁻¹' f ·) := fun y ↦ by
  rcases hf (g y) with ⟨t, hgy, ht⟩
  exact ⟨g ⁻¹' t, hg.continuousAt hgy, ht.anti fun _ ⟨z, hz⟩ ↦ ⟨g z, hz⟩⟩

/-- The closures of the members of a discrete family form a discrete family. -/
protected theorem closure (hf : DiscreteFamily f) :
    DiscreteFamily fun i ↦ closure (f i) := by
  intro x
  rcases hf x with ⟨s, hsx, hsf⟩
  refine ⟨interior s, interior_mem_nhds.2 hsx, hsf.anti fun i hi ↦ ?_⟩
  exact (hi.mono isOpen_interior.closure_inter).of_closure.mono
    (inter_subset_inter_right _ interior_subset)

theorem closure_iUnion (hf : DiscreteFamily f) : closure (⋃ i, f i) = ⋃ i, closure (f i) :=
  hf.locallyFinite.closure_iUnion

theorem isClosed_iUnion (hf : DiscreteFamily f) (hc : ∀ i, IsClosed (f i)) :
    IsClosed (⋃ i, f i) :=
  hf.locallyFinite.isClosed_iUnion hc

end DiscreteFamily

@[simp]
theorem Equiv.discreteFamily_comp_iff (e : ι' ≃ ι) :
    DiscreteFamily (f ∘ e) ↔ DiscreteFamily f :=
  ⟨fun h ↦ by
    simpa only [comp_def, e.apply_symm_apply] using h.comp_injective e.symm.injective,
    fun h ↦ h.comp_injective e.injective⟩

/-- A family is sigma-discrete if its index type is covered by countably many sets on each of
which the restricted family is discrete. The sets of indices need not be pairwise disjoint. -/
def SigmaDiscreteFamily (f : ι → Set X) : Prop :=
  ∃ I : ℕ → Set ι, (⋃ n, I n) = univ ∧
    ∀ n, DiscreteFamily fun i : I n ↦ f i

namespace SigmaDiscreteFamily

/-- A discrete family is sigma-discrete. -/
theorem of_discreteFamily (hf : DiscreteFamily f) : SigmaDiscreteFamily f :=
  ⟨fun _ ↦ univ, by ext; simp, fun _ ↦ hf.comp_injective Subtype.val_injective⟩

/-- Replacing every member of a sigma-discrete family by a subset preserves sigma-discreteness. -/
protected theorem subset (hf : SigmaDiscreteFamily f) (hg : ∀ i, g i ⊆ f i) :
    SigmaDiscreteFamily g := by
  rcases hf with ⟨I, hI, hdisc⟩
  exact ⟨I, hI, fun n ↦ (hdisc n).subset fun i ↦ hg i⟩

/-- Injectively reindexing a sigma-discrete family preserves sigma-discreteness. -/
theorem comp_injective {g : ι' → ι} (hf : SigmaDiscreteFamily f) (hg : Injective g) :
    SigmaDiscreteFamily (f ∘ g) := by
  rcases hf with ⟨I, hI, hdisc⟩
  refine ⟨fun n ↦ g ⁻¹' I n, ?_, fun n ↦ ?_⟩
  · rw [← preimage_iUnion, hI, preimage_univ]
  · let e : g ⁻¹' I n → I n := fun i ↦ ⟨g i, i.2⟩
    exact (hdisc n).comp_injective fun (i j : g ⁻¹' I n) (h : e i = e j) ↦
      Subtype.ext <| hg <| congrArg Subtype.val h

/-- A surjective reindexing detects whether a family is sigma-discrete. -/
theorem of_comp_surjective {g : ι' → ι} (hg : Surjective g)
    (hfg : SigmaDiscreteFamily (f ∘ g)) : SigmaDiscreteFamily f := by
  simpa only [comp_def, surjInv_eq hg] using
    hfg.comp_injective (injective_surjInv hg)

/-- A family remains sigma-discrete when indexed by its range. -/
theorem on_range (hf : SigmaDiscreteFamily f) :
    SigmaDiscreteFamily ((↑) : range f → Set X) :=
  of_comp_surjective rangeFactorization_surjective hf

/-- Continuous preimages of a sigma-discrete family form a sigma-discrete family. -/
theorem preimage_continuous {g : Y → X} (hf : SigmaDiscreteFamily f) (hg : Continuous g) :
    SigmaDiscreteFamily (g ⁻¹' f ·) := by
  rcases hf with ⟨I, hI, hdisc⟩
  exact ⟨I, hI, fun n ↦ (hdisc n).preimage_continuous hg⟩

/-- Taking the closure of each member of a sigma-discrete family preserves sigma-discreteness. -/
protected theorem closure (hf : SigmaDiscreteFamily f) :
    SigmaDiscreteFamily fun i ↦ closure (f i) := by
  rcases hf with ⟨I, hI, hdisc⟩
  exact ⟨I, hI, fun n ↦ (hdisc n).closure⟩

end SigmaDiscreteFamily

@[simp]
theorem Equiv.sigmaDiscreteFamily_comp_iff (e : ι' ≃ ι) :
    SigmaDiscreteFamily (f ∘ e) ↔ SigmaDiscreteFamily f :=
  ⟨fun h ↦ by
    simpa only [comp_def, e.apply_symm_apply] using h.comp_injective e.symm.injective,
    fun h ↦ h.comp_injective e.injective⟩

section PseudoMetrizableSpace

private theorem inv_two_pow_pos_aux (n : ℕ) : (0 : ℝ≥0∞) < 2⁻¹ ^ n :=
  ENNReal.pow_pos (ENNReal.inv_pos.2 ENNReal.ofNat_ne_top) _

private theorem inv_two_pow_le_aux {m n : ℕ} (h : m ≤ n) :
    (2⁻¹ : ℝ≥0∞) ^ n ≤ 2⁻¹ ^ m :=
  pow_le_pow_right_of_le_one' (ENNReal.inv_le_one.2 ENNReal.one_lt_two.le) h

private theorem two_mul_inv_two_pow_succ_aux (n : ℕ) :
    2 * (2⁻¹ : ℝ≥0∞) ^ (n + 1) = 2⁻¹ ^ n := by
  simp [pow_succ', ← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ofNat_ne_top]

section PseudoMetricSpace

variable {Z : Type*} [PseudoMetricSpace Z] [LinearOrder ι] [WellFoundedLT ι]

private noncomputable def sigmaDiscreteCoverIndex (u : ι → Set Z)
    (hucov : ⋃ i, u i = univ) (x : Z) : ι :=
  wellFounded_lt.min {i | x ∈ u i} (iUnion_eq_univ_iff.1 hucov x)

omit [PseudoMetricSpace Z] in
private theorem mem_sigmaDiscreteCoverIndex_aux (u : ι → Set Z)
    (hucov : ⋃ i, u i = univ) (x : Z) : x ∈ u (sigmaDiscreteCoverIndex u hucov x) :=
  wellFounded_lt.min_mem _ (iUnion_eq_univ_iff.1 hucov x)

omit [PseudoMetricSpace Z] in
private theorem not_mem_of_lt_sigmaDiscreteCoverIndex_aux (u : ι → Set Z)
    (hucov : ⋃ i, u i = univ) {x : Z} {i : ι} (hi : i < sigmaDiscreteCoverIndex u hucov x) :
    x ∉ u i := fun hxi ↦ wellFounded_lt.not_lt_min {i | x ∈ u i} hxi hi

private noncomputable def sigmaDiscreteRefinement (u : ι → Set Z)
    (hucov : ⋃ i, u i = univ) : ℕ → ι → Set Z :=
  Nat.strongRec fun n v i ↦
    ⋃ (x : Z) (_ : sigmaDiscreteCoverIndex u hucov x = i)
      (_ : Metric.eball x (3 * 2⁻¹ ^ n) ⊆ u i)
      (_ : ∀ (m : ℕ) (H : m < n), ∀ j, x ∉ v m H j), Metric.eball x (2⁻¹ ^ n)

private theorem sigmaDiscreteRefinement_eq_aux (u : ι → Set Z)
    (hucov : ⋃ i, u i = univ) (n : ℕ) (i : ι) :
    sigmaDiscreteRefinement u hucov n i =
      ⋃ (x : Z) (_ : sigmaDiscreteCoverIndex u hucov x = i)
        (_ : Metric.eball x (3 * 2⁻¹ ^ n) ⊆ u i)
        (_ : ∀ m < n, ∀ j, x ∉ sigmaDiscreteRefinement u hucov m j),
        Metric.eball x (2⁻¹ ^ n) := by
  rw [sigmaDiscreteRefinement, Nat.strongRec_eq]
  rfl

private theorem mem_sigmaDiscreteRefinement_aux (u : ι → Set Z)
    (hucov : ⋃ i, u i = univ) {n : ℕ} {i : ι} {y : Z} :
    y ∈ sigmaDiscreteRefinement u hucov n i ↔
      ∃ x : Z, sigmaDiscreteCoverIndex u hucov x = i ∧
        Metric.eball x (3 * 2⁻¹ ^ n) ⊆ u i ∧
        (∀ m < n, ∀ j, x ∉ sigmaDiscreteRefinement u hucov m j) ∧
        edist y x < 2⁻¹ ^ n := by
  rw [sigmaDiscreteRefinement_eq_aux]
  simp only [mem_iUnion, Metric.mem_eball, exists_prop]

private theorem exists_mem_sigmaDiscreteRefinement_aux (u : ι → Set Z)
    (huo : ∀ i, IsOpen (u i)) (hucov : ⋃ i, u i = univ) (x : Z) :
    ∃ n i, x ∈ sigmaDiscreteRefinement u hucov n i := by
  let ind := sigmaDiscreteCoverIndex u hucov
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Metric.eball x (3 * 2⁻¹ ^ n) ⊆ u (ind x) := by
    rcases EMetric.isOpen_iff.1 (huo <| ind x) x
      (mem_sigmaDiscreteCoverIndex_aux u hucov x) with ⟨ε, hε, hεu⟩
    have hε3 : 0 < ε / 3 := ENNReal.div_pos_iff.2 ⟨hε.lt.ne', ENNReal.coe_ne_top⟩
    obtain ⟨n, hn⟩ := ENNReal.exists_inv_two_pow_lt hε3.ne'
    refine ⟨n, (Metric.eball_subset_eball ?_).trans hεu⟩
    simpa only [div_eq_mul_inv, mul_comm] using (ENNReal.mul_lt_of_lt_div hn).le
  by_contra! h
  apply h n (ind x)
  exact mem_sigmaDiscreteRefinement_aux u hucov |>.2
    ⟨x, rfl, hn, fun _ _ _ ↦ h _ _, Metric.mem_eball_self (inv_two_pow_pos_aux _)⟩

private theorem isOpen_sigmaDiscreteRefinement_aux (u : ι → Set Z)
    (hucov : ⋃ i, u i = univ) (n : ℕ) (i : ι) :
    IsOpen (sigmaDiscreteRefinement u hucov n i) := by
  rw [sigmaDiscreteRefinement_eq_aux]
  iterate 4 refine isOpen_iUnion fun _ ↦ ?_
  exact Metric.isOpen_eball

private theorem sigmaDiscreteRefinement_subset_aux (u : ι → Set Z)
    (hucov : ⋃ i, u i = univ) (n : ℕ) (i : ι) :
    sigmaDiscreteRefinement u hucov n i ⊆ u i := by
  rintro x (hx : x ∈ sigmaDiscreteRefinement u hucov n i)
  rcases (mem_sigmaDiscreteRefinement_aux u hucov).1 hx with ⟨y, rfl, hsub, -, hyx⟩
  exact hsub (hyx.trans_le <| le_mul_of_one_le_left' <| by norm_num1)

private theorem sigmaDiscreteRefinement_disjoint_eball_aux (u : ι → Set Z)
    (hucov : ⋃ i, u i = univ) {n k p : ℕ} {i : ι} {x : Z}
    (hk : Metric.eball x (2⁻¹ ^ k) ⊆ sigmaDiscreteRefinement u hucov n i)
    (hp : n + k + 1 ≤ p) (j : ι) :
    Disjoint (sigmaDiscreteRefinement u hucov p j)
      (Metric.eball x (2⁻¹ ^ (n + k + 1))) := by
  rw [Set.disjoint_left]
  rintro y hyp hyx
  rcases (mem_sigmaDiscreteRefinement_aux u hucov).1 hyp with ⟨z, rfl, -, hzv, hyz⟩
  apply hzv n (by omega) i
  apply hk
  calc
    edist z x ≤ edist y z + edist y x := edist_triangle_left _ _ _
    _ < 2⁻¹ ^ p + 2⁻¹ ^ (n + k + 1) := ENNReal.add_lt_add hyz hyx
    _ ≤ 2⁻¹ ^ (k + 1) + 2⁻¹ ^ (k + 1) :=
      add_le_add (inv_two_pow_le_aux <| by omega) (inv_two_pow_le_aux <| by omega)
    _ = 2⁻¹ ^ k := by rw [← two_mul, two_mul_inv_two_pow_succ_aux]

private theorem sigmaDiscreteRefinement_inter_eball_subsingleton_aux (u : ι → Set Z)
    (hucov : ⋃ i, u i = univ) {n k m : ℕ} {x : Z} (hm : m ≤ n + k) :
    {j | (sigmaDiscreteRefinement u hucov m j ∩
      Metric.eball x (2⁻¹ ^ (n + k + 1))).Nonempty}.Subsingleton := by
  rintro j₁ ⟨y, hyD, hyB⟩ j₂ ⟨z, hzD, hzB⟩
  by_contra hne : j₁ ≠ j₂
  wlog hlt : j₁ < j₂ generalizing j₁ j₂ y z
  · exact this z hzD hzB y hyD hyB hne.symm (hne.lt_or_gt.resolve_left hlt)
  rcases (mem_sigmaDiscreteRefinement_aux u hucov).1 hyD with
    ⟨y', rfl, hsuby, -, hdisty⟩
  rcases (mem_sigmaDiscreteRefinement_aux u hucov).1 hzD with
    ⟨z', rfl, -, -, hdistz⟩
  apply not_mem_of_lt_sigmaDiscreteCoverIndex_aux u hucov hlt
  apply hsuby
  calc
    edist z' y' ≤ edist z' x + edist x y' := edist_triangle _ _ _
    _ ≤ edist z z' + edist z x + (edist y x + edist y y') :=
      add_le_add (edist_triangle_left _ _ _) (edist_triangle_left _ _ _)
    _ < 2⁻¹ ^ m + 2⁻¹ ^ (n + k + 1) + (2⁻¹ ^ (n + k + 1) + 2⁻¹ ^ m) := by
      apply_rules [ENNReal.add_lt_add]
    _ = 2 * (2⁻¹ ^ m + 2⁻¹ ^ (n + k + 1)) := by simp [two_mul, add_comm]
    _ ≤ 2 * (2⁻¹ ^ m + 2⁻¹ ^ (m + 1)) := by
      gcongr 2 * (_ + ?_)
      exact inv_two_pow_le_aux (add_le_add hm le_rfl)
    _ = 3 * 2⁻¹ ^ m := by
      rw [mul_add, two_mul_inv_two_pow_succ_aux, ← two_add_one_eq_three, add_mul, one_mul]

private theorem discreteFamily_sigmaDiscreteRefinement_aux (u : ι → Set Z)
    (huo : ∀ i, IsOpen (u i)) (hucov : ⋃ i, u i = univ) (m : ℕ) :
    DiscreteFamily (sigmaDiscreteRefinement u hucov m) := by
  intro x
  rcases exists_mem_sigmaDiscreteRefinement_aux u huo hucov x with ⟨n, i, hxn⟩
  have hvn : sigmaDiscreteRefinement u hucov n i ∈ 𝓝 x :=
    (isOpen_sigmaDiscreteRefinement_aux u hucov n i).mem_nhds hxn
  rcases (nhds_basis_uniformity uniformity_basis_edist_inv_two_pow).mem_iff.1 hvn with
    ⟨k, -, hk : Metric.eball x (2⁻¹ ^ k) ⊆ sigmaDiscreteRefinement u hucov n i⟩
  let B := Metric.eball x (2⁻¹ ^ (n + k + 1))
  refine ⟨B, Metric.eball_mem_nhds _ (inv_two_pow_pos_aux _), ?_⟩
  by_cases hm : m ≤ n + k
  · exact sigmaDiscreteRefinement_inter_eball_subsingleton_aux u hucov hm
  · apply subsingleton_empty.anti
    rintro j ⟨y, hyv, hyB⟩
    exact Set.disjoint_left.1
      (sigmaDiscreteRefinement_disjoint_eball_aux u hucov hk (by omega) j) hyv hyB

end PseudoMetricSpace

/-- Every open cover of a pseudometrizable space has an open sigma-discrete precise refinement. -/
theorem exists_sigmaDiscrete_refinement [PseudoMetrizableSpace X] (u : ι → Set X)
    (huo : ∀ i, IsOpen (u i)) (hucov : ⋃ i, u i = univ) :
    ∃ v : ℕ → ι → Set X,
      (∀ n i, IsOpen (v n i)) ∧
      (⋃ n, ⋃ i, v n i) = univ ∧
      (∀ n i, v n i ⊆ u i) ∧
      ∀ n, DiscreteFamily (v n) := by
  letI : PseudoMetricSpace X := pseudoMetrizableSpacePseudoMetric X
  obtain ⟨_, _⟩ := exists_wellFoundedLT ι
  let v := sigmaDiscreteRefinement u hucov
  refine ⟨v, isOpen_sigmaDiscreteRefinement_aux u hucov, ?_,
    sigmaDiscreteRefinement_subset_aux u hucov,
    discreteFamily_sigmaDiscreteRefinement_aux u huo hucov⟩
  apply iUnion_eq_univ_iff.2
  intro x
  rcases exists_mem_sigmaDiscreteRefinement_aux u huo hucov x with ⟨n, i, hxi⟩
  exact ⟨n, mem_iUnion.2 ⟨i, hxi⟩⟩

private theorem isTopologicalBasis_iUnion_range_aux {Z : Type*} [PseudoMetricSpace Z]
    (v : ℕ → ℕ → Z → Set Z) (v_open : ∀ k n x, IsOpen (v k n x))
    (v_cov : ∀ k, ⋃ n, ⋃ x, v k n x = univ)
    (v_sub : ∀ k n x, v k n x ⊆ Metric.eball x (2⁻¹ ^ k)) :
    IsTopologicalBasis
      (⋃ p, range (v (Nat.pairEquiv.symm p).1 (Nat.pairEquiv.symm p).2)) := by
  apply isTopologicalBasis_of_isOpen_of_nhds
  · intro s hs
    rcases mem_iUnion.1 hs with ⟨p, hp⟩
    rcases hp with ⟨x, rfl⟩
    exact v_open _ _ _
  · intro x s hxs hs
    rcases EMetric.isOpen_iff.1 hs x hxs with ⟨ε, hε, hεs⟩
    have hε2 : 0 < ε / 2 := ENNReal.div_pos_iff.2 ⟨hε.lt.ne', ENNReal.coe_ne_top⟩
    rcases ENNReal.exists_inv_two_pow_lt hε2.ne' with ⟨k, hk⟩
    have h2k : 2 * (2⁻¹ : ℝ≥0∞) ^ k < ε := by
      simpa only [div_eq_mul_inv, mul_comm] using ENNReal.mul_lt_of_lt_div hk
    rcases iUnion_eq_univ_iff.1 (v_cov k) x with ⟨n, hxn⟩
    rcases mem_iUnion.1 hxn with ⟨y, hxy⟩
    refine ⟨v k n y, ?_, hxy, fun z hz ↦ hεs ?_⟩
    · apply mem_iUnion.2
      exact ⟨Nat.pairEquiv (k, n), ⟨y, by simp⟩⟩
    · calc
        edist z x ≤ edist z y + edist y x := edist_triangle _ _ _
        _ < 2⁻¹ ^ k + 2⁻¹ ^ k := ENNReal.add_lt_add (v_sub k n y hz)
          (by simpa only [Metric.mem_eball, edist_comm] using v_sub k n y hxy)
        _ = 2 * 2⁻¹ ^ k := by rw [two_mul]
        _ < ε := h2k

/-- Every pseudometrizable space has a topological basis which is a countable union of discrete
families. -/
theorem exists_isTopologicalBasis_sigmaDiscrete [PseudoMetrizableSpace X] :
    ∃ b : ℕ → Set (Set X),
      IsTopologicalBasis (⋃ n, b n) ∧
      ∀ n, DiscreteFamily ((↑) : b n → Set X) := by
  letI : PseudoMetricSpace X := pseudoMetrizableSpacePseudoMetric X
  let u : ℕ → X → Set X := fun k x ↦ Metric.eball x (2⁻¹ ^ k)
  have u_open : ∀ k x, IsOpen (u k x) := fun _ _ ↦ Metric.isOpen_eball
  have u_cov : ∀ k, ⋃ x, u k x = univ := fun k ↦ iUnion_eq_univ_iff.2 fun x ↦
    ⟨x, Metric.mem_eball_self <| inv_two_pow_pos_aux k⟩
  choose v v_open v_cov v_sub v_disc using
    fun k ↦ exists_sigmaDiscrete_refinement (u k) (u_open k) (u_cov k)
  let b : ℕ → Set (Set X) := fun p ↦
    range (v (Nat.pairEquiv.symm p).1 (Nat.pairEquiv.symm p).2)
  refine ⟨b, isTopologicalBasis_iUnion_range_aux v v_open v_cov ?_, fun p ↦ ?_⟩
  · exact fun k n x ↦ v_sub k n x
  · exact (v_disc (Nat.pairEquiv.symm p).1 (Nat.pairEquiv.symm p).2).on_range

end PseudoMetrizableSpace
