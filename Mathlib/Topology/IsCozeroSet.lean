/-
Copyright (c) 2026 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
module

public import Mathlib.Topology.ContinuousMap.Lattice
public import Mathlib.Topology.Separation.PerfectlyNormal
public import Mathlib.Topology.UnitInterval

import Mathlib.Topology.Algebra.Indicator
import Mathlib.Topology.GDelta.MetrizableSpace

/-! # Cozero sets
In this file we define cozero sets as sets that are the support of a continuous function to `ℝ`. In
perfectly normal spaces (in particular in metric spaces) this is equivalent to being open, but in
general it is a stronger property.

## Main definitions & results:
* `IsCozeroSet u`: predicate stating that `u` is the cozero set of some continuous function to `ℝ`.
* Every cozero set is open, and in perfectly normal spaces every open set is a cozero set.
* Every clopen set is a cozero set.
* Finite intersections and σ-locally finite unions of cozero sets are cozero sets.
* Preimages of cozero sets under continuous maps are cozero sets.
* Images and coimages of cozero sets under open proper maps are cozero sets.
* Cozero sets are Fσ; in normal spaces, being a cozero set is equivalent to being Fσ and open.
* A space is perfectly normal iff every open set in it is a cozero set.
-/

public section

open Set Function

open scoped Topology unitInterval

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {u : Set X}

/-- A set is a cozero set if it is the support of some continuous function to `ℝ`. -/
@[expose]
def IsCozeroSet (u : Set X) : Prop := ∃ f : C(X, ℝ), support f = u

/-- The function that a cozero set is the support of can be chosen to be nonnegative. -/
lemma IsCozeroSet.exists_nonneg (hu : IsCozeroSet u) :
    ∃ f ≥ (0 : C(X, ℝ)), support f = u := by
  obtain ⟨f, rfl⟩ := hu
  exact ⟨|f|, by simp⟩

/-- The function that a cozero set is the support of can be chosen to be nonnegative and bounded
from above by `1`. -/
lemma IsCozeroSet.exists_nonneg_le_one (hu : IsCozeroSet u) :
    ∃ f : C(X, ℝ), 0 ≤ f ∧ f ≤ 1 ∧ support f = u := by
  obtain ⟨f, hf, rfl⟩ := hu.exists_nonneg
  exact ⟨f ⊓ 1, fun x ↦ by simpa using hf x, by simp, by
    ext; grind [support, ContinuousMap.inf_apply, ContinuousMap.one_apply]⟩

/-- A set is a cozero set if and only if it is the support of a continuous function to the unit
interval. -/
lemma isCozeroSet_iff_unitInterval : IsCozeroSet u ↔ ∃ f : C(X, I), support f = u := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨f, hf, rfl⟩ := h.exists_nonneg
    use .comp ⟨_, continuous_projIcc (h := one_pos.le)⟩ f
    ext x; simpa using (hf x).lt_iff_ne'
  · obtain ⟨f, rfl⟩ := h
    use .comp ⟨(↑), by fun_prop⟩ f
    ext; simp

/-- Every cozero set is open. -/
lemma IsCozeroSet.isOpen (hu : IsCozeroSet u) : IsOpen u := by
  obtain ⟨f, rfl⟩ := hu
  exact (map_continuous f).isOpen_support

/-- Every open set in a perfectly normal space is a cozero set. -/
lemma IsOpen.isCozeroSet [PerfectlyNormalSpace X] (hu : IsOpen u) : IsCozeroSet u := by
  have ⟨f, hf⟩ := perfectlyNormalSpace_iff_forall_isClosed_preimage_zero.1 ‹_› _ hu.isClosed_compl
  refine ⟨f, ?_⟩
  rw [compl_eq_comm] at hf
  grind [support]

lemma IsClopen.isCozeroSet (hu : IsClopen u) : IsCozeroSet u :=
  ⟨⟨u.indicator 1, hu.continuous_indicator continuous_const⟩, by simp⟩

lemma IsCozeroSet.preimage (hu : IsCozeroSet u) {f : Y → X} (hf : Continuous f) :
    IsCozeroSet (f ⁻¹' u) := by
  obtain ⟨g, rfl⟩ := hu
  exact ⟨g.comp ⟨f, hf⟩, by simp [support_comp_eq_preimage]⟩

lemma Continuous.isCozeroSet_support [T6Space Y] [Zero Y] {f : X → Y}
    (hf : Continuous f) : IsCozeroSet (support f) := by
  rw [support_eq_preimage]
  exact .preimage isOpen_compl_singleton.isCozeroSet hf

lemma isCozeroSet_empty : IsCozeroSet (∅ : Set X) := ⟨0, by simp⟩

lemma isCozeroSet_univ : IsCozeroSet (univ : Set X) := ⟨1, by simp⟩

lemma IsCozeroSet.inter (hu : IsCozeroSet u) {v : Set X} (hv : IsCozeroSet v) :
    IsCozeroSet (u ∩ v) := by
  obtain ⟨f, rfl⟩ := hu
  obtain ⟨g, rfl⟩ := hv
  exact ⟨f * g, by simp⟩

lemma isCozeroSet_biInter {ι : Type*} {s : Finset ι} {u : ι → Set X} (hu : ∀ i, IsCozeroSet (u i)) :
    IsCozeroSet (⋂ i ∈ s, u i) := by
  choose f hf using hu
  use ∏ i ∈ s, f i
  simp [Finset.support_prod, hf, show ∏ i ∈ s, f i = fun x ↦ ∏ i ∈ s, f i x by ext x; simp]

lemma isCozeroSet_iInter {ι : Type*} [Finite ι] {u : ι → Set X} (hu : ∀ i, IsCozeroSet (u i)) :
    IsCozeroSet (⋂ i, u i) := by
  have := Fintype.ofFinite
  simpa using isCozeroSet_biInter (s := Finset.univ) hu

lemma IsCozeroSet.union (hu : IsCozeroSet u) {v : Set X} (hv : IsCozeroSet v) :
    IsCozeroSet (u ∪ v) := by
  obtain ⟨f, hf, rfl⟩ := hu.exists_nonneg
  obtain ⟨g, hg, rfl⟩ := hv.exists_nonneg
  exact ⟨f + g, support_add_of_nonneg hf hg⟩

/-- Unions of σ-locally finite families of cozero sets are cozero sets. -/
lemma isCozeroSet_iUnion {ι : Type*} {u : ι → Set X}
    (hu : ∀ i, IsCozeroSet (u i)) (hu' : SigmaLocallyFinite u) : IsCozeroSet (⋃ i, u i) := by
  /- It suffices to prove separately that cozero sets are closed under locally finite unions and
  countable unions. -/
  revert ι
  suffices h : (∀ (ι : Type _) (u : ι → Set X),
      (∀ i, IsCozeroSet (u i)) → LocallyFinite u → IsCozeroSet (⋃ i, u i)) ∧
        ∀ u : ℕ → Set X, (∀ n, IsCozeroSet (u n)) → IsCozeroSet (⋃ n, u n) by
    rintro ι u hu hu'
    have ⟨κ', e, he⟩ := sigmaLocallyFinite_iff_exists_equiv.1 hu'
    rw [← e.symm.surjective.iUnion_comp, iUnion_sigma]
    exact h.2 _ fun n ↦ h.1 _ _ (fun _ ↦ hu _) (he n)
  refine ⟨fun ι u hu hu' ↦ ?_, fun u hu ↦ ?_⟩
  · /- Cozero sets are closed under locally finite unions because the continuous functions
    representing them can just be added. -/
    choose f hf hf' using fun i ↦ (hu i).exists_nonneg
    use ⟨_, continuous_finsum (fun i ↦ map_continuous (f i)) (by simpa [hf'])⟩
    ext x
    suffices h : ∑ᶠ i, f i x = 0 ↔ ∀ i, f i x = 0 by simpa [← hf'] using not_iff_not.2 h
    refine finsum_eq_zero_iff (fun i ↦ hf i x) ?_
    simpa [HasFiniteSupport, support, ← hf'] using hu'.point_finite x
  · /- Cozero sets are closed under countable unions because for any sequence of representing
    functions `f i` valued in the unit interval, the pointwise maximum of `f n / (n + 1)` over all
    `n` is a continuous function representing their union. A perhaps shorter proof would use the
    sum of all `f n / 2 ^ n` instead, but has been avoided in order to not import analysis files. -/
    choose f hf using fun i ↦ isCozeroSet_iff_unitInterval.1 (hu i)
    let t (n : ℕ) : I := ⟨(n + 1)⁻¹, by grind [inv_nonneg, inv_le_one₀]⟩
    have ht n m (h : n ≤ m) : t m ≤ t n := by
      grind [Subtype.mk_le_mk, inv_le_inv₀, add_le_add_iff_right, Nat.cast_le]
    refine isCozeroSet_iff_unitInterval.2 ⟨⟨⨆ n : ℕ, t n • f n, ?_⟩, ?_⟩
    · refine continuous_iff_continuousAt.2 fun x ↦ ?_
      by_cases h : ∃ n, f n x > 0
      · obtain ⟨n, hn⟩ := h
        have ⟨m, hm⟩ : ∃ m, t m < t n * f n x := by
          simpa [← Subtype.coe_lt_coe] using exists_nat_one_div_lt <|
            mul_pos (by grind [inv_pos]) <| unitInterval.coe_pos.2 hn
        refine .congr_of_eventuallyEq (.finset_sup_apply (s := Finset.Iio m)
          fun k _ ↦ map_continuousAt (t k • f k) x) ?_
        refine ((map_continuousAt (t n • f n) x).eventually_const_lt hm).mono fun x' hm' ↦ ?_
        simp only [iSup_apply, Pi.smul_apply, smul_eq_mul, ContinuousMap.coe_smul]
        rw [iSup_split _ fun k ↦ k ∈ Finset.Iio m, Finset.sup_eq_iSup, max_eq_left_iff]
        refine iSup₂_le fun k hk ↦ le_iSup₂_of_le n ?_ ?_
        · rw [Finset.mem_Iio] at hk ⊢
          grind [hm'.trans_le <| unitInterval.mul_le_left]
        · exact unitInterval.mul_le_left.trans <| (ht m k <| by simpa using hk).trans hm'.le
      · simp only [gt_iff_lt, not_exists, not_lt, nonpos_iff_eq_zero] at h
        simp only [ContinuousAt, iSup_apply, Pi.smul_apply, h, smul_eq_mul, mul_zero, ciSup_const]
        refine nhds_bot_basis_Iic.tendsto_right_iff.2 <| show (⊥ : I) = 0 by rfl ▸ fun t' ht' ↦ ?_
        have ⟨n, hn⟩ : ∃ n, t n < t' := by
          simpa [← Subtype.coe_lt_coe] using exists_nat_one_div_lt <| unitInterval.coe_pos.2 ht'
        simp only [iSup_apply, Pi.smul_apply, smul_eq_mul, mem_Iic, iSup_le_iff]
        refine ((Finset.Iic n).eventually_all (p := fun m x ↦ t m * f m x ≤ t').2 ?_).mono ?_
        · simpa using fun m hm ↦ (map_continuousAt (t m • f m) x).eventually_mem
            (s := Set.Iic t') <| Iic_mem_nhds <| by simp [h, ht']
        · refine fun x ↦ forall_imp fun m ↦ ?_
          suffices n ≤ m → t m * (f m) x ≤ t' by grind
          exact fun hm ↦ unitInterval.mul_le_left.trans <| (ht n m hm).trans hn.le
    · suffices h : ∀ n : ℕ, (⟨(n + 1)⁻¹, by grind [inv_nonneg, inv_le_one₀]⟩ : I) ≠ 0 by
        ext x; simp [show (0 : I) = ⊥ by rfl ▸ iSup_eq_bot, ← hf, t, h]
      grind [← unitInterval.coe_ne_zero, inv_eq_zero]

lemma continuous_sSup_fiber {f : X → Y} (hf : IsProperMap f) (hf' : IsOpenMap f)
    {α : Type*} [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {g : X → α} (hg : Continuous g) : Continuous fun y ↦ ⨆ x ∈ f ⁻¹' {y}, g x := by
  refine OrderTopology.continuous_iff.2 fun t ↦ ⟨?_, ?_⟩
  · convert hf' _ ((isOpen_Ioi (a := t)).preimage hg)
    ext y
    simp [lt_iSup_iff, and_comm]
  · obtain rfl | ht := eq_bot_or_bot_lt t
    · simp
    · convert (hf.isClosedMap _ ((isClosed_Ici (a := t)).preimage hg)).isOpen_compl
      ext y
      obtain hy | hy := (f ⁻¹' {y}).eq_empty_or_nonempty
      · replace hy : ∀ x, f x ≠ y := by grind [preimage_singleton_eq_empty]
        simpa [hy]
      · refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
        · simp only [mem_preimage, mem_singleton_iff, mem_Iio, mem_compl_iff, mem_image, mem_Ici,
          not_exists, not_and] at h ⊢
          intro x hx
          contrapose! hx
          exact (le_iSup₂ x hx).trans_lt h
        · have ⟨x, hx, hx'⟩ :=
            (hf.isCompact_preimage isCompact_singleton).exists_isMaxOn hy hg.continuousOn
          rw [mem_preimage, mem_Iio, ← iSup_subtype'', hx'.iSup_eq hx]
          grind

lemma continuous_sInf_fiber {f : X → Y} (hf : IsProperMap f) (hf' : IsOpenMap f)
    {α : Type*} [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {g : X → α} (hg : Continuous g) : Continuous fun y ↦ ⨅ x ∈ f ⁻¹' {y}, g x :=
  continuous_ofDual.comp <| continuous_sSup_fiber hf hf' (continuous_toDual.comp hg)

lemma continuous_parametric_iSup [CompactSpace Y]
    {α : Type*} [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {f : X → Y → α} (hf : Continuous f.uncurry) :
    Continuous fun x ↦ ⨆ y, f x y :=
  (continuous_sSup_fiber isProperMap_fst_of_compactSpace isOpenMap_fst hf).congr fun x ↦
    le_antisymm (iSup₂_le fun ⟨x, y⟩ _ ↦ le_iSup_of_le y <| by grind)
      (iSup_le fun y ↦ le_iSup₂_of_le (x, y) rfl le_rfl)

lemma continuous_parametric_iInf [CompactSpace Y]
    {α : Type*} [CompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α]
    {f : X → Y → α} (hf : Continuous f.uncurry) :
    Continuous fun x ↦ ⨅ y, f x y :=
  (continuous_sInf_fiber isProperMap_fst_of_compactSpace isOpenMap_fst hf).congr fun x ↦
    le_antisymm (le_iInf fun y ↦ iInf₂_le_of_le (x, y) rfl le_rfl)
      (le_iInf₂ fun ⟨x, y⟩ _ ↦ iInf_le_of_le y <| by grind)

/-- The image of a cozero set `u` under any proper open map `f : X → Y` is a cozero set. -/
lemma IsCozeroSet.image (hu : IsCozeroSet u) {f : X → Y} (hf : IsProperMap f)
    (hf' : IsOpenMap f) : IsCozeroSet (f '' u) := by
  rw [isCozeroSet_iff_unitInterval] at hu ⊢
  obtain ⟨g, rfl⟩ := hu
  use ⟨_, continuous_sSup_fiber hf hf' (map_continuous g)⟩
  ext y
  simp only [ContinuousMap.coe_mk, mem_support, mem_image, ← pos_iff_ne_zero, lt_biSup_iff]
  grind

/-- The coimage of a cozero set `u` under any proper open map `f : X → Y`, i.e. the set of all `y`
whose fibre `f ⁻¹' {y}` is contained in `u`, is a cozero set. -/
lemma IsCozeroSet.coimage (hu : IsCozeroSet u) {f : X → Y} (hf : IsProperMap f)
    (hf' : IsOpenMap f) : IsCozeroSet (f '' uᶜ)ᶜ := by
  rw [isCozeroSet_iff_unitInterval] at hu ⊢
  obtain ⟨g, rfl⟩ := hu
  use ⟨_, continuous_sInf_fiber hf hf' (map_continuous g)⟩
  ext y
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simp only [mem_preimage, mem_singleton_iff, ContinuousMap.coe_mk, mem_support, mem_compl_iff,
      mem_image, not_exists, not_and, ← pos_iff_ne_zero, not_imp_not] at h ⊢
    exact fun x hx ↦ h.trans_le (iInf₂_le x hx)
  · rw [mem_support, ← pos_iff_ne_zero]
    dsimp
    obtain hy | hy := (f ⁻¹' {y}).eq_empty_or_nonempty
    · simp [hy, show (0 : I) < ⊤ from one_pos]
    · have ⟨x, hx, hx'⟩ := (hf.isCompact_preimage isCompact_singleton).exists_isMinOn hy
        (map_continuous g).continuousOn
      rw [← iInf_subtype'', hx'.iInf_eq hx]
      simp only [mem_compl_iff, mem_image, mem_support, ← pos_iff_ne_zero] at h
      grind

/-- Every cozero set is Fσ, i.e. a countable union of closed sets. -/
lemma IsCozeroSet.isFσ (hu : IsCozeroSet u) : IsFσ u := by
  obtain ⟨f, rfl⟩ := hu
  exact isClosed_singleton.isOpen_compl.isFσ.preimage (map_continuous f)

/-- In normal spaces, being a cozero set is equivalent to being open and Fσ. -/
lemma isCozeroSet_iff_isFσ [NormalSpace X] : IsCozeroSet u ↔ IsOpen u ∧ IsFσ u := by
  refine ⟨fun hu ↦ ⟨hu.isOpen, hu.isFσ⟩, ?_⟩
  simp only [isFσ_iff_eq_iUnion_nat]
  rintro ⟨hu, f, hf, rfl⟩
  choose g hg using fun n ↦ exists_continuous_zero_one_of_isClosed hu.isClosed_compl (hf n) <| by
    grind [subset_iUnion f n]
  suffices h : ⋃ n, f n = ⋃ n, support (g n) from
    h ▸ isCozeroSet_iUnion (fun n ↦ (map_continuous _).isCozeroSet_support) .of_countable
  refine subset_antisymm (iUnion_mono fun n x hx ↦ ?_) (iUnion_subset fun n ↦ ?_)
  · simp only [EqOn, Pi.zero_apply, Pi.one_apply] at hg
    grind
  · simp only [EqOn, compl_iUnion, mem_iInter, Pi.zero_apply, Pi.one_apply] at hg
    grind [support_subset_iff, mem_iUnion]

/-- A topological space is perfectly normal if and only if every open set in it is a cozero set. -/
lemma perfectlyNormalSpace_iff_forall_isOpen_isCozeroSet :
    PerfectlyNormalSpace X ↔ ∀ u : Set X, IsOpen u → IsCozeroSet u := by
  rw [compl_surjective.forall]
  simp only [perfectlyNormalSpace_iff_forall_isClosed_preimage_zero, isOpen_compl_iff]
  refine forall₂_congr fun s _ ↦ ⟨fun ⟨f, hf⟩ ↦ ⟨f, by ext; simp [hf.1]⟩, fun hs ↦  ?_⟩
  have ⟨f, hf⟩ := hs.exists_nonneg_le_one
  refine ⟨f, ?_, fun x ↦ ⟨hf.1 x, hf.2.1 x⟩⟩
  simpa [support_eq_preimage] using eq_compl_comm.2 hf.2.2
