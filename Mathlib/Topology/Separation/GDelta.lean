/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yongxi Lin
-/
module

public import Mathlib.Topology.UrysohnsLemma

/-!
# Separation properties of topological spaces.

## Main definitions

* `PerfectlyNormalSpace`: A perfectly normal space is a normal space such that
  closed sets are Gδ.
* `T6Space`: A T₆ space is a perfectly normal T₀ space. T₆ implies T₅.

Note that `mathlib` adopts the modern convention that `m ≤ n` if and only if `T_m → T_n`, but
occasionally the literature swaps definitions for e.g. T₃ and regular.

-/

@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section Separation

theorem IsGδ.compl_singleton (x : X) [T1Space X] : IsGδ ({x}ᶜ : Set X) :=
  isOpen_compl_singleton.isGδ

theorem Set.Countable.isGδ_compl {s : Set X} [T1Space X] (hs : s.Countable) : IsGδ sᶜ := by
  rw [← biUnion_of_singleton s, compl_iUnion₂]
  exact .biInter hs fun x _ => .compl_singleton x

theorem Set.Finite.isGδ_compl {s : Set X} [T1Space X] (hs : s.Finite) : IsGδ sᶜ :=
  hs.countable.isGδ_compl

theorem Set.Subsingleton.isGδ_compl {s : Set X} [T1Space X] (hs : s.Subsingleton) : IsGδ sᶜ :=
  hs.finite.isGδ_compl

theorem Finset.isGδ_compl [T1Space X] (s : Finset X) : IsGδ (sᶜ : Set X) :=
  s.finite_toSet.isGδ_compl

protected theorem IsGδ.singleton [FirstCountableTopology X] [T1Space X] (x : X) :
    IsGδ ({x} : Set X) := by
  rcases (nhds_basis_opens x).exists_antitone_subbasis with ⟨U, hU, h_basis⟩
  rw [← biInter_basis_nhds h_basis.toHasBasis]
  exact .biInter (to_countable _) fun n _ => (hU n).2.isGδ

theorem Set.Finite.isGδ [FirstCountableTopology X] {s : Set X} [T1Space X] (hs : s.Finite) :
    IsGδ s :=
  Finite.induction_on _ hs .empty fun _ _ ↦ .union (.singleton _)


section PerfectlyNormal

/-- A topological space `X` is a *perfectly normal space* provided it is normal and
closed sets are Gδ. -/
class PerfectlyNormalSpace (X : Type u) [TopologicalSpace X] : Prop extends NormalSpace X where
    closed_gdelta : ∀ ⦃h : Set X⦄, IsClosed h → IsGδ h

/-- In a perfectly normal space, all closed sets are Gδ. -/
theorem IsClosed.isGδ [PerfectlyNormalSpace X] {s : Set X} (hs : IsClosed s) : IsGδ s :=
  PerfectlyNormalSpace.closed_gdelta hs

/-- A topological space is perfectly normal iff every closed set is the zero set of a continuous
function taking values in the unit interval. -/
theorem perfectlyNormalSpace_iff_forall_isClosed_preimage_zero :
    PerfectlyNormalSpace X ↔ ∀ s, IsClosed s → ∃ f : C(X, ℝ), s = f ⁻¹' {0} ∧
      range f ⊆ Icc 0 1 where
  mp h s hs := by
    -- write `s` as the intersection of a sequence of open sets `U n`
    obtain ⟨U, ho, hu⟩ := isGδ_iff_eq_iInter_nat.1 hs.isGδ
    have (n : ℕ) : Disjoint s (U n)ᶜ := by
      apply HasSubset.Subset.disjoint_compl_right
      grw [hu, iInter_subset]
    -- for each `n`, construct a continuous function `f n` that separates `s` from `(U n)ᶜ`
    choose f hfs hfu hfr using fun n =>
      exists_continuous_zero_one_of_isClosed hs (ho n).isClosed_compl (this n)
    have hsb (x : X) (n : ℕ) : ‖(f n) x * (1 / 2 / 2 ^ n)‖ ≤ 1 / 2 / 2 ^ n := by
      simp [abs_of_nonneg (hfr n x).1, (hfr n x).2]
    have hsx (x : X) : Summable fun n => f n x * (1 / 2 / 2 ^ n) :=
      (summable_geometric_two' 1).of_norm_bounded fun n => hsb x n
    -- consider the infinite sum of `f n x * (1 / 2 / 2 ^ n)`, which is uniformly convergent and
    -- thus continuous because it is dominated by a geometric series
    let h : C(X, ℝ) := {
      toFun x := ∑' n, f n x * (1 / 2 / 2 ^ n)
      continuous_toFun :=
        continuous_tsum (fun n => by fun_prop) (summable_geometric_two' 1) fun n x => hsb x n
      }
    refine ⟨h, ?_, fun r ⟨x, hx⟩ => ⟨?_, ?_⟩⟩
    · ext x
      refine ⟨fun hp => ?_, fun hp => ?_⟩
      · suffices ∀ n, f n x = 0 from by simp [h, this]
        exact fun n => hfs n hp
      · contrapose h
        simp only [preimage, notMem_setOf_iff, ContinuousMap.coe_mk, mem_singleton_iff]
        apply ne_of_gt
        obtain ⟨i, hi⟩ := mem_iUnion.1 <| compl_iInter _ ▸ mem_compl (hu ▸ h)
        calc
        _ < 1 / 2 / 2 ^ i := by positivity
        _ = f i x * (1 / 2 / 2 ^ i) := by simp [hfu i hi]
        _ ≤ _ := (hsx x).le_tsum i fun j hj => by positivity [(hfr j x).1]
    · exact hx ▸ tsum_nonneg fun n => by simp [(hfr n x).1]
    · calc
      _ = ∑' n, f n x * (1 / 2 / 2 ^ n) := by simp [← hx, h]
      _ ≤ ∑' n, 1 / 2 / 2 ^ n :=
        (hsx x).tsum_le_tsum (fun n => by simp [(hfr n x).2]) (summable_geometric_two' 1)
      _ = _ := tsum_geometric_two' 1
  mpr h := {
    normal s t hs ht hst := by
      -- pick `f, g` such that `s = f ⁻¹' {0}` and `t = g ⁻¹' {0}`, and then the function
      -- `f / (f  + g)` separates `s` and `t`.
      obtain ⟨f, hf, hfr⟩ := h s hs
      obtain ⟨g, hg, hgr⟩ := h t ht
      have hsn : SeparatedNhds {(0 : ℝ)} {1} :=
        SeparatedNhds.of_finite (finite_singleton _) (finite_singleton _)
        (disjoint_singleton.2 zero_ne_one)
      have hfg (x : X) : f x + g x ≠ 0 := by
        simp_all only [preimage, mem_singleton_iff]
        by_cases! hfx : f x = 0
        · simpa [hfx] using hst.notMem_of_mem_left hfx
        · simp only [range, Icc, setOf_subset_setOf, forall_exists_index,
            forall_apply_eq_imp_iff] at hfr hgr
          positivity [(hgr x).1, (hfr x).1]
      have hp : s = (fun a => f a / (f a + g a)) ⁻¹' {0} := by simp_all [preimage]
      have : t = (fun a => f a / (f a + g a)) ⁻¹' {1} := by simp_all [preimage, div_eq_one_iff_eq]
      rw [hp, this]
      exact hsn.preimage (f.continuous.div₀ (f.continuous.add g.continuous) hfg)
    closed_gdelta s hs := by
      by_cases! hse : s = ∅
      · simp_all
      -- pick `f` such that `s = f ⁻¹' {0} = ⋂ n, f ⁻¹' {(-1, 1 / (n + 1))}`
      obtain ⟨f, hf, hfr⟩ := h s hs
      refine isGδ_iff_eq_iInter_nat.2 ⟨fun n => f ⁻¹' (Ioo (-1 : ℝ) (1 / (n + 1))), fun n => ?_, ?_⟩
      · exact f.continuous.isOpen_preimage _ isOpen_Ioo
      · simp only [hf, ← preimage_iInter,
          ← preimage_range_inter (s := ⋂ (n : ℕ), Ioo (-1 : ℝ) (1 / (n + 1))), inter_iInter]
        congr
        ext x
        refine ⟨fun h => mem_iInter_of_mem fun n => ?_, fun h => ?_⟩
        · refine ⟨?_, ?_, by simp_all; grind⟩ <;> aesop
        · apply le_antisymm
          · simp only [mem_iInter, mem_inter_iff, mem_Ioo] at h
            exact ge_of_tendsto' tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (h n).2.2.le)
          · exact (hfr (mem_iInter.1 h 0).1).1
  }

theorem Topology.IsEmbedding.perfectlyNormalSpace {e : X → Y} (he : IsEmbedding e)
    [PerfectlyNormalSpace Y] : PerfectlyNormalSpace X := by
  rw [perfectlyNormalSpace_iff_forall_isClosed_preimage_zero]
  intro t ht
  obtain ⟨c, hc⟩ : ∃ c, IsClosed c ∧ e '' t = c ∩ range e := he.image_eq_isClosed_inter_range ht
  obtain ⟨f, rfl, hf⟩ :=
    perfectlyNormalSpace_iff_forall_isClosed_preimage_zero.1 inferInstance c hc.1
  refine ⟨⟨f ∘ e, f.continuous.comp he.continuous⟩, ?_, (range_comp_subset_range e f).trans hf⟩
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hx' : e x ∈ e '' t := by grind
    simp_all
  · have hx' : e x ∈ e '' t := by simp_all
    exact he.injective.mem_set_image.1 hx'

instance {s : Set X} [PerfectlyNormalSpace X] : PerfectlyNormalSpace s :=
  IsEmbedding.subtypeVal.perfectlyNormalSpace

/-- Lemma that allows the easy conclusion that perfectly normal spaces are completely normal. -/
theorem Disjoint.hasSeparatingCover_closed_gdelta_right {s t : Set X} [NormalSpace X]
    (st_dis : Disjoint s t) (t_cl : IsClosed t) (t_gd : IsGδ t) : HasSeparatingCover s t := by
  obtain ⟨T, T_open, T_count, T_int⟩ := t_gd
  rcases T.eq_empty_or_nonempty with rfl | T_nonempty
  · rw [T_int, sInter_empty] at st_dis
    rw [(s.disjoint_univ).mp st_dis]
    exact t.hasSeparatingCover_empty_left
  obtain ⟨g, g_surj⟩ := T_count.exists_surjective T_nonempty
  choose g' g'_open clt_sub_g' clg'_sub_g using fun n ↦ by
    apply normal_exists_closure_subset t_cl (T_open (g n).1 (g n).2)
    rw [T_int]
    exact sInter_subset_of_mem (g n).2
  have clg'_int : t = ⋂ i, closure (g' i) := by
    apply (subset_iInter fun n ↦ (clt_sub_g' n).trans subset_closure).antisymm
    rw [T_int]
    refine subset_sInter fun t tinT ↦ ?_
    obtain ⟨n, gn⟩ := g_surj ⟨t, tinT⟩
    refine iInter_subset_of_subset n <| (clg'_sub_g n).trans ?_
    rw [gn]
  use fun n ↦ (closure (g' n))ᶜ
  constructor
  · rw [← compl_iInter, subset_compl_comm, ← clg'_int]
    exact st_dis.subset_compl_left
  · refine fun n ↦ ⟨isOpen_compl_iff.mpr isClosed_closure, ?_⟩
    simp only [closure_compl, disjoint_compl_left_iff_subset]
    rw [← closure_eq_iff_isClosed.mpr t_cl] at clt_sub_g'
    exact subset_closure.trans <| (clt_sub_g' n).trans <| (g'_open n).subset_interior_closure

instance (priority := 100) PerfectlyNormalSpace.toCompletelyNormalSpace
    [PerfectlyNormalSpace X] : CompletelyNormalSpace X where
  completely_normal _ _ hd₁ hd₂ := separatedNhds_iff_disjoint.mp <|
    hasSeparatingCovers_iff_separatedNhds.mp
      ⟨(hd₂.hasSeparatingCover_closed_gdelta_right isClosed_closure <|
         closed_gdelta isClosed_closure).mono (fun ⦃_⦄ a ↦ a) subset_closure,
       ((Disjoint.symm hd₁).hasSeparatingCover_closed_gdelta_right isClosed_closure <|
         closed_gdelta isClosed_closure).mono (fun ⦃_⦄ a ↦ a) subset_closure⟩

instance (priority := 100) [PerfectlyNormalSpace X] : R0Space X where
  specializes_symmetric x y hxy := by
    rw [specializes_iff_forall_closed]
    intro K hK hyK
    apply IsClosed.isGδ at hK
    obtain ⟨Ts, hoTs, -, rfl⟩ := hK
    rw [mem_sInter] at hyK ⊢
    intros
    solve_by_elim [hxy.mem_open]

/-- A T₆ space is a perfectly normal T₀ space. -/
class T6Space (X : Type u) [TopologicalSpace X] : Prop extends T0Space X, PerfectlyNormalSpace X

-- see Note [lower instance priority]
/-- A `T₆` space is a `T₅` space. -/
instance (priority := 100) T6Space.toT5Space [T6Space X] : T5Space X where

end PerfectlyNormal

end Separation
