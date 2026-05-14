/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.Enum
public import Mathlib.Tactic.TFAE
public import Mathlib.Topology.Order.Monotone
public import Mathlib.Topology.Order.SuccPred

/-!
# Topology of ordinals

We prove some miscellaneous results involving the order topology of ordinals.

## Main results

* `Ordinal.isClosed_iff_iSup`: A set of ordinals is closed iff it's
  closed under suprema.
* `Ordinal.enumOrd_isNormal_iff_isClosed`: The function enumerating the ordinals of a set is
  normal iff the set is closed.

## Todo

Most things in this file should be generalized to other well-orders, or to Scott-Hausdorff
topologies.
-/

@[expose] public noncomputable section

universe u v

open Cardinal Order Topology

namespace Ordinal

variable {s : Set Ordinal.{u}} {a : Ordinal.{u}}

instance : TopologicalSpace Ordinal.{u} := Preorder.topology Ordinal.{u}
instance : OrderTopology Ordinal.{u} := ⟨rfl⟩

@[deprecated SuccOrder.isOpen_singleton_iff (since := "2026-01-20")]
theorem isOpen_singleton_iff : IsOpen ({a} : Set Ordinal) ↔ ¬ IsSuccLimit a :=
  SuccOrder.isOpen_singleton_iff

@[deprecated SuccOrder.nhds_eq_pure (since := "2026-01-20")]
theorem nhds_eq_pure : 𝓝 a = pure a ↔ ¬ IsSuccLimit a :=
  SuccOrder.nhds_eq_pure

@[deprecated SuccOrder.isOpen_iff (since := "2026-01-20")]
theorem isOpen_iff : IsOpen s ↔ ∀ o ∈ s, IsSuccLimit o → ∃ a < o, Set.Ioo a o ⊆ s :=
  SuccOrder.isOpen_iff

open List Set in
theorem mem_closure_tfae (a : Ordinal.{u}) (s : Set Ordinal) :
    TFAE [a ∈ closure s,
      a ∈ closure (s ∩ Iic a),
      (s ∩ Iic a).Nonempty ∧ sSup (s ∩ Iic a) = a,
      ∃ t, t ⊆ s ∧ t.Nonempty ∧ BddAbove t ∧ sSup t = a,
      ∃ (ι : Type u), Nonempty ι ∧ ∃ f : ι → Ordinal, (∀ i, f i ∈ s) ∧ ⨆ i, f i = a] := by
  tfae_have 1 → 2 := by
    simpa only [mem_closure_iff_nhdsWithin_neBot, inter_comm s, nhdsWithin_inter',
      SuccOrder.nhdsLE_eq_nhds] using id
  tfae_have 2 → 3
  | h => by
    rcases (s ∩ Iic a).eq_empty_or_nonempty with he | hne
    · simp [he] at h
    · refine ⟨hne, (isLUB_of_mem_closure ?_ h).csSup_eq hne⟩
      exact fun x hx => hx.2
  tfae_have 3 → 4
  | h => ⟨_, inter_subset_left, h.1, bddAbove_Iic.mono inter_subset_right, h.2⟩
  tfae_have 4 → 5 := by
    rintro ⟨t, ht, ht₀, ht₁, rfl⟩
    rw [bddAbove_iff_small] at ht₁
    refine ⟨Shrink t, ?_, Subtype.val ∘ (equivShrink _).symm, ?_, ?_⟩
    · have := ht₀.to_subtype
      exact (equivShrink _).symm.nonempty
    · simpa [← (equivShrink t).forall_congr_left (p := (·.1 ∈ s))]
    · simp [(equivShrink t).symm.iSup_comp, ← sSup_eq_iSup']
  tfae_have 5 → 1 := by
    rintro ⟨ι, hne, f, hfs, rfl⟩
    exact closure_mono (range_subset_iff.2 hfs) <| csSup_mem_closure (range_nonempty f)
      bddAbove_of_small
  tfae_finish

theorem mem_closure_iff_iSup :
    a ∈ closure s ↔
      ∃ (ι : Type u) (_ : Nonempty ι) (f : ι → Ordinal), (∀ i, f i ∈ s) ∧ ⨆ i, f i = a := by
  apply ((mem_closure_tfae a s).out 0 4).trans
  simp_rw [exists_prop]

theorem mem_iff_iSup_of_isClosed (hs : IsClosed s) :
    a ∈ s ↔ ∃ (ι : Type u) (_hι : Nonempty ι) (f : ι → Ordinal),
      (∀ i, f i ∈ s) ∧ ⨆ i, f i = a := by
  rw [← mem_closure_iff_iSup, hs.closure_eq]

set_option linter.deprecated false in
@[deprecated mem_closure_iff_iSup (since := "2026-04-05")]
theorem mem_closure_iff_bsup :
    a ∈ closure s ↔
      ∃ (o : Ordinal) (_ho : o ≠ 0) (f : ∀ a < o, Ordinal),
        (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a := by
  rw [mem_closure_iff_iSup]
  constructor
  · rintro ⟨ι, _, f, hf, rfl⟩
    exact ⟨_, by simp, bfamilyOfFamily f, fun i hi ↦ hf .., bsup_eq_iSup f⟩
  · rintro ⟨o, ho, f, hf, rfl⟩
    exact ⟨_, by simpa, familyOfBFamily _ f, fun i ↦ hf .., iSup_eq_bsup f⟩

set_option linter.deprecated false in
@[deprecated mem_closure_iff_iSup (since := "2026-04-05")]
theorem mem_closed_iff_bsup (hs : IsClosed s) :
    a ∈ s ↔
      ∃ (o : Ordinal) (_ho : o ≠ 0) (f : ∀ a < o, Ordinal),
        (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a := by
  rw [← mem_closure_iff_bsup, hs.closure_eq]

theorem isClosed_iff_iSup :
    IsClosed s ↔
      ∀ {ι : Type u}, Nonempty ι → ∀ f : ι → Ordinal, (∀ i, f i ∈ s) → ⨆ i, f i ∈ s := by
  use fun hs ι hι f hf => (mem_iff_iSup_of_isClosed hs).2 ⟨ι, hι, f, hf, rfl⟩
  rw [← closure_subset_iff_isClosed]
  intro h x hx
  rcases mem_closure_iff_iSup.1 hx with ⟨ι, hι, f, hf, rfl⟩
  exact h hι f hf

set_option linter.deprecated false in
@[deprecated isClosed_iff_iSup (since := "2026-04-05")]
theorem isClosed_iff_bsup :
    IsClosed s ↔
      ∀ {o : Ordinal}, o ≠ 0 → ∀ f : ∀ a < o, Ordinal,
        (∀ i hi, f i hi ∈ s) → bsup.{u, u} o f ∈ s := by
  rw [isClosed_iff_iSup]
  refine ⟨fun H o ho f hf => H (nonempty_toType_iff.2 ho) _ ?_, fun H ι hι f hf => ?_⟩
  · exact fun i => hf _ _
  · rw [← bsup_eq_iSup]
    apply H (type_ne_zero_iff_nonempty.2 hι)
    exact fun i hi => hf _

@[deprecated SuccOrder.isSuccLimit_of_mem_frontier (since := "2026-01-20")]
theorem isSuccLimit_of_mem_frontier (ha : a ∈ frontier s) : IsSuccLimit a :=
  SuccOrder.isSuccLimit_of_mem_frontier ha

theorem enumOrd_isNormal_iff_isClosed (hs : ¬ BddAbove s) :
    IsNormal (enumOrd s) ↔ IsClosed s := by
  have Hs := enumOrd_strictMono hs
  refine
    ⟨fun h => isClosed_iff_iSup.2 fun {ι} hι f hf => ?_, fun h =>
      isNormal_iff.2 ⟨Hs, fun a ha o H => ?_⟩⟩
  · let g : ι → Ordinal.{u} := fun i => (enumOrdOrderIso s hs).symm ⟨_, hf i⟩
    suffices enumOrd s (⨆ i, g i) = ⨆ i, f i by
      rw [← this]
      exact enumOrd_mem hs _
    rw [h.map_iSup bddAbove_of_small]
    congr
    ext x
    change (enumOrdOrderIso s hs _).val = f x
    rw [OrderIso.apply_symm_apply]
  · have := csSup_mem_closure (ha.nonempty_Iio.image (enumOrd s)) bddAbove_of_small
    have := h.closure_eq ▸ closure_mono (t := s) ?_ this
    · apply (Set.image_subset_range ..).trans_eq
      rw [range_enumOrd hs]
    · apply (enumOrd_le_of_forall_lt this _).trans
      · apply csSup_le'
        grind [upperBounds]
      · exact fun b hb ↦ (enumOrd_strictMono hs (lt_add_one b)).trans_le <|
          le_csSup bddAbove_of_small <| Set.mem_image_of_mem _ (ha.add_one_lt hb)

open Set Filter Set.Notation

/-- An ordinal is an accumulation point of a set of ordinals if it is positive and there
are elements in the set arbitrarily close to the ordinal from below. -/
def IsAcc (o : Ordinal) (S : Set Ordinal) : Prop :=
  AccPt o (𝓟 S)

/-- A set of ordinals is closed below an ordinal if it contains all of
its accumulation points below the ordinal. -/
def IsClosedBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  IsClosed (Iio o ↓∩ S)

theorem isAcc_iff (o : Ordinal) (S : Set Ordinal) : o.IsAcc S ↔
    o ≠ 0 ∧ ∀ p < o, (S ∩ Ioo p o).Nonempty := by
  dsimp [IsAcc]
  constructor
  · rw [accPt_iff_nhds]
    intro h
    constructor
    · rintro rfl
      obtain ⟨x, hx⟩ := h (Iio 1) (Iio_mem_nhds zero_lt_one)
      exact hx.2 <| lt_one_iff.mp hx.1.1
    · intro p plt
      obtain ⟨x, hx⟩ := h (Ioo p (o + 1)) <| Ioo_mem_nhds plt (lt_succ o)
      use x
      refine ⟨hx.1.2, ⟨hx.1.1.1, lt_of_le_of_ne ?_ hx.2⟩⟩
      have := hx.1.1.2
      rwa [← succ_eq_add_one, lt_succ_iff] at this
  · rw [accPt_iff_nhds]
    intro h u umem
    obtain ⟨l, hl⟩ := exists_Ioc_subset_of_mem_nhds umem ⟨0, pos_iff_ne_zero.mpr h.1⟩
    obtain ⟨x, hx⟩ := h.2 l hl.1
    use x
    exact ⟨⟨hl.2 ⟨hx.2.1, hx.2.2.le⟩, hx.1⟩, hx.2.2.ne⟩

theorem IsAcc.forall_lt {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) :
    ∀ p < o, (S ∩ Ioo p o).Nonempty := ((isAcc_iff _ _).mp h).2

theorem IsAcc.pos {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) :
    0 < o := pos_iff_ne_zero.mpr ((isAcc_iff _ _).mp h).1

theorem IsAcc.isSuccLimit {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) : IsSuccLimit o := by
  rw [isAcc_iff] at h
  rw [isSuccLimit_iff]
  refine ⟨h.1, isSuccPrelimit_of_succ_ne fun x hx ↦ ?_⟩
  rcases h.2 x (lt_of_lt_of_le (lt_succ x) hx.le) with ⟨p, hp⟩
  exact (hx.symm ▸ (succ_le_iff.mpr hp.2.1)).not_gt hp.2.2

theorem IsAcc.mono {o : Ordinal} {S T : Set Ordinal} (h : S ⊆ T) (ho : o.IsAcc S) :
    o.IsAcc T := by
  rw [isAcc_iff] at *
  exact ⟨ho.1, fun p plto ↦ (ho.2 p plto).casesOn fun s hs ↦ ⟨s, h hs.1, hs.2⟩⟩

theorem IsAcc.inter_Ioo_nonempty {o : Ordinal} {S : Set Ordinal} (hS : o.IsAcc S)
    {p : Ordinal} (hp : p < o) : (S ∩ Ioo p o).Nonempty := hS.forall_lt p hp

@[deprecated IsOpenEmbedding.accPt_comap_iff (since := "2026-03-30")]
theorem accPt_subtype {p o : Ordinal} (S : Set Ordinal) (hpo : p < o) :
    AccPt p (𝓟 S) ↔ AccPt ⟨p, hpo⟩ (𝓟 (Iio o ↓∩ S)) := by
  rw [← comap_principal, isOpen_Iio.isOpenEmbedding_subtypeVal.accPt_comap_iff]

theorem isClosedBelow_iff {S : Set Ordinal} {o : Ordinal} : IsClosedBelow S o ↔
    ∀ p < o, IsAcc p S → p ∈ S := by
  simp [IsClosedBelow, IsAcc, isClosed_iff_accPt, ← comap_principal,
    isOpen_Iio.isOpenEmbedding_subtypeVal.accPt_comap_iff]

alias ⟨IsClosedBelow.forall_lt, _⟩ := isClosedBelow_iff

theorem IsClosedBelow.sInter {o : Ordinal} {S : Set (Set Ordinal)}
    (h : ∀ C ∈ S, IsClosedBelow C o) : IsClosedBelow (⋂₀ S) o := by
  rw [isClosedBelow_iff]
  intro p plto pAcc C CmemS
  exact (h C CmemS).forall_lt p plto (pAcc.mono (sInter_subset_of_mem CmemS))

theorem IsClosedBelow.iInter {ι : Type u} {f : ι → Set Ordinal} {o : Ordinal}
    (h : ∀ i, IsClosedBelow (f i) o) : IsClosedBelow (⋂ i, f i) o :=
  IsClosedBelow.sInter fun _ ⟨i, hi⟩ ↦ hi ▸ (h i)

end Ordinal
