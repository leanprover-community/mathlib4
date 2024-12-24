/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Enum
import Mathlib.Tactic.TFAE
import Mathlib.Topology.Order.Monotone

/-!
### Topology of ordinals

We prove some miscellaneous results involving the order topology of ordinals.

### Main results

* `Ordinal.isClosed_iff_iSup` / `Ordinal.isClosed_iff_bsup`: A set of ordinals is closed iff it's
  closed under suprema.
* `Ordinal.isNormal_iff_strictMono_and_continuous`: A characterization of normal ordinal
  functions.
* `Ordinal.enumOrd_isNormal_iff_isClosed`: The function enumerating the ordinals of a set is
  normal iff the set is closed.
-/


noncomputable section

universe u v

open Cardinal Order Topology

namespace Ordinal

variable {s : Set Ordinal.{u}} {a : Ordinal.{u}}

instance : TopologicalSpace Ordinal.{u} := Preorder.topology Ordinal.{u}
instance : OrderTopology Ordinal.{u} := ⟨rfl⟩

theorem isOpen_singleton_iff : IsOpen ({a} : Set Ordinal) ↔ ¬IsLimit a := by
  refine ⟨fun h ha => ?_, fun ha => ?_⟩
  · obtain ⟨b, c, hbc, hbc'⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨0, ha.pos⟩ ⟨_, lt_succ a⟩).1
        (h.mem_nhds rfl)
    have hba := ha.succ_lt hbc.1
    exact hba.ne (hbc' ⟨lt_succ b, hba.trans hbc.2⟩)
  · rcases zero_or_succ_or_limit a with (rfl | ⟨b, rfl⟩ | ha')
    · rw [← bot_eq_zero, ← Set.Iic_bot, ← Iio_succ]
      exact isOpen_Iio
    · rw [← Set.Icc_self, Icc_succ_left, ← Ioo_succ_right]
      exact isOpen_Ioo
    · exact (ha ha').elim

protected theorem nhdsGT (a : Ordinal) : 𝓝[>] a = ⊥ := SuccOrder.nhdsGT

@[deprecated (since := "2024-12-22")] alias nhds_right' := Ordinal.nhdsGT

-- todo: generalize to a `SuccOrder`
theorem nhdsLT_eq_nhdsNE (a : Ordinal) : 𝓝[<] a = 𝓝[≠] a := by
  rw [← nhdsLT_sup_nhdsGT, Ordinal.nhdsGT, sup_bot_eq]

@[deprecated (since := "2024-12-22")] alias nhds_left'_eq_nhds_ne := nhdsLT_eq_nhdsNE

-- todo: generalize to a `SuccOrder`
theorem nhdsLE_eq_nhds (a : Ordinal) : 𝓝[≤] a = 𝓝 a := by
  rw [← nhdsLE_sup_nhdsGT, SuccOrder.nhdsGT, sup_bot_eq]

@[deprecated (since := "2024-12-22")] alias nhds_left_eq_nhds := nhdsLE_eq_nhds

-- todo: generalize to a `SuccOrder`
theorem hasBasis_nhds_Ioc (h : a ≠ 0) : (𝓝 a).HasBasis (· < a) (Set.Ioc · a) :=
  nhdsLE_eq_nhds a ▸ nhdsLE_basis_of_exists_lt ⟨0, h.bot_lt⟩

@[deprecated (since := "2024-12-22")] alias nhdsBasis_Ioc := hasBasis_nhds_Ioc

-- todo: generalize to a `SuccOrder`
theorem nhds_eq_pure : 𝓝 a = pure a ↔ ¬IsLimit a :=
  (isOpen_singleton_iff_nhds_eq_pure _).symm.trans isOpen_singleton_iff

-- todo: generalize `Ordinal.IsLimit` and this lemma to a `SuccOrder`
theorem isOpen_iff : IsOpen s ↔ ∀ o ∈ s, IsLimit o → ∃ a < o, Set.Ioo a o ⊆ s := by
  refine isOpen_iff_mem_nhds.trans <| forall₂_congr fun o ho => ?_
  by_cases ho' : IsLimit o
  · simp only [(hasBasis_nhds_Ioc ho'.ne_zero).mem_iff, ho', true_implies]
    refine exists_congr fun a => and_congr_right fun ha => ?_
    simp only [← Set.Ioo_insert_right ha, Set.insert_subset_iff, ho, true_and]
  · simp [nhds_eq_pure.2 ho', ho, ho']

open List Set in
theorem mem_closure_tfae (a : Ordinal.{u}) (s : Set Ordinal) :
    TFAE [a ∈ closure s,
      a ∈ closure (s ∩ Iic a),
      (s ∩ Iic a).Nonempty ∧ sSup (s ∩ Iic a) = a,
      ∃ t, t ⊆ s ∧ t.Nonempty ∧ BddAbove t ∧ sSup t = a,
      ∃ (o : Ordinal.{u}), o ≠ 0 ∧ ∃ (f : ∀ x < o, Ordinal),
        (∀ x hx, f x hx ∈ s) ∧ bsup.{u, u} o f = a,
      ∃ (ι : Type u), Nonempty ι ∧ ∃ f : ι → Ordinal, (∀ i, f i ∈ s) ∧ ⨆ i, f i = a] := by
  tfae_have 1 → 2 := by
    simp only [mem_closure_iff_nhdsWithin_neBot, inter_comm s, nhdsWithin_inter', nhdsLE_eq_nhds]
    exact id
  tfae_have 2 → 3
  | h => by
    rcases (s ∩ Iic a).eq_empty_or_nonempty with he | hne
    · simp [he] at h
    · refine ⟨hne, (isLUB_of_mem_closure ?_ h).csSup_eq hne⟩
      exact fun x hx => hx.2
  tfae_have 3 → 4
  | h => ⟨_, inter_subset_left, h.1, bddAbove_Iic.mono inter_subset_right, h.2⟩
  tfae_have 4 → 5 := by
    rintro ⟨t, hts, hne, hbdd, rfl⟩
    have hlub : IsLUB t (sSup t) := isLUB_csSup hne hbdd
    let ⟨y, hyt⟩ := hne
    classical
      refine ⟨succ (sSup t), succ_ne_zero _, fun x _ => if x ∈ t then x else y, fun x _ => ?_, ?_⟩
      · simp only
        split_ifs with h <;> exact hts ‹_›
      · refine le_antisymm (bsup_le fun x _ => ?_) (csSup_le hne fun x hx => ?_)
        · split_ifs <;> exact hlub.1 ‹_›
        · refine (if_pos hx).symm.trans_le (le_bsup _ _ <| (hlub.1 hx).trans_lt (lt_succ _))
  tfae_have 5 → 6 := by
    rintro ⟨o, h₀, f, hfs, rfl⟩
    exact ⟨_, toType_nonempty_iff_ne_zero.2 h₀, familyOfBFamily o f, fun _ => hfs _ _, rfl⟩
  tfae_have 6 → 1 := by
    rintro ⟨ι, hne, f, hfs, rfl⟩
    exact closure_mono (range_subset_iff.2 hfs) <| csSup_mem_closure (range_nonempty f)
      (bddAbove_range.{u, u} f)
  tfae_finish

theorem mem_closure_iff_iSup :
    a ∈ closure s ↔
      ∃ (ι : Type u) (_ : Nonempty ι) (f : ι → Ordinal), (∀ i, f i ∈ s) ∧ ⨆ i, f i = a := by
  apply ((mem_closure_tfae a s).out 0 5).trans
  simp_rw [exists_prop]

set_option linter.deprecated false in
@[deprecated mem_closure_iff_iSup (since := "2024-08-27")]
theorem mem_closure_iff_sup :
    a ∈ closure s ↔
      ∃ (ι : Type u) (_ : Nonempty ι) (f : ι → Ordinal), (∀ i, f i ∈ s) ∧ sup f = a :=
  mem_closure_iff_iSup

theorem mem_iff_iSup_of_isClosed (hs : IsClosed s) :
    a ∈ s ↔ ∃ (ι : Type u) (_hι : Nonempty ι) (f : ι → Ordinal),
      (∀ i, f i ∈ s) ∧ ⨆ i, f i = a := by
  rw [← mem_closure_iff_iSup, hs.closure_eq]

set_option linter.deprecated false in
@[deprecated mem_iff_iSup_of_isClosed (since := "2024-08-27")]
theorem mem_closed_iff_sup (hs : IsClosed s) :
    a ∈ s ↔ ∃ (ι : Type u) (_hι : Nonempty ι) (f : ι → Ordinal),
      (∀ i, f i ∈ s) ∧ sup f = a :=
  mem_iff_iSup_of_isClosed hs

theorem mem_closure_iff_bsup :
    a ∈ closure s ↔
      ∃ (o : Ordinal) (_ho : o ≠ 0) (f : ∀ a < o, Ordinal),
        (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a := by
  apply ((mem_closure_tfae a s).out 0 4).trans
  simp_rw [exists_prop]

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
@[deprecated mem_iff_iSup_of_isClosed (since := "2024-08-27")]
theorem isClosed_iff_sup :
    IsClosed s ↔
      ∀ {ι : Type u}, Nonempty ι → ∀ f : ι → Ordinal, (∀ i, f i ∈ s) → ⨆ i, f i ∈ s := by
  use fun hs ι hι f hf => (mem_closed_iff_sup hs).2 ⟨ι, hι, f, hf, rfl⟩
  rw [← closure_subset_iff_isClosed]
  intro h x hx
  rcases mem_closure_iff_sup.1 hx with ⟨ι, hι, f, hf, rfl⟩
  exact h hι f hf

theorem isClosed_iff_bsup :
    IsClosed s ↔
      ∀ {o : Ordinal}, o ≠ 0 → ∀ f : ∀ a < o, Ordinal,
        (∀ i hi, f i hi ∈ s) → bsup.{u, u} o f ∈ s := by
  rw [isClosed_iff_iSup]
  refine ⟨fun H o ho f hf => H (toType_nonempty_iff_ne_zero.2 ho) _ ?_, fun H ι hι f hf => ?_⟩
  · exact fun i => hf _ _
  · rw [← Ordinal.sup, ← bsup_eq_sup]
    apply H (type_ne_zero_iff_nonempty.2 hι)
    exact fun i hi => hf _

theorem isLimit_of_mem_frontier (ha : a ∈ frontier s) : IsLimit a := by
  simp only [frontier_eq_closure_inter_closure, Set.mem_inter_iff, mem_closure_iff] at ha
  by_contra h
  rw [← isOpen_singleton_iff] at h
  rcases ha.1 _ h rfl with ⟨b, hb, hb'⟩
  rcases ha.2 _ h rfl with ⟨c, hc, hc'⟩
  rw [Set.mem_singleton_iff] at *
  subst hb; subst hc
  exact hc' hb'

theorem isNormal_iff_strictMono_and_continuous (f : Ordinal.{u} → Ordinal.{u}) :
    IsNormal f ↔ StrictMono f ∧ Continuous f := by
  refine ⟨fun h => ⟨h.strictMono, ?_⟩, ?_⟩
  · rw [continuous_def]
    intro s hs
    rw [isOpen_iff] at *
    intro o ho ho'
    rcases hs _ ho (h.isLimit ho') with ⟨a, ha, has⟩
    rw [← IsNormal.bsup_eq.{u, u} h ho', lt_bsup] at ha
    rcases ha with ⟨b, hb, hab⟩
    exact
      ⟨b, hb, fun c hc =>
        Set.mem_preimage.2 (has ⟨hab.trans (h.strictMono hc.1), h.strictMono hc.2⟩)⟩
  · rw [isNormal_iff_strictMono_limit]
    rintro ⟨h, h'⟩
    refine ⟨h, fun o ho a h => ?_⟩
    suffices o ∈ f ⁻¹' Set.Iic a from Set.mem_preimage.1 this
    rw [mem_iff_iSup_of_isClosed (IsClosed.preimage h' (@isClosed_Iic _ _ _ _ a))]
    exact
      ⟨_, toType_nonempty_iff_ne_zero.2 ho.ne_zero, typein (· < ·), fun i => h _ (typein_lt_self i),
        sup_typein_limit fun _ ↦ ho.succ_lt⟩

theorem enumOrd_isNormal_iff_isClosed (hs : ¬ BddAbove s) :
    IsNormal (enumOrd s) ↔ IsClosed s := by
  have Hs := enumOrd_strictMono hs
  refine
    ⟨fun h => isClosed_iff_iSup.2 fun {ι} hι f hf => ?_, fun h =>
      (isNormal_iff_strictMono_limit _).2 ⟨Hs, fun a ha o H => ?_⟩⟩
  · let g : ι → Ordinal.{u} := fun i => (enumOrdOrderIso s hs).symm ⟨_, hf i⟩
    suffices enumOrd s (⨆ i, g i) = ⨆ i, f i by
      rw [← this]
      exact enumOrd_mem hs _
    rw [IsNormal.map_iSup h g]
    congr
    ext x
    change (enumOrdOrderIso s hs _).val = f x
    rw [OrderIso.apply_symm_apply]
  · rw [isClosed_iff_bsup] at h
    suffices enumOrd s a ≤ bsup.{u, u} a fun b (_ : b < a) => enumOrd s b from
      this.trans (bsup_le H)
    obtain ⟨b, hb⟩ := enumOrd_surjective hs (h ha.ne_zero (fun b _ => enumOrd s b)
      fun b _ => enumOrd_mem hs b)
    rw [← hb]
    apply Hs.monotone
    by_contra! hba
    apply (Hs (lt_succ b)).not_le
    rw [hb]
    exact le_bsup.{u, u} _ _ (ha.succ_lt hba)

open Set Filter Set.Notation

/-- An ordinal is an accumulation point of a set of ordinals if it is positive and there
are elements in the set arbitrarily close to the ordinal from below. -/
def IsAcc (o : Ordinal) (S : Set Ordinal) : Prop :=
  AccPt o (𝓟 S)

/-- A set of ordinals is closed below an ordinal if it contains all of
its accumulation points below the ordinal. -/
def IsClosedBelow (S : Set Ordinal) (o : Ordinal) : Prop :=
  IsClosed (Iio o ↓∩ S)

theorem isAcc_iff {o : Ordinal} {S : Set Ordinal} : o.IsAcc S ↔
    o ≠ 0 ∧ ∀ p < o, (S ∩ Ioo p o).Nonempty := by
  dsimp [IsAcc]
  constructor
  · rw [accPt_iff_nhds]
    intro h
    constructor
    · rintro rfl
      obtain ⟨x, hx⟩ := h (Iio 1) (Iio_mem_nhds zero_lt_one)
      exact hx.2 <| lt_one_iff_zero.mp hx.1.1
    · intro p plt
      obtain ⟨x, hx⟩ := h (Ioo p (o + 1)) <| Ioo_mem_nhds plt (lt_succ o)
      use x
      refine ⟨hx.1.2, ⟨hx.1.1.1, lt_of_le_of_ne ?_ hx.2⟩⟩
      have := hx.1.1.2
      rwa [← succ_eq_add_one, lt_succ_iff] at this
  · rw [accPt_iff_nhds]
    intro h u umem
    obtain ⟨l, hl⟩ := exists_Ioc_subset_of_mem_nhds umem ⟨0, Ordinal.pos_iff_ne_zero.mpr h.1⟩
    obtain ⟨x, hx⟩ := h.2 l hl.1
    use x
    exact ⟨⟨hl.2 ⟨hx.2.1, hx.2.2.le⟩, hx.1⟩, hx.2.2.ne⟩

theorem IsAcc.forall_lt {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) :
    ∀ p < o, (S ∩ Ioo p o).Nonempty := (isAcc_iff.mp h).2

theorem IsAcc.pos {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) :
    0 < o := Ordinal.pos_iff_ne_zero.mpr (isAcc_iff.mp h).1

theorem IsAcc.isLimit {o : Ordinal} {S : Set Ordinal} (h : o.IsAcc S) : IsLimit o := by
  rw [isAcc_iff] at h
  refine isLimit_of_not_succ_of_ne_zero (fun ⟨x, hx⟩ ↦ ?_) h.1
  rcases h.2 x (lt_of_lt_of_le (lt_succ x) hx.symm.le) with ⟨p, hp⟩
  exact (hx.symm ▸ (succ_le_iff.mpr hp.2.1)).not_lt hp.2.2

theorem IsAcc.mono {o : Ordinal} {S T : Set Ordinal} (h : S ⊆ T) (ho : o.IsAcc S) :
    o.IsAcc T := by
  rw [isAcc_iff] at *
  exact ⟨ho.1, fun p plto ↦ (ho.2 p plto).casesOn fun s hs ↦ ⟨s, h hs.1, hs.2⟩⟩

theorem IsAcc.inter_Ioo_nonempty {o : Ordinal} {S : Set Ordinal} (hS : o.IsAcc S)
    {p : Ordinal} (hp : p < o) : (S ∩ Ioo p o).Nonempty := hS.forall_lt p hp

-- todo: prove this for a general linear `SuccOrder`.
theorem accPt_subtype {p o : Ordinal} (S : Set Ordinal) (hpo : p < o) :
    AccPt p (𝓟 S) ↔ AccPt ⟨p, hpo⟩ (𝓟 (Iio o ↓∩ S)) := by
  constructor
  · intro h
    have plim : p.IsLimit := IsAcc.isLimit h
    rw [accPt_iff_nhds] at *
    intro u hu
    obtain ⟨l, hl⟩ := exists_Ioc_subset_of_mem_nhds hu ⟨⟨0, plim.pos.trans hpo⟩, plim.pos⟩
    obtain ⟨x, hx⟩ := h (Ioo l (p + 1)) (Ioo_mem_nhds hl.1 (lt_add_one _))
    use ⟨x, lt_of_le_of_lt (lt_succ_iff.mp hx.1.1.2) hpo⟩
    refine ⟨?_, Subtype.coe_ne_coe.mp hx.2⟩
    exact ⟨hl.2 ⟨hx.1.1.1, by exact_mod_cast lt_succ_iff.mp hx.1.1.2⟩, hx.1.2⟩
  · intro h
    rw [accPt_iff_nhds] at *
    intro u hu
    by_cases ho : p + 1 < o
    · have ppos : p ≠ 0 := by
        rintro rfl
        rw [zero_add] at ho
        specialize h (Iio ⟨1, ho⟩) (Iio_mem_nhds (Subtype.mk_lt_mk.mpr zero_lt_one))
        obtain ⟨_, h⟩ := h
        exact h.2 <| Subtype.mk_eq_mk.mpr (lt_one_iff_zero.mp h.1.1)
      have plim : p.IsLimit := by
        contrapose! h
        obtain ⟨q, hq⟩ := ((zero_or_succ_or_limit p).resolve_left ppos).resolve_right h
        use (Ioo ⟨q, ((hq ▸ lt_succ q).trans hpo)⟩ ⟨p + 1, ho⟩)
        constructor
        · exact Ioo_mem_nhds (by simp only [hq, Subtype.mk_lt_mk, lt_succ]) (lt_succ p)
        · intro _ mem
          have aux1 := Subtype.mk_lt_mk.mp mem.1.1
          have aux2 := Subtype.mk_lt_mk.mp mem.1.2
          rw [Subtype.mk_eq_mk]
          rw [hq] at aux2 ⊢
          exact ((succ_le_iff.mpr aux1).antisymm (le_of_lt_succ aux2)).symm
      obtain ⟨l, hl⟩ := exists_Ioc_subset_of_mem_nhds hu ⟨0, plim.pos⟩
      obtain ⟨x, hx⟩ := h (Ioo ⟨l, hl.1.trans hpo⟩ ⟨p + 1, ho⟩) (Ioo_mem_nhds hl.1 (lt_add_one p))
      use x
      exact ⟨⟨hl.2 ⟨hx.1.1.1, lt_succ_iff.mp hx.1.1.2⟩, hx.1.2⟩, fun h ↦ hx.2 (SetCoe.ext h)⟩
    have hp : o = p + 1 := (le_succ_iff_eq_or_le.mp (le_of_not_lt ho)).resolve_right
      (not_le_of_lt hpo)
    have ppos : p ≠ 0 := by
      rintro rfl
      obtain ⟨x, hx⟩ := h Set.univ univ_mem
      have : ↑x < o := x.2
      simp_rw [hp, zero_add, lt_one_iff_zero] at this
      exact hx.2 (SetCoe.ext this)
    obtain ⟨l, hl⟩ := exists_Ioc_subset_of_mem_nhds hu ⟨0, Ordinal.pos_iff_ne_zero.mpr ppos⟩
    obtain ⟨x, hx⟩ := h (Ioi ⟨l, hl.1.trans hpo⟩) (Ioi_mem_nhds hl.1)
    use x
    refine ⟨⟨hl.2 ⟨hx.1.1, ?_⟩, hx.1.2⟩, fun h ↦ hx.2 (SetCoe.ext h)⟩
    rw [← lt_add_one_iff, ← hp]
    exact x.2

theorem isClosedBelow_iff {S : Set Ordinal} {o : Ordinal} : IsClosedBelow S o ↔
    ∀ p < o, IsAcc p S → p ∈ S := by
  dsimp [IsClosedBelow]
  constructor
  · intro h p plto hp
    have : AccPt ⟨p, plto⟩ (𝓟 (Iio o ↓∩ S)) := (accPt_subtype _ _).mp hp
    rw [isClosed_iff_clusterPt] at h
    exact h ⟨p, plto⟩ this.clusterPt
  · intro h
    rw [isClosed_iff_clusterPt]
    intro r hr
    match clusterPt_principal.mp hr with
    | .inl h => exact h
    | .inr h' => exact h r.1 r.2 <| (accPt_subtype _ _).mpr h'

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
