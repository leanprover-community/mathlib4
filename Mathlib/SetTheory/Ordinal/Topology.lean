/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic.TFAE
import Mathlib.Topology.Order.Monotone

#align_import set_theory.ordinal.topology from "leanprover-community/mathlib"@"740acc0e6f9adf4423f92a485d0456fc271482da"

/-!
### Topology of ordinals

We prove some miscellaneous results involving the order topology of ordinals.

### Main results

* `Ordinal.isClosed_iff_sup` / `Ordinal.isClosed_iff_bsup`: A set of ordinals is closed iff it's
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
  refine ⟨fun h ⟨h₀, hsucc⟩ => ?_, fun ha => ?_⟩
  · obtain ⟨b, c, hbc, hbc'⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨0, Ordinal.pos_iff_ne_zero.2 h₀⟩ ⟨_, lt_succ a⟩).1
        (h.mem_nhds rfl)
    have hba := hsucc b hbc.1
    exact hba.ne (hbc' ⟨lt_succ b, hba.trans hbc.2⟩)
  · rcases zero_or_succ_or_limit a with (rfl | ⟨b, rfl⟩ | ha')
    · rw [← bot_eq_zero, ← Set.Iic_bot, ← Iio_succ]
      exact isOpen_Iio
    · rw [← Set.Icc_self, Icc_succ_left, ← Ioo_succ_right]
      exact isOpen_Ioo
    · exact (ha ha').elim
#align ordinal.is_open_singleton_iff Ordinal.isOpen_singleton_iff

-- Porting note (#11215): TODO: generalize to a `SuccOrder`
theorem nhds_right' (a : Ordinal) : 𝓝[>] a = ⊥ := (covBy_succ a).nhdsWithin_Ioi

-- todo: generalize to a `SuccOrder`
theorem nhds_left'_eq_nhds_ne (a : Ordinal) : 𝓝[<] a = 𝓝[≠] a := by
  rw [← nhds_left'_sup_nhds_right', nhds_right', sup_bot_eq]

-- todo: generalize to a `SuccOrder`
theorem nhds_left_eq_nhds (a : Ordinal) : 𝓝[≤] a = 𝓝 a := by
  rw [← nhds_left_sup_nhds_right', nhds_right', sup_bot_eq]

-- todo: generalize to a `SuccOrder`
theorem nhdsBasis_Ioc (h : a ≠ 0) : (𝓝 a).HasBasis (· < a) (Set.Ioc · a) :=
  nhds_left_eq_nhds a ▸ nhdsWithin_Iic_basis' ⟨0, h.bot_lt⟩

-- todo: generalize to a `SuccOrder`
theorem nhds_eq_pure : 𝓝 a = pure a ↔ ¬IsLimit a :=
  (isOpen_singleton_iff_nhds_eq_pure _).symm.trans isOpen_singleton_iff

-- todo: generalize `Ordinal.IsLimit` and this lemma to a `SuccOrder`
theorem isOpen_iff : IsOpen s ↔ ∀ o ∈ s, IsLimit o → ∃ a < o, Set.Ioo a o ⊆ s := by
  refine isOpen_iff_mem_nhds.trans <| forall₂_congr fun o ho => ?_
  by_cases ho' : IsLimit o
  · simp only [(nhdsBasis_Ioc ho'.1).mem_iff, ho', true_implies]
    refine exists_congr fun a => and_congr_right fun ha => ?_
    simp only [← Set.Ioo_insert_right ha, Set.insert_subset_iff, ho, true_and]
  · simp [nhds_eq_pure.2 ho', ho, ho']
#align ordinal.is_open_iff Ordinal.isOpen_iff

open List Set in
theorem mem_closure_tfae (a : Ordinal.{u}) (s : Set Ordinal) :
    TFAE [a ∈ closure s,
      a ∈ closure (s ∩ Iic a),
      (s ∩ Iic a).Nonempty ∧ sSup (s ∩ Iic a) = a,
      ∃ t, t ⊆ s ∧ t.Nonempty ∧ BddAbove t ∧ sSup t = a,
      ∃ (o : Ordinal.{u}), o ≠ 0 ∧ ∃ (f : ∀ x < o, Ordinal),
        (∀ x hx, f x hx ∈ s) ∧ bsup.{u, u} o f = a,
      ∃ (ι : Type u), Nonempty ι ∧ ∃ f : ι → Ordinal, (∀ i, f i ∈ s) ∧ sup.{u, u} f = a] := by
  tfae_have 1 → 2
  · simp only [mem_closure_iff_nhdsWithin_neBot, inter_comm s, nhdsWithin_inter', nhds_left_eq_nhds]
    exact id
  tfae_have 2 → 3
  · intro h
    rcases (s ∩ Iic a).eq_empty_or_nonempty with he | hne
    · simp [he] at h
    · refine ⟨hne, (isLUB_of_mem_closure ?_ h).csSup_eq hne⟩
      exact fun x hx => hx.2
  tfae_have 3 → 4
  · exact fun h => ⟨_, inter_subset_left, h.1, bddAbove_Iic.mono inter_subset_right, h.2⟩
  tfae_have 4 → 5
  · rintro ⟨t, hts, hne, hbdd, rfl⟩
    have hlub : IsLUB t (sSup t) := isLUB_csSup hne hbdd
    let ⟨y, hyt⟩ := hne
    classical
      refine ⟨succ (sSup t), succ_ne_zero _, fun x _ => if x ∈ t then x else y, fun x _ => ?_, ?_⟩
      · simp only
        split_ifs with h <;> exact hts ‹_›
      · refine le_antisymm (bsup_le fun x _ => ?_) (csSup_le hne fun x hx => ?_)
        · split_ifs <;> exact hlub.1 ‹_›
        · refine (if_pos hx).symm.trans_le (le_bsup _ _ <| (hlub.1 hx).trans_lt (lt_succ _))
  tfae_have 5 → 6
  · rintro ⟨o, h₀, f, hfs, rfl⟩
    exact ⟨_, out_nonempty_iff_ne_zero.2 h₀, familyOfBFamily o f, fun _ => hfs _ _, rfl⟩
  tfae_have 6 → 1
  · rintro ⟨ι, hne, f, hfs, rfl⟩
    rw [sup, iSup]
    exact closure_mono (range_subset_iff.2 hfs) <| csSup_mem_closure (range_nonempty f)
      (bddAbove_range.{u, u} f)
  tfae_finish

theorem mem_closure_iff_sup :
    a ∈ closure s ↔
      ∃ (ι : Type u) (_ : Nonempty ι) (f : ι → Ordinal), (∀ i, f i ∈ s) ∧ sup.{u, u} f = a :=
  ((mem_closure_tfae a s).out 0 5).trans <| by simp only [exists_prop]
#align ordinal.mem_closure_iff_sup Ordinal.mem_closure_iff_sup

theorem mem_closed_iff_sup (hs : IsClosed s) :
    a ∈ s ↔ ∃ (ι : Type u) (_hι : Nonempty ι) (f : ι → Ordinal),
      (∀ i, f i ∈ s) ∧ sup.{u, u} f = a := by
  rw [← mem_closure_iff_sup, hs.closure_eq]
#align ordinal.mem_closed_iff_sup Ordinal.mem_closed_iff_sup

theorem mem_closure_iff_bsup :
    a ∈ closure s ↔
      ∃ (o : Ordinal) (_ho : o ≠ 0) (f : ∀ a < o, Ordinal),
        (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a :=
  ((mem_closure_tfae a s).out 0 4).trans <| by simp only [exists_prop]
#align ordinal.mem_closure_iff_bsup Ordinal.mem_closure_iff_bsup

theorem mem_closed_iff_bsup (hs : IsClosed s) :
    a ∈ s ↔
      ∃ (o : Ordinal) (_ho : o ≠ 0) (f : ∀ a < o, Ordinal),
        (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a := by
  rw [← mem_closure_iff_bsup, hs.closure_eq]
#align ordinal.mem_closed_iff_bsup Ordinal.mem_closed_iff_bsup

theorem isClosed_iff_sup :
    IsClosed s ↔
      ∀ {ι : Type u}, Nonempty ι → ∀ f : ι → Ordinal, (∀ i, f i ∈ s) → sup.{u, u} f ∈ s := by
  use fun hs ι hι f hf => (mem_closed_iff_sup hs).2 ⟨ι, hι, f, hf, rfl⟩
  rw [← closure_subset_iff_isClosed]
  intro h x hx
  rcases mem_closure_iff_sup.1 hx with ⟨ι, hι, f, hf, rfl⟩
  exact h hι f hf
#align ordinal.is_closed_iff_sup Ordinal.isClosed_iff_sup

theorem isClosed_iff_bsup :
    IsClosed s ↔
      ∀ {o : Ordinal}, o ≠ 0 → ∀ f : ∀ a < o, Ordinal,
        (∀ i hi, f i hi ∈ s) → bsup.{u, u} o f ∈ s := by
  rw [isClosed_iff_sup]
  refine ⟨fun H o ho f hf => H (out_nonempty_iff_ne_zero.2 ho) _ ?_, fun H ι hι f hf => ?_⟩
  · exact fun i => hf _ _
  · rw [← bsup_eq_sup]
    apply H (type_ne_zero_iff_nonempty.2 hι)
    exact fun i hi => hf _
#align ordinal.is_closed_iff_bsup Ordinal.isClosed_iff_bsup

theorem isLimit_of_mem_frontier (ha : a ∈ frontier s) : IsLimit a := by
  simp only [frontier_eq_closure_inter_closure, Set.mem_inter_iff, mem_closure_iff] at ha
  by_contra h
  rw [← isOpen_singleton_iff] at h
  rcases ha.1 _ h rfl with ⟨b, hb, hb'⟩
  rcases ha.2 _ h rfl with ⟨c, hc, hc'⟩
  rw [Set.mem_singleton_iff] at *
  subst hb; subst hc
  exact hc' hb'
#align ordinal.is_limit_of_mem_frontier Ordinal.isLimit_of_mem_frontier

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
    rw [mem_closed_iff_sup (IsClosed.preimage h' (@isClosed_Iic _ _ _ _ a))]
    exact
      ⟨_, out_nonempty_iff_ne_zero.2 ho.1, typein (· < ·), fun i => h _ (typein_lt_self i),
        sup_typein_limit ho.2⟩
#align ordinal.is_normal_iff_strict_mono_and_continuous Ordinal.isNormal_iff_strictMono_and_continuous

theorem enumOrd_isNormal_iff_isClosed (hs : s.Unbounded (· < ·)) :
    IsNormal (enumOrd s) ↔ IsClosed s := by
  have Hs := enumOrd_strictMono hs
  refine
    ⟨fun h => isClosed_iff_sup.2 fun {ι} hι f hf => ?_, fun h =>
      (isNormal_iff_strictMono_limit _).2 ⟨Hs, fun a ha o H => ?_⟩⟩
  · let g : ι → Ordinal.{u} := fun i => (enumOrdOrderIso hs).symm ⟨_, hf i⟩
    suffices enumOrd s (sup.{u, u} g) = sup.{u, u} f by
      rw [← this]
      exact enumOrd_mem hs _
    rw [@IsNormal.sup.{u, u, u} _ h ι g hι]
    congr
    ext x
    change ((enumOrdOrderIso hs) _).val = f x
    rw [OrderIso.apply_symm_apply]
  · rw [isClosed_iff_bsup] at h
    suffices enumOrd s a ≤ bsup.{u, u} a fun b (_ : b < a) => enumOrd s b from
      this.trans (bsup_le H)
    cases' enumOrd_surjective hs _
        (h ha.1 (fun b _ => enumOrd s b) fun b _ => enumOrd_mem hs b) with
      b hb
    rw [← hb]
    apply Hs.monotone
    by_contra! hba
    apply (Hs (lt_succ b)).not_le
    rw [hb]
    exact le_bsup.{u, u} _ _ (ha.2 _ hba)
#align ordinal.enum_ord_is_normal_iff_is_closed Ordinal.enumOrd_isNormal_iff_isClosed

open Set Filter

/-- A positive ordinal is an accumulation point of a set of ordinals if there
are elements in the set arbitrarily close to the ordinal from below. -/
def IsAcc (o : Ordinal) (S : Set Ordinal) : Prop :=
  o ≠ 0 ∧ ∀ p < o, ∃ s ∈ S, p < s ∧ s < o

/-- A set of ordinals is closed in an ordinal if it contains all of
its accumulation points below the ordinal. -/
def IsClosed (S : Set Ordinal) (o : Ordinal) : Prop :=
  ∀ p < o, IsAcc p S → p ∈ S

theorem IsAcc.subset {o : Ordinal} {S T : Set Ordinal} (h : S ⊆ T) (ho : o.IsAcc S) :
    o.IsAcc T := ⟨ho.1, fun p plto ↦ (ho.2 p plto).casesOn fun s hs ↦ ⟨s, h hs.1, hs.2⟩⟩

theorem IsAcc.isLimit {o : Ordinal} {U : Set Ordinal} (h : o.IsAcc U) : IsLimit o := by
  refine' isLimit_of_not_succ_of_ne_zero (fun ⟨x, hx⟩ ↦ _) h.1
  rcases h.2 x (lt_of_lt_of_le (lt_succ x) hx.symm.le) with ⟨p, hp⟩
  exact (hx.symm ▸ (succ_le_iff.mpr hp.2.1)).not_lt hp.2.2

theorem IsAcc.inter_Ioo_nonempty {o : Ordinal} {U : Set Ordinal} (hU : o.IsAcc U)
    {p : Ordinal} (hp : p < o) : (U ∩ Ioo p o).Nonempty := by
  rcases hU.2 p hp with ⟨q, hq⟩
  exact ⟨q, hq.1, hq.2.1, hq.2.2⟩

theorem isClosed_zero (S : Set Ordinal) : IsClosed S 0 := fun _ h ↦
  False.elim <| (Ordinal.zero_le _).not_lt h

theorem isAcc_of_accPt {o p : Ordinal} (A : Set Ordinal) (hpos : p ≠ 0) (hp : p < o)
    (h : AccPt ⟨p, hp⟩ (𝓟 {x : Iio o | x.1 ∈ A})) : IsAcc p A := by
  use hpos
  rw [accPt_iff_nhds] at h
  intro q qltp
  by_cases h' : Order.succ p = o
  · let I : Set (Iio o) := Ioi ⟨q, qltp.trans hp⟩
    have Inh : I ∈ nhds ⟨p, hp⟩ := IsOpen.mem_nhds isOpen_Ioi qltp
    rcases h I Inh with ⟨r, ⟨rmemI, rmemA⟩, rnep⟩
    use r, rmemA, rmemI
    have : r ≤ p := Order.lt_succ_iff.mp (h' ▸ r.2)
    exact this.lt_or_eq.resolve_right <| Subtype.coe_ne_coe.mpr rnep
  · let I : Set (Iio o) := Ioo ⟨q, qltp.trans hp⟩ ⟨p + 1,
      (succ_le_of_lt hp).lt_or_eq.resolve_right h'⟩
    have Inh : I ∈ nhds ⟨p, hp⟩ := IsOpen.mem_nhds isOpen_Ioo ⟨qltp, lt_add_one p⟩
    rcases h I Inh with ⟨r, ⟨rmemI, rmemA⟩, rnep⟩
    use r, rmemA, rmemI.1
    have : r.1 ≤ p := lt_succ_iff.mp rmemI.2
    exact this.lt_or_eq.resolve_right <| Subtype.coe_ne_coe.mpr rnep

theorem accPt_of_isAcc {o p : Ordinal} (A : Set Ordinal) (hp : p < o)
    (h : IsAcc p A) : AccPt ⟨p, hp⟩ (𝓟 {x : Iio o | x.1 ∈ A}) := by
  rw [accPt_iff_nhds]
  intro u hu
  have lb := exists_Ioc_subset_of_mem_nhds hu ⟨⟨0, pos_of_gt' hp⟩,
    (Ordinal.zero_le p).lt_or_eq.resolve_right h.1.symm⟩
  rcases lb with ⟨a, pmem, hi⟩
  rcases h.2 a pmem with ⟨x, hx⟩
  use ⟨x, hx.2.2.trans hp⟩
  exact ⟨⟨hi ⟨hx.2.1, hx.2.2.le⟩, hx.1⟩, fun h ↦ hx.2.2.ne <| Subtype.mk_eq_mk.mp h⟩

theorem isAcc_iff_accPt {o p : Ordinal} (A : Set Ordinal) (hp : p < o) (hpos : p ≠ 0) :
    IsAcc p A ↔ AccPt ⟨p, hp⟩ (𝓟 {x : Iio o | x.1 ∈ A}) :=
  ⟨accPt_of_isAcc A hp, isAcc_of_accPt A hpos hp⟩

theorem not_accPt_zero {o : Ordinal} (ho : o ≠ 0) (S : Set (Iio o)) :
    ¬(AccPt ⟨0, Ordinal.pos_iff_ne_zero.mpr ho⟩ (𝓟 S)) := by
  intro h
  rw [accPt_iff_nhds] at h
  by_cases h' : 1 < o
  let I : Set (Iio o) := Iio ⟨1, h'⟩
  have : I ∈ nhds ⟨0, Ordinal.pos_iff_ne_zero.mpr ho⟩ :=
    IsOpen.mem_nhds isOpen_Iio (Ordinal.lt_one_iff_zero.mpr rfl)
  rcases h I this with ⟨x, ⟨hx, _⟩, xnz⟩
  exact xnz (SetCoe.ext (lt_one_iff_zero.mp hx))
  · have := (not_lt_iff_eq_or_lt.mp h').resolve_right fun h ↦
      ho <| Ordinal.lt_one_iff_zero.mp h
    rcases h Set.univ univ_mem with ⟨x, _, hx⟩
    exact hx <| SetCoe.ext <| Ordinal.lt_one_iff_zero.mp (this ▸ x.2)

theorem isClosed_iff {o : Ordinal} (A : Set Ordinal) :
    IsClosed A o ↔ _root_.IsClosed {x : Iio o | x.1 ∈ A} := by
  by_cases ho : o = 0
  · rw [ho, eq_true (isClosed_zero A)]
    have : {x : Iio o | x.1 ∈ A} = ∅ := by
      apply eq_empty_iff_forall_not_mem.mpr
      intro x
      have := x.2
      simp_rw [ho] at this
      cases (Ordinal.zero_le _).not_lt this
    have : _root_.IsClosed {x : Iio o | x.1 ∈ A} := by
      rw [this]
      exact isClosed_empty
    have := ho ▸ (eq_true this)
    rw [this]
  rw [isClosed_iff_clusterPt]
  constructor
  · intro h
    intro r hr
    change r.1 ∈ A
    match clusterPt_principal hr with
    | .inl h' => exact h'
    | .inr h' =>
      have rnz : r.1 ≠ 0 := fun h ↦ by
        have := not_accPt_zero ho {x : Iio o | x.1 ∈ A}
        simp_rw [← h] at this
        exact this h'
      have := (isAcc_iff_accPt A r.2 rnz)
      exact h r.1 r.2 (this.mpr h')
  · intro h p plto hp
    apply h ⟨p, plto⟩
    have := (isAcc_iff_accPt A plto hp.1).mp hp
    apply ((acc_iff_cluster (⟨p, plto⟩ : Iio o) _).mp this).mono inf_le_right

theorem IsClosed.sInter {o : Ordinal.{u}} {S : Set (Set Ordinal)} (h : ∀ C ∈ S, IsClosed C o) :
    IsClosed (⋂₀ S) o :=
  fun p plto pAcc C CmemS ↦ (h C CmemS) p plto (pAcc.subset (sInter_subset_of_mem CmemS))

theorem IsClosed.iInter {ι : Type u} {f : ι → Set Ordinal} {o : Ordinal.{u}}
    (h : ∀ i, IsClosed (f i) o) : IsClosed (⋂ i, f i) o := by
  have := IsClosed.sInter (fun C (⟨i, fieqC⟩ : C ∈ range f) ↦ fieqC ▸ (h i))
  change IsClosed (⋂₀ (range f)) o at this
  rwa [sInter_range] at this

end Ordinal
