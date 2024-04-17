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
  refine' ⟨fun h ⟨h₀, hsucc⟩ => _, fun ha => _⟩
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
  · exact fun h => ⟨_, inter_subset_left _ _, h.1, bddAbove_Iic.mono (inter_subset_right _ _), h.2⟩
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
        · exact (if_pos hx).symm.trans_le (le_bsup _ _ <| (hlub.1 hx).trans_lt (lt_succ _))
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
      (∀ i, f i ∈ s) ∧ sup.{u, u} f = a :=
  by rw [← mem_closure_iff_sup, hs.closure_eq]
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
        (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a :=
  by rw [← mem_closure_iff_bsup, hs.closure_eq]
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
  refine' ⟨fun H o ho f hf => H (out_nonempty_iff_ne_zero.2 ho) _ _, fun H ι hι f hf => _⟩
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
  refine' ⟨fun h => ⟨h.strictMono, _⟩, _⟩
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
    refine' ⟨h, fun o ho a h => _⟩
    suffices o ∈ f ⁻¹' Set.Iic a from Set.mem_preimage.1 this
    rw [mem_closed_iff_sup (IsClosed.preimage h' (@isClosed_Iic _ _ _ _ a))]
    exact
      ⟨_, out_nonempty_iff_ne_zero.2 ho.1, typein (· < ·), fun i => h _ (typein_lt_self i),
        sup_typein_limit ho.2⟩
#align ordinal.is_normal_iff_strict_mono_and_continuous Ordinal.isNormal_iff_strictMono_and_continuous

theorem enumOrd_isNormal_iff_isClosed (hs : s.Unbounded (· < ·)) :
    IsNormal (enumOrd s) ↔ IsClosed s := by
  have Hs := enumOrd_strictMono hs
  refine'
    ⟨fun h => isClosed_iff_sup.2 fun {ι} hι f hf => _, fun h =>
      (isNormal_iff_strictMono_limit _).2 ⟨Hs, fun a ha o H => _⟩⟩
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

end Ordinal
