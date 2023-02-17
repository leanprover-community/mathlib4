/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios

! This file was ported from Lean 3 source module set_theory.ordinal.topology
! leanprover-community/mathlib commit 740acc0e6f9adf4423f92a485d0456fc271482da
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.SetTheory.Ordinal.Arithmetic
import Mathbin.Topology.Order.Basic

/-!
### Topology of ordinals

We prove some miscellaneous results involving the order topology of ordinals.

### Main results

* `ordinal.is_closed_iff_sup` / `ordinal.is_closed_iff_bsup`: A set of ordinals is closed iff it's
  closed under suprema.
* `ordinal.is_normal_iff_strict_mono_and_continuous`: A characterization of normal ordinal
  functions.
* `ordinal.enum_ord_is_normal_iff_is_closed`: The function enumerating the ordinals of a set is
  normal iff the set is closed.
-/


noncomputable section

universe u v

open Cardinal Order

namespace Ordinal

variable {s : Set Ordinal.{u}} {a : Ordinal.{u}}

instance : TopologicalSpace Ordinal.{u} :=
  Preorder.topology Ordinal.{u}

instance : OrderTopology Ordinal.{u} :=
  ⟨rfl⟩

theorem isOpen_singleton_iff : IsOpen ({a} : Set Ordinal) ↔ ¬IsLimit a :=
  by
  refine' ⟨fun h ha => _, fun ha => _⟩
  · obtain ⟨b, c, hbc, hbc'⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨0, Ordinal.pos_iff_ne_zero.2 ha.1⟩ ⟨_, lt_succ a⟩).1
        (h.mem_nhds rfl)
    have hba := ha.2 b hbc.1
    exact hba.ne (hbc' ⟨lt_succ b, hba.trans hbc.2⟩)
  · rcases zero_or_succ_or_limit a with (rfl | ⟨b, hb⟩ | ha')
    · convert isOpen_gt' (1 : Ordinal)
      ext
      exact ordinal.lt_one_iff_zero.symm
    · convert @isOpen_Ioo _ _ _ _ b (a + 1)
      ext c
      refine' ⟨fun hc => _, _⟩
      · rw [Set.mem_singleton_iff.1 hc]
        refine' ⟨_, lt_succ a⟩
        rw [hb]
        exact lt_succ b
      · rintro ⟨hc, hc'⟩
        apply le_antisymm (le_of_lt_succ hc')
        rw [hb]
        exact succ_le_of_lt hc
    · exact (ha ha').elim
#align ordinal.is_open_singleton_iff Ordinal.isOpen_singleton_iff

theorem isOpen_iff : IsOpen s ↔ ∀ o ∈ s, IsLimit o → ∃ a < o, Set.Ioo a o ⊆ s := by
  classical
    refine' ⟨_, fun h => _⟩
    · rw [isOpen_iff_generate_intervals]
      intro h o hos ho
      have ho₀ := Ordinal.pos_iff_ne_zero.2 ho.1
      induction' h with t ht t u ht hu ht' hu' t ht H
      · rcases ht with ⟨a, rfl | rfl⟩
        · exact ⟨a, hos, fun b hb => hb.1⟩
        · exact ⟨0, ho₀, fun b hb => hb.2.trans hos⟩
      · exact ⟨0, ho₀, fun b _ => Set.mem_univ b⟩
      · rcases ht' hos.1 with ⟨a, ha, ha'⟩
        rcases hu' hos.2 with ⟨b, hb, hb'⟩
        exact
          ⟨_, max_lt ha hb, fun c hc =>
            ⟨ha' ⟨(le_max_left a b).trans_lt hc.1, hc.2⟩,
              hb' ⟨(le_max_right a b).trans_lt hc.1, hc.2⟩⟩⟩
      · rcases hos with ⟨u, hu, hu'⟩
        rcases H u hu hu' with ⟨a, ha, ha'⟩
        exact ⟨a, ha, fun b hb => ⟨u, hu, ha' hb⟩⟩
    · let f : s → Set Ordinal := fun o =>
        if ho : is_limit o.val then Set.Ioo (Classical.choose (h o.val o.Prop ho)) (o + 1)
        else {o.val}
      have : ∀ a, IsOpen (f a) := fun a =>
        by
        change IsOpen (dite _ _ _)
        split_ifs
        · exact isOpen_Ioo
        · rwa [is_open_singleton_iff]
      convert isOpen_unionᵢ this
      ext o
      refine' ⟨fun ho => Set.mem_unionᵢ.2 ⟨⟨o, ho⟩, _⟩, _⟩
      · split_ifs with ho'
        · refine' ⟨_, lt_succ o⟩
          cases' Classical.choose_spec (h o ho ho') with H
          exact H
        · exact Set.mem_singleton o
      · rintro ⟨t, ⟨a, ht⟩, hoa⟩
        change dite _ _ _ = t at ht
        split_ifs  at ht with ha <;> subst ht
        · cases' Classical.choose_spec (h a.val a.prop ha) with H has
          rcases lt_or_eq_of_le (le_of_lt_succ hoa.2) with (hoa' | rfl)
          · exact has ⟨hoa.1, hoa'⟩
          · exact a.prop
        · convert a.prop
#align ordinal.is_open_iff Ordinal.isOpen_iff

theorem mem_closure_iff_sup :
    a ∈ closure s ↔
      ∃ (ι : Type u)(_ : Nonempty ι)(f : ι → Ordinal), (∀ i, f i ∈ s) ∧ sup.{u, u} f = a :=
  by
  refine' mem_closure_iff.trans ⟨fun h => _, _⟩
  · by_cases has : a ∈ s
    · exact ⟨PUnit, by infer_instance, fun _ => a, fun _ => has, sup_const a⟩
    · have H := fun b (hba : b < a) => h _ (@isOpen_Ioo _ _ _ _ b (a + 1)) ⟨hba, lt_succ a⟩
      let f : a.out.α → Ordinal := fun i =>
        Classical.choose (H (typein (· < ·) i) (typein_lt_self i))
      have hf : ∀ i, f i ∈ Set.Ioo (typein (· < ·) i) (a + 1) ∩ s := fun i =>
        Classical.choose_spec (H _ _)
      rcases eq_zero_or_pos a with (rfl | ha₀)
      · rcases h _ (is_open_singleton_iff.2 not_zero_is_limit) rfl with ⟨b, hb, hb'⟩
        rw [Set.mem_singleton_iff.1 hb] at *
        exact (has hb').elim
      refine'
        ⟨_, out_nonempty_iff_ne_zero.2 (Ordinal.pos_iff_ne_zero.1 ha₀), f, fun i => (hf i).2,
          le_antisymm (sup_le fun i => le_of_lt_succ (hf i).1.2) _⟩
      by_contra' h
      cases' H _ h with b hb
      rcases eq_or_lt_of_le (le_of_lt_succ hb.1.2) with (rfl | hba)
      · exact has hb.2
      · have : b < f (enum (· < ·) b (by rwa [type_lt])) :=
          by
          have := (hf (enum (· < ·) b (by rwa [type_lt]))).1.1
          rwa [typein_enum] at this
        have : b ≤ sup.{u, u} f := this.le.trans (le_sup f _)
        exact this.not_lt hb.1.1
  · rintro ⟨ι, ⟨i⟩, f, hf, rfl⟩ t ht hat
    cases' eq_zero_or_pos (sup.{u, u} f) with ha₀ ha₀
    · rw [ha₀] at hat
      use 0, hat
      convert hf i
      exact (sup_eq_zero_iff.1 ha₀ i).symm
    rcases(mem_nhds_iff_exists_Ioo_subset' ⟨0, ha₀⟩ ⟨_, lt_succ _⟩).1 (ht.mem_nhds hat) with
      ⟨b, c, ⟨hab, hac⟩, hbct⟩
    cases' lt_sup.1 hab with i hi
    exact ⟨_, hbct ⟨hi, (le_sup.{u, u} f i).trans_lt hac⟩, hf i⟩
#align ordinal.mem_closure_iff_sup Ordinal.mem_closure_iff_sup

theorem mem_closed_iff_sup (hs : IsClosed s) :
    a ∈ s ↔ ∃ (ι : Type u)(hι : Nonempty ι)(f : ι → Ordinal), (∀ i, f i ∈ s) ∧ sup.{u, u} f = a :=
  by rw [← mem_closure_iff_sup, hs.closure_eq]
#align ordinal.mem_closed_iff_sup Ordinal.mem_closed_iff_sup

theorem mem_closure_iff_bsup :
    a ∈ closure s ↔
      ∃ (o : Ordinal)(ho : o ≠ 0)(f : ∀ a < o, Ordinal),
        (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a :=
  mem_closure_iff_sup.trans
    ⟨fun ⟨ι, ⟨i⟩, f, hf, ha⟩ =>
      ⟨_, fun h => (type_eq_zero_iff_isEmpty.1 h).elim i, bfamilyOfFamily f, fun i hi => hf _, by
        rwa [bsup_eq_sup]⟩,
      fun ⟨o, ho, f, hf, ha⟩ =>
      ⟨_, out_nonempty_iff_ne_zero.2 ho, familyOfBFamily o f, fun i => hf _ _, by
        rwa [sup_eq_bsup]⟩⟩
#align ordinal.mem_closure_iff_bsup Ordinal.mem_closure_iff_bsup

theorem mem_closed_iff_bsup (hs : IsClosed s) :
    a ∈ s ↔
      ∃ (o : Ordinal)(ho : o ≠ 0)(f : ∀ a < o, Ordinal),
        (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a :=
  by rw [← mem_closure_iff_bsup, hs.closure_eq]
#align ordinal.mem_closed_iff_bsup Ordinal.mem_closed_iff_bsup

theorem isClosed_iff_sup :
    IsClosed s ↔
      ∀ {ι : Type u} (hι : Nonempty ι) (f : ι → Ordinal), (∀ i, f i ∈ s) → sup.{u, u} f ∈ s :=
  by
  use fun hs ι hι f hf => (mem_closed_iff_sup hs).2 ⟨ι, hι, f, hf, rfl⟩
  rw [← closure_subset_iff_isClosed]
  intro h x hx
  rcases mem_closure_iff_sup.1 hx with ⟨ι, hι, f, hf, rfl⟩
  exact h hι f hf
#align ordinal.is_closed_iff_sup Ordinal.isClosed_iff_sup

theorem isClosed_iff_bsup :
    IsClosed s ↔
      ∀ {o : Ordinal} (ho : o ≠ 0) (f : ∀ a < o, Ordinal),
        (∀ i hi, f i hi ∈ s) → bsup.{u, u} o f ∈ s :=
  by
  rw [is_closed_iff_sup]
  refine' ⟨fun H o ho f hf => H (out_nonempty_iff_ne_zero.2 ho) _ _, fun H ι hι f hf => _⟩
  · exact fun i => hf _ _
  · rw [← bsup_eq_sup]
    apply H (type_ne_zero_iff_nonempty.2 hι)
    exact fun i hi => hf _
#align ordinal.is_closed_iff_bsup Ordinal.isClosed_iff_bsup

theorem isLimit_of_mem_frontier (ha : a ∈ frontier s) : IsLimit a :=
  by
  simp only [frontier_eq_closure_inter_closure, Set.mem_inter_iff, mem_closure_iff] at ha
  by_contra h
  rw [← is_open_singleton_iff] at h
  rcases ha.1 _ h rfl with ⟨b, hb, hb'⟩
  rcases ha.2 _ h rfl with ⟨c, hc, hc'⟩
  rw [Set.mem_singleton_iff] at *
  subst hb; subst hc
  exact hc' hb'
#align ordinal.is_limit_of_mem_frontier Ordinal.isLimit_of_mem_frontier

theorem isNormal_iff_strictMono_and_continuous (f : Ordinal.{u} → Ordinal.{u}) :
    IsNormal f ↔ StrictMono f ∧ Continuous f :=
  by
  refine' ⟨fun h => ⟨h.StrictMono, _⟩, _⟩
  · rw [continuous_def]
    intro s hs
    rw [is_open_iff] at *
    intro o ho ho'
    rcases hs _ ho (h.is_limit ho') with ⟨a, ha, has⟩
    rw [← IsNormal.bsup_eq.{u, u} h ho', lt_bsup] at ha
    rcases ha with ⟨b, hb, hab⟩
    exact
      ⟨b, hb, fun c hc =>
        Set.mem_preimage.2 (has ⟨hab.trans (h.strict_mono hc.1), h.strict_mono hc.2⟩)⟩
  · rw [is_normal_iff_strict_mono_limit]
    rintro ⟨h, h'⟩
    refine' ⟨h, fun o ho a h => _⟩
    suffices : o ∈ f ⁻¹' Set.Iic a
    exact Set.mem_preimage.1 this
    rw [mem_closed_iff_sup (IsClosed.preimage h' (@isClosed_Iic _ _ _ _ a))]
    exact
      ⟨_, out_nonempty_iff_ne_zero.2 ho.1, typein (· < ·), fun i => h _ (typein_lt_self i),
        sup_typein_limit ho.2⟩
#align ordinal.is_normal_iff_strict_mono_and_continuous Ordinal.isNormal_iff_strictMono_and_continuous

/- ./././Mathport/Syntax/Translate/Basic.lean:628:2: warning: expanding binder collection (b «expr < » a) -/
theorem enumOrd_isNormal_iff_isClosed (hs : s.Unbounded (· < ·)) :
    IsNormal (enumOrd s) ↔ IsClosed s :=
  by
  have Hs := enum_ord_strict_mono hs
  refine'
    ⟨fun h => is_closed_iff_sup.2 fun ι hι f hf => _, fun h =>
      (is_normal_iff_strict_mono_limit _).2 ⟨Hs, fun a ha o H => _⟩⟩
  · let g : ι → Ordinal.{u} := fun i => (enum_ord_order_iso hs).symm ⟨_, hf i⟩
    suffices enum_ord s (sup.{u, u} g) = sup.{u, u} f
      by
      rw [← this]
      exact enum_ord_mem hs _
    rw [@IsNormal.sup.{u, u, u} _ h ι g hι]
    congr
    ext
    change ((enum_ord_order_iso hs) _).val = f x
    rw [OrderIso.apply_symm_apply]
  · rw [is_closed_iff_bsup] at h
    suffices : enum_ord s a ≤ bsup.{u, u} a fun b (_ : b < a) => enum_ord s b
    exact this.trans (bsup_le H)
    cases'
      enum_ord_surjective hs _
        (h ha.1 (fun b hb => enum_ord s b) fun b hb => enum_ord_mem hs b) with
      b hb
    rw [← hb]
    apply Hs.monotone
    by_contra' hba
    apply (Hs (lt_succ b)).not_le
    rw [hb]
    exact le_bsup.{u, u} _ _ (ha.2 _ hba)
#align ordinal.enum_ord_is_normal_iff_is_closed Ordinal.enumOrd_isNormal_iff_isClosed

end Ordinal

