/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Tactic.TFAE
import Mathlib.Topology.Order.Basic

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
  -- ⊢ False
  · obtain ⟨b, c, hbc, hbc'⟩ :=
      (mem_nhds_iff_exists_Ioo_subset' ⟨0, Ordinal.pos_iff_ne_zero.2 h₀⟩ ⟨_, lt_succ a⟩).1
        (h.mem_nhds rfl)
    have hba := hsucc b hbc.1
    -- ⊢ False
    exact hba.ne (hbc' ⟨lt_succ b, hba.trans hbc.2⟩)
    -- 🎉 no goals
  · rcases zero_or_succ_or_limit a with (rfl | ⟨b, rfl⟩ | ha')
    · rw [← bot_eq_zero, ← Set.Iic_bot, ← Iio_succ]
      -- ⊢ IsOpen (Set.Iio (succ ⊥))
      exact isOpen_Iio
      -- 🎉 no goals
    · rw [← Set.Icc_self, Icc_succ_left, ← Ioo_succ_right]
      -- ⊢ IsOpen (Set.Ioo b (succ (succ b)))
      exact isOpen_Ioo
      -- 🎉 no goals
    · exact (ha ha').elim
      -- 🎉 no goals
#align ordinal.is_open_singleton_iff Ordinal.isOpen_singleton_iff

-- porting note: todo: generalize to a `SuccOrder`
theorem nhds_right' (a : Ordinal) : 𝓝[>] a = ⊥ := (covby_succ a).nhdsWithin_Ioi

-- todo: generalize to a `SuccOrder`
theorem nhds_left'_eq_nhds_ne (a : Ordinal) : 𝓝[<] a = 𝓝[≠] a := by
  rw [← nhds_left'_sup_nhds_right', nhds_right', sup_bot_eq]
  -- 🎉 no goals

-- todo: generalize to a `SuccOrder`
theorem nhds_left_eq_nhds (a : Ordinal) : 𝓝[≤] a = 𝓝 a := by
  rw [← nhds_left_sup_nhds_right', nhds_right', sup_bot_eq]
  -- 🎉 no goals

-- todo: generalize to a `SuccOrder`
theorem nhdsBasis_Ioc (h : a ≠ 0) : (𝓝 a).HasBasis (· < a) (Set.Ioc · a) :=
  nhds_left_eq_nhds a ▸ nhdsWithin_Iic_basis' ⟨0, h.bot_lt⟩

-- todo: generalize to a `SuccOrder`
theorem nhds_eq_pure : 𝓝 a = pure a ↔ ¬IsLimit a :=
  (isOpen_singleton_iff_nhds_eq_pure _).symm.trans isOpen_singleton_iff

-- todo: generalize `Ordinal.IsLimit` and this lemma to a `SuccOrder`
theorem isOpen_iff : IsOpen s ↔ ∀ o ∈ s, IsLimit o → ∃ a < o, Set.Ioo a o ⊆ s := by
  refine isOpen_iff_mem_nhds.trans <| forall₂_congr fun o ho => ?_
  -- ⊢ s ∈ 𝓝 o ↔ IsLimit o → ∃ a, a < o ∧ Set.Ioo a o ⊆ s
  by_cases ho' : IsLimit o
  -- ⊢ s ∈ 𝓝 o ↔ IsLimit o → ∃ a, a < o ∧ Set.Ioo a o ⊆ s
  · simp only [(nhdsBasis_Ioc ho'.1).mem_iff, ho', true_implies]
    -- ⊢ (∃ i, i < o ∧ Set.Ioc i o ⊆ s) ↔ ∃ a, a < o ∧ Set.Ioo a o ⊆ s
    refine exists_congr fun a => and_congr_right fun ha => ?_
    -- ⊢ Set.Ioc a o ⊆ s ↔ Set.Ioo a o ⊆ s
    simp only [← Set.Ioo_insert_right ha, Set.insert_subset_iff, ho, true_and]
    -- 🎉 no goals
  · simp [nhds_eq_pure.2 ho', ho, ho']
    -- 🎉 no goals
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
  -- ⊢ a ∈ closure s → a ∈ closure (s ∩ Iic a)
  · simp only [mem_closure_iff_nhdsWithin_neBot, inter_comm s, nhdsWithin_inter', nhds_left_eq_nhds]
    -- ⊢ Filter.NeBot (𝓝[s] a) → Filter.NeBot (𝓝 a ⊓ Filter.principal s)
    exact id
    -- 🎉 no goals
  tfae_have 2 → 3
  -- ⊢ a ∈ closure (s ∩ Iic a) → Set.Nonempty (s ∩ Iic a) ∧ sSup (s ∩ Iic a) = a
  · intro h
    -- ⊢ Set.Nonempty (s ∩ Iic a) ∧ sSup (s ∩ Iic a) = a
    cases' (s ∩ Iic a).eq_empty_or_nonempty with he hne
    -- ⊢ Set.Nonempty (s ∩ Iic a) ∧ sSup (s ∩ Iic a) = a
    · simp [he] at h
      -- 🎉 no goals
    · refine ⟨hne, (isLUB_of_mem_closure ?_ h).csSup_eq hne⟩
      -- ⊢ a ∈ upperBounds (s ∩ Iic a)
      exact fun x hx => hx.2
      -- 🎉 no goals
  tfae_have 3 → 4
  -- ⊢ Set.Nonempty (s ∩ Iic a) ∧ sSup (s ∩ Iic a) = a → ∃ t, t ⊆ s ∧ Set.Nonempty  …
  · exact fun h => ⟨_, inter_subset_left _ _, h.1, bddAbove_Iic.mono (inter_subset_right _ _), h.2⟩
    -- 🎉 no goals
  tfae_have 4 → 5
  -- ⊢ (∃ t, t ⊆ s ∧ Set.Nonempty t ∧ BddAbove t ∧ sSup t = a) → ∃ o, o ≠ 0 ∧ ∃ f,  …
  · rintro ⟨t, hts, hne, hbdd, rfl⟩
    -- ⊢ ∃ o, o ≠ 0 ∧ ∃ f, (∀ (x : Ordinal.{u}) (hx : x < o), f x hx ∈ s) ∧ bsup o f  …
    have hlub : IsLUB t (sSup t) := isLUB_csSup hne hbdd
    -- ⊢ ∃ o, o ≠ 0 ∧ ∃ f, (∀ (x : Ordinal.{u}) (hx : x < o), f x hx ∈ s) ∧ bsup o f  …
    let ⟨y, hyt⟩ := hne
    -- ⊢ ∃ o, o ≠ 0 ∧ ∃ f, (∀ (x : Ordinal.{u}) (hx : x < o), f x hx ∈ s) ∧ bsup o f  …
    classical
      refine ⟨succ (sSup t), succ_ne_zero _, fun x _ => if x ∈ t then x else y, fun x _ => ?_, ?_⟩
      · simp only
        split_ifs with h <;> exact hts ‹_›
      · refine le_antisymm (bsup_le fun x _ => ?_) (csSup_le hne fun x hx => ?_)
        · split_ifs <;> exact hlub.1 ‹_›
        · refine (if_pos hx).symm.trans_le (le_bsup _ _ <| (hlub.1 hx).trans_lt (lt_succ _))
  tfae_have 5 → 6
  -- ⊢ (∃ o, o ≠ 0 ∧ ∃ f, (∀ (x : Ordinal.{u}) (hx : x < o), f x hx ∈ s) ∧ bsup o f …
  · rintro ⟨o, h₀, f, hfs, rfl⟩
    -- ⊢ ∃ ι, Nonempty ι ∧ ∃ f_1, (∀ (i : ι), f_1 i ∈ s) ∧ sup f_1 = bsup o f
    exact ⟨_, out_nonempty_iff_ne_zero.2 h₀, familyOfBFamily o f, fun _ => hfs _ _, rfl⟩
    -- 🎉 no goals
  tfae_have 6 → 1
  -- ⊢ (∃ ι, Nonempty ι ∧ ∃ f, (∀ (i : ι), f i ∈ s) ∧ sup f = a) → a ∈ closure s
  · rintro ⟨ι, hne, f, hfs, rfl⟩
    -- ⊢ sup f ∈ closure s
    rw [sup, iSup]
    -- ⊢ sSup (Set.range f) ∈ closure s
    exact closure_mono (range_subset_iff.2 hfs) <| csSup_mem_closure (range_nonempty f)
      (bddAbove_range.{u, u} f)
  tfae_finish
  -- 🎉 no goals

theorem mem_closure_iff_sup :
    a ∈ closure s ↔
      ∃ (ι : Type u) (_ : Nonempty ι) (f : ι → Ordinal), (∀ i, f i ∈ s) ∧ sup.{u, u} f = a :=
  ((mem_closure_tfae a s).out 0 5).trans <| by simp only [exists_prop]
                                               -- 🎉 no goals
#align ordinal.mem_closure_iff_sup Ordinal.mem_closure_iff_sup

theorem mem_closed_iff_sup (hs : IsClosed s) :
    a ∈ s ↔ ∃ (ι : Type u) (_hι : Nonempty ι) (f : ι → Ordinal),
      (∀ i, f i ∈ s) ∧ sup.{u, u} f = a :=
  by rw [← mem_closure_iff_sup, hs.closure_eq]
     -- 🎉 no goals
#align ordinal.mem_closed_iff_sup Ordinal.mem_closed_iff_sup

theorem mem_closure_iff_bsup :
    a ∈ closure s ↔
      ∃ (o : Ordinal) (_ho : o ≠ 0) (f : ∀ a < o, Ordinal),
        (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a :=
  ((mem_closure_tfae a s).out 0 4).trans <| by simp only [exists_prop]
                                               -- 🎉 no goals
#align ordinal.mem_closure_iff_bsup Ordinal.mem_closure_iff_bsup

theorem mem_closed_iff_bsup (hs : IsClosed s) :
    a ∈ s ↔
      ∃ (o : Ordinal) (_ho : o ≠ 0) (f : ∀ a < o, Ordinal),
        (∀ i hi, f i hi ∈ s) ∧ bsup.{u, u} o f = a :=
  by rw [← mem_closure_iff_bsup, hs.closure_eq]
     -- 🎉 no goals
#align ordinal.mem_closed_iff_bsup Ordinal.mem_closed_iff_bsup

theorem isClosed_iff_sup :
    IsClosed s ↔
      ∀ {ι : Type u}, Nonempty ι → ∀ f : ι → Ordinal, (∀ i, f i ∈ s) → sup.{u, u} f ∈ s := by
  use fun hs ι hι f hf => (mem_closed_iff_sup hs).2 ⟨ι, hι, f, hf, rfl⟩
  -- ⊢ (∀ {ι : Type u}, Nonempty ι → ∀ (f : ι → Ordinal.{u}), (∀ (i : ι), f i ∈ s)  …
  rw [← closure_subset_iff_isClosed]
  -- ⊢ (∀ {ι : Type u}, Nonempty ι → ∀ (f : ι → Ordinal.{u}), (∀ (i : ι), f i ∈ s)  …
  intro h x hx
  -- ⊢ x ∈ s
  rcases mem_closure_iff_sup.1 hx with ⟨ι, hι, f, hf, rfl⟩
  -- ⊢ sup f ∈ s
  exact h hι f hf
  -- 🎉 no goals
#align ordinal.is_closed_iff_sup Ordinal.isClosed_iff_sup

theorem isClosed_iff_bsup :
    IsClosed s ↔
      ∀ {o : Ordinal}, o ≠ 0 → ∀ f : ∀ a < o, Ordinal,
        (∀ i hi, f i hi ∈ s) → bsup.{u, u} o f ∈ s := by
  rw [isClosed_iff_sup]
  -- ⊢ (∀ {ι : Type u}, Nonempty ι → ∀ (f : ι → Ordinal.{u}), (∀ (i : ι), f i ∈ s)  …
  refine' ⟨fun H o ho f hf => H (out_nonempty_iff_ne_zero.2 ho) _ _, fun H ι hι f hf => _⟩
  -- ⊢ ∀ (i : (Quotient.out o).α), familyOfBFamily o f i ∈ s
  · exact fun i => hf _ _
    -- 🎉 no goals
  · rw [← bsup_eq_sup]
    -- ⊢ bsup (type WellOrderingRel) (bfamilyOfFamily f) ∈ s
    apply H (type_ne_zero_iff_nonempty.2 hι)
    -- ⊢ ∀ (i : Ordinal.{u}) (hi : i < type WellOrderingRel), bfamilyOfFamily f i hi  …
    exact fun i hi => hf _
    -- 🎉 no goals
#align ordinal.is_closed_iff_bsup Ordinal.isClosed_iff_bsup

theorem isLimit_of_mem_frontier (ha : a ∈ frontier s) : IsLimit a := by
  simp only [frontier_eq_closure_inter_closure, Set.mem_inter_iff, mem_closure_iff] at ha
  -- ⊢ IsLimit a
  by_contra h
  -- ⊢ False
  rw [← isOpen_singleton_iff] at h
  -- ⊢ False
  rcases ha.1 _ h rfl with ⟨b, hb, hb'⟩
  -- ⊢ False
  rcases ha.2 _ h rfl with ⟨c, hc, hc'⟩
  -- ⊢ False
  rw [Set.mem_singleton_iff] at *
  -- ⊢ False
  subst hb; subst hc
  -- ⊢ False
            -- ⊢ False
  exact hc' hb'
  -- 🎉 no goals
#align ordinal.is_limit_of_mem_frontier Ordinal.isLimit_of_mem_frontier

theorem isNormal_iff_strictMono_and_continuous (f : Ordinal.{u} → Ordinal.{u}) :
    IsNormal f ↔ StrictMono f ∧ Continuous f := by
  refine' ⟨fun h => ⟨h.strictMono, _⟩, _⟩
  -- ⊢ Continuous f
  · rw [continuous_def]
    -- ⊢ ∀ (s : Set Ordinal.{u}), IsOpen s → IsOpen (f ⁻¹' s)
    intro s hs
    -- ⊢ IsOpen (f ⁻¹' s)
    rw [isOpen_iff] at *
    -- ⊢ ∀ (o : Ordinal.{u}), o ∈ f ⁻¹' s → IsLimit o → ∃ a, a < o ∧ Set.Ioo a o ⊆ f  …
    intro o ho ho'
    -- ⊢ ∃ a, a < o ∧ Set.Ioo a o ⊆ f ⁻¹' s
    rcases hs _ ho (h.isLimit ho') with ⟨a, ha, has⟩
    -- ⊢ ∃ a, a < o ∧ Set.Ioo a o ⊆ f ⁻¹' s
    rw [← IsNormal.bsup_eq.{u, u} h ho', lt_bsup] at ha
    -- ⊢ ∃ a, a < o ∧ Set.Ioo a o ⊆ f ⁻¹' s
    rcases ha with ⟨b, hb, hab⟩
    -- ⊢ ∃ a, a < o ∧ Set.Ioo a o ⊆ f ⁻¹' s
    exact
      ⟨b, hb, fun c hc =>
        Set.mem_preimage.2 (has ⟨hab.trans (h.strictMono hc.1), h.strictMono hc.2⟩)⟩
  · rw [isNormal_iff_strictMono_limit]
    -- ⊢ StrictMono f ∧ Continuous f → StrictMono f ∧ ∀ (o : Ordinal.{u}), IsLimit o  …
    rintro ⟨h, h'⟩
    -- ⊢ StrictMono f ∧ ∀ (o : Ordinal.{u}), IsLimit o → ∀ (a : Ordinal.{u}), (∀ (b : …
    refine' ⟨h, fun o ho a h => _⟩
    -- ⊢ f o ≤ a
    suffices : o ∈ f ⁻¹' Set.Iic a
    -- ⊢ f o ≤ a
    exact Set.mem_preimage.1 this
    -- ⊢ o ∈ f ⁻¹' Set.Iic a
    rw [mem_closed_iff_sup (IsClosed.preimage h' (@isClosed_Iic _ _ _ _ a))]
    -- ⊢ ∃ ι _hι f_1, (∀ (i : ι), f_1 i ∈ f ⁻¹' Set.Iic a) ∧ sup f_1 = o
    exact
      ⟨_, out_nonempty_iff_ne_zero.2 ho.1, typein (· < ·), fun i => h _ (typein_lt_self i),
        sup_typein_limit ho.2⟩
#align ordinal.is_normal_iff_strict_mono_and_continuous Ordinal.isNormal_iff_strictMono_and_continuous

theorem enumOrd_isNormal_iff_isClosed (hs : s.Unbounded (· < ·)) :
    IsNormal (enumOrd s) ↔ IsClosed s := by
  have Hs := enumOrd_strictMono hs
  -- ⊢ IsNormal (enumOrd s) ↔ IsClosed s
  refine'
    ⟨fun h => isClosed_iff_sup.2 fun {ι} hι f hf => _, fun h =>
      (isNormal_iff_strictMono_limit _).2 ⟨Hs, fun a ha o H => _⟩⟩
  · let g : ι → Ordinal.{u} := fun i => (enumOrdOrderIso hs).symm ⟨_, hf i⟩
    -- ⊢ sup f ∈ s
    suffices enumOrd s (sup.{u, u} g) = sup.{u, u} f by
      rw [← this]
      exact enumOrd_mem hs _
    rw [@IsNormal.sup.{u, u, u} _ h ι g hι]
    -- ⊢ sup (enumOrd s ∘ g) = sup f
    congr
    -- ⊢ enumOrd s ∘ g = f
    ext x
    -- ⊢ (enumOrd s ∘ g) x = f x
    change ((enumOrdOrderIso hs) _).val = f x
    -- ⊢ ↑(↑(enumOrdOrderIso hs) (g x)) = f x
    rw [OrderIso.apply_symm_apply]
    -- 🎉 no goals
  · rw [isClosed_iff_bsup] at h
    -- ⊢ enumOrd s a ≤ o
    suffices : enumOrd s a ≤ bsup.{u, u} a fun b (_ : b < a) => enumOrd s b
    -- ⊢ enumOrd s a ≤ o
    exact this.trans (bsup_le H)
    -- ⊢ enumOrd s a ≤ bsup a fun b x => enumOrd s b
    cases' enumOrd_surjective hs _
        (h ha.1 (fun b _ => enumOrd s b) fun b _ => enumOrd_mem hs b) with
      b hb
    rw [← hb]
    -- ⊢ enumOrd s a ≤ enumOrd s b
    apply Hs.monotone
    -- ⊢ a ≤ b
    by_contra' hba
    -- ⊢ False
    apply (Hs (lt_succ b)).not_le
    -- ⊢ enumOrd s (succ b) ≤ enumOrd s b
    rw [hb]
    -- ⊢ enumOrd s (succ b) ≤ bsup a fun b x => enumOrd s b
    exact le_bsup.{u, u} _ _ (ha.2 _ hba)
    -- 🎉 no goals
#align ordinal.enum_ord_is_normal_iff_is_closed Ordinal.enumOrd_isNormal_iff_isClosed

end Ordinal
