/-
Copyright (c) 2026 Juanjo Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juanjo Madrigal
-/
import Mathlib.SetTheory.Cardinal.Aleph
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.T5

/-!
# The space `ω₁`

The space `ω₁` with the order topology, a source of many counterexamples in general topology.
We follow [Munkres2000], where this space is denoted `S_Ω`.

## References

* [J. Munkres, *Topology*][Munkres2000]
-/

open scoped Cardinal Ordinal Topology
open Set

namespace Omega1Space

universe u

/-! Lemmas on the natural inclusion `Iio ω₁ ↪ Iic ω₁`. -/

def inc : Iio ω₁ → Iic ω₁ := inclusion Iio_subset_Iic_self

lemma inc_embedding : Topology.IsEmbedding inc := Topology.IsEmbedding.inclusion Iio_subset_Iic_self
lemma inc_continuous : Continuous inc := inc_embedding.continuous

lemma inc_prod_embedding :
    Topology.IsEmbedding (fun (p : Iio ω₁ × Iic ω₁) => (inc p.1, p.2)) :=
  inc_embedding.prodMap Topology.IsEmbedding.id

lemma countable_section_iff_lt_omega (x : Ordinal) : (Iio x).Countable ↔ x < ω₁ := by
  rw [← Cardinal.le_aleph0_iff_set_countable]
  simp [-Ordinal.lift_card, Cardinal.lt_omega_iff_card_lt]

/-! Lemmas on countability and compactness. -/

lemma uncountable_section : ¬ (Iio ω₁).Countable := by simp [countable_section_iff_lt_omega]

instance : Uncountable (Iio ω₁) := by rw [uncountable_iff_not_countable]; exact uncountable_section

lemma countable_section (x : Iio ω₁) : (Iio x : Set Ordinal).Countable :=
  (countable_section_iff_lt_omega x).mpr x.2

lemma ω₁_succ_limit : Order.IsSuccLimit ω₁ := Cardinal.isSuccLimit_omega 1

instance : Nontrivial (Iic ω₁) :=
  nontrivial_of_ne ⊥ ⊤ (fun h => ω₁_succ_limit.bot_lt.ne (Subtype.ext_iff.mp h))

lemma no_max {s : Ordinal} (h : s < ω₁) : ∃ a, s < a ∧ a < ω₁ :=
  ⟨s + 1, Order.lt_succ s, ω₁_succ_limit.succ_lt h⟩

lemma countable_bounded (T : Set (Iio ω₁)) (hT : T.Countable) : ∃ b, b < ω₁ ∧ ∀ a ∈ T, a ≤ b := by
  by_contra h; push Not at h
  exact uncountable_section ((hT.biUnion fun a _ => countable_section a).mono
    fun x hx => let ⟨a, haT, hxa⟩ := h x hx; mem_biUnion haT hxa)

lemma exists_lub_of_seq (s : ℕ → Ordinal) (hs : ∀ n, s n < ω₁) :
    ∃ b, b < ω₁ ∧ IsLUB (range s) b := by
  obtain ⟨b', hb'ω₁, hb'⟩ :=
    countable_bounded (range fun n => (⟨s n, hs n⟩ : Iio ω₁)) (countable_range _)
  have hub : b' ∈ upperBounds (range s) := by rintro _ ⟨n, rfl⟩; exact hb' _ ⟨n, rfl⟩
  exact ⟨wellFounded_lt.min (upperBounds (range s)) ⟨b', hub⟩,
    lt_of_le_of_lt (not_lt.mp (wellFounded_lt.not_lt_min _ hub)) hb'ω₁,
    wellFounded_lt.min_mem _ ⟨b', hub⟩, fun u hu => not_lt.mp (wellFounded_lt.not_lt_min _ hu)⟩

lemma isCompact_Iic_ω₁ : IsCompact (Iic ω₁) :=
  by simp only [← Icc_bot, bot_eq_zero', isCompact_Icc];

instance : CompactSpace (Iic ω₁) := isCompact_iff_compactSpace.mp isCompact_Iic_ω₁

/-! Main theorem: `Iio ω₁ × Iic ω₁` is not normal. -/

theorem prod_Iio_ω₁_Iic_ω₁_not_normal : ¬ NormalSpace (Iio.{u+1} ω₁ × Iic.{u+1} ω₁) := by
  intro
  let A : Set (Iio ω₁ × Iic ω₁) := {(a,b) | inc a = b}
  let B : Set (Iio ω₁ × Iic ω₁) := {(a,b) | b = ⊤}
  have hA : IsClosed A := isClosed_eq (inc_continuous.comp continuous_fst) continuous_snd
  have hB : IsClosed B := isClosed_eq continuous_snd continuous_const
  have hAB : Disjoint A B := by
    rw [disjoint_left]
    intro ⟨a, b⟩ (ha : inc a = b) (hb : b = ⊤)
    exact absurd (Subtype.ext_iff.mp (ha.trans hb)) a.2.ne
  obtain ⟨U, V, hU, hV, hAU, hBV, hUV⟩ := normal_separation hA hB hAB
  have hβ_ex : ∀ x : Iio ω₁, ∃ y : Iio ω₁, x < y ∧ (x, inc y) ∉ U := by
    intro x
    obtain ⟨_, hN1, N2, hN2, hsub⟩ := mem_nhds_prod_iff.mp (hV.mem_nhds (hBV rfl))
    obtain ⟨c, hcω₁, hcN⟩ := nhds_top_basis.mem_iff.mp hN2
    obtain ⟨z, hz1, hz2⟩ := no_max (max_lt x.2 (Subtype.coe_lt_coe.mpr hcω₁))
    have hx : x < ⟨z, hz2⟩ := Subtype.coe_lt_coe.mp (lt_of_le_of_lt (le_max_left _ _) hz1)
    have hc : c < inc ⟨z, hz2⟩ :=
      Subtype.coe_lt_coe.mp (lt_of_le_of_lt (le_max_right _ _) hz1)
    exact ⟨⟨z, hz2⟩, hx, fun hU' => hUV.le_bot ⟨hU', hsub ⟨mem_of_mem_nhds hN1, hcN hc⟩⟩⟩
  choose β hβ1 hβ2 using hβ_ex
  let seq : ℕ → Iio ω₁ := Nat.rec ⟨0, ω₁_succ_limit.bot_lt⟩ fun _ prev => β prev
  have hmono : Monotone (fun n => (seq n).1) :=
    monotone_nat_of_le_succ fun n => (Subtype.coe_lt_coe.mpr (hβ1 (seq n))).le
  obtain ⟨b, hbω₁, hb_lub⟩ := exists_lub_of_seq (fun n => (seq n).1) (fun n => (seq n).2)
  have htf : Filter.Tendsto (fun n => (seq n).1) Filter.atTop (𝓝 b) :=
    tendsto_atTop_isLUB hmono hb_lub
  have htprod : Filter.Tendsto (fun n => ((seq n, inc (seq (n + 1))) : Iio ω₁ × Iic ω₁))
      Filter.atTop (𝓝 (⟨b, hbω₁⟩, inc ⟨b, hbω₁⟩)) :=
    (Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr htf).prodMk_nhds
      (Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
        (htf.comp (Filter.tendsto_add_atTop_nat 1)))
  obtain ⟨n, hn⟩ := (htprod.eventually (hU.mem_nhds (hAU rfl))).exists
  exact hβ2 (seq n) hn

instance Iic_ω₁_prod_paracompact : ParacompactSpace (Iic ω₁ × Iic ω₁) := inferInstance
instance Iic_ω₁_prod_normal : NormalSpace (Iic ω₁ × Iic ω₁) := inferInstance

/-! A subspace of a paracompact space need not be paracompact. -/

theorem subspace_of_paracompact_not_paracompact :
    ¬ ∀ (X Y : Type (u+1)) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y),
      ParacompactSpace Y → Topology.IsEmbedding f → ParacompactSpace X := fun h => by
  have : ParacompactSpace (Iio.{u+1} ω₁ × Iic.{u+1} ω₁) :=
    h _ _ _ Iic_ω₁_prod_paracompact inc_prod_embedding
  exact prod_Iio_ω₁_Iic_ω₁_not_normal inferInstance

/-! The product of two normal spaces need not be normal. -/

theorem product_of_normal_not_normal :
    ¬ ∀ (X Y : Type (u+1)) [TopologicalSpace X] [TopologicalSpace Y],
      NormalSpace X → NormalSpace Y → NormalSpace (X × Y) :=
  fun h => prod_Iio_ω₁_Iic_ω₁_not_normal (h _ _ inferInstance inferInstance)

/-! A subspace of a normal space need not be normal. -/

theorem subspace_of_normal_not_normal :
    ¬ ∀ (X Y : Type (u+1)) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y),
      NormalSpace Y → Topology.IsEmbedding f → NormalSpace X :=
  fun h => prod_Iio_ω₁_Iic_ω₁_not_normal (h _ _ _ Iic_ω₁_prod_normal inc_prod_embedding)

/-! A regular space need not be normal. -/

theorem regular_not_normal :
    ¬ ∀ (X : Type (u+1)) [TopologicalSpace X], RegularSpace X → NormalSpace X :=
  fun h => prod_Iio_ω₁_Iic_ω₁_not_normal (h _ inferInstance)

end Omega1Space
