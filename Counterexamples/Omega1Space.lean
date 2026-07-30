/-
Copyright (c) 2026 Juanjo Madrigal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juanjo Madrigal
-/
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.SetTheory.Ordinal.Topology
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Paracompact
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.T5
import Mathlib.Topology.Instances.Shrink

/-!
# The space `ω₁`

The space `ω₁` with the order topology, a source of many counterexamples in general topology.
We follow [Munkres2000], where this space is denoted `S_Ω`.

## References

* [J. Munkres, *Topology*][Munkres2000]
-/

namespace Counterexample

open scoped Cardinal Ordinal Topology
open Set

namespace Omega1Space

def inc : Iio ω₁ → Iic ω₁ := inclusion Iio_subset_Iic_self

lemma inc_embedding : Topology.IsEmbedding inc := Topology.IsEmbedding.inclusion Iio_subset_Iic_self

instance : Nontrivial (Iic ω₁) :=
  nontrivial_of_ne ⊥ ⊤ (fun h => (Cardinal.isSuccLimit_omega _).bot_lt.ne (Subtype.ext_iff.mp h))

instance : CompactSpace (Iic ω₁) :=
  isCompact_iff_compactSpace.mp (by simp only [← Icc_bot, bot_eq_zero, isCompact_Icc])

/-- Main theorem: `Iio ω₁ × Iic ω₁` is not normal. -/
theorem not_normalSpace_Iio_prod_Iic_omega_one.{u} :
    ¬ NormalSpace (Iio.{u+1} ω₁ × Iic.{u+1} ω₁) := by
  intro
  let A : Set (Iio ω₁ × Iic ω₁) := {(a,b) | inc a = b}
  let B : Set (Iio ω₁ × Iic ω₁) := {(a,b) | b = ⊤}
  have hA : IsClosed A := isClosed_eq (inc_embedding.continuous.comp continuous_fst) continuous_snd
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
    obtain ⟨z, hz1, hz2⟩ := (Order.IsSuccLimit.lt_iff_exists_lt (Cardinal.isSuccLimit_omega _)).mp
      (max_lt x.2 (Subtype.coe_lt_coe.mpr hcω₁))
    have hx : x < ⟨z, hz1⟩ := Subtype.coe_lt_coe.mp (lt_of_le_of_lt (le_max_left _ _) hz2)
    have hc : c < inc ⟨z, hz1⟩ :=
      Subtype.coe_lt_coe.mp (lt_of_le_of_lt (le_max_right _ _) hz2)
    exact ⟨⟨z, hz1⟩, hx, fun hU' => hUV.le_bot ⟨hU', hsub ⟨mem_of_mem_nhds hN1, hcN hc⟩⟩⟩
  choose β hβ1 hβ2 using hβ_ex
  let seq : ℕ → Iio ω₁ := Nat.rec ⟨0, (Cardinal.isSuccLimit_omega _).bot_lt⟩ fun _ prev => β prev
  have hmono : Monotone (fun n => (seq n).1) :=
    monotone_nat_of_le_succ fun n => (Subtype.coe_lt_coe.mpr (hβ1 (seq n))).le
  let b := ⨆ i, (seq i).1
  let hbω₁ := Ordinal.iSup_lt_omega_one (fun n => (seq n).2)
  have htf : Filter.Tendsto (fun n => (seq n).1) Filter.atTop (𝓝 b) :=
    tendsto_atTop_ciSup hmono (by use ω₁; grind [upperBounds])
  have htprod : Filter.Tendsto (fun n => ((seq n, inc (seq (n + 1))) : Iio ω₁ × Iic ω₁))
      Filter.atTop (𝓝 (⟨b, hbω₁⟩, inc ⟨b, hbω₁⟩)) :=
    (Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr htf).prodMk_nhds
      (Topology.IsInducing.subtypeVal.tendsto_nhds_iff.mpr
        (htf.comp (Filter.tendsto_add_atTop_nat 1)))
  obtain ⟨n, hn⟩ := (htprod.eventually (hU.mem_nhds (hAU rfl))).exists
  exact hβ2 (seq n) hn

/-!
With this result, the counterexamples below can be proven for topological spaces X and Y in
Type (u+1). We use Shrink to build versions of Iio.{1} ω₁ and Iic.{1} ω₁ in every universe
and make the results more general.
-/

instance smIio.{u} : Small.{u,1} (Iio ω₁) := small_lift _
abbrev ShIio := Shrink (Iio ω₁)
noncomputable def homeoIio : ShIio ≃ₜ Iio ω₁ := (Shrink.homeomorph (Iio ω₁)).symm
instance smIic.{u} : Small.{u,1} (Iic ω₁) := small_lift _
abbrev ShIic := Shrink (Iic ω₁)
noncomputable def homeoIic : ShIic ≃ₜ Iic ω₁ := (Shrink.homeomorph (Iic ω₁)).symm

instance : T2Space ShIio := homeoIio.symm.t2Space
instance : T2Space ShIic := homeoIic.symm.t2Space
instance : NormalSpace ShIio := homeoIio.symm.normalSpace
instance : NormalSpace ShIic := homeoIic.symm.normalSpace

noncomputable def homeoIicIic : ShIic ≃ₜ ShIic := homeoIic.trans homeoIic.symm
instance compactSpace_toType : CompactSpace ShIic := homeoIic.symm.compactSpace
noncomputable def incT : ShIio → ShIic := homeoIic.symm ∘ inc ∘ homeoIio

lemma incT_prod_embedding.{u, v} : Topology.IsEmbedding
    (fun (p : ShIio × ShIic) =>
      (incT.{u, v} p.1, homeoIicIic.{u, v} p.2)) := by
  refine Topology.IsEmbedding.prodMap ?_ homeoIicIic.isEmbedding
  exact homeoIic.{v}.symm.isEmbedding.comp
    (inc_embedding.comp homeoIio.isEmbedding)

theorem prod_ShIio_ShIic_not_normal.{u, v} :
    ¬ NormalSpace (ShIio.{u} × ShIic.{v}) := by
  intro
  exact not_normalSpace_Iio_prod_Iic_omega_one
    (homeoIio.prodCongr homeoIic).normalSpace

/-! Counterexamples -/

/-- A subspace of a paracompact space need not be paracompact. -/
theorem subspace_of_paracompact_not_paracompact.{u,v} :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y),
      ParacompactSpace Y → Topology.IsEmbedding f → ParacompactSpace X := fun h => by
  have := h _ _ _ inferInstance incT_prod_embedding.{u, v}
  exact prod_ShIio_ShIic_not_normal.{u, u} inferInstance

/-- The product of two normal spaces need not be normal. -/
theorem product_of_normal_not_normal.{u,v} :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y],
      NormalSpace X → NormalSpace Y → NormalSpace (X × Y) :=
  fun h => prod_ShIio_ShIic_not_normal.{u, v} (h _ _ inferInstance inferInstance)

/-- A subspace of a normal space need not be normal. -/
theorem subspace_of_normal_not_normal.{u,v} :
    ¬ ∀ (X : Type u) (Y : Type v) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y),
      NormalSpace Y → Topology.IsEmbedding f → NormalSpace X :=
  fun h => prod_ShIio_ShIic_not_normal.{u, u}
    (h _ _ _ inferInstance incT_prod_embedding.{u, v})

/-- A regular space need not be normal. -/
theorem regular_not_normal.{u} :
    ¬ ∀ (X : Type u) [TopologicalSpace X], RegularSpace X → NormalSpace X :=
  fun h => prod_ShIio_ShIic_not_normal.{u, u} (h _ inferInstance)

end Omega1Space

end Counterexample
