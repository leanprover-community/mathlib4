/-
Copyright (c) 2025 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine
-/
module

public import Mathlib.Dynamics.TopologicalEntropy.NetEntropy
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.ContinuousFunctionalCalculus
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.Closure
import Mathlib.Topology.ClusterPt

/-!
# Topological entropy of subsets: monotonicity, closure, union

This file contains general results about the topological entropy of various subsets of the same
dynamical system `(X, T)`. We prove that:
- the topological entropy `CoverEntropy T F` of `F` is monotone in `F`: the larger the subset,
  the larger its entropy.
- the topological entropy of a subset equals the entropy of its closure.
- the entropy of the union of two sets is the maximum of their entropies. We generalize
  the latter property to finite unions.

## Implementation notes

Most results are proved using only the definition of the topological entropy by covers. Some lemmas
of general interest are also proved for nets.

## TODO

One may implement a notion of Hausdorff convergence for subsets using uniform
spaces, and then prove the semicontinuity of the topological entropy. It would be a nice
generalization of the lemmas on closures.

## Tags

closure, entropy, subset, union
-/

@[expose] public section

namespace Dynamics

open ExpGrowth Set UniformSpace
open scoped SetRel Uniformity

variable {X : Type*} {T : X → X} {F G s t : Set X} {U V : SetRel X X} {n : ℕ}

/-! ### Monotonicity of entropy as a function of the subset -/

section Subset

lemma IsDynCoverOf.monotone_subset (F_G : F ⊆ G) (h : IsDynCoverOf T G U n s) :
    IsDynCoverOf T F U n s :=
  F_G.trans h

lemma IsDynNetIn.monotone_subset (F_G : F ⊆ G) (h : IsDynNetIn T F U n s) : IsDynNetIn T G U n s :=
  ⟨h.1.trans F_G, h.2⟩

lemma coverMincard_monotone_subset (T : X → X) (U : SetRel X X) (n : ℕ) :
    Monotone fun F : Set X ↦ coverMincard T F U n :=
  fun _ _ F_G ↦ biInf_mono fun _ h ↦ h.monotone_subset F_G

lemma netMaxcard_monotone_subset (T : X → X) (U : SetRel X X) (n : ℕ) :
    Monotone fun F : Set X ↦ netMaxcard T F U n :=
  fun _ _ F_G ↦ biSup_mono fun _ h ↦ h.monotone_subset F_G

lemma coverEntropyInfEntourage_monotone (T : X → X) (U : SetRel X X) :
    Monotone fun F : Set X ↦ coverEntropyInfEntourage T F U := by
  refine fun F G F_G ↦ ExpGrowth.expGrowthInf_monotone fun n ↦ ?_
  exact ENat.toENNReal_mono (coverMincard_monotone_subset T U n F_G)

lemma coverEntropyEntourage_monotone (T : X → X) (U : SetRel X X) :
    Monotone fun F : Set X ↦ coverEntropyEntourage T F U := by
  refine fun F G F_G ↦ ExpGrowth.expGrowthSup_monotone fun n ↦ ?_
  exact ENat.toENNReal_mono (coverMincard_monotone_subset T U n F_G)

lemma netEntropyInfEntourage_monotone (T : X → X) (U : SetRel X X) :
    Monotone fun F : Set X ↦ netEntropyInfEntourage T F U := by
  refine fun F G F_G ↦ ExpGrowth.expGrowthInf_monotone fun n ↦ ?_
  exact ENat.toENNReal_mono (netMaxcard_monotone_subset T U n F_G)

lemma netEntropyEntourage_monotone (T : X → X) (U : SetRel X X) :
    Monotone fun F : Set X ↦ netEntropyEntourage T F U := by
  refine fun F G F_G ↦ ExpGrowth.expGrowthSup_monotone fun n ↦ ?_
  exact ENat.toENNReal_mono (netMaxcard_monotone_subset T U n F_G)

lemma coverEntropyInf_monotone [UniformSpace X] (T : X → X) :
    Monotone fun F : Set X ↦ coverEntropyInf T F :=
  fun _ _ F_G ↦ iSup₂_mono fun U _ ↦ coverEntropyInfEntourage_monotone T U F_G

lemma coverEntropy_monotone [UniformSpace X] (T : X → X) :
    Monotone fun F : Set X ↦ coverEntropy T F :=
  fun _ _ F_G ↦ iSup₂_mono fun U _ ↦ coverEntropyEntourage_monotone T U F_G

end Subset

/-! ### Closure -/

section Closure

variable [UniformSpace X]

lemma IsDynCoverOf.closure (h : Continuous T)
    (V_uni : V ∈ 𝓤 X) (s_cover : IsDynCoverOf T F U n s) :
    IsDynCoverOf T (closure F) (V ○ U) n s := by
  rcases (hasBasis_symmetric.mem_iff' V).1 V_uni with ⟨W, ⟨W_uni, W_symm⟩, W_V⟩
  refine IsDynCoverOf.of_entourage_subset (SetRel.comp_subset_comp_left W_V) fun x hx ↦ ?_
  obtain ⟨y, hxy, hy⟩ := mem_closure_iff_nhds.1 hx _ (ball_dynEntourage_mem_nhds h W_uni n x)
  obtain ⟨z, hz, hyz⟩ := s_cover hy
  exact ⟨z, hz, dynEntourage_comp_subset _ _ _ _ ⟨y, hxy, hyz⟩⟩

lemma coverMincard_closure_le (h : Continuous T) (F : Set X) (U : SetRel X X)
    (V_uni : V ∈ 𝓤 X) (n : ℕ) :
    coverMincard T (closure F) (V ○ U) n ≤ coverMincard T F U n := by
  rcases eq_top_or_lt_top (coverMincard T F U n) with h' | h'
  · exact h' ▸ le_top
  obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U n).1 h'
  exact s_coverMincard ▸ (s_cover.closure h V_uni).coverMincard_le_card

lemma coverEntropyInfEntourage_closure (h : Continuous T) (F : Set X) (U : SetRel X X)
    (V_uni : V ∈ 𝓤 X) :
    coverEntropyInfEntourage T (closure F) (V ○ U) ≤ coverEntropyInfEntourage T F U :=
  expGrowthInf_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_closure_le h F U V_uni n)

lemma coverEntropyEntourage_closure (h : Continuous T) (F : Set X) (U : SetRel X X)
    (V_uni : V ∈ 𝓤 X) :
    coverEntropyEntourage T (closure F) (V ○ U) ≤ coverEntropyEntourage T F U :=
  expGrowthSup_monotone fun n ↦ ENat.toENNReal_mono (coverMincard_closure_le h F U V_uni n)

lemma coverEntropyInf_closure (h : Continuous T) :
    coverEntropyInf T (closure F) = coverEntropyInf T F := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm (coverEntropyInf_monotone T subset_closure)
  obtain ⟨V, V_uni, V_U⟩ := comp_mem_uniformity_sets U_uni
  exact le_iSup₂_of_le V V_uni ((coverEntropyInfEntourage_antitone T (closure F) V_U).trans
    (coverEntropyInfEntourage_closure h F V V_uni))

theorem coverEntropy_closure (h : Continuous T) :
    coverEntropy T (closure F) = coverEntropy T F := by
  refine (iSup₂_le fun U U_uni ↦ ?_).antisymm (coverEntropy_monotone T subset_closure)
  obtain ⟨V, V_uni, V_U⟩ := comp_mem_uniformity_sets U_uni
  exact le_iSup₂_of_le V V_uni ((coverEntropyEntourage_antitone T (closure F) V_U).trans
    (coverEntropyEntourage_closure h F V V_uni))

end Closure

/-! ### Finite unions -/

section Union

lemma IsDynCoverOf.union (hs : IsDynCoverOf T F U n s) (ht : IsDynCoverOf T G U n t) :
    IsDynCoverOf T (F ∪ G) U n (s ∪ t) := SetRel.IsCover.union hs ht

lemma coverMincard_union_le (T : X → X) (F G : Set X) (U : SetRel X X) (n : ℕ) :
    coverMincard T (F ∪ G) U n ≤ coverMincard T F U n + coverMincard T G U n := by
  classical
  rcases eq_top_or_lt_top (coverMincard T F U n) with hF | hF
  · rw [hF, top_add]; exact le_top
  rcases eq_top_or_lt_top (coverMincard T G U n) with hG | hG
  · rw [hG, add_top]; exact le_top
  obtain ⟨s, s_cover, s_coverMincard⟩ := (coverMincard_finite_iff T F U n).1 hF
  obtain ⟨t, t_cover, t_coverMincard⟩ := (coverMincard_finite_iff T G U n).1 hG
  rw [← s_coverMincard, ← t_coverMincard, ← ENat.coe_add]
  apply (IsDynCoverOf.coverMincard_le_card _).trans (WithTop.coe_mono (s.card_union_le t))
  rw [s.coe_union t]
  exact s_cover.union t_cover

lemma coverEntropyEntourage_union :
    coverEntropyEntourage T (F ∪ G) U
      = max (coverEntropyEntourage T F U) (coverEntropyEntourage T G U) := by
  refine le_antisymm ?_ ?_
  · apply le_of_le_of_eq (expGrowthSup_monotone fun n ↦ ?_) expGrowthSup_add
    rw [Pi.add_apply, ← ENat.toENNReal_add]
    exact ENat.toENNReal_mono (coverMincard_union_le T F G U n)
  · exact max_le (coverEntropyEntourage_monotone T U subset_union_left)
      (coverEntropyEntourage_monotone T U subset_union_right)

variable {ι : Type*} [UniformSpace X]

lemma coverEntropy_union :
    coverEntropy T (F ∪ G) = max (coverEntropy T F) (coverEntropy T G) := by
  simp only [coverEntropy, ← iSup_sup_eq]
  exact biSup_congr fun _ _ ↦ coverEntropyEntourage_union

lemma coverEntropyInf_iUnion_le (T : X → X) (F : ι → Set X) :
    ⨆ i, coverEntropyInf T (F i) ≤ coverEntropyInf T (⋃ i, F i) :=
  iSup_le fun i ↦ coverEntropyInf_monotone T (subset_iUnion F i)

lemma coverEntropy_iUnion_le (T : X → X) (F : ι → Set X) :
    ⨆ i, coverEntropy T (F i) ≤ coverEntropy T (⋃ i, F i) :=
  iSup_le fun i ↦ coverEntropy_monotone T (subset_iUnion F i)

lemma coverEntropyInf_biUnion_le (s : Set ι) (T : X → X) (F : ι → Set X) :
    ⨆ i ∈ s, coverEntropyInf T (F i) ≤ coverEntropyInf T (⋃ i ∈ s, F i) :=
  iSup₂_le fun _ i_s ↦ coverEntropyInf_monotone T (subset_biUnion_of_mem i_s)

lemma coverEntropy_biUnion_le (s : Set ι) (T : X → X) (F : ι → Set X) :
    ⨆ i ∈ s, coverEntropy T (F i) ≤ coverEntropy T (⋃ i ∈ s, F i) :=
  iSup₂_le fun _ i_s ↦ coverEntropy_monotone T (subset_biUnion_of_mem i_s)

/-- Topological entropy `CoverEntropy T` as a `SupBotHom` function of the subset. -/
noncomputable def coverEntropy_supBotHom (T : X → X) :
    SupBotHom (Set X) EReal where
  toFun := coverEntropy T
  map_sup' := fun _ _ ↦ coverEntropy_union
  map_bot' := coverEntropy_empty

lemma coverEntropy_iUnion_of_finite [Finite ι] {T : X → X} {F : ι → Set X} :
    coverEntropy T (⋃ i : ι, F i) = ⨆ i : ι, coverEntropy T (F i) :=
  map_finite_iSup (coverEntropy_supBotHom T) F

lemma coverEntropy_biUnion_finset {T : X → X} {F : ι → Set X} {s : Finset ι} :
    coverEntropy T (⋃ i ∈ s, F i) = ⨆ i ∈ s, coverEntropy T (F i) := by
  have := map_finset_sup (coverEntropy_supBotHom T) s F
  rw [s.sup_set_eq_biUnion, s.sup_eq_iSup, coverEntropy_supBotHom, SupBotHom.coe_mk,
    SupHom.coe_mk] at this
  rw [this]
  congr

end Union

end Dynamics
