/-
Copyright (c) 2026 Yi Yuan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yi Yuan
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.Topology.Subpath

/-!
# The generation part of the Seifert–van Kampen theorem

Let `(W i)` be a family of open subsets of `X` that cover `X`, and suppose that every `W i`
contains the basepoint `x₀` and the intersection of every two distinct members is path-connected.
This file proves that the images of the homomorphisms from the fundamental groups of the `W i`
induced by the inclusions generate the fundamental group of `X` at `x₀`.

This is the generation part of the Seifert–van Kampen theorem. The proof subdivides a loop into
subpaths lying in members of the cover and joins the subdivision points to `x₀` through pairwise
intersections.

## Main results

* `FundamentalGroup.exists_start_path_of_labelled_subdivision`: an induction principle for a path
  with finitely many labelled subpaths.
* `FundamentalGroup.iSup_map_subtypeVal_range_eq_top`: the images induced by the inclusions of an
  arbitrary open cover generate the fundamental group.
* `FundamentalGroup.map_subtypeVal_range_sup_eq_top`: the images of the two inclusion-induced
  homomorphisms generate the fundamental group, as a specialization of the preceding result.

## References

* [James R. Munkres, *Topology*][Munkres2000], Theorem 59.1.
-/

@[expose] public section

namespace FundamentalGroup

open Path.Homotopic.Quotient

variable {X ι : Type*} [TopologicalSpace X] {S : Set X} {W : ι → Set X} {x₀ a b c : X}

/-- If the range of a loop is contained in `S`, then its homotopy class lies in the range of the
homomorphism on fundamental groups induced by the inclusion `S ↪ X`. -/
lemma mk_mem_range_map_subtypeVal (hx₀ : x₀ ∈ S) {γ : Path x₀ x₀} (hγ : Set.range γ ⊆ S) :
    mk γ ∈ (map (ContinuousMap.subtypeVal S) ⟨x₀, hx₀⟩).range := by
  set lift : Path (⟨x₀, hx₀⟩ : S) ⟨x₀, hx₀⟩ :=
    { toFun := fun t ↦ ⟨γ t, hγ (Set.mem_range_self t)⟩
      continuous_toFun := γ.continuous.subtype_mk _
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  exact ⟨mk lift, by rw [map_apply, ← mk_map]; rfl⟩

lemma path_trans_range_subset {γ : Path a b} {δ : Path b c} (hγ : Set.range γ ⊆ S)
    (hδ : Set.range δ ⊆ S) : Set.range (γ.trans δ) ⊆ S := by grind

lemma path_symm_range_subset {γ : Path a b} (hγ : Set.range γ ⊆ S) : Set.range γ.symm ⊆ S := by
  grind

lemma path_cast_range_subset {a' b' : X} {γ : Path a b} (ha : a' = a) (hb : b' = b)
    (hγ : Set.range γ ⊆ S) : Set.range (γ.cast ha hb) ⊆ S := by
  rintro z ⟨t, rfl⟩
  simpa using hγ (Set.mem_range_self t)

/-- Backward induction along a nonempty labelled subdivision of a path.

Each subpath of `f` lies in the set indexed by its label. The hypothesis `hloop` says that loops
lying in any one labelled set have class in `H`. When two consecutive labels differ, `hchange`
supplies a path from `x₀` to their common endpoint that lies in both labelled sets. Given a path
`β` from `x₀` to the endpoint of `f`, the conclusion supplies a corresponding path `α` to the
starting point of `f` such that the loop formed from `α`, `f`, and `β.symm` has class in `H`. -/
lemma exists_start_path_of_labelled_subdivision {H : Subgroup (FundamentalGroup X x₀)}
    (hloop : ∀ side (γ : Path x₀ x₀), Set.range γ ⊆ W side → mk γ ∈ H)
    (hchange : ∀ i j z, i ≠ j → z ∈ W i ∩ W j → ∃ γ : Path x₀ z, Set.range γ ⊆ W i ∩ W j)
    {n : ℕ} {x y : X} {f : Path x y} {t : Fin (n + 2) → unitInterval} {side : Fin (n + 1) → ι}
    (hsubpath : ∀ i, Set.range (f.subpath (t i.castSucc) (t i.succ)) ⊆ W (side i))
    (β : Path x₀ (f (t (Fin.last (n + 1))))) (hβ : Set.range β ⊆ W (side (Fin.last n))) :
    ∃ α : Path x₀ (f (t 0)), Set.range α ⊆ W (side 0) ∧
      ((mk α).trans ((mk (f.subpath (t 0) (t (Fin.last (n + 1))))).trans (mk β).symm)) ∈ H := by
  induction n with
  | zero =>
      let α : Path x₀ (f (t 0)) := β.trans (f.subpath (t 0) (t (Fin.last 1))).symm
      refine ⟨α, path_trans_range_subset hβ (path_symm_range_subset (hsubpath 0)), ?_⟩
      change ((mk β).trans (mk (f.subpath (t 0) (t (Fin.last 1)))).symm).trans
        ((mk (f.subpath (t 0) (t (Fin.last 1)))).trans (mk β).symm) ∈ H
      rw [trans_assoc, ← trans_assoc (mk (f.subpath (t 0) (t (Fin.last 1)))).symm,
        symm_trans, refl_trans, trans_symm, ← one_def]
      exact H.one_mem
  | succ n ih =>
      let i : Fin (n + 2) := (Fin.last n).castSucc
      let j : Fin (n + 2) := Fin.last (n + 1)
      let q := f.subpath (t j.castSucc) (t j.succ)
      obtain ⟨γ, hγi, hγj⟩ : ∃ γ : Path x₀ (f (t j.castSucc)),
          Set.range γ ⊆ W (side i) ∧ Set.range γ ⊆ W (side j) := by
        by_cases hs : side i = side j
        · let γ : Path x₀ (f (t j.castSucc)) := β.trans q.symm
          have hγ : Set.range γ ⊆ W (side j) :=
            path_trans_range_subset hβ (path_symm_range_subset (hsubpath j))
          exact ⟨γ, hs.symm ▸ hγ, hγ⟩
        · have hi := hsubpath i (Path.target_mem_range _)
          have hj := hsubpath j (Path.source_mem_range _)
          rw [show i.succ = j.castSucc from rfl] at hi
          obtain ⟨γ, hγ⟩ := hchange (side i) (side j) _ hs ⟨hi, hj⟩
          exact ⟨γ, hγ.trans Set.inter_subset_left, hγ.trans Set.inter_subset_right⟩
      obtain ⟨α, hα, hp⟩ := ih (t := t ∘ Fin.castSucc)
        (side := fun k ↦ side k.castSucc) (fun k ↦ hsubpath k.castSucc) γ hγi
      refine ⟨α, hα, ?_⟩
      have hq : Set.range (q.trans β.symm) ⊆ W (side j) :=
        path_trans_range_subset (hsubpath j) (path_symm_range_subset hβ)
      have hγ : Set.range (γ.trans (q.trans β.symm)) ⊆ W (side j) :=
        path_trans_range_subset hγj hq
      have hl := hloop (side j) (γ.trans (q.trans β.symm)) hγ
      simp only [mk_trans] at hl
      have h := H.mul_mem hl hp
      simp only [mul_def, mk_symm, trans_assoc, ← trans_assoc (mk γ).symm,
        symm_trans, refl_trans] at h
      rw [← trans_assoc (mk (f.subpath ((t ∘ Fin.castSucc) 0)
        ((t ∘ Fin.castSucc) (Fin.last (n + 1)))))] at h
      simpa [i, j, q] using h

lemma path_class_cast_mem_of_closed_concat
    {H : Subgroup (FundamentalGroup X x₀)} (hsource : a = x₀) (htarget : b = x₀)
    (α : Path x₀ a) (C : Path a b) (hα : mk (α.cast rfl hsource.symm) ∈ H)
    (hclosed : (mk α).trans ((mk C).trans (mk ((Path.refl x₀).cast rfl htarget)).symm) ∈ H) :
    (mk (C.cast hsource.symm htarget.symm) : FundamentalGroup X x₀) ∈ H := by
  subst a; subst b
  simp only [mk_cast, cast_rfl_rfl] at hα hclosed ⊢
  rw [← mk_symm, Path.refl_symm, mk_refl, trans_refl] at hclosed
  simpa [mul_def, inv_def, ← trans_assoc] using H.mul_mem hclosed (H.inv_mem hα)

/-- A loop subordinate to a finite labelled subdivision lies in the subgroup generated by the
ranges induced by the inclusions of the labelled sets. -/
lemma mk_mem_iSup_range_of_subdivision (hx₀ : ∀ i, x₀ ∈ W i)
    (hinter : ∀ i j, i ≠ j → IsPathConnected (W i ∩ W j))
    {f : Path x₀ x₀} {n : ℕ} {a : Fin (n + 2) → unitInterval}
    (hstart : a 0 = 0) (hend : a (Fin.last (n + 1)) = 1) {side : Fin (n + 1) → ι}
    (hsubpath : ∀ i, Set.range (f.subpath (a i.castSucc) (a i.succ)) ⊆ W (side i)) :
    mk f ∈ (⨆ i, (map (ContinuousMap.subtypeVal (W i)) ⟨x₀, hx₀ i⟩).range :
      Subgroup (FundamentalGroup X x₀)) := by
  let ranges : ι → Subgroup (FundamentalGroup X x₀) :=
    fun i ↦ (map (ContinuousMap.subtypeVal (W i)) ⟨x₀, hx₀ i⟩).range
  have hl : ∀ i (γ : Path x₀ x₀), Set.range γ ⊆ W i → mk γ ∈ ⨆ i, ranges i := by
    intro i γ hγ
    exact SetLike.le_def.mp (le_iSup ranges i) (mk_mem_range_map_subtypeVal (hx₀ i) hγ)
  have hc : ∀ i j z, i ≠ j → z ∈ W i ∩ W j →
      ∃ γ : Path x₀ z, Set.range γ ⊆ W i ∩ W j := by
    intro i j z hij hz
    let h := (hinter i j hij).joinedIn x₀ ⟨hx₀ i, hx₀ j⟩ z hz
    exact ⟨h.somePath, Set.range_subset_iff.mpr h.somePath_mem⟩
  have hs : (f ∘ a) 0 = x₀ := (congrArg f hstart).trans f.source
  have ht : (f ∘ a) (Fin.last (n + 1)) = x₀ := (congrArg f hend).trans f.target
  let β : Path x₀ ((f ∘ a) (Fin.last (n + 1))) := (Path.refl x₀).cast rfl ht
  have hβ : Set.range β ⊆ W (side (Fin.last n)) :=
    path_cast_range_subset rfl ht (by grind)
  obtain ⟨α, hα, h⟩ := exists_start_path_of_labelled_subdivision hl hc hsubpath β hβ
  rw [← show (f.subpath (a 0) (a (Fin.last (n + 1)))).cast hs.symm ht.symm = f by
      ext s; simp [Path.subpath, hstart, hend]]
  refine path_class_cast_mem_of_closed_concat hs ht α
    (f.subpath (a 0) (a (Fin.last (n + 1)))) ?_ h
  exact hl (side 0) (α.cast rfl hs.symm) (path_cast_range_subset rfl hs.symm hα)

/-- **Generation part of the Seifert–van Kampen theorem.** If a family of open sets covers `X`,
each set contains `x₀`, and intersections of distinct sets are path-connected, then the ranges of
the homomorphisms on fundamental groups induced by the inclusions generate the fundamental group
of `X` at `x₀`. -/
theorem iSup_map_subtypeVal_range_eq_top (hW : ∀ i, IsOpen (W i)) (hx₀ : ∀ i, x₀ ∈ W i)
    (hcover : ⋃ i, W i = ⊤) (hinter : ∀ i j, i ≠ j → IsPathConnected (W i ∩ W j)) :
    ⨆ i, (map (ContinuousMap.subtypeVal (W i)) ⟨x₀, hx₀ i⟩).range =
      (⊤ : Subgroup (FundamentalGroup X x₀)) := by
  apply top_unique; intro g _
  obtain ⟨f, rfl⟩ := mk_surjective (toPath g)
  let c : ι → Set unitInterval := fun i ↦ f ⁻¹' W i
  have ho : ∀ i, IsOpen (c i) := fun i ↦ (hW i).preimage f.continuous
  have hc : Set.univ ⊆ ⋃ i, c i := by
    rw [← Set.preimage_iUnion, hcover]
    rfl
  obtain ⟨t, h0, ht, ⟨m, hm⟩, hsub⟩ := exists_monotone_Icc_subset_open_cover_unitInterval ho hc
  obtain _ | n := m
  · exact (zero_ne_one (h0.symm.trans (hm 0 le_rfl))).elim
  choose side hs using fun i : Fin (n + 1) ↦ hsub i
  have hp (i : Fin (n + 1)) : Set.range (f.subpath (t i.castSucc) (t i.succ)) ⊆ W (side i) := by
    have hi : t i.castSucc ≤ t i.succ := ht (Nat.le_succ i)
    grind [Path.range_subpath_of_le]
  exact mk_mem_iSup_range_of_subdivision (n := n) (a := fun i ↦ t i) hx₀ hinter h0
    (hm (n + 1) le_rfl) hp

/-- If two open sets `U` and `V` cover `X` and contain the basepoint `x₀` in their path-connected
intersection, then the ranges of the homomorphisms on fundamental groups induced by their
inclusions generate the fundamental group of `X` at `x₀`. -/
theorem map_subtypeVal_range_sup_eq_top {U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hx₀ : x₀ ∈ U ∩ V) (hcover : U ∪ V = ⊤) [PathConnectedSpace (U ∩ V : Set X)] :
    (map (ContinuousMap.subtypeVal U) ⟨x₀, hx₀.1⟩).range ⊔
      (map (ContinuousMap.subtypeVal V) ⟨x₀, hx₀.2⟩).range =
        (⊤ : Subgroup (FundamentalGroup X x₀)) := by
  set W : Bool → Set X := fun side ↦ cond side V U
  have hx : ∀ side, x₀ ∈ W side := by grind
  have hc : ⋃ side, W side = ⊤ := by
    rw [← Set.union_eq_iUnion]
    grind
  have hi : ∀ i j, i ≠ j → IsPathConnected (W i ∩ W j) := by
    rintro (_ | _) (_ | _) hij
    · exact (hij rfl).elim
    · exact (isPathConnected_iff_pathConnectedSpace.mpr inferInstance : IsPathConnected (U ∩ V))
    · simpa [W, Set.inter_comm] using
        (isPathConnected_iff_pathConnectedSpace.mpr inferInstance : IsPathConnected (U ∩ V))
    · exact (hij rfl).elim
  apply le_antisymm le_top
  have h : ⨆ side, (map (ContinuousMap.subtypeVal (W side)) ⟨x₀, hx side⟩).range ≤
      (map (ContinuousMap.subtypeVal U) ⟨x₀, hx₀.1⟩).range ⊔
        (map (ContinuousMap.subtypeVal V) ⟨x₀, hx₀.2⟩).range := by
    refine iSup_le fun side ↦ ?_
    cases side
    · exact le_sup_left
    · exact le_sup_right
  exact (iSup_map_subtypeVal_range_eq_top (by grind) hx hc hi) ▸ h

end FundamentalGroup
