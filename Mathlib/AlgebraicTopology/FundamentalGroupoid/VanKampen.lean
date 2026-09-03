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

Let `U` and `V` be open subsets of `X` that cover `X`, and suppose that `U ∩ V` is path-connected
and contains the basepoint `x₀`. This file proves that the images of the homomorphisms from the
fundamental groups of `U` and `V` induced by the inclusions generate the fundamental group of `X`
at `x₀`.

This is the generation part of the Seifert–van Kampen theorem. The proof subdivides a loop into
subpaths lying in `U` or `V` and joins the subdivision points to `x₀` through `U ∩ V`.

## Main results

* `FundamentalGroup.exists_start_path_of_labelled_subdivision`: an induction principle for a path
  with finitely many labelled subpaths.
* `FundamentalGroup.map_subtypeVal_range_sup_eq_top`: the images of the two inclusion-induced
  homomorphisms generate the fundamental group.

## References

* [James R. Munkres, *Topology*][Munkres2000], Theorem 59.1.
-/

@[expose] public section

universe u

namespace FundamentalGroup

open Path.Homotopic.Quotient

/-- If the range of a loop is contained in `S`, then its homotopy class lies in the range of the
homomorphism on fundamental groups induced by the inclusion `S ↪ X`. -/
lemma mk_mem_range_map_subtypeVal {X : Type u} [TopologicalSpace X]
    {S : Set X} {x₀ : X} (hx₀ : x₀ ∈ S) (γ : Path x₀ x₀) (hγ : Set.range γ ⊆ S) :
    mk γ ∈ (map (ContinuousMap.subtypeVal S) ⟨x₀, hx₀⟩).range := by
  set lift : Path (⟨x₀, hx₀⟩ : S) ⟨x₀, hx₀⟩ :=
    { toFun := fun t ↦ ⟨γ t, hγ (Set.mem_range_self t)⟩
      continuous_toFun := γ.continuous.subtype_mk _
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  exact ⟨mk lift, by rw [map_apply, ← mk_map]; rfl⟩

lemma path_trans_range_subset {X : Type u} [TopologicalSpace X]
    {S : Set X} {a b c : X} (γ : Path a b) (δ : Path b c)
    (hγ : Set.range γ ⊆ S) (hδ : Set.range δ ⊆ S) : Set.range (γ.trans δ) ⊆ S := by
  simpa [Path.trans_range] using Set.union_subset hγ hδ

lemma path_symm_range_subset {X : Type u} [TopologicalSpace X]
    {S : Set X} {a b : X} (γ : Path a b) (hγ : Set.range γ ⊆ S) : Set.range γ.symm ⊆ S := by
  simpa [Path.symm_range]

lemma path_cast_range_subset {X : Type u} [TopologicalSpace X]
    {S : Set X} {a b a' b' : X} (γ : Path a b)
    (ha : a' = a) (hb : b' = b) (hγ : Set.range γ ⊆ S) : Set.range (γ.cast ha hb) ⊆ S := by
  rintro z ⟨t, rfl⟩
  simpa using hγ (Set.mem_range_self t)

/-- Backward induction along a nonempty labelled subdivision of a path.

Each subpath of `f` lies in the set indexed by its label. The hypothesis `hloop` says that loops
lying in any one labelled set have class in `H`. When two consecutive labels differ, `hchange`
supplies a path from `x₀` to their common endpoint that lies in both labelled sets. Given a path
`β` from `x₀` to the endpoint of `f`, the conclusion supplies a corresponding path `α` to the
starting point of `f` such that the loop formed from `α`, `f`, and `β.symm` has class in `H`. -/
lemma exists_start_path_of_labelled_subdivision {X : Type u} [TopologicalSpace X]
    {ι : Type*} {W : ι → Set X} {x₀ : X} {H : Subgroup (FundamentalGroup X x₀)}
    (hloop : ∀ side (γ : Path x₀ x₀), Set.range γ ⊆ W side → mk γ ∈ H)
    (hchange : ∀ i j z, i ≠ j → z ∈ W i ∩ W j → ∃ γ : Path x₀ z, Set.range γ ⊆ W i ∩ W j)
    {n : ℕ} {x y : X} (f : Path x y) {t : Fin (n + 2) → unitInterval} {side : Fin (n + 1) → ι}
    (hsubpath : ∀ i, Set.range (f.subpath (t i.castSucc) (t i.succ)) ⊆ W (side i))
    (β : Path x₀ (f (t (Fin.last (n + 1))))) (hβ : Set.range β ⊆ W (side (Fin.last n))) :
    ∃ α : Path x₀ (f (t 0)), Set.range α ⊆ W (side 0) ∧
      ((mk α).trans ((mk (f.subpath (t 0) (t (Fin.last (n + 1))))).trans (mk β).symm)) ∈ H := by
  induction n with
  | zero =>
      let α : Path x₀ (f (t 0)) := β.trans (f.subpath (t 0) (t (Fin.last 1))).symm
      refine ⟨α, path_trans_range_subset β _ hβ
        (path_symm_range_subset _ (hsubpath 0)), ?_⟩
      change ((mk β).trans (mk (f.subpath (t 0) (t (Fin.last 1)))).symm).trans
        ((mk (f.subpath (t 0) (t (Fin.last 1)))).trans (mk β).symm) ∈ H
      rw [trans_assoc, ← trans_assoc (mk (f.subpath (t 0) (t (Fin.last 1)))).symm,
        symm_trans, refl_trans, trans_symm, ← one_def]
      exact H.one_mem
  | succ n ih =>
      let i : Fin (n + 2) := (Fin.last n).castSucc
      let j : Fin (n + 2) := Fin.last (n + 1)
      let q := f.subpath (t j.castSucc) (t j.succ)
      obtain ⟨γ, hγprevious, hγlast⟩ : ∃ γ : Path x₀ (f (t j.castSucc)),
          Set.range γ ⊆ W (side i) ∧ Set.range γ ⊆ W (side j) := by
        by_cases hside : side i = side j
        · let γ : Path x₀ (f (t j.castSucc)) := β.trans q.symm
          have hγlast : Set.range γ ⊆ W (side j) :=
            path_trans_range_subset β _ hβ (path_symm_range_subset q (hsubpath j))
          exact ⟨γ, hside.symm ▸ hγlast, hγlast⟩
        · have hi := hsubpath i (Path.target_mem_range _)
          have hj := hsubpath j (Path.source_mem_range _)
          rw [show i.succ = j.castSucc from rfl] at hi
          obtain ⟨γ, hγ⟩ := hchange (side i) (side j) _ hside ⟨hi, hj⟩
          exact ⟨γ, hγ.trans Set.inter_subset_left, hγ.trans Set.inter_subset_right⟩
      obtain ⟨α, hα, hprefix⟩ := ih (t := t ∘ Fin.castSucc)
        (side := fun k ↦ side k.castSucc) (fun k ↦ hsubpath k.castSucc) γ hγprevious
      refine ⟨α, hα, ?_⟩
      have htailRange : Set.range (q.trans β.symm) ⊆ W (side j) :=
        path_trans_range_subset q β.symm (hsubpath j) (path_symm_range_subset β hβ)
      have hclosedRange : Set.range (γ.trans (q.trans β.symm)) ⊆ W (side j) :=
        path_trans_range_subset γ _ hγlast htailRange
      have hlast := hloop (side j) (γ.trans (q.trans β.symm)) hclosedRange
      simp only [mk_trans] at hlast
      have hcombined := H.mul_mem hlast hprefix
      simp only [mul_def, mk_symm, trans_assoc, ← trans_assoc (mk γ).symm,
        symm_trans, refl_trans] at hcombined
      rw [← trans_assoc (mk (f.subpath ((t ∘ Fin.castSucc) 0)
        ((t ∘ Fin.castSucc) (Fin.last (n + 1)))))] at hcombined
      simpa [i, j, q] using hcombined

lemma path_class_cast_mem_of_closed_concat {X : Type u} [TopologicalSpace X]
    {x₀ a b : X} (H : Subgroup (FundamentalGroup X x₀)) (hsource : a = x₀) (htarget : b = x₀)
    (α : Path x₀ a) (C : Path a b) (hα : mk (α.cast rfl hsource.symm) ∈ H)
    (hclosed : (mk α).trans ((mk C).trans (mk ((Path.refl x₀).cast rfl htarget)).symm) ∈ H) :
    (mk (C.cast hsource.symm htarget.symm) : FundamentalGroup X x₀) ∈ H := by
  subst a; subst b
  simp only [mk_cast, cast_rfl_rfl] at hα hclosed ⊢
  rw [← mk_symm, Path.refl_symm, mk_refl, trans_refl] at hclosed
  simpa [mul_def, inv_def, ← trans_assoc] using H.mul_mem hclosed (H.inv_mem hα)

/-- A loop subordinate to a finite subdivision by `U` and `V` lies in the
subgroup generated by the two inclusion-induced ranges. -/
lemma mk_mem_range_sup_of_subdivision {X : Type u} [TopologicalSpace X]
    (U V : Set X) (x₀ : X) (hx₀ : x₀ ∈ U ∩ V)
    [PathConnectedSpace (U ∩ V : Set X)]
    (f : Path x₀ x₀) (n : ℕ) (a : Fin (n + 2) → unitInterval)
    (hstart : a 0 = 0) (hend : a (Fin.last (n + 1)) = 1)
    (side : Fin (n + 1) → Bool)
    (hsubpath : ∀ i, Set.range (f.subpath (a i.castSucc) (a i.succ)) ⊆ if side i then V else U) :
    mk f ∈ (map (ContinuousMap.subtypeVal U) ⟨x₀, hx₀.1⟩).range ⊔
    (map (ContinuousMap.subtypeVal V) ⟨x₀, hx₀.2⟩).range := by
  let W : Bool → Set X := fun side ↦ cond side V U
  let : PathConnectedSpace (W false ∩ W true : Set X) := by
    simpa only [W, cond] using (inferInstance : PathConnectedSpace (U ∩ V : Set X))
  let H : Subgroup (FundamentalGroup X x₀) :=
    (map (ContinuousMap.subtypeVal U) ⟨x₀, hx₀.1⟩).range ⊔
    (map (ContinuousMap.subtypeVal V) ⟨x₀, hx₀.2⟩).range
  have hsingleSide : ∀ choice (γ : Path x₀ x₀), Set.range γ ⊆ W choice → mk γ ∈ H := by
    rintro (_ | _) γ hγ
    · exact SetLike.le_def.mp le_sup_left (mk_mem_range_map_subtypeVal hx₀.1 γ hγ)
    · exact SetLike.le_def.mp le_sup_right (mk_mem_range_map_subtypeVal hx₀.2 γ hγ)
  have hchange : ∀ i j z, i ≠ j → z ∈ W i ∩ W j → ∃ γ : Path x₀ z, Set.range γ ⊆ W i ∩ W j := by
    intro i j z hij hz
    have h : W i ∩ W j = W false ∩ W true := by grind
    rw [h] at hz ⊢
    let δ := PathConnectedSpace.somePath (⟨x₀, by grind⟩ : ↑(W false ∩ W true)) ⟨z, hz⟩
    refine ⟨δ.map continuous_subtype_val, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact (δ s).property
  have hsource : (f ∘ a) 0 = x₀ := (congrArg f hstart).trans f.source
  have htarget : (f ∘ a) (Fin.last (n + 1)) = x₀ := (congrArg f hend).trans f.target
  let β : Path x₀ ((f ∘ a) (Fin.last (n + 1))) := (Path.refl x₀).cast rfl htarget
  have hβ : Set.range β ⊆ W (side (Fin.last n)) :=
    path_cast_range_subset (Path.refl x₀) rfl htarget (by grind)
  obtain ⟨α, hα, hclosed⟩ :=
    exists_start_path_of_labelled_subdivision hsingleSide hchange f (by grind) β hβ
  rw [← show (f.subpath (a 0) (a (Fin.last (n + 1)))).cast hsource.symm htarget.symm = f by
      ext s; simp [Path.subpath, hstart, hend]]
  refine path_class_cast_mem_of_closed_concat H hsource htarget α
    (f.subpath (a 0) (a (Fin.last (n + 1)))) ?_ hclosed
  exact hsingleSide (side 0) (α.cast rfl hsource.symm)
    (path_cast_range_subset α rfl hsource.symm hα)

/-- **Generation part of the Seifert–van Kampen theorem.** If two open sets `U` and `V` cover
`X`, contain the basepoint `x₀` in their path-connected intersection, then the ranges of the
homomorphisms on fundamental groups induced by the inclusions of `U` and `V` generate the
fundamental group of `X` at `x₀`. -/
theorem map_subtypeVal_range_sup_eq_top {X : Type u} [TopologicalSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) {x₀ : X} (hx₀ : x₀ ∈ U ∩ V)
    (hcover : U ∪ V = ⊤) [PathConnectedSpace (U ∩ V : Set X)] :
    (map (ContinuousMap.subtypeVal U) ⟨x₀, hx₀.1⟩).range ⊔
    (map (ContinuousMap.subtypeVal V) ⟨x₀, hx₀.2⟩).range = ⊤ := by
  apply top_unique; intro g _
  obtain ⟨f, rfl⟩ := mk_surjective (toPath g)
  let c : Bool → Set unitInterval := fun side ↦ f ⁻¹' cond side V U
  have hcOpen : ∀ choice, IsOpen (c choice) :=
    Bool.forall_bool.2 ⟨hU.preimage f.continuous, hV.preimage f.continuous⟩
  have hcCover : Set.univ ⊆ ⋃ choice, c choice := by
    rw [← Set.preimage_iUnion, ← Set.union_eq_iUnion, Set.union_comm, hcover]
    rfl
  obtain ⟨t, ht0, htmono, ⟨m, hm⟩, htSubordinate⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval hcOpen hcCover
  obtain _ | n := m
  · exact (zero_ne_one (ht0.symm.trans (hm 0 le_rfl))).elim
  choose side hside using fun i : Fin (n + 1) ↦ htSubordinate i
  have hsubpath : ∀ i, Set.range (f.subpath (t i.castSucc) (t i.succ)) ⊆
      if side i then V else U := by
    intro i
    have hstep : t i.castSucc ≤ t i.succ := htmono (Nat.le_succ i)
    grind [Path.range_subpath_of_le]
  exact mk_mem_range_sup_of_subdivision U V x₀ hx₀ f n (fun i ↦ t i) ht0
    (hm (n + 1) le_rfl) side hsubpath

end FundamentalGroup
