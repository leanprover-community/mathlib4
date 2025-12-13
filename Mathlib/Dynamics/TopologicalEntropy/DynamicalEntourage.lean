/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
module

public import Mathlib.Data.Nat.Lattice
public import Mathlib.Topology.UniformSpace.Basic

/-!
# Dynamical entourages

Bowen-Dinaburg's definition of topological entropy of a transformation `T` in a metric space
`(X, d)` relies on the so-called dynamical balls. These balls are sets
`B (x, ε, n) = { y | ∀ k < n, d(T^[k] x, T^[k] y) < ε }`.

We implement Bowen-Dinaburg's definitions in the more general context of uniform spaces. Dynamical
balls are replaced by what we call dynamical entourages. This file collects all general lemmas
about these objects.

## Main definitions

- `dynEntourage`: dynamical entourage associated with a given transformation `T`, entourage `U`
and time `n`.

## Tags

entropy

## TODO

Add product of entourages.

In the context of (pseudo-e)metric spaces, relate the usual definition of dynamical balls with
these dynamical entourages.
-/

@[expose] public section

namespace Dynamics

open Prod Set UniformSpace
open scoped SetRel Topology Uniformity

variable {X : Type*} {T : X → X} {U V : SetRel X X} {m n : ℕ} {x y : X}

/-- The dynamical entourage associated to a transformation `T`, entourage `U` and time `n`
is the entourage where `x` and `y` are close iff `T^[k] x` and `T^[k] y` are `U`-close
for all `k < n`, i.e. iff they are `U`-close up to time `n`. -/
def dynEntourage (T : X → X) (U : SetRel X X) (n : ℕ) : SetRel X X :=
  ⋂ k < n, (map T T)^[k] ⁻¹' U

lemma dynEntourage_eq_inter_Ico (T : X → X) (U : SetRel X X) (n : ℕ) :
    dynEntourage T U n = ⋂ k : Ico 0 n, (map T T)^[k] ⁻¹' U := by
  simp [dynEntourage]

lemma mem_dynEntourage : (x, y) ∈ dynEntourage T U n ↔ ∀ k < n, (T^[k] x, T^[k] y) ∈ U := by
  simp [dynEntourage]

lemma mem_ball_dynEntourage :
    y ∈ ball x (dynEntourage T U n) ↔ ∀ k < n, T^[k] y ∈ ball (T^[k] x) U := by
  simp only [ball, mem_preimage, mem_dynEntourage]

lemma dynEntourage_mem_uniformity [UniformSpace X] (h : UniformContinuous T)
    (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    dynEntourage T U n ∈ 𝓤 X := by
  rw [dynEntourage_eq_inter_Ico T U n]
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [iInter_coe_set, mem_Ico, Nat.zero_le, true_and] at ih ⊢
    rw [Set.biInter_lt_succ]
    apply Filter.inter_mem ih
    rw [map_iterate T T n]
    exact uniformContinuous_def.1 (UniformContinuous.iterate T n h) U U_uni

lemma ball_dynEntourage_mem_nhds [UniformSpace X] (h : Continuous T)
    (U_uni : U ∈ 𝓤 X) (n : ℕ) (x : X) :
    ball x (dynEntourage T U n) ∈ 𝓝 x := by
  rw [dynEntourage_eq_inter_Ico T U n, ball_iInter, Filter.iInter_mem, Subtype.forall]
  intro k _
  simp only [map_iterate, _root_.ball_preimage]
  exact (h.iterate k).continuousAt.preimage_mem_nhds (ball_mem_nhds (T^[k] x) U_uni)

set_option linter.flexible false in -- simp followed by infer_instance
instance isRefl_dynEntourage [U.IsRefl] : (dynEntourage T U n).IsRefl := by
  simp [dynEntourage]; infer_instance

set_option linter.flexible false in -- simp followed by infer_instance
instance isSymm_dynEntourage [U.IsSymm] : (dynEntourage T U n).IsSymm := by
  simp [dynEntourage]; infer_instance

set_option linter.deprecated false in
@[deprecated isRefl_dynEntourage (since := "2025-10-17")]
lemma idRel_subset_dynEntourage (T : X → X) {U : Set (X × X)} (h : idRel ⊆ U) (n : ℕ) :
    idRel ⊆ (dynEntourage T U n) := by
  simp only [dynEntourage, map_iterate, subset_iInter_iff, idRel_subset, mem_preimage, map_apply]
  exact fun _ _ _ ↦ h rfl

set_option linter.deprecated false in
@[deprecated isSymm_dynEntourage (since := "2025-10-17")]
lemma _root_.IsSymmetricRel.dynEntourage (T : X → X) {U : Set (X × X)}
    (h : IsSymmetricRel U) (n : ℕ) :
    IsSymmetricRel (dynEntourage T U n) := by
  ext xy
  simp only [Dynamics.dynEntourage, map_iterate, mem_preimage, mem_iInter]
  refine forall₂_congr fun k _ ↦ ?_
  exact map_apply' _ _ _ ▸ IsSymmetricRel.mk_mem_comm h

lemma dynEntourage_comp_subset (T : X → X) (U V : SetRel X X) (n : ℕ) :
    (dynEntourage T U n) ○ (dynEntourage T V n) ⊆ dynEntourage T (U ○ V) n := by
  simp only [dynEntourage, map_iterate, subset_iInter_iff]
  intro k k_n xy xy_comp
  simp only [SetRel.comp, mem_iInter, mem_preimage, map_apply, mem_setOf_eq] at xy_comp ⊢
  rcases xy_comp with ⟨z, hz1, hz2⟩
  exact mem_ball_comp (hz1 k k_n) (hz2 k k_n)

lemma _root_.isOpen.dynEntourage [TopologicalSpace X] {T : X → X} (T_cont : Continuous T)
    (U_open : IsOpen U) (n : ℕ) :
    IsOpen (dynEntourage T U n) := by
  rw [dynEntourage_eq_inter_Ico T U n]
  refine isOpen_iInter_of_finite fun k ↦ ?_
  exact U_open.preimage ((T_cont.prodMap T_cont).iterate k)

lemma dynEntourage_monotone (T : X → X) (n : ℕ) :
    Monotone (fun U : SetRel X X ↦ dynEntourage T U n) :=
  fun _ _ h ↦ iInter₂_mono fun _ _ ↦ preimage_mono h

lemma dynEntourage_antitone (T : X → X) (U : SetRel X X) :
    Antitone (fun n : ℕ ↦ dynEntourage T U n) :=
  fun m n m_n ↦ iInter₂_mono' fun k k_m ↦ by use k, lt_of_lt_of_le k_m m_n

@[gcongr]
lemma dynEntourage_mono (hUV : U ⊆ V) (hmn : m ≤ n) : dynEntourage T U n ⊆ dynEntourage T V m :=
  (dynEntourage_monotone _ _ hUV).trans (dynEntourage_antitone _ _ hmn)

@[simp] lemma dynEntourage_zero : dynEntourage T U 0 = univ := by simp [dynEntourage]
@[simp] lemma dynEntourage_one : dynEntourage T U 1 = U := by simp [dynEntourage]

@[simp]
lemma dynEntourage_univ {T : X → X} {n : ℕ} :
    dynEntourage T univ n = univ := by simp [dynEntourage]

lemma mem_ball_dynEntourage_comp (T : X → X) (n : ℕ) {U : SetRel X X} [U.IsSymm]
    (x y : X) (h : (ball x (dynEntourage T U n) ∩ ball y (dynEntourage T U n)).Nonempty) :
    x ∈ ball y (dynEntourage T (U ○ U) n) := by
  rcases h with ⟨z, z_Bx, z_By⟩
  rw [mem_ball_symmetry] at z_Bx
  exact dynEntourage_comp_subset T U U n (mem_ball_comp z_By z_Bx)

lemma _root_.Function.Semiconj.preimage_dynEntourage {Y : Type*} {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Function.Semiconj φ S T) (U : Set (Y × Y)) (n : ℕ) :
    (map φ φ)⁻¹' (dynEntourage T U n) = dynEntourage S ((map φ φ)⁻¹' U) n := by
  rw [dynEntourage, preimage_iInter₂]
  refine iInter₂_congr fun k _ ↦ ?_
  rw [← preimage_comp, ← preimage_comp, map_iterate S S k, map_iterate T T k, map_comp_map,
    map_comp_map, (Function.Semiconj.iterate_right h k).comp_eq]

end Dynamics
