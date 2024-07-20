/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Tactic
import Mathlib.Topology.UniformSpace.Compact

/-!
# Dynamical uniformities
Bowen-Dinaburg's definition of topological entropy of a transformation `T` in a metric space
`(X, d)` relies on the so-called dynamical balls. These balls are sets
`B (x, ε, n) = { y | ∀ k < n, d(T^[k] x, T^[k] y) < ε }`.

We implement Bowen-Dinaburg's definitions in the more general context of uniform spaces. Dynamical
balls are replaced by what we call dynamical uniformities. This file collects all general lemmas
about these objects.

## Main definitions
- `DynamicalUni`: dynamical uniformity associated with a given transformation `T`, uniformity `U`
and time `n`.

## Tags
entropy

## TODO
In the context of (pseudo-e)metric spaces, relate the usual definition of dynamical balls with
these dynamical uniformities
-/

namespace DynamicalUniformity

open Prod Set Uniformity UniformSpace

variable {X : Type*}

/-- A dynamical uniform neighborhood is the uniform space version of dynamical balls.-/
def DynamicalUni (T : X → X) (U : Set (X × X)) (n : ℕ) : Set (X × X) :=
  ⋂ k < n, (map T T)^[k] ⁻¹' U

theorem dynamical_uni_inter_Ico (T : X → X) (U : Set (X × X)) (n : ℕ) :
    DynamicalUni T U n = ⋂ k : Ico 0 n, (map T T)^[k] ⁻¹' U := by
  simp only [DynamicalUni, iInter_coe_set, mem_Ico, zero_le, true_and]

theorem dynamical_uni_mem {T : X → X} {U : Set (X × X)} {n : ℕ} {x y : X} :
    (x, y) ∈ DynamicalUni T U n ↔ ∀ k < n, (T^[k] x, T^[k] y) ∈ U := by
  simp only [DynamicalUni, map_iterate, mem_preimage, mem_iInter, map_apply]

theorem dynamical_balls_mem {T : X → X} {U : Set (X × X)} {n : ℕ} {x y : X} :
    y ∈ ball x (DynamicalUni T U n) ↔ ∀ k < n, T^[k] y ∈ ball (T^[k] x) U := by
  simp only [ball, mem_preimage]; exact dynamical_uni_mem

theorem dynamical_uni_of_uni [UniformSpace X] {T : X → X} (h : UniformContinuous T)
    {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    DynamicalUni T U n ∈ 𝓤 X := by
  rw [dynamical_uni_inter_Ico T U n]
  refine Filter.iInter_mem.2 fun k ↦ ?_
  rw [map_iterate T T k]
  exact uniformContinuous_def.1 (UniformContinuous.iterate T k h) U U_uni

theorem dynamical_uni_of_rfl_is_rfl (T : X → X) {U : Set (X × X)} (h : idRel ⊆ U) (n : ℕ) :
    idRel ⊆ (DynamicalUni T U n) := by
  simp only [DynamicalUni, map_iterate, subset_iInter_iff, idRel_subset, mem_preimage, map_apply]
  intro _ _ _
  apply h
  rw [mem_idRel]

theorem dynamical_uni_of_symm_is_symm (T : X → X) {U : Set (X × X)} (h : SymmetricRel U) (n : ℕ) :
    SymmetricRel (DynamicalUni T U n) := by
  ext xy
  simp only [DynamicalUni, map_iterate, mem_preimage, mem_iInter]
  refine forall₂_congr fun k _ ↦ ?_
  rw [map_apply', map_apply']
  exact SymmetricRel.mk_mem_comm h

theorem dynamical_uni_of_comp_is_comp (T : X → X) (U V : Set (X × X)) (n : ℕ) :
    (DynamicalUni T U n) ○ (DynamicalUni T V n) ⊆ DynamicalUni T (U ○ V) n := by
  simp only [DynamicalUni, map_iterate, subset_iInter_iff]
  intro k k_n xy xy_comp
  simp only [compRel, mem_iInter, mem_preimage, map_apply, mem_setOf_eq] at xy_comp ⊢
  rcases xy_comp with ⟨z, hz1, hz2⟩
  exact mem_ball_comp (hz1 k k_n) (hz2 k k_n)

theorem dynamical_uni_of_open_is_open [TopologicalSpace X] {T : X → X} (T_cont : Continuous T)
    {U : Set (X × X)} (U_open : IsOpen U) (n : ℕ) :
    IsOpen (DynamicalUni T U n) := by
  rw [dynamical_uni_inter_Ico T U n]
  refine isOpen_iInter_of_finite fun k ↦ ?_
  exact continuous_def.1 (Continuous.iterate (Continuous.prod_map T_cont T_cont) k) U U_open

theorem dynamical_uni_monotone_uni (T : X → X) (n : ℕ) :
    Monotone (fun U : Set (X × X) ↦ DynamicalUni T U n) :=
  fun _ _ h ↦ iInter₂_mono fun _ _ ↦ preimage_mono h

theorem dynamical_uni_antitone_time (T : X → X) (U : Set (X × X)) :
    Antitone (fun n : ℕ ↦ DynamicalUni T U n) := by
  intro m n m_n
  refine iInter₂_mono' fun k k_m ↦ ?_
  use k, lt_of_lt_of_le k_m m_n

@[simp]
theorem dynamical_uni_time_zero {T : X → X} {U : Set (X × X)} :
    DynamicalUni T U 0 = univ := by
  simp only [DynamicalUni, not_lt_zero', iInter_of_empty, iInter_univ]

@[simp]
theorem dynamical_time_one {T : X → X} {U : Set (X × X)} :
    DynamicalUni T U 1 = U := by
  simp [DynamicalUni]

@[simp]
theorem dynamical_univ {T : X → X} {n : ℕ} :
    DynamicalUni T univ n = univ := by
  simp [DynamicalUni]

theorem inter_of_dynamical_balls (T : X → X) (n : ℕ) {U : Set (X × X)} (U_symm : SymmetricRel U)
    (x y : X) (h : (ball x (DynamicalUni T U n) ∩ ball y (DynamicalUni T U n)).Nonempty) :
    x ∈ ball y (DynamicalUni T (U ○ U) n) := by
  rcases h with ⟨z, z_Bx, z_By⟩
  rw [mem_ball_symmetry (dynamical_uni_of_symm_is_symm T U_symm n)] at z_Bx
  exact dynamical_uni_of_comp_is_comp T U U n (mem_ball_comp z_By z_Bx)

/--Preimages of dynamical uniformities under semiconjugacies.-/
theorem preimage_of_dynamical_uni {Y : Type*} {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Function.Semiconj φ S T) (U : Set (Y × Y)) (n : ℕ) :
    (map φ φ)⁻¹' (DynamicalUni T U n) = DynamicalUni S ((map φ φ)⁻¹' U) n := by
  unfold DynamicalUni
  rw [preimage_iInter₂]
  refine iInter₂_congr fun k _ ↦ ?_
  rw [← preimage_comp, ← preimage_comp, map_iterate S S k, map_iterate T T k, map_comp_map,
    map_comp_map, (Function.Semiconj.iterate_right h k).comp_eq]

/--Notation for the product of two uniform neighborhoods.-/
def UniformityProd {Y : Type*} (U : Set (X × X)) (V : Set (Y × Y)) : Set ((X × Y) × X × Y) :=
  {W : (X × Y) × X × Y | (W.1.1, W.2.1) ∈ U ∧ (W.1.2, W.2.2) ∈ V}
/-Should be expanded and put into the library on uniform spaces.-/

theorem ball_prod {Y : Type*} (U : Set (X × X)) (V : Set (Y × Y)) (xy : X × Y) :
    ball xy (UniformityProd U V) = ball xy.1 U ×ˢ ball xy.2 V := by
  ext p
  simp only [ball, UniformityProd, mem_setOf_eq, mem_prod, mem_preimage]

theorem dynamical_uni_prod {Y : Type*} (S : X → X) (T : Y → Y) (U : Set (X × X)) (V : Set (Y × Y))
    (n : ℕ) :
    DynamicalUni (map S T) (UniformityProd U V) n =
    UniformityProd (DynamicalUni S U n) (DynamicalUni T V n) := by
  ext xy
  rw [dynamical_uni_mem]
  simp only [UniformityProd, mem_setOf_eq]
  rw [dynamical_uni_mem, dynamical_uni_mem, ← forall₂_and]
  refine forall₂_congr fun k _ ↦ ?_
  simp only [map_iterate, map_fst, map_snd]

end DynamicalUniformity

#lint
