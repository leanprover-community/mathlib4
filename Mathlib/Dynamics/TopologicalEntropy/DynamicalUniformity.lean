/-
Copyright (c) 2024 Damien Thomine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damien Thomine, Pietro Monticone
-/
import Mathlib.Tactic
import Mathlib.Topology.UniformSpace.Compact
import BET.TopologicalEntropy.Miscellaneous.Misc

/-!
# Dynamical uniformites
We implement Bowen-Dinaburg's definitions of the topological entropy. The most common version
of this definition uses metric spaces and then defines dynamical balls. To get a more flexible
version of topological entropy, we work instead with uniform spaces. Dynamical balls are
replaced by (what I called) dynamical uniformities.

The nomenclature may be changed.
-/

namespace DynamicalUniformity

open Misc UniformSpace

/--Shorthand for the space of uniform neighborhoods--/
notation "𝓤" => uniformity

/-- A dynamical uniform neighborhood is the uniform space version of dynamical balls.-/
def DynamicalUni {X : Type _} (T : X → X) (U : Set (X × X)) (n : ℕ) : Set (X × X) :=
  ⋂ (k : ℕ) (_ : k < n), (Prod.map T T)^[k] ⁻¹' U

theorem dynamical_uni_mem {X : Type _} (T : X → X) (U : Set (X × X)) (n : ℕ) (x y : X) :
    (x, y) ∈ DynamicalUni T U n ↔ ∀ k < n, (T^[k] x, T^[k] y) ∈ U := by
  simp only [DynamicalUni, Function.iterate_prod_map, Set.mem_preimage, Set.mem_iInter,
    Prod_map]

theorem dynamical_uni_iff {X : Type _} (T : X → X) (U : Set (X × X)) (n : ℕ) (x y : X) :
    y ∈ ball x (DynamicalUni T U n) ↔ ∀ k < n, T^[k] y ∈ ball (T^[k] x) U := by
  simp only [ball, Set.mem_preimage]
  exact dynamical_uni_mem T U n x y

theorem dynamical_of_uni_is_uni {X : Type _} [UniformSpace X] {T : X → X}
    (h : UniformContinuous T) {U : Set (X × X)} (U_uni : U ∈ 𝓤 X) (n : ℕ) :
    DynamicalUni T U n ∈ 𝓤 X := by
  have : DynamicalUni T U n = ⋂ (k : ℕ) (_ : k ∈ Set.Ico 0 n), (Prod.map T T)^[k] ⁻¹' U := by
    simp only [DynamicalUni, Function.iterate_prod_map, Set.mem_Ico, zero_le, true_and]
  rw [this]; clear this
  apply (Filter.biInter_mem (Set.finite_Ico 0 n)).2
  intro k _
  rw [prod_map_ite T T k]
  exact uniformContinuous_def.1 (uniformContinuous_ite T k h) U U_uni

theorem dynamical_of_rfl_is_rfl {X : Type _} (T : X → X) {U : Set (X × X)}
    (h : idRel ⊆ U) (n : ℕ) :
    idRel ⊆ (DynamicalUni T U n) := by
  simp only [DynamicalUni, Function.iterate_prod_map, Set.subset_iInter_iff, idRel_subset,
    Set.mem_preimage, Prod_map]
  intros _ _ _
  apply h
  simp only [mem_idRel]

theorem dynamical_of_symm_is_symm {X : Type _} (T : X → X) {U : Set (X × X)}
    (h : SymmetricRel U) (n : ℕ) :
    SymmetricRel (DynamicalUni T U n) := by
  ext xy
  simp only [DynamicalUni, Function.iterate_prod_map, Set.mem_preimage, Set.mem_iInter, Prod_map,
    Prod.fst_swap, Prod.snd_swap]
  unfold SymmetricRel at h
  nth_rewrite 1 [← h]
  simp only [Set.mem_preimage, Prod.swap_prod_mk]

theorem dynamical_of_comp_is_comp {X : Type _} (T : X → X) (U V : Set (X × X)) (n : ℕ) :
    compRel (DynamicalUni T U n) (DynamicalUni T V n) ⊆ DynamicalUni T (compRel U V) n := by
  simp only [DynamicalUni, Function.iterate_prod_map, Set.subset_iInter_iff]
  intro k k_lt_n xy xy_in_comp
  simp only [compRel, Set.mem_iInter, Set.mem_preimage, Prod_map, Set.mem_setOf_eq] at xy_in_comp
  simp only [Set.mem_preimage, Prod_map]
  rcases xy_in_comp with ⟨z, hz1, hz2⟩
  specialize hz1 k k_lt_n
  specialize hz2 k k_lt_n
  exact mem_ball_comp hz1 hz2

theorem dynamical_of_open_is_open {X : Type _} [TopologicalSpace X] {T : X → X}
    (T_cont : Continuous T) {U : Set (X × X)} (U_open : IsOpen U) (n : ℕ) :
    IsOpen (DynamicalUni T U n) := by
  have : DynamicalUni T U n = ⋂ (k : ℕ) (_ : k ∈ Set.Ico 0 n), (Prod.map T T)^[k] ⁻¹' U := by
    simp only [DynamicalUni, Function.iterate_prod_map, Set.mem_Ico, zero_le, true_and]
  rw [this]; clear this
  apply Set.Finite.isOpen_biInter (Set.finite_Ico 0 n)
  intro k _
  apply continuous_def.1 _ U U_open
  rw [prod_map_ite]
  apply Continuous.prod_map
  repeat' exact Continuous.iterate T_cont k

theorem dynamical_uni_monotone_uni {X : Type _} (T : X → X) (n : ℕ) :
    Monotone (fun U : Set (X × X) ↦ DynamicalUni T U n) := by
  intro U V U_sub_V
  apply Set.iInter₂_mono
  intro k _
  exact Set.preimage_mono U_sub_V

theorem dynamical_uni_antitone_time {X : Type _} (T : X → X) (U : Set (X × X)) :
    Antitone (fun n : ℕ ↦ DynamicalUni T U n) := by
  intro m n m_le_n
  apply Set.iInter_mono
  intro k
  apply Set.iInter_mono'
  intro k_lt_m
  use LT.lt.trans_le k_lt_m m_le_n

@[simp]
theorem dynamical_time_zero {X : Type _} (T : X → X) (U : Set (X × X)) :
    DynamicalUni T U 0 = Set.univ := by
  simp only [DynamicalUni, not_lt_zero', Function.iterate_prod_map, Set.iInter_of_empty,
    Set.iInter_univ]

@[simp]
theorem dynamical_time_one {X : Type _} (T : X → X) (U : Set (X × X)) :
    DynamicalUni T U 1 = U := by
  simp only [DynamicalUni, Nat.lt_one_iff, Function.iterate_prod_map, Set.iInter_iInter_eq_left,
    Function.iterate_zero, Prod.map_id, Set.preimage_id_eq, id_eq]

theorem inter_of_dynamical_balls {X : Type _} (T : X → X) (n : ℕ) {U : Set (X × X)}
    (U_symm : SymmetricRel U) (x y : X) :
    (ball x (DynamicalUni T U n) ∩ ball y (DynamicalUni T U n)).Nonempty →
    x ∈ ball y (DynamicalUni T (compRel U U) n) := by
  intro hxy
  rcases hxy with ⟨z, z_in_Bx, z_in_By⟩
  rw [mem_ball_symmetry (dynamical_of_symm_is_symm T U_symm n)] at z_in_Bx
  apply dynamical_of_comp_is_comp T U U n
  exact mem_ball_comp z_in_By z_in_Bx

/--Preimages of dynamical uniformities under semiconjugacies.-/
theorem preimage_of_dynamical_uni {X Y : Type _} {S : X → X} {T : Y → Y} {φ : X → Y}
    (h : Function.Semiconj φ S T) (U : Set (Y × Y)) (n : ℕ) :
    (Prod.map φ φ)⁻¹' (DynamicalUni T U n) = DynamicalUni S ((Prod.map φ φ)⁻¹' U) n := by
  unfold DynamicalUni
  rw [Set.preimage_iInter₂]
  apply Set.iInter₂_congr
  intros k k_lt_n; clear k_lt_n
  rw [← Set.preimage_comp, ← Set.preimage_comp, prod_map_ite S S k, prod_map_ite T T k,
    Prod.map_comp_map, Prod.map_comp_map, (Function.Semiconj.iterate_right h k).comp_eq]

/--Notation for the product of two uniform neighborhoods.-/
def UniformityProd {X Y : Type _} (U : Set (X × X)) (V : Set (Y × Y)) : Set ((X × Y) × X × Y) :=
  {W : (X × Y) × X × Y | (W.1.1, W.2.1) ∈ U ∧ (W.1.2, W.2.2) ∈ V}
/-Should be expanded and put into the library on uniform spaces.-/

theorem ball_prod {X Y : Type _} (U : Set (X × X)) (V : Set (Y × Y)) (xy : X × Y) :
    ball xy (UniformityProd U V) = ball xy.1 U ×ˢ ball xy.2 V := by
  ext p
  simp only [ball, UniformityProd, Set.preimage_setOf_eq, Set.mem_setOf_eq, Set.mem_prod,
    Set.mem_preimage]

theorem dynamical_uni_prod {X Y : Type _} (S : X → X) (T : Y → Y) (U : Set (X × X))
    (V : Set (Y × Y)) (n : ℕ) :
    DynamicalUni (Prod.map S T) (UniformityProd U V) n =
    UniformityProd (DynamicalUni S U n) (DynamicalUni T V n) := by
  apply Set.Subset.antisymm
  · intro p p_in_uniformity
    simp only [UniformityProd, DynamicalUni, Function.iterate_prod_map, Set.mem_iInter,
      Set.mem_preimage, Prod_map, Set.mem_setOf_eq]
    simp only [DynamicalUni, Function.iterate_prod_map, UniformityProd, Set.preimage_setOf_eq,
      Prod_map, Set.mem_iInter, Set.mem_setOf_eq] at p_in_uniformity
    constructor
    · intro k k_lt_n
      specialize p_in_uniformity k k_lt_n
      exact p_in_uniformity.1
    · intro k k_lt_n
      specialize p_in_uniformity k k_lt_n
      exact p_in_uniformity.2
  · intro p p_in_product
    simp only [DynamicalUni, Function.iterate_prod_map, UniformityProd, Set.preimage_setOf_eq,
      Prod_map, Set.mem_iInter, Set.mem_setOf_eq]
    intro k k_lt_n
    cases' p_in_product with p_in_U p_in_V
    simp only [DynamicalUni, Function.iterate_prod_map, Set.mem_iInter, Set.mem_preimage,
      Prod_map] at p_in_U
    simp only [DynamicalUni, Function.iterate_prod_map, Set.mem_iInter, Set.mem_preimage,
      Prod_map] at p_in_V
    specialize p_in_U k k_lt_n
    specialize p_in_V k k_lt_n
    exact ⟨p_in_U, p_in_V⟩

end DynamicalUniformity

#lint
