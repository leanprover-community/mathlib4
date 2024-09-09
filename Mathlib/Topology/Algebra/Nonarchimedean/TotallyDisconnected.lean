/-
Copyright (c) 2024 Jou Glasheen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jou Glasheen, Kevin Buzzard
-/

import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Total Disconnectedness of Nonarchimedean Groups

In this file we introduce an instance of a nonarchimedean group as a totally disconnected
topological space. (The nonarchimedean group is not necessarily abelian.)

## Main results

- `NonarchimedeanGroup.non_singleton_set_disconnected` : in a nonarchimedean group, any subset which
                                                         contains two distinct points is
                                                         disconnected.
- `NonarchimedeanGroup.totally_disconnected_space`: instance of a nonarchimedean group as a totally
                                                    disconnected topological space.


## Notation

 - `G` : Nonarchimedean group.
 - `V` : Open subgroup which is a neighbourhood of the identity in `G`.

## References
Prop 2.3.9. of Gouvêa, F. Q. (2020) p-adic Numbers An Introduction. 3rd edition.
  Cham, Springer International Publishing.
-/

namespace NonarchimedeanGroup
open scoped Pointwise
variable (G : Type*) [TopologicalSpace G] [Group G] [TopologicalGroup G]
  [NonarchimedeanGroup G] [T2Space G]

-- #synth TotallyDisconnectedSpace G -- can't synth

/-open TopologicalSpace in
@[to_additive]
lemma open_subgroup_separating
    (t : G) (ht : t ≠ 1) : ∃ (A : Opens G),
    IsOpen A ∧ IsOpen B ∧ (y⁻¹ * x) ∈ A  ∧ 1 ∈ B ∧ Disjoint A B ∧
    ∃ V : OpenSubgroup G, (V : Set G) ⊆ B := by
  change (y = x) → False at hxy
  rw [← inv_mul_eq_one] at hxy
  apply t2_separation at hxy
  rcases hxy with ⟨A, B, opena, openb, diff, one, disj⟩
  use A
  use B
  refine ⟨opena, openb, diff, one, disj, ?_⟩
  · apply IsOpen.mem_nhds at one
    apply NonarchimedeanGroup.is_nonarchimedean at one
    exact one
    exact openb-/

-- I don't know if `Opens G` is better than `A : Set G` + `IsOpen A`.
open TopologicalSpace in
@[to_additive]
lemma open_subgroup_separating'
    (t : G) (ht : t ≠ 1) : ∃ (A : Opens G) (V : OpenSubgroup G),
    t ∈ A ∧ 1 ∈ V ∧ Disjoint A V := by
  rcases (t2_separation ht) with ⟨A, B, opena, openb, diff, one, disj⟩
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean B (IsOpen.mem_nhds openb one)
  exact ⟨⟨A, opena⟩, V, diff, one_mem V,
    fun _ ↦ by apply Set.disjoint_of_subset_right hV disj⟩

open scoped Pointwise
variable (x y U : Type*) (x y : G) (U : Set G)
(hx : x ∈ U) (hy :  y ∈ U) (V : OpenSubgroup G)

-- building the components of `¬ IsPreconnected U`:

@[to_additive]
lemma is_open_coset (y : G) (V : OpenSubgroup G)  :
    IsOpen (y • (V : Set G)) := IsOpen.smul (OpenSubgroup.isOpen V) y

@[to_additive]
lemma is_open_compl_coset' (y : G)
    (V : OpenSubgroup G) :
    IsOpen  (y • (V : Set G))ᶜ := by
  refine isOpen_compl_iff.mpr ?_
  refine IsClosed.smul ?hs y
  exact OpenSubgroup.isClosed V

@[to_additive]
lemma subset_coset_comp (y : G) (U : Set G) (V : OpenSubgroup G) :
    U ⊆  (y • (V : Set G)) ∪
      (y • (V : Set G))ᶜ := by
  simp only [Set.union_compl_self, Set.subset_univ]

@[to_additive]
lemma mem_subgroup_coset (x y : G) (hxy : y ≠ x) (V : OpenSubgroup G) :
    y ∈ (y • (V : Set G)) := by
  have omem : 1 ∈ (V : Set G) := one_mem V
  change (y = x) → False at hxy
  rw [← inv_mul_eq_one] at hxy
  refine Set.mem_smul_set_iff_inv_smul_mem.mpr ?h.a
  simp only [smul_eq_mul, inv_mul_cancel, SetLike.mem_coe]
  exact omem

@[to_additive]
  lemma non_empty_intersection_coset (x y : G) (U : Set G) (hy :  y ∈ U) (hxy : y ≠ x)
    (V : OpenSubgroup G) : (U ∩ (y • (V : Set G))).Nonempty := by
  refine Set.inter_nonempty.mpr ?_
  use y
  refine (Set.mem_inter_iff y U (y • ↑V)).mp ?h.a
  refine (Set.mem_inter_iff y U (y • ↑V)).mpr ?h.a.a
  constructor
  · exact hy
  · exact mem_subgroup_coset G x y hxy V

open TopologicalSpace in
@[to_additive]
lemma non_empty_intersection_compl_coset (x y : G) (U : Set G) (hx : x ∈ U)
    (A : Opens G) (quot : (y⁻¹ * x) ∈ A ) (V : OpenSubgroup G) (dva : Disjoint (V : Opens G) A) :
    (U ∩ ((y • (V : Set G))ᶜ)).Nonempty := by
  simp_rw [Set.inter_nonempty, Set.mem_compl_iff]
  use x, hx
  intro con
  rw [mem_leftCoset_iff y] at con
  simp only [Disjoint, le_bot_iff] at dva
  sorry
  -- have ne : (V : Opens G) ∩ A = ∅ → False := by
  -- exact Disjoint.subset_compl_right (Disjoint.symm dva) quot con

open TopologicalSpace in
@[to_additive]
lemma non_empty_intersection_compl_coset' (x y : G) (U : Set G) (hx : x ∈ U)
    (A : Opens G) (quot : (y⁻¹ * x) ∈ A ) (V : OpenSubgroup G) (dva : Disjoint (V : Set G) A) :
    (U ∩ ((y • (V : Set G))ᶜ)).Nonempty := by
  simp_rw [Set.inter_nonempty, Set.mem_compl_iff]
  use x, hx
  intro con
  rw [mem_leftCoset_iff y] at con
  have mem : (y⁻¹ * x) ∈ (V : Set G) ∩ A := Set.mem_inter con quot
  have subempty : (V : Set G) ∩ A = ∅ := Disjoint.inter_eq dva
  rw [subempty] at mem
  simp at mem

/-theorem Set.disjoint_iff {α : Type u} {s : Set α} {t : Set α} :
Disjoint s t ↔ s ∩ t ⊆ ∅-/

@[to_additive]
lemma intersection_of_intersection_of_complements_empty (y : G)  (U : Set G)
    (V : OpenSubgroup G) : ¬ (U ∩ ((y • (V : Set G)) ∩
    (y • (V : Set G))ᶜ)).Nonempty := by
  refine Set.not_nonempty_iff_eq_empty.mpr ?_
  simp only [Set.inter_compl_self, Set.inter_empty]

open TopologicalSpace in
/-- In a nonarchimedean group `G`, any set which contains two distinct points is disconnected. This
can be used to show that for any `x : G`, the connected component of `x` is `{x}`.-/
@[to_additive]
theorem non_singleton_set_disconnected
    (x y : G) (U : Set G)
    (hx : x ∈ U) (hy :  y ∈ U) (hxy : y ≠ x) : ¬ IsConnected U := by
  have exv : ∃ (A B : Opens G),
    (y⁻¹ * x) ∈ A  ∧ 1 ∈ B ∧ Disjoint A B ∧
    ∃ V : OpenSubgroup G, (V : Set G) ⊆ B   := by
      have ht : y⁻¹ * x ≠ 1 := by
        by_contra! con
        have hy : y⁻¹ * y = 1 := inv_mul_cancel y
        rw [← hy] at con
        have : x = y := by
          apply mul_left_cancel at con
          exact con
        exact hxy (id (Eq.symm this))
      have : ∃ (A : Opens G) (V : OpenSubgroup G), y⁻¹ * x ∈ A ∧ 1 ∈ V ∧ Disjoint A V := by
        exact open_subgroup_separating' G (y⁻¹ * x) ht
      rcases this with ⟨A , V, ha, hv, dav⟩
      use A , V
      constructor
      · exact ha
      · constructor
        · exact hv
        · constructor
          · exact dav
          · use V
            exact fun ⦃a⦄ a ↦ a
  rcases exv with ⟨A , B, ha, hb , dab, V, vb⟩
  have dva : Disjoint (V : Opens G) A   := by
    exact Disjoint.mono vb (fun ⦃a⦄ a ↦ a) (id (Disjoint.symm dab))
  have dva' : Disjoint (V : Set G) A := by
    apply Disjoint.mono vb (fun ⦃a⦄ a ↦ a)
    refine Disjoint.symm ?_
    convert dab
    constructor
    · exact fun a ↦ dab
    · intro h
      sorry
  obtain ⟨u , v, ou, ov, Uuv, Uu, Uv, emptyUuv⟩
      : ∃ u v : Set G, (IsOpen u) ∧ (IsOpen v) ∧ (U ⊆ u ∪ v) ∧ ((U ∩ u).Nonempty) ∧
      ((U ∩ v).Nonempty) ∧ (¬(U ∩ (u ∩ v)).Nonempty) := by
    use (y • (V : Set G)) , (y • (V : Set G))ᶜ
    refine ⟨is_open_coset G y V, is_open_compl_coset' G y V, subset_coset_comp G y U V,
        non_empty_intersection_coset G x y U hy hxy V,
        non_empty_intersection_compl_coset' G x y U hx A ha V dva',
        intersection_of_intersection_of_complements_empty G y U V⟩
  rintro ⟨_, h2⟩
  exact emptyUuv <| ((((h2 u v ou) ov) Uuv) Uu) Uv

open TopologicalSpace in
@[to_additive]
theorem non_singleton_set_disconnected'
    (x y : G) (U : Set G)
    (hx : x ∈ U) (hy :  y ∈ U) (hxy : y ≠ x) : ¬ IsConnected U := by
  have exv : ∃ (A B : Opens G),
    (y⁻¹ * x) ∈ A  ∧ 1 ∈ B ∧ Disjoint (A : Set G) B ∧
    ∃ V : OpenSubgroup G, (V : Set G) ⊆ B   := by
      have ht : y⁻¹ * x ≠ 1 := by
        by_contra! con
        have hy : y⁻¹ * y = 1 := inv_mul_cancel y
        rw [← hy] at con
        have : x = y := by
          apply mul_left_cancel at con
          exact con
        exact hxy (id (Eq.symm this))
      have : ∃ (A : Opens G) (V : OpenSubgroup G), y⁻¹ * x ∈ A ∧ 1 ∈ V ∧ Disjoint A V := by
        exact open_subgroup_separating' G (y⁻¹ * x) ht
      rcases this with ⟨A , V, ha, hv, dav⟩
      use A , V
      constructor
      · exact ha
      · constructor
        · exact hv
        · constructor
          · simp only [OpenSubgroup.coe_toOpens]
            unfold Disjoint
            intro x ha hv
            unfold Disjoint at dav
            have habot : ⊥ ≤ A := OrderBot.bot_le A
            have hvbot : ⊥ ≤ (V : Opens G) := OrderBot.bot_le ↑V
            by_contra! con
            have hx : x ≤ (A : Opens G) := by exact ha
            specialize dav habot hvbot
            -- refine Set.disjoint_iff.mpr ?h.right.right.left.a dav
            sorry
          · use V
            exact fun ⦃a⦄ a ↦ a
  rcases exv with ⟨A , B, ha, hb , dab, V, vb⟩
  -- have dva : Disjoint (V : Opens G) A   := by sorry
   -- exact Disjoint.mono vb (fun ⦃a⦄ a ↦ a) (id (Disjoint.symm dab))
  have dva' : Disjoint (V : Set G) A := by
    apply Disjoint.mono vb (fun ⦃a⦄ a ↦ a)
    refine Disjoint.symm ?_
    convert dab
  obtain ⟨u , v, ou, ov, Uuv, Uu, Uv, emptyUuv⟩
      : ∃ u v : Set G, (IsOpen u) ∧ (IsOpen v) ∧ (U ⊆ u ∪ v) ∧ ((U ∩ u).Nonempty) ∧
      ((U ∩ v).Nonempty) ∧ (¬(U ∩ (u ∩ v)).Nonempty) := by
    use (y • (V : Set G)) , (y • (V : Set G))ᶜ
    refine ⟨is_open_coset G y V, is_open_compl_coset' G y V, subset_coset_comp G y U V,
        non_empty_intersection_coset G x y U hy hxy V,
        non_empty_intersection_compl_coset' G x y U hx A ha V dva',
        intersection_of_intersection_of_complements_empty G y U V⟩
  rintro ⟨_, h2⟩
  exact emptyUuv <| ((((h2 u v ou) ov) Uuv) Uu) Uv

-- should be elsewhere
lemma _root_.mem_unique_to_singleton {X : Type*} {U : Set X} {x : X} (hx : x ∈ U)
    (h : ∀ y : X, y ∈ U → y = x) : U = {x} := by
  ext
  constructor <;> simp_all

/-- Instance of a nonarchimedean group as a totally disconnected topological space
(TotallyDisconnectedSpace). (The nonarchimedean group is not necessarily abelian.)-/
@[to_additive]
instance totally_disconnected_space : TotallyDisconnectedSpace G := by
      rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
      intro x
      by_contra con
      obtain ⟨y, hyu, hneq⟩ : ∃ y : G, (y ∈ connectedComponent x) ∧ (y ≠ x) := by
        by_contra! con2
        exact con <| mem_unique_to_singleton mem_connectedComponent con2
      exact non_singleton_set_disconnected G x y (connectedComponent x) mem_connectedComponent hyu
        hneq isConnected_connectedComponent

end NonarchimedeanGroup

--#lint fails
