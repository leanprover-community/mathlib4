/-
Copyright (c) 2021 Ashwin Iyengar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Ashwin Iyengar, Patrick Massot
-/
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Ring.Basic

#align_import topology.algebra.nonarchimedean.basic from "leanprover-community/mathlib"@"83f81aea33931a1edb94ce0f32b9a5d484de6978"

/-!
# Nonarchimedean Topology

In this file we set up the theory of nonarchimedean topological groups and rings.

A nonarchimedean group is a topological group whose topology admits a basis of
open neighborhoods of the identity element in the group consisting of open subgroups.
A nonarchimedean ring is a topological ring whose underlying topological (additive)
group is nonarchimedean.

## Definitions

- `NonarchimedeanAddGroup`: nonarchimedean additive group.
- `NonarchimedeanGroup`: nonarchimedean multiplicative group.
- `NonarchimedeanRing`: nonarchimedean ring.

-/


open Pointwise

/-- A topological additive group is nonarchimedean if every neighborhood of 0
  contains an open subgroup. -/
class NonarchimedeanAddGroup (G : Type*) [AddGroup G] [TopologicalSpace G] extends
  TopologicalAddGroup G : Prop where
  is_nonarchimedean : ∀ U ∈ nhds (0 : G), ∃ V : OpenAddSubgroup G, (V : Set G) ⊆ U
#align nonarchimedean_add_group NonarchimedeanAddGroup

/-- A topological group is nonarchimedean if every neighborhood of 1 contains an open subgroup. -/
@[to_additive]
class NonarchimedeanGroup (G : Type*) [Group G] [TopologicalSpace G] extends TopologicalGroup G :
  Prop where
  is_nonarchimedean : ∀ U ∈ nhds (1 : G), ∃ V : OpenSubgroup G, (V : Set G) ⊆ U
#align nonarchimedean_group NonarchimedeanGroup

/-- A topological ring is nonarchimedean if its underlying topological additive
  group is nonarchimedean. -/
class NonarchimedeanRing (R : Type*) [Ring R] [TopologicalSpace R] extends TopologicalRing R :
  Prop where
  is_nonarchimedean : ∀ U ∈ nhds (0 : R), ∃ V : OpenAddSubgroup R, (V : Set R) ⊆ U
#align nonarchimedean_ring NonarchimedeanRing

-- see Note [lower instance priority]
/-- Every nonarchimedean ring is naturally a nonarchimedean additive group. -/
instance (priority := 100) NonarchimedeanRing.to_nonarchimedeanAddGroup (R : Type*) [Ring R]
    [TopologicalSpace R] [t : NonarchimedeanRing R] : NonarchimedeanAddGroup R :=
  { t with }
#align nonarchimedean_ring.to_nonarchimedean_add_group NonarchimedeanRing.to_nonarchimedeanAddGroup

namespace NonarchimedeanGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [NonarchimedeanGroup G]

variable {H : Type*} [Group H] [TopologicalSpace H] [TopologicalGroup H]

variable {K : Type*} [Group K] [TopologicalSpace K] [NonarchimedeanGroup K]

/-- If a topological group embeds into a nonarchimedean group, then it is nonarchimedean. -/
@[to_additive]
theorem nonarchimedean_of_emb (f : G →* H) (emb : OpenEmbedding f) : NonarchimedeanGroup H :=
  { is_nonarchimedean := fun U hU =>
      have h₁ : f ⁻¹' U ∈ nhds (1 : G) := by
        apply emb.continuous.tendsto
        rwa [f.map_one]
      let ⟨V, hV⟩ := is_nonarchimedean (f ⁻¹' U) h₁
      ⟨{ Subgroup.map f V with isOpen' := emb.isOpenMap _ V.isOpen }, Set.image_subset_iff.2 hV⟩ }
#align nonarchimedean_group.nonarchimedean_of_emb NonarchimedeanGroup.nonarchimedean_of_emb
#align nonarchimedean_add_group.nonarchimedean_of_emb NonarchimedeanAddGroup.nonarchimedean_of_emb

/-- An open neighborhood of the identity in the cartesian product of two nonarchimedean groups
contains the cartesian product of an open neighborhood in each group. -/
@[to_additive NonarchimedeanAddGroup.prod_subset "An open neighborhood of the identity in
the cartesian product of two nonarchimedean groups contains the cartesian product of
an open neighborhood in each group."]
theorem prod_subset {U} (hU : U ∈ nhds (1 : G × K)) :
    ∃ (V : OpenSubgroup G) (W : OpenSubgroup K), (V : Set G) ×ˢ (W : Set K) ⊆ U := by
  erw [nhds_prod_eq, Filter.mem_prod_iff] at hU
  rcases hU with ⟨U₁, hU₁, U₂, hU₂, h⟩
  cases' is_nonarchimedean _ hU₁ with V hV
  cases' is_nonarchimedean _ hU₂ with W hW
  use V; use W
  rw [Set.prod_subset_iff]
  intro x hX y hY
  exact Set.Subset.trans (Set.prod_mono hV hW) h (Set.mem_sep hX hY)
#align nonarchimedean_group.prod_subset NonarchimedeanGroup.prod_subset
#align nonarchimedean_add_group.prod_subset NonarchimedeanAddGroup.prod_subset

/-- An open neighborhood of the identity in the cartesian square of a nonarchimedean group
contains the cartesian square of an open neighborhood in the group. -/
@[to_additive NonarchimedeanAddGroup.prod_self_subset "An open neighborhood of the identity in
the cartesian square of a nonarchimedean group contains the cartesian square of
an open neighborhood in the group."]
theorem prod_self_subset {U} (hU : U ∈ nhds (1 : G × G)) :
    ∃ V : OpenSubgroup G, (V : Set G) ×ˢ (V : Set G) ⊆ U :=
  let ⟨V, W, h⟩ := prod_subset hU
  ⟨V ⊓ W, by refine' Set.Subset.trans (Set.prod_mono _ _) ‹_› <;> simp⟩
#align nonarchimedean_group.prod_self_subset NonarchimedeanGroup.prod_self_subset
#align nonarchimedean_add_group.prod_self_subset NonarchimedeanAddGroup.prod_self_subset

/-- The cartesian product of two nonarchimedean groups is nonarchimedean. -/
@[to_additive "The cartesian product of two nonarchimedean groups is nonarchimedean."]
instance : NonarchimedeanGroup (G × K)
    where is_nonarchimedean U hU :=
    let ⟨V, W, h⟩ := prod_subset hU
    ⟨V.prod W, ‹_›⟩

end NonarchimedeanGroup

namespace NonarchimedeanRing

open NonarchimedeanRing

open NonarchimedeanAddGroup

variable {R S : Type*}

variable [Ring R] [TopologicalSpace R] [NonarchimedeanRing R]

variable [Ring S] [TopologicalSpace S] [NonarchimedeanRing S]

/-- The cartesian product of two nonarchimedean rings is nonarchimedean. -/
instance : NonarchimedeanRing (R × S)
    where is_nonarchimedean := NonarchimedeanAddGroup.is_nonarchimedean

/-- Given an open subgroup `U` and an element `r` of a nonarchimedean ring, there is an open
  subgroup `V` such that `r • V` is contained in `U`. -/
theorem left_mul_subset (U : OpenAddSubgroup R) (r : R) :
    ∃ V : OpenAddSubgroup R, r • (V : Set R) ⊆ U :=
  ⟨U.comap (AddMonoidHom.mulLeft r) (continuous_mul_left r), (U : Set R).image_preimage_subset _⟩
#align nonarchimedean_ring.left_mul_subset NonarchimedeanRing.left_mul_subset

/-- An open subgroup of a nonarchimedean ring contains the square of another one. -/
theorem mul_subset (U : OpenAddSubgroup R) : ∃ V : OpenAddSubgroup R, (V : Set R) * V ⊆ U := by
  let ⟨V, H⟩ :=
    prod_self_subset
      (IsOpen.mem_nhds (IsOpen.preimage continuous_mul U.isOpen)
        (by simpa only [Set.mem_preimage, SetLike.mem_coe, Prod.snd_zero,
            mul_zero] using U.zero_mem))
  use V
  rintro v ⟨a, b, ha, hb, hv⟩
  have hy := H (Set.mk_mem_prod ha hb)
  simp only [Set.mem_preimage, SetLike.mem_coe, hv] at hy
  rw [SetLike.mem_coe]
  exact hy
#align nonarchimedean_ring.mul_subset NonarchimedeanRing.mul_subset

end NonarchimedeanRing
