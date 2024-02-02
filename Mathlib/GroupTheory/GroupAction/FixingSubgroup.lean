/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.GroupTheory.Subgroup.Actions
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.FixedPoints

#align_import group_theory.group_action.fixing_subgroup from "leanprover-community/mathlib"@"f93c11933efbc3c2f0299e47b8ff83e9b539cbf6"

/-!

# Fixing submonoid, fixing subgroup of an action

In the presence of an action of a monoid or a group,
this file defines the fixing submonoid or the fixing subgroup,
and relates it to the set of fixed points via a Galois connection.

## Main definitions

* `fixingSubmonoid M s` : in the presence of `MulAction M α` (with `Monoid M`)
  it is the `Submonoid M` consisting of elements which fix `s : Set α` pointwise.

* `fixingSubmonoid_fixedPoints_gc M α` is the `GaloisConnection`
  that relates `fixingSubmonoid` with `fixedPoints`.

* `fixingSubgroup M s` : in the presence of `MulAction M α` (with `Group M`)
  it is the `Subgroup M` consisting of elements which fix `s : Set α` pointwise.

* `fixingSubgroup_fixedPoints_gc M α` is the `GaloisConnection`
  that relates `fixingSubgroup` with `fixedPoints`.

TODO :

* Maybe other lemmas are useful

* Treat semigroups ?

* add `to_additive` for the various lemmas

-/


section Monoid

open MulAction

variable (M : Type*) {α : Type*} [Monoid M] [MulAction M α]

/-- The submonoid fixing a set under a `MulAction`. -/
@[to_additive " The additive submonoid fixing a set under an `AddAction`. "]
def fixingSubmonoid (s : Set α) : Submonoid M
    where
  carrier := { ϕ : M | ∀ x : s, ϕ • (x : α) = x }
  one_mem' _ := one_smul _ _
  mul_mem' {x y} hx hy z := by rw [mul_smul, hy z, hx z]
#align fixing_submonoid fixingSubmonoid
#align fixing_add_submonoid fixingAddSubmonoid

theorem mem_fixingSubmonoid_iff {s : Set α} {m : M} :
    m ∈ fixingSubmonoid M s ↔ ∀ y ∈ s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩
#align mem_fixing_submonoid_iff mem_fixingSubmonoid_iff

variable (α)

/-- The Galois connection between fixing submonoids and fixed points of a monoid action -/
theorem fixingSubmonoid_fixedPoints_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubmonoid M)
      ((fun P : Submonoid M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun _s _P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩
#align fixing_submonoid_fixed_points_gc fixingSubmonoid_fixedPoints_gc

theorem fixingSubmonoid_antitone : Antitone fun s : Set α => fixingSubmonoid M s :=
  (fixingSubmonoid_fixedPoints_gc M α).monotone_l
#align fixing_submonoid_antitone fixingSubmonoid_antitone

theorem fixedPoints_antitone : Antitone fun P : Submonoid M => fixedPoints P α :=
  (fixingSubmonoid_fixedPoints_gc M α).monotone_u.dual_left
#align fixed_points_antitone fixedPoints_antitone

/-- Fixing submonoid of union is intersection -/
theorem fixingSubmonoid_union {s t : Set α} :
    fixingSubmonoid M (s ∪ t) = fixingSubmonoid M s ⊓ fixingSubmonoid M t :=
  (fixingSubmonoid_fixedPoints_gc M α).l_sup
#align fixing_submonoid_union fixingSubmonoid_union

/-- Fixing submonoid of iUnion is intersection -/
theorem fixingSubmonoid_iUnion {ι : Sort*} {s : ι → Set α} :
    fixingSubmonoid M (⋃ i, s i) = ⨅ i, fixingSubmonoid M (s i) :=
  (fixingSubmonoid_fixedPoints_gc M α).l_iSup
#align fixing_submonoid_Union fixingSubmonoid_iUnion

/-- Fixed points of sup of submonoids is intersection -/
theorem fixedPoints_submonoid_sup {P Q : Submonoid M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α ∩ fixedPoints Q α :=
  (fixingSubmonoid_fixedPoints_gc M α).u_inf
#align fixed_points_submonoid_sup fixedPoints_submonoid_sup

/-- Fixed points of iSup of submonoids is intersection -/
theorem fixedPoints_submonoid_iSup {ι : Sort*} {P : ι → Submonoid M} :
    fixedPoints (↥(iSup P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixingSubmonoid_fixedPoints_gc M α).u_iInf
#align fixed_points_submonoid_supr fixedPoints_submonoid_iSup

end Monoid

section Group

open MulAction

variable (M : Type*) {α : Type*} [Group M] [MulAction M α]

/-- The subgroup fixing a set under a `MulAction`. -/
@[to_additive " The additive subgroup fixing a set under an `AddAction`. "]
def fixingSubgroup (s : Set α) : Subgroup M :=
  { fixingSubmonoid M s with inv_mem' := fun hx z => by rw [inv_smul_eq_iff, hx z] }
#align fixing_subgroup fixingSubgroup
#align fixing_add_subgroup fixingAddSubgroup

/--
`G•[s]` is notation for `fixingSubgroup G s`; this notation is only available if the `MulAction`
scope is opened.
-/
scoped[MulAction] notation:max G "•[" s "]" => fixingSubgroup G s

/--
`G+ᵥ[s]` is notation for `fixingAddSubgroup G s`; this notation is only available if the `AddAction`
scope is opened.
-/
scoped[AddAction] notation:max G "+ᵥ[" s "]" => fixingAddSubgroup G s

@[to_additive]
theorem mem_fixingSubgroup_iff {s : Set α} {m : G} : m ∈ fixingSubgroup G s ↔ ∀ y ∈ s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩
#align mem_fixing_subgroup_iff mem_fixingSubgroup_iff

theorem mem_fixingSubgroup_iff_subset_fixedBy {s : Set α} {m : M} :
    m ∈ fixingSubgroup M s ↔ s ⊆ fixedBy α m := by
  simp_rw [mem_fixingSubgroup_iff, Set.subset_def, mem_fixedBy]

theorem mem_fixingSubgroup_compl_iff_movedBy_subset {s : Set α} {m : M} :
    m ∈ fixingSubgroup M sᶜ ↔ (fixedBy α m)ᶜ ⊆ s := by
  rw [mem_fixingSubgroup_iff_subset_fixedBy, Set.compl_subset_comm]

variable (α)

/-- The Galois connection between fixing subgroups and fixed points of a group action -/
theorem fixingSubgroup_fixedPoints_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubgroup M)
      ((fun P : Subgroup M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun _s _P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩
#align fixing_subgroup_fixed_points_gc fixingSubgroup_fixedPoints_gc

theorem fixingSubgroup_antitone : Antitone (fixingSubgroup M : Set α → Subgroup M) :=
  (fixingSubgroup_fixedPoints_gc M α).monotone_l
#align fixing_subgroup_antitone fixingSubgroup_antitone

theorem fixedPoints_subgroup_antitone : Antitone fun P : Subgroup M => fixedPoints P α :=
  (fixingSubgroup_fixedPoints_gc M α).monotone_u.dual_left
#align fixed_points_subgroup_antitone fixedPoints_subgroup_antitone

@[simp]
theorem fixingSubgroup_empty : G•[(∅ : Set α)] = ⊤ := by
  ext g
  simp_rw [mem_fixingSubgroup_iff, Set.mem_empty_iff_false, IsEmpty.forall_iff, implies_true,
    Subgroup.mem_top]

variable {α}

/-- Fixing subgroup of union is intersection -/
theorem fixingSubgroup_union {s t : Set α} :
    fixingSubgroup M (s ∪ t) = fixingSubgroup M s ⊓ fixingSubgroup M t :=
  (fixingSubgroup_fixedPoints_gc M α).l_sup
#align fixing_subgroup_union fixingSubgroup_union

/-- Fixing subgroup of iUnion is intersection -/
theorem fixingSubgroup_iUnion {ι : Sort*} {s : ι → Set α} :
    fixingSubgroup M (⋃ i, s i) = ⨅ i, fixingSubgroup M (s i) :=
  (fixingSubgroup_fixedPoints_gc M α).l_iSup
#align fixing_subgroup_Union fixingSubgroup_iUnion

/-- Fixed points of sup of subgroups is intersection -/
theorem fixedPoints_subgroup_sup {P Q : Subgroup M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α ∩ fixedPoints Q α :=
  (fixingSubgroup_fixedPoints_gc M α).u_inf
#align fixed_points_subgroup_sup fixedPoints_subgroup_sup

/-- Fixed points of iSup of subgroups is intersection -/
theorem fixedPoints_subgroup_iSup {ι : Sort*} {P : ι → Subgroup M} :
    fixedPoints (↥(iSup P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixingSubgroup_fixedPoints_gc M α).u_iInf
#align fixed_points_subgroup_supr fixedPoints_subgroup_iSup

/-- The orbit of the fixing subgroup of `sᶜ` (ie. the moving subgroup of `s`) is a subset of `s` -/
theorem orbit_fixingSubgroup_compl_subset {s : Set α} {a : α} (a_in_s : a ∈ s) :
    MulAction.orbit (fixingSubgroup M sᶜ) a ⊆ s := by
  intro b b_in_orbit
  let ⟨⟨g, g_fixing⟩, g_eq⟩ := MulAction.mem_orbit_iff.mp b_in_orbit
  rw [Submonoid.mk_smul] at g_eq
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at g_fixing
<<<<<<< HEAD
  rwa [← g_eq, smul_mem_of_set_mem_fixedBy (set_mem_fixedBy_of_movedBy_subset g_fixing)]
||||||| parent of 4c67043ad2 (feat(Topology/Algebra/Group/LocallyDense): finish proving lemma 2.2)
  rwa [← g_eq, ← smul_mem_of_set_mem_fixedBy (set_mem_fixedBy_of_movedBy_subset g_fixing)]

/--
The fixing subgroup of a set `s` is disjoint from the fixing subgroup of `sᶜ`
if the action is faithful.
-/
theorem fixingSubgroup_compl_disjoint [FaithfulSMul G α] (s : Set α) :
    Disjoint (fixingSubgroup G s) (fixingSubgroup G sᶜ) := by
  rw [Subgroup.disjoint_def]
  intro x x_in_fs x_in_fsc
  rw [mem_fixingSubgroup_iff_subset_fixedBy] at x_in_fs
  rw [mem_fixingSubgroup_iff_subset_fixedBy] at x_in_fsc
  rw [← fixedBy_eq_univ_iff_eq_one (α := α), eq_comm]
  apply subset_antisymm _ (Set.subset_univ _)
  rw [← Set.union_compl_self s]
  apply Set.union_subset <;> assumption

theorem fixingSubgroup_smul (s : Set α) (g : G) : G•[g • s] = MulAut.conj g • G•[s] := by
  ext h
  rw [mem_fixingSubgroup_iff_subset_fixedBy, Set.set_smul_subset_iff, smul_fixedBy, inv_inv,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_fixingSubgroup_iff_subset_fixedBy,
    MulAut.smul_def, MulAut.conj_inv_apply]

section Faithful

variable [FaithfulSMul G α]

@[simp]
theorem fixingSubgroup_univ : G•[(Set.univ : Set α)] = ⊥ := by
  ext x
  rw [Subgroup.mem_bot, mem_fixingSubgroup_iff_subset_fixedBy, Set.univ_subset_iff,
    fixedBy_eq_univ_iff_eq_one]

theorem not_mem_fixingSubgroup_compl_of_mem_fixingSubgroup (s : Set α) {g : G} (g_ne_one : g ≠ 1)
    (g_in_subgroup : g ∈ G•[s]) : g ∉ G•[sᶜ] := by
  intro h₁
  apply g_ne_one
  apply Subgroup.disjoint_def.mp (fixingSubgroup_compl_disjoint G s) <;> assumption

theorem commute_of_fixingSubgroup_compl_of_disjoint {g h : G} {s : Set α}
    (g_in_subgroup : g ∈ G•[sᶜ]) (disjoint_movedBy : Disjoint s (fixedBy α h)ᶜ) :
    Commute g h := by
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at g_in_subgroup
  have s_subset_fixedBy : s ⊆ fixedBy α h := by
    rwa [← Set.disjoint_compl_right_iff_subset]
  have movedBy_subset_sc : (fixedBy α h)ᶜ ⊆ sᶜ := by
    rwa [← Set.disjoint_compl_left_iff_subset, compl_compl]

  refine eq_of_smul_eq_smul fun x: α => ?comm_eq

  by_cases x ∈ s
  case pos x_in_s =>
    rw [mul_smul, mul_smul, s_subset_fixedBy x_in_s]
    rw [smul_mem_of_set_mem_fixedBy (set_mem_fixedBy_of_movedBy_subset g_in_subgroup)] at x_in_s
    rw [s_subset_fixedBy x_in_s]
  case neg x_notin_s =>
    rw [Set.compl_subset_comm] at g_in_subgroup
    rw [mul_smul, mul_smul, g_in_subgroup x_notin_s]

    by_cases x ∈ fixedBy α h
    case pos x_fixed =>
      rw [x_fixed, g_in_subgroup x_notin_s]
    case neg x_moved =>
      rw [← smul_mem_fixedBy_iff_mem_fixedBy] at x_moved
      rw [g_in_subgroup (movedBy_subset_sc x_moved)]

end Faithful
=======
  rwa [← g_eq, ← smul_mem_of_set_mem_fixedBy (set_mem_fixedBy_of_movedBy_subset g_fixing)]

/--
The fixing subgroup of a set `s` is disjoint from the fixing subgroup of `sᶜ`
if the action is faithful.
-/
theorem fixingSubgroup_compl_disjoint [FaithfulSMul G α] (s : Set α) :
    Disjoint (fixingSubgroup G s) (fixingSubgroup G sᶜ) := by
  rw [Subgroup.disjoint_def]
  intro x x_in_fs x_in_fsc
  rw [mem_fixingSubgroup_iff_subset_fixedBy] at x_in_fs
  rw [mem_fixingSubgroup_iff_subset_fixedBy] at x_in_fsc
  rw [← fixedBy_eq_univ_iff_eq_one (α := α), eq_comm]
  apply subset_antisymm _ (Set.subset_univ _)
  rw [← Set.union_compl_self s]
  apply Set.union_subset <;> assumption

theorem fixingSubgroup_smul (s : Set α) (g : G) : G•[g • s] = MulAut.conj g • G•[s] := by
  ext h
  rw [mem_fixingSubgroup_iff_subset_fixedBy, Set.set_smul_subset_iff, smul_fixedBy, inv_inv,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_fixingSubgroup_iff_subset_fixedBy,
    MulAut.smul_def, MulAut.conj_inv_apply]

section Faithful

variable [FaithfulSMul G α]

@[simp]
theorem fixingSubgroup_univ : G•[(Set.univ : Set α)] = ⊥ := by
  ext g
  rw [Subgroup.mem_bot, mem_fixingSubgroup_iff_subset_fixedBy, Set.univ_subset_iff,
    fixedBy_eq_univ_iff_eq_one]


theorem not_mem_fixingSubgroup_compl_of_mem_fixingSubgroup (s : Set α) {g : G} (g_ne_one : g ≠ 1)
    (g_in_subgroup : g ∈ G•[s]) : g ∉ G•[sᶜ] := by
  intro h₁
  apply g_ne_one
  apply Subgroup.disjoint_def.mp (fixingSubgroup_compl_disjoint G s) <;> assumption

theorem commute_of_fixingSubgroup_compl_of_disjoint {g h : G} {s : Set α}
    (g_in_subgroup : g ∈ G•[sᶜ]) (disjoint_movedBy : Disjoint s (fixedBy α h)ᶜ) :
    Commute g h := by
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at g_in_subgroup
  have s_subset_fixedBy : s ⊆ fixedBy α h := by
    rwa [← Set.disjoint_compl_right_iff_subset]
  have movedBy_subset_sc : (fixedBy α h)ᶜ ⊆ sᶜ := by
    rwa [← Set.disjoint_compl_left_iff_subset, compl_compl]

  refine eq_of_smul_eq_smul fun x: α => ?comm_eq

  by_cases x ∈ s
  case pos x_in_s =>
    rw [mul_smul, mul_smul, s_subset_fixedBy x_in_s]
    rw [smul_mem_of_set_mem_fixedBy (set_mem_fixedBy_of_movedBy_subset g_in_subgroup)] at x_in_s
    rw [s_subset_fixedBy x_in_s]
  case neg x_notin_s =>
    rw [Set.compl_subset_comm] at g_in_subgroup
    rw [mul_smul, mul_smul, g_in_subgroup x_notin_s]

    by_cases x ∈ fixedBy α h
    case pos x_fixed =>
      rw [x_fixed, g_in_subgroup x_notin_s]
    case neg x_moved =>
      rw [← smul_mem_fixedBy_iff_mem_fixedBy] at x_moved
      rw [g_in_subgroup (movedBy_subset_sc x_moved)]

end Faithful
>>>>>>> 4c67043ad2 (feat(Topology/Algebra/Group/LocallyDense): finish proving lemma 2.2)

end Group
