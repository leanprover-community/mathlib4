/-
Copyright (c) 2022 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.GroupTheory.GroupAction.FixedPoints

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

-/


section Monoid

open MulAction

variable (M : Type*) {α : Type*} [Monoid M] [MulAction M α]

/-- The submonoid fixing a set under a `MulAction`. -/
@[to_additive /-- The additive submonoid fixing a set under an `AddAction`. -/]
def fixingSubmonoid (s : Set α) : Submonoid M where
  carrier := { ϕ : M | ∀ x : s, ϕ • (x : α) = x }
  one_mem' _ := one_smul _ _
  mul_mem' {x y} hx hy z := by rw [mul_smul, hy z, hx z]

@[to_additive]
theorem mem_fixingSubmonoid_iff {s : Set α} {m : M} :
    m ∈ fixingSubmonoid M s ↔ ∀ y ∈ s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩

variable (α)

/-- The Galois connection between fixing submonoids and fixed points of a monoid action -/
@[to_additive]
theorem fixingSubmonoid_fixedPoints_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubmonoid M)
      ((fun P : Submonoid M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun _s _P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩

@[to_additive]
theorem fixingSubmonoid_antitone : Antitone fun s : Set α => fixingSubmonoid M s :=
  (fixingSubmonoid_fixedPoints_gc M α).monotone_l

@[to_additive fixedPoints_antitone_addSubmonoid]
theorem fixedPoints_antitone : Antitone fun P : Submonoid M => fixedPoints P α :=
  (fixingSubmonoid_fixedPoints_gc M α).monotone_u.dual_left

/-- Fixing submonoid of union is intersection -/
@[to_additive]
theorem fixingSubmonoid_union {s t : Set α} :
    fixingSubmonoid M (s ∪ t) = fixingSubmonoid M s ⊓ fixingSubmonoid M t :=
  (fixingSubmonoid_fixedPoints_gc M α).l_sup

/-- Fixing submonoid of iUnion is intersection -/
@[to_additive]
theorem fixingSubmonoid_iUnion {ι : Sort*} {s : ι → Set α} :
    fixingSubmonoid M (⋃ i, s i) = ⨅ i, fixingSubmonoid M (s i) :=
  (fixingSubmonoid_fixedPoints_gc M α).l_iSup

/-- Fixed points of sup of submonoids is intersection -/
@[to_additive]
theorem fixedPoints_submonoid_sup {P Q : Submonoid M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α ∩ fixedPoints Q α :=
  (fixingSubmonoid_fixedPoints_gc M α).u_inf

/-- Fixed points of iSup of submonoids is intersection -/
@[to_additive]
theorem fixedPoints_submonoid_iSup {ι : Sort*} {P : ι → Submonoid M} :
    fixedPoints (↥(iSup P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixingSubmonoid_fixedPoints_gc M α).u_iInf

end Monoid

section Group

open MulAction

variable (M : Type*) {α : Type*} [Group M] [MulAction M α]

/-- The subgroup fixing a set under a `MulAction`. -/
@[to_additive /-- The additive subgroup fixing a set under an `AddAction`. -/]
def fixingSubgroup (s : Set α) : Subgroup M :=
  { fixingSubmonoid M s with inv_mem' := fun hx z => by rw [inv_smul_eq_iff, hx z] }

@[to_additive]
theorem mem_fixingSubgroup_iff {s : Set α} {m : M} : m ∈ fixingSubgroup M s ↔ ∀ y ∈ s, m • y = y :=
  ⟨fun hg y hy => hg ⟨y, hy⟩, fun h ⟨y, hy⟩ => h y hy⟩

@[to_additive]
theorem mem_fixingSubgroup_iff_subset_fixedBy {s : Set α} {m : M} :
    m ∈ fixingSubgroup M s ↔ s ⊆ fixedBy α m := by
  simp_rw [mem_fixingSubgroup_iff, Set.subset_def, mem_fixedBy]

@[to_additive]
theorem mem_fixingSubgroup_compl_iff_movedBy_subset {s : Set α} {m : M} :
    m ∈ fixingSubgroup M sᶜ ↔ (fixedBy α m)ᶜ ⊆ s := by
  rw [mem_fixingSubgroup_iff_subset_fixedBy, Set.compl_subset_comm]

variable (α)

/-- The Galois connection between fixing subgroups and fixed points of a group action -/
@[to_additive]
theorem fixingSubgroup_fixedPoints_gc :
    GaloisConnection (OrderDual.toDual ∘ fixingSubgroup M)
      ((fun P : Subgroup M => fixedPoints P α) ∘ OrderDual.ofDual) :=
  fun _s _P => ⟨fun h s hs p => h p.2 ⟨s, hs⟩, fun h p hp s => h s.2 ⟨p, hp⟩⟩

@[to_additive (attr := simp)]
lemma fixingSubgroup_empty : fixingSubgroup M (∅ : Set α) = ⊤ :=
  GaloisConnection.l_bot (fixingSubgroup_fixedPoints_gc M α)

@[to_additive]
theorem fixingSubgroup_antitone : Antitone (fixingSubgroup M : Set α → Subgroup M) :=
  (fixingSubgroup_fixedPoints_gc M α).monotone_l

@[to_additive]
theorem fixedPoints_subgroup_antitone : Antitone fun P : Subgroup M => fixedPoints P α :=
  (fixingSubgroup_fixedPoints_gc M α).monotone_u.dual_left

/-- Fixing subgroup of union is intersection -/
@[to_additive]
theorem fixingSubgroup_union {s t : Set α} :
    fixingSubgroup M (s ∪ t) = fixingSubgroup M s ⊓ fixingSubgroup M t :=
  (fixingSubgroup_fixedPoints_gc M α).l_sup

/-- Fixing subgroup of iUnion is intersection -/
@[to_additive]
theorem fixingSubgroup_iUnion {ι : Sort*} {s : ι → Set α} :
    fixingSubgroup M (⋃ i, s i) = ⨅ i, fixingSubgroup M (s i) :=
  (fixingSubgroup_fixedPoints_gc M α).l_iSup

/-- Fixed points of sup of subgroups is intersection -/
@[to_additive]
theorem fixedPoints_subgroup_sup {P Q : Subgroup M} :
    fixedPoints (↥(P ⊔ Q)) α = fixedPoints P α ∩ fixedPoints Q α :=
  (fixingSubgroup_fixedPoints_gc M α).u_inf

/-- Fixed points of iSup of subgroups is intersection -/
@[to_additive]
theorem fixedPoints_subgroup_iSup {ι : Sort*} {P : ι → Subgroup M} :
    fixedPoints (↥(iSup P)) α = ⋂ i, fixedPoints (P i) α :=
  (fixingSubgroup_fixedPoints_gc M α).u_iInf

/-- The orbit of the fixing subgroup of `sᶜ` (i.e. the moving subgroup of `s`) is a subset of `s` -/
@[to_additive]
theorem orbit_fixingSubgroup_compl_subset {s : Set α} {a : α} (a_in_s : a ∈ s) :
    MulAction.orbit (fixingSubgroup M sᶜ) a ⊆ s := by
  intro b b_in_orbit
  let ⟨⟨g, g_fixing⟩, g_eq⟩ := MulAction.mem_orbit_iff.mp b_in_orbit
  rw [Submonoid.mk_smul] at g_eq
  rw [mem_fixingSubgroup_compl_iff_movedBy_subset] at g_fixing
  rwa [← g_eq, smul_mem_of_set_mem_fixedBy (set_mem_fixedBy_of_movedBy_subset g_fixing)]

end Group
