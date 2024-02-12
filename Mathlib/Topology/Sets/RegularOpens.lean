/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Order.Heyting.Regular

/-!
# Boolean algebra of regular open sets

This module defines *regular open* sets in a topological space, which are the sets `s` for which
`interior (closure s) = s`.

The type `RegularOpens X` is the type of bundled regular open sets in `X`,
which is constructed from the regular subalgebra of the Heyting algebra on `Opens X`.

## Main results

* `IsRegularOpen`: the proposition that a set `s` is regular open.
* `TopologicalSpace.RegularOpens`: bundled regular open sets.
* `TopologicalSpace.RegularOpens.intCl`: the regular open set obtained by taking the interior
  of the closure of a set `s`.
* `TopologicalSpace.RegularOpens.pointwiseMulAction`: the pointwise group action of `G` on
  regular open sets, only available when the `Pointwise` scope is opened.

## References

* [S. Givant, P. Halmos, *Introduction to Boolean Algebras*][halmos2009introduction], Chapter 10
* [S. H. Kim, T. Koberda,
*Structure and Regularity of Group Actions on One-Manifolds*][kim2021structure],
  Chapter 3.6
-/

variable {X : Type*} [TopologicalSpace X]
variable {s t : Set X}

open TopologicalSpace (Opens)

/--
A set `s` is regular open if `interior (closure s) = s`
-/
def IsRegularOpen (s : Set X) : Prop :=
  interior (closure s) = s

theorem isRegularOpen_iff : IsRegularOpen s ↔ interior (closure s) = s := Iff.rfl

section Lemmas

/-! ### Basic properties of `interior (closure s)`
-/

@[simp]
theorem IsOpen.closure_interior_closure_eq_closure (s_open : IsOpen s) :
    closure (interior (closure s)) = closure s := by
  apply subset_antisymm
  · nth_rw 2 [← closure_closure (s := s)]
    exact closure_mono interior_subset
  · nth_rw 1 [← IsOpen.interior_eq s_open]
    exact closure_mono <| interior_mono subset_closure

theorem IsOpen.subset_interior_closure (s_open : IsOpen s) :
    s ⊆ interior (closure s) := by
  nth_rw 1 [← IsOpen.interior_eq s_open]
  exact interior_mono subset_closure

theorem IsOpen.interior_closure_disjoint_left_iff {s t : Set X} (s_open : IsOpen s)
    (t_open : IsOpen t) : Disjoint (interior (closure s)) t ↔ Disjoint s t := by
  refine ⟨fun h => ?disj_ic, fun disj_ic => ?disj⟩
  · apply Set.disjoint_of_subset_left subset_closure
    rw [← s_open.closure_interior_closure_eq_closure]
    exact h.closure_left t_open
  · exact Set.disjoint_of_subset_left interior_subset <| disj_ic.closure_left t_open

/--
If `s` and `t` are open, then `s` is disjoint from `t` iff `interior (closure s)` is disjoint from
`interior (closure t)`.
-/
theorem IsOpen.interior_closure_disjoint_iff {s t : Set X} (s_open : IsOpen s) (t_open : IsOpen t) :
    Disjoint (interior (closure s)) (interior (closure t)) ↔ Disjoint s t := by
  rw [IsOpen.interior_closure_disjoint_left_iff s_open isOpen_interior, disjoint_comm,
    IsOpen.interior_closure_disjoint_left_iff t_open s_open, disjoint_comm]

/--
The extension of `IsOpen.inter_closure` to the interior of the closure of a set.

Used in proving that `fun s => (closure s)ᶜ` distributes with the intersection of regular open
sets.
-/
lemma IsOpen.inter_interior_closure (s_open : IsOpen s) :
    s ∩ interior (closure t) ⊆ interior (closure (s ∩ t)) := by
  have res := interior_mono (IsOpen.inter_closure s_open (t := t))
  rw [← Set.compl_subset_compl, ← closure_compl (s := s ∩ closure t), Set.compl_inter,
    Set.compl_subset_comm, ← interior_compl] at res
  simpa [closure_compl, Set.compl_union, interior_inter, s_open.interior_eq] using res

end Lemmas

namespace IsRegularOpen

/-! ### Basic properties of regular open sets
-/

variable (X) in
theorem empty : IsRegularOpen (∅ : Set X) := by
  rw [isRegularOpen_iff, closure_empty, interior_empty]

variable (X) in
theorem univ : IsRegularOpen (Set.univ : Set X) := by
  rw [isRegularOpen_iff, closure_univ, interior_univ]

theorem of_compl_closure (s_open : IsOpen s) : IsRegularOpen (closure s)ᶜ := by
  rw [isRegularOpen_iff, closure_compl, interior_compl,
    IsOpen.closure_interior_closure_eq_closure s_open]

theorem of_interior_closure (s : Set X) : IsRegularOpen (interior (closure s)) := by
  rw [closure_eq_compl_interior_compl, interior_compl]
  exact of_compl_closure isOpen_interior

/--
A regular open set is open.
-/
theorem isOpen (s_reg : IsRegularOpen s) : IsOpen s := s_reg ▸ isOpen_interior

/--
The intersection of two regular open sets yields a regular open set.
-/
theorem inter {s t : Set X} (s_reg : IsRegularOpen s) (t_reg : IsRegularOpen t) :
    IsRegularOpen (s ∩ t) := by
  rw [isRegularOpen_iff]
  apply subset_antisymm
  · apply Set.subset_inter
    · nth_rw 2 [← s_reg]
      exact interior_mono (closure_mono (Set.inter_subset_left s t))
    · nth_rw 2 [← t_reg]
      exact interior_mono (closure_mono (Set.inter_subset_right s t))
  · apply IsOpen.subset_interior_closure
    exact s_reg.isOpen.inter t_reg.isOpen

theorem iInter_of_finite {ι : Sort*} [Finite ι] {f : ι → Set X}
    (regular : ∀ i : ι, IsRegularOpen (f i)) : IsRegularOpen (⋂ i : ι, f i) := by
  rw [isRegularOpen_iff]
  apply subset_antisymm
  · simp_rw [Set.subset_iInter_iff]
    intro i
    rw [← regular i]
    exact interior_mono (closure_mono (Set.iInter_subset _ i))
  · exact IsOpen.subset_interior_closure <| isOpen_iInter_of_finite fun i => (regular i).isOpen

theorem biInter_of_finite {ι : Type*} {f : ι → Set X} {s : Set ι} (finite : s.Finite)
    (regular : ∀ i ∈ s, IsRegularOpen (f i)) : IsRegularOpen (⋂ i ∈ s, f i) := by
  have fin : Finite { i // i ∈ s } := Set.finite_coe_iff.mpr finite
  rw [← Set.iInter_subtype (fun i => i ∈ s) (fun i => f i.val)]
  exact iInter_of_finite fun i => regular i.val i.prop

theorem subset_closure_iff (t_regular : IsRegularOpen t) (s_open : IsOpen s) :
    s ⊆ closure t ↔ s ⊆ t := by
  refine ⟨fun subset_closure => ?ss, fun ss => subset_trans ss subset_closure⟩
  rw [← s_open.interior_eq, ← t_regular]
  exact interior_mono subset_closure

end IsRegularOpen

/--
The interior of the closure distributes together with set intersection.
-/
lemma IsOpen.interior_closure_inter {s t : Set X} (s_open : IsOpen s) :
    interior (closure (s ∩ t)) = interior (closure s) ∩ interior (closure t) := by
  apply subset_antisymm
  · apply Set.subset_inter <;> apply interior_mono <;> apply closure_mono
    · exact Set.inter_subset_left s t
    · exact Set.inter_subset_right s t
  · rw [Set.inter_comm]
    apply _root_.subset_trans (IsOpen.inter_interior_closure isOpen_interior)
    rw [Set.inter_comm, ← IsRegularOpen.of_interior_closure (s ∩ t)]
    exact interior_mono <| closure_mono <| IsOpen.inter_interior_closure s_open

/--
If an open set `s` is not a subset of a regular open set `t`, then there exists
a nonempty, open subset of `s` that is disjoint from `t`.
-/
theorem IsRegularOpen.disjoint_open_subset_of_not_subset {s t : Set X} (s_open : IsOpen s)
    (t_regular : IsRegularOpen t) (not_subset : ¬s ⊆ t) :
    ∃ u, IsOpen u ∧ u.Nonempty ∧ u ⊆ s ∧ Disjoint u t := by
  refine ⟨
    s ∩ (closure t)ᶜ,
    s_open.inter <| isOpen_compl_iff.mpr isClosed_closure,
    ?nonempty,
    Set.inter_subset_left _ _,
    Set.disjoint_of_subset_left (Set.inter_subset_right _ _)
      <| Set.disjoint_of_subset_right subset_closure
      <| disjoint_compl_left⟩
  rwa [Set.inter_compl_nonempty_iff, t_regular.subset_closure_iff s_open]

/-! ### Bundled regular open sets
-/

-- TODO: use Yaël's instance for `HeytingAlgebra` from `Frame`
instance : HeytingAlgebra (Opens X) := {
  toLattice := inferInstance,
  himp := fun s t => Opens.interior (sᶜ ∪ t : Set X),
  compl := fun s => Opens.interior (sᶜ : Set X),
  le_himp_iff := by
    intro s t u
    change _ ≤ Opens.interior _ ↔ _
    simp_rw [← SetLike.coe_subset_coe, Opens.coe_inf, Opens.coe_interior, Set.inter_subset]
    refine ⟨fun subset => ?ss, fun subset => interior_maximal subset s.isOpen⟩
    calc
      (s : Set X) ⊆ _root_.interior (tᶜ ∪ u) := subset
      _ ⊆ tᶜ ∪ _root_.interior u := (isClosed_compl_iff.mpr t.isOpen).interior_union_left
      _ = (tᶜ : Set X) ∪ u := by rw [u.isOpen.interior_eq]
  himp_bot := by
    intro a
    change Opens.interior (aᶜ ∪ ∅ : Set X) = Opens.interior (aᶜ : Set X)
    rw [Set.union_empty]
}
theorem Opens.coe_compl {s : Opens X} : ↑(sᶜ) = interior (s : Set X)ᶜ := rfl

theorem IsRegularOpen.heytingRegular_iff {s : Opens X} :
    Heyting.IsRegular s ↔ IsRegularOpen (s : Set X) := by
  simp_rw [IsRegularOpen, closure_eq_compl_interior_compl, ← Opens.coe_compl, SetLike.coe_set_eq,
    Heyting.IsRegular]

variable (X) in
abbrev TopologicalSpace.RegularOpens := Heyting.Regular (Opens X)

namespace TopologicalSpace.RegularOpens

theorem regularOpen (r : TopologicalSpace.RegularOpens X) :
    IsRegularOpen (r : Set X) := IsRegularOpen.heytingRegular_iff.mp r.prop


instance instMembership : Membership X (RegularOpens X) where
  mem := fun x r => x ∈ (r : Set X)

theorem mem_iff {x : X} {r : RegularOpens X} : x ∈ (r : Set X) ↔ x ∈ r := Iff.rfl

def of (s : Set X) (s_reg : IsRegularOpen s) : RegularOpens X :=
  ⟨⟨s, s_reg.isOpen⟩, IsRegularOpen.heytingRegular_iff.mpr s_reg⟩

@[simp]
theorem coe_of {s : Set X} (s_reg : IsRegularOpen s) : (of s s_reg : Set X) = s := rfl

instance canLift : CanLift (Set X) (RegularOpens X) (↑) IsRegularOpen := ⟨
  fun s s_reg => ⟨of s s_reg, rfl⟩⟩

@[simp]
theorem coe_sup {r s : RegularOpens X} : (↑(r ⊔ s) : Set X) = interior (closure (↑r ∪ ↑s)) := by
  simp_rw [Heyting.Regular.coe_sup, Opens.coe_compl, ← closure_eq_compl_interior_compl,
    Opens.coe_sup]

theorem sup_def {r s : RegularOpens X} : r ⊔ s = (rᶜ ⊓ sᶜ)ᶜ := by simp_rw [compl_inf, compl_compl]

/--
The canonical way to turn a `Set α` into a regular open set is to take the interior of its
closure. This operation yields the smallest regular open superset of `s` (if `s` is open)
and is monotone.
-/
def intCl (s : Set X) : RegularOpens X := of (interior (closure s)) <|
  IsRegularOpen.of_interior_closure s

@[simp]
theorem coe_intCl (s : Set X) : (intCl s : Set X) = interior (closure s) := rfl

@[simp]
theorem intCl_coe (r : RegularOpens X) : intCl (↑r : Set X) = r := by
  rw [← Heyting.Regular.coe_inj, ← SetLike.coe_set_eq, coe_intCl, r.regularOpen]

theorem intCl_mono {s t : Set X} (s_ss_t : s ⊆ t) : intCl s ≤ intCl t := by
  rw [← Heyting.Regular.coe_le_coe, ← SetLike.coe_subset_coe, coe_intCl, coe_intCl]
  exact interior_mono (closure_mono s_ss_t)

variable (X) in
theorem intCl_monotone : Monotone (intCl (X := X)) := fun _ _ h => intCl_mono h

variable (X) in
theorem intCl_surjective : Function.Surjective (intCl (X := X)) := fun r => ⟨r, intCl_coe r⟩

variable (X) in
@[simp]
theorem intCl_univ : intCl (Set.univ : Set X) = ⊤ := by
  rw [← Heyting.Regular.coe_inj, ← SetLike.coe_set_eq, coe_intCl, closure_univ, interior_univ,
    Heyting.Regular.coe_top, Opens.coe_top]

variable (X) in
@[simp]
theorem intCl_empty : intCl (∅ : Set X) = ⊥ := by
  rw [← Heyting.Regular.coe_inj, ← SetLike.coe_set_eq, coe_intCl, closure_empty, interior_empty,
    Heyting.Regular.coe_bot, Opens.coe_bot]

theorem intCl_inf {s t : Set X} (s_open : IsOpen s) : intCl s ⊓ intCl t = intCl (s ∩ t) := by
  simp_rw [← Heyting.Regular.coe_inj, ← SetLike.coe_set_eq, Heyting.Regular.coe_inf,
    Opens.coe_inf, coe_intCl, s_open.interior_closure_inter]

theorem disjoint_intCl {s t : Set X} (s_open : IsOpen s) (t_open : IsOpen t) :
    Disjoint (intCl s) (intCl t) ↔ Disjoint s t := by
  rw [disjoint_iff (a := intCl s), ← Heyting.Regular.coe_inj, ← SetLike.coe_set_eq,
    ← IsOpen.interior_closure_disjoint_iff s_open t_open, Set.disjoint_iff_inter_eq_empty]
  simp

theorem subset_intCl_of_isOpen (s_open : IsOpen s) : s ⊆ intCl s :=
  s_open.subset_interior_closure

theorem subset_closure_iff_le {r s : RegularOpens X} :
    (↑r : Set X) ⊆ closure (↑s) ↔ r ≤ s := by
  refine ⟨fun ss_cl => ?ss, fun ss => _root_.subset_trans ss subset_closure⟩
  rw [← Heyting.Regular.coe_le_coe, ← SetLike.coe_subset_coe,
    ← IsOpen.interior_eq r.regularOpen.isOpen, ← s.regularOpen]
  exact interior_mono ss_cl

theorem closure_subset_closure_iff_le {r s : RegularOpens X} :
    closure (↑r : Set X) ⊆ closure (↑s) ↔ r ≤ s := by
  refine ⟨fun cl_ss => ?ss, fun ss => closure_mono ss⟩
  rw [← Heyting.Regular.coe_le_coe, ← SetLike.coe_subset_coe, ← r.regularOpen, ← s.regularOpen]
  exact interior_mono cl_ss

/--
Constructs the `RegularOpens` set made up of finite intersections of `s`.
-/
def finiteInter (s : Set (RegularOpens X)) (s_finite : s.Finite) : RegularOpens X :=
  of (⋂ t ∈ s, (t : Set X)) <| IsRegularOpen.biInter_of_finite s_finite fun i _ => i.regularOpen

@[simp]
theorem coe_finiteInter {s : Set (RegularOpens X)} (s_finite : s.Finite) :
    (finiteInter s s_finite : Set X) = ⋂ t ∈ s, (t : Set X) := rfl

end TopologicalSpace.RegularOpens

section ContinuousConstSMul

/-! ### Pointwise action on regular open sets

The instance below is only available when the `Pointwise` scope is opened.
-/

variable {G : Type*} [Group G]
variable [MulAction G X] [ContinuousConstSMul G X]

open Pointwise

theorem smul_isRegularOpen (g : G) (s_reg : IsRegularOpen s) :
    IsRegularOpen (g • s) := by
  rw [isRegularOpen_iff, closure_smul, interior_smul, s_reg]

namespace TopologicalSpace.RegularOpens

/--
A continuous action of `G` on `X` induces a pointwise action of `G` on regular open sets of `X`.
-/
protected def pointwiseMulAction : MulAction G (RegularOpens X) where
  smul := fun g r => of (g • (r : Set X)) <| smul_isRegularOpen g r.regularOpen
  one_smul := by
    intro r
    rw [← Heyting.Regular.coe_inj, ← SetLike.coe_set_eq]
    show (1 : G) • (r : Set X) = r
    rw [one_smul]
  mul_smul := by
    intro g h r
    rw [← Heyting.Regular.coe_inj, ← SetLike.coe_set_eq]
    show (g * h) • (r : Set X) = g • h • (r : Set X)
    rw [mul_smul]

scoped[Pointwise] attribute [instance] TopologicalSpace.RegularOpens.pointwiseMulAction

@[simp]
theorem coe_smul (g : G) (r : RegularOpens X) : (↑(g • r) : Set X) = g • ↑r := rfl

theorem smul_intCl (g : G) (s : Set X) : g • intCl s = intCl (g • s) := by
  rw [← Heyting.Regular.coe_inj, ← SetLike.coe_set_eq, coe_smul, coe_intCl, coe_intCl, closure_smul,
    interior_smul]

theorem smul_inf (g : G) (r s : RegularOpens X) : (g • r) ⊓ (g • s) = g • (r ⊓ s) := by
  rw [← Heyting.Regular.coe_inj, ← SetLike.coe_set_eq]
  simp only [coe_smul, Heyting.Regular.coe_inf, Opens.coe_inf, Set.smul_set_inter]

theorem smul_compl (g : G) (r : RegularOpens X) : (g • r)ᶜ = g • rᶜ := by
  rw [← Heyting.Regular.coe_inj, ← SetLike.coe_set_eq, coe_smul, Heyting.Regular.coe_compl,
    Opens.coe_compl, coe_smul, ← Set.smul_set_compl, interior_smul]
  rfl

theorem smul_sup (g : G) (r s : RegularOpens X) : (g • r) ⊔ (g • s) = g • (r ⊔ s) := by
  simp only [sup_def, smul_compl, smul_inf]

theorem mem_smul_iff_inv_mem {g : G} {r : RegularOpens X} {x : X} :
    x ∈ g • r ↔ g⁻¹ • x ∈ r := by
  rw [← mem_iff, coe_smul, Set.mem_smul_set_iff_inv_smul_mem, mem_iff]

@[simp]
theorem disjoint_coe {r s : RegularOpens X} :
    Disjoint (r : Set X) (s : Set X) ↔ Disjoint r s := by
  rw [Set.disjoint_iff_inter_eq_empty, disjoint_iff, ← Heyting.Regular.coe_inj,
    ← SetLike.coe_set_eq (q := ((⊥ : RegularOpens X) : Opens X)),
    Heyting.Regular.coe_inf, Opens.coe_inf, Heyting.Regular.coe_bot, Opens.coe_bot]

theorem disjoint_smul {r s : RegularOpens X} (disj : Disjoint r s) (g : G) :
    Disjoint (g • r) (g • s) := by
  rwa [← disjoint_coe, coe_smul, coe_smul, Set.smul_set_disjoint g, disjoint_coe]

end TopologicalSpace.RegularOpens

end ContinuousConstSMul
