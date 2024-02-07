/-
Copyright (c) 2024 Emilie Burgun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emilie Burgun
-/
import Mathlib.Topology.Basic
import Mathlib.Topology.Sets.Opens
import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Boolean algebra of regular open sets

This module defines *regular open* sets in a topological space, which are the sets `s` for which
`interior (closure s) = s`.
The type `RegularOpens` is a bundled set that is regular open.

A boolean algebra can be constructed for the regular open sets, with `↑(a ⊓ b) = ↑a ∩ ↑b` and
`↑(aᶜ) = (closure ↑a)ᶜ`.

## Main results

* `IsRegularOpen`: the proposition that a set `s` is regular open
* `TopologicalSpace.RegularOpens`: bundled regular open sets
* `TopologicalSpace.RegularOpens.booleanAlgebra`: the boolean algebra of regular open sets

## TODO

It should be possible to show that the above choice for `⊓` and `ᶜ` leads to a Heyting algebra on
`Opens`, and `RegularOpens` can then be constructed using `HeytingAlgebra.Regular`.

## References

* [S. Givant, P. Halmos, *Introduction to Boolean Algebras*][halmos2009introduction], Chapter 10
* [S. H. Kim, T. Koberda,
*Structure and Regularity of Group Actions on One-Manifolds*][kim2021structure],
  Chapter 3.6
-/

variable {X : Type*} [TopologicalSpace X]
variable {s t : Set X}

/--
A set `s` is regular open if `interior (closure s) = s`
-/
def IsRegularOpen (s : Set X) : Prop :=
  interior (closure s) = s

theorem isRegularOpen_iff : IsRegularOpen s ↔ interior (closure s) = s := Iff.rfl

section Lemmas

/-! ### Basic properties of the interior of the closure
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

theorem IsOpen.interior_closure_disjoint_left {s t : Set X} (t_open : IsOpen t)
    (disj : Disjoint s t) : Disjoint (interior (closure s)) t := by
  apply Set.disjoint_of_subset_left interior_subset
  exact disj.closure_left t_open

theorem IsOpen.interior_closure_disjoint_left_iff {s t : Set X} (s_open : IsOpen s)
    (t_open : IsOpen t) : Disjoint (interior (closure s)) t ↔ Disjoint s t := by
  refine ⟨fun h => ?disj, t_open.interior_closure_disjoint_left⟩
  apply Set.disjoint_of_subset_left subset_closure
  rw [← s_open.closure_interior_closure_eq_closure]
  exact h.closure_left t_open

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
    ← Set.compl_subset_compl, ← interior_compl] at res
  simp only [closure_compl, compl_compl, Set.compl_union, interior_inter,
    s_open.interior_eq] at res
  assumption
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
  · apply IsOpen.subset_interior_closure
    exact isOpen_iInter_of_finite fun i => (regular i).isOpen

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

variable (X) in
/--
The type of sets that are regular open in α.

The regular open sets in a topology form a boolean algebra, with as complement operator
`s ↦ (closure s)ᶜ` and as infimum `s ∩ t`.
-/
structure TopologicalSpace.RegularOpens :=
  /-- The underlying set that is regular open -/
  carrier : Set X
  /-- The statement that `carrier` is regular open -/
  regularOpen' : IsRegularOpen carrier

namespace TopologicalSpace.RegularOpens

@[simp]
theorem carrier_eq_iff {r s : RegularOpens X} : r.carrier = s.carrier ↔ r = s := by
  rw [mk.injEq]

instance : SetLike (RegularOpens X) X where
  coe := carrier
  coe_injective' := fun _ _ => carrier_eq_iff.mp

@[simp]
theorem coe_mk {s_regular : IsRegularOpen s} :
    (↑(⟨s, s_regular⟩ : RegularOpens X) : Set X) = s := rfl

theorem regularOpen (r : RegularOpens X) : IsRegularOpen (r : Set X) := r.regularOpen'

instance : CanLift (Set X) (RegularOpens X) RegularOpens.carrier IsRegularOpen := ⟨
  fun s s_reg => ⟨⟨s, s_reg⟩, rfl⟩⟩

/-! ### Construction of the boolean algebra for regular open sets
-/

instance : HasCompl (RegularOpens X) where
  compl := fun s => ⟨
    (closure (s : Set X))ᶜ,
    IsRegularOpen.of_compl_closure s.regularOpen.isOpen
  ⟩

theorem coe_compl {s : RegularOpens X} : (↑(sᶜ) : Set X) = (closure ↑s)ᶜ := rfl

theorem compl_antitone : Antitone (fun s: RegularOpens X => sᶜ) := by
  intro s t s_le_t
  apply Set.compl_subset_compl.mpr
  exact closure_mono s_le_t

theorem compl_compl (s : RegularOpens X) : sᶜᶜ = s := by
  rw [← SetLike.coe_set_eq]
  show (closure (closure (s : Set X))ᶜ)ᶜ = s
  rw [closure_compl, _root_.compl_compl, s.regularOpen]

theorem compl_le_compl_iff {s t : RegularOpens X} : sᶜ ≤ tᶜ ↔ t ≤ s := by
  refine ⟨fun h => ?t_le_s, fun h => compl_antitone h⟩
  rw [← compl_compl s, ← compl_compl t]
  exact compl_antitone h

theorem compl_inj {s t : RegularOpens X} : sᶜ = tᶜ ↔ s = t := by
  refine ⟨fun h => le_antisymm ?sc_le_tc ?tc_le_sc, fun h => h ▸ rfl⟩
  all_goals rw [← compl_le_compl_iff]
  all_goals apply le_of_eq
  · exact h.symm
  · exact h

instance : Inf (RegularOpens X) where
  inf := fun r s => ⟨
    (r : Set X) ∩ s,
    IsRegularOpen.inter r.regularOpen s.regularOpen⟩

instance : Sup (RegularOpens X) where
  sup := fun r s => (rᶜ ⊓ sᶜ)ᶜ

theorem sup_def (r s : RegularOpens X) : r ⊔ s = (rᶜ ⊓ sᶜ)ᶜ := rfl

theorem coe_sup (r s : RegularOpens X) :
    (↑(r ⊔ s) : Set X) = interior (closure (↑r ∪ ↑s)) := by
  show (closure ((closure _)ᶜ ∩ (closure _)ᶜ))ᶜ = _
  repeat rw [← interior_compl]
  rw [← interior_inter, ← Set.compl_union, interior_compl, interior_compl, closure_compl,
    _root_.compl_compl]

theorem coe_inf (r s : RegularOpens X) : (↑(r ⊓ s) : Set X) = ↑r ∩ ↑s := rfl

theorem sup_inf_distrib_right (r s t : RegularOpens X) :
    r ⊔ (s ⊓ t) = (r ⊔ s) ⊓ (r ⊔ t) := by
  rw [← SetLike.coe_set_eq]
  simp only [coe_sup, coe_inf]
  rw [Set.union_inter_distrib_left, IsOpen.interior_closure_inter]
  apply IsOpen.union r.regularOpen.isOpen s.regularOpen.isOpen

theorem inf_compl_eq_bot (r : RegularOpens X) : (↑(r ⊓ rᶜ) : Set X) = ∅ := by
  rw [RegularOpens.coe_inf, RegularOpens.coe_compl,
    ← Set.disjoint_iff_inter_eq_empty, Set.disjoint_compl_right_iff_subset]
  exact subset_closure

instance booleanAlgebra : BooleanAlgebra (RegularOpens X) where
  inf_le_left := fun r s => Set.inter_subset_left r.carrier s.carrier
  inf_le_right := fun r s => Set.inter_subset_right r.carrier s.carrier
  le_inf := fun _ _ _ h₁ h₂ => Set.subset_inter h₁ h₂

  le_sup_left := fun r s => by
    show r ≤ (rᶜ ⊓ sᶜ)ᶜ
    nth_rw 1 [← compl_compl r]
    apply compl_antitone
    exact Set.inter_subset_left _ _
  le_sup_right := fun r s => by
    show s ≤ (rᶜ ⊓ sᶜ)ᶜ
    nth_rw 1 [← compl_compl s]
    apply compl_antitone
    exact Set.inter_subset_right _ _
  sup_le := fun r s t h₁ h₂ => by
    show (rᶜ ⊓ sᶜ)ᶜ ≤ t
    rw [← compl_compl t]
    apply compl_antitone
    apply Set.subset_inter <;> apply compl_antitone
    all_goals assumption

  top := ⟨Set.univ, IsRegularOpen.univ X⟩
  le_top := fun r => Set.subset_univ r.carrier

  bot := ⟨∅, IsRegularOpen.empty X⟩
  bot_le := fun r => Set.empty_subset r.carrier

  le_sup_inf := by
    intro r s t
    rw [sup_inf_distrib_right]

  inf_compl_le_bot := by
    intro r
    rw [← SetLike.coe_subset_coe, inf_compl_eq_bot]
    exact subset_refl _
  top_le_sup_compl := by
    intro r
    rw [← SetLike.coe_subset_coe, sup_def, compl_compl]
    show Set.univ ⊆ (closure _)ᶜ
    rw [← Set.compl_empty, Set.compl_subset_comm, _root_.compl_compl, Set.subset_empty_iff,
      closure_empty_iff]
    nth_rw 2 [← compl_compl r]
    exact inf_compl_eq_bot rᶜ

@[simp]
theorem coe_top : ((⊤ : RegularOpens X) : Set X) = Set.univ := rfl

@[simp]
theorem coe_bot : ((⊥ : RegularOpens X) : Set X) = ∅ := rfl

/--
The canonical way to turn a `Set α` into a regular open set is to take the interior of its
closure. This operation yields the smallest regular open superset of `s` and is monotone.
-/
def fromSet (s : Set X) : RegularOpens X := ⟨
  interior (closure s),
  IsRegularOpen.of_interior_closure s⟩

@[simp]
theorem coe_fromSet (s : Set X) : (fromSet s : Set X) = interior (closure s) := rfl

@[simp]
theorem fromSet_coe (r : RegularOpens X) : fromSet (↑r : Set X) = r := by
  rw [← SetLike.coe_set_eq, coe_fromSet, r.regularOpen]

theorem fromSet_mono {s t : Set X} (s_ss_t : s ⊆ t) : fromSet s ≤ fromSet t := by
  rw [← SetLike.coe_subset_coe, coe_fromSet, coe_fromSet]
  exact interior_mono (closure_mono s_ss_t)

variable (X) in
theorem fromSet_monotone : Monotone (fromSet (X := X)) := fun _ _ h => fromSet_mono h

variable (X) in
theorem fromSet_surjective : Function.Surjective (fromSet (X := X)) :=
  fun r => ⟨r.carrier, fromSet_coe r⟩

variable (X) in
@[simp]
theorem fromSet_univ : fromSet (Set.univ : Set X) = ⊤ := by
  rw [← SetLike.coe_set_eq, coe_fromSet, closure_univ, interior_univ, coe_top]

variable (X) in
@[simp]
theorem fromSet_empty : fromSet (∅ : Set X) = ⊥ := by
  rw [← SetLike.coe_set_eq, coe_fromSet, closure_empty, interior_empty, coe_bot]

theorem disjoint_fromSet {s t : Set X} (s_open : IsOpen s) (t_open : IsOpen t):
    Disjoint (fromSet s) (fromSet t) ↔ Disjoint s t := by
  rw [disjoint_iff (a := fromSet s), ← SetLike.coe_set_eq, coe_bot, coe_inf, coe_fromSet,
    coe_fromSet, ← Set.disjoint_iff_inter_eq_empty,
    IsOpen.interior_closure_disjoint_iff s_open t_open]

theorem subset_fromSet_of_isOpen (s_open : IsOpen s) : s ⊆ fromSet s :=
  s_open.subset_interior_closure

theorem subset_closure_iff_le {r s : RegularOpens X} :
    (↑r : Set X) ⊆ closure (↑s) ↔ r ≤ s := by
  refine ⟨fun ss_cl => ?ss, fun ss => _root_.subset_trans ss subset_closure⟩
  rw [← SetLike.coe_subset_coe, ← IsOpen.interior_eq r.regularOpen.isOpen, ← s.regularOpen]
  exact interior_mono ss_cl

theorem closure_subset_closure_iff_le {r s : RegularOpens X} :
    closure (↑r : Set X) ⊆ closure (↑s) ↔ r ≤ s := by
  refine ⟨fun cl_ss => ?ss, fun ss => closure_mono ss⟩
  rw [← SetLike.coe_subset_coe, ← r.regularOpen, ← s.regularOpen]
  exact interior_mono cl_ss

/--
Constructs the `RegularOpens` set made up of finite intersections of `s`.
-/
def finiteInter (s : Set (RegularOpens X)) (s_finite : s.Finite) : RegularOpens X where
  carrier := ⋂ t ∈ s, (t : Set X)
  regularOpen' := IsRegularOpen.biInter_of_finite s_finite fun i _ => i.regularOpen

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
  smul := fun g r => ⟨g • r.carrier, smul_isRegularOpen g r.regularOpen'⟩
  one_smul := by
    intro r
    rw [← SetLike.coe_set_eq]
    show (1 : G) • (r : Set X) = r
    rw [one_smul]
  mul_smul := by
    intro g h r
    rw [← SetLike.coe_set_eq]
    show (g * h) • (r : Set X) = g • h • (r : Set X)
    rw [mul_smul]

scoped[Pointwise] attribute [instance] TopologicalSpace.RegularOpens.pointwiseMulAction

@[simp]
theorem coe_smul (g : G) (r : RegularOpens X) : (↑(g • r) : Set X) = g • ↑r := rfl

theorem smul_fromSet (g : G) (s : Set X) : g • fromSet s = fromSet (g • s) := by
  rw [← SetLike.coe_set_eq, coe_smul, coe_fromSet, coe_fromSet, closure_smul, interior_smul]

theorem inf_smul (g : G) (r s : RegularOpens X) : (g • r) ⊓ (g • s) = g • (r ⊓ s) := by
  rw [← SetLike.coe_set_eq]
  simp only [coe_smul, coe_inf, Set.smul_set_inter]

theorem compl_smul (g : G) (r : RegularOpens X) : (g • r)ᶜ = g • rᶜ := by
  rw [← SetLike.coe_set_eq, coe_smul, coe_compl, coe_smul, closure_smul, ← Set.smul_set_compl]
  rfl

theorem sup_smul (g : G) (r s : RegularOpens X) : (g • r) ⊔ (g • s) = g • (r ⊔ s) := by
  repeat rw [sup_def]
  simp only [inf_smul, compl_smul]

theorem mem_smul_iff_inv_mem {g : G} {r : RegularOpens X} {x : X} :
    x ∈ g • r ↔ g⁻¹ • x ∈ r := by
  rw [← SetLike.mem_coe, coe_smul, Set.mem_smul_set_iff_inv_smul_mem]
  rfl

@[simp]
theorem disjoint_coe {r s : RegularOpens X} :
    Disjoint (r : Set X) (s : Set X) ↔ Disjoint r s := by
  rw [Set.disjoint_iff_inter_eq_empty, disjoint_iff, ← SetLike.coe_set_eq (q := ⊥),
    coe_inf, coe_bot]

theorem disjoint_smul {r s : RegularOpens X} (disj : Disjoint r s) (g : G) :
    Disjoint (g • r) (g • s) := by
  rwa [← disjoint_coe, coe_smul, coe_smul, Set.smul_set_disjoint g, disjoint_coe]

end TopologicalSpace.RegularOpens

end ContinuousConstSMul
