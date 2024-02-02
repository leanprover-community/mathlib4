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

## TODO

It should be possible to show that the above choice for `⊓` and `ᶜ` leads to a Heyting algebra on
`Opens`, and `RegularOpens` can then be constructed using `HeytingAlgebra.Regular`.

## References

* [S. Givant, P. Halmos, *Introduction to Boolean Algebras*][halmos2009introduction], Chapter 10
* [S. H. Kim, T. Koberda,
*Structure and Regularity of Group Actions on One-Manifolds*][kim2021structure],
  Chapter 3.6
-/

variable {α : Type*} [TopologicalSpace α]

/--
A set `s` is regular open if `interior (closure s) = s`
-/
def IsRegularOpen (s : Set α) : Prop :=
  interior (closure s) = s

theorem isRegularOpen_iff (s : Set α) : IsRegularOpen s ↔ interior (closure s) = s := Iff.rfl

namespace IsRegularOpen

variable (α) in
theorem empty : IsRegularOpen (∅ : Set α) := by
  rw [isRegularOpen_iff, closure_empty, interior_empty]

variable (α) in
theorem univ : IsRegularOpen (Set.univ : Set α) := by
  rw [isRegularOpen_iff, closure_univ, interior_univ]

theorem of_compl_closure_of_open {s : Set α} (s_open : IsOpen s) : IsRegularOpen (closure s)ᶜ := by
  rw [isRegularOpen_iff, closure_compl, interior_compl,
    IsOpen.closure_interior_closure_eq_closure s_open]

theorem of_interior_closure (s : Set α) : IsRegularOpen (interior (closure s)) := by
  rw [closure_eq_compl_interior_compl, interior_compl]
  exact of_compl_closure_of_open isOpen_interior

/--
A regular open set is open.
-/
theorem isOpen {s : Set α} (s_reg : IsRegularOpen s) : IsOpen s := s_reg ▸ isOpen_interior

theorem compl_closure {s : Set α} (s_reg : IsRegularOpen s) : IsRegularOpen (closure s)ᶜ :=
  of_compl_closure_of_open s_reg.isOpen

theorem inter {s t : Set α} (s_reg : IsRegularOpen s) (t_reg : IsRegularOpen t) :
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

theorem iInter_of_finite {ι : Sort*} [Finite ι] {f : ι → Set α}
    (regular : ∀ i : ι, IsRegularOpen (f i)) : IsRegularOpen (⋂ i : ι, f i) := by
  rw [isRegularOpen_iff]
  apply subset_antisymm
  · simp_rw [Set.subset_iInter_iff]
    intro i
    rw [← regular i]
    exact interior_mono (closure_mono (Set.iInter_subset _ i))
  · apply IsOpen.subset_interior_closure
    exact isOpen_iInter_of_finite fun i => (regular i).isOpen

theorem biInter_of_finite {ι : Type*} {f : ι → Set α} {s : Set ι} (finite : s.Finite)
    (regular : ∀ i ∈ s, IsRegularOpen (f i)) : IsRegularOpen (⋂ i ∈ s, f i) := by
  have fin : Finite { i // i ∈ s } := Set.finite_coe_iff.mpr finite
  rw [← Set.iInter_subtype (fun i => i ∈ s) (fun i => f i.val)]
  exact iInter_of_finite fun i => regular i.val i.prop

end IsRegularOpen

lemma IsOpen.interior_closure_inter {s t : Set α} (s_open : IsOpen s) :
    interior (closure (s ∩ t)) = interior (closure s) ∩ interior (closure t) := by
  apply subset_antisymm
  · apply Set.subset_inter
    all_goals apply interior_mono
    all_goals apply closure_mono
    · exact Set.inter_subset_left s t
    · exact Set.inter_subset_right s t
  · rw [Set.inter_comm]
    apply _root_.subset_trans (IsOpen.inter_interior_closure isOpen_interior)
    rw [Set.inter_comm, ← IsRegularOpen.of_interior_closure (s ∩ t)]
    apply interior_mono
    apply closure_mono
    exact IsOpen.inter_interior_closure s_open

theorem subset_of_subset_closure_of_regularOpen {s t : Set α} (s_open : IsOpen s)
    (t_regular : IsRegularOpen t) (subset_closure : s ⊆ closure t) : s ⊆ t := by
  rw [← s_open.interior_eq, ← t_regular]
  exact interior_mono subset_closure

theorem disjoint_open_subset_of_not_subset_regularOpen {s t : Set α} (s_open : IsOpen s)
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
  rw [Set.inter_compl_nonempty_iff]
  exact mt (subset_of_subset_closure_of_regularOpen s_open t_regular) not_subset

variable (α) in
/--
The type of sets that are regular open in α.

The regular open sets in a topology form a boolean algebra, with as complement operator
`s ↦ (closure s)ᶜ` and as infimum `s ∩ t`.
-/
structure TopologicalSpace.RegularOpens :=
  /-- The underlying set that is regular open -/
  carrier : Set α
  /-- The statement that `carrier` is regular open -/
  regularOpen' : IsRegularOpen carrier

namespace TopologicalSpace.RegularOpens

@[simp]
theorem eq_iff {r s : RegularOpens α} : r.carrier = s.carrier ↔ r = s := by
  rw [mk.injEq]

instance : SetLike (RegularOpens α) α where
  coe := carrier
  coe_injective' := fun _ _ => eq_iff.mp

/-- Regular open sets are open. -/
instance : Coe (RegularOpens α) (TopologicalSpace.Opens α) where
  coe := fun r => ⟨r.carrier, r.regularOpen'.isOpen⟩

@[simp]
theorem coe_mk {s : Set α} {s_regular : IsRegularOpen s} :
    (↑(⟨s, s_regular⟩ : RegularOpens α) : Set α) = s := rfl

theorem regularOpen (r : RegularOpens α) : IsRegularOpen (r : Set α) := r.regularOpen'

instance : CanLift (Set α) (RegularOpens α) RegularOpens.carrier IsRegularOpen := ⟨
  fun s s_reg => ⟨⟨s, s_reg⟩, rfl⟩⟩

instance : PartialOrder (RegularOpens α) where
  le := fun r s => (↑r : Set α) ⊆ (↑s : Set α)
  le_refl := fun r => subset_refl r.carrier
  le_trans := fun _ _ _ h₁ h₂ => _root_.subset_trans h₁ h₂
  le_antisymm := fun r s h₁ h₂ => by
    rw [← eq_iff]
    exact subset_antisymm h₁ h₂

@[simp]
theorem subset_iff_le {r s : RegularOpens α} : (↑r : Set α) ⊆ ↑s ↔ r ≤ s := Iff.rfl

instance : OrderBot (RegularOpens α) where
  bot := ⟨∅, IsRegularOpen.empty α⟩
  bot_le := fun r => Set.empty_subset r.carrier

@[simp]
theorem coe_bot : ((⊥ : RegularOpens α) : Set α) = ∅ := rfl

instance : OrderTop (RegularOpens α) where
  top := ⟨Set.univ, IsRegularOpen.univ α⟩
  le_top := fun r => Set.subset_univ r.carrier

@[simp]
theorem coe_top : ((⊤ : RegularOpens α) : Set α) = Set.univ := rfl

instance : SemilatticeInf (RegularOpens α) where
  inf := fun r s => ⟨
    r.carrier ∩ s.carrier,
    IsRegularOpen.inter r.regularOpen s.regularOpen⟩
  inf_le_left := fun r s => Set.inter_subset_left r.carrier s.carrier
  inf_le_right := fun r s => Set.inter_subset_right r.carrier s.carrier
  le_inf := fun _ _ _ h₁ h₂ => Set.subset_inter h₁ h₂

instance : HasCompl (RegularOpens α) where
  compl := fun s => ⟨
    (closure s.carrier)ᶜ,
    IsRegularOpen.compl_closure s.regularOpen
  ⟩

theorem coe_compl {s : RegularOpens α} : (↑(sᶜ) : Set α) = (closure ↑s)ᶜ := rfl

theorem compl_antitone : Antitone (fun s: RegularOpens α => sᶜ) := by
  intro s t s_le_t
  apply Set.compl_subset_compl.mpr
  exact closure_mono s_le_t

theorem compl_compl (s : RegularOpens α) : sᶜᶜ = s := by
  rw [← SetLike.coe_set_eq]
  show (closure (closure (s : Set α))ᶜ)ᶜ = s
  rw [closure_compl, _root_.compl_compl, s.regularOpen]

theorem compl_le_compl_iff {s t : RegularOpens α} : sᶜ ≤ tᶜ ↔ t ≤ s := by
  refine ⟨fun h => ?t_le_s, fun h => compl_antitone h⟩
  rw [← compl_compl s, ← compl_compl t]
  exact compl_antitone h

theorem compl_inj {s t : RegularOpens α} : sᶜ = tᶜ ↔ s = t := by
  refine ⟨fun h => le_antisymm ?sc_le_tc ?tc_le_sc, fun h => h ▸ rfl⟩
  all_goals rw [← compl_le_compl_iff]
  all_goals apply le_of_eq
  · exact h.symm
  · exact h

variable (α) in
theorem compl_bot : (⊥ : RegularOpens α)ᶜ = ⊤ := by
  rw [← SetLike.coe_set_eq, coe_compl, coe_bot, coe_top, closure_empty, Set.compl_empty]

variable (α) in
theorem compl_top : (⊤ : RegularOpens α)ᶜ = ⊥ := by
  rw [← compl_compl ⊥, compl_bot]

instance : SemilatticeSup (RegularOpens α) where
  sup := fun r s => (rᶜ ⊓ sᶜ)ᶜ
  le_sup_left := fun r s => by
    show r ≤ (rᶜ ⊓ sᶜ)ᶜ
    nth_rw 1 [← compl_compl r]
    apply compl_antitone
    exact inf_le_left
  le_sup_right := fun r s => by
    show s ≤ (rᶜ ⊓ sᶜ)ᶜ
    nth_rw 1 [← compl_compl s]
    apply compl_antitone
    exact inf_le_right
  sup_le := fun r s t h₁ h₂ => by
    show (rᶜ ⊓ sᶜ)ᶜ ≤ t
    rw [← compl_compl t]
    apply compl_antitone
    apply le_inf <;> apply compl_antitone
    all_goals assumption

theorem sup_def (r s : RegularOpens α) : r ⊔ s = (rᶜ ⊓ sᶜ)ᶜ := rfl

theorem coe_sup (r s : RegularOpens α) :
    (↑(r ⊔ s) : Set α) = interior (closure (↑r ∪ ↑s)) := by
  show (closure ((closure r.carrier)ᶜ ∩ (closure s.carrier)ᶜ))ᶜ =
    interior (closure (r.carrier ∪ s.carrier))
  repeat rw [← interior_compl]
  rw [← interior_inter, ← Set.compl_union, interior_compl, interior_compl, closure_compl,
    _root_.compl_compl]

theorem coe_inf (r s : RegularOpens α) : (↑(r ⊓ s) : Set α) = ↑r ∩ ↑s := rfl

theorem le_iff_subset (r s : RegularOpens α) : (↑r : Set α) ⊆ ↑s ↔ r ≤ s := Iff.rfl

theorem sup_inf_distrib_right (r s t : RegularOpens α) :
    r ⊔ (s ⊓ t) = (r ⊔ s) ⊓ (r ⊔ t) := by
  rw [← SetLike.coe_set_eq]
  simp only [coe_sup, coe_inf]
  rw [Set.union_inter_distrib_left, IsOpen.interior_closure_inter]
  apply IsOpen.union r.regularOpen.isOpen s.regularOpen.isOpen

instance : DistribLattice (RegularOpens α) where
  inf_le_left := fun r s => inf_le_left
  inf_le_right := fun r s => inf_le_right
  le_inf := fun r s t => le_inf
  le_sup_inf := by
    intro r s t
    rw [sup_inf_distrib_right]

lemma inf_compl_eq_bot (r : RegularOpens α) : r ⊓ rᶜ = ⊥ := by
  rw [← SetLike.coe_set_eq, RegularOpens.coe_inf, RegularOpens.coe_compl, RegularOpens.coe_bot,
    ← Set.disjoint_iff_inter_eq_empty, Set.disjoint_compl_right_iff_subset]
  exact subset_closure

instance : BooleanAlgebra (RegularOpens α) where
  bot_le := fun s => bot_le
  le_top := fun s => le_top
  inf_compl_le_bot := by
    intro r
    rw [le_bot_iff, RegularOpens.inf_compl_eq_bot]
  top_le_sup_compl := by
    intro r
    rw [top_le_iff, RegularOpens.sup_def, RegularOpens.compl_compl, ← RegularOpens.compl_bot,
      RegularOpens.compl_inj, inf_comm, RegularOpens.inf_compl_eq_bot]

-- /--
-- Like regular open sets
-- -/

/--
The canonical way to turn a `Set α` into a regular open set is to simply take the interior of its
closure. This operation yields the smallest regular open superset of `s` and is monotone.
-/
def fromSet (s : Set α) : RegularOpens α := ⟨
  interior (closure s),
  IsRegularOpen.of_interior_closure s⟩

@[simp]
theorem coe_fromSet (s : Set α) : (fromSet s : Set α) = interior (closure s) := rfl

@[simp]
theorem fromSet_coe (r : RegularOpens α) : fromSet (↑r : Set α) = r := by
  rw [← SetLike.coe_set_eq, coe_fromSet, r.regularOpen]

@[simp]
theorem coe_opens_fromSet (s : Set α) : (fromSet s : Opens α) = Opens.interior (closure s) := rfl

theorem fromSet_mono {s t : Set α} (s_ss_t : s ⊆ t) : fromSet s ≤ fromSet t := by
  rw [← SetLike.coe_subset, coe_fromSet, coe_fromSet]
  exact interior_mono (closure_mono s_ss_t)

variable (α) in
theorem fromSet_monotone : Monotone (fromSet (α := α)) := fun _ _ h => fromSet_mono h

variable (α) in
theorem fromSet_surjective : Function.Surjective (fromSet (α := α)) :=
  fun r => ⟨r.carrier, fromSet_coe r⟩

theorem disjoint_fromSet {s t : Set α} (s_open : IsOpen s) (t_open : IsOpen t):
    Disjoint s t ↔ Disjoint (fromSet s) (fromSet t) := by
  rw [disjoint_iff (a := fromSet s), ← SetLike.coe_set_eq, coe_bot, coe_inf, coe_fromSet,
    coe_fromSet, ← Set.disjoint_iff_inter_eq_empty,
    IsOpen.interior_closure_disjoint_iff s_open t_open]

theorem subset_fromSet_of_isOpen {s : Set α} (s_open : IsOpen s) : s ⊆ fromSet s :=
  s_open.subset_interior_closure

theorem t2_separation_regularOpen [T2Space α] {x y : α} (x_ne_y : x ≠ y) :
    ∃ (r s : RegularOpens α), Disjoint r s ∧ x ∈ r ∧ y ∈ s := by
  let ⟨s, t, s_open, t_open, x_in_s, y_in_t, disj_st⟩ := t2_separation x_ne_y
  exact ⟨
    fromSet s,
    fromSet t,
    (disjoint_fromSet s_open t_open).mp disj_st,
    subset_fromSet_of_isOpen s_open x_in_s,
    subset_fromSet_of_isOpen t_open y_in_t
  ⟩

theorem subset_closure_iff_le {r s : RegularOpens α} :
    (↑r : Set α) ⊆ closure (↑s) ↔ r ≤ s := by
  refine ⟨fun ss_cl => ?ss, fun ss => _root_.subset_trans ss subset_closure⟩
  rw [← subset_iff_le, ← IsOpen.interior_eq r.regularOpen.isOpen, ← s.regularOpen]
  exact interior_mono ss_cl

theorem closure_subset_closure_iff_le {r s : RegularOpens α} :
    closure (↑r : Set α) ⊆ closure (↑s) ↔ r ≤ s := by
  refine ⟨fun cl_ss => ?ss, fun ss => closure_mono ss⟩
  rw [← subset_iff_le, ← r.regularOpen, ← s.regularOpen]
  exact interior_mono cl_ss

end TopologicalSpace.RegularOpens

section ContinuousConstSMul

variable {G : Type*} [Group G]
variable [MulAction G α] [ContinuousConstSMul G α]

open Pointwise

theorem smul_isRegularOpen (g : G) {s : Set α} (s_reg : IsRegularOpen s) :
    IsRegularOpen (g • s) := by
  rw [isRegularOpen_iff, closure_smul, interior_smul, s_reg]

namespace TopologicalSpace.RegularOpens

/--
The action on `G` implies a pointwise action on regular open sets.
-/
protected def pointwiseMulAction : MulAction G (RegularOpens α) where
  smul := fun g r => ⟨g • r.carrier, smul_isRegularOpen g r.regularOpen'⟩
  one_smul := by
    intro r
    rw [← eq_iff]
    show 1 • r.carrier = r.carrier
    rw [one_smul]
  mul_smul := by
    intro g h r
    rw [← eq_iff]
    show (g * h) • r.carrier = g • h • r.carrier
    rw [mul_smul]

scoped[Pointwise] attribute [instance] TopologicalSpace.RegularOpens.pointwiseMulAction

@[simp]
theorem coe_smul (g : G) (r : RegularOpens α) : (↑(g • r) : Set α) = g • ↑r := rfl

theorem smul_fromSet (g : G) (s : Set α) : g • fromSet s = fromSet (g • s) := by
  rw [← SetLike.coe_set_eq, coe_smul, coe_fromSet, coe_fromSet, closure_smul, interior_smul]

theorem inf_smul (g : G) (r s : RegularOpens α) : (g • r) ⊓ (g • s) = g • (r ⊓ s) := by
  rw [← SetLike.coe_set_eq]
  simp only [coe_smul, coe_inf, Set.smul_set_inter]

theorem compl_smul (g : G) (r : RegularOpens α) : (g • r)ᶜ = g • rᶜ := by
  rw [← SetLike.coe_set_eq, coe_smul, coe_compl, coe_smul, closure_smul, ← Set.smul_set_compl]
  rfl

theorem sup_smul (g : G) (r s : RegularOpens α) : (g • r) ⊔ (g • s) = g • (r ⊔ s) := by
  repeat rw [sup_def]
  simp only [inf_smul, compl_smul]

theorem mem_smul_iff_inv_mem {g : G} {r : RegularOpens α} {x : α} :
    x ∈ g • r ↔ g⁻¹ • x ∈ r := by
  rw [← SetLike.mem_coe, coe_smul, Set.mem_smul_set_iff_inv_smul_mem]
  rfl

@[simp]
theorem disjoint_coe {r s : RegularOpens α} :
    Disjoint (r : Set α) (s : Set α) ↔ Disjoint r s := by
  rw [Set.disjoint_iff_inter_eq_empty, disjoint_iff, ← SetLike.coe_set_eq (q := ⊥),
    coe_inf, coe_bot]

theorem disjoint_smul {r s : RegularOpens α} (disj : Disjoint r s) (g : G) :
    Disjoint (g • r) (g • s) := by
  rwa [← disjoint_coe, coe_smul, coe_smul, ← Set.smul_set_disjoint g, disjoint_coe]

-- Note: the same argument can be made for TopologicalSpace.Opens
/--
If the topological space `α` is Hausdorff and the group action of `G` on `α` is faithful and
continuous, then this action is also faithful on the regular open sets.
-/
instance pointwiseMulAction_faithful_of_t2space [FaithfulSMul G α] [T2Space α] :
    FaithfulSMul G (RegularOpens α) := by
  constructor
  intro g h img_eq
  rw [← inv_inj]
  apply FaithfulSMul.eq_of_smul_eq_smul (α := α)
  intro x
  by_contra gx_ne_hx
  let ⟨u, v, disj_uv, x_in_gu, x_in_hv⟩ := t2_separation_regularOpen gx_ne_hx
  rw [← mem_smul_iff_inv_mem] at x_in_gu
  rw [← mem_smul_iff_inv_mem] at x_in_hv
  have disj_img := disjoint_smul disj_uv g
  rw [img_eq v, ← disjoint_coe, Set.disjoint_iff_forall_ne] at disj_img

  exact disj_img x_in_gu x_in_hv rfl

end TopologicalSpace.RegularOpens

end ContinuousConstSMul

section FiniteInter

namespace TopologicalSpace.RegularOpens

/--
Constructs the `RegularOpens` set made up of finite intersections of `s`.
-/
def finiteInter (s : Set (RegularOpens α)) (s_finite : s.Finite) : RegularOpens α where
  carrier := ⋂ t ∈ s, (t : Set α)
  regularOpen' := IsRegularOpen.biInter_of_finite s_finite fun i _ => i.regularOpen

@[simp]
theorem coe_finiteInter {s : Set (RegularOpens α)} (s_finite : s.Finite) :
    (finiteInter s s_finite : Set α) = ⋂ t ∈ s, (t : Set α) := rfl

end TopologicalSpace.RegularOpens

end FiniteInter
