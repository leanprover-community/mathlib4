/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module order.complete_lattice
! leanprover-community/mathlib commit 5709b0d8725255e76f47debca6400c07b5c2d8e6
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Bool.Set
import Mathlib.Data.Nat.Set
import Mathlib.Data.ULift
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Hom.Basic

import Mathlib.Mathport.Notation


/-!
# Theory of complete lattices

## Main definitions

* `supₛ` and `infₛ` are the supremum and the infimum of a set;
* `supᵢ (f : ι → α)` and `infᵢ (f : ι → α)` are indexed supremum and infimum of a function,
  defined as `supₛ` and `infₛ` of the range of this function;
* `class CompleteLattice`: a bounded lattice such that `supₛ s` is always the least upper boundary
  of `s` and `infₛ s` is always the greatest lower boundary of `s`;
* `class CompleteLinearOrder`: a linear ordered complete lattice.

## Naming conventions

In lemma names,
* `supₛ` is called `supₛ`
* `infₛ` is called `infₛ`
* `⨆ i, s i` is called `supᵢ`
* `⨅ i, s i` is called `infᵢ`
* `⨆ i j, s i j` is called `supᵢ₂`. This is a `supᵢ` inside a `supᵢ`.
* `⨅ i j, s i j` is called `infᵢ₂`. This is an `infᵢ` inside an `infᵢ`.
* `⨆ i ∈ s, t i` is called `bsupᵢ` for "bounded `supᵢ`". This is the special case of `supᵢ₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `binfᵢ` for "bounded `infᵢ`". This is the special case of `infᵢ₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `supᵢ f`, the supremum of the range of `f`;
* `⨅ i, f i` : `infᵢ f`, the infimum of the range of `f`.
-/


open Function OrderDual Set

variable {α β β₂ γ : Type _} {ι ι' : Sort _} {κ : ι → Sort _} {κ' : ι' → Sort _}

/-- class for the `supₛ` operator -/
class SupSet (α : Type _) where
  supₛ : Set α → α
#align has_Sup SupSet
#align has_Sup.Sup SupSet.supₛ


/-- class for the `infₛ` operator -/
class InfSet (α : Type _) where
  infₛ : Set α → α
#align has_Inf InfSet
#align has_Inf.Inf InfSet.infₛ


export SupSet (supₛ)

export InfSet (infₛ)

/-- Supremum of a set -/
add_decl_doc SupSet.supₛ

/-- Infimum of a set -/
add_decl_doc InfSet.infₛ

/-- Indexed supremum -/
def supᵢ [SupSet α] {ι} (s : ι → α) : α :=
  supₛ (range s)
#align supr supᵢ

/-- Indexed infimum -/
def infᵢ [InfSet α] {ι} (s : ι → α) : α :=
  infₛ (range s)
#align infi infᵢ

instance (priority := 50) infSet_to_nonempty (α) [InfSet α] : Nonempty α :=
  ⟨infₛ ∅⟩
#align has_Inf_to_nonempty infSet_to_nonempty

instance (priority := 50) supSet_to_nonempty (α) [SupSet α] : Nonempty α :=
  ⟨supₛ ∅⟩
#align has_Sup_to_nonempty supSet_to_nonempty

/-
Porting note: the code below could replace the `notation3` command
open Std.ExtendedBinder in
syntax "⨆ " extBinder ", " term:51 : term

macro_rules
  | `(⨆ $x:ident, $p) => `(supᵢ fun $x:ident ↦ $p)
  | `(⨆ $x:ident : $t, $p) => `(supᵢ fun $x:ident : $t ↦ $p)
  | `(⨆ $x:ident $b:binderPred, $p) =>
    `(supᵢ fun $x:ident ↦ satisfies_binder_pred% $x $b ∧ $p) -/

/-- Indexed supremum. -/
notation3 "⨆ "(...)", "r:(scoped f => supᵢ f) => r

/-- Unexpander for the indexed supremum notation.-/
@[app_unexpander supᵢ]
def supᵢ.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ $p) => `(⨆ $x:ident, $p)
  | `($_ fun $x:ident : $ty:term ↦ $p) => `(⨆ $x:ident : $ty:term, $p)
  | _ => throw ()

/-- Indexed infimum. -/
notation3 "⨅ "(...)", "r:(scoped f => infᵢ f) => r

/-- Unexpander for the indexed infimum notation.-/
@[app_unexpander infᵢ]
def infᵢ.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ $p) => `(⨅ $x:ident, $p)
  | `($_ fun $x:ident : $ty:term ↦ $p) => `(⨅ $x:ident : $ty:term, $p)
  | _ => throw ()

instance OrderDual.supSet (α) [InfSet α] : SupSet αᵒᵈ :=
  ⟨(infₛ : Set α → α)⟩

instance OrderDual.infSet (α) [SupSet α] : InfSet αᵒᵈ :=
  ⟨(supₛ : Set α → α)⟩

/-- Note that we rarely use `CompleteSemilatticeSup`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
class CompleteSemilatticeSup (α : Type _) extends PartialOrder α, SupSet α where
  /-- Any element of a set is less than the set supremum. -/
  le_supₛ : ∀ s, ∀ a ∈ s, a ≤ supₛ s
  /-- Any upper bound is more than the set supremum. -/
  supₛ_le : ∀ s a, (∀ b ∈ s, b ≤ a) → supₛ s ≤ a
#align complete_semilattice_Sup CompleteSemilatticeSup

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b : α}

-- --@[ematch] Porting note: attribute removed
theorem le_supₛ : a ∈ s → a ≤ supₛ s :=
  CompleteSemilatticeSup.le_supₛ s a
#align le_Sup le_supₛ

theorem supₛ_le : (∀ b ∈ s, b ≤ a) → supₛ s ≤ a :=
  CompleteSemilatticeSup.supₛ_le s a
#align Sup_le supₛ_le

theorem isLUB_supₛ (s : Set α) : IsLUB s (supₛ s) :=
  ⟨fun _ ↦ le_supₛ, fun _ ↦ supₛ_le⟩
#align is_lub_Sup isLUB_supₛ

theorem IsLUB.supₛ_eq (h : IsLUB s a) : supₛ s = a :=
  (isLUB_supₛ s).unique h
#align is_lub.Sup_eq IsLUB.supₛ_eq

theorem le_supₛ_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ supₛ s :=
  le_trans h (le_supₛ hb)
#align le_Sup_of_le le_supₛ_of_le

theorem supₛ_le_supₛ (h : s ⊆ t) : supₛ s ≤ supₛ t :=
  (isLUB_supₛ s).mono (isLUB_supₛ t) h
#align Sup_le_Sup supₛ_le_supₛ

@[simp]
theorem supₛ_le_iff : supₛ s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_supₛ s)
#align Sup_le_iff supₛ_le_iff

theorem le_supₛ_iff : a ≤ supₛ s ↔ ∀ b ∈ upperBounds s, a ≤ b :=
  ⟨fun h _ hb => le_trans h (supₛ_le hb), fun hb => hb _ fun _ => le_supₛ⟩
#align le_Sup_iff le_supₛ_iff

theorem le_supᵢ_iff {s : ι → α} : a ≤ supᵢ s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by
  simp [supᵢ, le_supₛ_iff, upperBounds]
#align le_supr_iff le_supᵢ_iff

theorem supₛ_le_supₛ_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) : supₛ s ≤ supₛ t :=
  le_supₛ_iff.2 fun _ hb =>
    supₛ_le fun a ha =>
      let ⟨_, hct, hac⟩ := h a ha
      hac.trans (hb hct)
#align Sup_le_Sup_of_forall_exists_le supₛ_le_supₛ_of_forall_exists_le

-- We will generalize this to conditionally complete lattices in `csupₛ_singleton`.
theorem supₛ_singleton {a : α} : supₛ {a} = a :=
  isLUB_singleton.supₛ_eq
#align Sup_singleton supₛ_singleton

end

/-- Note that we rarely use `CompleteSemilatticeInf`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
class CompleteSemilatticeInf (α : Type _) extends PartialOrder α, InfSet α where
  /-- Any element of a set is more than the set infimum. -/
  infₛ_le : ∀ s, ∀ a ∈ s, infₛ s ≤ a
  /-- Any lower bound is less than the set infimum. -/
  le_infₛ : ∀ s a, (∀ b ∈ s, a ≤ b) → a ≤ infₛ s
#align complete_semilattice_Inf CompleteSemilatticeInf

section

variable [CompleteSemilatticeInf α] {s t : Set α} {a b : α}

-- --@[ematch] Porting note: attribute removed
theorem infₛ_le : a ∈ s → infₛ s ≤ a :=
  CompleteSemilatticeInf.infₛ_le s a
#align Inf_le infₛ_le

theorem le_infₛ : (∀ b ∈ s, a ≤ b) → a ≤ infₛ s :=
  CompleteSemilatticeInf.le_infₛ s a
#align le_Inf le_infₛ

theorem isGLB_infₛ (s : Set α) : IsGLB s (infₛ s) :=
  ⟨fun _ => infₛ_le, fun _ => le_infₛ⟩
#align is_glb_Inf isGLB_infₛ

theorem IsGLB.infₛ_eq (h : IsGLB s a) : infₛ s = a :=
  (isGLB_infₛ s).unique h
#align is_glb.Inf_eq IsGLB.infₛ_eq

theorem infₛ_le_of_le (hb : b ∈ s) (h : b ≤ a) : infₛ s ≤ a :=
  le_trans (infₛ_le hb) h
#align Inf_le_of_le infₛ_le_of_le

theorem infₛ_le_infₛ (h : s ⊆ t) : infₛ t ≤ infₛ s :=
  (isGLB_infₛ s).mono (isGLB_infₛ t) h
#align Inf_le_Inf infₛ_le_infₛ

@[simp]
theorem le_infₛ_iff : a ≤ infₛ s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_infₛ s)
#align le_Inf_iff le_infₛ_iff

theorem infₛ_le_iff : infₛ s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h _ hb => le_trans (le_infₛ hb) h, fun hb => hb _ fun _ => infₛ_le⟩
#align Inf_le_iff infₛ_le_iff

theorem infᵢ_le_iff {s : ι → α} : infᵢ s ≤ a ↔ ∀ b, (∀ i, b ≤ s i) → b ≤ a := by
  simp [infᵢ, infₛ_le_iff, lowerBounds]
#align infi_le_iff infᵢ_le_iff

theorem infₛ_le_infₛ_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) : infₛ t ≤ infₛ s :=
  le_of_forall_le
    (by
      simp only [le_infₛ_iff]
      introv h₀ h₁
      rcases h _ h₁ with ⟨y, hy, hy'⟩
      solve_by_elim [le_trans _ hy'])
#align Inf_le_Inf_of_forall_exists_le infₛ_le_infₛ_of_forall_exists_le

-- We will generalize this to conditionally complete lattices in `cInf_singleton`.
theorem infₛ_singleton {a : α} : infₛ {a} = a :=
  isGLB_singleton.infₛ_eq
#align Inf_singleton infₛ_singleton

end

/-- A complete lattice is a bounded lattice which has supᵢema and infima for every subset. -/
class CompleteLattice (α : Type _) extends Lattice α, CompleteSemilatticeSup α,
  CompleteSemilatticeInf α, Top α, Bot α where
  /-- Any element is less than the top one. -/
  protected le_top : ∀ x : α, x ≤ ⊤
  /-- Any element is more than the bottom one. -/
  protected bot_le : ∀ x : α, ⊥ ≤ x
#align complete_lattice CompleteLattice

-- see Note [lower instance priority]
instance (priority := 100) CompleteLattice.toBoundedOrder [h : CompleteLattice α] :
    BoundedOrder α :=
  { h with }
#align complete_lattice.to_bounded_order CompleteLattice.toBoundedOrder

/-- Create a `CompleteLattice` from a `PartialOrder` and `InfSet`
that returns the greatest lower bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `CompleteLattice`
instance as
```
instance : CompleteLattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, supₛ, bot, top
  ..completeLatticeOfInf my_T _ }
```
-/
def completeLatticeOfInf (α : Type _) [H1 : PartialOrder α] [H2 : InfSet α]
    (isGLB_infₛ : ∀ s : Set α, IsGLB s (infₛ s)) : CompleteLattice α :=
  { H1, H2 with
    bot := infₛ univ
    bot_le := fun x => (isGLB_infₛ univ).1 trivial
    top := infₛ ∅
    le_top := fun a => (isGLB_infₛ ∅).2 <| by simp
    sup := fun a b => infₛ { x : α | a ≤ x ∧ b ≤ x }
    inf := fun a b => infₛ {a, b}
    le_inf := fun a b c hab hac => by
      apply (isGLB_infₛ _).2
      simp [*]
    inf_le_right := fun a b => (isGLB_infₛ _).1 <| mem_insert_of_mem _ <| mem_singleton _
    inf_le_left := fun a b => (isGLB_infₛ _).1 <| mem_insert _ _
    sup_le := fun a b c hac hbc => (isGLB_infₛ _).1 <| by simp [*]
    le_sup_left := fun a b => (isGLB_infₛ _).2 fun x => And.left
    le_sup_right := fun a b => (isGLB_infₛ _).2 fun x => And.right
    le_infₛ := fun s a ha => (isGLB_infₛ s).2 ha
    infₛ_le := fun s a ha => (isGLB_infₛ s).1 ha
    supₛ := fun s => infₛ (upperBounds s)
    le_supₛ := fun s a ha => (isGLB_infₛ (upperBounds s)).2 fun b hb => hb ha
    supₛ_le := fun s a ha => (isGLB_infₛ (upperBounds s)).1 ha }
#align complete_lattice_of_Inf completeLatticeOfInf

/-- Any `CompleteSemilatticeInf` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfInf`.
-/
def completeLatticeOfCompleteSemilatticeInf (α : Type _) [CompleteSemilatticeInf α] :
    CompleteLattice α :=
  completeLatticeOfInf α fun s => isGLB_infₛ s
#align complete_lattice_of_complete_semilattice_Inf completeLatticeOfCompleteSemilatticeInf

/-- Create a `CompleteLattice` from a `PartialOrder` and `SupSet`
that returns the least upper bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `CompleteLattice`
instance as
```
instance : CompleteLattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, infₛ, bot, top
  ..completeLatticeOfSup my_T _ }
```
-/
def completeLatticeOfSup (α : Type _) [H1 : PartialOrder α] [H2 : SupSet α]
    (isLUB_supₛ : ∀ s : Set α, IsLUB s (supₛ s)) : CompleteLattice α :=
  { H1, H2 with
    top := supₛ univ
    le_top := fun x => (isLUB_supₛ univ).1 trivial
    bot := supₛ ∅
    bot_le := fun x => (isLUB_supₛ ∅).2 <| by simp
    sup := fun a b => supₛ {a, b}
    sup_le := fun a b c hac hbc => (isLUB_supₛ _).2 (by simp [*])
    le_sup_left := fun a b => (isLUB_supₛ _).1 <| mem_insert _ _
    le_sup_right := fun a b => (isLUB_supₛ _).1 <| mem_insert_of_mem _ <| mem_singleton _
    inf := fun a b => supₛ { x | x ≤ a ∧ x ≤ b }
    le_inf := fun a b c hab hac => (isLUB_supₛ _).1 <| by simp [*]
    inf_le_left := fun a b => (isLUB_supₛ _).2 fun x => And.left
    inf_le_right := fun a b => (isLUB_supₛ _).2 fun x => And.right
    infₛ := fun s => supₛ (lowerBounds s)
    supₛ_le := fun s a ha => (isLUB_supₛ s).2 ha
    le_supₛ := fun s a ha => (isLUB_supₛ s).1 ha
    infₛ_le := fun s a ha => (isLUB_supₛ (lowerBounds s)).2 fun b hb => hb ha
    le_infₛ := fun s a ha => (isLUB_supₛ (lowerBounds s)).1 ha }
#align complete_lattice_of_Sup completeLatticeOfSup

/-- Any `CompleteSemilatticeSup` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfSup`.
-/
def completeLatticeOfCompleteSemilatticeSup (α : Type _) [CompleteSemilatticeSup α] :
    CompleteLattice α :=
  completeLatticeOfSup α fun s => isLUB_supₛ s
#align complete_lattice_of_complete_semilattice_Sup completeLatticeOfCompleteSemilatticeSup

-- Porting note: as we cannot rename fields while extending,
-- `CompleteLinearOrder` does not directly extend `LinearOrder`.
-- Instead we add the fields by hand, and write a manual instance.

/-- A complete linear order is a linear order whose lattice structure is complete. -/
class CompleteLinearOrder (α : Type _) extends CompleteLattice α where
  /-- A linear order is total. -/
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidable_le : DecidableRel (. ≤ . : α → α → Prop)
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidable_eq : DecidableEq α := @decidableEq_of_decidableLE _ _ decidable_le
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidable_lt : DecidableRel (. < . : α → α → Prop) :=
    @decidableLT_of_decidableLE _ _ decidable_le
#align complete_linear_order CompleteLinearOrder

instance CompleteLinearOrder.toLinearOrder [i : CompleteLinearOrder α] : LinearOrder α :=
  { i with
    min := Inf.inf
    max := Sup.sup
    min_def := fun a b => by
      split_ifs with h
      . simp [h]
      . simp [(CompleteLinearOrder.le_total a b).resolve_left h]
    max_def :=  fun a b => by
      split_ifs with h
      . simp [h]
      . simp [(CompleteLinearOrder.le_total a b).resolve_left h] }

namespace OrderDual

variable (α)

instance completeLattice [CompleteLattice α] : CompleteLattice αᵒᵈ :=
  { OrderDual.lattice α, OrderDual.supSet α, OrderDual.infSet α, OrderDual.boundedOrder α with
    le_supₛ := @CompleteLattice.infₛ_le α _
    supₛ_le := @CompleteLattice.le_infₛ α _
    infₛ_le := @CompleteLattice.le_supₛ α _
    le_infₛ := @CompleteLattice.supₛ_le α _ }

instance [CompleteLinearOrder α] : CompleteLinearOrder αᵒᵈ :=
  { OrderDual.completeLattice α, OrderDual.linearOrder α with }

end OrderDual

open OrderDual

section

variable [CompleteLattice α] {s t : Set α} {a b : α}

@[simp]
theorem toDual_supₛ (s : Set α) : toDual (supₛ s) = infₛ (ofDual ⁻¹' s) :=
  rfl
#align to_dual_Sup toDual_supₛ

@[simp]
theorem toDual_infₛ (s : Set α) : toDual (infₛ s) = supₛ (ofDual ⁻¹' s) :=
  rfl
#align to_dual_Inf toDual_infₛ

@[simp]
theorem ofDual_supₛ (s : Set αᵒᵈ) : ofDual (supₛ s) = infₛ (toDual ⁻¹' s) :=
  rfl
#align of_dual_Sup ofDual_supₛ

@[simp]
theorem ofDual_infₛ (s : Set αᵒᵈ) : ofDual (infₛ s) = supₛ (toDual ⁻¹' s) :=
  rfl
#align of_dual_Inf ofDual_infₛ

@[simp]
theorem toDual_supᵢ (f : ι → α) : toDual (⨆ i, f i) = ⨅ i, toDual (f i) :=
  rfl
#align to_dual_supr toDual_supᵢ

@[simp]
theorem toDual_infᵢ (f : ι → α) : toDual (⨅ i, f i) = ⨆ i, toDual (f i) :=
  rfl
#align to_dual_infi toDual_infᵢ

@[simp]
theorem ofDual_supᵢ (f : ι → αᵒᵈ) : ofDual (⨆ i, f i) = ⨅ i, ofDual (f i) :=
  rfl
#align of_dual_supr ofDual_supᵢ

@[simp]
theorem ofDual_infᵢ (f : ι → αᵒᵈ) : ofDual (⨅ i, f i) = ⨆ i, ofDual (f i) :=
  rfl
#align of_dual_infi ofDual_infᵢ

theorem infₛ_le_supₛ (hs : s.Nonempty) : infₛ s ≤ supₛ s :=
  isGLB_le_isLUB (isGLB_infₛ s) (isLUB_supₛ s) hs
#align Inf_le_Sup infₛ_le_supₛ

theorem supₛ_union {s t : Set α} : supₛ (s ∪ t) = supₛ s ⊔ supₛ t :=
  ((isLUB_supₛ s).union (isLUB_supₛ t)).supₛ_eq
#align Sup_union supₛ_union

theorem infₛ_union {s t : Set α} : infₛ (s ∪ t) = infₛ s ⊓ infₛ t :=
  ((isGLB_infₛ s).union (isGLB_infₛ t)).infₛ_eq
#align Inf_union infₛ_union

theorem supₛ_inter_le {s t : Set α} : supₛ (s ∩ t) ≤ supₛ s ⊓ supₛ t :=
  supₛ_le fun _ hb => le_inf (le_supₛ hb.1) (le_supₛ hb.2)
#align Sup_inter_le supₛ_inter_le

theorem le_infₛ_inter {s t : Set α} : infₛ s ⊔ infₛ t ≤ infₛ (s ∩ t) :=
  @supₛ_inter_le αᵒᵈ _ _ _
#align le_Inf_inter le_infₛ_inter

@[simp]
theorem supₛ_empty : supₛ ∅ = (⊥ : α) :=
  (@isLUB_empty α _ _).supₛ_eq
#align Sup_empty supₛ_empty

@[simp]
theorem infₛ_empty : infₛ ∅ = (⊤ : α) :=
  (@isGLB_empty α _ _).infₛ_eq
#align Inf_empty infₛ_empty

@[simp]
theorem supₛ_univ : supₛ univ = (⊤ : α) :=
  (@isLUB_univ α _ _).supₛ_eq
#align Sup_univ supₛ_univ

@[simp]
theorem infₛ_univ : infₛ univ = (⊥ : α) :=
  (@isGLB_univ α _ _).infₛ_eq
#align Inf_univ infₛ_univ

-- TODO(Jeremy): get this automatically
@[simp]
theorem supₛ_insert {a : α} {s : Set α} : supₛ (insert a s) = a ⊔ supₛ s :=
  ((isLUB_supₛ s).insert a).supₛ_eq
#align Sup_insert supₛ_insert

@[simp]
theorem infₛ_insert {a : α} {s : Set α} : infₛ (insert a s) = a ⊓ infₛ s :=
  ((isGLB_infₛ s).insert a).infₛ_eq
#align Inf_insert infₛ_insert

theorem supₛ_le_supₛ_of_subset_insert_bot (h : s ⊆ insert ⊥ t) : supₛ s ≤ supₛ t :=
  le_trans (supₛ_le_supₛ h) (le_of_eq (_root_.trans supₛ_insert bot_sup_eq))
#align Sup_le_Sup_of_subset_insert_bot supₛ_le_supₛ_of_subset_insert_bot

theorem infₛ_le_infₛ_of_subset_insert_top (h : s ⊆ insert ⊤ t) : infₛ t ≤ infₛ s :=
  le_trans (le_of_eq (_root_.trans top_inf_eq.symm infₛ_insert.symm)) (infₛ_le_infₛ h)
#align Inf_le_Inf_of_subset_insert_top infₛ_le_infₛ_of_subset_insert_top

@[simp]
theorem supₛ_diff_singleton_bot (s : Set α) : supₛ (s \ {⊥}) = supₛ s :=
  (supₛ_le_supₛ (diff_subset _ _)).antisymm <|
    supₛ_le_supₛ_of_subset_insert_bot <| subset_insert_diff_singleton _ _
#align Sup_diff_singleton_bot supₛ_diff_singleton_bot

@[simp]
theorem infₛ_diff_singleton_top (s : Set α) : infₛ (s \ {⊤}) = infₛ s :=
  @supₛ_diff_singleton_bot αᵒᵈ _ s
#align Inf_diff_singleton_top infₛ_diff_singleton_top

theorem supₛ_pair {a b : α} : supₛ {a, b} = a ⊔ b :=
  (@isLUB_pair α _ a b).supₛ_eq
#align Sup_pair supₛ_pair

theorem infₛ_pair {a b : α} : infₛ {a, b} = a ⊓ b :=
  (@isGLB_pair α _ a b).infₛ_eq
#align Inf_pair infₛ_pair

@[simp]
theorem supₛ_eq_bot : supₛ s = ⊥ ↔ ∀ a ∈ s, a = ⊥ :=
  ⟨fun h _ ha => bot_unique <| h ▸ le_supₛ ha, fun h =>
    bot_unique <| supₛ_le fun a ha => le_bot_iff.2 <| h a ha⟩
#align Sup_eq_bot supₛ_eq_bot

@[simp]
theorem infₛ_eq_top : infₛ s = ⊤ ↔ ∀ a ∈ s, a = ⊤ :=
  @supₛ_eq_bot αᵒᵈ _ _
#align Inf_eq_top infₛ_eq_top

theorem eq_singleton_bot_of_supₛ_eq_bot_of_nonempty {s : Set α} (h_sup : supₛ s = ⊥)
    (hne : s.Nonempty) : s = {⊥} := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [supₛ_eq_bot] at h_sup
  exact ⟨hne, h_sup⟩
#align eq_singleton_bot_of_Sup_eq_bot_of_nonempty eq_singleton_bot_of_supₛ_eq_bot_of_nonempty

theorem eq_singleton_top_of_infₛ_eq_top_of_nonempty : infₛ s = ⊤ → s.Nonempty → s = {⊤} :=
  @eq_singleton_bot_of_supₛ_eq_bot_of_nonempty αᵒᵈ _ _
#align eq_singleton_top_of_Inf_eq_top_of_nonempty eq_singleton_top_of_infₛ_eq_top_of_nonempty

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w < b`.
See `csupₛ_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem supₛ_eq_of_forall_le_of_forall_lt_exists_gt (h₁ : ∀ a ∈ s, a ≤ b)
    (h₂ : ∀ w, w < b → ∃ a ∈ s, w < a) : supₛ s = b :=
  (supₛ_le h₁).eq_of_not_lt fun h =>
    let ⟨_, ha, ha'⟩ := h₂ _ h
    ((le_supₛ ha).trans_lt ha').false
#align Sup_eq_of_forall_le_of_forall_lt_exists_gt supₛ_eq_of_forall_le_of_forall_lt_exists_gt

/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w > b`.
See `cinfₛ_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem infₛ_eq_of_forall_ge_of_forall_gt_exists_lt :
    (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → infₛ s = b :=
  @supₛ_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _
#align Inf_eq_of_forall_ge_of_forall_gt_exists_lt infₛ_eq_of_forall_ge_of_forall_gt_exists_lt

end

section CompleteLinearOrder

variable [CompleteLinearOrder α] {s t : Set α} {a b : α}

theorem lt_supₛ_iff : b < supₛ s ↔ ∃ a ∈ s, b < a :=
  lt_isLUB_iff <| isLUB_supₛ s
#align lt_Sup_iff lt_supₛ_iff

theorem infₛ_lt_iff : infₛ s < b ↔ ∃ a ∈ s, a < b :=
  isGLB_lt_iff <| isGLB_infₛ s
#align Inf_lt_iff infₛ_lt_iff

theorem supₛ_eq_top : supₛ s = ⊤ ↔ ∀ b < ⊤, ∃ a ∈ s, b < a :=
  ⟨fun h _ hb => lt_supₛ_iff.1 <| hb.trans_eq h.symm, fun h =>
    top_unique <|
      le_of_not_gt fun h' =>
        let ⟨_, ha, h⟩ := h _ h'
        (h.trans_le <| le_supₛ ha).false⟩
#align Sup_eq_top supₛ_eq_top

theorem infₛ_eq_bot : infₛ s = ⊥ ↔ ∀ b > ⊥, ∃ a ∈ s, a < b :=
  @supₛ_eq_top αᵒᵈ _ _
#align Inf_eq_bot infₛ_eq_bot

theorem lt_supᵢ_iff {f : ι → α} : a < supᵢ f ↔ ∃ i, a < f i :=
  lt_supₛ_iff.trans exists_range_iff
#align lt_supr_iff lt_supᵢ_iff

theorem infᵢ_lt_iff {f : ι → α} : infᵢ f < a ↔ ∃ i, f i < a :=
  infₛ_lt_iff.trans exists_range_iff
#align infi_lt_iff infᵢ_lt_iff

end CompleteLinearOrder

/-
### supᵢ & infᵢ
-/
section SupSet

variable [SupSet α] {f g : ι → α}

theorem supₛ_range : supₛ (range f) = supᵢ f :=
  rfl
#align Sup_range supₛ_range

theorem supₛ_eq_supᵢ' (s : Set α) : supₛ s = ⨆ a : s, (a : α) := by rw [supᵢ, Subtype.range_coe]
#align Sup_eq_supr' supₛ_eq_supᵢ'

theorem supᵢ_congr (h : ∀ i, f i = g i) : (⨆ i, f i) = ⨆ i, g i :=
  congr_arg _ <| funext h
#align supr_congr supᵢ_congr

theorem Function.Surjective.supᵢ_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    (⨆ x, g (f x)) = ⨆ y, g y := by
  simp [supᵢ]
  congr
  exact hf.range_comp g
#align function.surjective.supr_comp Function.Surjective.supᵢ_comp

theorem Equiv.supᵢ_comp {g : ι' → α} (e : ι ≃ ι') : (⨆ x, g (e x)) = ⨆ y, g y :=
  e.surjective.supᵢ_comp _
#align equiv.supr_comp Equiv.supᵢ_comp

protected theorem Function.Surjective.supᵢ_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⨆ x, f x) = ⨆ y, g y := by
  convert h1.supᵢ_comp g
  exact (h2 _).symm
#align function.surjective.supr_congr Function.Surjective.supᵢ_congr

protected theorem Equiv.supᵢ_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    (⨆ x, f x) = ⨆ y, g y :=
  e.surjective.supᵢ_congr _ h
#align equiv.supr_congr Equiv.supᵢ_congr

@[congr]
theorem supᵢ_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : supᵢ f₁ = supᵢ f₂ := by
  obtain rfl := propext pq
  congr with x
  apply f
#align supr_congr_Prop supᵢ_congr_Prop

theorem supᵢ_plift_up (f : PLift ι → α) : (⨆ i, f (PLift.up i)) = ⨆ i, f i :=
  (PLift.up_surjective.supᵢ_congr _) fun _ => rfl
#align supr_plift_up supᵢ_plift_up

theorem supᵢ_plift_down (f : ι → α) : (⨆ i, f (PLift.down i)) = ⨆ i, f i :=
  (PLift.down_surjective.supᵢ_congr _) fun _ => rfl
#align supr_plift_down supᵢ_plift_down

theorem supᵢ_range' (g : β → α) (f : ι → β) : (⨆ b : range f, g b) = ⨆ i, g (f i) := by
  rw [supᵢ, supᵢ, ← image_eq_range, ← range_comp]
  rfl
#align supr_range' supᵢ_range'

theorem supₛ_image' {s : Set β} {f : β → α} : supₛ (f '' s) = ⨆ a : s, f a := by
  rw [supᵢ, image_eq_range]
#align Sup_image' supₛ_image'

end SupSet

section InfSet

variable [InfSet α] {f g : ι → α}

theorem infₛ_range : infₛ (range f) = infᵢ f :=
  rfl
#align Inf_range infₛ_range

theorem infₛ_eq_infᵢ' (s : Set α) : infₛ s = ⨅ a : s, (a : α) :=
  @supₛ_eq_supᵢ' αᵒᵈ _ _
#align Inf_eq_infi' infₛ_eq_infᵢ'

theorem infᵢ_congr (h : ∀ i, f i = g i) : (⨅ i, f i) = ⨅ i, g i :=
  congr_arg _ <| funext h
#align infi_congr infᵢ_congr

theorem Function.Surjective.infᵢ_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    (⨅ x, g (f x)) = ⨅ y, g y :=
  @Function.Surjective.supᵢ_comp αᵒᵈ _ _ _ f hf g
#align function.surjective.infi_comp Function.Surjective.infᵢ_comp

theorem Equiv.infᵢ_comp {g : ι' → α} (e : ι ≃ ι') : (⨅ x, g (e x)) = ⨅ y, g y :=
  @Equiv.supᵢ_comp αᵒᵈ _ _ _ _ e
#align equiv.infi_comp Equiv.infᵢ_comp

protected theorem Function.Surjective.infᵢ_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⨅ x, f x) = ⨅ y, g y :=
  @Function.Surjective.supᵢ_congr αᵒᵈ _ _ _ _ _ h h1 h2
#align function.surjective.infi_congr Function.Surjective.infᵢ_congr

protected theorem Equiv.infᵢ_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    (⨅ x, f x) = ⨅ y, g y :=
  @Equiv.supᵢ_congr αᵒᵈ _ _ _ _ _ e h
#align equiv.infi_congr Equiv.infᵢ_congr

@[congr]
theorem infᵢ_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : infᵢ f₁ = infᵢ f₂ :=
  @supᵢ_congr_Prop αᵒᵈ _ p q f₁ f₂ pq f
#align infi_congr_Prop infᵢ_congr_Prop

theorem infᵢ_plift_up (f : PLift ι → α) : (⨅ i, f (PLift.up i)) = ⨅ i, f i :=
  (PLift.up_surjective.infᵢ_congr _) fun _ => rfl
#align infi_plift_up infᵢ_plift_up

theorem infᵢ_plift_down (f : ι → α) : (⨅ i, f (PLift.down i)) = ⨅ i, f i :=
  (PLift.down_surjective.infᵢ_congr _) fun _ => rfl
#align infi_plift_down infᵢ_plift_down

theorem infᵢ_range' (g : β → α) (f : ι → β) : (⨅ b : range f, g b) = ⨅ i, g (f i) :=
  @supᵢ_range' αᵒᵈ _ _ _ _ _
#align infi_range' infᵢ_range'

theorem infₛ_image' {s : Set β} {f : β → α} : infₛ (f '' s) = ⨅ a : s, f a :=
  @supₛ_image' αᵒᵈ _ _ _ _
#align Inf_image' infₛ_image'

end InfSet

section

variable [CompleteLattice α] {f g s t : ι → α} {a b : α}

-- TODO: this declaration gives error when starting smt state
----@[ematch] Porting note: attribute removed
theorem le_supᵢ (f : ι → α) (i : ι) : f i ≤ supᵢ f :=
  le_supₛ ⟨i, rfl⟩
#align le_supr le_supᵢ

theorem infᵢ_le (f : ι → α) (i : ι) : infᵢ f ≤ f i :=
  infₛ_le ⟨i, rfl⟩
#align infi_le infᵢ_le

-- --@[ematch] Porting note: attribute removed
theorem le_supᵢ' (f : ι → α) (i : ι) : f i ≤ supᵢ f :=
  le_supₛ ⟨i, rfl⟩
#align le_supr' le_supᵢ'

----@[ematch] Porting note: attribute removed
theorem infᵢ_le' (f : ι → α) (i : ι) : infᵢ f ≤ f i :=
  infₛ_le ⟨i, rfl⟩
#align infi_le' infᵢ_le'

/- TODO: this version would be more powerful, but, alas, the pattern matcher
   doesn't accept it.
--@[ematch] lemma le_supᵢ' (f : ι → α) (i : ι) : (: f i :) ≤ (: supᵢ f :) :=
le_supₛ ⟨i, rfl⟩
-/
theorem isLUB_supᵢ : IsLUB (range f) (⨆ j, f j) :=
  isLUB_supₛ _
#align is_lub_supr isLUB_supᵢ

theorem isGLB_infᵢ : IsGLB (range f) (⨅ j, f j) :=
  isGLB_infₛ _
#align is_glb_infi isGLB_infᵢ

theorem IsLUB.supᵢ_eq (h : IsLUB (range f) a) : (⨆ j, f j) = a :=
  h.supₛ_eq
#align is_lub.supr_eq IsLUB.supᵢ_eq

theorem IsGLB.infᵢ_eq (h : IsGLB (range f) a) : (⨅ j, f j) = a :=
  h.infₛ_eq
#align is_glb.infi_eq IsGLB.infᵢ_eq

theorem le_supᵢ_of_le (i : ι) (h : a ≤ f i) : a ≤ supᵢ f :=
  h.trans <| le_supᵢ _ i
#align le_supr_of_le le_supᵢ_of_le

theorem infᵢ_le_of_le (i : ι) (h : f i ≤ a) : infᵢ f ≤ a :=
  (infᵢ_le _ i).trans h
#align infi_le_of_le infᵢ_le_of_le

theorem le_supᵢ₂ {f : ∀ i, κ i → α} (i : ι) (j : κ i) : f i j ≤ ⨆ (i) (j), f i j :=
  le_supᵢ_of_le i <| le_supᵢ (f i) j
#align le_supr₂ le_supᵢ₂

theorem infᵢ₂_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) : (⨅ (i) (j), f i j) ≤ f i j :=
  infᵢ_le_of_le i <| infᵢ_le (f i) j
#align infi₂_le infᵢ₂_le

theorem le_supᵢ₂_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : a ≤ f i j) :
    a ≤ ⨆ (i) (j), f i j :=
  h.trans <| le_supᵢ₂ i j
#align le_supr₂_of_le le_supᵢ₂_of_le

theorem infᵢ₂_le_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : f i j ≤ a) :
    (⨅ (i) (j), f i j) ≤ a :=
  (infᵢ₂_le i j).trans h
#align infi₂_le_of_le infᵢ₂_le_of_le

theorem supᵢ_le (h : ∀ i, f i ≤ a) : supᵢ f ≤ a :=
  supₛ_le fun _ ⟨i, Eq⟩ => Eq ▸ h i
#align supr_le supᵢ_le

theorem le_infᵢ (h : ∀ i, a ≤ f i) : a ≤ infᵢ f :=
  le_infₛ fun _ ⟨i, Eq⟩ => Eq ▸ h i
#align le_infi le_infᵢ

theorem supᵢ₂_le {f : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ a) : (⨆ (i) (j), f i j) ≤ a :=
  supᵢ_le fun i => supᵢ_le <| h i
#align supr₂_le supᵢ₂_le

theorem le_infᵢ₂ {f : ∀ i, κ i → α} (h : ∀ i j, a ≤ f i j) : a ≤ ⨅ (i) (j), f i j :=
  le_infᵢ fun i => le_infᵢ <| h i
#align le_infi₂ le_infᵢ₂

theorem supᵢ₂_le_supᵢ (κ : ι → Sort _) (f : ι → α) : (⨆ (i) (_j : κ i), f i) ≤ ⨆ i, f i :=
  supᵢ₂_le fun i _ => le_supᵢ f i
#align supr₂_le_supr supᵢ₂_le_supᵢ

theorem infᵢ_le_infᵢ₂ (κ : ι → Sort _) (f : ι → α) : (⨅ i, f i) ≤ ⨅ (i) (_j : κ i), f i :=
  le_infᵢ₂ fun i _ => infᵢ_le f i
#align infi_le_infi₂ infᵢ_le_infᵢ₂

theorem supᵢ_mono (h : ∀ i, f i ≤ g i) : supᵢ f ≤ supᵢ g :=
  supᵢ_le fun i => le_supᵢ_of_le i <| h i
#align supr_mono supᵢ_mono

theorem infᵢ_mono (h : ∀ i, f i ≤ g i) : infᵢ f ≤ infᵢ g :=
  le_infᵢ fun i => infᵢ_le_of_le i <| h i
#align infi_mono infᵢ_mono

theorem supᵢ₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    (⨆ (i) (j), f i j) ≤ ⨆ (i) (j), g i j :=
  supᵢ_mono fun i => supᵢ_mono <| h i
#align supr₂_mono supᵢ₂_mono

theorem infᵢ₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    (⨅ (i) (j), f i j) ≤ ⨅ (i) (j), g i j :=
  infᵢ_mono fun i => infᵢ_mono <| h i
#align infi₂_mono infᵢ₂_mono

theorem supᵢ_mono' {g : ι' → α} (h : ∀ i, ∃ i', f i ≤ g i') : supᵢ f ≤ supᵢ g :=
  supᵢ_le fun i => Exists.elim (h i) le_supᵢ_of_le
#align supr_mono' supᵢ_mono'

theorem infᵢ_mono' {g : ι' → α} (h : ∀ i', ∃ i, f i ≤ g i') : infᵢ f ≤ infᵢ g :=
  le_infᵢ fun i' => Exists.elim (h i') infᵢ_le_of_le
#align infi_mono' infᵢ_mono'

theorem supᵢ₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i j ≤ g i' j') :
    (⨆ (i) (j), f i j) ≤ ⨆ (i) (j), g i j :=
  supᵢ₂_le fun i j =>
    let ⟨i', j', h⟩ := h i j
    le_supᵢ₂_of_le i' j' h
#align supr₂_mono' supᵢ₂_mono'

theorem infᵢ₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i' j' ≤ g i j) :
    (⨅ (i) (j), f i j) ≤ ⨅ (i) (j), g i j :=
  le_infᵢ₂ fun i j =>
    let ⟨i', j', h⟩ := h i j
    infᵢ₂_le_of_le i' j' h
#align infi₂_mono' infᵢ₂_mono'

theorem supᵢ_const_mono (h : ι → ι') : (⨆ _i : ι, a) ≤ ⨆ _j : ι', a :=
  supᵢ_le <| le_supᵢ _ ∘ h
#align supr_const_mono supᵢ_const_mono

theorem infᵢ_const_mono (h : ι' → ι) : (⨅ _i : ι, a) ≤ ⨅ _j : ι', a :=
  le_infᵢ <| infᵢ_le _ ∘ h
#align infi_const_mono infᵢ_const_mono

theorem supᵢ_infᵢ_le_infᵢ_supᵢ (f : ι → ι' → α) : (⨆ i, ⨅ j, f i j) ≤ ⨅ j, ⨆ i, f i j :=
  supᵢ_le fun i => infᵢ_mono fun j => le_supᵢ (fun i => f i j) i
#align supr_infi_le_infi_supr supᵢ_infᵢ_le_infᵢ_supᵢ

theorem bsupᵢ_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    (⨆ (i) (_h : p i), f i) ≤ ⨆ (i) (_h : q i), f i :=
  supᵢ_mono fun i => supᵢ_const_mono (hpq i)
#align bsupr_mono bsupᵢ_mono

theorem binfᵢ_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    (⨅ (i) (_h : q i), f i) ≤ ⨅ (i) (_h : p i), f i :=
  infᵢ_mono fun i => infᵢ_const_mono (hpq i)
#align binfi_mono binfᵢ_mono

@[simp]
theorem supᵢ_le_iff : supᵢ f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff isLUB_supᵢ).trans forall_range_iff
#align supr_le_iff supᵢ_le_iff

@[simp]
theorem le_infᵢ_iff : a ≤ infᵢ f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff isGLB_infᵢ).trans forall_range_iff
#align le_infi_iff le_infᵢ_iff

theorem supᵢ₂_le_iff {f : ∀ i, κ i → α} : (⨆ (i) (j), f i j) ≤ a ↔ ∀ i j, f i j ≤ a := by
  simp_rw [supᵢ_le_iff]
#align supr₂_le_iff supᵢ₂_le_iff

theorem le_infᵢ₂_iff {f : ∀ i, κ i → α} : (a ≤ ⨅ (i) (j), f i j) ↔ ∀ i j, a ≤ f i j := by
  simp_rw [le_infᵢ_iff]
#align le_infi₂_iff le_infᵢ₂_iff

theorem supᵢ_lt_iff : supᵢ f < a ↔ ∃ b, b < a ∧ ∀ i, f i ≤ b :=
  ⟨fun h => ⟨supᵢ f, h, le_supᵢ f⟩, fun ⟨_, h, hb⟩ => (supᵢ_le hb).trans_lt h⟩
#align supr_lt_iff supᵢ_lt_iff

theorem lt_infᵢ_iff : a < infᵢ f ↔ ∃ b, a < b ∧ ∀ i, b ≤ f i :=
  ⟨fun h => ⟨infᵢ f, h, infᵢ_le f⟩, fun ⟨_, h, hb⟩ => h.trans_le <| le_infᵢ hb⟩
#align lt_infi_iff lt_infᵢ_iff

theorem supₛ_eq_supᵢ {s : Set α} : supₛ s = ⨆ a ∈ s, a :=
  le_antisymm (supₛ_le le_supᵢ₂) (supᵢ₂_le fun _ => le_supₛ)
#align Sup_eq_supr supₛ_eq_supᵢ

theorem infₛ_eq_infᵢ {s : Set α} : infₛ s = ⨅ a ∈ s, a :=
  @supₛ_eq_supᵢ αᵒᵈ _ _
#align Inf_eq_infi infₛ_eq_infᵢ

theorem Monotone.le_map_supᵢ [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    (⨆ i, f (s i)) ≤ f (supᵢ s) :=
  supᵢ_le fun _ => hf <| le_supᵢ _ _
#align monotone.le_map_supr Monotone.le_map_supᵢ

theorem Antitone.le_map_infᵢ [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    (⨆ i, f (s i)) ≤ f (infᵢ s) :=
  hf.dual_left.le_map_supᵢ
#align antitone.le_map_infi Antitone.le_map_infᵢ

theorem Monotone.le_map_supᵢ₂ [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    (⨆ (i) (j), f (s i j)) ≤ f (⨆ (i) (j), s i j) :=
  supᵢ₂_le fun _ _ => hf <| le_supᵢ₂ _ _
#align monotone.le_map_supr₂ Monotone.le_map_supᵢ₂

theorem Antitone.le_map_infᵢ₂ [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    (⨆ (i) (j), f (s i j)) ≤ f (⨅ (i) (j), s i j) :=
  hf.dual_left.le_map_supᵢ₂ _
#align antitone.le_map_infi₂ Antitone.le_map_infᵢ₂

theorem Monotone.le_map_supₛ [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    (⨆ a ∈ s, f a) ≤ f (supₛ s) := by rw [supₛ_eq_supᵢ] ; exact hf.le_map_supᵢ₂ _
#align monotone.le_map_Sup Monotone.le_map_supₛ

theorem Antitone.le_map_infₛ [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    (⨆ a ∈ s, f a) ≤ f (infₛ s) :=
  hf.dual_left.le_map_supₛ
#align antitone.le_map_Inf Antitone.le_map_infₛ

theorem OrderIso.map_supᵢ [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨆ i, x i) = ⨆ i, f (x i) :=
  eq_of_forall_ge_iff <| f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, supᵢ_le_iff]
#align order_iso.map_supr OrderIso.map_supᵢ

theorem OrderIso.map_infᵢ [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨅ i, x i) = ⨅ i, f (x i) :=
  OrderIso.map_supᵢ f.dual _
#align order_iso.map_infi OrderIso.map_infᵢ

theorem OrderIso.map_supₛ [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (supₛ s) = ⨆ a ∈ s, f a :=
  by simp only [supₛ_eq_supᵢ, OrderIso.map_supᵢ]
#align order_iso.map_Sup OrderIso.map_supₛ

theorem OrderIso.map_infₛ [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (infₛ s) = ⨅ a ∈ s, f a :=
  OrderIso.map_supₛ f.dual _
#align order_iso.map_Inf OrderIso.map_infₛ

theorem supᵢ_comp_le {ι' : Sort _} (f : ι' → α) (g : ι → ι') : (⨆ x, f (g x)) ≤ ⨆ y, f y :=
  supᵢ_mono' fun _ => ⟨_, le_rfl⟩
#align supr_comp_le supᵢ_comp_le

theorem le_infᵢ_comp {ι' : Sort _} (f : ι' → α) (g : ι → ι') : (⨅ y, f y) ≤ ⨅ x, f (g x) :=
  infᵢ_mono' fun _ => ⟨_, le_rfl⟩
#align le_infi_comp le_infᵢ_comp

theorem Monotone.supᵢ_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, x ≤ s i) : (⨆ x, f (s x)) = ⨆ y, f y :=
  le_antisymm (supᵢ_comp_le _ _) (supᵢ_mono' fun x => (hs x).imp fun _ hi => hf hi)
#align monotone.supr_comp_eq Monotone.supᵢ_comp_eq

theorem Monotone.infᵢ_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, s i ≤ x) : (⨅ x, f (s x)) = ⨅ y, f y :=
  le_antisymm (infᵢ_mono' fun x => (hs x).imp fun _ hi => hf hi) (le_infᵢ_comp _ _)
#align monotone.infi_comp_eq Monotone.infᵢ_comp_eq

theorem Antitone.map_supᵢ_le [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    f (supᵢ s) ≤ ⨅ i, f (s i) :=
  le_infᵢ fun _ => hf <| le_supᵢ _ _
#align antitone.map_supr_le Antitone.map_supᵢ_le

theorem Monotone.map_infᵢ_le [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    f (infᵢ s) ≤ ⨅ i, f (s i) :=
  hf.dual_left.map_supᵢ_le
#align monotone.map_infi_le Monotone.map_infᵢ_le

theorem Antitone.map_supᵢ₂_le [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    f (⨆ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_infᵢ₂ _
#align antitone.map_supr₂_le Antitone.map_supᵢ₂_le

theorem Monotone.map_infᵢ₂_le [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    f (⨅ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_supᵢ₂ _
#align monotone.map_infi₂_le Monotone.map_infᵢ₂_le

theorem Antitone.map_supₛ_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    f (supₛ s) ≤ ⨅ a ∈ s, f a := by
  rw [supₛ_eq_supᵢ]
  exact hf.map_supᵢ₂_le _
#align antitone.map_Sup_le Antitone.map_supₛ_le

theorem Monotone.map_infₛ_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    f (infₛ s) ≤ ⨅ a ∈ s, f a :=
  hf.dual_left.map_supₛ_le
#align monotone.map_Inf_le Monotone.map_infₛ_le

theorem supᵢ_const_le : (⨆ _i : ι, a) ≤ a :=
  supᵢ_le fun _ => le_rfl
#align supr_const_le supᵢ_const_le

theorem le_infᵢ_const : a ≤ ⨅ _i : ι, a :=
  le_infᵢ fun _ => le_rfl
#align le_infi_const le_infᵢ_const

-- We generalize this to conditionally complete lattices in `csupᵢ_const` and `cinfᵢ_const`.
theorem supᵢ_const [Nonempty ι] : (⨆ _b : ι, a) = a := by rw [supᵢ, range_const, supₛ_singleton]
#align supr_const supᵢ_const

theorem infᵢ_const [Nonempty ι] : (⨅ _b : ι, a) = a :=
  @supᵢ_const αᵒᵈ _ _ a _
#align infi_const infᵢ_const

@[simp]
theorem supᵢ_bot : (⨆ _i : ι, ⊥ : α) = ⊥ :=
  bot_unique supᵢ_const_le
#align supr_bot supᵢ_bot

@[simp]
theorem infᵢ_top : (⨅ _i : ι, ⊤ : α) = ⊤ :=
  top_unique le_infᵢ_const
#align infi_top infᵢ_top

@[simp]
theorem supᵢ_eq_bot : supᵢ s = ⊥ ↔ ∀ i, s i = ⊥ :=
  supₛ_eq_bot.trans forall_range_iff
#align supr_eq_bot supᵢ_eq_bot

@[simp]
theorem infᵢ_eq_top : infᵢ s = ⊤ ↔ ∀ i, s i = ⊤ :=
  infₛ_eq_top.trans forall_range_iff
#align infi_eq_top infᵢ_eq_top

theorem supᵢ₂_eq_bot {f : ∀ i, κ i → α} : (⨆ (i) (j), f i j) = ⊥ ↔ ∀ i j, f i j = ⊥ := by
  simp
#align supr₂_eq_bot supᵢ₂_eq_bot

theorem infᵢ₂_eq_top {f : ∀ i, κ i → α} : (⨅ (i) (j), f i j) = ⊤ ↔ ∀ i j, f i j = ⊤ := by
  simp
#align infi₂_eq_top infᵢ₂_eq_top

@[simp]
theorem supᵢ_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
  le_antisymm (supᵢ_le fun _ => le_rfl) (le_supᵢ _ _)
#align supr_pos supᵢ_pos

@[simp]
theorem infᵢ_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
  le_antisymm (infᵢ_le _ _) (le_infᵢ fun _ => le_rfl)
#align infi_pos infᵢ_pos

@[simp]
theorem supᵢ_neg {p : Prop} {f : p → α} (hp : ¬p) : (⨆ h : p, f h) = ⊥ :=
  le_antisymm (supᵢ_le fun h => (hp h).elim) bot_le
#align supr_neg supᵢ_neg

@[simp]
theorem infᵢ_neg {p : Prop} {f : p → α} (hp : ¬p) : (⨅ h : p, f h) = ⊤ :=
  le_antisymm le_top <| le_infᵢ fun h => (hp h).elim
#align infi_neg infᵢ_neg

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `csupᵢ_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem supᵢ_eq_of_forall_le_of_forall_lt_exists_gt {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : (⨆ i : ι, f i) = b :=
  supₛ_eq_of_forall_le_of_forall_lt_exists_gt (forall_range_iff.mpr h₁) fun w hw =>
    exists_range_iff.mpr <| h₂ w hw
#align supr_eq_of_forall_le_of_forall_lt_exists_gt supᵢ_eq_of_forall_le_of_forall_lt_exists_gt

/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `cinfᵢ_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem infᵢ_eq_of_forall_ge_of_forall_gt_exists_lt :
    (∀ i, b ≤ f i) → (∀ w, b < w → ∃ i, f i < w) → (⨅ i, f i) = b :=
  @supᵢ_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ _
#align infi_eq_of_forall_ge_of_forall_gt_exists_lt infᵢ_eq_of_forall_ge_of_forall_gt_exists_lt

theorem supᵢ_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    (⨆ h : p, a h) = if h : p then a h else ⊥ := by by_cases h : p <;> simp [h]
#align supr_eq_dif supᵢ_eq_dif

theorem supᵢ_eq_if {p : Prop} [Decidable p] (a : α) : (⨆ _h : p, a) = if p then a else ⊥ :=
  supᵢ_eq_dif fun _ => a
#align supr_eq_if supᵢ_eq_if

theorem infᵢ_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    (⨅ h : p, a h) = if h : p then a h else ⊤ :=
  @supᵢ_eq_dif αᵒᵈ _ _ _ _
#align infi_eq_dif infᵢ_eq_dif

theorem infᵢ_eq_if {p : Prop} [Decidable p] (a : α) : (⨅ _h : p, a) = if p then a else ⊤ :=
  infᵢ_eq_dif fun _ => a
#align infi_eq_if infᵢ_eq_if

theorem supᵢ_comm {f : ι → ι' → α} : (⨆ (i) (j), f i j) = ⨆ (j) (i), f i j :=
  le_antisymm (supᵢ_le fun i => supᵢ_mono fun j => le_supᵢ (fun i => f i j) i)
    (supᵢ_le fun _ => supᵢ_mono fun _ => le_supᵢ _ _)
#align supr_comm supᵢ_comm

theorem infᵢ_comm {f : ι → ι' → α} : (⨅ (i) (j), f i j) = ⨅ (j) (i), f i j :=
  @supᵢ_comm αᵒᵈ _ _ _ _
#align infi_comm infᵢ_comm

theorem supᵢ₂_comm {ι₁ ι₂ : Sort _} {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    (⨆ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂) = ⨆ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@supᵢ_comm _ (κ₁ _), @supᵢ_comm _ ι₁]
#align supr₂_comm supᵢ₂_comm

theorem infᵢ₂_comm {ι₁ ι₂ : Sort _} {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    (⨅ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂) = ⨅ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@infᵢ_comm _ (κ₁ _), @infᵢ_comm _ ι₁]
#align infi₂_comm infᵢ₂_comm

/- TODO: this is strange. In the proof below, we get exactly the desired
   among the equalities, but close does not get it.
begin
  apply @le_antisymm,
    simp, intros,
    begin [smt]
      ematch, ematch, ematch, trace_state, have := le_refl (f i_1 i),
      trace_state, close
    end
end
-/
@[simp]
theorem supᵢ_supᵢ_eq_left {b : β} {f : ∀ x : β, x = b → α} : (⨆ x, ⨆ h : x = b, f x h) = f b rfl :=
  (@le_supᵢ₂ _ _ _ _ f b rfl).antisymm'
    (supᵢ_le fun c =>
      supᵢ_le <| by
        rintro rfl
        rfl)
#align supr_supr_eq_left supᵢ_supᵢ_eq_left

@[simp]
theorem infᵢ_infᵢ_eq_left {b : β} {f : ∀ x : β, x = b → α} : (⨅ x, ⨅ h : x = b, f x h) = f b rfl :=
  @supᵢ_supᵢ_eq_left αᵒᵈ _ _ _ _
#align infi_infi_eq_left infᵢ_infᵢ_eq_left

@[simp]
theorem supᵢ_supᵢ_eq_right {b : β} {f : ∀ x : β, b = x → α} : (⨆ x, ⨆ h : b = x, f x h) = f b rfl :=
  (le_supᵢ₂ b rfl).antisymm'
    (supᵢ₂_le fun c => by
      rintro rfl
      rfl)
#align supr_supr_eq_right supᵢ_supᵢ_eq_right

@[simp]
theorem infᵢ_infᵢ_eq_right {b : β} {f : ∀ x : β, b = x → α} : (⨅ x, ⨅ h : b = x, f x h) = f b rfl :=
  @supᵢ_supᵢ_eq_right αᵒᵈ _ _ _ _
#align infi_infi_eq_right infᵢ_infᵢ_eq_right

-- attribute [ematch] le_refl Porting note: removed attribute

theorem supᵢ_subtype {p : ι → Prop} {f : Subtype p → α} : supᵢ f = ⨆ (i) (h : p i), f ⟨i, h⟩ :=
  le_antisymm (supᵢ_le fun ⟨i, h⟩ => @le_supᵢ₂ _ _ p _ (fun i h => f ⟨i, h⟩) i h)
    (supᵢ₂_le fun _ _ => le_supᵢ _ _)
#align supr_subtype supᵢ_subtype

theorem infᵢ_subtype : ∀ {p : ι → Prop} {f : Subtype p → α}, infᵢ f = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  @supᵢ_subtype αᵒᵈ _ _
#align infi_subtype infᵢ_subtype

theorem supᵢ_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    (⨆ (i) (h), f i h) = ⨆ x : Subtype p, f x x.property :=
  (@supᵢ_subtype _ _ _ p fun x => f x.val x.property).symm
#align supr_subtype' supᵢ_subtype'

theorem infᵢ_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    (⨅ (i) (h : p i), f i h) = ⨅ x : Subtype p, f x x.property :=
  (@infᵢ_subtype _ _ _ p fun x => f x.val x.property).symm
#align infi_subtype' infᵢ_subtype'

theorem supᵢ_subtype'' {ι} (s : Set ι) (f : ι → α) : (⨆ i : s, f i) = ⨆ (t : ι) (_H : t ∈ s), f t :=
  supᵢ_subtype
#align supr_subtype'' supᵢ_subtype''

theorem infᵢ_subtype'' {ι} (s : Set ι) (f : ι → α) : (⨅ i : s, f i) = ⨅ (t : ι) (_H : t ∈ s), f t :=
  infᵢ_subtype
#align infi_subtype'' infᵢ_subtype''

theorem bsupᵢ_const {ι : Sort _} {a : α} {s : Set ι} (hs : s.Nonempty) : (⨆ i ∈ s, a) = a := by
  haveI : Nonempty s := Set.nonempty_coe_sort.mpr hs
  rw [← supᵢ_subtype'', supᵢ_const]
#align bsupr_const bsupᵢ_const

theorem binfᵢ_const {ι : Sort _} {a : α} {s : Set ι} (hs : s.Nonempty) : (⨅ i ∈ s, a) = a :=
  @bsupᵢ_const αᵒᵈ _ ι _ s hs
#align binfi_const binfᵢ_const

theorem supᵢ_sup_eq : (⨆ x, f x ⊔ g x) = (⨆ x, f x) ⊔ ⨆ x, g x :=
  le_antisymm (supᵢ_le fun _ => sup_le_sup (le_supᵢ _ _) <| le_supᵢ _ _)
    (sup_le (supᵢ_mono fun _ => le_sup_left) <| supᵢ_mono fun _ => le_sup_right)
#align supr_sup_eq supᵢ_sup_eq

theorem infᵢ_inf_eq : (⨅ x, f x ⊓ g x) = (⨅ x, f x) ⊓ ⨅ x, g x :=
  @supᵢ_sup_eq αᵒᵈ _ _ _ _
#align infi_inf_eq infᵢ_inf_eq

/- TODO: here is another example where more flexible pattern matching
   might help.

begin
  apply @le_antisymm,
  safe, pose h := f a ⊓ g a, begin [smt] ematch, ematch  end
end
-/
theorem supᵢ_sup [Nonempty ι] {f : ι → α} {a : α} : (⨆ x, f x) ⊔ a = ⨆ x, f x ⊔ a := by
  rw [supᵢ_sup_eq, supᵢ_const]
#align supr_sup supᵢ_sup

theorem infᵢ_inf [Nonempty ι] {f : ι → α} {a : α} : (⨅ x, f x) ⊓ a = ⨅ x, f x ⊓ a := by
  rw [infᵢ_inf_eq, infᵢ_const]
#align infi_inf infᵢ_inf

theorem sup_supᵢ [Nonempty ι] {f : ι → α} {a : α} : (a ⊔ ⨆ x, f x) = ⨆ x, a ⊔ f x := by
  rw [supᵢ_sup_eq, supᵢ_const]
#align sup_supr sup_supᵢ

theorem inf_infᵢ [Nonempty ι] {f : ι → α} {a : α} : (a ⊓ ⨅ x, f x) = ⨅ x, a ⊓ f x := by
  rw [infᵢ_inf_eq, infᵢ_const]
#align inf_infi inf_infᵢ

theorem bsupᵢ_sup {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨆ (i) (h : p i), f i h) ⊔ a = ⨆ (i) (h : p i), f i h ⊔ a := by
  haveI : Nonempty { i // p i } :=
      let ⟨i, hi⟩ := h
      ⟨⟨i, hi⟩⟩ ;
    rw [supᵢ_subtype', supᵢ_subtype', supᵢ_sup]
#align bsupr_sup bsupᵢ_sup

theorem sup_bsupᵢ {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊔ ⨆ (i) (h : p i), f i h) = ⨆ (i) (h : p i), a ⊔ f i h := by
  simpa only [sup_comm] using @bsupᵢ_sup α _ _ p _ _ h
#align sup_bsupr sup_bsupᵢ

theorem binfᵢ_inf {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨅ (i) (h : p i), f i h) ⊓ a = ⨅ (i) (h : p i), f i h ⊓ a :=
  @bsupᵢ_sup αᵒᵈ ι _ p f _ h
#align binfi_inf binfᵢ_inf

theorem inf_binfᵢ {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊓ ⨅ (i) (h : p i), f i h) = ⨅ (i) (h : p i), a ⊓ f i h :=
  @sup_bsupᵢ αᵒᵈ ι _ p f _ h
#align inf_binfi inf_binfᵢ

/-! ### `supᵢ` and `infᵢ` under `Prop` -/


theorem supᵢ_false {s : False → α} : supᵢ s = ⊥ :=
  by simp
#align supr_false supᵢ_false

theorem infᵢ_false {s : False → α} : infᵢ s = ⊤ :=
  by simp
#align infi_false infᵢ_false

theorem supᵢ_true {s : True → α} : supᵢ s = s trivial :=
  supᵢ_pos trivial
#align supr_true supᵢ_true

theorem infᵢ_true {s : True → α} : infᵢ s = s trivial :=
  infᵢ_pos trivial
#align infi_true infᵢ_true

@[simp]
theorem supᵢ_exists {p : ι → Prop} {f : Exists p → α} : (⨆ x, f x) = ⨆ (i) (h), f ⟨i, h⟩ :=
  le_antisymm (supᵢ_le fun ⟨i, h⟩ => @le_supᵢ₂ _ _ _ _ (fun _ _ => _) i h)
    (supᵢ₂_le fun _ _ => le_supᵢ _ _)
#align supr_exists supᵢ_exists

@[simp]
theorem infᵢ_exists {p : ι → Prop} {f : Exists p → α} : (⨅ x, f x) = ⨅ (i) (h), f ⟨i, h⟩ :=
  @supᵢ_exists αᵒᵈ _ _ _ _
#align infi_exists infᵢ_exists

theorem supᵢ_and {p q : Prop} {s : p ∧ q → α} : supᵢ s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  le_antisymm (supᵢ_le fun ⟨i, h⟩ => @le_supᵢ₂ _ _ _ _ (fun _ _ => _) i h)
    (supᵢ₂_le fun _ _ => le_supᵢ _ _)
#align supr_and supᵢ_and

theorem infᵢ_and {p q : Prop} {s : p ∧ q → α} : infᵢ s = ⨅ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  @supᵢ_and αᵒᵈ _ _ _ _
#align infi_and infᵢ_and

/-- The symmetric case of `supᵢ_and`, useful for rewriting into a supremum over a conjunction -/
theorem supᵢ_and' {p q : Prop} {s : p → q → α} :
    (⨆ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨆ h : p ∧ q, s h.1 h.2 :=
  Eq.symm supᵢ_and
#align supr_and' supᵢ_and'

/-- The symmetric case of `infᵢ_and`, useful for rewriting into a infimum over a conjunction -/
theorem infᵢ_and' {p q : Prop} {s : p → q → α} :
    (⨅ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨅ h : p ∧ q, s h.1 h.2 :=
  Eq.symm infᵢ_and
#align infi_and' infᵢ_and'

theorem supᵢ_or {p q : Prop} {s : p ∨ q → α} :
    (⨆ x, s x) = (⨆ i, s (Or.inl i)) ⊔ ⨆ j, s (Or.inr j) :=
  le_antisymm
    (supᵢ_le fun i =>
      match i with
      | Or.inl _ => le_sup_of_le_left <| le_supᵢ (fun _ => s _) _
      | Or.inr _ => le_sup_of_le_right <| le_supᵢ (fun _ => s _) _)
    (sup_le (supᵢ_comp_le _ _) (supᵢ_comp_le _ _))
#align supr_or supᵢ_or

theorem infᵢ_or {p q : Prop} {s : p ∨ q → α} :
    (⨅ x, s x) = (⨅ i, s (Or.inl i)) ⊓ ⨅ j, s (Or.inr j) :=
  @supᵢ_or αᵒᵈ _ _ _ _
#align infi_or infᵢ_or

section

variable (p : ι → Prop) [DecidablePred p]

theorem supᵢ_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    (⨆ i, if h : p i then f i h else g i h) = (⨆ (i) (h : p i), f i h) ⊔ ⨆ (i) (h : ¬p i),
    g i h := by
  rw [← supᵢ_sup_eq]
  congr 1 with i
  split_ifs with h <;> simp [h]
#align supr_dite supᵢ_dite

theorem infᵢ_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    (⨅ i, if h : p i then f i h else g i h) = (⨅ (i) (h : p i), f i h) ⊓ ⨅ (i) (h : ¬p i), g i h :=
  supᵢ_dite p (show ∀ i, p i → αᵒᵈ from f) g
#align infi_dite infᵢ_dite

theorem supᵢ_ite (f g : ι → α) :
    (⨆ i, if p i then f i else g i) = (⨆ (i) (_h : p i), f i) ⊔ ⨆ (i) (_h : ¬p i), g i :=
  supᵢ_dite _ _ _
#align supr_ite supᵢ_ite

theorem infᵢ_ite (f g : ι → α) :
    (⨅ i, if p i then f i else g i) = (⨅ (i) (_h : p i), f i) ⊓ ⨅ (i) (_h : ¬p i), g i :=
  infᵢ_dite _ _ _
#align infi_ite infᵢ_ite

end

theorem supᵢ_range {g : β → α} {f : ι → β} : (⨆ b ∈ range f, g b) = ⨆ i, g (f i) := by
  rw [← supᵢ_subtype'', supᵢ_range']
#align supr_range supᵢ_range

theorem infᵢ_range : ∀ {g : β → α} {f : ι → β}, (⨅ b ∈ range f, g b) = ⨅ i, g (f i) :=
  @supᵢ_range αᵒᵈ _ _ _
#align infi_range infᵢ_range

theorem supₛ_image {s : Set β} {f : β → α} : supₛ (f '' s) = ⨆ a ∈ s, f a := by
  rw [← supᵢ_subtype'', supₛ_image']
#align Sup_image supₛ_image

theorem infₛ_image {s : Set β} {f : β → α} : infₛ (f '' s) = ⨅ a ∈ s, f a :=
  @supₛ_image αᵒᵈ _ _ _ _
#align Inf_image infₛ_image

/-
### supᵢ and infᵢ under set constructions
-/
theorem supᵢ_emptyset {f : β → α} : (⨆ x ∈ (∅ : Set β), f x) = ⊥ := by simp
#align supr_emptyset supᵢ_emptyset

theorem infᵢ_emptyset {f : β → α} : (⨅ x ∈ (∅ : Set β), f x) = ⊤ := by simp
#align infi_emptyset infᵢ_emptyset

theorem supᵢ_univ {f : β → α} : (⨆ x ∈ (univ : Set β), f x) = ⨆ x, f x := by simp
#align supr_univ supᵢ_univ

theorem infᵢ_univ {f : β → α} : (⨅ x ∈ (univ : Set β), f x) = ⨅ x, f x := by simp
#align infi_univ infᵢ_univ

theorem supᵢ_union {f : β → α} {s t : Set β} : (⨆ x ∈ s ∪ t, f x) = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x :=
  by simp_rw [mem_union, supᵢ_or, supᵢ_sup_eq]
#align supr_union supᵢ_union

theorem infᵢ_union {f : β → α} {s t : Set β} : (⨅ x ∈ s ∪ t, f x) = (⨅ x ∈ s, f x) ⊓ ⨅ x ∈ t, f x :=
  @supᵢ_union αᵒᵈ _ _ _ _ _
#align infi_union infᵢ_union

theorem supᵢ_split (f : β → α) (p : β → Prop) :
    (⨆ i, f i) = (⨆ (i) (_h : p i), f i) ⊔ ⨆ (i) (_h : ¬p i), f i := by
  simpa [Classical.em] using @supᵢ_union _ _ _ f { i | p i } { i | ¬p i }
#align supr_split supᵢ_split

theorem infᵢ_split :
    ∀ (f : β → α) (p : β → Prop), (⨅ i, f i) = (⨅ (i) (_h : p i), f i) ⊓ ⨅ (i) (_h : ¬p i), f i :=
  @supᵢ_split αᵒᵈ _ _
#align infi_split infᵢ_split

theorem supᵢ_split_single (f : β → α) (i₀ : β) : (⨆ i, f i) = f i₀ ⊔ ⨆ (i) (_h : i ≠ i₀), f i := by
  convert supᵢ_split f (fun i => i = i₀)
  simp
#align supr_split_single supᵢ_split_single

theorem infᵢ_split_single (f : β → α) (i₀ : β) : (⨅ i, f i) = f i₀ ⊓ ⨅ (i) (_h : i ≠ i₀), f i :=
  @supᵢ_split_single αᵒᵈ _ _ _ _
#align infi_split_single infᵢ_split_single

theorem supᵢ_le_supᵢ_of_subset {f : β → α} {s t : Set β} : s ⊆ t → (⨆ x ∈ s, f x) ≤ ⨆ x ∈ t, f x :=
  bsupᵢ_mono
#align supr_le_supr_of_subset supᵢ_le_supᵢ_of_subset

theorem infᵢ_le_infᵢ_of_subset {f : β → α} {s t : Set β} : s ⊆ t → (⨅ x ∈ t, f x) ≤ ⨅ x ∈ s, f x :=
  binfᵢ_mono
#align infi_le_infi_of_subset infᵢ_le_infᵢ_of_subset

theorem supᵢ_insert {f : β → α} {s : Set β} {b : β} :
    (⨆ x ∈ insert b s, f x) = f b ⊔ ⨆ x ∈ s, f x :=
  Eq.trans supᵢ_union <| congr_arg (fun x => x ⊔ ⨆ x ∈ s, f x) supᵢ_supᵢ_eq_left
#align supr_insert supᵢ_insert

theorem infᵢ_insert {f : β → α} {s : Set β} {b : β} :
    (⨅ x ∈ insert b s, f x) = f b ⊓ ⨅ x ∈ s, f x :=
  Eq.trans infᵢ_union <| congr_arg (fun x => x ⊓ ⨅ x ∈ s, f x) infᵢ_infᵢ_eq_left
#align infi_insert infᵢ_insert

theorem supᵢ_singleton {f : β → α} {b : β} : (⨆ x ∈ (singleton b : Set β), f x) = f b := by simp
#align supr_singleton supᵢ_singleton

theorem infᵢ_singleton {f : β → α} {b : β} : (⨅ x ∈ (singleton b : Set β), f x) = f b := by simp
#align infi_singleton infᵢ_singleton

theorem supᵢ_pair {f : β → α} {a b : β} : (⨆ x ∈ ({a, b} : Set β), f x) = f a ⊔ f b := by
  rw [supᵢ_insert, supᵢ_singleton]
#align supr_pair supᵢ_pair

theorem infᵢ_pair {f : β → α} {a b : β} : (⨅ x ∈ ({a, b} : Set β), f x) = f a ⊓ f b := by
  rw [infᵢ_insert, infᵢ_singleton]
#align infi_pair infᵢ_pair

theorem supᵢ_image {γ} {f : β → γ} {g : γ → α} {t : Set β} :
    (⨆ c ∈ f '' t, g c) = ⨆ b ∈ t, g (f b) := by rw [← supₛ_image, ← supₛ_image, ← image_comp] ; rfl
#align supr_image supᵢ_image

theorem infᵢ_image :
    ∀ {γ} {f : β → γ} {g : γ → α} {t : Set β}, (⨅ c ∈ f '' t, g c) = ⨅ b ∈ t, g (f b) :=
  @supᵢ_image αᵒᵈ _ _
#align infi_image infᵢ_image

theorem supᵢ_extend_bot {e : ι → β} (he : Injective e) (f : ι → α) :
    (⨆ j, extend e f ⊥ j) = ⨆ i, f i := by
  rw [supᵢ_split _ fun j => ∃ i, e i = j]
  simp (config := { contextual := true }) [he.extend_apply, extend_apply', @supᵢ_comm _ β ι]
#align supr_extend_bot supᵢ_extend_bot

theorem infᵢ_extend_top {e : ι → β} (he : Injective e) (f : ι → α) :
    (⨅ j, extend e f ⊤ j) = infᵢ f :=
  @supᵢ_extend_bot αᵒᵈ _ _ _ _ he _
#align infi_extend_top infᵢ_extend_top

/-!
### `supᵢ` and `infᵢ` under `Type`
-/


theorem supᵢ_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι → α) : supᵢ f = supₛ (∅ : Set α) :=
  congr_arg supₛ (range_eq_empty f)
#align supr_of_empty' supᵢ_of_empty'

theorem infᵢ_of_empty' {α ι} [InfSet α] [IsEmpty ι] (f : ι → α) : infᵢ f = infₛ (∅ : Set α) :=
  congr_arg infₛ (range_eq_empty f)
#align infi_of_empty' infᵢ_of_empty'

theorem supᵢ_of_empty [IsEmpty ι] (f : ι → α) : supᵢ f = ⊥ :=
  (supᵢ_of_empty' f).trans supₛ_empty
#align supr_of_empty supᵢ_of_empty

theorem infᵢ_of_empty [IsEmpty ι] (f : ι → α) : infᵢ f = ⊤ :=
  @supᵢ_of_empty αᵒᵈ _ _ _ f
#align infi_of_empty infᵢ_of_empty

theorem supᵢ_bool_eq {f : Bool → α} : (⨆ b : Bool, f b) = f true ⊔ f false := by
  rw [supᵢ, Bool.range_eq, supₛ_pair, sup_comm]
#align supr_bool_eq supᵢ_bool_eq

theorem infᵢ_bool_eq {f : Bool → α} : (⨅ b : Bool, f b) = f true ⊓ f false :=
  @supᵢ_bool_eq αᵒᵈ _ _
#align infi_bool_eq infᵢ_bool_eq

theorem sup_eq_supᵢ (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y := by
  rw [supᵢ_bool_eq, Bool.cond_true, Bool.cond_false]
#align sup_eq_supr sup_eq_supᵢ

theorem inf_eq_infᵢ (x y : α) : x ⊓ y = ⨅ b : Bool, cond b x y :=
  @sup_eq_supᵢ αᵒᵈ _ _ _
#align inf_eq_infi inf_eq_infᵢ

theorem isGLB_binfᵢ {s : Set β} {f : β → α} : IsGLB (f '' s) (⨅ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, infᵢ_subtype'] using
    @isGLB_infᵢ α s _ (f ∘ fun x => (x : β))
#align is_glb_binfi isGLB_binfᵢ

theorem isLUB_bsupᵢ {s : Set β} {f : β → α} : IsLUB (f '' s) (⨆ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, supᵢ_subtype'] using
    @isLUB_supᵢ α s _ (f ∘ fun x => (x : β))
#align is_lub_bsupr isLUB_bsupᵢ

theorem supᵢ_sigma {p : β → Type _} {f : Sigma p → α} : (⨆ x, f x) = ⨆ (i) (j), f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun c => by simp only [supᵢ_le_iff, Sigma.forall]
#align supr_sigma supᵢ_sigma

theorem infᵢ_sigma {p : β → Type _} {f : Sigma p → α} : (⨅ x, f x) = ⨅ (i) (j), f ⟨i, j⟩ :=
  @supᵢ_sigma αᵒᵈ _ _ _ _
#align infi_sigma infᵢ_sigma

theorem supᵢ_prod {f : β × γ → α} : (⨆ x, f x) = ⨆ (i) (j), f (i, j) :=
  eq_of_forall_ge_iff fun c => by simp only [supᵢ_le_iff, Prod.forall]
#align supr_prod supᵢ_prod

theorem infᵢ_prod {f : β × γ → α} : (⨅ x, f x) = ⨅ (i) (j), f (i, j) :=
  @supᵢ_prod αᵒᵈ _ _ _ _
#align infi_prod infᵢ_prod

theorem bsupᵢ_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    (⨆ x ∈ s ×ˢ t, f x) = ⨆ (a ∈ s) (b ∈ t), f (a, b) := by
  simp_rw [supᵢ_prod, mem_prod, supᵢ_and]
  exact supᵢ_congr fun _ => supᵢ_comm
#align bsupr_prod bsupᵢ_prod

theorem binfᵢ_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    (⨅ x ∈ s ×ˢ t, f x) = ⨅ (a ∈ s) (b ∈ t), f (a, b) :=
  @bsupᵢ_prod αᵒᵈ _ _ _ _ _ _
#align binfi_prod binfᵢ_prod

theorem supᵢ_sum {f : Sum β γ → α} : (⨆ x, f x) = (⨆ i, f (Sum.inl i)) ⊔ ⨆ j, f (Sum.inr j) :=
  eq_of_forall_ge_iff fun c => by simp only [sup_le_iff, supᵢ_le_iff, Sum.forall]
#align supr_sum supᵢ_sum

theorem infᵢ_sum {f : Sum β γ → α} : (⨅ x, f x) = (⨅ i, f (Sum.inl i)) ⊓ ⨅ j, f (Sum.inr j) :=
  @supᵢ_sum αᵒᵈ _ _ _ _
#align infi_sum infᵢ_sum

theorem supᵢ_option (f : Option β → α) : (⨆ o, f o) = f none ⊔ ⨆ b, f (Option.some b) :=
  eq_of_forall_ge_iff fun c => by simp only [supᵢ_le_iff, sup_le_iff, Option.forall]
#align supr_option supᵢ_option

theorem infᵢ_option (f : Option β → α) : (⨅ o, f o) = f none ⊓ ⨅ b, f (Option.some b) :=
  @supᵢ_option αᵒᵈ _ _ _
#align infi_option infᵢ_option

/-- A version of `supᵢ_option` useful for rewriting right-to-left. -/
theorem supᵢ_option_elim (a : α) (f : β → α) : (⨆ o : Option β, o.elim a f) = a ⊔ ⨆ b, f b := by
  simp [supᵢ_option]
#align supr_option_elim supᵢ_option_elim

/-- A version of `infᵢ_option` useful for rewriting right-to-left. -/
theorem infᵢ_option_elim (a : α) (f : β → α) : (⨅ o : Option β, o.elim a f) = a ⊓ ⨅ b, f b :=
  @supᵢ_option_elim αᵒᵈ _ _ _ _
#align infi_option_elim infᵢ_option_elim

/-- When taking the supremum of `f : ι → α`, the elements of `ι` on which `f` gives `⊥` can be
dropped, without changing the result. -/
theorem supᵢ_ne_bot_subtype (f : ι → α) : (⨆ i : { i // f i ≠ ⊥ }, f i) = ⨆ i, f i := by
  by_cases htriv : ∀ i, f i = ⊥
  · simp only [supᵢ_bot, (funext htriv : f = _)]
  refine' (supᵢ_comp_le f _).antisymm (supᵢ_mono' fun i => _)
  by_cases hi : f i = ⊥
  · rw [hi]
    obtain ⟨i₀, hi₀⟩ := not_forall.mp htriv
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩
  · exact ⟨⟨i, hi⟩, rfl.le⟩
#align supr_ne_bot_subtype supᵢ_ne_bot_subtype

/-- When taking the infimum of `f : ι → α`, the elements of `ι` on which `f` gives `⊤` can be
dropped, without changing the result. -/
theorem infᵢ_ne_top_subtype (f : ι → α) : (⨅ i : { i // f i ≠ ⊤ }, f i) = ⨅ i, f i :=
  @supᵢ_ne_bot_subtype αᵒᵈ ι _ f
#align infi_ne_top_subtype infᵢ_ne_top_subtype

theorem supₛ_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    supₛ (image2 f s t) = ⨆ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, supₛ_image, bsupᵢ_prod]
#align Sup_image2 supₛ_image2

theorem infₛ_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    infₛ (image2 f s t) = ⨅ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, infₛ_image, binfᵢ_prod]
#align Inf_image2 infₛ_image2

/-!
### `supᵢ` and `infᵢ` under `ℕ`
-/


theorem supᵢ_ge_eq_supᵢ_nat_add (u : ℕ → α) (n : ℕ) : (⨆ i ≥ n, u i) = ⨆ i, u (i + n) := by
  apply le_antisymm <;> simp only [supᵢ_le_iff]
  · refine fun i hi => le_supₛ ⟨i - n, ?_⟩
    dsimp only
    rw [Nat.sub_add_cancel hi]
  · exact fun i => le_supₛ ⟨i + n, supᵢ_pos (Nat.le_add_left _ _)⟩
#align supr_ge_eq_supr_nat_add supᵢ_ge_eq_supᵢ_nat_add

theorem infᵢ_ge_eq_infᵢ_nat_add (u : ℕ → α) (n : ℕ) : (⨅ i ≥ n, u i) = ⨅ i, u (i + n) :=
  @supᵢ_ge_eq_supᵢ_nat_add αᵒᵈ _ _ _
#align infi_ge_eq_infi_nat_add infᵢ_ge_eq_infᵢ_nat_add

theorem Monotone.supᵢ_nat_add {f : ℕ → α} (hf : Monotone f) (k : ℕ) : (⨆ n, f (n + k)) = ⨆ n, f n :=
  le_antisymm (supᵢ_le fun i => le_supᵢ _ (i + k)) <| supᵢ_mono fun i => hf <| Nat.le_add_right i k
#align monotone.supr_nat_add Monotone.supᵢ_nat_add

theorem Antitone.infᵢ_nat_add {f : ℕ → α} (hf : Antitone f) (k : ℕ) : (⨅ n, f (n + k)) = ⨅ n, f n :=
  hf.dual_right.supᵢ_nat_add k
#align antitone.infi_nat_add Antitone.infᵢ_nat_add

-- Porting note: the linter doesn't like this being marked as `@[simp]`,
-- saying that it doesn't work when called on its LHS.
-- Mysteriously, it *does* work. Nevertheless, per
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/complete_lattice.20and.20has_sup/near/316497982
-- "the subterm ?f (i + ?k) produces an ugly higher-order unification problem."
-- @[simp]
theorem supᵢ_infᵢ_ge_nat_add (f : ℕ → α) (k : ℕ) :
    (⨆ n, ⨅ i ≥ n, f (i + k)) = ⨆ n, ⨅ i ≥ n, f i := by
  have hf : Monotone fun n => ⨅ i ≥ n, f i := fun n m h => binfᵢ_mono fun i => h.trans
  rw [← Monotone.supᵢ_nat_add hf k]
  · simp_rw [infᵢ_ge_eq_infᵢ_nat_add, ← Nat.add_assoc]
#align supr_infi_ge_nat_add supᵢ_infᵢ_ge_nat_add

-- Porting note: removing `@[simp]`, see discussion on `supᵢ_infᵢ_ge_nat_add`.
-- @[simp]
theorem infᵢ_supᵢ_ge_nat_add :
    ∀ (f : ℕ → α) (k : ℕ), (⨅ n, ⨆ i ≥ n, f (i + k)) = ⨅ n, ⨆ i ≥ n, f i :=
  @supᵢ_infᵢ_ge_nat_add αᵒᵈ _
#align infi_supr_ge_nat_add infᵢ_supᵢ_ge_nat_add

theorem sup_supᵢ_nat_succ (u : ℕ → α) : (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ i, u i :=
  calc
    (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ x ∈ {0} ∪ range Nat.succ, u x := by
      { rw [supᵢ_union, supᵢ_singleton, supᵢ_range] }
    _ = ⨆ i, u i := by rw [Nat.zero_union_range_succ, supᵢ_univ]
#align sup_supr_nat_succ sup_supᵢ_nat_succ

theorem inf_infᵢ_nat_succ (u : ℕ → α) : (u 0 ⊓ ⨅ i, u (i + 1)) = ⨅ i, u i :=
  @sup_supᵢ_nat_succ αᵒᵈ _ u
#align inf_infi_nat_succ inf_infᵢ_nat_succ

theorem infᵢ_nat_gt_zero_eq (f : ℕ → α) : (⨅ i > 0, f i) = ⨅ i, f (i + 1) := by
  rw [← infᵢ_range, Nat.range_succ]
  simp
#align infi_nat_gt_zero_eq infᵢ_nat_gt_zero_eq

theorem supᵢ_nat_gt_zero_eq (f : ℕ → α) : (⨆ i > 0, f i) = ⨆ i, f (i + 1) :=
  @infᵢ_nat_gt_zero_eq αᵒᵈ _ f
#align supr_nat_gt_zero_eq supᵢ_nat_gt_zero_eq

end

section CompleteLinearOrder

variable [CompleteLinearOrder α]

theorem supᵢ_eq_top (f : ι → α) : supᵢ f = ⊤ ↔ ∀ b < ⊤, ∃ i, b < f i := by
  simp only [← supₛ_range, supₛ_eq_top, Set.exists_range_iff]
#align supr_eq_top supᵢ_eq_top

theorem infᵢ_eq_bot (f : ι → α) : infᵢ f = ⊥ ↔ ∀ b > ⊥, ∃ i, f i < b := by
  simp only [← infₛ_range, infₛ_eq_bot, Set.exists_range_iff]
#align infi_eq_bot infᵢ_eq_bot

end CompleteLinearOrder

/-!
### Instances
-/


instance Prop.completeLattice : CompleteLattice Prop :=
  { Prop.boundedOrder, Prop.distribLattice with
    supₛ := fun s => ∃ a ∈ s, a
    le_supₛ := fun _ a h p => ⟨a, h, p⟩
    supₛ_le := fun _ _ h ⟨b, h', p⟩ => h b h' p
    infₛ := fun s => ∀ a, a ∈ s → a
    infₛ_le := fun _ a h p => p a h
    le_infₛ := fun _ _ h p b hb => h b hb p }
#align Prop.complete_lattice Prop.completeLattice

noncomputable instance Prop.completeLinearOrder : CompleteLinearOrder Prop :=
  { Prop.completeLattice, Prop.linearOrder with }
#align Prop.complete_linear_order Prop.completeLinearOrder

@[simp]
theorem supₛ_Prop_eq {s : Set Prop} : supₛ s = ∃ p ∈ s, p :=
  rfl
#align Sup_Prop_eq supₛ_Prop_eq

@[simp]
theorem infₛ_Prop_eq {s : Set Prop} : infₛ s = ∀ p ∈ s, p :=
  rfl
#align Inf_Prop_eq infₛ_Prop_eq

@[simp]
theorem supᵢ_Prop_eq {p : ι → Prop} : (⨆ i, p i) = ∃ i, p i :=
  le_antisymm (fun ⟨_, ⟨i, (eq : p i = _)⟩, hq⟩ => ⟨i, eq.symm ▸ hq⟩) fun ⟨i, hi⟩ =>
    ⟨p i, ⟨i, rfl⟩, hi⟩
#align supr_Prop_eq supᵢ_Prop_eq

@[simp]
theorem infᵢ_Prop_eq {p : ι → Prop} : (⨅ i, p i) = ∀ i, p i :=
  le_antisymm (fun h i => h _ ⟨i, rfl⟩) fun h _ ⟨i, Eq⟩ => Eq ▸ h i
#align infi_Prop_eq infᵢ_Prop_eq

instance Pi.supSet {α : Type _} {β : α → Type _} [∀ i, SupSet (β i)] : SupSet (∀ i, β i) :=
  ⟨fun s i => ⨆ f : s, (f : ∀ i, β i) i⟩
#align pi.has_Sup Pi.supSet

instance Pi.infSet {α : Type _} {β : α → Type _} [∀ i, InfSet (β i)] : InfSet (∀ i, β i) :=
  ⟨fun s i => ⨅ f : s, (f : ∀ i, β i) i⟩
#align pi.has_Inf Pi.infSet

instance Pi.completeLattice {α : Type _} {β : α → Type _} [∀ i, CompleteLattice (β i)] :
    CompleteLattice (∀ i, β i) :=
  { Pi.boundedOrder, Pi.lattice with
    le_supₛ := fun s f hf i => le_supᵢ (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩
    infₛ_le := fun s f hf i => infᵢ_le (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩
    supₛ_le := fun _ _ hf i => supᵢ_le fun g => hf g g.2 i
    le_infₛ := fun _ _ hf i => le_infᵢ fun g => hf g g.2 i }
#align pi.complete_lattice Pi.completeLattice

theorem supₛ_apply {α : Type _} {β : α → Type _} [∀ i, SupSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    (supₛ s) a = ⨆ f : s, (f : ∀ a, β a) a :=
  rfl
#align Sup_apply supₛ_apply

theorem infₛ_apply {α : Type _} {β : α → Type _} [∀ i, InfSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    infₛ s a = ⨅ f : s, (f : ∀ a, β a) a :=
  rfl
#align Inf_apply infₛ_apply

@[simp]
theorem supᵢ_apply {α : Type _} {β : α → Type _} {ι : Sort _} [∀ i, SupSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨆ i, f i) a = ⨆ i, f i a := by
  rw [supᵢ, supₛ_apply, supᵢ, supᵢ, ← image_eq_range (fun f : ∀ i, β i => f a) (range f), ←
    range_comp] ; rfl
#align supr_apply supᵢ_apply

@[simp]
theorem infᵢ_apply {α : Type _} {β : α → Type _} {ι : Sort _} [∀ i, InfSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨅ i, f i) a = ⨅ i, f i a :=
  @supᵢ_apply α (fun i => (β i)ᵒᵈ) _ _ _ _
#align infi_apply infᵢ_apply

theorem unary_relation_supₛ_iff {α : Type _} (s : Set (α → Prop)) {a : α} :
    supₛ s a ↔ ∃ r : α → Prop, r ∈ s ∧ r a := by
  rw [supₛ_apply]
  simp [← eq_iff_iff]
#align unary_relation_Sup_iff unary_relation_supₛ_iff

theorem unary_relation_infₛ_iff {α : Type _} (s : Set (α → Prop)) {a : α} :
    infₛ s a ↔ ∀ r : α → Prop, r ∈ s → r a := by
  rw [infₛ_apply]
  simp [← eq_iff_iff]
#align unary_relation_Inf_iff unary_relation_infₛ_iff

theorem binary_relation_supₛ_iff {α β : Type _} (s : Set (α → β → Prop)) {a : α} {b : β} :
    supₛ s a b ↔ ∃ r : α → β → Prop, r ∈ s ∧ r a b := by
  rw [supₛ_apply]
  simp [← eq_iff_iff]
#align binary_relation_Sup_iff binary_relation_supₛ_iff

theorem binary_relation_infₛ_iff {α β : Type _} (s : Set (α → β → Prop)) {a : α} {b : β} :
    infₛ s a b ↔ ∀ r : α → β → Prop, r ∈ s → r a b := by
  rw [infₛ_apply]
  simp [← eq_iff_iff]
#align binary_relation_Inf_iff binary_relation_infₛ_iff

section CompleteLattice

variable [Preorder α] [CompleteLattice β]

theorem monotone_supₛ_of_monotone {s : Set (α → β)} (m_s : ∀ f ∈ s, Monotone f) :
    Monotone (supₛ s) := fun _ _ h => supᵢ_mono fun f => m_s f f.2 h
#align monotone_Sup_of_monotone monotone_supₛ_of_monotone

theorem monotone_infₛ_of_monotone {s : Set (α → β)} (m_s : ∀ f ∈ s, Monotone f) :
    Monotone (infₛ s) := fun _ _ h => infᵢ_mono fun f => m_s f f.2 h
#align monotone_Inf_of_monotone monotone_infₛ_of_monotone

end CompleteLattice

namespace Prod

variable (α β)

instance supSet [SupSet α] [SupSet β] : SupSet (α × β) :=
  ⟨fun s => (supₛ (Prod.fst '' s), supₛ (Prod.snd '' s))⟩

instance infSet [InfSet α] [InfSet β] : InfSet (α × β) :=
  ⟨fun s => (infₛ (Prod.fst '' s), infₛ (Prod.snd '' s))⟩

variable {α β}

theorem fst_infₛ [InfSet α] [InfSet β] (s : Set (α × β)) : (infₛ s).fst = infₛ (Prod.fst '' s) :=
  rfl
#align prod.fst_Inf Prod.fst_infₛ

theorem snd_infₛ [InfSet α] [InfSet β] (s : Set (α × β)) : (infₛ s).snd = infₛ (Prod.snd '' s) :=
  rfl
#align prod.snd_Inf Prod.snd_infₛ

theorem swap_infₛ [InfSet α] [InfSet β] (s : Set (α × β)) : (infₛ s).swap = infₛ (Prod.swap '' s) :=
  ext (congr_arg infₛ <| image_comp Prod.fst swap s : _)
    (congr_arg infₛ <| image_comp Prod.snd swap s : _)
#align prod.swap_Inf Prod.swap_infₛ

theorem fst_supₛ [SupSet α] [SupSet β] (s : Set (α × β)) : (supₛ s).fst = supₛ (Prod.fst '' s) :=
  rfl
#align prod.fst_Sup Prod.fst_supₛ

theorem snd_supₛ [SupSet α] [SupSet β] (s : Set (α × β)) : (supₛ s).snd = supₛ (Prod.snd '' s) :=
  rfl
#align prod.snd_Sup Prod.snd_supₛ

theorem swap_supₛ [SupSet α] [SupSet β] (s : Set (α × β)) : (supₛ s).swap = supₛ (Prod.swap '' s) :=
  ext (congr_arg supₛ <| image_comp Prod.fst swap s : _)
    (congr_arg supₛ <| image_comp Prod.snd swap s : _)
#align prod.swap_Sup Prod.swap_supₛ

theorem fst_infᵢ [InfSet α] [InfSet β] (f : ι → α × β) : (infᵢ f).fst = ⨅ i, (f i).fst :=
  congr_arg infₛ (range_comp _ _).symm
#align prod.fst_infi Prod.fst_infᵢ

theorem snd_infᵢ [InfSet α] [InfSet β] (f : ι → α × β) : (infᵢ f).snd = ⨅ i, (f i).snd :=
  congr_arg infₛ (range_comp _ _).symm
#align prod.snd_infi Prod.snd_infᵢ

theorem swap_infᵢ [InfSet α] [InfSet β] (f : ι → α × β) : (infᵢ f).swap = ⨅ i, (f i).swap := by
  simp_rw [infᵢ, swap_infₛ, ←range_comp, Function.comp]  -- Porting note: need to unfold `∘`
#align prod.swap_infi Prod.swap_infᵢ

theorem infᵢ_mk [InfSet α] [InfSet β] (f : ι → α) (g : ι → β) :
    (⨅ i, (f i, g i)) = (⨅ i, f i, ⨅ i, g i) :=
  congr_arg₂ Prod.mk (fst_infᵢ _) (snd_infᵢ _)
#align prod.infi_mk Prod.infᵢ_mk

theorem fst_supᵢ [SupSet α] [SupSet β] (f : ι → α × β) : (supᵢ f).fst = ⨆ i, (f i).fst :=
  congr_arg supₛ (range_comp _ _).symm
#align prod.fst_supr Prod.fst_supᵢ

theorem snd_supᵢ [SupSet α] [SupSet β] (f : ι → α × β) : (supᵢ f).snd = ⨆ i, (f i).snd :=
  congr_arg supₛ (range_comp _ _).symm
#align prod.snd_supr Prod.snd_supᵢ

theorem swap_supᵢ [SupSet α] [SupSet β] (f : ι → α × β) : (supᵢ f).swap = ⨆ i, (f i).swap := by
  simp_rw [supᵢ, swap_supₛ, ←range_comp, Function.comp]  -- Porting note: need to unfold `∘`
#align prod.swap_supr Prod.swap_supᵢ

theorem supᵢ_mk [SupSet α] [SupSet β] (f : ι → α) (g : ι → β) :
    (⨆ i, (f i, g i)) = (⨆ i, f i, ⨆ i, g i) :=
  congr_arg₂ Prod.mk (fst_supᵢ _) (snd_supᵢ _)
#align prod.supr_mk Prod.supᵢ_mk

variable (α β)

instance completeLattice [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) :=
  { Prod.lattice α β, Prod.boundedOrder α β, Prod.supSet α β, Prod.infSet α β with
    le_supₛ := fun _ _ hab => ⟨le_supₛ <| mem_image_of_mem _ hab, le_supₛ <| mem_image_of_mem _ hab⟩
    supₛ_le := fun _ _ h =>
      ⟨supₛ_le <| ball_image_of_ball fun p hp => (h p hp).1,
        supₛ_le <| ball_image_of_ball fun p hp => (h p hp).2⟩
    infₛ_le := fun _ _ hab => ⟨infₛ_le <| mem_image_of_mem _ hab, infₛ_le <| mem_image_of_mem _ hab⟩
    le_infₛ := fun _ _ h =>
      ⟨le_infₛ <| ball_image_of_ball fun p hp => (h p hp).1,
        le_infₛ <| ball_image_of_ball fun p hp => (h p hp).2⟩ }

end Prod

lemma infₛ_prod [InfSet α] [InfSet β] {s : Set α} {t : Set β} (hs : s.Nonempty) (ht : t.Nonempty) :
  infₛ (s ×ˢ t) = (infₛ s, infₛ t) :=
congr_arg₂ Prod.mk (congr_arg infₛ $ fst_image_prod _ ht) (congr_arg infₛ $ snd_image_prod hs _)
#align Inf_prod infₛ_prod

lemma supₛ_prod [SupSet α] [SupSet β] {s : Set α} {t : Set β} (hs : s.Nonempty) (ht : t.Nonempty) :
  supₛ (s ×ˢ t) = (supₛ s, supₛ t) :=
congr_arg₂ Prod.mk (congr_arg supₛ $ fst_image_prod _ ht) (congr_arg supₛ $ snd_image_prod hs _)
#align Sup_prod supₛ_prod

section CompleteLattice

variable [CompleteLattice α] {a : α} {s : Set α}

/-- This is a weaker version of `sup_infₛ_eq` -/
theorem sup_infₛ_le_infᵢ_sup : a ⊔ infₛ s ≤ ⨅ b ∈ s, a ⊔ b :=
  le_infᵢ₂ fun _ h => sup_le_sup_left (infₛ_le h) _
#align sup_Inf_le_infi_sup sup_infₛ_le_infᵢ_sup

/-- This is a weaker version of `inf_supₛ_eq` -/
theorem supᵢ_inf_le_inf_supₛ : (⨆ b ∈ s, a ⊓ b) ≤ a ⊓ supₛ s :=
  @sup_infₛ_le_infᵢ_sup αᵒᵈ _ _ _
#align supr_inf_le_inf_Sup supᵢ_inf_le_inf_supₛ

/-- This is a weaker version of `infₛ_sup_eq` -/
theorem infₛ_sup_le_infᵢ_sup : infₛ s ⊔ a ≤ ⨅ b ∈ s, b ⊔ a :=
  le_infᵢ₂ fun _ h => sup_le_sup_right (infₛ_le h) _
#align Inf_sup_le_infi_sup infₛ_sup_le_infᵢ_sup

/-- This is a weaker version of `supₛ_inf_eq` -/
theorem supᵢ_inf_le_supₛ_inf : (⨆ b ∈ s, b ⊓ a) ≤ supₛ s ⊓ a :=
  @infₛ_sup_le_infᵢ_sup αᵒᵈ _ _ _
#align supr_inf_le_Sup_inf supᵢ_inf_le_supₛ_inf

theorem le_supᵢ_inf_supᵢ (f g : ι → α) : (⨆ i, f i ⊓ g i) ≤ (⨆ i, f i) ⊓ ⨆ i, g i :=
  le_inf (supᵢ_mono fun _ => inf_le_left) (supᵢ_mono fun _ => inf_le_right)
#align le_supr_inf_supr le_supᵢ_inf_supᵢ

theorem infᵢ_sup_infᵢ_le (f g : ι → α) : ((⨅ i, f i) ⊔ ⨅ i, g i) ≤ ⨅ i, f i ⊔ g i :=
  @le_supᵢ_inf_supᵢ αᵒᵈ ι _ f g
#align infi_sup_infi_le infᵢ_sup_infᵢ_le

theorem disjoint_supₛ_left {a : Set α} {b : α} (d : Disjoint (supₛ a) b) {i} (hi : i ∈ a) :
    Disjoint i b :=
  disjoint_iff_inf_le.mpr (supᵢ₂_le_iff.1 (supᵢ_inf_le_supₛ_inf.trans d.le_bot) i hi : _)
#align disjoint_Sup_left disjoint_supₛ_left

theorem disjoint_supₛ_right {a : Set α} {b : α} (d : Disjoint b (supₛ a)) {i} (hi : i ∈ a) :
    Disjoint b i :=
  disjoint_iff_inf_le.mpr (supᵢ₂_le_iff.mp (supᵢ_inf_le_inf_supₛ.trans d.le_bot) i hi : _)
#align disjoint_Sup_right disjoint_supₛ_right

end CompleteLattice

-- See note [reducible non-instances]
/-- Pullback a `CompleteLattice` along an injection. -/
@[reducible]
protected def Function.Injective.completeLattice [Sup α] [Inf α] [SupSet α] [InfSet α] [Top α]
    [Bot α] [CompleteLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_supₛ : ∀ s, f (supₛ s) = ⨆ a ∈ s, f a) (map_infₛ : ∀ s, f (infₛ s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteLattice α :=
  { -- we cannot use BoundedOrder.lift here as the `LE` instance doesn't exist yet
    hf.lattice f map_sup map_inf with
    le_supₛ := fun _ a h => (le_supᵢ₂ a h).trans (map_supₛ _).ge
    supₛ_le := fun _ _ h => (map_supₛ _).trans_le <| supᵢ₂_le h
    infₛ_le := fun _ a h => (map_infₛ _).trans_le <| infᵢ₂_le a h
    le_infₛ := fun _ _ h => (le_infᵢ₂ h).trans (map_infₛ _).ge
    top := ⊤
    le_top := fun _ => (@le_top β _ _ _).trans map_top.ge
    bot := ⊥
    bot_le := fun _ => map_bot.le.trans bot_le }
#align function.injective.complete_lattice Function.Injective.completeLattice
