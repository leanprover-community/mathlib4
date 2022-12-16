/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl

! This file was ported from Lean 3 source module order.complete_lattice
! leanprover-community/mathlib commit aba57d4d3dae35460225919dcd82fe91355162f9
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Bool.Set
import Mathlib.Data.Nat.Set
import Mathlib.Data.ULift
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Hom.Basic

import Mathlib.Mathport.Notation
import Init.NotationExtra

/-!
# Theory of complete lattices

## Main definitions

* `Sup` and `Inf` are the supremum and the infimum of a set;
* `supᵢ (f : ι → α)` and `infᵢ (f : ι → α)` are indexed supremum and infimum of a function,
  defined as `Sup` and `Inf` of the range of this function;
* `class CompleteLattice`: a bounded lattice such that `Sup s` is always the least upper boundary
  of `s` and `Inf s` is always the greatest lower boundary of `s`;
* `class CompleteLinearOrder`: a linear ordered complete lattice.

## Naming conventions

In lemma names,
* `Sup` is called `Sup`
* `Inf` is called `Inf`
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
#align infᵢ infᵢ

instance (priority := 50) has_Inf_to_nonempty (α) [InfSet α] : Nonempty α :=
  ⟨infₛ ∅⟩
#align has_Inf_to_nonempty has_Inf_to_nonempty

instance (priority := 50) has_Sup_to_nonempty (α) [SupSet α] : Nonempty α :=
  ⟨supₛ ∅⟩
#align has_Sup_to_nonempty has_Sup_to_nonempty

/-
Porting note: the code below could replace the `notation3` command
open Std.ExtendedBinder in
syntax "⨆ " extBinder ", " term:51 : term

macro_rules
  | `(⨆ $x:ident, $p) => `(supᵢ fun $x:ident ↦ $p)
  | `(⨆ $x:ident : $t, $p) => `(supᵢ fun $x:ident : $t ↦ $p)
  | `(⨆ $x:ident $b:binderPred, $p) =>
    `(supᵢ fun $x:ident ↦ satisfiesBinderPred% $x $b ∧ $p) -/


notation3 "⨆ "(...)", "r:(scoped f => supᵢ f) => r

@[app_unexpander supᵢ]
def supᵢ.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ $p) => `(⨆ $x:ident, $p)
  | `($_ fun $x:ident : $ty:term ↦ $p) => `(⨆ $x:ident : $ty:term, $p)
  | _ => throw ()

notation3 "⨅ "(...)", "r:(scoped f => infᵢ f) => r

@[app_unexpander infᵢ]
def infᵢ.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ fun $x:ident ↦ $p) => `(⨅ $x:ident, $p)
  | `($_ fun $x:ident : $ty:term ↦ $p) => `(⨅ $x:ident : $ty:term, $p)
  | _ => throw ()

instance (α) [InfSet α] : SupSet αᵒᵈ :=
  ⟨(infₛ : Set α → α)⟩

instance (α) [SupSet α] : InfSet αᵒᵈ :=
  ⟨(supₛ : Set α → α)⟩

/-- Note that we rarely use `CompleteSemilatticeSup`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
class CompleteSemilatticeSup (α : Type _) extends PartialOrder α, SupSet α where
  le_supₛ : ∀ s, ∀ a ∈ s, a ≤ supₛ s
  supₛ_le : ∀ s a, (∀ b ∈ s, b ≤ a) → supₛ s ≤ a
#align complete_semilattice_Sup CompleteSemilatticeSup

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b : α}

-- @[ematch]  Porting note: attribute removed
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
#align le_supᵢ_iff le_supᵢ_iff

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
  Inf_le : ∀ s, ∀ a ∈ s, infₛ s ≤ a
  le_Inf : ∀ s a, (∀ b ∈ s, a ≤ b) → a ≤ infₛ s
#align complete_semilattice_Inf CompleteSemilatticeInf

section

variable [CompleteSemilatticeInf α] {s t : Set α} {a b : α}

-- @[ematch]  Porting note: attribute removed
theorem infₛ_le : a ∈ s → infₛ s ≤ a :=
  CompleteSemilatticeInf.Inf_le s a
#align Inf_le infₛ_le

theorem le_infₛ : (∀ b ∈ s, a ≤ b) → a ≤ infₛ s :=
  CompleteSemilatticeInf.le_Inf s a
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
#align infᵢ_le_iff infᵢ_le_iff

theorem infₛ_le_infₛ_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) : infₛ t ≤ infₛ s :=
  le_of_forall_le
    (by
      simp only [le_infₛ_iff]
      introv h₀ h₁
      rcases h _ h₁ with ⟨y, hy, hy'⟩
      solve_by_elim [le_trans _ hy'] )
#align Inf_le_Inf_of_forall_exists_le infₛ_le_infₛ_of_forall_exists_le

-- We will generalize this to conditionally complete lattices in `cInf_singleton`.
theorem infₛ_singleton {a : α} : infₛ {a} = a :=
  isGLB_singleton.infₛ_eq
#align Inf_singleton infₛ_singleton

end

/-- A complete lattice is a bounded lattice which has suprema and infima for every subset. -/
class CompleteLattice (α : Type _) extends Lattice α, CompleteSemilatticeSup α,
  CompleteSemilatticeInf α, Top α, Bot α where
  protected le_top : ∀ x : α, x ≤ ⊤
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
provided; for example, if `inf` is known explicitly, construct the `complete_lattice`
instance as
```
instance : CompleteLattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Sup, bot, top
  ..complete_lattice_of_Inf my_T _ }
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
    le_Inf := fun s a ha => (isGLB_infₛ s).2 ha
    Inf_le := fun s a ha => (isGLB_infₛ s).1 ha
    supₛ := fun s => infₛ (upperBounds s)
    le_supₛ := fun s a ha => (isGLB_infₛ (upperBounds s)).2 fun b hb => hb ha
    supₛ_le := fun s a ha => (isGLB_infₛ (upperBounds s)).1 ha }
#align complete_lattice_of_Inf completeLatticeOfInf

/-- Any `complete_semilattice_Inf` is in fact a `complete_lattice`.

Note that this construction has bad definitional properties:
see the doc-string on `complete_lattice_of_Inf`.
-/
def completeLatticeOfCompleteSemilatticeInf (α : Type _) [CompleteSemilatticeInf α] :
    CompleteLattice α :=
  completeLatticeOfInf α fun s => is_glb_Inf s
#align complete_lattice_of_complete_semilattice_Inf completeLatticeOfCompleteSemilatticeInf

/-- Create a `complete_lattice` from a `partial_order` and `Sup` function
that returns the least upper bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `complete_lattice`
instance as
```
instance : complete_lattice my_T :=
{ inf := better_inf,
  le_inf := ...,
  inf_le_right := ...,
  inf_le_left := ...
  -- don't care to fix sup, Inf, bot, top
  ..complete_lattice_of_Sup my_T _ }
```
-/
def completeLatticeOfSup (α : Type _) [H1 : PartialOrder α] [H2 : SupSet α]
    (is_lub_Sup : ∀ s : Set α, IsLUB s (sup s)) : CompleteLattice α :=
  { H1, H2 with
    top := sup univ
    le_top := fun x => (is_lub_Sup univ).1 trivial
    bot := sup ∅
    bot_le := fun x => (is_lub_Sup ∅).2 <| by simp
    sup := fun a b => sup {a, b}
    sup_le := fun a b c hac hbc => (is_lub_Sup _).2 (by simp [*])
    le_sup_left := fun a b => (is_lub_Sup _).1 <| mem_insert _ _
    le_sup_right := fun a b => (is_lub_Sup _).1 <| mem_insert_of_mem _ <| mem_singleton _
    inf := fun a b => sup { x | x ≤ a ∧ x ≤ b }
    le_inf := fun a b c hab hac => (is_lub_Sup _).1 <| by simp [*]
    inf_le_left := fun a b => (is_lub_Sup _).2 fun x => And.left
    inf_le_right := fun a b => (is_lub_Sup _).2 fun x => And.right
    inf := fun s => sup (lowerBounds s)
    Sup_le := fun s a ha => (is_lub_Sup s).2 ha
    le_Sup := fun s a ha => (is_lub_Sup s).1 ha
    Inf_le := fun s a ha => (is_lub_Sup (lowerBounds s)).2 fun b hb => hb ha
    le_Inf := fun s a ha => (is_lub_Sup (lowerBounds s)).1 ha }
#align complete_lattice_of_Sup completeLatticeOfSup

/-- Any `complete_semilattice_Sup` is in fact a `complete_lattice`.

Note that this construction has bad definitional properties:
see the doc-string on `complete_lattice_of_Sup`.
-/
def completeLatticeOfCompleteSemilatticeSup (α : Type _) [CompleteSemilatticeSup α] :
    CompleteLattice α :=
  completeLatticeOfSup α fun s => is_lub_Sup s
#align complete_lattice_of_complete_semilattice_Sup completeLatticeOfCompleteSemilatticeSup

/- ./././Mathport/Syntax/Translate/Command.lean:407:11: unsupported: advanced extends in structure -/
/-- A complete linear order is a linear order whose lattice structure is complete. -/
class CompleteLinearOrder (α : Type _) extends CompleteLattice α,
  "./././Mathport/Syntax/Translate/Command.lean:407:11: unsupported: advanced extends in structure"
#align complete_linear_order CompleteLinearOrder

namespace OrderDual

variable (α)

instance [CompleteLattice α] : CompleteLattice αᵒᵈ :=
  { OrderDual.lattice α, OrderDual.SupSet α, OrderDual.InfSet α, OrderDual.boundedOrder α with
    le_Sup := @CompleteLattice.Inf_le α _
    Sup_le := @CompleteLattice.le_Inf α _
    Inf_le := @CompleteLattice.le_Sup α _
    le_Inf := @CompleteLattice.Sup_le α _ }

instance [CompleteLinearOrder α] : CompleteLinearOrder αᵒᵈ :=
  { OrderDual.completeLattice α, OrderDual.instLinearOrderOrderDual α with }

end OrderDual

open OrderDual

section

variable [CompleteLattice α] {s t : Set α} {a b : α}

@[simp]
theorem to_dual_Sup (s : Set α) : toDual (sup s) = inf (of_dual ⁻¹' s) :=
  rfl
#align to_dual_Sup to_dual_Sup

@[simp]
theorem to_dual_Inf (s : Set α) : toDual (inf s) = sup (of_dual ⁻¹' s) :=
  rfl
#align to_dual_Inf to_dual_Inf

@[simp]
theorem of_dual_Sup (s : Set αᵒᵈ) : ofDual (sup s) = inf (to_dual ⁻¹' s) :=
  rfl
#align of_dual_Sup of_dual_Sup

@[simp]
theorem of_dual_Inf (s : Set αᵒᵈ) : ofDual (inf s) = sup (to_dual ⁻¹' s) :=
  rfl
#align of_dual_Inf of_dual_Inf

@[simp]
theorem to_dual_supᵢ (f : ι → α) : toDual (⨆ i, f i) = ⨅ i, toDual (f i) :=
  rfl
#align to_dual_supᵢ to_dual_supᵢ

@[simp]
theorem to_dual_infᵢ (f : ι → α) : toDual (⨅ i, f i) = ⨆ i, toDual (f i) :=
  rfl
#align to_dual_infᵢ to_dual_infᵢ

@[simp]
theorem of_dual_supᵢ (f : ι → αᵒᵈ) : ofDual (⨆ i, f i) = ⨅ i, ofDual (f i) :=
  rfl
#align of_dual_supᵢ of_dual_supᵢ

@[simp]
theorem of_dual_infᵢ (f : ι → αᵒᵈ) : ofDual (⨅ i, f i) = ⨆ i, ofDual (f i) :=
  rfl
#align of_dual_infᵢ of_dual_infᵢ

theorem Inf_le_Sup (hs : s.Nonempty) : inf s ≤ sup s :=
  is_glb_le_is_lub (is_glb_Inf s) (is_lub_Sup s) hs
#align Inf_le_Sup Inf_le_Sup

theorem Sup_union {s t : Set α} : sup (s ∪ t) = sup s ⊔ sup t :=
  ((is_lub_Sup s).union (is_lub_Sup t)).Sup_eq
#align Sup_union Sup_union

theorem Inf_union {s t : Set α} : inf (s ∪ t) = inf s ⊓ inf t :=
  ((is_glb_Inf s).union (is_glb_Inf t)).Inf_eq
#align Inf_union Inf_union

theorem Sup_inter_le {s t : Set α} : sup (s ∩ t) ≤ sup s ⊓ sup t :=
  Sup_le fun b hb => le_inf (le_Sup hb.1) (le_Sup hb.2)
#align Sup_inter_le Sup_inter_le

theorem le_Inf_inter {s t : Set α} : inf s ⊔ inf t ≤ inf (s ∩ t) :=
  @Sup_inter_le αᵒᵈ _ _ _
#align le_Inf_inter le_Inf_inter

@[simp]
theorem Sup_empty : sup ∅ = (⊥ : α) :=
  (@is_lub_empty α _ _).Sup_eq
#align Sup_empty Sup_empty

@[simp]
theorem Inf_empty : inf ∅ = (⊤ : α) :=
  (@is_glb_empty α _ _).Inf_eq
#align Inf_empty Inf_empty

@[simp]
theorem Sup_univ : sup univ = (⊤ : α) :=
  (@is_lub_univ α _ _).Sup_eq
#align Sup_univ Sup_univ

@[simp]
theorem Inf_univ : inf univ = (⊥ : α) :=
  (@is_glb_univ α _ _).Inf_eq
#align Inf_univ Inf_univ

-- TODO(Jeremy): get this automatically
@[simp]
theorem Sup_insert {a : α} {s : Set α} : sup (insert a s) = a ⊔ sup s :=
  ((is_lub_Sup s).insert a).Sup_eq
#align Sup_insert Sup_insert

@[simp]
theorem Inf_insert {a : α} {s : Set α} : inf (insert a s) = a ⊓ inf s :=
  ((is_glb_Inf s).insert a).Inf_eq
#align Inf_insert Inf_insert

theorem Sup_le_Sup_of_subset_insert_bot (h : s ⊆ insert ⊥ t) : sup s ≤ sup t :=
  le_trans (Sup_le_Sup h) (le_of_eq (trans Sup_insert bot_sup_eq))
#align Sup_le_Sup_of_subset_insert_bot Sup_le_Sup_of_subset_insert_bot

theorem Inf_le_Inf_of_subset_insert_top (h : s ⊆ insert ⊤ t) : inf t ≤ inf s :=
  le_trans (le_of_eq (trans top_inf_eq.symm Inf_insert.symm)) (Inf_le_Inf h)
#align Inf_le_Inf_of_subset_insert_top Inf_le_Inf_of_subset_insert_top

@[simp]
theorem Sup_diff_singleton_bot (s : Set α) : sup (s \ {⊥}) = sup s :=
  (Sup_le_Sup (diff_subset _ _)).antisymm <|
    Sup_le_Sup_of_subset_insert_bot <| subset_insert_diff_singleton _ _
#align Sup_diff_singleton_bot Sup_diff_singleton_bot

@[simp]
theorem Inf_diff_singleton_top (s : Set α) : inf (s \ {⊤}) = inf s :=
  @Sup_diff_singleton_bot αᵒᵈ _ s
#align Inf_diff_singleton_top Inf_diff_singleton_top

theorem Sup_pair {a b : α} : sup {a, b} = a ⊔ b :=
  (@is_lub_pair α _ a b).Sup_eq
#align Sup_pair Sup_pair

theorem Inf_pair {a b : α} : inf {a, b} = a ⊓ b :=
  (@is_glb_pair α _ a b).Inf_eq
#align Inf_pair Inf_pair

@[simp]
theorem Sup_eq_bot : sup s = ⊥ ↔ ∀ a ∈ s, a = ⊥ :=
  ⟨fun h a ha => bot_unique <| h ▸ le_Sup ha, fun h =>
    bot_unique <| Sup_le fun a ha => le_bot_iff.2 <| h a ha⟩
#align Sup_eq_bot Sup_eq_bot

@[simp]
theorem Inf_eq_top : inf s = ⊤ ↔ ∀ a ∈ s, a = ⊤ :=
  @Sup_eq_bot αᵒᵈ _ _
#align Inf_eq_top Inf_eq_top

theorem eq_singleton_bot_of_Sup_eq_bot_of_nonempty {s : Set α} (h_sup : sup s = ⊥)
    (hne : s.Nonempty) : s = {⊥} := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [Sup_eq_bot] at h_sup
  exact ⟨hne, h_sup⟩
#align eq_singleton_bot_of_Sup_eq_bot_of_nonempty eq_singleton_bot_of_Sup_eq_bot_of_nonempty

theorem eq_singleton_top_of_Inf_eq_top_of_nonempty : inf s = ⊤ → s.Nonempty → s = {⊤} :=
  @eq_singleton_bot_of_Sup_eq_bot_of_nonempty αᵒᵈ _ _
#align eq_singleton_top_of_Inf_eq_top_of_nonempty eq_singleton_top_of_Inf_eq_top_of_nonempty

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w < b`.
See `cSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem Sup_eq_of_forall_le_of_forall_lt_exists_gt (h₁ : ∀ a ∈ s, a ≤ b)
    (h₂ : ∀ w, w < b → ∃ a ∈ s, w < a) : sup s = b :=
  (Sup_le h₁).eq_of_not_lt fun h =>
    let ⟨a, ha, ha'⟩ := h₂ _ h
    ((le_Sup ha).trans_lt ha').False
#align Sup_eq_of_forall_le_of_forall_lt_exists_gt Sup_eq_of_forall_le_of_forall_lt_exists_gt

/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w > b`.
See `cInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem Inf_eq_of_forall_ge_of_forall_gt_exists_lt :
    (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → inf s = b :=
  @Sup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _
#align Inf_eq_of_forall_ge_of_forall_gt_exists_lt Inf_eq_of_forall_ge_of_forall_gt_exists_lt

end

section CompleteLinearOrder

variable [CompleteLinearOrder α] {s t : Set α} {a b : α}

theorem lt_Sup_iff : b < sup s ↔ ∃ a ∈ s, b < a :=
  lt_is_lub_iff <| is_lub_Sup s
#align lt_Sup_iff lt_Sup_iff

theorem Inf_lt_iff : inf s < b ↔ ∃ a ∈ s, a < b :=
  is_glb_lt_iff <| is_glb_Inf s
#align Inf_lt_iff Inf_lt_iff

theorem Sup_eq_top : sup s = ⊤ ↔ ∀ b < ⊤, ∃ a ∈ s, b < a :=
  ⟨fun h b hb => lt_Sup_iff.1 <| hb.trans_eq h.symm, fun h =>
    top_unique <|
      le_of_not_gt fun h' =>
        let ⟨a, ha, h⟩ := h _ h'
        (h.trans_le <| le_Sup ha).False⟩
#align Sup_eq_top Sup_eq_top

theorem Inf_eq_bot : inf s = ⊥ ↔ ∀ b > ⊥, ∃ a ∈ s, a < b :=
  @Sup_eq_top αᵒᵈ _ _
#align Inf_eq_bot Inf_eq_bot

theorem lt_supᵢ_iff {f : ι → α} : a < supᵢ f ↔ ∃ i, a < f i :=
  lt_Sup_iff.trans exists_range_iff
#align lt_supᵢ_iff lt_supᵢ_iff

theorem infᵢ_lt_iff {f : ι → α} : infᵢ f < a ↔ ∃ i, f i < a :=
  Inf_lt_iff.trans exists_range_iff
#align infᵢ_lt_iff infᵢ_lt_iff

end CompleteLinearOrder

/-
### supᵢ & infᵢ
-/
section SupSet

variable [SupSet α] {f g : ι → α}

theorem Sup_range : sup (range f) = supᵢ f :=
  rfl
#align Sup_range Sup_range

theorem Sup_eq_supᵢ' (s : Set α) : sup s = ⨆ a : s, a := by rw [supᵢ, Subtype.range_coe]
#align Sup_eq_supᵢ' Sup_eq_supᵢ'

theorem supᵢ_congr (h : ∀ i, f i = g i) : (⨆ i, f i) = ⨆ i, g i :=
  congr_arg _ <| funext h
#align supᵢ_congr supᵢ_congr

theorem Function.Surjective.supᵢ_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    (⨆ x, g (f x)) = ⨆ y, g y := by simp only [supᵢ, hf.range_comp]
#align function.surjective.supᵢ_comp Function.Surjective.supᵢ_comp

theorem Equiv.supᵢ_comp {g : ι' → α} (e : ι ≃ ι') : (⨆ x, g (e x)) = ⨆ y, g y :=
  e.Surjective.supᵢ_comp _
#align equiv.supᵢ_comp Equiv.supᵢ_comp

protected theorem Function.Surjective.supᵢ_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⨆ x, f x) = ⨆ y, g y := by
  convert h1.supᵢ_comp g
  exact (funext h2).symm
#align function.surjective.supᵢ_congr Function.Surjective.supᵢ_congr

protected theorem Equiv.supᵢ_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    (⨆ x, f x) = ⨆ y, g y :=
  e.Surjective.supᵢ_congr _ h
#align equiv.supᵢ_congr Equiv.supᵢ_congr

@[congr]
theorem supᵢ_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : supᵢ f₁ = supᵢ f₂ := by
  obtain rfl := propext pq
  congr with x
  apply f
#align supᵢ_congr_Prop supᵢ_congr_Prop

theorem supᵢ_plift_up (f : PLift ι → α) : (⨆ i, f (PLift.up i)) = ⨆ i, f i :=
  (PLift.up_surjective.supᵢ_congr _) fun _ => rfl
#align supᵢ_plift_up supᵢ_plift_up

theorem supᵢ_plift_down (f : ι → α) : (⨆ i, f (PLift.down i)) = ⨆ i, f i :=
  (PLift.down_surjective.supᵢ_congr _) fun _ => rfl
#align supᵢ_plift_down supᵢ_plift_down

theorem supᵢ_range' (g : β → α) (f : ι → β) : (⨆ b : range f, g b) = ⨆ i, g (f i) := by
  rw [supᵢ, supᵢ, ← image_eq_range, ← range_comp]
#align supᵢ_range' supᵢ_range'

theorem Sup_image' {s : Set β} {f : β → α} : sup (f '' s) = ⨆ a : s, f a := by
  rw [supᵢ, image_eq_range]
#align Sup_image' Sup_image'

end SupSet

section InfSet

variable [InfSet α] {f g : ι → α}

theorem Inf_range : inf (range f) = infᵢ f :=
  rfl
#align Inf_range Inf_range

theorem Inf_eq_infᵢ' (s : Set α) : inf s = ⨅ a : s, a :=
  @Sup_eq_supᵢ' αᵒᵈ _ _
#align Inf_eq_infᵢ' Inf_eq_infᵢ'

theorem infᵢ_congr (h : ∀ i, f i = g i) : (⨅ i, f i) = ⨅ i, g i :=
  congr_arg _ <| funext h
#align infᵢ_congr infᵢ_congr

theorem Function.Surjective.infᵢ_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    (⨅ x, g (f x)) = ⨅ y, g y :=
  @Function.Surjective.supᵢ_comp αᵒᵈ _ _ _ f hf g
#align function.surjective.infᵢ_comp Function.Surjective.infᵢ_comp

theorem Equiv.infᵢ_comp {g : ι' → α} (e : ι ≃ ι') : (⨅ x, g (e x)) = ⨅ y, g y :=
  @Equiv.supᵢ_comp αᵒᵈ _ _ _ _ e
#align equiv.infᵢ_comp Equiv.infᵢ_comp

protected theorem Function.Surjective.infᵢ_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : (⨅ x, f x) = ⨅ y, g y :=
  @Function.Surjective.supᵢ_congr αᵒᵈ _ _ _ _ _ h h1 h2
#align function.surjective.infᵢ_congr Function.Surjective.infᵢ_congr

protected theorem Equiv.infᵢ_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    (⨅ x, f x) = ⨅ y, g y :=
  @Equiv.supᵢ_congr αᵒᵈ _ _ _ _ _ e h
#align equiv.infᵢ_congr Equiv.infᵢ_congr

@[congr]
theorem infᵢ_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : infᵢ f₁ = infᵢ f₂ :=
  @supᵢ_congr_Prop αᵒᵈ _ p q f₁ f₂ pq f
#align infᵢ_congr_Prop infᵢ_congr_Prop

theorem infᵢ_plift_up (f : PLift ι → α) : (⨅ i, f (PLift.up i)) = ⨅ i, f i :=
  (PLift.up_surjective.infᵢ_congr _) fun _ => rfl
#align infᵢ_plift_up infᵢ_plift_up

theorem infᵢ_plift_down (f : ι → α) : (⨅ i, f (PLift.down i)) = ⨅ i, f i :=
  (PLift.down_surjective.infᵢ_congr _) fun _ => rfl
#align infᵢ_plift_down infᵢ_plift_down

theorem infᵢ_range' (g : β → α) (f : ι → β) : (⨅ b : range f, g b) = ⨅ i, g (f i) :=
  @supᵢ_range' αᵒᵈ _ _ _ _ _
#align infᵢ_range' infᵢ_range'

theorem Inf_image' {s : Set β} {f : β → α} : inf (f '' s) = ⨅ a : s, f a :=
  @Sup_image' αᵒᵈ _ _ _ _
#align Inf_image' Inf_image'

end InfSet

section

variable [CompleteLattice α] {f g s t : ι → α} {a b : α}

-- TODO: this declaration gives error when starting smt state
--@[ematch]
theorem le_supᵢ (f : ι → α) (i : ι) : f i ≤ supᵢ f :=
  le_Sup ⟨i, rfl⟩
#align le_supᵢ le_supᵢ

theorem infᵢ_le (f : ι → α) (i : ι) : infᵢ f ≤ f i :=
  Inf_le ⟨i, rfl⟩
#align infᵢ_le infᵢ_le

@[ematch]
theorem le_supᵢ' (f : ι → α) (i : ι) : f i ≤ supᵢ f :=
  le_Sup ⟨i, rfl⟩
#align le_supᵢ' le_supᵢ'

@[ematch]
theorem infᵢ_le' (f : ι → α) (i : ι) : infᵢ f ≤ f i :=
  Inf_le ⟨i, rfl⟩
#align infᵢ_le' infᵢ_le'

/- TODO: this version would be more powerful, but, alas, the pattern matcher
   doesn't accept it.
@[ematch] lemma le_supᵢ' (f : ι → α) (i : ι) : (: f i :) ≤ (: supᵢ f :) :=
le_Sup ⟨i, rfl⟩
-/
theorem is_lub_supᵢ : IsLUB (range f) (⨆ j, f j) :=
  is_lub_Sup _
#align is_lub_supᵢ is_lub_supᵢ

theorem is_glb_infᵢ : IsGlb (range f) (⨅ j, f j) :=
  is_glb_Inf _
#align is_glb_infᵢ is_glb_infᵢ

theorem IsLUB.supᵢ_eq (h : IsLUB (range f) a) : (⨆ j, f j) = a :=
  h.Sup_eq
#align is_lub.supᵢ_eq IsLUB.supᵢ_eq

theorem IsGlb.infᵢ_eq (h : IsGlb (range f) a) : (⨅ j, f j) = a :=
  h.Inf_eq
#align is_glb.infᵢ_eq IsGlb.infᵢ_eq

theorem le_supᵢ_of_le (i : ι) (h : a ≤ f i) : a ≤ supᵢ f :=
  h.trans <| le_supᵢ _ i
#align le_supᵢ_of_le le_supᵢ_of_le

theorem infᵢ_le_of_le (i : ι) (h : f i ≤ a) : infᵢ f ≤ a :=
  (infᵢ_le _ i).trans h
#align infᵢ_le_of_le infᵢ_le_of_le

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem le_supᵢ₂ {f : ∀ i, κ i → α} (i : ι) (j : κ i) : f i j ≤ ⨆ (i) (j), f i j :=
  le_supᵢ_of_le i <| le_supᵢ (f i) j
#align le_supᵢ₂ le_supᵢ₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ₂_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) : (⨅ (i) (j), f i j) ≤ f i j :=
  infᵢ_le_of_le i <| infᵢ_le (f i) j
#align infᵢ₂_le infᵢ₂_le

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem le_supᵢ₂_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : a ≤ f i j) :
    a ≤ ⨆ (i) (j), f i j :=
  h.trans <| le_supᵢ₂ i j
#align le_supᵢ₂_of_le le_supᵢ₂_of_le

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ₂_le_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : f i j ≤ a) :
    (⨅ (i) (j), f i j) ≤ a :=
  (infᵢ₂_le i j).trans h
#align infᵢ₂_le_of_le infᵢ₂_le_of_le

theorem supᵢ_le (h : ∀ i, f i ≤ a) : supᵢ f ≤ a :=
  Sup_le fun b ⟨i, Eq⟩ => Eq ▸ h i
#align supᵢ_le supᵢ_le

theorem le_infᵢ (h : ∀ i, a ≤ f i) : a ≤ infᵢ f :=
  le_Inf fun b ⟨i, Eq⟩ => Eq ▸ h i
#align le_infᵢ le_infᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supᵢ₂_le {f : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ a) : (⨆ (i) (j), f i j) ≤ a :=
  supᵢ_le fun i => supᵢ_le <| h i
#align supᵢ₂_le supᵢ₂_le

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem le_infᵢ₂ {f : ∀ i, κ i → α} (h : ∀ i j, a ≤ f i j) : a ≤ ⨅ (i) (j), f i j :=
  le_infᵢ fun i => le_infᵢ <| h i
#align le_infᵢ₂ le_infᵢ₂

theorem supᵢ₂_le_supᵢ (κ : ι → Sort _) (f : ι → α) : (⨆ (i) (j : κ i), f i) ≤ ⨆ i, f i :=
  supᵢ₂_le fun i j => le_supᵢ f i
#align supᵢ₂_le_supᵢ supᵢ₂_le_supᵢ

theorem infᵢ_le_infᵢ₂ (κ : ι → Sort _) (f : ι → α) : (⨅ i, f i) ≤ ⨅ (i) (j : κ i), f i :=
  le_infᵢ₂ fun i j => infᵢ_le f i
#align infᵢ_le_infᵢ₂ infᵢ_le_infᵢ₂

theorem supᵢ_mono (h : ∀ i, f i ≤ g i) : supᵢ f ≤ supᵢ g :=
  supᵢ_le fun i => le_supᵢ_of_le i <| h i
#align supᵢ_mono supᵢ_mono

theorem infᵢ_mono (h : ∀ i, f i ≤ g i) : infᵢ f ≤ infᵢ g :=
  le_infᵢ fun i => infᵢ_le_of_le i <| h i
#align infᵢ_mono infᵢ_mono

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supᵢ₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    (⨆ (i) (j), f i j) ≤ ⨆ (i) (j), g i j :=
  supᵢ_mono fun i => supᵢ_mono <| h i
#align supᵢ₂_mono supᵢ₂_mono

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    (⨅ (i) (j), f i j) ≤ ⨅ (i) (j), g i j :=
  infᵢ_mono fun i => infᵢ_mono <| h i
#align infᵢ₂_mono infᵢ₂_mono

theorem supᵢ_mono' {g : ι' → α} (h : ∀ i, ∃ i', f i ≤ g i') : supᵢ f ≤ supᵢ g :=
  supᵢ_le fun i => Exists.elim (h i) le_supᵢ_of_le
#align supᵢ_mono' supᵢ_mono'

theorem infᵢ_mono' {g : ι' → α} (h : ∀ i', ∃ i, f i ≤ g i') : infᵢ f ≤ infᵢ g :=
  le_infᵢ fun i' => Exists.elim (h i') infᵢ_le_of_le
#align infᵢ_mono' infᵢ_mono'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supᵢ₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i j ≤ g i' j') :
    (⨆ (i) (j), f i j) ≤ ⨆ (i) (j), g i j :=
  supᵢ₂_le fun i j =>
    let ⟨i', j', h⟩ := h i j
    le_supᵢ₂_of_le i' j' h
#align supᵢ₂_mono' supᵢ₂_mono'

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i' j' ≤ g i j) :
    (⨅ (i) (j), f i j) ≤ ⨅ (i) (j), g i j :=
  le_infᵢ₂ fun i j =>
    let ⟨i', j', h⟩ := h i j
    infᵢ₂_le_of_le i' j' h
#align infᵢ₂_mono' infᵢ₂_mono'

theorem supᵢ_const_mono (h : ι → ι') : (⨆ i : ι, a) ≤ ⨆ j : ι', a :=
  supᵢ_le <| le_supᵢ _ ∘ h
#align supᵢ_const_mono supᵢ_const_mono

theorem infᵢ_const_mono (h : ι' → ι) : (⨅ i : ι, a) ≤ ⨅ j : ι', a :=
  le_infᵢ <| infᵢ_le _ ∘ h
#align infᵢ_const_mono infᵢ_const_mono

theorem supᵢ_infᵢ_le_infᵢ_supᵢ (f : ι → ι' → α) : (⨆ i, ⨅ j, f i j) ≤ ⨅ j, ⨆ i, f i j :=
  supᵢ_le fun i => infᵢ_mono fun j => le_supᵢ _ i
#align supᵢ_infᵢ_le_infᵢ_supᵢ supᵢ_infᵢ_le_infᵢ_supᵢ

theorem bsupᵢ_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    (⨆ (i) (h : p i), f i) ≤ ⨆ (i) (h : q i), f i :=
  supᵢ_mono fun i => supᵢ_const_mono (hpq i)
#align bsupᵢ_mono bsupᵢ_mono

theorem binfᵢ_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    (⨅ (i) (h : q i), f i) ≤ ⨅ (i) (h : p i), f i :=
  infᵢ_mono fun i => infᵢ_const_mono (hpq i)
#align binfᵢ_mono binfᵢ_mono

@[simp]
theorem supᵢ_le_iff : supᵢ f ≤ a ↔ ∀ i, f i ≤ a :=
  (is_lub_le_iff is_lub_supᵢ).trans forall_range_iff
#align supᵢ_le_iff supᵢ_le_iff

@[simp]
theorem le_infᵢ_iff : a ≤ infᵢ f ↔ ∀ i, a ≤ f i :=
  (le_is_glb_iff is_glb_infᵢ).trans forall_range_iff
#align le_infᵢ_iff le_infᵢ_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem supᵢ₂_le_iff {f : ∀ i, κ i → α} : (⨆ (i) (j), f i j) ≤ a ↔ ∀ i j, f i j ≤ a := by
  simp_rw [supᵢ_le_iff]
#align supᵢ₂_le_iff supᵢ₂_le_iff

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem le_infᵢ₂_iff {f : ∀ i, κ i → α} : (a ≤ ⨅ (i) (j), f i j) ↔ ∀ i j, a ≤ f i j := by
  simp_rw [le_infᵢ_iff]
#align le_infᵢ₂_iff le_infᵢ₂_iff

theorem supᵢ_lt_iff : supᵢ f < a ↔ ∃ b, b < a ∧ ∀ i, f i ≤ b :=
  ⟨fun h => ⟨supᵢ f, h, le_supᵢ f⟩, fun ⟨b, h, hb⟩ => (supᵢ_le hb).trans_lt h⟩
#align supᵢ_lt_iff supᵢ_lt_iff

theorem lt_infᵢ_iff : a < infᵢ f ↔ ∃ b, a < b ∧ ∀ i, b ≤ f i :=
  ⟨fun h => ⟨infᵢ f, h, infᵢ_le f⟩, fun ⟨b, h, hb⟩ => h.trans_le <| le_infᵢ hb⟩
#align lt_infᵢ_iff lt_infᵢ_iff

theorem Sup_eq_supᵢ {s : Set α} : sup s = ⨆ a ∈ s, a :=
  le_antisymm (Sup_le le_supᵢ₂) (supᵢ₂_le fun b => le_Sup)
#align Sup_eq_supᵢ Sup_eq_supᵢ

theorem Inf_eq_infᵢ {s : Set α} : inf s = ⨅ a ∈ s, a :=
  @Sup_eq_supᵢ αᵒᵈ _ _
#align Inf_eq_infᵢ Inf_eq_infᵢ

theorem Monotone.le_map_supᵢ [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    (⨆ i, f (s i)) ≤ f (supᵢ s) :=
  supᵢ_le fun i => hf <| le_supᵢ _ _
#align monotone.le_map_supᵢ Monotone.le_map_supᵢ

theorem Antitone.le_map_infᵢ [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    (⨆ i, f (s i)) ≤ f (infᵢ s) :=
  hf.dual_left.le_map_supᵢ
#align antitone.le_map_infᵢ Antitone.le_map_infᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Monotone.le_map_supᵢ₂ [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    (⨆ (i) (j), f (s i j)) ≤ f (⨆ (i) (j), s i j) :=
  supᵢ₂_le fun i j => hf <| le_supᵢ₂ _ _
#align monotone.le_map_supᵢ₂ Monotone.le_map_supᵢ₂

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Antitone.le_map_infᵢ₂ [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    (⨆ (i) (j), f (s i j)) ≤ f (⨅ (i) (j), s i j) :=
  hf.dual_left.le_map_supᵢ₂ _
#align antitone.le_map_infᵢ₂ Antitone.le_map_infᵢ₂

theorem Monotone.le_map_Sup [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    (⨆ a ∈ s, f a) ≤ f (sup s) := by rw [Sup_eq_supᵢ] <;> exact hf.le_map_supᵢ₂ _
#align monotone.le_map_Sup Monotone.le_map_Sup

theorem Antitone.le_map_Inf [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    (⨆ a ∈ s, f a) ≤ f (inf s) :=
  hf.dual_left.le_map_Sup
#align antitone.le_map_Inf Antitone.le_map_Inf

theorem OrderIso.map_supᵢ [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨆ i, x i) = ⨆ i, f (x i) :=
  eq_of_forall_ge_iff <| f.Surjective.forall.2 fun x => by simp only [f.le_iff_le, supᵢ_le_iff]
#align order_iso.map_supᵢ OrderIso.map_supᵢ

theorem OrderIso.map_infᵢ [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨅ i, x i) = ⨅ i, f (x i) :=
  OrderIso.map_supᵢ f.dual _
#align order_iso.map_infᵢ OrderIso.map_infᵢ

theorem OrderIso.map_Sup [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (sup s) = ⨆ a ∈ s, f a :=
  by simp only [Sup_eq_supᵢ, OrderIso.map_supᵢ]
#align order_iso.map_Sup OrderIso.map_Sup

theorem OrderIso.map_Inf [CompleteLattice β] (f : α ≃o β) (s : Set α) : f (inf s) = ⨅ a ∈ s, f a :=
  OrderIso.map_Sup f.dual _
#align order_iso.map_Inf OrderIso.map_Inf

theorem supᵢ_comp_le {ι' : Sort _} (f : ι' → α) (g : ι → ι') : (⨆ x, f (g x)) ≤ ⨆ y, f y :=
  supᵢ_mono' fun x => ⟨_, le_rfl⟩
#align supᵢ_comp_le supᵢ_comp_le

theorem le_infᵢ_comp {ι' : Sort _} (f : ι' → α) (g : ι → ι') : (⨅ y, f y) ≤ ⨅ x, f (g x) :=
  infᵢ_mono' fun x => ⟨_, le_rfl⟩
#align le_infᵢ_comp le_infᵢ_comp

theorem Monotone.supᵢ_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, x ≤ s i) : (⨆ x, f (s x)) = ⨆ y, f y :=
  le_antisymm (supᵢ_comp_le _ _) (supᵢ_mono' fun x => (hs x).imp fun i hi => hf hi)
#align monotone.supᵢ_comp_eq Monotone.supᵢ_comp_eq

theorem Monotone.infᵢ_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, s i ≤ x) : (⨅ x, f (s x)) = ⨅ y, f y :=
  le_antisymm (infᵢ_mono' fun x => (hs x).imp fun i hi => hf hi) (le_infᵢ_comp _ _)
#align monotone.infᵢ_comp_eq Monotone.infᵢ_comp_eq

theorem Antitone.map_supᵢ_le [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    f (supᵢ s) ≤ ⨅ i, f (s i) :=
  le_infᵢ fun i => hf <| le_supᵢ _ _
#align antitone.map_supᵢ_le Antitone.map_supᵢ_le

theorem Monotone.map_infᵢ_le [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    f (infᵢ s) ≤ ⨅ i, f (s i) :=
  hf.dual_left.map_supᵢ_le
#align monotone.map_infᵢ_le Monotone.map_infᵢ_le

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Antitone.map_supᵢ₂_le [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    f (⨆ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_infᵢ₂ _
#align antitone.map_supᵢ₂_le Antitone.map_supᵢ₂_le

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Monotone.map_infᵢ₂_le [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    f (⨅ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_supᵢ₂ _
#align monotone.map_infᵢ₂_le Monotone.map_infᵢ₂_le

theorem Antitone.map_Sup_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    f (sup s) ≤ ⨅ a ∈ s, f a := by
  rw [Sup_eq_supᵢ]
  exact hf.map_supᵢ₂_le _
#align antitone.map_Sup_le Antitone.map_Sup_le

theorem Monotone.map_Inf_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    f (inf s) ≤ ⨅ a ∈ s, f a :=
  hf.dual_left.map_Sup_le
#align monotone.map_Inf_le Monotone.map_Inf_le

theorem supᵢ_const_le : (⨆ i : ι, a) ≤ a :=
  supᵢ_le fun _ => le_rfl
#align supᵢ_const_le supᵢ_const_le

theorem le_infᵢ_const : a ≤ ⨅ i : ι, a :=
  le_infᵢ fun _ => le_rfl
#align le_infᵢ_const le_infᵢ_const

-- We generalize this to conditionally complete lattices in `csupᵢ_const` and `cinfᵢ_const`.
theorem supᵢ_const [Nonempty ι] : (⨆ b : ι, a) = a := by rw [supᵢ, range_const, Sup_singleton]
#align supᵢ_const supᵢ_const

theorem infᵢ_const [Nonempty ι] : (⨅ b : ι, a) = a :=
  @supᵢ_const αᵒᵈ _ _ a _
#align infᵢ_const infᵢ_const

@[simp]
theorem supᵢ_bot : (⨆ i : ι, ⊥ : α) = ⊥ :=
  bot_unique supᵢ_const_le
#align supᵢ_bot supᵢ_bot

@[simp]
theorem infᵢ_top : (⨅ i : ι, ⊤ : α) = ⊤ :=
  top_unique le_infᵢ_const
#align infᵢ_top infᵢ_top

@[simp]
theorem supᵢ_eq_bot : supᵢ s = ⊥ ↔ ∀ i, s i = ⊥ :=
  Sup_eq_bot.trans forall_range_iff
#align supᵢ_eq_bot supᵢ_eq_bot

@[simp]
theorem infᵢ_eq_top : infᵢ s = ⊤ ↔ ∀ i, s i = ⊤ :=
  Inf_eq_top.trans forall_range_iff
#align infᵢ_eq_top infᵢ_eq_top

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem supᵢ₂_eq_bot {f : ∀ i, κ i → α} : (⨆ (i) (j), f i j) = ⊥ ↔ ∀ i j, f i j = ⊥ := by
  simp_rw [supᵢ_eq_bot]
#align supᵢ₂_eq_bot supᵢ₂_eq_bot

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem infᵢ₂_eq_top {f : ∀ i, κ i → α} : (⨅ (i) (j), f i j) = ⊤ ↔ ∀ i j, f i j = ⊤ := by
  simp_rw [infᵢ_eq_top]
#align infᵢ₂_eq_top infᵢ₂_eq_top

@[simp]
theorem supᵢ_pos {p : Prop} {f : p → α} (hp : p) : (⨆ h : p, f h) = f hp :=
  le_antisymm (supᵢ_le fun h => le_rfl) (le_supᵢ _ _)
#align supᵢ_pos supᵢ_pos

@[simp]
theorem infᵢ_pos {p : Prop} {f : p → α} (hp : p) : (⨅ h : p, f h) = f hp :=
  le_antisymm (infᵢ_le _ _) (le_infᵢ fun h => le_rfl)
#align infᵢ_pos infᵢ_pos

@[simp]
theorem supᵢ_neg {p : Prop} {f : p → α} (hp : ¬p) : (⨆ h : p, f h) = ⊥ :=
  le_antisymm (supᵢ_le fun h => (hp h).elim) bot_le
#align supᵢ_neg supᵢ_neg

@[simp]
theorem infᵢ_neg {p : Prop} {f : p → α} (hp : ¬p) : (⨅ h : p, f h) = ⊤ :=
  le_antisymm le_top <| le_infᵢ fun h => (hp h).elim
#align infᵢ_neg infᵢ_neg

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `csupᵢ_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem supᵢ_eq_of_forall_le_of_forall_lt_exists_gt {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : (⨆ i : ι, f i) = b :=
  Sup_eq_of_forall_le_of_forall_lt_exists_gt (forall_range_iff.mpr h₁) fun w hw =>
    exists_range_iff.mpr <| h₂ w hw
#align supᵢ_eq_of_forall_le_of_forall_lt_exists_gt supᵢ_eq_of_forall_le_of_forall_lt_exists_gt

/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `cinfᵢ_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem infᵢ_eq_of_forall_ge_of_forall_gt_exists_lt :
    (∀ i, b ≤ f i) → (∀ w, b < w → ∃ i, f i < w) → (⨅ i, f i) = b :=
  @supᵢ_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ _
#align infᵢ_eq_of_forall_ge_of_forall_gt_exists_lt infᵢ_eq_of_forall_ge_of_forall_gt_exists_lt

theorem supᵢ_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    (⨆ h : p, a h) = if h : p then a h else ⊥ := by by_cases p <;> simp [h]
#align supᵢ_eq_dif supᵢ_eq_dif

theorem supᵢ_eq_if {p : Prop} [Decidable p] (a : α) : (⨆ h : p, a) = if p then a else ⊥ :=
  supᵢ_eq_dif fun _ => a
#align supᵢ_eq_if supᵢ_eq_if

theorem infᵢ_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    (⨅ h : p, a h) = if h : p then a h else ⊤ :=
  @supᵢ_eq_dif αᵒᵈ _ _ _ _
#align infᵢ_eq_dif infᵢ_eq_dif

theorem infᵢ_eq_if {p : Prop} [Decidable p] (a : α) : (⨅ h : p, a) = if p then a else ⊤ :=
  infᵢ_eq_dif fun _ => a
#align infᵢ_eq_if infᵢ_eq_if

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (j i) -/
theorem supᵢ_comm {f : ι → ι' → α} : (⨆ (i) (j), f i j) = ⨆ (j) (i), f i j :=
  le_antisymm (supᵢ_le fun i => supᵢ_mono fun j => le_supᵢ _ i)
    (supᵢ_le fun j => supᵢ_mono fun i => le_supᵢ _ _)
#align supᵢ_comm supᵢ_comm

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (j i) -/
theorem infᵢ_comm {f : ι → ι' → α} : (⨅ (i) (j), f i j) = ⨅ (j) (i), f i j :=
  @supᵢ_comm αᵒᵈ _ _ _ _
#align infᵢ_comm infᵢ_comm

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem supᵢ₂_comm {ι₁ ι₂ : Sort _} {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    (⨆ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂) = ⨆ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@supᵢ_comm _ (κ₁ _), @supᵢ_comm _ ι₁]
#align supᵢ₂_comm supᵢ₂_comm

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₁ j₁ i₂ j₂) -/
/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i₂ j₂ i₁ j₁) -/
theorem infᵢ₂_comm {ι₁ ι₂ : Sort _} {κ₁ : ι₁ → Sort _} {κ₂ : ι₂ → Sort _}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    (⨅ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂) = ⨅ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@infᵢ_comm _ (κ₁ _), @infᵢ_comm _ ι₁]
#align infᵢ₂_comm infᵢ₂_comm

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
#align supᵢ_supᵢ_eq_left supᵢ_supᵢ_eq_left

@[simp]
theorem infᵢ_infᵢ_eq_left {b : β} {f : ∀ x : β, x = b → α} : (⨅ x, ⨅ h : x = b, f x h) = f b rfl :=
  @supᵢ_supᵢ_eq_left αᵒᵈ _ _ _ _
#align infᵢ_infᵢ_eq_left infᵢ_infᵢ_eq_left

@[simp]
theorem supᵢ_supᵢ_eq_right {b : β} {f : ∀ x : β, b = x → α} : (⨆ x, ⨆ h : b = x, f x h) = f b rfl :=
  (le_supᵢ₂ b rfl).antisymm'
    (supᵢ₂_le fun c => by
      rintro rfl
      rfl)
#align supᵢ_supᵢ_eq_right supᵢ_supᵢ_eq_right

@[simp]
theorem infᵢ_infᵢ_eq_right {b : β} {f : ∀ x : β, b = x → α} : (⨅ x, ⨅ h : b = x, f x h) = f b rfl :=
  @supᵢ_supᵢ_eq_right αᵒᵈ _ _ _ _
#align infᵢ_infᵢ_eq_right infᵢ_infᵢ_eq_right

attribute [ematch] le_refl

theorem supᵢ_subtype {p : ι → Prop} {f : Subtype p → α} : supᵢ f = ⨆ (i) (h : p i), f ⟨i, h⟩ :=
  le_antisymm (supᵢ_le fun ⟨i, h⟩ => le_supᵢ₂ i h) (supᵢ₂_le fun i h => le_supᵢ _ _)
#align supᵢ_subtype supᵢ_subtype

theorem infᵢ_subtype : ∀ {p : ι → Prop} {f : Subtype p → α}, infᵢ f = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  @supᵢ_subtype αᵒᵈ _ _
#align infᵢ_subtype infᵢ_subtype

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i h) -/
theorem supᵢ_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    (⨆ (i) (h), f i h) = ⨆ x : Subtype p, f x x.property :=
  (@supᵢ_subtype _ _ _ p fun x => f x.val x.property).symm
#align supᵢ_subtype' supᵢ_subtype'

theorem infᵢ_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    (⨅ (i) (h : p i), f i h) = ⨅ x : Subtype p, f x x.property :=
  (@infᵢ_subtype _ _ _ p fun x => f x.val x.property).symm
#align infᵢ_subtype' infᵢ_subtype'

theorem supᵢ_subtype'' {ι} (s : Set ι) (f : ι → α) : (⨆ i : s, f i) = ⨆ (t : ι) (H : t ∈ s), f t :=
  supᵢ_subtype
#align supᵢ_subtype'' supᵢ_subtype''

theorem infᵢ_subtype'' {ι} (s : Set ι) (f : ι → α) : (⨅ i : s, f i) = ⨅ (t : ι) (H : t ∈ s), f t :=
  infᵢ_subtype
#align infᵢ_subtype'' infᵢ_subtype''

theorem bsupᵢ_const {ι : Sort _} {a : α} {s : Set ι} (hs : s.Nonempty) : (⨆ i ∈ s, a) = a := by
  haveI : Nonempty s := set.nonempty_coe_sort.mpr hs
  rw [← supᵢ_subtype'', supᵢ_const]
#align bsupᵢ_const bsupᵢ_const

theorem binfᵢ_const {ι : Sort _} {a : α} {s : Set ι} (hs : s.Nonempty) : (⨅ i ∈ s, a) = a :=
  @bsupᵢ_const αᵒᵈ _ ι _ s hs
#align binfᵢ_const binfᵢ_const

theorem supᵢ_sup_eq : (⨆ x, f x ⊔ g x) = (⨆ x, f x) ⊔ ⨆ x, g x :=
  le_antisymm (supᵢ_le fun i => sup_le_sup (le_supᵢ _ _) <| le_supᵢ _ _)
    (sup_le (supᵢ_mono fun i => le_sup_left) <| supᵢ_mono fun i => le_sup_right)
#align supᵢ_sup_eq supᵢ_sup_eq

theorem infᵢ_inf_eq : (⨅ x, f x ⊓ g x) = (⨅ x, f x) ⊓ ⨅ x, g x :=
  @supᵢ_sup_eq αᵒᵈ _ _ _ _
#align infᵢ_inf_eq infᵢ_inf_eq

/- TODO: here is another example where more flexible pattern matching
   might help.

begin
  apply @le_antisymm,
  safe, pose h := f a ⊓ g a, begin [smt] ematch, ematch  end
end
-/
theorem supᵢ_sup [Nonempty ι] {f : ι → α} {a : α} : (⨆ x, f x) ⊔ a = ⨆ x, f x ⊔ a := by
  rw [supᵢ_sup_eq, supᵢ_const]
#align supᵢ_sup supᵢ_sup

theorem infᵢ_inf [Nonempty ι] {f : ι → α} {a : α} : (⨅ x, f x) ⊓ a = ⨅ x, f x ⊓ a := by
  rw [infᵢ_inf_eq, infᵢ_const]
#align infᵢ_inf infᵢ_inf

theorem sup_supᵢ [Nonempty ι] {f : ι → α} {a : α} : (a ⊔ ⨆ x, f x) = ⨆ x, a ⊔ f x := by
  rw [supᵢ_sup_eq, supᵢ_const]
#align sup_supᵢ sup_supᵢ

theorem inf_infᵢ [Nonempty ι] {f : ι → α} {a : α} : (a ⊓ ⨅ x, f x) = ⨅ x, a ⊓ f x := by
  rw [infᵢ_inf_eq, infᵢ_const]
#align inf_infᵢ inf_infᵢ

theorem bsupᵢ_sup {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨆ (i) (h : p i), f i h) ⊔ a = ⨆ (i) (h : p i), f i h ⊔ a := by
  haveI : Nonempty { i // p i } :=
      let ⟨i, hi⟩ := h
      ⟨⟨i, hi⟩⟩ <;>
    rw [supᵢ_subtype', supᵢ_subtype', supᵢ_sup]
#align bsupᵢ_sup bsupᵢ_sup

theorem sup_bsupᵢ {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊔ ⨆ (i) (h : p i), f i h) = ⨆ (i) (h : p i), a ⊔ f i h := by
  simpa only [sup_comm] using bsupᵢ_sup h
#align sup_bsupᵢ sup_bsupᵢ

theorem binfᵢ_inf {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨅ (i) (h : p i), f i h) ⊓ a = ⨅ (i) (h : p i), f i h ⊓ a :=
  @bsupᵢ_sup αᵒᵈ ι _ p f _ h
#align binfᵢ_inf binfᵢ_inf

theorem inf_binfᵢ {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊓ ⨅ (i) (h : p i), f i h) = ⨅ (i) (h : p i), a ⊓ f i h :=
  @sup_bsupᵢ αᵒᵈ ι _ p f _ h
#align inf_binfᵢ inf_binfᵢ

/-! ### `supᵢ` and `infᵢ` under `Prop` -/


@[simp]
theorem supᵢ_false {s : False → α} : supᵢ s = ⊥ :=
  le_antisymm (supᵢ_le fun i => False.elim i) bot_le
#align supᵢ_false supᵢ_false

@[simp]
theorem infᵢ_false {s : False → α} : infᵢ s = ⊤ :=
  le_antisymm le_top (le_infᵢ fun i => False.elim i)
#align infᵢ_false infᵢ_false

theorem supᵢ_true {s : True → α} : supᵢ s = s trivial :=
  supᵢ_pos trivial
#align supᵢ_true supᵢ_true

theorem infᵢ_true {s : True → α} : infᵢ s = s trivial :=
  infᵢ_pos trivial
#align infᵢ_true infᵢ_true

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i h) -/
@[simp]
theorem supᵢ_exists {p : ι → Prop} {f : Exists p → α} : (⨆ x, f x) = ⨆ (i) (h), f ⟨i, h⟩ :=
  le_antisymm (supᵢ_le fun ⟨i, h⟩ => le_supᵢ₂ i h) (supᵢ₂_le fun i h => le_supᵢ _ _)
#align supᵢ_exists supᵢ_exists

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i h) -/
@[simp]
theorem infᵢ_exists {p : ι → Prop} {f : Exists p → α} : (⨅ x, f x) = ⨅ (i) (h), f ⟨i, h⟩ :=
  @supᵢ_exists αᵒᵈ _ _ _ _
#align infᵢ_exists infᵢ_exists

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (h₁ h₂) -/
theorem supᵢ_and {p q : Prop} {s : p ∧ q → α} : supᵢ s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  le_antisymm (supᵢ_le fun ⟨i, h⟩ => le_supᵢ₂ i h) (supᵢ₂_le fun i h => le_supᵢ _ _)
#align supᵢ_and supᵢ_and

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (h₁ h₂) -/
theorem infᵢ_and {p q : Prop} {s : p ∧ q → α} : infᵢ s = ⨅ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  @supᵢ_and αᵒᵈ _ _ _ _
#align infᵢ_and infᵢ_and

/-- The symmetric case of `supᵢ_and`, useful for rewriting into a supremum over a conjunction -/
theorem supᵢ_and' {p q : Prop} {s : p → q → α} :
    (⨆ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨆ h : p ∧ q, s h.1 h.2 :=
  Eq.symm supᵢ_and
#align supᵢ_and' supᵢ_and'

/-- The symmetric case of `infᵢ_and`, useful for rewriting into a infimum over a conjunction -/
theorem infᵢ_and' {p q : Prop} {s : p → q → α} :
    (⨅ (h₁ : p) (h₂ : q), s h₁ h₂) = ⨅ h : p ∧ q, s h.1 h.2 :=
  Eq.symm infᵢ_and
#align infᵢ_and' infᵢ_and'

theorem supᵢ_or {p q : Prop} {s : p ∨ q → α} :
    (⨆ x, s x) = (⨆ i, s (Or.inl i)) ⊔ ⨆ j, s (Or.inr j) :=
  le_antisymm
    (supᵢ_le fun i =>
      match i with
      | Or.inl i => le_sup_of_le_left <| le_supᵢ _ i
      | Or.inr j => le_sup_of_le_right <| le_supᵢ _ j)
    (sup_le (supᵢ_comp_le _ _) (supᵢ_comp_le _ _))
#align supᵢ_or supᵢ_or

theorem infᵢ_or {p q : Prop} {s : p ∨ q → α} :
    (⨅ x, s x) = (⨅ i, s (Or.inl i)) ⊓ ⨅ j, s (Or.inr j) :=
  @supᵢ_or αᵒᵈ _ _ _ _
#align infᵢ_or infᵢ_or

section

variable (p : ι → Prop) [DecidablePred p]

theorem supᵢ_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    (⨆ i, if h : p i then f i h else g i h) = (⨆ (i) (h : p i), f i h) ⊔ ⨆ (i) (h : ¬p i), g i h :=
  by
  rw [← supᵢ_sup_eq]
  congr 1 with i
  split_ifs with h <;> simp [h]
#align supᵢ_dite supᵢ_dite

theorem infᵢ_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    (⨅ i, if h : p i then f i h else g i h) = (⨅ (i) (h : p i), f i h) ⊓ ⨅ (i) (h : ¬p i), g i h :=
  supᵢ_dite p (show ∀ i, p i → αᵒᵈ from f) g
#align infᵢ_dite infᵢ_dite

theorem supᵢ_ite (f g : ι → α) :
    (⨆ i, if p i then f i else g i) = (⨆ (i) (h : p i), f i) ⊔ ⨆ (i) (h : ¬p i), g i :=
  supᵢ_dite _ _ _
#align supᵢ_ite supᵢ_ite

theorem infᵢ_ite (f g : ι → α) :
    (⨅ i, if p i then f i else g i) = (⨅ (i) (h : p i), f i) ⊓ ⨅ (i) (h : ¬p i), g i :=
  infᵢ_dite _ _ _
#align infᵢ_ite infᵢ_ite

end

theorem supᵢ_range {g : β → α} {f : ι → β} : (⨆ b ∈ range f, g b) = ⨆ i, g (f i) := by
  rw [← supᵢ_subtype'', supᵢ_range']
#align supᵢ_range supᵢ_range

theorem infᵢ_range : ∀ {g : β → α} {f : ι → β}, (⨅ b ∈ range f, g b) = ⨅ i, g (f i) :=
  @supᵢ_range αᵒᵈ _ _ _
#align infᵢ_range infᵢ_range

theorem Sup_image {s : Set β} {f : β → α} : sup (f '' s) = ⨆ a ∈ s, f a := by
  rw [← supᵢ_subtype'', Sup_image']
#align Sup_image Sup_image

theorem Inf_image {s : Set β} {f : β → α} : inf (f '' s) = ⨅ a ∈ s, f a :=
  @Sup_image αᵒᵈ _ _ _ _
#align Inf_image Inf_image

/-
### supᵢ and infᵢ under set constructions
-/
theorem supᵢ_emptyset {f : β → α} : (⨆ x ∈ (∅ : Set β), f x) = ⊥ := by simp
#align supᵢ_emptyset supᵢ_emptyset

theorem infᵢ_emptyset {f : β → α} : (⨅ x ∈ (∅ : Set β), f x) = ⊤ := by simp
#align infᵢ_emptyset infᵢ_emptyset

theorem supᵢ_univ {f : β → α} : (⨆ x ∈ (univ : Set β), f x) = ⨆ x, f x := by simp
#align supᵢ_univ supᵢ_univ

theorem infᵢ_univ {f : β → α} : (⨅ x ∈ (univ : Set β), f x) = ⨅ x, f x := by simp
#align infᵢ_univ infᵢ_univ

theorem supᵢ_union {f : β → α} {s t : Set β} : (⨆ x ∈ s ∪ t, f x) = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x :=
  by simp_rw [mem_union, supᵢ_or, supᵢ_sup_eq]
#align supᵢ_union supᵢ_union

theorem infᵢ_union {f : β → α} {s t : Set β} : (⨅ x ∈ s ∪ t, f x) = (⨅ x ∈ s, f x) ⊓ ⨅ x ∈ t, f x :=
  @supᵢ_union αᵒᵈ _ _ _ _ _
#align infᵢ_union infᵢ_union

theorem supᵢ_split (f : β → α) (p : β → Prop) :
    (⨆ i, f i) = (⨆ (i) (h : p i), f i) ⊔ ⨆ (i) (h : ¬p i), f i := by
  simpa [Classical.em] using @supᵢ_union _ _ _ f { i | p i } { i | ¬p i }
#align supᵢ_split supᵢ_split

theorem infᵢ_split :
    ∀ (f : β → α) (p : β → Prop), (⨅ i, f i) = (⨅ (i) (h : p i), f i) ⊓ ⨅ (i) (h : ¬p i), f i :=
  @supᵢ_split αᵒᵈ _ _
#align infᵢ_split infᵢ_split

theorem supᵢ_split_single (f : β → α) (i₀ : β) : (⨆ i, f i) = f i₀ ⊔ ⨆ (i) (h : i ≠ i₀), f i := by
  convert supᵢ_split _ _
  simp
#align supᵢ_split_single supᵢ_split_single

theorem infᵢ_split_single (f : β → α) (i₀ : β) : (⨅ i, f i) = f i₀ ⊓ ⨅ (i) (h : i ≠ i₀), f i :=
  @supᵢ_split_single αᵒᵈ _ _ _ _
#align infᵢ_split_single infᵢ_split_single

theorem supᵢ_le_supᵢ_of_subset {f : β → α} {s t : Set β} : s ⊆ t → (⨆ x ∈ s, f x) ≤ ⨆ x ∈ t, f x :=
  bsupᵢ_mono
#align supᵢ_le_supᵢ_of_subset supᵢ_le_supᵢ_of_subset

theorem infᵢ_le_infᵢ_of_subset {f : β → α} {s t : Set β} : s ⊆ t → (⨅ x ∈ t, f x) ≤ ⨅ x ∈ s, f x :=
  binfᵢ_mono
#align infᵢ_le_infᵢ_of_subset infᵢ_le_infᵢ_of_subset

theorem supᵢ_insert {f : β → α} {s : Set β} {b : β} :
    (⨆ x ∈ insert b s, f x) = f b ⊔ ⨆ x ∈ s, f x :=
  Eq.trans supᵢ_union <| congr_arg (fun x => x ⊔ ⨆ x ∈ s, f x) supᵢ_supᵢ_eq_left
#align supᵢ_insert supᵢ_insert

theorem infᵢ_insert {f : β → α} {s : Set β} {b : β} :
    (⨅ x ∈ insert b s, f x) = f b ⊓ ⨅ x ∈ s, f x :=
  Eq.trans infᵢ_union <| congr_arg (fun x => x ⊓ ⨅ x ∈ s, f x) infᵢ_infᵢ_eq_left
#align infᵢ_insert infᵢ_insert

theorem supᵢ_singleton {f : β → α} {b : β} : (⨆ x ∈ (singleton b : Set β), f x) = f b := by simp
#align supᵢ_singleton supᵢ_singleton

theorem infᵢ_singleton {f : β → α} {b : β} : (⨅ x ∈ (singleton b : Set β), f x) = f b := by simp
#align infᵢ_singleton infᵢ_singleton

theorem supᵢ_pair {f : β → α} {a b : β} : (⨆ x ∈ ({a, b} : Set β), f x) = f a ⊔ f b := by
  rw [supᵢ_insert, supᵢ_singleton]
#align supᵢ_pair supᵢ_pair

theorem infᵢ_pair {f : β → α} {a b : β} : (⨅ x ∈ ({a, b} : Set β), f x) = f a ⊓ f b := by
  rw [infᵢ_insert, infᵢ_singleton]
#align infᵢ_pair infᵢ_pair

theorem supᵢ_image {γ} {f : β → γ} {g : γ → α} {t : Set β} :
    (⨆ c ∈ f '' t, g c) = ⨆ b ∈ t, g (f b) := by rw [← Sup_image, ← Sup_image, ← image_comp]
#align supᵢ_image supᵢ_image

theorem infᵢ_image :
    ∀ {γ} {f : β → γ} {g : γ → α} {t : Set β}, (⨅ c ∈ f '' t, g c) = ⨅ b ∈ t, g (f b) :=
  @supᵢ_image αᵒᵈ _ _
#align infᵢ_image infᵢ_image

theorem supᵢ_extend_bot {e : ι → β} (he : Injective e) (f : ι → α) :
    (⨆ j, extend e f ⊥ j) = ⨆ i, f i := by
  rw [supᵢ_split _ fun j => ∃ i, e i = j]
  simp (config := { contextual := true }) [he.extend_apply, extend_apply', @supᵢ_comm _ β ι]
#align supᵢ_extend_bot supᵢ_extend_bot

theorem infᵢ_extend_top {e : ι → β} (he : Injective e) (f : ι → α) :
    (⨅ j, extend e f ⊤ j) = infᵢ f :=
  @supᵢ_extend_bot αᵒᵈ _ _ _ _ he _
#align infᵢ_extend_top infᵢ_extend_top

/-!
### `supᵢ` and `infᵢ` under `Type`
-/


theorem supᵢ_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι → α) : supᵢ f = sup (∅ : Set α) :=
  congr_arg sup (range_eq_empty f)
#align supᵢ_of_empty' supᵢ_of_empty'

theorem infᵢ_of_empty' {α ι} [InfSet α] [IsEmpty ι] (f : ι → α) : infᵢ f = inf (∅ : Set α) :=
  congr_arg inf (range_eq_empty f)
#align infᵢ_of_empty' infᵢ_of_empty'

theorem supᵢ_of_empty [IsEmpty ι] (f : ι → α) : supᵢ f = ⊥ :=
  (supᵢ_of_empty' f).trans Sup_empty
#align supᵢ_of_empty supᵢ_of_empty

theorem infᵢ_of_empty [IsEmpty ι] (f : ι → α) : infᵢ f = ⊤ :=
  @supᵢ_of_empty αᵒᵈ _ _ _ f
#align infᵢ_of_empty infᵢ_of_empty

theorem supᵢ_bool_eq {f : Bool → α} : (⨆ b : Bool, f b) = f true ⊔ f false := by
  rw [supᵢ, Bool.range_eq, Sup_pair, sup_comm]
#align supᵢ_bool_eq supᵢ_bool_eq

theorem infᵢ_bool_eq {f : Bool → α} : (⨅ b : Bool, f b) = f true ⊓ f false :=
  @supᵢ_bool_eq αᵒᵈ _ _
#align infᵢ_bool_eq infᵢ_bool_eq

theorem sup_eq_supᵢ (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y := by
  rw [supᵢ_bool_eq, Bool.cond_true, Bool.cond_false]
#align sup_eq_supᵢ sup_eq_supᵢ

theorem inf_eq_infᵢ (x y : α) : x ⊓ y = ⨅ b : Bool, cond b x y :=
  @sup_eq_supᵢ αᵒᵈ _ _ _
#align inf_eq_infᵢ inf_eq_infᵢ

theorem is_glb_binfᵢ {s : Set β} {f : β → α} : IsGlb (f '' s) (⨅ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, infᵢ_subtype'] using @is_glb_infᵢ α s _ (f ∘ coe)
#align is_glb_binfᵢ is_glb_binfᵢ

theorem is_lub_bsupᵢ {s : Set β} {f : β → α} : IsLUB (f '' s) (⨆ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, supᵢ_subtype'] using @is_lub_supᵢ α s _ (f ∘ coe)
#align is_lub_bsupᵢ is_lub_bsupᵢ

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supᵢ_sigma {p : β → Type _} {f : Sigma p → α} : (⨆ x, f x) = ⨆ (i) (j), f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun c => by simp only [supᵢ_le_iff, Sigma.forall]
#align supᵢ_sigma supᵢ_sigma

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ_sigma {p : β → Type _} {f : Sigma p → α} : (⨅ x, f x) = ⨅ (i) (j), f ⟨i, j⟩ :=
  @supᵢ_sigma αᵒᵈ _ _ _ _
#align infᵢ_sigma infᵢ_sigma

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem supᵢ_prod {f : β × γ → α} : (⨆ x, f x) = ⨆ (i) (j), f (i, j) :=
  eq_of_forall_ge_iff fun c => by simp only [supᵢ_le_iff, Prod.forall]
#align supᵢ_prod supᵢ_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem infᵢ_prod {f : β × γ → α} : (⨅ x, f x) = ⨅ (i) (j), f (i, j) :=
  @supᵢ_prod αᵒᵈ _ _ _ _
#align infᵢ_prod infᵢ_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem bsupᵢ_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    (⨆ x ∈ s ×ˢ t, f x) = ⨆ (a ∈ s) (b ∈ t), f (a, b) := by
  simp_rw [supᵢ_prod, mem_prod, supᵢ_and]
  exact supᵢ_congr fun _ => supᵢ_comm
#align bsupᵢ_prod bsupᵢ_prod

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem binfᵢ_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    (⨅ x ∈ s ×ˢ t, f x) = ⨅ (a ∈ s) (b ∈ t), f (a, b) :=
  @bsupᵢ_prod αᵒᵈ _ _ _ _ _ _
#align binfᵢ_prod binfᵢ_prod

theorem supᵢ_sum {f : Sum β γ → α} : (⨆ x, f x) = (⨆ i, f (Sum.inl i)) ⊔ ⨆ j, f (Sum.inr j) :=
  eq_of_forall_ge_iff fun c => by simp only [sup_le_iff, supᵢ_le_iff, Sum.forall]
#align supᵢ_sum supᵢ_sum

theorem infᵢ_sum {f : Sum β γ → α} : (⨅ x, f x) = (⨅ i, f (Sum.inl i)) ⊓ ⨅ j, f (Sum.inr j) :=
  @supᵢ_sum αᵒᵈ _ _ _ _
#align infᵢ_sum infᵢ_sum

theorem supᵢ_option (f : Option β → α) : (⨆ o, f o) = f none ⊔ ⨆ b, f (Option.some b) :=
  eq_of_forall_ge_iff fun c => by simp only [supᵢ_le_iff, sup_le_iff, Option.forall]
#align supᵢ_option supᵢ_option

theorem infᵢ_option (f : Option β → α) : (⨅ o, f o) = f none ⊓ ⨅ b, f (Option.some b) :=
  @supᵢ_option αᵒᵈ _ _ _
#align infᵢ_option infᵢ_option

/-- A version of `supᵢ_option` useful for rewriting right-to-left. -/
theorem supᵢ_option_elim (a : α) (f : β → α) : (⨆ o : Option β, o.elim a f) = a ⊔ ⨆ b, f b := by
  simp [supᵢ_option]
#align supᵢ_option_elim supᵢ_option_elim

/-- A version of `infᵢ_option` useful for rewriting right-to-left. -/
theorem infᵢ_option_elim (a : α) (f : β → α) : (⨅ o : Option β, o.elim a f) = a ⊓ ⨅ b, f b :=
  @supᵢ_option_elim αᵒᵈ _ _ _ _
#align infᵢ_option_elim infᵢ_option_elim

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
#align supᵢ_ne_bot_subtype supᵢ_ne_bot_subtype

/-- When taking the infimum of `f : ι → α`, the elements of `ι` on which `f` gives `⊤` can be
dropped, without changing the result. -/
theorem infᵢ_ne_top_subtype (f : ι → α) : (⨅ i : { i // f i ≠ ⊤ }, f i) = ⨅ i, f i :=
  @supᵢ_ne_bot_subtype αᵒᵈ ι _ f
#align infᵢ_ne_top_subtype infᵢ_ne_top_subtype

theorem Sup_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    sup (image2 f s t) = ⨆ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, Sup_image, bsupᵢ_prod]
#align Sup_image2 Sup_image2

theorem Inf_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    inf (image2 f s t) = ⨅ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, Inf_image, binfᵢ_prod]
#align Inf_image2 Inf_image2

/-!
### `supᵢ` and `infᵢ` under `ℕ`
-/


theorem supᵢ_ge_eq_supᵢ_nat_add (u : ℕ → α) (n : ℕ) : (⨆ i ≥ n, u i) = ⨆ i, u (i + n) := by
  apply le_antisymm <;> simp only [supᵢ_le_iff]
  ·
    exact fun i hi =>
      le_Sup
        ⟨i - n, by
          dsimp only
          rw [Nat.sub_add_cancel hi]⟩
  · exact fun i => le_Sup ⟨i + n, supᵢ_pos (Nat.le_add_left _ _)⟩
#align supᵢ_ge_eq_supᵢ_nat_add supᵢ_ge_eq_supᵢ_nat_add

theorem infᵢ_ge_eq_infᵢ_nat_add (u : ℕ → α) (n : ℕ) : (⨅ i ≥ n, u i) = ⨅ i, u (i + n) :=
  @supᵢ_ge_eq_supᵢ_nat_add αᵒᵈ _ _ _
#align infᵢ_ge_eq_infᵢ_nat_add infᵢ_ge_eq_infᵢ_nat_add

theorem Monotone.supᵢ_nat_add {f : ℕ → α} (hf : Monotone f) (k : ℕ) : (⨆ n, f (n + k)) = ⨆ n, f n :=
  le_antisymm (supᵢ_le fun i => le_supᵢ _ (i + k)) <| supᵢ_mono fun i => hf <| Nat.le_add_right i k
#align monotone.supᵢ_nat_add Monotone.supᵢ_nat_add

theorem Antitone.infᵢ_nat_add {f : ℕ → α} (hf : Antitone f) (k : ℕ) : (⨅ n, f (n + k)) = ⨅ n, f n :=
  hf.dual_right.supᵢ_nat_add k
#align antitone.infᵢ_nat_add Antitone.infᵢ_nat_add

@[simp]
theorem supᵢ_infᵢ_ge_nat_add (f : ℕ → α) (k : ℕ) : (⨆ n, ⨅ i ≥ n, f (i + k)) = ⨆ n, ⨅ i ≥ n, f i :=
  by
  have hf : Monotone fun n => ⨅ i ≥ n, f i := fun n m h => binfᵢ_mono fun i => h.trans
  rw [← Monotone.supᵢ_nat_add hf k]
  · simp_rw [infᵢ_ge_eq_infᵢ_nat_add, ← Nat.add_assoc]
#align supᵢ_infᵢ_ge_nat_add supᵢ_infᵢ_ge_nat_add

@[simp]
theorem infᵢ_supᵢ_ge_nat_add :
    ∀ (f : ℕ → α) (k : ℕ), (⨅ n, ⨆ i ≥ n, f (i + k)) = ⨅ n, ⨆ i ≥ n, f i :=
  @supᵢ_infᵢ_ge_nat_add αᵒᵈ _
#align infᵢ_supᵢ_ge_nat_add infᵢ_supᵢ_ge_nat_add

theorem sup_supᵢ_nat_succ (u : ℕ → α) : (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ i, u i :=
  calc
    (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ x ∈ {0} ∪ range Nat.succ, u x := by
      rw [supᵢ_union, supᵢ_singleton, supᵢ_range]
    _ = ⨆ i, u i := by rw [Nat.zero_union_range_succ, supᵢ_univ]

#align sup_supᵢ_nat_succ sup_supᵢ_nat_succ

theorem inf_infᵢ_nat_succ (u : ℕ → α) : (u 0 ⊓ ⨅ i, u (i + 1)) = ⨅ i, u i :=
  @sup_supᵢ_nat_succ αᵒᵈ _ u
#align inf_infᵢ_nat_succ inf_infᵢ_nat_succ

theorem infᵢ_nat_gt_zero_eq (f : ℕ → α) : (⨅ i > 0, f i) = ⨅ i, f (i + 1) := by
  rw [← infᵢ_range, Nat.range_succ]
  simp only [mem_set_of]
#align infᵢ_nat_gt_zero_eq infᵢ_nat_gt_zero_eq

theorem supᵢ_nat_gt_zero_eq (f : ℕ → α) : (⨆ i > 0, f i) = ⨆ i, f (i + 1) :=
  @infᵢ_nat_gt_zero_eq αᵒᵈ _ f
#align supᵢ_nat_gt_zero_eq supᵢ_nat_gt_zero_eq

end

section CompleteLinearOrder

variable [CompleteLinearOrder α]

theorem supᵢ_eq_top (f : ι → α) : supᵢ f = ⊤ ↔ ∀ b < ⊤, ∃ i, b < f i := by
  simp only [← Sup_range, Sup_eq_top, Set.exists_range_iff]
#align supᵢ_eq_top supᵢ_eq_top

theorem infᵢ_eq_bot (f : ι → α) : infᵢ f = ⊥ ↔ ∀ b > ⊥, ∃ i, f i < b := by
  simp only [← Inf_range, Inf_eq_bot, Set.exists_range_iff]
#align infᵢ_eq_bot infᵢ_eq_bot

end CompleteLinearOrder

/-!
### Instances
-/


instance PropCat.completeLattice : CompleteLattice Prop :=
  { Prop.boundedOrder, Prop.distribLattice with
    sup := fun s => ∃ a ∈ s, a
    le_Sup := fun s a h p => ⟨a, h, p⟩
    Sup_le := fun s a h ⟨b, h', p⟩ => h b h' p
    inf := fun s => ∀ a, a ∈ s → a
    Inf_le := fun s a h p => p a h
    le_Inf := fun s a h p b hb => h b hb p }
#align Prop.complete_lattice PropCat.completeLattice

noncomputable instance PropCat.completeLinearOrder : CompleteLinearOrder Prop :=
  { PropCat.completeLattice, Prop.linearOrder with }
#align Prop.complete_linear_order PropCat.completeLinearOrder

@[simp]
theorem Sup_Prop_eq {s : Set Prop} : sup s = ∃ p ∈ s, p :=
  rfl
#align Sup_Prop_eq Sup_Prop_eq

@[simp]
theorem Inf_Prop_eq {s : Set Prop} : inf s = ∀ p ∈ s, p :=
  rfl
#align Inf_Prop_eq Inf_Prop_eq

@[simp]
theorem supᵢ_Prop_eq {p : ι → Prop} : (⨆ i, p i) = ∃ i, p i :=
  le_antisymm (fun ⟨q, ⟨i, (Eq : p i = q)⟩, hq⟩ => ⟨i, Eq.symm ▸ hq⟩) fun ⟨i, hi⟩ =>
    ⟨p i, ⟨i, rfl⟩, hi⟩
#align supᵢ_Prop_eq supᵢ_Prop_eq

@[simp]
theorem infᵢ_Prop_eq {p : ι → Prop} : (⨅ i, p i) = ∀ i, p i :=
  le_antisymm (fun h i => h _ ⟨i, rfl⟩) fun h p ⟨i, Eq⟩ => Eq ▸ h i
#align infᵢ_Prop_eq infᵢ_Prop_eq

/- warning: pi.has_Sup clashes with pi.has_sup -> Pi.SupSet
Case conversion may be inaccurate. Consider using '#align pi.has_Sup Pi.SupSetₓ'. -/
#print Pi.SupSet /-
instance Pi.SupSet {α : Type _} {β : α → Type _} [∀ i, SupSet (β i)] : SupSet (∀ i, β i) :=
  ⟨fun s i => ⨆ f : s, (f : ∀ i, β i) i⟩
#align pi.has_Sup Pi.SupSet
-/

/- warning: pi.has_Inf clashes with pi.has_inf -> Pi.InfSet
Case conversion may be inaccurate. Consider using '#align pi.has_Inf Pi.InfSetₓ'. -/
#print Pi.InfSet /-
instance Pi.InfSet {α : Type _} {β : α → Type _} [∀ i, InfSet (β i)] : InfSet (∀ i, β i) :=
  ⟨fun s i => ⨅ f : s, (f : ∀ i, β i) i⟩
#align pi.has_Inf Pi.InfSet
-/

instance Pi.completeLattice {α : Type _} {β : α → Type _} [∀ i, CompleteLattice (β i)] :
    CompleteLattice (∀ i, β i) :=
  { Pi.boundedOrder, Pi.lattice with
    sup := sup
    inf := inf
    le_Sup := fun s f hf i => le_supᵢ (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩
    Inf_le := fun s f hf i => infᵢ_le (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩
    Sup_le := fun s f hf i => supᵢ_le fun g => hf g g.2 i
    le_Inf := fun s f hf i => le_infᵢ fun g => hf g g.2 i }
#align pi.complete_lattice Pi.completeLattice

theorem Sup_apply {α : Type _} {β : α → Type _} [∀ i, SupSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    (sup s) a = ⨆ f : s, (f : ∀ a, β a) a :=
  rfl
#align Sup_apply Sup_apply

theorem Inf_apply {α : Type _} {β : α → Type _} [∀ i, InfSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    inf s a = ⨅ f : s, (f : ∀ a, β a) a :=
  rfl
#align Inf_apply Inf_apply

@[simp]
theorem supᵢ_apply {α : Type _} {β : α → Type _} {ι : Sort _} [∀ i, SupSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨆ i, f i) a = ⨆ i, f i a := by
  rw [supᵢ, Sup_apply, supᵢ, supᵢ, ← image_eq_range (fun f : ∀ i, β i => f a) (range f), ←
    range_comp]
#align supᵢ_apply supᵢ_apply

@[simp]
theorem infᵢ_apply {α : Type _} {β : α → Type _} {ι : Sort _} [∀ i, InfSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨅ i, f i) a = ⨅ i, f i a :=
  @supᵢ_apply α (fun i => (β i)ᵒᵈ) _ _ _ _
#align infᵢ_apply infᵢ_apply

theorem unary_relation_Sup_iff {α : Type _} (s : Set (α → Prop)) {a : α} :
    sup s a ↔ ∃ r : α → Prop, r ∈ s ∧ r a := by
  unfold Sup
  simp [← eq_iff_iff]
#align unary_relation_Sup_iff unary_relation_Sup_iff

theorem unary_relation_Inf_iff {α : Type _} (s : Set (α → Prop)) {a : α} :
    inf s a ↔ ∀ r : α → Prop, r ∈ s → r a := by
  unfold Inf
  simp [← eq_iff_iff]
#align unary_relation_Inf_iff unary_relation_Inf_iff

theorem binary_relation_Sup_iff {α β : Type _} (s : Set (α → β → Prop)) {a : α} {b : β} :
    sup s a b ↔ ∃ r : α → β → Prop, r ∈ s ∧ r a b := by
  unfold Sup
  simp [← eq_iff_iff]
#align binary_relation_Sup_iff binary_relation_Sup_iff

theorem binary_relation_Inf_iff {α β : Type _} (s : Set (α → β → Prop)) {a : α} {b : β} :
    inf s a b ↔ ∀ r : α → β → Prop, r ∈ s → r a b := by
  unfold Inf
  simp [← eq_iff_iff]
#align binary_relation_Inf_iff binary_relation_Inf_iff

section CompleteLattice

variable [Preorder α] [CompleteLattice β]

theorem monotone_Sup_of_monotone {s : Set (α → β)} (m_s : ∀ f ∈ s, Monotone f) : Monotone (sup s) :=
  fun x y h => supᵢ_mono fun f => m_s f f.2 h
#align monotone_Sup_of_monotone monotone_Sup_of_monotone

theorem monotone_Inf_of_monotone {s : Set (α → β)} (m_s : ∀ f ∈ s, Monotone f) : Monotone (inf s) :=
  fun x y h => infᵢ_mono fun f => m_s f f.2 h
#align monotone_Inf_of_monotone monotone_Inf_of_monotone

end CompleteLattice

namespace Prod

variable (α β)

instance [SupSet α] [SupSet β] : SupSet (α × β) :=
  ⟨fun s => (sup (Prod.fst '' s), sup (Prod.snd '' s))⟩

instance [InfSet α] [InfSet β] : InfSet (α × β) :=
  ⟨fun s => (inf (Prod.fst '' s), inf (Prod.snd '' s))⟩

instance [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) :=
  { Prod.lattice α β, Prod.boundedOrder α β, Prod.SupSet α β, Prod.InfSet α β with
    le_Sup := fun s p hab => ⟨le_Sup <| mem_image_of_mem _ hab, le_Sup <| mem_image_of_mem _ hab⟩
    Sup_le := fun s p h =>
      ⟨Sup_le <| ball_image_of_ball fun p hp => (h p hp).1,
        Sup_le <| ball_image_of_ball fun p hp => (h p hp).2⟩
    Inf_le := fun s p hab => ⟨Inf_le <| mem_image_of_mem _ hab, Inf_le <| mem_image_of_mem _ hab⟩
    le_Inf := fun s p h =>
      ⟨le_Inf <| ball_image_of_ball fun p hp => (h p hp).1,
        le_Inf <| ball_image_of_ball fun p hp => (h p hp).2⟩ }

end Prod

section CompleteLattice

variable [CompleteLattice α] {a : α} {s : Set α}

/-- This is a weaker version of `sup_Inf_eq` -/
theorem sup_Inf_le_infᵢ_sup : a ⊔ inf s ≤ ⨅ b ∈ s, a ⊔ b :=
  le_infᵢ₂ fun i h => sup_le_sup_left (Inf_le h) _
#align sup_Inf_le_infᵢ_sup sup_Inf_le_infᵢ_sup

/-- This is a weaker version of `inf_Sup_eq` -/
theorem supᵢ_inf_le_inf_Sup : (⨆ b ∈ s, a ⊓ b) ≤ a ⊓ sup s :=
  @sup_Inf_le_infᵢ_sup αᵒᵈ _ _ _
#align supᵢ_inf_le_inf_Sup supᵢ_inf_le_inf_Sup

/-- This is a weaker version of `Inf_sup_eq` -/
theorem Inf_sup_le_infᵢ_sup : inf s ⊔ a ≤ ⨅ b ∈ s, b ⊔ a :=
  le_infᵢ₂ fun i h => sup_le_sup_right (Inf_le h) _
#align Inf_sup_le_infᵢ_sup Inf_sup_le_infᵢ_sup

/-- This is a weaker version of `Sup_inf_eq` -/
theorem supᵢ_inf_le_Sup_inf : (⨆ b ∈ s, b ⊓ a) ≤ sup s ⊓ a :=
  @Inf_sup_le_infᵢ_sup αᵒᵈ _ _ _
#align supᵢ_inf_le_Sup_inf supᵢ_inf_le_Sup_inf

theorem le_supᵢ_inf_supᵢ (f g : ι → α) : (⨆ i, f i ⊓ g i) ≤ (⨆ i, f i) ⊓ ⨆ i, g i :=
  le_inf (supᵢ_mono fun i => inf_le_left) (supᵢ_mono fun i => inf_le_right)
#align le_supᵢ_inf_supᵢ le_supᵢ_inf_supᵢ

theorem infᵢ_sup_infᵢ_le (f g : ι → α) : ((⨅ i, f i) ⊔ ⨅ i, g i) ≤ ⨅ i, f i ⊔ g i :=
  @le_supᵢ_inf_supᵢ αᵒᵈ ι _ f g
#align infᵢ_sup_infᵢ_le infᵢ_sup_infᵢ_le

theorem disjoint_Sup_left {a : Set α} {b : α} (d : Disjoint (sup a) b) {i} (hi : i ∈ a) :
    Disjoint i b :=
  disjoint_iff_inf_le.mpr (supᵢ₂_le_iff.1 (supᵢ_inf_le_Sup_inf.trans d.le_bot) i hi : _)
#align disjoint_Sup_left disjoint_Sup_left

theorem disjoint_Sup_right {a : Set α} {b : α} (d : Disjoint b (sup a)) {i} (hi : i ∈ a) :
    Disjoint b i :=
  disjoint_iff_inf_le.mpr (supᵢ₂_le_iff.mp (supᵢ_inf_le_inf_Sup.trans d.le_bot) i hi : _)
#align disjoint_Sup_right disjoint_Sup_right

end CompleteLattice

-- See note [reducible non-instances]
/-- Pullback a `complete_lattice` along an injection. -/
@[reducible]
protected def Function.Injective.completeLattice [SupSet α] [InfSet α] [SupSet α] [InfSet α] [Top α]
    [Bot α] [CompleteLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_Sup : ∀ s, f (sup s) = ⨆ a ∈ s, f a) (map_Inf : ∀ s, f (inf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteLattice α :=
  { -- we cannot use bounded_order.lift here as the `has_le` instance doesn't exist yet
        hf.Lattice
      f map_sup map_inf with
    sup := sup
    le_Sup := fun s a h => (le_supᵢ₂ a h).trans (map_Sup _).ge
    Sup_le := fun s a h => (map_Sup _).trans_le <| supᵢ₂_le h
    inf := inf
    Inf_le := fun s a h => (map_Inf _).trans_le <| infᵢ₂_le a h
    le_Inf := fun s a h => (le_infᵢ₂ h).trans (map_Inf _).ge
    top := ⊤
    le_top := fun a => (@le_top β _ _ _).trans map_top.ge
    bot := ⊥
    bot_le := fun a => map_bot.le.trans bot_le }
#align function.injective.complete_lattice Function.Injective.completeLattice
