/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Data.Bool.Set
import Mathlib.Data.Nat.Set
import Mathlib.Data.Set.Prod
import Mathlib.Data.ULift
import Mathlib.Order.Bounds.Basic
import Mathlib.Order.Hom.Set
import Mathlib.Order.SetNotation

#align_import order.complete_lattice from "leanprover-community/mathlib"@"5709b0d8725255e76f47debca6400c07b5c2d8e6"

/-!
# Theory of complete lattices

## Main definitions

* `sSup` and `sInf` are the supremum and the infimum of a set;
* `iSup (f : ι → α)` and `iInf (f : ι → α)` are indexed supremum and infimum of a function,
  defined as `sSup` and `sInf` of the range of this function;
* class `CompleteLattice`: a bounded lattice such that `sSup s` is always the least upper boundary
  of `s` and `sInf s` is always the greatest lower boundary of `s`;
* class `CompleteLinearOrder`: a linear ordered complete lattice.

## Naming conventions

In lemma names,
* `sSup` is called `sSup`
* `sInf` is called `sInf`
* `⨆ i, s i` is called `iSup`
* `⨅ i, s i` is called `iInf`
* `⨆ i j, s i j` is called `iSup₂`. This is an `iSup` inside an `iSup`.
* `⨅ i j, s i j` is called `iInf₂`. This is an `iInf` inside an `iInf`.
* `⨆ i ∈ s, t i` is called `biSup` for "bounded `iSup`". This is the special case of `iSup₂`
  where `j : i ∈ s`.
* `⨅ i ∈ s, t i` is called `biInf` for "bounded `iInf`". This is the special case of `iInf₂`
  where `j : i ∈ s`.

## Notation

* `⨆ i, f i` : `iSup f`, the supremum of the range of `f`;
* `⨅ i, f i` : `iInf f`, the infimum of the range of `f`.
-/

open Function OrderDual Set

variable {α β β₂ γ : Type*} {ι ι' : Sort*} {κ : ι → Sort*} {κ' : ι' → Sort*}

instance OrderDual.supSet (α) [InfSet α] : SupSet αᵒᵈ :=
  ⟨(sInf : Set α → α)⟩

instance OrderDual.infSet (α) [SupSet α] : InfSet αᵒᵈ :=
  ⟨(sSup : Set α → α)⟩

/-- Note that we rarely use `CompleteSemilatticeSup`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
class CompleteSemilatticeSup (α : Type*) extends PartialOrder α, SupSet α where
  /-- Any element of a set is less than the set supremum. -/
  le_sSup : ∀ s, ∀ a ∈ s, a ≤ sSup s
  /-- Any upper bound is more than the set supremum. -/
  sSup_le : ∀ s a, (∀ b ∈ s, b ≤ a) → sSup s ≤ a
#align complete_semilattice_Sup CompleteSemilatticeSup

section

variable [CompleteSemilatticeSup α] {s t : Set α} {a b : α}

theorem le_sSup : a ∈ s → a ≤ sSup s :=
  CompleteSemilatticeSup.le_sSup s a
#align le_Sup le_sSup

theorem sSup_le : (∀ b ∈ s, b ≤ a) → sSup s ≤ a :=
  CompleteSemilatticeSup.sSup_le s a
#align Sup_le sSup_le

theorem isLUB_sSup (s : Set α) : IsLUB s (sSup s) :=
  ⟨fun _ ↦ le_sSup, fun _ ↦ sSup_le⟩
#align is_lub_Sup isLUB_sSup

lemma isLUB_iff_sSup_eq : IsLUB s a ↔ sSup s = a :=
  ⟨(isLUB_sSup s).unique, by rintro rfl; exact isLUB_sSup _⟩

alias ⟨IsLUB.sSup_eq, _⟩ := isLUB_iff_sSup_eq
#align is_lub.Sup_eq IsLUB.sSup_eq

theorem le_sSup_of_le (hb : b ∈ s) (h : a ≤ b) : a ≤ sSup s :=
  le_trans h (le_sSup hb)
#align le_Sup_of_le le_sSup_of_le

@[gcongr]
theorem sSup_le_sSup (h : s ⊆ t) : sSup s ≤ sSup t :=
  (isLUB_sSup s).mono (isLUB_sSup t) h
#align Sup_le_Sup sSup_le_sSup

@[simp]
theorem sSup_le_iff : sSup s ≤ a ↔ ∀ b ∈ s, b ≤ a :=
  isLUB_le_iff (isLUB_sSup s)
#align Sup_le_iff sSup_le_iff

theorem le_sSup_iff : a ≤ sSup s ↔ ∀ b ∈ upperBounds s, a ≤ b :=
  ⟨fun h _ hb => le_trans h (sSup_le hb), fun hb => hb _ fun _ => le_sSup⟩
#align le_Sup_iff le_sSup_iff

theorem le_iSup_iff {s : ι → α} : a ≤ iSup s ↔ ∀ b, (∀ i, s i ≤ b) → a ≤ b := by
  simp [iSup, le_sSup_iff, upperBounds]
#align le_supr_iff le_iSup_iff

theorem sSup_le_sSup_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, x ≤ y) : sSup s ≤ sSup t :=
  le_sSup_iff.2 fun _ hb =>
    sSup_le fun a ha =>
      let ⟨_, hct, hac⟩ := h a ha
      hac.trans (hb hct)
#align Sup_le_Sup_of_forall_exists_le sSup_le_sSup_of_forall_exists_le

-- We will generalize this to conditionally complete lattices in `csSup_singleton`.
theorem sSup_singleton {a : α} : sSup {a} = a :=
  isLUB_singleton.sSup_eq
#align Sup_singleton sSup_singleton

end

/-- Note that we rarely use `CompleteSemilatticeInf`
(in fact, any such object is always a `CompleteLattice`, so it's usually best to start there).

Nevertheless it is sometimes a useful intermediate step in constructions.
-/
class CompleteSemilatticeInf (α : Type*) extends PartialOrder α, InfSet α where
  /-- Any element of a set is more than the set infimum. -/
  sInf_le : ∀ s, ∀ a ∈ s, sInf s ≤ a
  /-- Any lower bound is less than the set infimum. -/
  le_sInf : ∀ s a, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
#align complete_semilattice_Inf CompleteSemilatticeInf

section

variable [CompleteSemilatticeInf α] {s t : Set α} {a b : α}

theorem sInf_le : a ∈ s → sInf s ≤ a :=
  CompleteSemilatticeInf.sInf_le s a
#align Inf_le sInf_le

theorem le_sInf : (∀ b ∈ s, a ≤ b) → a ≤ sInf s :=
  CompleteSemilatticeInf.le_sInf s a
#align le_Inf le_sInf

theorem isGLB_sInf (s : Set α) : IsGLB s (sInf s) :=
  ⟨fun _ => sInf_le, fun _ => le_sInf⟩
#align is_glb_Inf isGLB_sInf

lemma isGLB_iff_sInf_eq : IsGLB s a ↔ sInf s = a :=
  ⟨(isGLB_sInf s).unique, by rintro rfl; exact isGLB_sInf _⟩

alias ⟨IsGLB.sInf_eq, _⟩ := isGLB_iff_sInf_eq
#align is_glb.Inf_eq IsGLB.sInf_eq

theorem sInf_le_of_le (hb : b ∈ s) (h : b ≤ a) : sInf s ≤ a :=
  le_trans (sInf_le hb) h
#align Inf_le_of_le sInf_le_of_le

@[gcongr]
theorem sInf_le_sInf (h : s ⊆ t) : sInf t ≤ sInf s :=
  (isGLB_sInf s).mono (isGLB_sInf t) h
#align Inf_le_Inf sInf_le_sInf

@[simp]
theorem le_sInf_iff : a ≤ sInf s ↔ ∀ b ∈ s, a ≤ b :=
  le_isGLB_iff (isGLB_sInf s)
#align le_Inf_iff le_sInf_iff

theorem sInf_le_iff : sInf s ≤ a ↔ ∀ b ∈ lowerBounds s, b ≤ a :=
  ⟨fun h _ hb => le_trans (le_sInf hb) h, fun hb => hb _ fun _ => sInf_le⟩
#align Inf_le_iff sInf_le_iff

theorem iInf_le_iff {s : ι → α} : iInf s ≤ a ↔ ∀ b, (∀ i, b ≤ s i) → b ≤ a := by
  simp [iInf, sInf_le_iff, lowerBounds]
#align infi_le_iff iInf_le_iff

theorem sInf_le_sInf_of_forall_exists_le (h : ∀ x ∈ s, ∃ y ∈ t, y ≤ x) : sInf t ≤ sInf s :=
  le_sInf fun x hx ↦ let ⟨_y, hyt, hyx⟩ := h x hx; sInf_le_of_le hyt hyx
#align Inf_le_Inf_of_forall_exists_le sInf_le_sInf_of_forall_exists_le

-- We will generalize this to conditionally complete lattices in `csInf_singleton`.
theorem sInf_singleton {a : α} : sInf {a} = a :=
  isGLB_singleton.sInf_eq
#align Inf_singleton sInf_singleton

end

/-- A complete lattice is a bounded lattice which has suprema and infima for every subset. -/
class CompleteLattice (α : Type*) extends Lattice α, CompleteSemilatticeSup α,
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
instance : CompleteLattice my_T where
  inf := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sSup, bot, top
  __ := completeLatticeOfInf my_T _
```
-/
def completeLatticeOfInf (α : Type*) [H1 : PartialOrder α] [H2 : InfSet α]
    (isGLB_sInf : ∀ s : Set α, IsGLB s (sInf s)) : CompleteLattice α where
  __ := H1; __ := H2
  bot := sInf univ
  bot_le x := (isGLB_sInf univ).1 trivial
  top := sInf ∅
  le_top a := (isGLB_sInf ∅).2 <| by simp
  sup a b := sInf { x : α | a ≤ x ∧ b ≤ x }
  inf a b := sInf {a, b}
  le_inf a b c hab hac := by
    apply (isGLB_sInf _).2
    simp [*]
  inf_le_right a b := (isGLB_sInf _).1 <| mem_insert_of_mem _ <| mem_singleton _
  inf_le_left a b := (isGLB_sInf _).1 <| mem_insert _ _
  sup_le a b c hac hbc := (isGLB_sInf _).1 <| by simp [*]
  le_sup_left a b := (isGLB_sInf _).2 fun x => And.left
  le_sup_right a b := (isGLB_sInf _).2 fun x => And.right
  le_sInf s a ha := (isGLB_sInf s).2 ha
  sInf_le s a ha := (isGLB_sInf s).1 ha
  sSup s := sInf (upperBounds s)
  le_sSup s a ha := (isGLB_sInf (upperBounds s)).2 fun b hb => hb ha
  sSup_le s a ha := (isGLB_sInf (upperBounds s)).1 ha
#align complete_lattice_of_Inf completeLatticeOfInf

/-- Any `CompleteSemilatticeInf` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfInf`.
-/
def completeLatticeOfCompleteSemilatticeInf (α : Type*) [CompleteSemilatticeInf α] :
    CompleteLattice α :=
  completeLatticeOfInf α fun s => isGLB_sInf s
#align complete_lattice_of_complete_semilattice_Inf completeLatticeOfCompleteSemilatticeInf

/-- Create a `CompleteLattice` from a `PartialOrder` and `SupSet`
that returns the least upper bound of a set. Usually this constructor provides
poor definitional equalities.  If other fields are known explicitly, they should be
provided; for example, if `inf` is known explicitly, construct the `CompleteLattice`
instance as
```
instance : CompleteLattice my_T where
  inf := better_inf
  le_inf := ...
  inf_le_right := ...
  inf_le_left := ...
  -- don't care to fix sup, sInf, bot, top
  __ := completeLatticeOfSup my_T _
```
-/
def completeLatticeOfSup (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α]
    (isLUB_sSup : ∀ s : Set α, IsLUB s (sSup s)) : CompleteLattice α where
  __ := H1; __ := H2
  top := sSup univ
  le_top x := (isLUB_sSup univ).1 trivial
  bot := sSup ∅
  bot_le x := (isLUB_sSup ∅).2 <| by simp
  sup a b := sSup {a, b}
  sup_le a b c hac hbc := (isLUB_sSup _).2 (by simp [*])
  le_sup_left a b := (isLUB_sSup _).1 <| mem_insert _ _
  le_sup_right a b := (isLUB_sSup _).1 <| mem_insert_of_mem _ <| mem_singleton _
  inf a b := sSup { x | x ≤ a ∧ x ≤ b }
  le_inf a b c hab hac := (isLUB_sSup _).1 <| by simp [*]
  inf_le_left a b := (isLUB_sSup _).2 fun x => And.left
  inf_le_right a b := (isLUB_sSup _).2 fun x => And.right
  sInf s := sSup (lowerBounds s)
  sSup_le s a ha := (isLUB_sSup s).2 ha
  le_sSup s a ha := (isLUB_sSup s).1 ha
  sInf_le s a ha := (isLUB_sSup (lowerBounds s)).2 fun b hb => hb ha
  le_sInf s a ha := (isLUB_sSup (lowerBounds s)).1 ha
#align complete_lattice_of_Sup completeLatticeOfSup

/-- Any `CompleteSemilatticeSup` is in fact a `CompleteLattice`.

Note that this construction has bad definitional properties:
see the doc-string on `completeLatticeOfSup`.
-/
def completeLatticeOfCompleteSemilatticeSup (α : Type*) [CompleteSemilatticeSup α] :
    CompleteLattice α :=
  completeLatticeOfSup α fun s => isLUB_sSup s
#align complete_lattice_of_complete_semilattice_Sup completeLatticeOfCompleteSemilatticeSup

-- Porting note: as we cannot rename fields while extending,
-- `CompleteLinearOrder` does not directly extend `LinearOrder`.
-- Instead we add the fields by hand, and write a manual instance.

/-- A complete linear order is a linear order whose lattice structure is complete. -/
class CompleteLinearOrder (α : Type*) extends CompleteLattice α where
  /-- A linear order is total. -/
  le_total (a b : α) : a ≤ b ∨ b ≤ a
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableLE : DecidableRel (· ≤ · : α → α → Prop)
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableEq : DecidableEq α := @decidableEqOfDecidableLE _ _ decidableLE
  /-- In a linearly ordered type, we assume the order relations are all decidable. -/
  decidableLT : DecidableRel (· < · : α → α → Prop) :=
    @decidableLTOfDecidableLE _ _ decidableLE
#align complete_linear_order CompleteLinearOrder

instance CompleteLinearOrder.toLinearOrder [i : CompleteLinearOrder α] : LinearOrder α where
  __ := i
  min := Inf.inf
  max := Sup.sup
  min_def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]
  max_def a b := by
    split_ifs with h
    · simp [h]
    · simp [(CompleteLinearOrder.le_total a b).resolve_left h]

namespace OrderDual

instance instCompleteLattice [CompleteLattice α] : CompleteLattice αᵒᵈ where
  __ := instBoundedOrder α
  le_sSup := @CompleteLattice.sInf_le α _
  sSup_le := @CompleteLattice.le_sInf α _
  sInf_le := @CompleteLattice.le_sSup α _
  le_sInf := @CompleteLattice.sSup_le α _

instance instCompleteLinearOrder [CompleteLinearOrder α] : CompleteLinearOrder αᵒᵈ where
  __ := instCompleteLattice
  __ := instLinearOrder α

end OrderDual

open OrderDual

section

variable [CompleteLattice α] {s t : Set α} {a b : α}

@[simp]
theorem toDual_sSup (s : Set α) : toDual (sSup s) = sInf (ofDual ⁻¹' s) :=
  rfl
#align to_dual_Sup toDual_sSup

@[simp]
theorem toDual_sInf (s : Set α) : toDual (sInf s) = sSup (ofDual ⁻¹' s) :=
  rfl
#align to_dual_Inf toDual_sInf

@[simp]
theorem ofDual_sSup (s : Set αᵒᵈ) : ofDual (sSup s) = sInf (toDual ⁻¹' s) :=
  rfl
#align of_dual_Sup ofDual_sSup

@[simp]
theorem ofDual_sInf (s : Set αᵒᵈ) : ofDual (sInf s) = sSup (toDual ⁻¹' s) :=
  rfl
#align of_dual_Inf ofDual_sInf

@[simp]
theorem toDual_iSup (f : ι → α) : toDual (⨆ i, f i) = ⨅ i, toDual (f i) :=
  rfl
#align to_dual_supr toDual_iSup

@[simp]
theorem toDual_iInf (f : ι → α) : toDual (⨅ i, f i) = ⨆ i, toDual (f i) :=
  rfl
#align to_dual_infi toDual_iInf

@[simp]
theorem ofDual_iSup (f : ι → αᵒᵈ) : ofDual (⨆ i, f i) = ⨅ i, ofDual (f i) :=
  rfl
#align of_dual_supr ofDual_iSup

@[simp]
theorem ofDual_iInf (f : ι → αᵒᵈ) : ofDual (⨅ i, f i) = ⨆ i, ofDual (f i) :=
  rfl
#align of_dual_infi ofDual_iInf

theorem sInf_le_sSup (hs : s.Nonempty) : sInf s ≤ sSup s :=
  isGLB_le_isLUB (isGLB_sInf s) (isLUB_sSup s) hs
#align Inf_le_Sup sInf_le_sSup

theorem sSup_union {s t : Set α} : sSup (s ∪ t) = sSup s ⊔ sSup t :=
  ((isLUB_sSup s).union (isLUB_sSup t)).sSup_eq
#align Sup_union sSup_union

theorem sInf_union {s t : Set α} : sInf (s ∪ t) = sInf s ⊓ sInf t :=
  ((isGLB_sInf s).union (isGLB_sInf t)).sInf_eq
#align Inf_union sInf_union

theorem sSup_inter_le {s t : Set α} : sSup (s ∩ t) ≤ sSup s ⊓ sSup t :=
  sSup_le fun _ hb => le_inf (le_sSup hb.1) (le_sSup hb.2)
#align Sup_inter_le sSup_inter_le

theorem le_sInf_inter {s t : Set α} : sInf s ⊔ sInf t ≤ sInf (s ∩ t) :=
  @sSup_inter_le αᵒᵈ _ _ _
#align le_Inf_inter le_sInf_inter

@[simp]
theorem sSup_empty : sSup ∅ = (⊥ : α) :=
  (@isLUB_empty α _ _).sSup_eq
#align Sup_empty sSup_empty

@[simp]
theorem sInf_empty : sInf ∅ = (⊤ : α) :=
  (@isGLB_empty α _ _).sInf_eq
#align Inf_empty sInf_empty

@[simp]
theorem sSup_univ : sSup univ = (⊤ : α) :=
  (@isLUB_univ α _ _).sSup_eq
#align Sup_univ sSup_univ

@[simp]
theorem sInf_univ : sInf univ = (⊥ : α) :=
  (@isGLB_univ α _ _).sInf_eq
#align Inf_univ sInf_univ

-- TODO(Jeremy): get this automatically
@[simp]
theorem sSup_insert {a : α} {s : Set α} : sSup (insert a s) = a ⊔ sSup s :=
  ((isLUB_sSup s).insert a).sSup_eq
#align Sup_insert sSup_insert

@[simp]
theorem sInf_insert {a : α} {s : Set α} : sInf (insert a s) = a ⊓ sInf s :=
  ((isGLB_sInf s).insert a).sInf_eq
#align Inf_insert sInf_insert

theorem sSup_le_sSup_of_subset_insert_bot (h : s ⊆ insert ⊥ t) : sSup s ≤ sSup t :=
  (sSup_le_sSup h).trans_eq (sSup_insert.trans (bot_sup_eq _))
#align Sup_le_Sup_of_subset_insert_bot sSup_le_sSup_of_subset_insert_bot

theorem sInf_le_sInf_of_subset_insert_top (h : s ⊆ insert ⊤ t) : sInf t ≤ sInf s :=
  (sInf_le_sInf h).trans_eq' (sInf_insert.trans (top_inf_eq _)).symm
#align Inf_le_Inf_of_subset_insert_top sInf_le_sInf_of_subset_insert_top

@[simp]
theorem sSup_diff_singleton_bot (s : Set α) : sSup (s \ {⊥}) = sSup s :=
  (sSup_le_sSup (diff_subset _ _)).antisymm <|
    sSup_le_sSup_of_subset_insert_bot <| subset_insert_diff_singleton _ _
#align Sup_diff_singleton_bot sSup_diff_singleton_bot

@[simp]
theorem sInf_diff_singleton_top (s : Set α) : sInf (s \ {⊤}) = sInf s :=
  @sSup_diff_singleton_bot αᵒᵈ _ s
#align Inf_diff_singleton_top sInf_diff_singleton_top

theorem sSup_pair {a b : α} : sSup {a, b} = a ⊔ b :=
  (@isLUB_pair α _ a b).sSup_eq
#align Sup_pair sSup_pair

theorem sInf_pair {a b : α} : sInf {a, b} = a ⊓ b :=
  (@isGLB_pair α _ a b).sInf_eq
#align Inf_pair sInf_pair

@[simp]
theorem sSup_eq_bot : sSup s = ⊥ ↔ ∀ a ∈ s, a = ⊥ :=
  ⟨fun h _ ha => bot_unique <| h ▸ le_sSup ha, fun h =>
    bot_unique <| sSup_le fun a ha => le_bot_iff.2 <| h a ha⟩
#align Sup_eq_bot sSup_eq_bot

@[simp]
theorem sInf_eq_top : sInf s = ⊤ ↔ ∀ a ∈ s, a = ⊤ :=
  @sSup_eq_bot αᵒᵈ _ _
#align Inf_eq_top sInf_eq_top

theorem eq_singleton_bot_of_sSup_eq_bot_of_nonempty {s : Set α} (h_sup : sSup s = ⊥)
    (hne : s.Nonempty) : s = {⊥} := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  rw [sSup_eq_bot] at h_sup
  exact ⟨hne, h_sup⟩
#align eq_singleton_bot_of_Sup_eq_bot_of_nonempty eq_singleton_bot_of_sSup_eq_bot_of_nonempty

theorem eq_singleton_top_of_sInf_eq_top_of_nonempty : sInf s = ⊤ → s.Nonempty → s = {⊤} :=
  @eq_singleton_bot_of_sSup_eq_bot_of_nonempty αᵒᵈ _ _
#align eq_singleton_top_of_Inf_eq_top_of_nonempty eq_singleton_top_of_sInf_eq_top_of_nonempty

/-- Introduction rule to prove that `b` is the supremum of `s`: it suffices to check that `b`
is larger than all elements of `s`, and that this is not the case of any `w < b`.
See `csSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem sSup_eq_of_forall_le_of_forall_lt_exists_gt (h₁ : ∀ a ∈ s, a ≤ b)
    (h₂ : ∀ w, w < b → ∃ a ∈ s, w < a) : sSup s = b :=
  (sSup_le h₁).eq_of_not_lt fun h =>
    let ⟨_, ha, ha'⟩ := h₂ _ h
    ((le_sSup ha).trans_lt ha').false
#align Sup_eq_of_forall_le_of_forall_lt_exists_gt sSup_eq_of_forall_le_of_forall_lt_exists_gt

/-- Introduction rule to prove that `b` is the infimum of `s`: it suffices to check that `b`
is smaller than all elements of `s`, and that this is not the case of any `w > b`.
See `csInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem sInf_eq_of_forall_ge_of_forall_gt_exists_lt :
    (∀ a ∈ s, b ≤ a) → (∀ w, b < w → ∃ a ∈ s, a < w) → sInf s = b :=
  @sSup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _
#align Inf_eq_of_forall_ge_of_forall_gt_exists_lt sInf_eq_of_forall_ge_of_forall_gt_exists_lt

end

section CompleteLinearOrder

variable [CompleteLinearOrder α] {s t : Set α} {a b : α}

theorem lt_sSup_iff : b < sSup s ↔ ∃ a ∈ s, b < a :=
  lt_isLUB_iff <| isLUB_sSup s
#align lt_Sup_iff lt_sSup_iff

theorem sInf_lt_iff : sInf s < b ↔ ∃ a ∈ s, a < b :=
  isGLB_lt_iff <| isGLB_sInf s
#align Inf_lt_iff sInf_lt_iff

theorem sSup_eq_top : sSup s = ⊤ ↔ ∀ b < ⊤, ∃ a ∈ s, b < a :=
  ⟨fun h _ hb => lt_sSup_iff.1 <| hb.trans_eq h.symm, fun h =>
    top_unique <|
      le_of_not_gt fun h' =>
        let ⟨_, ha, h⟩ := h _ h'
        (h.trans_le <| le_sSup ha).false⟩
#align Sup_eq_top sSup_eq_top

theorem sInf_eq_bot : sInf s = ⊥ ↔ ∀ b > ⊥, ∃ a ∈ s, a < b :=
  @sSup_eq_top αᵒᵈ _ _
#align Inf_eq_bot sInf_eq_bot

theorem lt_iSup_iff {f : ι → α} : a < iSup f ↔ ∃ i, a < f i :=
  lt_sSup_iff.trans exists_range_iff
#align lt_supr_iff lt_iSup_iff

theorem iInf_lt_iff {f : ι → α} : iInf f < a ↔ ∃ i, f i < a :=
  sInf_lt_iff.trans exists_range_iff
#align infi_lt_iff iInf_lt_iff

end CompleteLinearOrder

/-
### iSup & iInf
-/
section SupSet

variable [SupSet α] {f g : ι → α}

theorem sSup_range : sSup (range f) = iSup f :=
  rfl
#align Sup_range sSup_range

theorem sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α) := by rw [iSup, Subtype.range_coe]
#align Sup_eq_supr' sSup_eq_iSup'

theorem iSup_congr (h : ∀ i, f i = g i) : ⨆ i, f i = ⨆ i, g i :=
  congr_arg _ <| funext h
#align supr_congr iSup_congr

theorem biSup_congr {p : ι → Prop} (h : ∀ i, p i → f i = g i) :
    ⨆ (i) (_ : p i), f i = ⨆ (i) (_ : p i), g i :=
  iSup_congr fun i ↦ iSup_congr (h i)

theorem biSup_congr' {p : ι → Prop} {f g : (i : ι) → p i → α}
    (h : ∀ i (hi : p i), f i hi = g i hi) :
    ⨆ i, ⨆ (hi : p i), f i hi = ⨆ i, ⨆ (hi : p i), g i hi := by
  congr; ext i; congr; ext hi; exact h i hi

theorem Function.Surjective.iSup_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    ⨆ x, g (f x) = ⨆ y, g y := by
  simp only [iSup.eq_1]
  congr
  exact hf.range_comp g
#align function.surjective.supr_comp Function.Surjective.iSup_comp

theorem Equiv.iSup_comp {g : ι' → α} (e : ι ≃ ι') : ⨆ x, g (e x) = ⨆ y, g y :=
  e.surjective.iSup_comp _
#align equiv.supr_comp Equiv.iSup_comp

protected theorem Function.Surjective.iSup_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : ⨆ x, f x = ⨆ y, g y := by
  convert h1.iSup_comp g
  exact (h2 _).symm
#align function.surjective.supr_congr Function.Surjective.iSup_congr

protected theorem Equiv.iSup_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    ⨆ x, f x = ⨆ y, g y :=
  e.surjective.iSup_congr _ h
#align equiv.supr_congr Equiv.iSup_congr

@[congr]
theorem iSup_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂ := by
  obtain rfl := propext pq
  congr with x
  apply f
#align supr_congr_Prop iSup_congr_Prop

theorem iSup_plift_up (f : PLift ι → α) : ⨆ i, f (PLift.up i) = ⨆ i, f i :=
  (PLift.up_surjective.iSup_congr _) fun _ => rfl
#align supr_plift_up iSup_plift_up

theorem iSup_plift_down (f : ι → α) : ⨆ i, f (PLift.down i) = ⨆ i, f i :=
  (PLift.down_surjective.iSup_congr _) fun _ => rfl
#align supr_plift_down iSup_plift_down

theorem iSup_range' (g : β → α) (f : ι → β) : ⨆ b : range f, g b = ⨆ i, g (f i) := by
  rw [iSup, iSup, ← image_eq_range, ← range_comp]
  rfl
#align supr_range' iSup_range'

theorem sSup_image' {s : Set β} {f : β → α} : sSup (f '' s) = ⨆ a : s, f a := by
  rw [iSup, image_eq_range]
#align Sup_image' sSup_image'

end SupSet

section InfSet

variable [InfSet α] {f g : ι → α}

theorem sInf_range : sInf (range f) = iInf f :=
  rfl
#align Inf_range sInf_range

theorem sInf_eq_iInf' (s : Set α) : sInf s = ⨅ a : s, (a : α) :=
  @sSup_eq_iSup' αᵒᵈ _ _
#align Inf_eq_infi' sInf_eq_iInf'

theorem iInf_congr (h : ∀ i, f i = g i) : ⨅ i, f i = ⨅ i, g i :=
  congr_arg _ <| funext h
#align infi_congr iInf_congr

theorem biInf_congr {p : ι → Prop} (h : ∀ i, p i → f i = g i) :
    ⨅ (i) (_ : p i), f i = ⨅ (i) (_ : p i), g i :=
  biSup_congr (α := αᵒᵈ) h

theorem biInf_congr' {p : ι → Prop} {f g : (i : ι) → p i → α}
    (h : ∀ i (hi : p i), f i hi = g i hi) :
    ⨅ i, ⨅ (hi : p i), f i hi = ⨅ i, ⨅ (hi : p i), g i hi := by
  congr; ext i; congr; ext hi; exact h i hi

theorem Function.Surjective.iInf_comp {f : ι → ι'} (hf : Surjective f) (g : ι' → α) :
    ⨅ x, g (f x) = ⨅ y, g y :=
  @Function.Surjective.iSup_comp αᵒᵈ _ _ _ f hf g
#align function.surjective.infi_comp Function.Surjective.iInf_comp

theorem Equiv.iInf_comp {g : ι' → α} (e : ι ≃ ι') : ⨅ x, g (e x) = ⨅ y, g y :=
  @Equiv.iSup_comp αᵒᵈ _ _ _ _ e
#align equiv.infi_comp Equiv.iInf_comp

protected theorem Function.Surjective.iInf_congr {g : ι' → α} (h : ι → ι') (h1 : Surjective h)
    (h2 : ∀ x, g (h x) = f x) : ⨅ x, f x = ⨅ y, g y :=
  @Function.Surjective.iSup_congr αᵒᵈ _ _ _ _ _ h h1 h2
#align function.surjective.infi_congr Function.Surjective.iInf_congr

protected theorem Equiv.iInf_congr {g : ι' → α} (e : ι ≃ ι') (h : ∀ x, g (e x) = f x) :
    ⨅ x, f x = ⨅ y, g y :=
  @Equiv.iSup_congr αᵒᵈ _ _ _ _ _ e h
#align equiv.infi_congr Equiv.iInf_congr

@[congr]
theorem iInf_congr_Prop {p q : Prop} {f₁ : p → α} {f₂ : q → α} (pq : p ↔ q)
    (f : ∀ x, f₁ (pq.mpr x) = f₂ x) : iInf f₁ = iInf f₂ :=
  @iSup_congr_Prop αᵒᵈ _ p q f₁ f₂ pq f
#align infi_congr_Prop iInf_congr_Prop

theorem iInf_plift_up (f : PLift ι → α) : ⨅ i, f (PLift.up i) = ⨅ i, f i :=
  (PLift.up_surjective.iInf_congr _) fun _ => rfl
#align infi_plift_up iInf_plift_up

theorem iInf_plift_down (f : ι → α) : ⨅ i, f (PLift.down i) = ⨅ i, f i :=
  (PLift.down_surjective.iInf_congr _) fun _ => rfl
#align infi_plift_down iInf_plift_down

theorem iInf_range' (g : β → α) (f : ι → β) : ⨅ b : range f, g b = ⨅ i, g (f i) :=
  @iSup_range' αᵒᵈ _ _ _ _ _
#align infi_range' iInf_range'

theorem sInf_image' {s : Set β} {f : β → α} : sInf (f '' s) = ⨅ a : s, f a :=
  @sSup_image' αᵒᵈ _ _ _ _
#align Inf_image' sInf_image'

end InfSet

section

variable [CompleteLattice α] {f g s t : ι → α} {a b : α}

theorem le_iSup (f : ι → α) (i : ι) : f i ≤ iSup f :=
  le_sSup ⟨i, rfl⟩
#align le_supr le_iSup

theorem iInf_le (f : ι → α) (i : ι) : iInf f ≤ f i :=
  sInf_le ⟨i, rfl⟩
#align infi_le iInf_le

theorem le_iSup' (f : ι → α) (i : ι) : f i ≤ iSup f :=
  le_sSup ⟨i, rfl⟩
#align le_supr' le_iSup'

theorem iInf_le' (f : ι → α) (i : ι) : iInf f ≤ f i :=
  sInf_le ⟨i, rfl⟩
#align infi_le' iInf_le'

theorem isLUB_iSup : IsLUB (range f) (⨆ j, f j) :=
  isLUB_sSup _
#align is_lub_supr isLUB_iSup

theorem isGLB_iInf : IsGLB (range f) (⨅ j, f j) :=
  isGLB_sInf _
#align is_glb_infi isGLB_iInf

theorem IsLUB.iSup_eq (h : IsLUB (range f) a) : ⨆ j, f j = a :=
  h.sSup_eq
#align is_lub.supr_eq IsLUB.iSup_eq

theorem IsGLB.iInf_eq (h : IsGLB (range f) a) : ⨅ j, f j = a :=
  h.sInf_eq
#align is_glb.infi_eq IsGLB.iInf_eq

theorem le_iSup_of_le (i : ι) (h : a ≤ f i) : a ≤ iSup f :=
  h.trans <| le_iSup _ i
#align le_supr_of_le le_iSup_of_le

theorem iInf_le_of_le (i : ι) (h : f i ≤ a) : iInf f ≤ a :=
  (iInf_le _ i).trans h
#align infi_le_of_le iInf_le_of_le

theorem le_iSup₂ {f : ∀ i, κ i → α} (i : ι) (j : κ i) : f i j ≤ ⨆ (i) (j), f i j :=
  le_iSup_of_le i <| le_iSup (f i) j
#align le_supr₂ le_iSup₂

theorem iInf₂_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) : ⨅ (i) (j), f i j ≤ f i j :=
  iInf_le_of_le i <| iInf_le (f i) j
#align infi₂_le iInf₂_le

theorem le_iSup₂_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : a ≤ f i j) :
    a ≤ ⨆ (i) (j), f i j :=
  h.trans <| le_iSup₂ i j
#align le_supr₂_of_le le_iSup₂_of_le

theorem iInf₂_le_of_le {f : ∀ i, κ i → α} (i : ι) (j : κ i) (h : f i j ≤ a) :
    ⨅ (i) (j), f i j ≤ a :=
  (iInf₂_le i j).trans h
#align infi₂_le_of_le iInf₂_le_of_le

theorem iSup_le (h : ∀ i, f i ≤ a) : iSup f ≤ a :=
  sSup_le fun _ ⟨i, Eq⟩ => Eq ▸ h i
#align supr_le iSup_le

theorem le_iInf (h : ∀ i, a ≤ f i) : a ≤ iInf f :=
  le_sInf fun _ ⟨i, Eq⟩ => Eq ▸ h i
#align le_infi le_iInf

theorem iSup₂_le {f : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ a) : ⨆ (i) (j), f i j ≤ a :=
  iSup_le fun i => iSup_le <| h i
#align supr₂_le iSup₂_le

theorem le_iInf₂ {f : ∀ i, κ i → α} (h : ∀ i j, a ≤ f i j) : a ≤ ⨅ (i) (j), f i j :=
  le_iInf fun i => le_iInf <| h i
#align le_infi₂ le_iInf₂

theorem iSup₂_le_iSup (κ : ι → Sort*) (f : ι → α) : ⨆ (i) (_ : κ i), f i ≤ ⨆ i, f i :=
  iSup₂_le fun i _ => le_iSup f i
#align supr₂_le_supr iSup₂_le_iSup

theorem iInf_le_iInf₂ (κ : ι → Sort*) (f : ι → α) : ⨅ i, f i ≤ ⨅ (i) (_ : κ i), f i :=
  le_iInf₂ fun i _ => iInf_le f i
#align infi_le_infi₂ iInf_le_iInf₂

@[gcongr]
theorem iSup_mono (h : ∀ i, f i ≤ g i) : iSup f ≤ iSup g :=
  iSup_le fun i => le_iSup_of_le i <| h i
#align supr_mono iSup_mono

@[gcongr]
theorem iInf_mono (h : ∀ i, f i ≤ g i) : iInf f ≤ iInf g :=
  le_iInf fun i => iInf_le_of_le i <| h i
#align infi_mono iInf_mono

theorem iSup₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    ⨆ (i) (j), f i j ≤ ⨆ (i) (j), g i j :=
  iSup_mono fun i => iSup_mono <| h i
#align supr₂_mono iSup₂_mono

theorem iInf₂_mono {f g : ∀ i, κ i → α} (h : ∀ i j, f i j ≤ g i j) :
    ⨅ (i) (j), f i j ≤ ⨅ (i) (j), g i j :=
  iInf_mono fun i => iInf_mono <| h i
#align infi₂_mono iInf₂_mono

theorem iSup_mono' {g : ι' → α} (h : ∀ i, ∃ i', f i ≤ g i') : iSup f ≤ iSup g :=
  iSup_le fun i => Exists.elim (h i) le_iSup_of_le
#align supr_mono' iSup_mono'

theorem iInf_mono' {g : ι' → α} (h : ∀ i', ∃ i, f i ≤ g i') : iInf f ≤ iInf g :=
  le_iInf fun i' => Exists.elim (h i') iInf_le_of_le
#align infi_mono' iInf_mono'

theorem iSup₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i j ≤ g i' j') :
    ⨆ (i) (j), f i j ≤ ⨆ (i) (j), g i j :=
  iSup₂_le fun i j =>
    let ⟨i', j', h⟩ := h i j
    le_iSup₂_of_le i' j' h
#align supr₂_mono' iSup₂_mono'

theorem iInf₂_mono' {f : ∀ i, κ i → α} {g : ∀ i', κ' i' → α} (h : ∀ i j, ∃ i' j', f i' j' ≤ g i j) :
    ⨅ (i) (j), f i j ≤ ⨅ (i) (j), g i j :=
  le_iInf₂ fun i j =>
    let ⟨i', j', h⟩ := h i j
    iInf₂_le_of_le i' j' h
#align infi₂_mono' iInf₂_mono'

theorem iSup_const_mono (h : ι → ι') : ⨆ _ : ι, a ≤ ⨆ _ : ι', a :=
  iSup_le <| le_iSup _ ∘ h
#align supr_const_mono iSup_const_mono

theorem iInf_const_mono (h : ι' → ι) : ⨅ _ : ι, a ≤ ⨅ _ : ι', a :=
  le_iInf <| iInf_le _ ∘ h
#align infi_const_mono iInf_const_mono

theorem iSup_iInf_le_iInf_iSup (f : ι → ι' → α) : ⨆ i, ⨅ j, f i j ≤ ⨅ j, ⨆ i, f i j :=
  iSup_le fun i => iInf_mono fun j => le_iSup (fun i => f i j) i
#align supr_infi_le_infi_supr iSup_iInf_le_iInf_iSup

theorem biSup_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    ⨆ (i) (_ : p i), f i ≤ ⨆ (i) (_ : q i), f i :=
  iSup_mono fun i => iSup_const_mono (hpq i)
#align bsupr_mono biSup_mono

theorem biInf_mono {p q : ι → Prop} (hpq : ∀ i, p i → q i) :
    ⨅ (i) (_ : q i), f i ≤ ⨅ (i) (_ : p i), f i :=
  iInf_mono fun i => iInf_const_mono (hpq i)
#align binfi_mono biInf_mono

@[simp]
theorem iSup_le_iff : iSup f ≤ a ↔ ∀ i, f i ≤ a :=
  (isLUB_le_iff isLUB_iSup).trans forall_mem_range
#align supr_le_iff iSup_le_iff

@[simp]
theorem le_iInf_iff : a ≤ iInf f ↔ ∀ i, a ≤ f i :=
  (le_isGLB_iff isGLB_iInf).trans forall_mem_range
#align le_infi_iff le_iInf_iff

theorem iSup₂_le_iff {f : ∀ i, κ i → α} : ⨆ (i) (j), f i j ≤ a ↔ ∀ i j, f i j ≤ a := by
  simp_rw [iSup_le_iff]
#align supr₂_le_iff iSup₂_le_iff

theorem le_iInf₂_iff {f : ∀ i, κ i → α} : (a ≤ ⨅ (i) (j), f i j) ↔ ∀ i j, a ≤ f i j := by
  simp_rw [le_iInf_iff]
#align le_infi₂_iff le_iInf₂_iff

theorem iSup_lt_iff : iSup f < a ↔ ∃ b, b < a ∧ ∀ i, f i ≤ b :=
  ⟨fun h => ⟨iSup f, h, le_iSup f⟩, fun ⟨_, h, hb⟩ => (iSup_le hb).trans_lt h⟩
#align supr_lt_iff iSup_lt_iff

theorem lt_iInf_iff : a < iInf f ↔ ∃ b, a < b ∧ ∀ i, b ≤ f i :=
  ⟨fun h => ⟨iInf f, h, iInf_le f⟩, fun ⟨_, h, hb⟩ => h.trans_le <| le_iInf hb⟩
#align lt_infi_iff lt_iInf_iff

theorem sSup_eq_iSup {s : Set α} : sSup s = ⨆ a ∈ s, a :=
  le_antisymm (sSup_le le_iSup₂) (iSup₂_le fun _ => le_sSup)
#align Sup_eq_supr sSup_eq_iSup

theorem sInf_eq_iInf {s : Set α} : sInf s = ⨅ a ∈ s, a :=
  @sSup_eq_iSup αᵒᵈ _ _
#align Inf_eq_infi sInf_eq_iInf

theorem Monotone.le_map_iSup [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    ⨆ i, f (s i) ≤ f (iSup s) :=
  iSup_le fun _ => hf <| le_iSup _ _
#align monotone.le_map_supr Monotone.le_map_iSup

theorem Antitone.le_map_iInf [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    ⨆ i, f (s i) ≤ f (iInf s) :=
  hf.dual_left.le_map_iSup
#align antitone.le_map_infi Antitone.le_map_iInf

theorem Monotone.le_map_iSup₂ [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    ⨆ (i) (j), f (s i j) ≤ f (⨆ (i) (j), s i j) :=
  iSup₂_le fun _ _ => hf <| le_iSup₂ _ _
#align monotone.le_map_supr₂ Monotone.le_map_iSup₂

theorem Antitone.le_map_iInf₂ [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    ⨆ (i) (j), f (s i j) ≤ f (⨅ (i) (j), s i j) :=
  hf.dual_left.le_map_iSup₂ _
#align antitone.le_map_infi₂ Antitone.le_map_iInf₂

theorem Monotone.le_map_sSup [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    ⨆ a ∈ s, f a ≤ f (sSup s) := by rw [sSup_eq_iSup]; exact hf.le_map_iSup₂ _
#align monotone.le_map_Sup Monotone.le_map_sSup

theorem Antitone.le_map_sInf [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    ⨆ a ∈ s, f a ≤ f (sInf s) :=
  hf.dual_left.le_map_sSup
#align antitone.le_map_Inf Antitone.le_map_sInf

theorem OrderIso.map_iSup [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨆ i, x i) = ⨆ i, f (x i) :=
  eq_of_forall_ge_iff <| f.surjective.forall.2
  fun x => by simp only [f.le_iff_le, iSup_le_iff]
#align order_iso.map_supr OrderIso.map_iSup

theorem OrderIso.map_iInf [CompleteLattice β] (f : α ≃o β) (x : ι → α) :
    f (⨅ i, x i) = ⨅ i, f (x i) :=
  OrderIso.map_iSup f.dual _
#align order_iso.map_infi OrderIso.map_iInf

theorem OrderIso.map_sSup [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sSup s) = ⨆ a ∈ s, f a := by
  simp only [sSup_eq_iSup, OrderIso.map_iSup]
#align order_iso.map_Sup OrderIso.map_sSup

theorem OrderIso.map_sInf [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sInf s) = ⨅ a ∈ s, f a :=
  OrderIso.map_sSup f.dual _
#align order_iso.map_Inf OrderIso.map_sInf

theorem iSup_comp_le {ι' : Sort*} (f : ι' → α) (g : ι → ι') : ⨆ x, f (g x) ≤ ⨆ y, f y :=
  iSup_mono' fun _ => ⟨_, le_rfl⟩
#align supr_comp_le iSup_comp_le

theorem le_iInf_comp {ι' : Sort*} (f : ι' → α) (g : ι → ι') : ⨅ y, f y ≤ ⨅ x, f (g x) :=
  iInf_mono' fun _ => ⟨_, le_rfl⟩
#align le_infi_comp le_iInf_comp

theorem Monotone.iSup_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, x ≤ s i) : ⨆ x, f (s x) = ⨆ y, f y :=
  le_antisymm (iSup_comp_le _ _) (iSup_mono' fun x => (hs x).imp fun _ hi => hf hi)
#align monotone.supr_comp_eq Monotone.iSup_comp_eq

theorem Monotone.iInf_comp_eq [Preorder β] {f : β → α} (hf : Monotone f) {s : ι → β}
    (hs : ∀ x, ∃ i, s i ≤ x) : ⨅ x, f (s x) = ⨅ y, f y :=
  le_antisymm (iInf_mono' fun x => (hs x).imp fun _ hi => hf hi) (le_iInf_comp _ _)
#align monotone.infi_comp_eq Monotone.iInf_comp_eq

theorem Antitone.map_iSup_le [CompleteLattice β] {f : α → β} (hf : Antitone f) :
    f (iSup s) ≤ ⨅ i, f (s i) :=
  le_iInf fun _ => hf <| le_iSup _ _
#align antitone.map_supr_le Antitone.map_iSup_le

theorem Monotone.map_iInf_le [CompleteLattice β] {f : α → β} (hf : Monotone f) :
    f (iInf s) ≤ ⨅ i, f (s i) :=
  hf.dual_left.map_iSup_le
#align monotone.map_infi_le Monotone.map_iInf_le

theorem Antitone.map_iSup₂_le [CompleteLattice β] {f : α → β} (hf : Antitone f) (s : ∀ i, κ i → α) :
    f (⨆ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_iInf₂ _
#align antitone.map_supr₂_le Antitone.map_iSup₂_le

theorem Monotone.map_iInf₂_le [CompleteLattice β] {f : α → β} (hf : Monotone f) (s : ∀ i, κ i → α) :
    f (⨅ (i) (j), s i j) ≤ ⨅ (i) (j), f (s i j) :=
  hf.dual.le_map_iSup₂ _
#align monotone.map_infi₂_le Monotone.map_iInf₂_le

theorem Antitone.map_sSup_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Antitone f) :
    f (sSup s) ≤ ⨅ a ∈ s, f a := by
  rw [sSup_eq_iSup]
  exact hf.map_iSup₂_le _
#align antitone.map_Sup_le Antitone.map_sSup_le

theorem Monotone.map_sInf_le [CompleteLattice β] {s : Set α} {f : α → β} (hf : Monotone f) :
    f (sInf s) ≤ ⨅ a ∈ s, f a :=
  hf.dual_left.map_sSup_le
#align monotone.map_Inf_le Monotone.map_sInf_le

theorem iSup_const_le : ⨆ _ : ι, a ≤ a :=
  iSup_le fun _ => le_rfl
#align supr_const_le iSup_const_le

theorem le_iInf_const : a ≤ ⨅ _ : ι, a :=
  le_iInf fun _ => le_rfl
#align le_infi_const le_iInf_const

-- We generalize this to conditionally complete lattices in `ciSup_const` and `ciInf_const`.
theorem iSup_const [Nonempty ι] : ⨆ _ : ι, a = a := by rw [iSup, range_const, sSup_singleton]
#align supr_const iSup_const

theorem iInf_const [Nonempty ι] : ⨅ _ : ι, a = a :=
  @iSup_const αᵒᵈ _ _ a _
#align infi_const iInf_const

@[simp]
theorem iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥ :=
  bot_unique iSup_const_le
#align supr_bot iSup_bot

@[simp]
theorem iInf_top : (⨅ _ : ι, ⊤ : α) = ⊤ :=
  top_unique le_iInf_const
#align infi_top iInf_top

@[simp]
theorem iSup_eq_bot : iSup s = ⊥ ↔ ∀ i, s i = ⊥ :=
  sSup_eq_bot.trans forall_mem_range
#align supr_eq_bot iSup_eq_bot

@[simp]
theorem iInf_eq_top : iInf s = ⊤ ↔ ∀ i, s i = ⊤ :=
  sInf_eq_top.trans forall_mem_range
#align infi_eq_top iInf_eq_top

theorem iSup₂_eq_bot {f : ∀ i, κ i → α} : ⨆ (i) (j), f i j = ⊥ ↔ ∀ i j, f i j = ⊥ := by
  simp
#align supr₂_eq_bot iSup₂_eq_bot

theorem iInf₂_eq_top {f : ∀ i, κ i → α} : ⨅ (i) (j), f i j = ⊤ ↔ ∀ i j, f i j = ⊤ := by
  simp
#align infi₂_eq_top iInf₂_eq_top

@[simp]
theorem iSup_pos {p : Prop} {f : p → α} (hp : p) : ⨆ h : p, f h = f hp :=
  le_antisymm (iSup_le fun _ => le_rfl) (le_iSup _ _)
#align supr_pos iSup_pos

@[simp]
theorem iInf_pos {p : Prop} {f : p → α} (hp : p) : ⨅ h : p, f h = f hp :=
  le_antisymm (iInf_le _ _) (le_iInf fun _ => le_rfl)
#align infi_pos iInf_pos

@[simp]
theorem iSup_neg {p : Prop} {f : p → α} (hp : ¬p) : ⨆ h : p, f h = ⊥ :=
  le_antisymm (iSup_le fun h => (hp h).elim) bot_le
#align supr_neg iSup_neg

@[simp]
theorem iInf_neg {p : Prop} {f : p → α} (hp : ¬p) : ⨅ h : p, f h = ⊤ :=
  le_antisymm le_top <| le_iInf fun h => (hp h).elim
#align infi_neg iInf_neg

/-- Introduction rule to prove that `b` is the supremum of `f`: it suffices to check that `b`
is larger than `f i` for all `i`, and that this is not the case of any `w<b`.
See `ciSup_eq_of_forall_le_of_forall_lt_exists_gt` for a version in conditionally complete
lattices. -/
theorem iSup_eq_of_forall_le_of_forall_lt_exists_gt {f : ι → α} (h₁ : ∀ i, f i ≤ b)
    (h₂ : ∀ w, w < b → ∃ i, w < f i) : ⨆ i : ι, f i = b :=
  sSup_eq_of_forall_le_of_forall_lt_exists_gt (forall_mem_range.mpr h₁) fun w hw =>
    exists_range_iff.mpr <| h₂ w hw
#align supr_eq_of_forall_le_of_forall_lt_exists_gt iSup_eq_of_forall_le_of_forall_lt_exists_gt

/-- Introduction rule to prove that `b` is the infimum of `f`: it suffices to check that `b`
is smaller than `f i` for all `i`, and that this is not the case of any `w>b`.
See `ciInf_eq_of_forall_ge_of_forall_gt_exists_lt` for a version in conditionally complete
lattices. -/
theorem iInf_eq_of_forall_ge_of_forall_gt_exists_lt :
    (∀ i, b ≤ f i) → (∀ w, b < w → ∃ i, f i < w) → ⨅ i, f i = b :=
  @iSup_eq_of_forall_le_of_forall_lt_exists_gt αᵒᵈ _ _ _ _
#align infi_eq_of_forall_ge_of_forall_gt_exists_lt iInf_eq_of_forall_ge_of_forall_gt_exists_lt

theorem iSup_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    ⨆ h : p, a h = if h : p then a h else ⊥ := by by_cases h : p <;> simp [h]
#align supr_eq_dif iSup_eq_dif

theorem iSup_eq_if {p : Prop} [Decidable p] (a : α) : ⨆ _ : p, a = if p then a else ⊥ :=
  iSup_eq_dif fun _ => a
#align supr_eq_if iSup_eq_if

theorem iInf_eq_dif {p : Prop} [Decidable p] (a : p → α) :
    ⨅ h : p, a h = if h : p then a h else ⊤ :=
  @iSup_eq_dif αᵒᵈ _ _ _ _
#align infi_eq_dif iInf_eq_dif

theorem iInf_eq_if {p : Prop} [Decidable p] (a : α) : ⨅ _ : p, a = if p then a else ⊤ :=
  iInf_eq_dif fun _ => a
#align infi_eq_if iInf_eq_if

theorem iSup_comm {f : ι → ι' → α} : ⨆ (i) (j), f i j = ⨆ (j) (i), f i j :=
  le_antisymm (iSup_le fun i => iSup_mono fun j => le_iSup (fun i => f i j) i)
    (iSup_le fun _ => iSup_mono fun _ => le_iSup _ _)
#align supr_comm iSup_comm

theorem iInf_comm {f : ι → ι' → α} : ⨅ (i) (j), f i j = ⨅ (j) (i), f i j :=
  @iSup_comm αᵒᵈ _ _ _ _
#align infi_comm iInf_comm

theorem iSup₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    ⨆ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂ = ⨆ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@iSup_comm _ (κ₁ _), @iSup_comm _ ι₁]
#align supr₂_comm iSup₂_comm

theorem iInf₂_comm {ι₁ ι₂ : Sort*} {κ₁ : ι₁ → Sort*} {κ₂ : ι₂ → Sort*}
    (f : ∀ i₁, κ₁ i₁ → ∀ i₂, κ₂ i₂ → α) :
    ⨅ (i₁) (j₁) (i₂) (j₂), f i₁ j₁ i₂ j₂ = ⨅ (i₂) (j₂) (i₁) (j₁), f i₁ j₁ i₂ j₂ := by
  simp only [@iInf_comm _ (κ₁ _), @iInf_comm _ ι₁]
#align infi₂_comm iInf₂_comm

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
theorem iSup_iSup_eq_left {b : β} {f : ∀ x : β, x = b → α} : ⨆ x, ⨆ h : x = b, f x h = f b rfl :=
  (@le_iSup₂ _ _ _ _ f b rfl).antisymm'
    (iSup_le fun c =>
      iSup_le <| by
        rintro rfl
        rfl)
#align supr_supr_eq_left iSup_iSup_eq_left

@[simp]
theorem iInf_iInf_eq_left {b : β} {f : ∀ x : β, x = b → α} : ⨅ x, ⨅ h : x = b, f x h = f b rfl :=
  @iSup_iSup_eq_left αᵒᵈ _ _ _ _
#align infi_infi_eq_left iInf_iInf_eq_left

@[simp]
theorem iSup_iSup_eq_right {b : β} {f : ∀ x : β, b = x → α} : ⨆ x, ⨆ h : b = x, f x h = f b rfl :=
  (le_iSup₂ b rfl).antisymm'
    (iSup₂_le fun c => by
      rintro rfl
      rfl)
#align supr_supr_eq_right iSup_iSup_eq_right

@[simp]
theorem iInf_iInf_eq_right {b : β} {f : ∀ x : β, b = x → α} : ⨅ x, ⨅ h : b = x, f x h = f b rfl :=
  @iSup_iSup_eq_right αᵒᵈ _ _ _ _
#align infi_infi_eq_right iInf_iInf_eq_right

theorem iSup_subtype {p : ι → Prop} {f : Subtype p → α} : iSup f = ⨆ (i) (h : p i), f ⟨i, h⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ p _ (fun i h => f ⟨i, h⟩) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)
#align supr_subtype iSup_subtype

theorem iInf_subtype : ∀ {p : ι → Prop} {f : Subtype p → α}, iInf f = ⨅ (i) (h : p i), f ⟨i, h⟩ :=
  @iSup_subtype αᵒᵈ _ _
#align infi_subtype iInf_subtype

theorem iSup_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    ⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property :=
  (@iSup_subtype _ _ _ p fun x => f x.val x.property).symm
#align supr_subtype' iSup_subtype'

theorem iInf_subtype' {p : ι → Prop} {f : ∀ i, p i → α} :
    ⨅ (i) (h : p i), f i h = ⨅ x : Subtype p, f x x.property :=
  (@iInf_subtype _ _ _ p fun x => f x.val x.property).symm
#align infi_subtype' iInf_subtype'

theorem iSup_subtype'' {ι} (s : Set ι) (f : ι → α) : ⨆ i : s, f i = ⨆ (t : ι) (_ : t ∈ s), f t :=
  iSup_subtype
#align supr_subtype'' iSup_subtype''

theorem iInf_subtype'' {ι} (s : Set ι) (f : ι → α) : ⨅ i : s, f i = ⨅ (t : ι) (_ : t ∈ s), f t :=
  iInf_subtype
#align infi_subtype'' iInf_subtype''

theorem biSup_const {ι : Sort _} {a : α} {s : Set ι} (hs : s.Nonempty) : ⨆ i ∈ s, a = a := by
  haveI : Nonempty s := Set.nonempty_coe_sort.mpr hs
  rw [← iSup_subtype'', iSup_const]
#align bsupr_const biSup_const

theorem biInf_const {ι : Sort _} {a : α} {s : Set ι} (hs : s.Nonempty) : ⨅ i ∈ s, a = a :=
  @biSup_const αᵒᵈ _ ι _ s hs
#align binfi_const biInf_const

theorem iSup_sup_eq : ⨆ x, f x ⊔ g x = (⨆ x, f x) ⊔ ⨆ x, g x :=
  le_antisymm (iSup_le fun _ => sup_le_sup (le_iSup _ _) <| le_iSup _ _)
    (sup_le (iSup_mono fun _ => le_sup_left) <| iSup_mono fun _ => le_sup_right)
#align supr_sup_eq iSup_sup_eq

theorem iInf_inf_eq : ⨅ x, f x ⊓ g x = (⨅ x, f x) ⊓ ⨅ x, g x :=
  @iSup_sup_eq αᵒᵈ _ _ _ _
#align infi_inf_eq iInf_inf_eq

lemma Equiv.biSup_comp {ι ι' : Type*} {g : ι' → α} (e : ι ≃ ι') (s : Set ι') :
    ⨆ i ∈ e.symm '' s, g (e i) = ⨆ i ∈ s, g i := by
  simpa only [iSup_subtype'] using (image e.symm s).symm.iSup_comp (g := g ∘ (↑))

lemma Equiv.biInf_comp {ι ι' : Type*} {g : ι' → α} (e : ι ≃ ι') (s : Set ι') :
    ⨅ i ∈ e.symm '' s, g (e i) = ⨅ i ∈ s, g i :=
  e.biSup_comp s (α := αᵒᵈ)

lemma biInf_le {ι : Type*} {s : Set ι} (f : ι → α) {i : ι} (hi : i ∈ s) :
    ⨅ i ∈ s, f i ≤ f i := by
  simpa only [iInf_subtype'] using iInf_le (ι := s) (f := f ∘ (↑)) ⟨i, hi⟩

lemma le_biSup {ι : Type*} {s : Set ι} (f : ι → α) {i : ι} (hi : i ∈ s) :
    f i ≤ ⨆ i ∈ s, f i :=
  biInf_le (α := αᵒᵈ) f hi

/- TODO: here is another example where more flexible pattern matching
   might help.

begin
  apply @le_antisymm,
  safe, pose h := f a ⊓ g a, begin [smt] ematch, ematch  end
end
-/
theorem iSup_sup [Nonempty ι] {f : ι → α} {a : α} : (⨆ x, f x) ⊔ a = ⨆ x, f x ⊔ a := by
  rw [iSup_sup_eq, iSup_const]
#align supr_sup iSup_sup

theorem iInf_inf [Nonempty ι] {f : ι → α} {a : α} : (⨅ x, f x) ⊓ a = ⨅ x, f x ⊓ a := by
  rw [iInf_inf_eq, iInf_const]
#align infi_inf iInf_inf

theorem sup_iSup [Nonempty ι] {f : ι → α} {a : α} : (a ⊔ ⨆ x, f x) = ⨆ x, a ⊔ f x := by
  rw [iSup_sup_eq, iSup_const]
#align sup_supr sup_iSup

theorem inf_iInf [Nonempty ι] {f : ι → α} {a : α} : (a ⊓ ⨅ x, f x) = ⨅ x, a ⊓ f x := by
  rw [iInf_inf_eq, iInf_const]
#align inf_infi inf_iInf

theorem biSup_sup {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨆ (i) (h : p i), f i h) ⊔ a = ⨆ (i) (h : p i), f i h ⊔ a := by
  haveI : Nonempty { i // p i } :=
    let ⟨i, hi⟩ := h
    ⟨⟨i, hi⟩⟩
  rw [iSup_subtype', iSup_subtype', iSup_sup]
#align bsupr_sup biSup_sup

theorem sup_biSup {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊔ ⨆ (i) (h : p i), f i h) = ⨆ (i) (h : p i), a ⊔ f i h := by
  simpa only [sup_comm] using @biSup_sup α _ _ p _ _ h
#align sup_bsupr sup_biSup

theorem biInf_inf {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (⨅ (i) (h : p i), f i h) ⊓ a = ⨅ (i) (h : p i), f i h ⊓ a :=
  @biSup_sup αᵒᵈ ι _ p f _ h
#align binfi_inf biInf_inf

theorem inf_biInf {p : ι → Prop} {f : ∀ i, p i → α} {a : α} (h : ∃ i, p i) :
    (a ⊓ ⨅ (i) (h : p i), f i h) = ⨅ (i) (h : p i), a ⊓ f i h :=
  @sup_biSup αᵒᵈ ι _ p f _ h
#align inf_binfi inf_biInf

/-! ### `iSup` and `iInf` under `Prop` -/


theorem iSup_false {s : False → α} : iSup s = ⊥ := by simp
#align supr_false iSup_false

theorem iInf_false {s : False → α} : iInf s = ⊤ := by simp
#align infi_false iInf_false

theorem iSup_true {s : True → α} : iSup s = s trivial :=
  iSup_pos trivial
#align supr_true iSup_true

theorem iInf_true {s : True → α} : iInf s = s trivial :=
  iInf_pos trivial
#align infi_true iInf_true

@[simp]
theorem iSup_exists {p : ι → Prop} {f : Exists p → α} : ⨆ x, f x = ⨆ (i) (h), f ⟨i, h⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)
#align supr_exists iSup_exists

@[simp]
theorem iInf_exists {p : ι → Prop} {f : Exists p → α} : ⨅ x, f x = ⨅ (i) (h), f ⟨i, h⟩ :=
  @iSup_exists αᵒᵈ _ _ _ _
#align infi_exists iInf_exists

theorem iSup_and {p q : Prop} {s : p ∧ q → α} : iSup s = ⨆ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  le_antisymm (iSup_le fun ⟨i, h⟩ => @le_iSup₂ _ _ _ _ (fun _ _ => _) i h)
    (iSup₂_le fun _ _ => le_iSup _ _)
#align supr_and iSup_and

theorem iInf_and {p q : Prop} {s : p ∧ q → α} : iInf s = ⨅ (h₁) (h₂), s ⟨h₁, h₂⟩ :=
  @iSup_and αᵒᵈ _ _ _ _
#align infi_and iInf_and

/-- The symmetric case of `iSup_and`, useful for rewriting into a supremum over a conjunction -/
theorem iSup_and' {p q : Prop} {s : p → q → α} :
    ⨆ (h₁ : p) (h₂ : q), s h₁ h₂ = ⨆ h : p ∧ q, s h.1 h.2 :=
  Eq.symm iSup_and
#align supr_and' iSup_and'

/-- The symmetric case of `iInf_and`, useful for rewriting into an infimum over a conjunction -/
theorem iInf_and' {p q : Prop} {s : p → q → α} :
    ⨅ (h₁ : p) (h₂ : q), s h₁ h₂ = ⨅ h : p ∧ q, s h.1 h.2 :=
  Eq.symm iInf_and
#align infi_and' iInf_and'

theorem iSup_or {p q : Prop} {s : p ∨ q → α} :
    ⨆ x, s x = (⨆ i, s (Or.inl i)) ⊔ ⨆ j, s (Or.inr j) :=
  le_antisymm
    (iSup_le fun i =>
      match i with
      | Or.inl _ => le_sup_of_le_left <| le_iSup (fun _ => s _) _
      | Or.inr _ => le_sup_of_le_right <| le_iSup (fun _ => s _) _)
    (sup_le (iSup_comp_le _ _) (iSup_comp_le _ _))
#align supr_or iSup_or

theorem iInf_or {p q : Prop} {s : p ∨ q → α} :
    ⨅ x, s x = (⨅ i, s (Or.inl i)) ⊓ ⨅ j, s (Or.inr j) :=
  @iSup_or αᵒᵈ _ _ _ _
#align infi_or iInf_or

section

variable (p : ι → Prop) [DecidablePred p]

theorem iSup_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    ⨆ i, (if h : p i then f i h else g i h) = (⨆ (i) (h : p i), f i h) ⊔ ⨆ (i) (h : ¬p i),
    g i h := by
  rw [← iSup_sup_eq]
  congr 1 with i
  split_ifs with h <;> simp [h]
#align supr_dite iSup_dite

theorem iInf_dite (f : ∀ i, p i → α) (g : ∀ i, ¬p i → α) :
    ⨅ i, (if h : p i then f i h else g i h) = (⨅ (i) (h : p i), f i h) ⊓ ⨅ (i) (h : ¬p i), g i h :=
  iSup_dite p (show ∀ i, p i → αᵒᵈ from f) g
#align infi_dite iInf_dite

theorem iSup_ite (f g : ι → α) :
    ⨆ i, (if p i then f i else g i) = (⨆ (i) (_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), g i :=
  iSup_dite _ _ _
#align supr_ite iSup_ite

theorem iInf_ite (f g : ι → α) :
    ⨅ i, (if p i then f i else g i) = (⨅ (i) (_ : p i), f i) ⊓ ⨅ (i) (_ : ¬p i), g i :=
  iInf_dite _ _ _
#align infi_ite iInf_ite

end

theorem iSup_range {g : β → α} {f : ι → β} : ⨆ b ∈ range f, g b = ⨆ i, g (f i) := by
  rw [← iSup_subtype'', iSup_range']
#align supr_range iSup_range

theorem iInf_range : ∀ {g : β → α} {f : ι → β}, ⨅ b ∈ range f, g b = ⨅ i, g (f i) :=
  @iSup_range αᵒᵈ _ _ _
#align infi_range iInf_range

theorem sSup_image {s : Set β} {f : β → α} : sSup (f '' s) = ⨆ a ∈ s, f a := by
  rw [← iSup_subtype'', sSup_image']
#align Sup_image sSup_image

theorem sInf_image {s : Set β} {f : β → α} : sInf (f '' s) = ⨅ a ∈ s, f a :=
  @sSup_image αᵒᵈ _ _ _ _
#align Inf_image sInf_image

theorem OrderIso.map_sSup_eq_sSup_symm_preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sSup s) = sSup (f.symm ⁻¹' s) := by
  rw [map_sSup, ← sSup_image, f.image_eq_preimage]

theorem OrderIso.map_sInf_eq_sInf_symm_preimage [CompleteLattice β] (f : α ≃o β) (s : Set α) :
    f (sInf s) = sInf (f.symm ⁻¹' s) := by
  rw [map_sInf, ← sInf_image, f.image_eq_preimage]

/-
### iSup and iInf under set constructions
-/
theorem iSup_emptyset {f : β → α} : ⨆ x ∈ (∅ : Set β), f x = ⊥ := by simp
#align supr_emptyset iSup_emptyset

theorem iInf_emptyset {f : β → α} : ⨅ x ∈ (∅ : Set β), f x = ⊤ := by simp
#align infi_emptyset iInf_emptyset

theorem iSup_univ {f : β → α} : ⨆ x ∈ (univ : Set β), f x = ⨆ x, f x := by simp
#align supr_univ iSup_univ

theorem iInf_univ {f : β → α} : ⨅ x ∈ (univ : Set β), f x = ⨅ x, f x := by simp
#align infi_univ iInf_univ

theorem iSup_union {f : β → α} {s t : Set β} :
    ⨆ x ∈ s ∪ t, f x = (⨆ x ∈ s, f x) ⊔ ⨆ x ∈ t, f x := by
  simp_rw [mem_union, iSup_or, iSup_sup_eq]
#align supr_union iSup_union

theorem iInf_union {f : β → α} {s t : Set β} : ⨅ x ∈ s ∪ t, f x = (⨅ x ∈ s, f x) ⊓ ⨅ x ∈ t, f x :=
  @iSup_union αᵒᵈ _ _ _ _ _
#align infi_union iInf_union

theorem iSup_split (f : β → α) (p : β → Prop) :
    ⨆ i, f i = (⨆ (i) (_ : p i), f i) ⊔ ⨆ (i) (_ : ¬p i), f i := by
  simpa [Classical.em] using @iSup_union _ _ _ f { i | p i } { i | ¬p i }
#align supr_split iSup_split

theorem iInf_split :
    ∀ (f : β → α) (p : β → Prop), ⨅ i, f i = (⨅ (i) (_ : p i), f i) ⊓ ⨅ (i) (_ : ¬p i), f i :=
  @iSup_split αᵒᵈ _ _
#align infi_split iInf_split

theorem iSup_split_single (f : β → α) (i₀ : β) : ⨆ i, f i = f i₀ ⊔ ⨆ (i) (_ : i ≠ i₀), f i := by
  convert iSup_split f (fun i => i = i₀)
  simp
#align supr_split_single iSup_split_single

theorem iInf_split_single (f : β → α) (i₀ : β) : ⨅ i, f i = f i₀ ⊓ ⨅ (i) (_ : i ≠ i₀), f i :=
  @iSup_split_single αᵒᵈ _ _ _ _
#align infi_split_single iInf_split_single

theorem iSup_le_iSup_of_subset {f : β → α} {s t : Set β} : s ⊆ t → ⨆ x ∈ s, f x ≤ ⨆ x ∈ t, f x :=
  biSup_mono
#align supr_le_supr_of_subset iSup_le_iSup_of_subset

theorem iInf_le_iInf_of_subset {f : β → α} {s t : Set β} : s ⊆ t → ⨅ x ∈ t, f x ≤ ⨅ x ∈ s, f x :=
  biInf_mono
#align infi_le_infi_of_subset iInf_le_iInf_of_subset

theorem iSup_insert {f : β → α} {s : Set β} {b : β} :
    ⨆ x ∈ insert b s, f x = f b ⊔ ⨆ x ∈ s, f x :=
  Eq.trans iSup_union <| congr_arg (fun x => x ⊔ ⨆ x ∈ s, f x) iSup_iSup_eq_left
#align supr_insert iSup_insert

theorem iInf_insert {f : β → α} {s : Set β} {b : β} :
    ⨅ x ∈ insert b s, f x = f b ⊓ ⨅ x ∈ s, f x :=
  Eq.trans iInf_union <| congr_arg (fun x => x ⊓ ⨅ x ∈ s, f x) iInf_iInf_eq_left
#align infi_insert iInf_insert

theorem iSup_singleton {f : β → α} {b : β} : ⨆ x ∈ (singleton b : Set β), f x = f b := by simp
#align supr_singleton iSup_singleton

theorem iInf_singleton {f : β → α} {b : β} : ⨅ x ∈ (singleton b : Set β), f x = f b := by simp
#align infi_singleton iInf_singleton

theorem iSup_pair {f : β → α} {a b : β} : ⨆ x ∈ ({a, b} : Set β), f x = f a ⊔ f b := by
  rw [iSup_insert, iSup_singleton]
#align supr_pair iSup_pair

theorem iInf_pair {f : β → α} {a b : β} : ⨅ x ∈ ({a, b} : Set β), f x = f a ⊓ f b := by
  rw [iInf_insert, iInf_singleton]
#align infi_pair iInf_pair

theorem iSup_image {γ} {f : β → γ} {g : γ → α} {t : Set β} :
    ⨆ c ∈ f '' t, g c = ⨆ b ∈ t, g (f b) := by rw [← sSup_image, ← sSup_image, ← image_comp]; rfl
#align supr_image iSup_image

theorem iInf_image :
    ∀ {γ} {f : β → γ} {g : γ → α} {t : Set β}, ⨅ c ∈ f '' t, g c = ⨅ b ∈ t, g (f b) :=
  @iSup_image αᵒᵈ _ _
#align infi_image iInf_image

theorem iSup_extend_bot {e : ι → β} (he : Injective e) (f : ι → α) :
    ⨆ j, extend e f ⊥ j = ⨆ i, f i := by
  rw [iSup_split _ fun j => ∃ i, e i = j]
  simp (config := { contextual := true }) [he.extend_apply, extend_apply', @iSup_comm _ β ι]
#align supr_extend_bot iSup_extend_bot

theorem iInf_extend_top {e : ι → β} (he : Injective e) (f : ι → α) :
    ⨅ j, extend e f ⊤ j = iInf f :=
  @iSup_extend_bot αᵒᵈ _ _ _ _ he _
#align infi_extend_top iInf_extend_top

/-!
### `iSup` and `iInf` under `Type`
-/


theorem iSup_of_empty' {α ι} [SupSet α] [IsEmpty ι] (f : ι → α) : iSup f = sSup (∅ : Set α) :=
  congr_arg sSup (range_eq_empty f)
#align supr_of_empty' iSup_of_empty'

theorem iInf_of_isEmpty {α ι} [InfSet α] [IsEmpty ι] (f : ι → α) : iInf f = sInf (∅ : Set α) :=
  congr_arg sInf (range_eq_empty f)
#align infi_of_empty' iInf_of_isEmpty

theorem iSup_of_empty [IsEmpty ι] (f : ι → α) : iSup f = ⊥ :=
  (iSup_of_empty' f).trans sSup_empty
#align supr_of_empty iSup_of_empty

theorem iInf_of_empty [IsEmpty ι] (f : ι → α) : iInf f = ⊤ :=
  @iSup_of_empty αᵒᵈ _ _ _ f
#align infi_of_empty iInf_of_empty

theorem iSup_bool_eq {f : Bool → α} : ⨆ b : Bool, f b = f true ⊔ f false := by
  rw [iSup, Bool.range_eq, sSup_pair, sup_comm]
#align supr_bool_eq iSup_bool_eq

theorem iInf_bool_eq {f : Bool → α} : ⨅ b : Bool, f b = f true ⊓ f false :=
  @iSup_bool_eq αᵒᵈ _ _
#align infi_bool_eq iInf_bool_eq

theorem sup_eq_iSup (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y := by
  rw [iSup_bool_eq, Bool.cond_true, Bool.cond_false]
#align sup_eq_supr sup_eq_iSup

theorem inf_eq_iInf (x y : α) : x ⊓ y = ⨅ b : Bool, cond b x y :=
  @sup_eq_iSup αᵒᵈ _ _ _
#align inf_eq_infi inf_eq_iInf

theorem isGLB_biInf {s : Set β} {f : β → α} : IsGLB (f '' s) (⨅ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, iInf_subtype'] using
    @isGLB_iInf α s _ (f ∘ fun x => (x : β))
#align is_glb_binfi isGLB_biInf

theorem isLUB_biSup {s : Set β} {f : β → α} : IsLUB (f '' s) (⨆ x ∈ s, f x) := by
  simpa only [range_comp, Subtype.range_coe, iSup_subtype'] using
    @isLUB_iSup α s _ (f ∘ fun x => (x : β))
#align is_lub_bsupr isLUB_biSup

theorem iSup_sigma {p : β → Type*} {f : Sigma p → α} : ⨆ x, f x = ⨆ (i) (j), f ⟨i, j⟩ :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Sigma.forall]
#align supr_sigma iSup_sigma

theorem iInf_sigma {p : β → Type*} {f : Sigma p → α} : ⨅ x, f x = ⨅ (i) (j), f ⟨i, j⟩ :=
  @iSup_sigma αᵒᵈ _ _ _ _
#align infi_sigma iInf_sigma

lemma iSup_sigma' {κ : β → Type*} (f : ∀ i, κ i → α) :
    (⨆ i, ⨆ j, f i j) = ⨆ x : Σ i, κ i, f x.1 x.2 :=
(iSup_sigma (f := fun x ↦ f x.1 x.2)).symm

lemma iInf_sigma' {κ : β → Type*} (f : ∀ i, κ i → α) :
    (⨅ i, ⨅ j, f i j) = ⨅ x : Σ i, κ i, f x.1 x.2 :=
(iInf_sigma (f := fun x ↦ f x.1 x.2)).symm

theorem iSup_prod {f : β × γ → α} : ⨆ x, f x = ⨆ (i) (j), f (i, j) :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, Prod.forall]
#align supr_prod iSup_prod

theorem iInf_prod {f : β × γ → α} : ⨅ x, f x = ⨅ (i) (j), f (i, j) :=
  @iSup_prod αᵒᵈ _ _ _ _
#align infi_prod iInf_prod

lemma iSup_prod' (f : β → γ → α) : (⨆ i, ⨆ j, f i j) = ⨆ x : β × γ, f x.1 x.2 :=
(iSup_prod (f := fun x ↦ f x.1 x.2)).symm

lemma iInf_prod' (f : β → γ → α) : (⨅ i, ⨅ j, f i j) = ⨅ x : β × γ, f x.1 x.2 :=
(iInf_prod (f := fun x ↦ f x.1 x.2)).symm

theorem biSup_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    ⨆ x ∈ s ×ˢ t, f x = ⨆ (a ∈ s) (b ∈ t), f (a, b) := by
  simp_rw [iSup_prod, mem_prod, iSup_and]
  exact iSup_congr fun _ => iSup_comm
#align bsupr_prod biSup_prod

theorem biInf_prod {f : β × γ → α} {s : Set β} {t : Set γ} :
    ⨅ x ∈ s ×ˢ t, f x = ⨅ (a ∈ s) (b ∈ t), f (a, b) :=
  @biSup_prod αᵒᵈ _ _ _ _ _ _
#align binfi_prod biInf_prod

theorem iSup_sum {f : Sum β γ → α} : ⨆ x, f x = (⨆ i, f (Sum.inl i)) ⊔ ⨆ j, f (Sum.inr j) :=
  eq_of_forall_ge_iff fun c => by simp only [sup_le_iff, iSup_le_iff, Sum.forall]
#align supr_sum iSup_sum

theorem iInf_sum {f : Sum β γ → α} : ⨅ x, f x = (⨅ i, f (Sum.inl i)) ⊓ ⨅ j, f (Sum.inr j) :=
  @iSup_sum αᵒᵈ _ _ _ _
#align infi_sum iInf_sum

theorem iSup_option (f : Option β → α) : ⨆ o, f o = f none ⊔ ⨆ b, f (Option.some b) :=
  eq_of_forall_ge_iff fun c => by simp only [iSup_le_iff, sup_le_iff, Option.forall]
#align supr_option iSup_option

theorem iInf_option (f : Option β → α) : ⨅ o, f o = f none ⊓ ⨅ b, f (Option.some b) :=
  @iSup_option αᵒᵈ _ _ _
#align infi_option iInf_option

/-- A version of `iSup_option` useful for rewriting right-to-left. -/
theorem iSup_option_elim (a : α) (f : β → α) : ⨆ o : Option β, o.elim a f = a ⊔ ⨆ b, f b := by
  simp [iSup_option]
#align supr_option_elim iSup_option_elim

/-- A version of `iInf_option` useful for rewriting right-to-left. -/
theorem iInf_option_elim (a : α) (f : β → α) : ⨅ o : Option β, o.elim a f = a ⊓ ⨅ b, f b :=
  @iSup_option_elim αᵒᵈ _ _ _ _
#align infi_option_elim iInf_option_elim

/-- When taking the supremum of `f : ι → α`, the elements of `ι` on which `f` gives `⊥` can be
dropped, without changing the result. -/
@[simp]
theorem iSup_ne_bot_subtype (f : ι → α) : ⨆ i : { i // f i ≠ ⊥ }, f i = ⨆ i, f i := by
  by_cases htriv : ∀ i, f i = ⊥
  · simp only [iSup_bot, (funext htriv : f = _)]
  refine (iSup_comp_le f _).antisymm (iSup_mono' fun i => ?_)
  by_cases hi : f i = ⊥
  · rw [hi]
    obtain ⟨i₀, hi₀⟩ := not_forall.mp htriv
    exact ⟨⟨i₀, hi₀⟩, bot_le⟩
  · exact ⟨⟨i, hi⟩, rfl.le⟩
#align supr_ne_bot_subtype iSup_ne_bot_subtype

/-- When taking the infimum of `f : ι → α`, the elements of `ι` on which `f` gives `⊤` can be
dropped, without changing the result. -/
theorem iInf_ne_top_subtype (f : ι → α) : ⨅ i : { i // f i ≠ ⊤ }, f i = ⨅ i, f i :=
  @iSup_ne_bot_subtype αᵒᵈ ι _ f
#align infi_ne_top_subtype iInf_ne_top_subtype

theorem sSup_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    sSup (image2 f s t) = ⨆ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, sSup_image, biSup_prod]
#align Sup_image2 sSup_image2

theorem sInf_image2 {f : β → γ → α} {s : Set β} {t : Set γ} :
    sInf (image2 f s t) = ⨅ (a ∈ s) (b ∈ t), f a b := by rw [← image_prod, sInf_image, biInf_prod]
#align Inf_image2 sInf_image2

/-!
### `iSup` and `iInf` under `ℕ`
-/


theorem iSup_ge_eq_iSup_nat_add (u : ℕ → α) (n : ℕ) : ⨆ i ≥ n, u i = ⨆ i, u (i + n) := by
  apply le_antisymm <;> simp only [iSup_le_iff]
  · refine fun i hi => le_sSup ⟨i - n, ?_⟩
    dsimp only
    rw [Nat.sub_add_cancel hi]
  · exact fun i => le_sSup ⟨i + n, iSup_pos (Nat.le_add_left _ _)⟩
#align supr_ge_eq_supr_nat_add iSup_ge_eq_iSup_nat_add

theorem iInf_ge_eq_iInf_nat_add (u : ℕ → α) (n : ℕ) : ⨅ i ≥ n, u i = ⨅ i, u (i + n) :=
  @iSup_ge_eq_iSup_nat_add αᵒᵈ _ _ _
#align infi_ge_eq_infi_nat_add iInf_ge_eq_iInf_nat_add

theorem Monotone.iSup_nat_add {f : ℕ → α} (hf : Monotone f) (k : ℕ) : ⨆ n, f (n + k) = ⨆ n, f n :=
  le_antisymm (iSup_le fun i => le_iSup _ (i + k)) <| iSup_mono fun i => hf <| Nat.le_add_right i k
#align monotone.supr_nat_add Monotone.iSup_nat_add

theorem Antitone.iInf_nat_add {f : ℕ → α} (hf : Antitone f) (k : ℕ) : ⨅ n, f (n + k) = ⨅ n, f n :=
  hf.dual_right.iSup_nat_add k
#align antitone.infi_nat_add Antitone.iInf_nat_add

-- Porting note: the linter doesn't like this being marked as `@[simp]`,
-- saying that it doesn't work when called on its LHS.
-- Mysteriously, it *does* work. Nevertheless, per
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/complete_lattice.20and.20has_sup/near/316497982
-- "the subterm ?f (i + ?k) produces an ugly higher-order unification problem."
-- @[simp]
theorem iSup_iInf_ge_nat_add (f : ℕ → α) (k : ℕ) :
    ⨆ n, ⨅ i ≥ n, f (i + k) = ⨆ n, ⨅ i ≥ n, f i := by
  have hf : Monotone fun n => ⨅ i ≥ n, f i := fun n m h => biInf_mono fun i => h.trans
  rw [← Monotone.iSup_nat_add hf k]
  · simp_rw [iInf_ge_eq_iInf_nat_add, ← Nat.add_assoc]
#align supr_infi_ge_nat_add iSup_iInf_ge_nat_add

-- Porting note: removing `@[simp]`, see discussion on `iSup_iInf_ge_nat_add`.
-- @[simp]
theorem iInf_iSup_ge_nat_add :
    ∀ (f : ℕ → α) (k : ℕ), ⨅ n, ⨆ i ≥ n, f (i + k) = ⨅ n, ⨆ i ≥ n, f i :=
  @iSup_iInf_ge_nat_add αᵒᵈ _
#align infi_supr_ge_nat_add iInf_iSup_ge_nat_add

theorem sup_iSup_nat_succ (u : ℕ → α) : (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ i, u i :=
  calc
    (u 0 ⊔ ⨆ i, u (i + 1)) = ⨆ x ∈ {0} ∪ range Nat.succ, u x := by
      { rw [iSup_union, iSup_singleton, iSup_range] }
    _ = ⨆ i, u i := by rw [Nat.zero_union_range_succ, iSup_univ]
#align sup_supr_nat_succ sup_iSup_nat_succ

theorem inf_iInf_nat_succ (u : ℕ → α) : (u 0 ⊓ ⨅ i, u (i + 1)) = ⨅ i, u i :=
  @sup_iSup_nat_succ αᵒᵈ _ u
#align inf_infi_nat_succ inf_iInf_nat_succ

theorem iInf_nat_gt_zero_eq (f : ℕ → α) : ⨅ i > 0, f i = ⨅ i, f (i + 1) := by
  rw [← iInf_range, Nat.range_succ]
  simp
#align infi_nat_gt_zero_eq iInf_nat_gt_zero_eq

theorem iSup_nat_gt_zero_eq (f : ℕ → α) : ⨆ i > 0, f i = ⨆ i, f (i + 1) :=
  @iInf_nat_gt_zero_eq αᵒᵈ _ f
#align supr_nat_gt_zero_eq iSup_nat_gt_zero_eq

end

section CompleteLinearOrder

variable [CompleteLinearOrder α]

theorem iSup_eq_top (f : ι → α) : iSup f = ⊤ ↔ ∀ b < ⊤, ∃ i, b < f i := by
  simp only [← sSup_range, sSup_eq_top, Set.exists_range_iff]
#align supr_eq_top iSup_eq_top

theorem iInf_eq_bot (f : ι → α) : iInf f = ⊥ ↔ ∀ b > ⊥, ∃ i, f i < b := by
  simp only [← sInf_range, sInf_eq_bot, Set.exists_range_iff]
#align infi_eq_bot iInf_eq_bot

end CompleteLinearOrder

/-!
### Instances
-/


instance Prop.instCompleteLattice : CompleteLattice Prop where
  __ := Prop.instBoundedOrder
  __ := Prop.instDistribLattice
  sSup s := ∃ a ∈ s, a
  le_sSup _ a h p := ⟨a, h, p⟩
  sSup_le _ _ h := fun ⟨b, h', p⟩ => h b h' p
  sInf s := ∀ a, a ∈ s → a
  sInf_le _ a h p := p a h
  le_sInf _ _ h p b hb := h b hb p
#align Prop.complete_lattice Prop.instCompleteLattice

noncomputable instance Prop.instCompleteLinearOrder : CompleteLinearOrder Prop where
  __ := Prop.instCompleteLattice
  __ := Prop.linearOrder
#align Prop.complete_linear_order Prop.instCompleteLinearOrder

@[simp]
theorem sSup_Prop_eq {s : Set Prop} : sSup s = ∃ p ∈ s, p :=
  rfl
#align Sup_Prop_eq sSup_Prop_eq

@[simp]
theorem sInf_Prop_eq {s : Set Prop} : sInf s = ∀ p ∈ s, p :=
  rfl
#align Inf_Prop_eq sInf_Prop_eq

@[simp]
theorem iSup_Prop_eq {p : ι → Prop} : ⨆ i, p i = ∃ i, p i :=
  le_antisymm (fun ⟨_, ⟨i, (eq : p i = _)⟩, hq⟩ => ⟨i, eq.symm ▸ hq⟩) fun ⟨i, hi⟩ =>
    ⟨p i, ⟨i, rfl⟩, hi⟩
#align supr_Prop_eq iSup_Prop_eq

@[simp]
theorem iInf_Prop_eq {p : ι → Prop} : ⨅ i, p i = ∀ i, p i :=
  le_antisymm (fun h i => h _ ⟨i, rfl⟩) fun h _ ⟨i, Eq⟩ => Eq ▸ h i
#align infi_Prop_eq iInf_Prop_eq

instance Pi.supSet {α : Type*} {β : α → Type*} [∀ i, SupSet (β i)] : SupSet (∀ i, β i) :=
  ⟨fun s i => ⨆ f : s, (f : ∀ i, β i) i⟩
#align pi.has_Sup Pi.supSet

instance Pi.infSet {α : Type*} {β : α → Type*} [∀ i, InfSet (β i)] : InfSet (∀ i, β i) :=
  ⟨fun s i => ⨅ f : s, (f : ∀ i, β i) i⟩
#align pi.has_Inf Pi.infSet

instance Pi.instCompleteLattice {α : Type*} {β : α → Type*} [∀ i, CompleteLattice (β i)] :
    CompleteLattice (∀ i, β i) where
  __ := instBoundedOrder
  le_sSup s f hf := fun i => le_iSup (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩
  sInf_le s f hf := fun i => iInf_le (fun f : s => (f : ∀ i, β i) i) ⟨f, hf⟩
  sSup_le _ _ hf := fun i => iSup_le fun g => hf g g.2 i
  le_sInf _ _ hf := fun i => le_iInf fun g => hf g g.2 i
#align pi.complete_lattice Pi.instCompleteLattice

theorem sSup_apply {α : Type*} {β : α → Type*} [∀ i, SupSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    (sSup s) a = ⨆ f : s, (f : ∀ a, β a) a :=
  rfl
#align Sup_apply sSup_apply

theorem sInf_apply {α : Type*} {β : α → Type*} [∀ i, InfSet (β i)] {s : Set (∀ a, β a)} {a : α} :
    sInf s a = ⨅ f : s, (f : ∀ a, β a) a :=
  rfl
#align Inf_apply sInf_apply

@[simp]
theorem iSup_apply {α : Type*} {β : α → Type*} {ι : Sort*} [∀ i, SupSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨆ i, f i) a = ⨆ i, f i a := by
  rw [iSup, sSup_apply, iSup, iSup, ← image_eq_range (fun f : ∀ i, β i => f a) (range f), ←
    range_comp]; rfl
#align supr_apply iSup_apply

@[simp]
theorem iInf_apply {α : Type*} {β : α → Type*} {ι : Sort*} [∀ i, InfSet (β i)] {f : ι → ∀ a, β a}
    {a : α} : (⨅ i, f i) a = ⨅ i, f i a :=
  @iSup_apply α (fun i => (β i)ᵒᵈ) _ _ _ _
#align infi_apply iInf_apply

theorem unary_relation_sSup_iff {α : Type*} (s : Set (α → Prop)) {a : α} :
    sSup s a ↔ ∃ r : α → Prop, r ∈ s ∧ r a := by
  rw [sSup_apply]
  simp [← eq_iff_iff]
#align unary_relation_Sup_iff unary_relation_sSup_iff

theorem unary_relation_sInf_iff {α : Type*} (s : Set (α → Prop)) {a : α} :
    sInf s a ↔ ∀ r : α → Prop, r ∈ s → r a := by
  rw [sInf_apply]
  simp [← eq_iff_iff]
#align unary_relation_Inf_iff unary_relation_sInf_iff

theorem binary_relation_sSup_iff {α β : Type*} (s : Set (α → β → Prop)) {a : α} {b : β} :
    sSup s a b ↔ ∃ r : α → β → Prop, r ∈ s ∧ r a b := by
  rw [sSup_apply]
  simp [← eq_iff_iff]
#align binary_relation_Sup_iff binary_relation_sSup_iff

theorem binary_relation_sInf_iff {α β : Type*} (s : Set (α → β → Prop)) {a : α} {b : β} :
    sInf s a b ↔ ∀ r : α → β → Prop, r ∈ s → r a b := by
  rw [sInf_apply]
  simp [← eq_iff_iff]
#align binary_relation_Inf_iff binary_relation_sInf_iff

section CompleteLattice

variable [Preorder α] [CompleteLattice β]

theorem monotone_sSup_of_monotone {s : Set (α → β)} (m_s : ∀ f ∈ s, Monotone f) :
    Monotone (sSup s) := fun _ _ h => iSup_mono fun f => m_s f f.2 h
#align monotone_Sup_of_monotone monotone_sSup_of_monotone

theorem monotone_sInf_of_monotone {s : Set (α → β)} (m_s : ∀ f ∈ s, Monotone f) :
    Monotone (sInf s) := fun _ _ h => iInf_mono fun f => m_s f f.2 h
#align monotone_Inf_of_monotone monotone_sInf_of_monotone

end CompleteLattice

namespace Prod

variable (α β)

instance supSet [SupSet α] [SupSet β] : SupSet (α × β) :=
  ⟨fun s => (sSup (Prod.fst '' s), sSup (Prod.snd '' s))⟩

instance infSet [InfSet α] [InfSet β] : InfSet (α × β) :=
  ⟨fun s => (sInf (Prod.fst '' s), sInf (Prod.snd '' s))⟩

variable {α β}

theorem fst_sInf [InfSet α] [InfSet β] (s : Set (α × β)) : (sInf s).fst = sInf (Prod.fst '' s) :=
  rfl
#align prod.fst_Inf Prod.fst_sInf

theorem snd_sInf [InfSet α] [InfSet β] (s : Set (α × β)) : (sInf s).snd = sInf (Prod.snd '' s) :=
  rfl
#align prod.snd_Inf Prod.snd_sInf

theorem swap_sInf [InfSet α] [InfSet β] (s : Set (α × β)) : (sInf s).swap = sInf (Prod.swap '' s) :=
  ext (congr_arg sInf <| image_comp Prod.fst swap s : _)
    (congr_arg sInf <| image_comp Prod.snd swap s : _)
#align prod.swap_Inf Prod.swap_sInf

theorem fst_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).fst = sSup (Prod.fst '' s) :=
  rfl
#align prod.fst_Sup Prod.fst_sSup

theorem snd_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).snd = sSup (Prod.snd '' s) :=
  rfl
#align prod.snd_Sup Prod.snd_sSup

theorem swap_sSup [SupSet α] [SupSet β] (s : Set (α × β)) : (sSup s).swap = sSup (Prod.swap '' s) :=
  ext (congr_arg sSup <| image_comp Prod.fst swap s : _)
    (congr_arg sSup <| image_comp Prod.snd swap s : _)
#align prod.swap_Sup Prod.swap_sSup

theorem fst_iInf [InfSet α] [InfSet β] (f : ι → α × β) : (iInf f).fst = ⨅ i, (f i).fst :=
  congr_arg sInf (range_comp _ _).symm
#align prod.fst_infi Prod.fst_iInf

theorem snd_iInf [InfSet α] [InfSet β] (f : ι → α × β) : (iInf f).snd = ⨅ i, (f i).snd :=
  congr_arg sInf (range_comp _ _).symm
#align prod.snd_infi Prod.snd_iInf

theorem swap_iInf [InfSet α] [InfSet β] (f : ι → α × β) : (iInf f).swap = ⨅ i, (f i).swap := by
  simp_rw [iInf, swap_sInf, ← range_comp, Function.comp]  -- Porting note: need to unfold `∘`
#align prod.swap_infi Prod.swap_iInf

theorem iInf_mk [InfSet α] [InfSet β] (f : ι → α) (g : ι → β) :
    ⨅ i, (f i, g i) = (⨅ i, f i, ⨅ i, g i) :=
  congr_arg₂ Prod.mk (fst_iInf _) (snd_iInf _)
#align prod.infi_mk Prod.iInf_mk

theorem fst_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).fst = ⨆ i, (f i).fst :=
  congr_arg sSup (range_comp _ _).symm
#align prod.fst_supr Prod.fst_iSup

theorem snd_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).snd = ⨆ i, (f i).snd :=
  congr_arg sSup (range_comp _ _).symm
#align prod.snd_supr Prod.snd_iSup

theorem swap_iSup [SupSet α] [SupSet β] (f : ι → α × β) : (iSup f).swap = ⨆ i, (f i).swap := by
  simp_rw [iSup, swap_sSup, ← range_comp, Function.comp]  -- Porting note: need to unfold `∘`
#align prod.swap_supr Prod.swap_iSup

theorem iSup_mk [SupSet α] [SupSet β] (f : ι → α) (g : ι → β) :
    ⨆ i, (f i, g i) = (⨆ i, f i, ⨆ i, g i) :=
  congr_arg₂ Prod.mk (fst_iSup _) (snd_iSup _)
#align prod.supr_mk Prod.iSup_mk

instance instCompleteLattice [CompleteLattice α] [CompleteLattice β] : CompleteLattice (α × β) where
  __ := instBoundedOrder α β
  le_sSup _ _ hab := ⟨le_sSup <| mem_image_of_mem _ hab, le_sSup <| mem_image_of_mem _ hab⟩
  sSup_le _ _ h :=
    ⟨sSup_le <| forall_mem_image.2 fun p hp => (h p hp).1,
      sSup_le <| forall_mem_image.2 fun p hp => (h p hp).2⟩
  sInf_le _ _ hab := ⟨sInf_le <| mem_image_of_mem _ hab, sInf_le <| mem_image_of_mem _ hab⟩
  le_sInf _ _ h :=
    ⟨le_sInf <| forall_mem_image.2 fun p hp => (h p hp).1,
      le_sInf <| forall_mem_image.2 fun p hp => (h p hp).2⟩

end Prod

lemma sInf_prod [InfSet α] [InfSet β] {s : Set α} {t : Set β} (hs : s.Nonempty) (ht : t.Nonempty) :
    sInf (s ×ˢ t) = (sInf s, sInf t) :=
congr_arg₂ Prod.mk (congr_arg sInf <| fst_image_prod _ ht) (congr_arg sInf <| snd_image_prod hs _)
#align Inf_prod sInf_prod

lemma sSup_prod [SupSet α] [SupSet β] {s : Set α} {t : Set β} (hs : s.Nonempty) (ht : t.Nonempty) :
    sSup (s ×ˢ t) = (sSup s, sSup t) :=
congr_arg₂ Prod.mk (congr_arg sSup <| fst_image_prod _ ht) (congr_arg sSup <| snd_image_prod hs _)
#align Sup_prod sSup_prod

section CompleteLattice

variable [CompleteLattice α] {a : α} {s : Set α}

/-- This is a weaker version of `sup_sInf_eq` -/
theorem sup_sInf_le_iInf_sup : a ⊔ sInf s ≤ ⨅ b ∈ s, a ⊔ b :=
  le_iInf₂ fun _ h => sup_le_sup_left (sInf_le h) _
#align sup_Inf_le_infi_sup sup_sInf_le_iInf_sup

/-- This is a weaker version of `inf_sSup_eq` -/
theorem iSup_inf_le_inf_sSup : ⨆ b ∈ s, a ⊓ b ≤ a ⊓ sSup s :=
  @sup_sInf_le_iInf_sup αᵒᵈ _ _ _
#align supr_inf_le_inf_Sup iSup_inf_le_inf_sSup

/-- This is a weaker version of `sInf_sup_eq` -/
theorem sInf_sup_le_iInf_sup : sInf s ⊔ a ≤ ⨅ b ∈ s, b ⊔ a :=
  le_iInf₂ fun _ h => sup_le_sup_right (sInf_le h) _
#align Inf_sup_le_infi_sup sInf_sup_le_iInf_sup

/-- This is a weaker version of `sSup_inf_eq` -/
theorem iSup_inf_le_sSup_inf : ⨆ b ∈ s, b ⊓ a ≤ sSup s ⊓ a :=
  @sInf_sup_le_iInf_sup αᵒᵈ _ _ _
#align supr_inf_le_Sup_inf iSup_inf_le_sSup_inf

theorem le_iSup_inf_iSup (f g : ι → α) : ⨆ i, f i ⊓ g i ≤ (⨆ i, f i) ⊓ ⨆ i, g i :=
  le_inf (iSup_mono fun _ => inf_le_left) (iSup_mono fun _ => inf_le_right)
#align le_supr_inf_supr le_iSup_inf_iSup

theorem iInf_sup_iInf_le (f g : ι → α) : (⨅ i, f i) ⊔ ⨅ i, g i ≤ ⨅ i, f i ⊔ g i :=
  @le_iSup_inf_iSup αᵒᵈ ι _ f g
#align infi_sup_infi_le iInf_sup_iInf_le

theorem disjoint_sSup_left {a : Set α} {b : α} (d : Disjoint (sSup a) b) {i} (hi : i ∈ a) :
    Disjoint i b :=
  disjoint_iff_inf_le.mpr (iSup₂_le_iff.1 (iSup_inf_le_sSup_inf.trans d.le_bot) i hi : _)
#align disjoint_Sup_left disjoint_sSup_left

theorem disjoint_sSup_right {a : Set α} {b : α} (d : Disjoint b (sSup a)) {i} (hi : i ∈ a) :
    Disjoint b i :=
  disjoint_iff_inf_le.mpr (iSup₂_le_iff.mp (iSup_inf_le_inf_sSup.trans d.le_bot) i hi : _)
#align disjoint_Sup_right disjoint_sSup_right

end CompleteLattice

-- See note [reducible non-instances]
/-- Pullback a `CompleteLattice` along an injection. -/
protected abbrev Function.Injective.completeLattice [Sup α] [Inf α] [SupSet α] [InfSet α] [Top α]
    [Bot α] [CompleteLattice β] (f : α → β) (hf : Function.Injective f)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b)
    (map_sSup : ∀ s, f (sSup s) = ⨆ a ∈ s, f a) (map_sInf : ∀ s, f (sInf s) = ⨅ a ∈ s, f a)
    (map_top : f ⊤ = ⊤) (map_bot : f ⊥ = ⊥) : CompleteLattice α where
  -- we cannot use BoundedOrder.lift here as the `LE` instance doesn't exist yet
  __ := hf.lattice f map_sup map_inf
  le_sSup _ a h := (le_iSup₂ a h).trans (map_sSup _).ge
  sSup_le _ _ h := (map_sSup _).trans_le <| iSup₂_le h
  sInf_le _ a h := (map_sInf _).trans_le <| iInf₂_le a h
  le_sInf _ _ h := (le_iInf₂ h).trans (map_sInf _).ge
  top := ⊤
  le_top _ := (@le_top β _ _ _).trans map_top.ge
  bot := ⊥
  bot_le _ := map_bot.le.trans bot_le
#align function.injective.complete_lattice Function.Injective.completeLattice

namespace ULift

universe v

instance supSet [SupSet α] : SupSet (ULift.{v} α) where sSup s := ULift.up (sSup <| ULift.up ⁻¹' s)

theorem down_sSup [SupSet α] (s : Set (ULift.{v} α)) : (sSup s).down = sSup (ULift.up ⁻¹' s) := rfl
theorem up_sSup [SupSet α] (s : Set α) : up (sSup s) = sSup (ULift.down ⁻¹' s) := rfl

instance infSet [InfSet α] : InfSet (ULift.{v} α) where sInf s := ULift.up (sInf <| ULift.up ⁻¹' s)

theorem down_sInf [InfSet α] (s : Set (ULift.{v} α)) : (sInf s).down = sInf (ULift.up ⁻¹' s) := rfl
theorem up_sInf [InfSet α] (s : Set α) : up (sInf s) = sInf (ULift.down ⁻¹' s) := rfl

theorem down_iSup [SupSet α] (f : ι → ULift.{v} α) : (⨆ i, f i).down = ⨆ i, (f i).down :=
  congr_arg sSup <| (preimage_eq_iff_eq_image ULift.up_bijective).mpr <|
    Eq.symm (range_comp _ _).symm
theorem up_iSup [SupSet α] (f : ι → α) : up (⨆ i, f i) = ⨆ i, up (f i) :=
  congr_arg ULift.up <| (down_iSup _).symm

theorem down_iInf [InfSet α] (f : ι → ULift.{v} α) : (⨅ i, f i).down = ⨅ i, (f i).down :=
  congr_arg sInf <| (preimage_eq_iff_eq_image ULift.up_bijective).mpr <|
    Eq.symm (range_comp _ _).symm
theorem up_iInf [InfSet α] (f : ι → α) : up (⨅ i, f i) = ⨅ i, up (f i) :=
  congr_arg ULift.up <| (down_iInf _).symm

instance instCompleteLattice [CompleteLattice α] : CompleteLattice (ULift.{v} α) :=
  ULift.down_injective.completeLattice _ down_sup down_inf
    (fun s => by rw [sSup_eq_iSup', down_iSup, iSup_subtype''])
    (fun s => by rw [sInf_eq_iInf', down_iInf, iInf_subtype'']) down_top down_bot

end ULift
