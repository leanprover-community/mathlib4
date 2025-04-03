/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Defs
import Mathlib.Order.Lattice

#align_import order.monotone.monovary from "leanprover-community/mathlib"@"6cb77a8eaff0ddd100e87b1591c6d3ad319514ff"

/-!
# Monovariance of functions

Two functions *vary together* if a strict change in the first implies a change in the second.

This is in some sense a way to say that two functions `f : ι → α`, `g : ι → β` are "monotone
together", without actually having an order on `ι`.

This condition comes up in the rearrangement inequality. See `Algebra.Order.Rearrangement`.

## Main declarations

* `Monovary f g`: `f` monovaries with `g`. If `g i < g j`, then `f i ≤ f j`.
* `Antivary f g`: `f` antivaries with `g`. If `g i < g j`, then `f j ≤ f i`.
* `MonovaryOn f g s`: `f` monovaries with `g` on `s`.
* `MonovaryOn f g s`: `f` antivaries with `g` on `s`.
-/


open Function Set

variable {ι ι' α β γ : Type*}

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] {f : ι → α} {f' : α → γ} {g : ι → β} {g' : β → γ}
  {s t : Set ι}

/-- `f` monovaries with `g` if `g i < g j` implies `f i ≤ f j`. -/
def Monovary (f : ι → α) (g : ι → β) : Prop :=
  ∀ ⦃i j⦄, g i < g j → f i ≤ f j
#align monovary Monovary

/-- `f` antivaries with `g` if `g i < g j` implies `f j ≤ f i`. -/
def Antivary (f : ι → α) (g : ι → β) : Prop :=
  ∀ ⦃i j⦄, g i < g j → f j ≤ f i
#align antivary Antivary

/-- `f` monovaries with `g` on `s` if `g i < g j` implies `f i ≤ f j` for all `i, j ∈ s`. -/
def MonovaryOn (f : ι → α) (g : ι → β) (s : Set ι) : Prop :=
  ∀ ⦃i⦄ (_ : i ∈ s) ⦃j⦄ (_ : j ∈ s), g i < g j → f i ≤ f j
#align monovary_on MonovaryOn

/-- `f` antivaries with `g` on `s` if `g i < g j` implies `f j ≤ f i` for all `i, j ∈ s`. -/
def AntivaryOn (f : ι → α) (g : ι → β) (s : Set ι) : Prop :=
  ∀ ⦃i⦄ (_ : i ∈ s) ⦃j⦄ (_ : j ∈ s), g i < g j → f j ≤ f i
#align antivary_on AntivaryOn

protected theorem Monovary.monovaryOn (h : Monovary f g) (s : Set ι) : MonovaryOn f g s :=
  fun _ _ _ _ hij => h hij
#align monovary.monovary_on Monovary.monovaryOn

protected theorem Antivary.antivaryOn (h : Antivary f g) (s : Set ι) : AntivaryOn f g s :=
  fun _ _ _ _ hij => h hij
#align antivary.antivary_on Antivary.antivaryOn

@[simp]
theorem MonovaryOn.empty : MonovaryOn f g ∅ := fun _ => False.elim
#align monovary_on.empty MonovaryOn.empty

@[simp]
theorem AntivaryOn.empty : AntivaryOn f g ∅ := fun _ => False.elim
#align antivary_on.empty AntivaryOn.empty

@[simp]
theorem monovaryOn_univ : MonovaryOn f g univ ↔ Monovary f g :=
  ⟨fun h _ _ => h trivial trivial, fun h _ _ _ _ hij => h hij⟩
#align monovary_on_univ monovaryOn_univ

@[simp]
theorem antivaryOn_univ : AntivaryOn f g univ ↔ Antivary f g :=
  ⟨fun h _ _ => h trivial trivial, fun h _ _ _ _ hij => h hij⟩
#align antivary_on_univ antivaryOn_univ

protected theorem MonovaryOn.subset (hst : s ⊆ t) (h : MonovaryOn f g t) : MonovaryOn f g s :=
  fun _ hi _ hj => h (hst hi) (hst hj)
#align monovary_on.subset MonovaryOn.subset

protected theorem AntivaryOn.subset (hst : s ⊆ t) (h : AntivaryOn f g t) : AntivaryOn f g s :=
  fun _ hi _ hj => h (hst hi) (hst hj)
#align antivary_on.subset AntivaryOn.subset

theorem monovary_const_left (g : ι → β) (a : α) : Monovary (const ι a) g := fun _ _ _ => le_rfl
#align monovary_const_left monovary_const_left

theorem antivary_const_left (g : ι → β) (a : α) : Antivary (const ι a) g := fun _ _ _ => le_rfl
#align antivary_const_left antivary_const_left

theorem monovary_const_right (f : ι → α) (b : β) : Monovary f (const ι b) := fun _ _ h =>
  (h.ne rfl).elim
#align monovary_const_right monovary_const_right

theorem antivary_const_right (f : ι → α) (b : β) : Antivary f (const ι b) := fun _ _ h =>
  (h.ne rfl).elim
#align antivary_const_right antivary_const_right

theorem monovary_self (f : ι → α) : Monovary f f := fun _ _ => le_of_lt
#align monovary_self monovary_self

theorem monovaryOn_self (f : ι → α) (s : Set ι) : MonovaryOn f f s := fun _ _ _ _ => le_of_lt
#align monovary_on_self monovaryOn_self

protected theorem Subsingleton.monovary [Subsingleton ι] (f : ι → α) (g : ι → β) : Monovary f g :=
  fun _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim
#align subsingleton.monovary Subsingleton.monovary

protected theorem Subsingleton.antivary [Subsingleton ι] (f : ι → α) (g : ι → β) : Antivary f g :=
  fun _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim
#align subsingleton.antivary Subsingleton.antivary

protected theorem Subsingleton.monovaryOn [Subsingleton ι] (f : ι → α) (g : ι → β) (s : Set ι) :
    MonovaryOn f g s := fun _ _ _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim
#align subsingleton.monovary_on Subsingleton.monovaryOn

protected theorem Subsingleton.antivaryOn [Subsingleton ι] (f : ι → α) (g : ι → β) (s : Set ι) :
    AntivaryOn f g s := fun _ _ _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim
#align subsingleton.antivary_on Subsingleton.antivaryOn

theorem monovaryOn_const_left (g : ι → β) (a : α) (s : Set ι) : MonovaryOn (const ι a) g s :=
  fun _ _ _ _ _ => le_rfl
#align monovary_on_const_left monovaryOn_const_left

theorem antivaryOn_const_left (g : ι → β) (a : α) (s : Set ι) : AntivaryOn (const ι a) g s :=
  fun _ _ _ _ _ => le_rfl
#align antivary_on_const_left antivaryOn_const_left

theorem monovaryOn_const_right (f : ι → α) (b : β) (s : Set ι) : MonovaryOn f (const ι b) s :=
  fun _ _ _ _ h => (h.ne rfl).elim
#align monovary_on_const_right monovaryOn_const_right

theorem antivaryOn_const_right (f : ι → α) (b : β) (s : Set ι) : AntivaryOn f (const ι b) s :=
  fun _ _ _ _ h => (h.ne rfl).elim
#align antivary_on_const_right antivaryOn_const_right

theorem Monovary.comp_right (h : Monovary f g) (k : ι' → ι) : Monovary (f ∘ k) (g ∘ k) :=
  fun _ _ hij => h hij
#align monovary.comp_right Monovary.comp_right

theorem Antivary.comp_right (h : Antivary f g) (k : ι' → ι) : Antivary (f ∘ k) (g ∘ k) :=
  fun _ _ hij => h hij
#align antivary.comp_right Antivary.comp_right

theorem MonovaryOn.comp_right (h : MonovaryOn f g s) (k : ι' → ι) :
    MonovaryOn (f ∘ k) (g ∘ k) (k ⁻¹' s) := fun _ hi _ hj => h hi hj
#align monovary_on.comp_right MonovaryOn.comp_right

theorem AntivaryOn.comp_right (h : AntivaryOn f g s) (k : ι' → ι) :
    AntivaryOn (f ∘ k) (g ∘ k) (k ⁻¹' s) := fun _ hi _ hj => h hi hj
#align antivary_on.comp_right AntivaryOn.comp_right

theorem Monovary.comp_monotone_left (h : Monovary f g) (hf : Monotone f') : Monovary (f' ∘ f) g :=
  fun _ _ hij => hf <| h hij
#align monovary.comp_monotone_left Monovary.comp_monotone_left

theorem Monovary.comp_antitone_left (h : Monovary f g) (hf : Antitone f') : Antivary (f' ∘ f) g :=
  fun _ _ hij => hf <| h hij
#align monovary.comp_antitone_left Monovary.comp_antitone_left

theorem Antivary.comp_monotone_left (h : Antivary f g) (hf : Monotone f') : Antivary (f' ∘ f) g :=
  fun _ _ hij => hf <| h hij
#align antivary.comp_monotone_left Antivary.comp_monotone_left

theorem Antivary.comp_antitone_left (h : Antivary f g) (hf : Antitone f') : Monovary (f' ∘ f) g :=
  fun _ _ hij => hf <| h hij
#align antivary.comp_antitone_left Antivary.comp_antitone_left

theorem MonovaryOn.comp_monotone_on_left (h : MonovaryOn f g s) (hf : Monotone f') :
    MonovaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf <| h hi hj hij
#align monovary_on.comp_monotone_on_left MonovaryOn.comp_monotone_on_left

theorem MonovaryOn.comp_antitone_on_left (h : MonovaryOn f g s) (hf : Antitone f') :
    AntivaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf <| h hi hj hij
#align monovary_on.comp_antitone_on_left MonovaryOn.comp_antitone_on_left

theorem AntivaryOn.comp_monotone_on_left (h : AntivaryOn f g s) (hf : Monotone f') :
    AntivaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf <| h hi hj hij
#align antivary_on.comp_monotone_on_left AntivaryOn.comp_monotone_on_left

theorem AntivaryOn.comp_antitone_on_left (h : AntivaryOn f g s) (hf : Antitone f') :
    MonovaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf <| h hi hj hij
#align antivary_on.comp_antitone_on_left AntivaryOn.comp_antitone_on_left

section OrderDual

open OrderDual

theorem Monovary.dual : Monovary f g → Monovary (toDual ∘ f) (toDual ∘ g) :=
  swap
#align monovary.dual Monovary.dual

theorem Antivary.dual : Antivary f g → Antivary (toDual ∘ f) (toDual ∘ g) :=
  swap
#align antivary.dual Antivary.dual

theorem Monovary.dual_left : Monovary f g → Antivary (toDual ∘ f) g :=
  id
#align monovary.dual_left Monovary.dual_left

theorem Antivary.dual_left : Antivary f g → Monovary (toDual ∘ f) g :=
  id
#align antivary.dual_left Antivary.dual_left

theorem Monovary.dual_right : Monovary f g → Antivary f (toDual ∘ g) :=
  swap
#align monovary.dual_right Monovary.dual_right

theorem Antivary.dual_right : Antivary f g → Monovary f (toDual ∘ g) :=
  swap
#align antivary.dual_right Antivary.dual_right

theorem MonovaryOn.dual : MonovaryOn f g s → MonovaryOn (toDual ∘ f) (toDual ∘ g) s :=
  swap₂
#align monovary_on.dual MonovaryOn.dual

theorem AntivaryOn.dual : AntivaryOn f g s → AntivaryOn (toDual ∘ f) (toDual ∘ g) s :=
  swap₂
#align antivary_on.dual AntivaryOn.dual

theorem MonovaryOn.dual_left : MonovaryOn f g s → AntivaryOn (toDual ∘ f) g s :=
  id
#align monovary_on.dual_left MonovaryOn.dual_left

theorem AntivaryOn.dual_left : AntivaryOn f g s → MonovaryOn (toDual ∘ f) g s :=
  id
#align antivary_on.dual_left AntivaryOn.dual_left

theorem MonovaryOn.dual_right : MonovaryOn f g s → AntivaryOn f (toDual ∘ g) s :=
  swap₂
#align monovary_on.dual_right MonovaryOn.dual_right

theorem AntivaryOn.dual_right : AntivaryOn f g s → MonovaryOn f (toDual ∘ g) s :=
  swap₂
#align antivary_on.dual_right AntivaryOn.dual_right

@[simp]
theorem monovary_toDual_left : Monovary (toDual ∘ f) g ↔ Antivary f g :=
  Iff.rfl
#align monovary_to_dual_left monovary_toDual_left

@[simp]
theorem monovary_toDual_right : Monovary f (toDual ∘ g) ↔ Antivary f g :=
  forall_swap
#align monovary_to_dual_right monovary_toDual_right

@[simp]
theorem antivary_toDual_left : Antivary (toDual ∘ f) g ↔ Monovary f g :=
  Iff.rfl
#align antivary_to_dual_left antivary_toDual_left

@[simp]
theorem antivary_toDual_right : Antivary f (toDual ∘ g) ↔ Monovary f g :=
  forall_swap
#align antivary_to_dual_right antivary_toDual_right

@[simp]
theorem monovaryOn_toDual_left : MonovaryOn (toDual ∘ f) g s ↔ AntivaryOn f g s :=
  Iff.rfl
#align monovary_on_to_dual_left monovaryOn_toDual_left

@[simp]
theorem monovaryOn_toDual_right : MonovaryOn f (toDual ∘ g) s ↔ AntivaryOn f g s :=
  forall₂_swap
#align monovary_on_to_dual_right monovaryOn_toDual_right

@[simp]
theorem antivaryOn_toDual_left : AntivaryOn (toDual ∘ f) g s ↔ MonovaryOn f g s :=
  Iff.rfl
#align antivary_on_to_dual_left antivaryOn_toDual_left

@[simp]
theorem antivaryOn_toDual_right : AntivaryOn f (toDual ∘ g) s ↔ MonovaryOn f g s :=
  forall₂_swap
#align antivary_on_to_dual_right antivaryOn_toDual_right

end OrderDual

section PartialOrder

variable [PartialOrder ι]

@[simp]
theorem monovary_id_iff : Monovary f id ↔ Monotone f :=
  monotone_iff_forall_lt.symm
#align monovary_id_iff monovary_id_iff

@[simp]
theorem antivary_id_iff : Antivary f id ↔ Antitone f :=
  antitone_iff_forall_lt.symm
#align antivary_id_iff antivary_id_iff

@[simp]
theorem monovaryOn_id_iff : MonovaryOn f id s ↔ MonotoneOn f s :=
  monotoneOn_iff_forall_lt.symm
#align monovary_on_id_iff monovaryOn_id_iff

@[simp]
theorem antivaryOn_id_iff : AntivaryOn f id s ↔ AntitoneOn f s :=
  antitoneOn_iff_forall_lt.symm
#align antivary_on_id_iff antivaryOn_id_iff

end PartialOrder

variable [LinearOrder ι]

/- Porting note: Due to a bug in `alias`, many of the below lemmas have dot notation removed in the
proof-/

protected theorem Monotone.monovary (hf : Monotone f) (hg : Monotone g) : Monovary f g :=
  fun _ _ hij => hf (hg.reflect_lt hij).le
#align monotone.monovary Monotone.monovary

protected theorem Monotone.antivary (hf : Monotone f) (hg : Antitone g) : Antivary f g :=
  (hf.monovary hg.dual_right).dual_right
#align monotone.antivary Monotone.antivary

protected theorem Antitone.monovary (hf : Antitone f) (hg : Antitone g) : Monovary f g :=
  (hf.dual_right.antivary hg).dual_left
#align antitone.monovary Antitone.monovary

protected theorem Antitone.antivary (hf : Antitone f) (hg : Monotone g) : Antivary f g :=
  (hf.monovary hg.dual_right).dual_right
#align antitone.antivary Antitone.antivary

protected theorem MonotoneOn.monovaryOn (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonovaryOn f g s := fun _ hi _ hj hij => hf hi hj (hg.reflect_lt hi hj hij).le
#align monotone_on.monovary_on MonotoneOn.monovaryOn

protected theorem MonotoneOn.antivaryOn (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntivaryOn f g s :=
  (hf.monovaryOn hg.dual_right).dual_right
#align monotone_on.antivary_on MonotoneOn.antivaryOn

protected theorem AntitoneOn.monovaryOn (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    MonovaryOn f g s :=
  (hf.dual_right.antivaryOn hg).dual_left
#align antitone_on.monovary_on AntitoneOn.monovaryOn

protected theorem AntitoneOn.antivaryOn (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    AntivaryOn f g s :=
  (hf.monovaryOn hg.dual_right).dual_right
#align antitone_on.antivary_on AntitoneOn.antivaryOn

end Preorder

section LinearOrder

variable [Preorder α] [LinearOrder β] [Preorder γ] {f : ι → α} {f' : α → γ} {g : ι → β} {g' : β → γ}
  {s : Set ι}

theorem MonovaryOn.comp_monotoneOn_right (h : MonovaryOn f g s) (hg : MonotoneOn g' (g '' s)) :
    MonovaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
  h hi hj <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
#align monovary_on.comp_monotone_on_right MonovaryOn.comp_monotoneOn_right

theorem MonovaryOn.comp_antitoneOn_right (h : MonovaryOn f g s) (hg : AntitoneOn g' (g '' s)) :
    AntivaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
  h hj hi <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
#align monovary_on.comp_antitone_on_right MonovaryOn.comp_antitoneOn_right

theorem AntivaryOn.comp_monotoneOn_right (h : AntivaryOn f g s) (hg : MonotoneOn g' (g '' s)) :
    AntivaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
  h hi hj <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
#align antivary_on.comp_monotone_on_right AntivaryOn.comp_monotoneOn_right

theorem AntivaryOn.comp_antitoneOn_right (h : AntivaryOn f g s) (hg : AntitoneOn g' (g '' s)) :
    MonovaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
  h hj hi <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij
#align antivary_on.comp_antitone_on_right AntivaryOn.comp_antitoneOn_right

@[symm]
protected theorem Monovary.symm (h : Monovary f g) : Monovary g f := fun _ _ hf =>
  le_of_not_lt fun hg => hf.not_le <| h hg
#align monovary.symm Monovary.symm

@[symm]
protected theorem Antivary.symm (h : Antivary f g) : Antivary g f := fun _ _ hf =>
  le_of_not_lt fun hg => hf.not_le <| h hg
#align antivary.symm Antivary.symm

@[symm]
protected theorem MonovaryOn.symm (h : MonovaryOn f g s) : MonovaryOn g f s := fun _ hi _ hj hf =>
  le_of_not_lt fun hg => hf.not_le <| h hj hi hg
#align monovary_on.symm MonovaryOn.symm

@[symm]
protected theorem AntivaryOn.symm (h : AntivaryOn f g s) : AntivaryOn g f s := fun _ hi _ hj hf =>
  le_of_not_lt fun hg => hf.not_le <| h hi hj hg
#align antivary_on.symm AntivaryOn.symm

end LinearOrder

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : ι → α} {g : ι → β} {s : Set ι}

theorem monovary_comm : Monovary f g ↔ Monovary g f :=
  ⟨Monovary.symm, Monovary.symm⟩
#align monovary_comm monovary_comm

theorem antivary_comm : Antivary f g ↔ Antivary g f :=
  ⟨Antivary.symm, Antivary.symm⟩
#align antivary_comm antivary_comm

theorem monovaryOn_comm : MonovaryOn f g s ↔ MonovaryOn g f s :=
  ⟨MonovaryOn.symm, MonovaryOn.symm⟩
#align monovary_on_comm monovaryOn_comm

theorem antivaryOn_comm : AntivaryOn f g s ↔ AntivaryOn g f s :=
  ⟨AntivaryOn.symm, AntivaryOn.symm⟩
#align antivary_on_comm antivaryOn_comm

end LinearOrder
