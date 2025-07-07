/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Operations
import Mathlib.Order.Lattice

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
* `AntivaryOn f g s`: `f` antivaries with `g` on `s`.
-/


open Function Set

variable {ι ι' α β γ : Type*}

section Preorder

variable [Preorder α] [Preorder β] [Preorder γ] {f : ι → α} {f' : α → γ} {g : ι → β}
  {s t : Set ι}

/-- `f` monovaries with `g` if `g i < g j` implies `f i ≤ f j`. -/
def Monovary (f : ι → α) (g : ι → β) : Prop :=
  ∀ ⦃i j⦄, g i < g j → f i ≤ f j

/-- `f` antivaries with `g` if `g i < g j` implies `f j ≤ f i`. -/
def Antivary (f : ι → α) (g : ι → β) : Prop :=
  ∀ ⦃i j⦄, g i < g j → f j ≤ f i

/-- `f` monovaries with `g` on `s` if `g i < g j` implies `f i ≤ f j` for all `i, j ∈ s`. -/
def MonovaryOn (f : ι → α) (g : ι → β) (s : Set ι) : Prop :=
  ∀ ⦃i⦄ (_ : i ∈ s) ⦃j⦄ (_ : j ∈ s), g i < g j → f i ≤ f j

/-- `f` antivaries with `g` on `s` if `g i < g j` implies `f j ≤ f i` for all `i, j ∈ s`. -/
def AntivaryOn (f : ι → α) (g : ι → β) (s : Set ι) : Prop :=
  ∀ ⦃i⦄ (_ : i ∈ s) ⦃j⦄ (_ : j ∈ s), g i < g j → f j ≤ f i

protected theorem Monovary.monovaryOn (h : Monovary f g) (s : Set ι) : MonovaryOn f g s :=
  fun _ _ _ _ hij => h hij

protected theorem Antivary.antivaryOn (h : Antivary f g) (s : Set ι) : AntivaryOn f g s :=
  fun _ _ _ _ hij => h hij

@[simp]
theorem MonovaryOn.empty : MonovaryOn f g ∅ := fun _ => False.elim

@[simp]
theorem AntivaryOn.empty : AntivaryOn f g ∅ := fun _ => False.elim

@[simp]
theorem monovaryOn_univ : MonovaryOn f g univ ↔ Monovary f g :=
  ⟨fun h _ _ => h trivial trivial, fun h _ _ _ _ hij => h hij⟩

@[simp]
theorem antivaryOn_univ : AntivaryOn f g univ ↔ Antivary f g :=
  ⟨fun h _ _ => h trivial trivial, fun h _ _ _ _ hij => h hij⟩

lemma monovaryOn_iff_monovary : MonovaryOn f g s ↔ Monovary (fun i : s ↦ f i) fun i ↦ g i := by
  simp [Monovary, MonovaryOn]

lemma antivaryOn_iff_antivary : AntivaryOn f g s ↔ Antivary (fun i : s ↦ f i) fun i ↦ g i := by
  simp [Antivary, AntivaryOn]

protected theorem MonovaryOn.subset (hst : s ⊆ t) (h : MonovaryOn f g t) : MonovaryOn f g s :=
  fun _ hi _ hj => h (hst hi) (hst hj)

protected theorem AntivaryOn.subset (hst : s ⊆ t) (h : AntivaryOn f g t) : AntivaryOn f g s :=
  fun _ hi _ hj => h (hst hi) (hst hj)

theorem monovary_const_left (g : ι → β) (a : α) : Monovary (const ι a) g := fun _ _ _ => le_rfl

theorem antivary_const_left (g : ι → β) (a : α) : Antivary (const ι a) g := fun _ _ _ => le_rfl

theorem monovary_const_right (f : ι → α) (b : β) : Monovary f (const ι b) := fun _ _ h =>
  (h.ne rfl).elim

theorem antivary_const_right (f : ι → α) (b : β) : Antivary f (const ι b) := fun _ _ h =>
  (h.ne rfl).elim

theorem monovary_self (f : ι → α) : Monovary f f := fun _ _ => le_of_lt

theorem monovaryOn_self (f : ι → α) (s : Set ι) : MonovaryOn f f s := fun _ _ _ _ => le_of_lt

protected theorem Subsingleton.monovary [Subsingleton ι] (f : ι → α) (g : ι → β) : Monovary f g :=
  fun _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim

protected theorem Subsingleton.antivary [Subsingleton ι] (f : ι → α) (g : ι → β) : Antivary f g :=
  fun _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim

protected theorem Subsingleton.monovaryOn [Subsingleton ι] (f : ι → α) (g : ι → β) (s : Set ι) :
    MonovaryOn f g s := fun _ _ _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim

protected theorem Subsingleton.antivaryOn [Subsingleton ι] (f : ι → α) (g : ι → β) (s : Set ι) :
    AntivaryOn f g s := fun _ _ _ _ h => (ne_of_apply_ne _ h.ne <| Subsingleton.elim _ _).elim

theorem monovaryOn_const_left (g : ι → β) (a : α) (s : Set ι) : MonovaryOn (const ι a) g s :=
  fun _ _ _ _ _ => le_rfl

theorem antivaryOn_const_left (g : ι → β) (a : α) (s : Set ι) : AntivaryOn (const ι a) g s :=
  fun _ _ _ _ _ => le_rfl

theorem monovaryOn_const_right (f : ι → α) (b : β) (s : Set ι) : MonovaryOn f (const ι b) s :=
  fun _ _ _ _ h => (h.ne rfl).elim

theorem antivaryOn_const_right (f : ι → α) (b : β) (s : Set ι) : AntivaryOn f (const ι b) s :=
  fun _ _ _ _ h => (h.ne rfl).elim

theorem Monovary.comp_right (h : Monovary f g) (k : ι' → ι) : Monovary (f ∘ k) (g ∘ k) :=
  fun _ _ hij => h hij

theorem Antivary.comp_right (h : Antivary f g) (k : ι' → ι) : Antivary (f ∘ k) (g ∘ k) :=
  fun _ _ hij => h hij

theorem MonovaryOn.comp_right (h : MonovaryOn f g s) (k : ι' → ι) :
    MonovaryOn (f ∘ k) (g ∘ k) (k ⁻¹' s) := fun _ hi _ hj => h hi hj

theorem AntivaryOn.comp_right (h : AntivaryOn f g s) (k : ι' → ι) :
    AntivaryOn (f ∘ k) (g ∘ k) (k ⁻¹' s) := fun _ hi _ hj => h hi hj

theorem Monovary.comp_monotone_left (h : Monovary f g) (hf : Monotone f') : Monovary (f' ∘ f) g :=
  fun _ _ hij => hf <| h hij

theorem Monovary.comp_antitone_left (h : Monovary f g) (hf : Antitone f') : Antivary (f' ∘ f) g :=
  fun _ _ hij => hf <| h hij

theorem Antivary.comp_monotone_left (h : Antivary f g) (hf : Monotone f') : Antivary (f' ∘ f) g :=
  fun _ _ hij => hf <| h hij

theorem Antivary.comp_antitone_left (h : Antivary f g) (hf : Antitone f') : Monovary (f' ∘ f) g :=
  fun _ _ hij => hf <| h hij

theorem MonovaryOn.comp_monotone_on_left (h : MonovaryOn f g s) (hf : Monotone f') :
    MonovaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf <| h hi hj hij

theorem MonovaryOn.comp_antitone_on_left (h : MonovaryOn f g s) (hf : Antitone f') :
    AntivaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf <| h hi hj hij

theorem AntivaryOn.comp_monotone_on_left (h : AntivaryOn f g s) (hf : Monotone f') :
    AntivaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf <| h hi hj hij

theorem AntivaryOn.comp_antitone_on_left (h : AntivaryOn f g s) (hf : Antitone f') :
    MonovaryOn (f' ∘ f) g s := fun _ hi _ hj hij => hf <| h hi hj hij

section OrderDual

open OrderDual

theorem Monovary.dual : Monovary f g → Monovary (toDual ∘ f) (toDual ∘ g) :=
  swap

theorem Antivary.dual : Antivary f g → Antivary (toDual ∘ f) (toDual ∘ g) :=
  swap

theorem Monovary.dual_left : Monovary f g → Antivary (toDual ∘ f) g :=
  id

theorem Antivary.dual_left : Antivary f g → Monovary (toDual ∘ f) g :=
  id

theorem Monovary.dual_right : Monovary f g → Antivary f (toDual ∘ g) :=
  swap

theorem Antivary.dual_right : Antivary f g → Monovary f (toDual ∘ g) :=
  swap

theorem MonovaryOn.dual : MonovaryOn f g s → MonovaryOn (toDual ∘ f) (toDual ∘ g) s :=
  swap₂

theorem AntivaryOn.dual : AntivaryOn f g s → AntivaryOn (toDual ∘ f) (toDual ∘ g) s :=
  swap₂

theorem MonovaryOn.dual_left : MonovaryOn f g s → AntivaryOn (toDual ∘ f) g s :=
  id

theorem AntivaryOn.dual_left : AntivaryOn f g s → MonovaryOn (toDual ∘ f) g s :=
  id

theorem MonovaryOn.dual_right : MonovaryOn f g s → AntivaryOn f (toDual ∘ g) s :=
  swap₂

theorem AntivaryOn.dual_right : AntivaryOn f g s → MonovaryOn f (toDual ∘ g) s :=
  swap₂

@[simp]
theorem monovary_toDual_left : Monovary (toDual ∘ f) g ↔ Antivary f g :=
  Iff.rfl

@[simp]
theorem monovary_toDual_right : Monovary f (toDual ∘ g) ↔ Antivary f g :=
  forall_swap

@[simp]
theorem antivary_toDual_left : Antivary (toDual ∘ f) g ↔ Monovary f g :=
  Iff.rfl

@[simp]
theorem antivary_toDual_right : Antivary f (toDual ∘ g) ↔ Monovary f g :=
  forall_swap

@[simp]
theorem monovaryOn_toDual_left : MonovaryOn (toDual ∘ f) g s ↔ AntivaryOn f g s :=
  Iff.rfl

@[simp]
theorem monovaryOn_toDual_right : MonovaryOn f (toDual ∘ g) s ↔ AntivaryOn f g s :=
  forall₂_swap

@[simp]
theorem antivaryOn_toDual_left : AntivaryOn (toDual ∘ f) g s ↔ MonovaryOn f g s :=
  Iff.rfl

@[simp]
theorem antivaryOn_toDual_right : AntivaryOn f (toDual ∘ g) s ↔ MonovaryOn f g s :=
  forall₂_swap

end OrderDual

section PartialOrder

variable [PartialOrder ι]

@[simp]
theorem monovary_id_iff : Monovary f id ↔ Monotone f :=
  monotone_iff_forall_lt.symm

@[simp]
theorem antivary_id_iff : Antivary f id ↔ Antitone f :=
  antitone_iff_forall_lt.symm

@[simp]
theorem monovaryOn_id_iff : MonovaryOn f id s ↔ MonotoneOn f s :=
  monotoneOn_iff_forall_lt.symm

@[simp]
theorem antivaryOn_id_iff : AntivaryOn f id s ↔ AntitoneOn f s :=
  antitoneOn_iff_forall_lt.symm

lemma StrictMono.trans_monovary (hf : StrictMono f) (h : Monovary g f) : Monotone g :=
  monotone_iff_forall_lt.2 fun _a _b hab ↦ h <| hf hab

lemma StrictMono.trans_antivary (hf : StrictMono f) (h : Antivary g f) : Antitone g :=
  antitone_iff_forall_lt.2 fun _a _b hab ↦ h <| hf hab

lemma StrictAnti.trans_monovary (hf : StrictAnti f) (h : Monovary g f) : Antitone g :=
  antitone_iff_forall_lt.2 fun _a _b hab ↦ h <| hf hab

lemma StrictAnti.trans_antivary (hf : StrictAnti f) (h : Antivary g f) : Monotone g :=
  monotone_iff_forall_lt.2 fun _a _b hab ↦ h <| hf hab

lemma StrictMonoOn.trans_monovaryOn (hf : StrictMonoOn f s) (h : MonovaryOn g f s) :
    MonotoneOn g s := monotoneOn_iff_forall_lt.2 fun _a ha _b hb hab ↦ h ha hb <| hf ha hb hab

lemma StrictMonoOn.trans_antivaryOn (hf : StrictMonoOn f s) (h : AntivaryOn g f s) :
    AntitoneOn g s := antitoneOn_iff_forall_lt.2 fun _a ha _b hb hab ↦ h ha hb <| hf ha hb hab

lemma StrictAntiOn.trans_monovaryOn (hf : StrictAntiOn f s) (h : MonovaryOn g f s) :
    AntitoneOn g s := antitoneOn_iff_forall_lt.2 fun _a ha _b hb hab ↦ h hb ha <| hf ha hb hab

lemma StrictAntiOn.trans_antivaryOn (hf : StrictAntiOn f s) (h : AntivaryOn g f s) :
    MonotoneOn g s := monotoneOn_iff_forall_lt.2 fun _a ha _b hb hab ↦ h hb ha <| hf ha hb hab

end PartialOrder

variable [LinearOrder ι]

protected theorem Monotone.monovary (hf : Monotone f) (hg : Monotone g) : Monovary f g :=
  fun _ _ hij => hf (hg.reflect_lt hij).le

protected theorem Monotone.antivary (hf : Monotone f) (hg : Antitone g) : Antivary f g :=
  (hf.monovary hg.dual_right).dual_right

protected theorem Antitone.monovary (hf : Antitone f) (hg : Antitone g) : Monovary f g :=
  (hf.dual_right.antivary hg).dual_left

protected theorem Antitone.antivary (hf : Antitone f) (hg : Monotone g) : Antivary f g :=
  (hf.monovary hg.dual_right).dual_right

protected theorem MonotoneOn.monovaryOn (hf : MonotoneOn f s) (hg : MonotoneOn g s) :
    MonovaryOn f g s := fun _ hi _ hj hij => hf hi hj (hg.reflect_lt hi hj hij).le

protected theorem MonotoneOn.antivaryOn (hf : MonotoneOn f s) (hg : AntitoneOn g s) :
    AntivaryOn f g s :=
  (hf.monovaryOn hg.dual_right).dual_right

protected theorem AntitoneOn.monovaryOn (hf : AntitoneOn f s) (hg : AntitoneOn g s) :
    MonovaryOn f g s :=
  (hf.dual_right.antivaryOn hg).dual_left

protected theorem AntitoneOn.antivaryOn (hf : AntitoneOn f s) (hg : MonotoneOn g s) :
    AntivaryOn f g s :=
  (hf.monovaryOn hg.dual_right).dual_right

end Preorder

section LinearOrder

variable [Preorder α] [LinearOrder β] [Preorder γ] {f : ι → α} {g : ι → β} {g' : β → γ}
  {s : Set ι}

theorem MonovaryOn.comp_monotoneOn_right (h : MonovaryOn f g s) (hg : MonotoneOn g' (g '' s)) :
    MonovaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
  h hi hj <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

theorem MonovaryOn.comp_antitoneOn_right (h : MonovaryOn f g s) (hg : AntitoneOn g' (g '' s)) :
    AntivaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
  h hj hi <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

theorem AntivaryOn.comp_monotoneOn_right (h : AntivaryOn f g s) (hg : MonotoneOn g' (g '' s)) :
    AntivaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
  h hi hj <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

theorem AntivaryOn.comp_antitoneOn_right (h : AntivaryOn f g s) (hg : AntitoneOn g' (g '' s)) :
    MonovaryOn f (g' ∘ g) s := fun _ hi _ hj hij =>
  h hj hi <| hg.reflect_lt (mem_image_of_mem _ hi) (mem_image_of_mem _ hj) hij

@[symm]
protected theorem Monovary.symm (h : Monovary f g) : Monovary g f := fun _ _ hf =>
  le_of_not_gt fun hg => hf.not_ge <| h hg

@[symm]
protected theorem Antivary.symm (h : Antivary f g) : Antivary g f := fun _ _ hf =>
  le_of_not_gt fun hg => hf.not_ge <| h hg

@[symm]
protected theorem MonovaryOn.symm (h : MonovaryOn f g s) : MonovaryOn g f s := fun _ hi _ hj hf =>
  le_of_not_gt fun hg => hf.not_ge <| h hj hi hg

@[symm]
protected theorem AntivaryOn.symm (h : AntivaryOn f g s) : AntivaryOn g f s := fun _ hi _ hj hf =>
  le_of_not_gt fun hg => hf.not_ge <| h hi hj hg

end LinearOrder

section LinearOrder

variable [LinearOrder α] [LinearOrder β] {f : ι → α} {g : ι → β} {s : Set ι}

theorem monovary_comm : Monovary f g ↔ Monovary g f :=
  ⟨Monovary.symm, Monovary.symm⟩

theorem antivary_comm : Antivary f g ↔ Antivary g f :=
  ⟨Antivary.symm, Antivary.symm⟩

theorem monovaryOn_comm : MonovaryOn f g s ↔ MonovaryOn g f s :=
  ⟨MonovaryOn.symm, MonovaryOn.symm⟩

theorem antivaryOn_comm : AntivaryOn f g s ↔ AntivaryOn g f s :=
  ⟨AntivaryOn.symm, AntivaryOn.symm⟩

end LinearOrder
