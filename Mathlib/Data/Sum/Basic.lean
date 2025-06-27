/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury Kudryashov
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Additional lemmas about sum types

Most of the former contents of this file have been moved to Batteries.
-/


universe u v w x

variable {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {γ δ : Type*}

lemma not_isLeft_and_isRight {x : α ⊕ β} : ¬(x.isLeft ∧ x.isRight) := by simp

namespace Sum

@[simp]
theorem elim_swap {α β γ : Type*} {f : α → γ} {g : β → γ} :
    Sum.elim f g ∘ Sum.swap = Sum.elim g f := by
  ext x
  cases x with
  | inl x => simp
  | inr x => simp

-- Lean has removed the `@[simp]` attribute on these. For now Mathlib adds it back.
attribute [simp] Sum.forall Sum.exists

theorem exists_sum {γ : α ⊕ β → Sort*} (p : (∀ ab, γ ab) → Prop) :
    (∃ fab, p fab) ↔ (∃ fa fb, p (Sum.rec fa fb)) := by
  rw [← not_forall_not, forall_sum]
  simp

theorem inl_injective : Function.Injective (inl : α → α ⊕ β) := fun _ _ ↦ inl.inj

theorem inr_injective : Function.Injective (inr : β → α ⊕ β) := fun _ _ ↦ inr.inj

theorem sum_rec_congr (P : α ⊕ β → Sort*) (f : ∀ i, P (inl i)) (g : ∀ i, P (inr i))
    {x y : α ⊕ β} (h : x = y) :
    @Sum.rec _ _ _ f g x = cast (congr_arg P h.symm) (@Sum.rec _ _ _ f g y) := by cases h; rfl

section get

variable {x : α ⊕ β}

theorem eq_left_iff_getLeft_eq {a : α} : x = inl a ↔ ∃ h, x.getLeft h = a := by
  cases x <;> simp

theorem eq_right_iff_getRight_eq {b : β} : x = inr b ↔ ∃ h, x.getRight h = b := by
  cases x <;> simp

theorem getLeft_eq_getLeft? (h₁ : x.isLeft) (h₂ : x.getLeft?.isSome) :
    x.getLeft h₁ = x.getLeft?.get h₂ := by simp [← getLeft?_eq_some_iff]

theorem getRight_eq_getRight? (h₁ : x.isRight) (h₂ : x.getRight?.isSome) :
    x.getRight h₁ = x.getRight?.get h₂ := by simp [← getRight?_eq_some_iff]

@[simp] theorem isSome_getLeft?_iff_isLeft : x.getLeft?.isSome ↔ x.isLeft := by
  rw [isLeft_iff, Option.isSome_iff_exists]; simp

@[simp] theorem isSome_getRight?_iff_isRight : x.getRight?.isSome ↔ x.isRight := by
  rw [isRight_iff, Option.isSome_iff_exists]; simp

end get

open Function (update update_eq_iff update_comp_eq_of_injective update_comp_eq_of_forall_ne)

@[simp]
theorem update_elim_inl [DecidableEq α] [DecidableEq (α ⊕ β)] {f : α → γ} {g : β → γ} {i : α}
    {x : γ} : update (Sum.elim f g) (inl i) x = Sum.elim (update f i x) g :=
  update_eq_iff.2 ⟨by simp, by simp +contextual⟩

@[simp]
theorem update_elim_inr [DecidableEq β] [DecidableEq (α ⊕ β)] {f : α → γ} {g : β → γ} {i : β}
    {x : γ} : update (Sum.elim f g) (inr i) x = Sum.elim f (update g i x) :=
  update_eq_iff.2 ⟨by simp, by simp +contextual⟩

@[simp]
theorem update_inl_comp_inl [DecidableEq α] [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : α}
    {x : γ} : update f (inl i) x ∘ inl = update (f ∘ inl) i x :=
  update_comp_eq_of_injective _ inl_injective _ _

@[simp]
theorem update_inl_apply_inl [DecidableEq α] [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i j : α}
    {x : γ} : update f (inl i) x (inl j) = update (f ∘ inl) i x j := by
  rw [← update_inl_comp_inl, Function.comp_apply]

@[simp]
theorem update_inl_comp_inr [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {x : γ} :
    update f (inl i) x ∘ inr = f ∘ inr :=
  (update_comp_eq_of_forall_ne _ _) fun _ ↦ inr_ne_inl

theorem update_inl_apply_inr [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {j : β} {x : γ} :
    update f (inl i) x (inr j) = f (inr j) :=
  Function.update_of_ne inr_ne_inl ..

@[simp]
theorem update_inr_comp_inl [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : β} {x : γ} :
    update f (inr i) x ∘ inl = f ∘ inl :=
  (update_comp_eq_of_forall_ne _ _) fun _ ↦ inl_ne_inr

theorem update_inr_apply_inl [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : α} {j : β} {x : γ} :
    update f (inr j) x (inl i) = f (inl i) :=
  Function.update_of_ne inl_ne_inr ..

@[simp]
theorem update_inr_comp_inr [DecidableEq β] [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i : β}
    {x : γ} : update f (inr i) x ∘ inr = update (f ∘ inr) i x :=
  update_comp_eq_of_injective _ inr_injective _ _

@[simp]
theorem update_inr_apply_inr [DecidableEq β] [DecidableEq (α ⊕ β)] {f : α ⊕ β → γ} {i j : β}
    {x : γ} : update f (inr i) x (inr j) = update (f ∘ inr) i x j := by
  rw [← update_inr_comp_inr, Function.comp_apply]

@[simp]
theorem update_inl_apply_inl' {γ : α ⊕ β → Type*} [DecidableEq α] [DecidableEq (α ⊕ β)]
    {f : (i : α ⊕ β) → γ i} {i : α} {x : γ (.inl i)} (j : α) :
    update f (.inl i) x (Sum.inl j) = update (fun j ↦ f (.inl j)) i x j :=
  Function.update_apply_of_injective f Sum.inl_injective i x j

@[simp]
theorem update_inr_apply_inr' {γ : α ⊕ β → Type*} [DecidableEq β] [DecidableEq (α ⊕ β)]
    {f : (i : α ⊕ β) → γ i} {i : β} {x : γ (.inr i)} (j : β) :
    update f (.inr i) x (Sum.inr j) = update (fun j ↦ f (.inr j)) i x j :=
  Function.update_apply_of_injective f Sum.inr_injective i x j

@[simp]
lemma rec_update_left {γ : α ⊕ β → Sort*} [DecidableEq α] [DecidableEq β]
    (f : ∀ a, γ (.inl a)) (g : ∀ b, γ (.inr b)) (a : α) (x : γ (.inl a)) :
    Sum.rec (update f a x) g = update (Sum.rec f g) (.inl a) x :=
  Function.rec_update Sum.inl_injective (Sum.rec · g) (fun _ _ => rfl) (fun
    | _, _, .inl _, h => (h _ rfl).elim
    | _, _, .inr _, _ => rfl) _ _ _

@[simp]
lemma rec_update_right {γ : α ⊕ β → Sort*} [DecidableEq α] [DecidableEq β]
    (f : ∀ a, γ (.inl a)) (g : ∀ b, γ (.inr b)) (b : β) (x : γ (.inr b)) :
    Sum.rec f (update g b x) = update (Sum.rec f g) (.inr b) x :=
  Function.rec_update Sum.inr_injective (Sum.rec f) (fun _ _ => rfl) (fun
    | _, _, .inr _, h => (h _ rfl).elim
    | _, _, .inl _, _ => rfl) _ _ _

@[simp]
lemma elim_update_left {γ : Sort*} [DecidableEq α] [DecidableEq β]
    (f : α → γ) (g : β → γ) (a : α) (x : γ) :
    Sum.elim (update f a x) g = update (Sum.elim f g) (.inl a) x :=
  rec_update_left _ _ _ _

@[simp]
lemma elim_update_right {γ : Sort*} [DecidableEq α] [DecidableEq β]
    (f : α → γ) (g : β → γ) (b : β) (x : γ) :
    Sum.elim f (update g b x) = update (Sum.elim f g) (.inr b) x :=
  rec_update_right _ _ _ _

@[simp]
theorem swap_leftInverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap

@[simp]
theorem swap_rightInverse : Function.RightInverse (@swap α β) swap :=
  swap_swap

mk_iff_of_inductive_prop Sum.LiftRel Sum.liftRel_iff

namespace LiftRel

variable {r : α → γ → Prop} {s : β → δ → Prop} {x : α ⊕ β} {y : γ ⊕ δ}
  {a : α} {b : β} {c : γ} {d : δ}

theorem isLeft_congr (h : LiftRel r s x y) : x.isLeft ↔ y.isLeft := by cases h <;> rfl
theorem isRight_congr (h : LiftRel r s x y) : x.isRight ↔ y.isRight := by cases h <;> rfl

theorem isLeft_left (h : LiftRel r s x (inl c)) : x.isLeft := by cases h; rfl
theorem isLeft_right (h : LiftRel r s (inl a) y) : y.isLeft := by cases h; rfl
theorem isRight_left (h : LiftRel r s x (inr d)) : x.isRight := by cases h; rfl
theorem isRight_right (h : LiftRel r s (inr b) y) : y.isRight := by cases h; rfl

theorem exists_of_isLeft_left (h₁ : LiftRel r s x y) (h₂ : x.isLeft) :
    ∃ a c, r a c ∧ x = inl a ∧ y = inl c := by
  rcases isLeft_iff.mp h₂ with ⟨_, rfl⟩
  simp only [liftRel_iff, false_and, and_false, exists_false, or_false, reduceCtorEq] at h₁
  exact h₁

theorem exists_of_isLeft_right (h₁ : LiftRel r s x y) (h₂ : y.isLeft) :
    ∃ a c, r a c ∧ x = inl a ∧ y = inl c := exists_of_isLeft_left h₁ ((isLeft_congr h₁).mpr h₂)

theorem exists_of_isRight_left (h₁ : LiftRel r s x y) (h₂ : x.isRight) :
    ∃ b d, s b d ∧ x = inr b ∧ y = inr d := by
  rcases isRight_iff.mp h₂ with ⟨_, rfl⟩
  simp only [liftRel_iff, false_and, and_false, exists_false, false_or, reduceCtorEq] at h₁
  exact h₁

theorem exists_of_isRight_right (h₁ : LiftRel r s x y) (h₂ : y.isRight) :
    ∃ b d, s b d ∧ x = inr b ∧ y = inr d :=
  exists_of_isRight_left h₁ ((isRight_congr h₁).mpr h₂)

end LiftRel

end Sum

open Sum

namespace Function

theorem Injective.sumElim {γ : Sort*} {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (hfg : ∀ a b, f a ≠ g b) : Injective (Sum.elim f g)
  | inl _, inl _, h => congr_arg inl <| hf h
  | inl _, inr _, h => (hfg _ _ h).elim
  | inr _, inl _, h => (hfg _ _ h.symm).elim
  | inr _, inr _, h => congr_arg inr <| hg h

@[deprecated (since := "2025-02-20")] alias Injective.sum_elim := Injective.sumElim

theorem Injective.sumMap {f : α → β} {g : α' → β'} (hf : Injective f) (hg : Injective g) :
    Injective (Sum.map f g)
  | inl _, inl _, h => congr_arg inl <| hf <| inl.inj h
  | inr _, inr _, h => congr_arg inr <| hg <| inr.inj h

@[deprecated (since := "2025-02-20")] alias Injective.sum_map := Injective.sumMap

theorem Surjective.sumMap {f : α → β} {g : α' → β'} (hf : Surjective f) (hg : Surjective g) :
    Surjective (Sum.map f g)
  | inl y =>
    let ⟨x, hx⟩ := hf y
    ⟨inl x, congr_arg inl hx⟩
  | inr y =>
    let ⟨x, hx⟩ := hg y
    ⟨inr x, congr_arg inr hx⟩

@[deprecated (since := "2025-02-20")] alias Surjective.sum_map := Surjective.sumMap

theorem Bijective.sumMap {f : α → β} {g : α' → β'} (hf : Bijective f) (hg : Bijective g) :
    Bijective (Sum.map f g) :=
  ⟨hf.injective.sumMap hg.injective, hf.surjective.sumMap hg.surjective⟩

@[deprecated (since := "2025-02-20")] alias Bijective.sum_map := Bijective.sumMap

end Function

namespace Sum

open Function

@[simp]
theorem elim_injective {γ : Sort*} {f : α → γ} {g : β → γ} :
    Injective (Sum.elim f g) ↔ Injective f ∧ Injective g ∧ ∀ a b, f a ≠ g b where
  mp h := ⟨h.comp inl_injective, h.comp inr_injective, fun _ _ => h.ne inl_ne_inr⟩
  mpr | ⟨hf, hg, hfg⟩ => hf.sumElim hg hfg

@[simp]
theorem map_injective {f : α → γ} {g : β → δ} :
    Injective (Sum.map f g) ↔ Injective f ∧ Injective g  where
  mp h := ⟨.of_comp <| h.comp inl_injective, .of_comp <| h.comp inr_injective⟩
  mpr | ⟨hf, hg⟩ => hf.sumMap hg

@[simp]
theorem map_surjective {f : α → γ} {g : β → δ} :
    Surjective (Sum.map f g) ↔ Surjective f ∧ Surjective g where
  mp h := ⟨
      (fun c => by
        obtain ⟨a | b, h⟩ := h (inl c)
        · exact ⟨a, inl_injective h⟩
        · cases h),
      (fun d => by
        obtain ⟨a | b, h⟩ := h (inr d)
        · cases h
        · exact ⟨b, inr_injective h⟩)⟩
  mpr | ⟨hf, hg⟩ => hf.sumMap hg

@[simp]
theorem map_bijective {f : α → γ} {g : β → δ} :
    Bijective (Sum.map f g) ↔ Bijective f ∧ Bijective g :=
  (map_injective.and map_surjective).trans <| and_and_and_comm

end Sum

/-!
### Ternary sum

Abbreviations for the maps from the summands to `α ⊕ β ⊕ γ`. This is useful for pattern-matching.
-/

namespace Sum3

/-- The map from the first summand into a ternary sum. -/
@[match_pattern, simp, reducible]
def in₀ (a : α) : α ⊕ (β ⊕ γ) :=
  inl a

/-- The map from the second summand into a ternary sum. -/
@[match_pattern, simp, reducible]
def in₁ (b : β) : α ⊕ (β ⊕ γ) :=
  inr <| inl b

/-- The map from the third summand into a ternary sum. -/
@[match_pattern, simp, reducible]
def in₂ (c : γ) : α ⊕ (β ⊕ γ) :=
  inr <| inr c

end Sum3

/-!
### PSum
-/

namespace PSum

variable {α β : Sort*}

theorem inl_injective : Function.Injective (PSum.inl : α → α ⊕' β) := fun _ _ ↦ inl.inj

theorem inr_injective : Function.Injective (PSum.inr : β → α ⊕' β) := fun _ _ ↦ inr.inj

end PSum
