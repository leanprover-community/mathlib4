/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.MkIffOfInductiveProp

#align_import data.sum.basic from "leanprover-community/mathlib"@"bd9851ca476957ea4549eb19b40e7b5ade9428cc"

/-!
# Additional lemmas about sum types

Most of the former contents of this file have been moved to Batteries.
-/


universe u v w x

variable {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {γ δ : Type*}

namespace Sum

#align sum.forall Sum.forall
#align sum.exists Sum.exists

theorem exists_sum {γ : α ⊕ β → Sort*} (p : (∀ ab, γ ab) → Prop) :
    (∃ fab, p fab) ↔ (∃ fa fb, p (Sum.rec fa fb)) := by
  rw [← not_forall_not, forall_sum]
  simp

theorem inl_injective : Function.Injective (inl : α → Sum α β) := fun _ _ ↦ inl.inj
#align sum.inl_injective Sum.inl_injective

theorem inr_injective : Function.Injective (inr : β → Sum α β) := fun _ _ ↦ inr.inj
#align sum.inr_injective Sum.inr_injective

theorem sum_rec_congr (P : α ⊕ β → Sort*) (f : ∀ i, P (inl i)) (g : ∀ i, P (inr i))
    {x y : α ⊕ β} (h : x = y) :
    @Sum.rec _ _ _ f g x = cast (congr_arg P h.symm) (@Sum.rec _ _ _ f g y) := by cases h; rfl

section get

#align sum.is_left Sum.isLeft
#align sum.is_right Sum.isRight
#align sum.get_left Sum.getLeft?
#align sum.get_right Sum.getRight?

variable {x y : Sum α β}

#align sum.get_left_eq_none_iff Sum.getLeft?_eq_none_iff
#align sum.get_right_eq_none_iff Sum.getRight?_eq_none_iff

theorem eq_left_iff_getLeft_eq {a : α} : x = inl a ↔ ∃ h, x.getLeft h = a := by
  cases x <;> simp

theorem eq_right_iff_getRight_eq {b : β} : x = inr b ↔ ∃ h, x.getRight h = b := by
  cases x <;> simp

#align sum.get_left_eq_some_iff Sum.getLeft?_eq_some_iff
#align sum.get_right_eq_some_iff Sum.getRight?_eq_some_iff

theorem getLeft_eq_getLeft? (h₁ : x.isLeft) (h₂ : x.getLeft?.isSome) :
    x.getLeft h₁ = x.getLeft?.get h₂ := by simp [← getLeft?_eq_some_iff]

theorem getRight_eq_getRight? (h₁ : x.isRight) (h₂ : x.getRight?.isSome) :
    x.getRight h₁ = x.getRight?.get h₂ := by simp [← getRight?_eq_some_iff]

#align sum.bnot_is_left Sum.bnot_isLeft
#align sum.is_left_eq_ff Sum.isLeft_eq_false
#align sum.not_is_left Sum.not_isLeft
#align sum.bnot_is_right Sum.bnot_isRight
#align sum.is_right_eq_ff Sum.isRight_eq_false
#align sum.not_is_right Sum.not_isRight
#align sum.is_left_iff Sum.isLeft_iff
#align sum.is_right_iff Sum.isRight_iff

@[simp] theorem isSome_getLeft?_iff_isLeft : x.getLeft?.isSome ↔ x.isLeft := by
  rw [isLeft_iff, Option.isSome_iff_exists]; simp

@[simp] theorem isSome_getRight?_iff_isRight : x.getRight?.isSome ↔ x.isRight := by
  rw [isRight_iff, Option.isSome_iff_exists]; simp

end get

#align sum.inl.inj_iff Sum.inl.inj_iff
#align sum.inr.inj_iff Sum.inr.inj_iff
#align sum.inl_ne_inr Sum.inl_ne_inr
#align sum.inr_ne_inl Sum.inr_ne_inl
#align sum.elim Sum.elim
#align sum.elim_inl Sum.elim_inl
#align sum.elim_inr Sum.elim_inr
#align sum.elim_comp_inl Sum.elim_comp_inl
#align sum.elim_comp_inr Sum.elim_comp_inr
#align sum.elim_inl_inr Sum.elim_inl_inr
#align sum.comp_elim Sum.comp_elim
#align sum.elim_comp_inl_inr Sum.elim_comp_inl_inr
#align sum.map Sum.map
#align sum.map_inl Sum.map_inl
#align sum.map_inr Sum.map_inr
#align sum.map_map Sum.map_map
#align sum.map_comp_map Sum.map_comp_map
#align sum.map_id_id Sum.map_id_id
#align sum.elim_map Sum.elim_map
#align sum.elim_comp_map Sum.elim_comp_map
#align sum.is_left_map Sum.isLeft_map
#align sum.is_right_map Sum.isRight_map
#align sum.get_left_map Sum.getLeft?_map
#align sum.get_right_map Sum.getRight?_map

open Function (update update_eq_iff update_comp_eq_of_injective update_comp_eq_of_forall_ne)

@[simp]
theorem update_elim_inl [DecidableEq α] [DecidableEq (Sum α β)] {f : α → γ} {g : β → γ} {i : α}
    {x : γ} : update (Sum.elim f g) (inl i) x = Sum.elim (update f i x) g :=
  update_eq_iff.2 ⟨by simp, by simp (config := { contextual := true })⟩
#align sum.update_elim_inl Sum.update_elim_inl

@[simp]
theorem update_elim_inr [DecidableEq β] [DecidableEq (Sum α β)] {f : α → γ} {g : β → γ} {i : β}
    {x : γ} : update (Sum.elim f g) (inr i) x = Sum.elim f (update g i x) :=
  update_eq_iff.2 ⟨by simp, by simp (config := { contextual := true })⟩
#align sum.update_elim_inr Sum.update_elim_inr

@[simp]
theorem update_inl_comp_inl [DecidableEq α] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α}
    {x : γ} : update f (inl i) x ∘ inl = update (f ∘ inl) i x :=
  update_comp_eq_of_injective _ inl_injective _ _
#align sum.update_inl_comp_inl Sum.update_inl_comp_inl

@[simp]
theorem update_inl_apply_inl [DecidableEq α] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i j : α}
    {x : γ} : update f (inl i) x (inl j) = update (f ∘ inl) i x j := by
  rw [← update_inl_comp_inl, Function.comp_apply]
#align sum.update_inl_apply_inl Sum.update_inl_apply_inl

@[simp]
theorem update_inl_comp_inr [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α} {x : γ} :
    update f (inl i) x ∘ inr = f ∘ inr :=
  (update_comp_eq_of_forall_ne _ _) fun _ ↦ inr_ne_inl
#align sum.update_inl_comp_inr Sum.update_inl_comp_inr

theorem update_inl_apply_inr [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α} {j : β} {x : γ} :
    update f (inl i) x (inr j) = f (inr j) :=
  Function.update_noteq inr_ne_inl _ _
#align sum.update_inl_apply_inr Sum.update_inl_apply_inr

@[simp]
theorem update_inr_comp_inl [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : β} {x : γ} :
    update f (inr i) x ∘ inl = f ∘ inl :=
  (update_comp_eq_of_forall_ne _ _) fun _ ↦ inl_ne_inr
#align sum.update_inr_comp_inl Sum.update_inr_comp_inl

theorem update_inr_apply_inl [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α} {j : β} {x : γ} :
    update f (inr j) x (inl i) = f (inl i) :=
  Function.update_noteq inl_ne_inr _ _
#align sum.update_inr_apply_inl Sum.update_inr_apply_inl

@[simp]
theorem update_inr_comp_inr [DecidableEq β] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : β}
    {x : γ} : update f (inr i) x ∘ inr = update (f ∘ inr) i x :=
  update_comp_eq_of_injective _ inr_injective _ _
#align sum.update_inr_comp_inr Sum.update_inr_comp_inr

@[simp]
theorem update_inr_apply_inr [DecidableEq β] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i j : β}
    {x : γ} : update f (inr i) x (inr j) = update (f ∘ inr) i x j := by
  rw [← update_inr_comp_inr, Function.comp_apply]
#align sum.update_inr_apply_inr Sum.update_inr_apply_inr

#align sum.swap Sum.swap
#align sum.swap_inl Sum.swap_inl
#align sum.swap_inr Sum.swap_inr
#align sum.swap_swap Sum.swap_swap
#align sum.swap_swap_eq Sum.swap_swap_eq

@[simp]
theorem swap_leftInverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap
#align sum.swap_left_inverse Sum.swap_leftInverse

@[simp]
theorem swap_rightInverse : Function.RightInverse (@swap α β) swap :=
  swap_swap
#align sum.swap_right_inverse Sum.swap_rightInverse

#align sum.is_left_swap Sum.isLeft_swap
#align sum.is_right_swap Sum.isRight_swap
#align sum.get_left_swap Sum.getLeft?_swap
#align sum.get_right_swap Sum.getRight?_swap

mk_iff_of_inductive_prop Sum.LiftRel Sum.liftRel_iff

namespace LiftRel

#align sum.lift_rel Sum.LiftRel
#align sum.lift_rel_inl_inl Sum.liftRel_inl_inl
#align sum.not_lift_rel_inl_inr Sum.not_liftRel_inl_inr
#align sum.not_lift_rel_inr_inl Sum.not_liftRel_inr_inl
#align sum.lift_rel_inr_inr Sum.liftRel_inr_inr
#align sum.lift_rel.mono Sum.LiftRel.mono
#align sum.lift_rel.mono_left Sum.LiftRel.mono_left
#align sum.lift_rel.mono_right Sum.LiftRel.mono_right
#align sum.lift_rel.swap Sum.LiftRel.swap
#align sum.lift_rel_swap_iff Sum.liftRel_swap_iff

variable {r : α → γ → Prop} {s : β → δ → Prop} {x : Sum α β} {y : Sum γ δ}
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
  simp only [liftRel_iff, false_and, and_false, exists_false, or_false] at h₁
  exact h₁

theorem exists_of_isLeft_right (h₁ : LiftRel r s x y) (h₂ : y.isLeft) :
    ∃ a c, r a c ∧ x = inl a ∧ y = inl c := exists_of_isLeft_left h₁ ((isLeft_congr h₁).mpr h₂)

theorem exists_of_isRight_left (h₁ : LiftRel r s x y) (h₂ : x.isRight) :
    ∃ b d, s b d ∧ x = inr b ∧ y = inr d := by
  rcases isRight_iff.mp h₂ with ⟨_, rfl⟩
  simp only [liftRel_iff, false_and, and_false, exists_false, false_or] at h₁
  exact h₁

theorem exists_of_isRight_right (h₁ : LiftRel r s x y) (h₂ : y.isRight) :
    ∃ b d, s b d ∧ x = inr b ∧ y = inr d :=
  exists_of_isRight_left h₁ ((isRight_congr h₁).mpr h₂)

end LiftRel

section Lex

#align sum.lex.inl Sum.Lex.inl
#align sum.lex.inr Sum.Lex.inr
#align sum.lex.sep Sum.Lex.sep
#align sum.lex Sum.Lex
#align sum.lex_inl_inl Sum.lex_inl_inl
#align sum.lex_inr_inr Sum.lex_inr_inr
#align sum.lex_inr_inl Sum.lex_inr_inl
#align sum.lift_rel.lex Sum.LiftRel.lex
#align sum.lift_rel_subrelation_lex Sum.liftRel_subrelation_lex
#align sum.lex.mono_left Sum.Lex.mono_left
#align sum.lex.mono_right Sum.Lex.mono_right
#align sum.lex_acc_inl Sum.lex_acc_inl
#align sum.lex_acc_inr Sum.lex_acc_inr
#align sum.lex_wf Sum.lex_wf

end Lex

end Sum

open Sum

namespace Function

theorem Injective.sum_elim {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (hfg : ∀ a b, f a ≠ g b) : Injective (Sum.elim f g)
  | inl _, inl _, h => congr_arg inl <| hf h
  | inl _, inr _, h => (hfg _ _ h).elim
  | inr _, inl _, h => (hfg _ _ h.symm).elim
  | inr _, inr _, h => congr_arg inr <| hg h
#align function.injective.sum_elim Function.Injective.sum_elim

theorem Injective.sum_map {f : α → β} {g : α' → β'} (hf : Injective f) (hg : Injective g) :
    Injective (Sum.map f g)
  | inl _, inl _, h => congr_arg inl <| hf <| inl.inj h
  | inr _, inr _, h => congr_arg inr <| hg <| inr.inj h
#align function.injective.sum_map Function.Injective.sum_map

theorem Surjective.sum_map {f : α → β} {g : α' → β'} (hf : Surjective f) (hg : Surjective g) :
    Surjective (Sum.map f g)
  | inl y =>
    let ⟨x, hx⟩ := hf y
    ⟨inl x, congr_arg inl hx⟩
  | inr y =>
    let ⟨x, hx⟩ := hg y
    ⟨inr x, congr_arg inr hx⟩
#align function.surjective.sum_map Function.Surjective.sum_map

theorem Bijective.sum_map {f : α → β} {g : α' → β'} (hf : Bijective f) (hg : Bijective g) :
    Bijective (Sum.map f g) :=
  ⟨hf.injective.sum_map hg.injective, hf.surjective.sum_map hg.surjective⟩
#align function.bijective.sum_map Function.Bijective.sum_map

end Function

namespace Sum

open Function

@[simp]
theorem map_injective {f : α → γ} {g : β → δ} :
    Injective (Sum.map f g) ↔ Injective f ∧ Injective g :=
  ⟨fun h =>
    ⟨fun a₁ a₂ ha => inl_injective <| @h (inl a₁) (inl a₂) (congr_arg inl ha : _), fun b₁ b₂ hb =>
      inr_injective <| @h (inr b₁) (inr b₂) (congr_arg inr hb : _)⟩,
    fun h => h.1.sum_map h.2⟩
#align sum.map_injective Sum.map_injective

@[simp]
theorem map_surjective {f : α → γ} {g : β → δ} :
    Surjective (Sum.map f g) ↔ Surjective f ∧ Surjective g :=
  ⟨ fun h => ⟨
      (fun c => by
        obtain ⟨a | b, h⟩ := h (inl c)
        · exact ⟨a, inl_injective h⟩
        · cases h),
      (fun d => by
        obtain ⟨a | b, h⟩ := h (inr d)
        · cases h
        · exact ⟨b, inr_injective h⟩)⟩,
    fun h => h.1.sum_map h.2⟩
#align sum.map_surjective Sum.map_surjective

@[simp]
theorem map_bijective {f : α → γ} {g : β → δ} :
    Bijective (Sum.map f g) ↔ Bijective f ∧ Bijective g :=
  (map_injective.and map_surjective).trans <| and_and_and_comm
#align sum.map_bijective Sum.map_bijective

#align sum.elim_const_const Sum.elim_const_const
#align sum.elim_lam_const_lam_const Sum.elim_lam_const_lam_const

theorem elim_update_left [DecidableEq α] [DecidableEq β] (f : α → γ) (g : β → γ) (i : α) (c : γ) :
    Sum.elim (Function.update f i c) g = Function.update (Sum.elim f g) (inl i) c := by
  ext x
  rcases x with x | x
  · by_cases h : x = i
    · subst h
      simp
    · simp [h]
  · simp
#align sum.elim_update_left Sum.elim_update_left

theorem elim_update_right [DecidableEq α] [DecidableEq β] (f : α → γ) (g : β → γ) (i : β) (c : γ) :
    Sum.elim f (Function.update g i c) = Function.update (Sum.elim f g) (inr i) c := by
  ext x
  rcases x with x | x
  · simp
  · by_cases h : x = i
    · subst h
      simp
    · simp [h]
#align sum.elim_update_right Sum.elim_update_right

end Sum

/-!
### Ternary sum

Abbreviations for the maps from the summands to `α ⊕ β ⊕ γ`. This is useful for pattern-matching.
-/

namespace Sum3

/-- The map from the first summand into a ternary sum. -/
@[match_pattern, simp, reducible]
def in₀ (a : α) : Sum α (Sum β γ) :=
  inl a
#align sum3.in₀ Sum3.in₀

/-- The map from the second summand into a ternary sum. -/
@[match_pattern, simp, reducible]
def in₁ (b : β) : Sum α (Sum β γ) :=
  inr <| inl b
#align sum3.in₁ Sum3.in₁

/-- The map from the third summand into a ternary sum. -/
@[match_pattern, simp, reducible]
def in₂ (c : γ) : Sum α (Sum β γ) :=
  inr <| inr c
#align sum3.in₂ Sum3.in₂

end Sum3
