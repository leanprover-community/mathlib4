/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
import Mathlib.Logic.Function.Basic

#align_import data.sum.basic from "leanprover-community/mathlib"@"bd9851ca476957ea4549eb19b40e7b5ade9428cc"

/-!
# Disjoint union of types

This file proves basic results about the sum type `α ⊕ β`.

`α ⊕ β` is the type made of a copy of `α` and a copy of `β`. It is also called *disjoint union*.

## Main declarations

* `Sum.getLeft?`: Retrieves the left content of `x : α ⊕ β` or returns `none` if it's coming from
  the right.
* `Sum.getRight?`: Retrieves the right content of `x : α ⊕ β` or returns `none` if it's coming from
  the left.
* `Sum.isLeft`: Returns whether `x : α ⊕ β` comes from the left component or not.
* `Sum.isRight`: Returns whether `x : α ⊕ β` comes from the right component or not.
* `Sum.map`: Maps `α ⊕ β` to `γ ⊕ δ` component-wise.
* `Sum.elim`: Nondependent eliminator/induction principle for `α ⊕ β`.
* `Sum.swap`: Maps `α ⊕ β` to `β ⊕ α` by swapping components.
* `Sum.Lex`: Lexicographic order on `α ⊕ β` induced by a relation on `α` and a relation on `β`.

## Notes

The definition of `Sum` takes values in `Type*`. This effectively forbids `Prop`- valued sum types.
To this effect, we have `PSum`, which takes value in `Sort*` and carries a more complicated
universe signature in consequence. The `Prop` version is `or`.
-/


universe u v w x

variable {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {γ δ : Type*}

namespace Sum

deriving instance DecidableEq for Sum
deriving instance BEq for Sum

@[simp]
theorem «forall» {p : Sum α β → Prop} : (∀ x, p x) ↔ (∀ a, p (inl a)) ∧ ∀ b, p (inr b) :=
  ⟨fun h ↦ ⟨fun _ ↦ h _, fun _ ↦ h _⟩, fun ⟨h₁, h₂⟩ ↦ Sum.rec h₁ h₂⟩
#align sum.forall Sum.forall

@[simp]
theorem «exists» {p : Sum α β → Prop} : (∃ x, p x) ↔ (∃ a, p (inl a)) ∨ ∃ b, p (inr b) :=
  ⟨ fun
    | ⟨inl a, h⟩ => Or.inl ⟨a, h⟩
    | ⟨inr b, h⟩ => Or.inr ⟨b, h⟩,
    fun
    | Or.inl ⟨a, h⟩ => ⟨inl a, h⟩
    | Or.inr ⟨b, h⟩ => ⟨inr b, h⟩⟩
#align sum.exists Sum.exists

theorem forall_sum_pi {γ : α ⊕ β → Sort*} (p : (∀ ab, γ ab) → Prop) :
    (∀ fab, p fab) ↔ (∀ fa fb, p (Sum.rec fa fb)) :=
  ⟨fun h fa fb => h _, fun h fab => by
    have h1 : fab = Sum.rec (fun a => fab (Sum.inl a)) (fun b => fab (Sum.inr b)) := by
      ext ab; cases ab <;> rfl
    rw [h1]; exact h _ _⟩

theorem exists_sum_pi {γ : α ⊕ β → Sort*} (p : (∀ ab, γ ab) → Prop) :
    (∃ fab, p fab) ↔ (∃ fa fb, p (Sum.rec fa fb)) := by
  rw [← not_forall_not, forall_sum_pi]
  simp

theorem inl_injective : Function.Injective (inl : α → Sum α β) := fun _ _ ↦ inl.inj
#align sum.inl_injective Sum.inl_injective

theorem inr_injective : Function.Injective (inr : β → Sum α β) := fun _ _ ↦ inr.inj
#align sum.inr_injective Sum.inr_injective

section get

/-- Check if a sum is `inl` and if so, retrieve its contents. -/
def getLeft? : Sum α β → Option α
  | inl a => some a
  | inr _ => none
#align sum.get_left Sum.getLeft?

/-- Check if a sum is `inr` and if so, retrieve its contents. -/
def getRight? : Sum α β → Option β
  | inr b => some b
  | inl _ => none
#align sum.get_right Sum.getRight?

/-- Check if a sum is `inl`. -/
def isLeft : Sum α β → Bool
  | inl _ => true
  | inr _ => false
#align sum.is_left Sum.isLeft

/-- Check if a sum is `inr`. -/
def isRight : Sum α β → Bool
  | inl _ => false
  | inr _ => true
#align sum.is_right Sum.isRight

variable {x y : Sum α β}

@[simp] theorem getLeft?_inl (x : α) : (inl x : α ⊕ β).getLeft? = some x := rfl
@[simp] theorem getLeft?_inr (x : β) : (inr x : α ⊕ β).getLeft? = none := rfl
@[simp] theorem getRight?_inl (x : α) : (inl x : α ⊕ β).getRight? = none := rfl
@[simp] theorem getRight?_inr (x : β) : (inr x : α ⊕ β).getRight? = some x := rfl

@[simp] theorem isLeft_inl (x : α) : (inl x : α ⊕ β).isLeft = true := rfl
@[simp] theorem isLeft_inr (x : β) : (inr x : α ⊕ β).isLeft = false := rfl
@[simp] theorem isRight_inl (x : α) : (inl x : α ⊕ β).isRight = false := rfl
@[simp] theorem isRight_inr (x : β) : (inr x : α ⊕ β).isRight = true := rfl

@[simp] theorem getLeft?_eq_none_iff : x.getLeft? = none ↔ x.isRight := by
  cases x <;> simp only [getLeft?, isRight, eq_self_iff_true]
#align sum.get_left_eq_none_iff Sum.getLeft?_eq_none_iff

@[simp] theorem getRight?_eq_none_iff : x.getRight? = none ↔ x.isLeft := by
  cases x <;> simp only [getRight?, isLeft, eq_self_iff_true]
#align sum.get_right_eq_none_iff Sum.getRight?_eq_none_iff

@[simp] lemma getLeft?_eq_some_iff {a : α} : x.getLeft? = a ↔ x = inl a := by
  cases x <;> simp only [getLeft?, Option.some.injEq, inl.injEq]
#align sum.get_left_eq_some_iff Sum.getLeft?_eq_some_iff

@[simp] lemma getRight?_eq_some_iff {b : β} : x.getRight? = b ↔ x = inr b := by
  cases x <;> simp only [getRight?, Option.some.injEq, inr.injEq]
#align sum.get_right_eq_some_iff Sum.getRight?_eq_some_iff

@[simp]
theorem not_isLeft (x : Sum α β) : not x.isLeft = x.isRight := by cases x <;> rfl
#align sum.bnot_is_left Sum.not_isLeft

@[simp]
theorem isLeft_eq_false : x.isLeft = false ↔ x.isRight := by cases x <;> simp
#align sum.is_left_eq_ff Sum.isLeft_eq_false

theorem Not_isLeft : ¬x.isLeft ↔ x.isRight := by simp
#align sum.not_is_left Sum.Not_isLeft

@[simp]
theorem not_isRight (x : Sum α β) : !x.isRight = x.isLeft := by cases x <;> rfl
#align sum.bnot_is_right Sum.not_isRight

@[simp]
theorem isRight_eq_false : x.isRight = false ↔ x.isLeft := by cases x <;> simp
#align sum.is_right_eq_ff Sum.isRight_eq_false

theorem Not_isRight : ¬x.isRight ↔ x.isLeft := by simp
#align sum.not_is_right Sum.Not_isRight

theorem isLeft_iff : x.isLeft ↔ ∃ y, x = Sum.inl y := by cases x <;> simp
#align sum.is_left_iff Sum.isLeft_iff

theorem isRight_iff : x.isRight ↔ ∃ y, x = Sum.inr y := by cases x <;> simp
#align sum.is_right_iff Sum.isRight_iff

end get

theorem inl.inj_iff {a b} : (inl a : Sum α β) = inl b ↔ a = b :=
  ⟨inl.inj, congr_arg _⟩
#align sum.inl.inj_iff Sum.inl.inj_iff

theorem inr.inj_iff {a b} : (inr a : Sum α β) = inr b ↔ a = b :=
  ⟨inr.inj, congr_arg _⟩
#align sum.inr.inj_iff Sum.inr.inj_iff

theorem inl_ne_inr {a : α} {b : β} : inl a ≠ inr b :=
  fun.
#align sum.inl_ne_inr Sum.inl_ne_inr

theorem inr_ne_inl {a : α} {b : β} : inr b ≠ inl a :=
  fun.
#align sum.inr_ne_inl Sum.inr_ne_inl

/-- Define a function on `α ⊕ β` by giving separate definitions on `α` and `β`. -/
protected def elim {α β γ : Sort _} (f : α → γ) (g : β → γ) : Sum α β → γ :=
  fun x ↦ Sum.casesOn x f g
#align sum.elim Sum.elim

@[simp]
theorem elim_inl {α β γ : Sort _} (f : α → γ) (g : β → γ) (x : α) : Sum.elim f g (inl x) = f x :=
  rfl
#align sum.elim_inl Sum.elim_inl

@[simp]
theorem elim_inr {α β γ : Sort _} (f : α → γ) (g : β → γ) (x : β) : Sum.elim f g (inr x) = g x :=
  rfl
#align sum.elim_inr Sum.elim_inr

@[simp]
theorem elim_comp_inl {α β γ : Sort _} (f : α → γ) (g : β → γ) : Sum.elim f g ∘ inl = f :=
  rfl
#align sum.elim_comp_inl Sum.elim_comp_inl

@[simp]
theorem elim_comp_inr {α β γ : Sort _} (f : α → γ) (g : β → γ) : Sum.elim f g ∘ inr = g :=
  rfl
#align sum.elim_comp_inr Sum.elim_comp_inr

@[simp]
theorem elim_inl_inr {α β : Sort _} : @Sum.elim α β _ inl inr = id :=
  funext fun x ↦ Sum.casesOn x (fun _ ↦ rfl) fun _ ↦ rfl
#align sum.elim_inl_inr Sum.elim_inl_inr

theorem comp_elim {α β γ δ : Sort _} (f : γ → δ) (g : α → γ) (h : β → γ) :
    f ∘ Sum.elim g h = Sum.elim (f ∘ g) (f ∘ h) :=
  funext fun x ↦ Sum.casesOn x (fun _ ↦ rfl) fun _ ↦ rfl
#align sum.comp_elim Sum.comp_elim

@[simp]
theorem elim_comp_inl_inr {α β γ : Sort _} (f : Sum α β → γ) : Sum.elim (f ∘ inl) (f ∘ inr) = f :=
  funext fun x ↦ Sum.casesOn x (fun _ ↦ rfl) fun _ ↦ rfl
#align sum.elim_comp_inl_inr Sum.elim_comp_inl_inr

/-- Map `α ⊕ β` to `α' ⊕ β'` sending `α` to `α'` and `β` to `β'`. -/
protected def map (f : α → α') (g : β → β') : Sum α β → Sum α' β' :=
  Sum.elim (inl ∘ f) (inr ∘ g)
#align sum.map Sum.map

@[simp]
theorem map_inl (f : α → α') (g : β → β') (x : α) : (inl x).map f g = inl (f x) :=
  rfl
#align sum.map_inl Sum.map_inl

@[simp]
theorem map_inr (f : α → α') (g : β → β') (x : β) : (inr x).map f g = inr (g x) :=
  rfl
#align sum.map_inr Sum.map_inr

@[simp]
theorem map_map {α'' β''} (f' : α' → α'') (g' : β' → β'') (f : α → α') (g : β → β') :
    ∀ x : Sum α β, (x.map f g).map f' g' = x.map (f' ∘ f) (g' ∘ g)
  | inl _ => rfl
  | inr _ => rfl
#align sum.map_map Sum.map_map

@[simp]
theorem map_comp_map {α'' β''} (f' : α' → α'') (g' : β' → β'') (f : α → α') (g : β → β') :
    Sum.map f' g' ∘ Sum.map f g = Sum.map (f' ∘ f) (g' ∘ g) :=
  funext <| map_map f' g' f g
#align sum.map_comp_map Sum.map_comp_map

@[simp]
theorem map_id_id (α β) : Sum.map (@id α) (@id β) = id :=
  funext fun x ↦ Sum.recOn x (fun _ ↦ rfl) fun _ ↦ rfl
#align sum.map_id_id Sum.map_id_id

theorem elim_map {α β γ δ ε : Sort _} {f₁ : α → β} {f₂ : β → ε} {g₁ : γ → δ} {g₂ : δ → ε} {x} :
    Sum.elim f₂ g₂ (Sum.map f₁ g₁ x) = Sum.elim (f₂ ∘ f₁) (g₂ ∘ g₁) x := by
  cases x <;> rfl
#align sum.elim_map Sum.elim_map

theorem elim_comp_map {α β γ δ ε : Sort _} {f₁ : α → β} {f₂ : β → ε} {g₁ : γ → δ} {g₂ : δ → ε} :
    Sum.elim f₂ g₂ ∘ Sum.map f₁ g₁ = Sum.elim (f₂ ∘ f₁) (g₂ ∘ g₁) :=
  funext $ fun _ => elim_map
#align sum.elim_comp_map Sum.elim_comp_map

@[simp]
theorem isLeft_map (f : α → β) (g : γ → δ) (x : Sum α γ) : isLeft (x.map f g) = isLeft x := by
  cases x <;> rfl
#align sum.is_left_map Sum.isLeft_map

@[simp]
theorem isRight_map (f : α → β) (g : γ → δ) (x : Sum α γ) : isRight (x.map f g) = isRight x := by
  cases x <;> rfl
#align sum.is_right_map Sum.isRight_map

@[simp]
theorem getLeft?_map (f : α → β) (g : γ → δ) (x : Sum α γ) :
    (x.map f g).getLeft? = x.getLeft?.map f := by
  cases x <;> rfl
#align sum.get_left_map Sum.getLeft?_map

@[simp]
theorem getRight?_map (f : α → β) (g : γ → δ) (x : α ⊕ γ) :
    (x.map f g).getRight? = x.getRight?.map g := by cases x <;> rfl
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

/-- Swap the factors of a sum type -/
def swap : Sum α β → Sum β α :=
  Sum.elim inr inl
#align sum.swap Sum.swap

@[simp]
theorem swap_inl (x : α) : swap (inl x : Sum α β) = inr x :=
  rfl
#align sum.swap_inl Sum.swap_inl

@[simp]
theorem swap_inr (x : β) : swap (inr x : Sum α β) = inl x :=
  rfl
#align sum.swap_inr Sum.swap_inr

@[simp]
theorem swap_swap (x : Sum α β) : swap (swap x) = x := by cases x <;> rfl
#align sum.swap_swap Sum.swap_swap

@[simp]
theorem swap_swap_eq : swap ∘ swap = @id (Sum α β) :=
  funext <| swap_swap
#align sum.swap_swap_eq Sum.swap_swap_eq

@[simp]
theorem swap_leftInverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap
#align sum.swap_left_inverse Sum.swap_leftInverse

@[simp]
theorem swap_rightInverse : Function.RightInverse (@swap α β) swap :=
  swap_swap
#align sum.swap_right_inverse Sum.swap_rightInverse

@[simp]
theorem isLeft_swap (x : Sum α β) : x.swap.isLeft = x.isRight := by cases x <;> rfl
#align sum.is_left_swap Sum.isLeft_swap

@[simp]
theorem isRight_swap (x : Sum α β) : x.swap.isRight = x.isLeft := by cases x <;> rfl
#align sum.is_right_swap Sum.isRight_swap

@[simp]
theorem getLeft?_swap (x : Sum α β) : x.swap.getLeft? = x.getRight? := by cases x <;> rfl
#align sum.get_left_swap Sum.getLeft?_swap

@[simp]
theorem getRight?_swap (x : Sum α β) : x.swap.getRight? = x.getLeft? := by cases x <;> rfl
#align sum.get_right_swap Sum.getRight?_swap

section LiftRel

/-- Lifts pointwise two relations between `α` and `γ` and between `β` and `δ` to a relation between
`α ⊕ β` and `γ ⊕ δ`. -/
inductive LiftRel (r : α → γ → Prop) (s : β → δ → Prop) : Sum α β → Sum γ δ → Prop
  | protected inl {a c} : r a c → LiftRel r s (inl a) (inl c)
  | protected inr {b d} : s b d → LiftRel r s (inr b) (inr d)
#align sum.lift_rel Sum.LiftRel

variable {r r₁ r₂ : α → γ → Prop} {s s₁ s₂ : β → δ → Prop} {a : α} {b : β} {c : γ} {d : δ}
  {x : Sum α β} {y : Sum γ δ}

@[simp]
theorem liftRel_inl_inl : LiftRel r s (inl a) (inl c) ↔ r a c :=
  ⟨fun h ↦ by
    cases h
    assumption, LiftRel.inl⟩
#align sum.lift_rel_inl_inl Sum.liftRel_inl_inl

@[simp]
theorem not_liftRel_inl_inr : ¬LiftRel r s (inl a) (inr d) :=
  fun.
#align sum.not_lift_rel_inl_inr Sum.not_liftRel_inl_inr

@[simp]
theorem not_liftRel_inr_inl : ¬LiftRel r s (inr b) (inl c) :=
  fun.
#align sum.not_lift_rel_inr_inl Sum.not_liftRel_inr_inl

@[simp]
theorem liftRel_inr_inr : LiftRel r s (inr b) (inr d) ↔ s b d :=
  ⟨fun h ↦ by
    cases h
    assumption, LiftRel.inr⟩
#align sum.lift_rel_inr_inr Sum.liftRel_inr_inr

instance [∀ a c, Decidable (r a c)] [∀ b d, Decidable (s b d)] :
    ∀ (ab : Sum α β) (cd : Sum γ δ), Decidable (LiftRel r s ab cd)
  | inl _, inl _ => decidable_of_iff' _ liftRel_inl_inl
  | inl _, inr _ => Decidable.isFalse not_liftRel_inl_inr
  | inr _, inl _ => Decidable.isFalse not_liftRel_inr_inl
  | inr _, inr _ => decidable_of_iff' _ liftRel_inr_inr

theorem LiftRel.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ a b, s₁ a b → s₂ a b)
  (h : LiftRel r₁ s₁ x y) : LiftRel r₂ s₂ x y := by
  cases h
  · exact LiftRel.inl (hr _ _ ‹_›)
  · exact LiftRel.inr (hs _ _ ‹_›)
#align sum.lift_rel.mono Sum.LiftRel.mono

theorem LiftRel.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) (h : LiftRel r₁ s x y) :
    LiftRel r₂ s x y :=
  (h.mono hr) fun _ _ ↦ id
#align sum.lift_rel.mono_left Sum.LiftRel.mono_left

theorem LiftRel.mono_right (hs : ∀ a b, s₁ a b → s₂ a b) (h : LiftRel r s₁ x y) :
    LiftRel r s₂ x y :=
  h.mono (fun _ _ ↦ id) hs
#align sum.lift_rel.mono_right Sum.LiftRel.mono_right

protected theorem LiftRel.swap (h : LiftRel r s x y) : LiftRel s r x.swap y.swap := by
  cases h
  · exact LiftRel.inr ‹_›
  · exact LiftRel.inl ‹_›
#align sum.lift_rel.swap Sum.LiftRel.swap

@[simp]
theorem liftRel_swap_iff : LiftRel s r x.swap y.swap ↔ LiftRel r s x y :=
  ⟨fun h ↦ by
    rw [← swap_swap x, ← swap_swap y]
    exact h.swap, LiftRel.swap⟩
#align sum.lift_rel_swap_iff Sum.liftRel_swap_iff

end LiftRel

section Lex

/-- Lexicographic order for sum. Sort all the `inl a` before the `inr b`, otherwise use the
respective order on `α` or `β`. -/
inductive Lex (r : α → α → Prop) (s : β → β → Prop) : Sum α β → Sum α β → Prop
  | protected inl {a₁ a₂} (h : r a₁ a₂) : Lex r s (inl a₁) (inl a₂)
  | protected inr {b₁ b₂} (h : s b₁ b₂) : Lex r s (inr b₁) (inr b₂)
  | sep (a b) : Lex r s (inl a) (inr b)
#align sum.lex.inl Sum.Lex.inl
#align sum.lex.inr Sum.Lex.inr
#align sum.lex.sep Sum.Lex.sep
#align sum.lex Sum.Lex

attribute [simp] Lex.sep

variable {r r₁ r₂ : α → α → Prop} {s s₁ s₂ : β → β → Prop} {a a₁ a₂ : α} {b b₁ b₂ : β}
  {x y : Sum α β}

@[simp]
theorem lex_inl_inl : Lex r s (inl a₁) (inl a₂) ↔ r a₁ a₂ :=
  ⟨fun h ↦ by
    cases h
    assumption, Lex.inl⟩
#align sum.lex_inl_inl Sum.lex_inl_inl

@[simp]
theorem lex_inr_inr : Lex r s (inr b₁) (inr b₂) ↔ s b₁ b₂ :=
  ⟨fun h ↦ by
    cases h
    assumption, Lex.inr⟩
#align sum.lex_inr_inr Sum.lex_inr_inr

@[simp]
theorem lex_inr_inl : ¬Lex r s (inr b) (inl a) :=
  fun.
#align sum.lex_inr_inl Sum.lex_inr_inl

instance instDecidableRelSumLex [DecidableRel r] [DecidableRel s] : DecidableRel (Lex r s)
  | inl _, inl _ => decidable_of_iff' _ lex_inl_inl
  | inl _, inr _ => Decidable.isTrue (Lex.sep _ _)
  | inr _, inl _ => Decidable.isFalse lex_inr_inl
  | inr _, inr _ => decidable_of_iff' _ lex_inr_inr

protected theorem LiftRel.lex {a b : Sum α β} (h : LiftRel r s a b) : Lex r s a b := by
  cases h
  · exact Lex.inl ‹_›
  · exact Lex.inr ‹_›
#align sum.lift_rel.lex Sum.LiftRel.lex

theorem liftRel_subrelation_lex : Subrelation (LiftRel r s) (Lex r s) := LiftRel.lex
#align sum.lift_rel_subrelation_lex Sum.liftRel_subrelation_lex

theorem Lex.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ a b, s₁ a b → s₂ a b) (h : Lex r₁ s₁ x y) :
    Lex r₂ s₂ x y := by
  cases h
  · exact Lex.inl (hr _ _ ‹_›)
  · exact Lex.inr (hs _ _ ‹_›)
  · exact Lex.sep _ _
#align sum.lex.mono Sum.Lex.mono

theorem Lex.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) (h : Lex r₁ s x y) : Lex r₂ s x y :=
  (h.mono hr) fun _ _ ↦ id
#align sum.lex.mono_left Sum.Lex.mono_left

theorem Lex.mono_right (hs : ∀ a b, s₁ a b → s₂ a b) (h : Lex r s₁ x y) : Lex r s₂ x y :=
  h.mono (fun _ _ ↦ id) hs
#align sum.lex.mono_right Sum.Lex.mono_right

theorem lex_acc_inl {a} (aca : Acc r a) : Acc (Lex r s) (inl a) := by
  induction' aca with a _ IH
  constructor
  intro y h
  cases' h with a' _ h'
  exact IH _ h'
#align sum.lex_acc_inl Sum.lex_acc_inl

theorem lex_acc_inr (aca : ∀ a, Acc (Lex r s) (inl a)) {b} (acb : Acc s b) :
    Acc (Lex r s) (inr b) := by
  induction' acb with b _ IH
  constructor
  intro y h
  cases' h with _ _ _ b' _ h' a
  · exact IH _ h'
  · exact aca _
#align sum.lex_acc_inr Sum.lex_acc_inr

theorem lex_wf (ha : WellFounded r) (hb : WellFounded s) : WellFounded (Lex r s) :=
  have aca : ∀ a, Acc (Lex r s) (inl a) := fun a ↦ lex_acc_inl (ha.apply a)
  ⟨fun x ↦ Sum.recOn x aca fun b ↦ lex_acc_inr aca (hb.apply b)⟩
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

theorem elim_const_const (c : γ) :
    Sum.elim (const _ c : α → γ) (const _ c : β → γ) = const _ c := by
  ext x
  cases x <;> rfl
#align sum.elim_const_const Sum.elim_const_const

@[simp]
theorem elim_lam_const_lam_const (c : γ) :
    (Sum.elim (fun _ : α ↦ c) fun _ : β ↦ c) = fun _ ↦ c :=
  Sum.elim_const_const c
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
