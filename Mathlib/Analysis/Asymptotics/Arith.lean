/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.Basic

/-!
# Arithmetic operations on asymptotic relations

This file develops the behavior of `IsBigOWith`, `IsBigO`, and `IsLittleO` under absolute values,
negation, addition, subtraction, zero, constants, and finite sums.

-/

@[expose] public section

assert_not_exists IsBoundedSMul Summable OpenPartialHomeomorph BoundedLENhdsClass

open Set Filter

namespace Asymptotics

variable {α E F E' F' E'' F'' : Type*}

variable [Norm E] [Norm F]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F']
  [NormedAddCommGroup E''] [NormedAddCommGroup F'']

variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F}
variable {f' : α → E'} {g' : α → F'}
variable {f'' : α → E''} {g'' : α → F''}
variable {l : Filter α}

/-! ### Simplification: absolute value -/

section Abs

variable {u v : α → ℝ}

@[simp]
theorem isBigOWith_abs_right : (IsBigOWith c l f fun x => |u x|) ↔ IsBigOWith c l f u :=
  by simpa only [Real.norm_eq_abs] using
    (isBigOWith_norm_right (c := c) (l := l) (f := f) (g' := u))

alias ⟨IsBigOWith.of_abs_right, IsBigOWith.abs_right⟩ := isBigOWith_abs_right

@[simp]
theorem isBigO_abs_right : (f =O[l] fun x => |u x|) ↔ f =O[l] u :=
  by simpa only [Real.norm_eq_abs] using (isBigO_norm_right (l := l) (f := f) (g' := u))

alias ⟨IsBigO.of_abs_right, IsBigO.abs_right⟩ := isBigO_abs_right

@[simp]
theorem isLittleO_abs_right : (f =o[l] fun x => |u x|) ↔ f =o[l] u :=
  by simpa only [Real.norm_eq_abs] using (isLittleO_norm_right (l := l) (f := f) (g' := u))

alias ⟨IsLittleO.of_abs_right, IsLittleO.abs_right⟩ := isLittleO_abs_right

@[simp]
theorem isBigOWith_abs_left : IsBigOWith c l (fun x => |u x|) g ↔ IsBigOWith c l u g :=
  by simpa only [Real.norm_eq_abs] using
    (isBigOWith_norm_left (c := c) (l := l) (f' := u) (g := g))

alias ⟨IsBigOWith.of_abs_left, IsBigOWith.abs_left⟩ := isBigOWith_abs_left

@[simp]
theorem isBigO_abs_left : (fun x => |u x|) =O[l] g ↔ u =O[l] g :=
  by simpa only [Real.norm_eq_abs] using (isBigO_norm_left (l := l) (f' := u) (g := g))

alias ⟨IsBigO.of_abs_left, IsBigO.abs_left⟩ := isBigO_abs_left

@[simp]
theorem isLittleO_abs_left : (fun x => |u x|) =o[l] g ↔ u =o[l] g :=
  by simpa only [Real.norm_eq_abs] using (isLittleO_norm_left (l := l) (f' := u) (g := g))

alias ⟨IsLittleO.of_abs_left, IsLittleO.abs_left⟩ := isLittleO_abs_left

theorem isBigOWith_abs_abs :
    (IsBigOWith c l (fun x => |u x|) fun x => |v x|) ↔ IsBigOWith c l u v :=
  isBigOWith_abs_left.trans isBigOWith_abs_right

alias ⟨IsBigOWith.of_abs_abs, IsBigOWith.abs_abs⟩ := isBigOWith_abs_abs

theorem isBigO_abs_abs : ((fun x => |u x|) =O[l] fun x => |v x|) ↔ u =O[l] v :=
  isBigO_abs_left.trans isBigO_abs_right

alias ⟨IsBigO.of_abs_abs, IsBigO.abs_abs⟩ := isBigO_abs_abs

theorem isLittleO_abs_abs : ((fun x => |u x|) =o[l] fun x => |v x|) ↔ u =o[l] v :=
  isLittleO_abs_left.trans isLittleO_abs_right

alias ⟨IsLittleO.of_abs_abs, IsLittleO.abs_abs⟩ := isLittleO_abs_abs

end Abs

/-! ### Simplification: negate -/

@[simp]
theorem isBigOWith_neg_right : (IsBigOWith c l f fun x => -g' x) ↔ IsBigOWith c l f g' := by
  simp only [IsBigOWith_def, norm_neg]

alias ⟨IsBigOWith.of_neg_right, IsBigOWith.neg_right⟩ := isBigOWith_neg_right

@[simp]
theorem isBigO_neg_right : (f =O[l] fun x => -g' x) ↔ f =O[l] g' := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_neg_right

alias ⟨IsBigO.of_neg_right, IsBigO.neg_right⟩ := isBigO_neg_right

@[simp]
theorem isLittleO_neg_right : (f =o[l] fun x => -g' x) ↔ f =o[l] g' := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_neg_right

alias ⟨IsLittleO.of_neg_right, IsLittleO.neg_right⟩ := isLittleO_neg_right

@[simp]
theorem isBigOWith_neg_left : IsBigOWith c l (fun x => -f' x) g ↔ IsBigOWith c l f' g := by
  simp only [IsBigOWith_def, norm_neg]

alias ⟨IsBigOWith.of_neg_left, IsBigOWith.neg_left⟩ := isBigOWith_neg_left

@[simp]
theorem isBigO_neg_left : (fun x => -f' x) =O[l] g ↔ f' =O[l] g := by
  simp only [IsBigO_def]
  exact exists_congr fun _ => isBigOWith_neg_left

alias ⟨IsBigO.of_neg_left, IsBigO.neg_left⟩ := isBigO_neg_left

@[simp]
theorem isLittleO_neg_left : (fun x => -f' x) =o[l] g ↔ f' =o[l] g := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun _ _ => isBigOWith_neg_left

alias ⟨IsLittleO.of_neg_left, IsLittleO.neg_left⟩ := isLittleO_neg_left

theorem IsBigOWith.eq_zero_imp (h : IsBigOWith c l f'' g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  Eventually.mono h.bound fun x hx hg => norm_le_zero_iff.1 <| by simpa [hg] using hx

theorem IsBigO.eq_zero_imp (h : f'' =O[l] g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  let ⟨_C, hC⟩ := h.isBigOWith
  hC.eq_zero_imp

/-! ### Addition and subtraction -/

section add_sub

variable {f₁ f₂ : α → E'} {g₁ g₂ : α → F'}

theorem IsBigOWith.add (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x + f₂ x) g := by
  rw [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with x hx₁ hx₂ using
    calc
      ‖f₁ x + f₂ x‖ ≤ c₁ * ‖g x‖ + c₂ * ‖g x‖ := norm_add_le_of_le hx₁ hx₂
      _ = (c₁ + c₂) * ‖g x‖ := (add_mul _ _ _).symm

theorem IsBigO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  let ⟨_c₁, hc₁⟩ := h₁.isBigOWith
  let ⟨_c₂, hc₂⟩ := h₂.isBigOWith
  (hc₁.add hc₂).isBigO

theorem IsLittleO.add (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g :=
  IsLittleO.of_isBigOWith fun c cpos =>
    ((h₁.forall_isBigOWith <| half_pos cpos).add (h₂.forall_isBigOWith <|
      half_pos cpos)).congr_const (add_halves c)

theorem IsBigOWith.add_add {g₁ g₂ : α → ℝ} (h₁ : IsBigOWith c₁ l f₁ g₁)
    (h₂ : IsBigOWith c₂ l f₂ g₂) :
    IsBigOWith (max c₁ c₂) l (fun x ↦ f₁ x + f₂ x) (fun x ↦ ‖g₁ x‖ + ‖g₂ x‖) := by
  rw [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with x hx₁ hx₂
  calc
    ‖f₁ x + f₂ x‖ ≤ c₁ * ‖g₁ x‖ + c₂ * ‖g₂ x‖ := norm_add_le_of_le hx₁ hx₂
    _ ≤ (max c₁ c₂) * ‖g₁ x‖ + (max c₁ c₂) * ‖g₂ x‖ := by
        gcongr <;> simp [le_max_left _ _, le_max_right _ _]
    _ = (max c₁ c₂) * ‖‖g₁ x‖ + ‖g₂ x‖‖ := by
        rw [Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)), mul_add]

theorem IsBigO.add_add {g₁ g₂ : α → ℝ} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x ↦ f₁ x + f₂ x) =O[l] fun x ↦ ‖g₁ x‖ + ‖g₂ x‖ := by
  obtain ⟨c₁, hc₁⟩ := h₁.isBigOWith
  obtain ⟨c₂, hc₂⟩ := h₂.isBigOWith
  exact (hc₁.add_add hc₂).isBigO

theorem IsLittleO.add_add (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x + f₂ x) =o[l] fun x => ‖g₁ x‖ + ‖g₂ x‖ := by
  refine (h₁.trans_le fun x => ?_).add (h₂.trans_le ?_) <;> simp [abs_of_nonneg, add_nonneg]

theorem IsBigO.add_isLittleO (h₁ : f₁ =O[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.add h₂.isBigO

theorem IsLittleO.add_isBigO (h₁ : f₁ =o[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.isBigO.add h₂

theorem IsBigOWith.add_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₁.add (h₂.forall_isBigOWith (sub_pos.2 hc))).congr_const (add_sub_cancel _ _)

theorem IsLittleO.add_isBigOWith (h₁ : f₁ =o[l] g) (h₂ : IsBigOWith c₁ l f₂ g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₂.add_isLittleO h₁ hc).congr_left fun _ => add_comm _ _

theorem IsBigOWith.sub (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : IsBigOWith c₂ l f₂ g) :
    IsBigOWith (c₁ + c₂) l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

theorem IsBigOWith.sub_isLittleO (h₁ : IsBigOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsBigOWith c₂ l (fun x => f₁ x - f₂ x) g := by
  simpa only [sub_eq_add_neg] using h₁.add_isLittleO h₂.neg_left hc

theorem IsBigO.sub (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

theorem IsLittleO.sub (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g := by
  simpa only [sub_eq_add_neg] using h₁.add h₂.neg_left

theorem IsBigO.add_iff_left (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₁ =O[l] g) :=
  ⟨fun h ↦ h.sub h₂ |>.congr (fun _ ↦ add_sub_cancel_right _ _) (fun _ ↦ rfl), fun h ↦ h.add h₂⟩

theorem IsBigO.add_iff_right (h₁ : f₁ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g ↔ (f₂ =O[l] g) :=
  ⟨fun h ↦ h.sub h₁ |>.congr (fun _ ↦ (eq_sub_of_add_eq' rfl).symm) (fun _ ↦ rfl), fun h ↦ h₁.add h⟩

theorem IsLittleO.add_iff_left (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₁ =o[l] g) :=
  ⟨fun h ↦ h.sub h₂ |>.congr (fun _ ↦ add_sub_cancel_right _ _) (fun _ ↦ rfl), fun h ↦ h.add h₂⟩

theorem IsLittleO.add_iff_right (h₁ : f₁ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g ↔ (f₂ =o[l] g) :=
  ⟨fun h ↦ h.sub h₁ |>.congr (fun _ ↦ (eq_sub_of_add_eq' rfl).symm) (fun _ ↦ rfl), fun h ↦ h₁.add h⟩

theorem IsBigO.sub_iff_left (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₁ =O[l] g) :=
  ⟨fun h ↦ h.add h₂ |>.congr (fun _ ↦ sub_add_cancel ..) (fun _ ↦ rfl), fun h ↦ h.sub h₂⟩

theorem IsBigO.sub_iff_right (h₁ : f₁ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g ↔ (f₂ =O[l] g) :=
  ⟨fun h ↦ h₁.sub h |>.congr (fun _ ↦ sub_sub_self ..) (fun _ ↦ rfl), fun h ↦ h₁.sub h⟩

theorem IsLittleO.sub_iff_left (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₁ =o[l] g) :=
  ⟨fun h ↦ h.add h₂ |>.congr (fun _ ↦ sub_add_cancel ..) (fun _ ↦ rfl), fun h ↦ h.sub h₂⟩

theorem IsLittleO.sub_iff_right (h₁ : f₁ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g ↔ (f₂ =o[l] g) :=
  ⟨fun h ↦ h₁.sub h |>.congr (fun _ ↦ sub_sub_self ..) (fun _ ↦ rfl), fun h ↦ h₁.sub h⟩

end add_sub

/-!
### Lemmas about `IsBigO (f₁ - f₂) g l` / `IsLittleO (f₁ - f₂) g l` treated as a binary relation
-/

section IsBigOOAsRel

variable {f₁ f₂ f₃ : α → E'}

theorem IsBigOWith.symm (h : IsBigOWith c l (fun x => f₁ x - f₂ x) g) :
    IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  h.neg_left.congr_left fun _x => neg_sub _ _

theorem isBigOWith_comm :
    IsBigOWith c l (fun x => f₁ x - f₂ x) g ↔ IsBigOWith c l (fun x => f₂ x - f₁ x) g :=
  ⟨IsBigOWith.symm, IsBigOWith.symm⟩

theorem IsBigO.symm (h : (fun x => f₁ x - f₂ x) =O[l] g) : (fun x => f₂ x - f₁ x) =O[l] g :=
  h.neg_left.congr_left fun _x => neg_sub _ _

theorem isBigO_comm : (fun x => f₁ x - f₂ x) =O[l] g ↔ (fun x => f₂ x - f₁ x) =O[l] g :=
  ⟨IsBigO.symm, IsBigO.symm⟩

theorem IsLittleO.symm (h : (fun x => f₁ x - f₂ x) =o[l] g) : (fun x => f₂ x - f₁ x) =o[l] g := by
  simpa only [neg_sub] using h.neg_left

theorem isLittleO_comm : (fun x => f₁ x - f₂ x) =o[l] g ↔ (fun x => f₂ x - f₁ x) =o[l] g :=
  ⟨IsLittleO.symm, IsLittleO.symm⟩

theorem IsBigOWith.triangle (h₁ : IsBigOWith c l (fun x => f₁ x - f₂ x) g)
    (h₂ : IsBigOWith c' l (fun x => f₂ x - f₃ x) g) :
    IsBigOWith (c + c') l (fun x => f₁ x - f₃ x) g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

theorem IsBigO.triangle (h₁ : (fun x => f₁ x - f₂ x) =O[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =O[l] g) : (fun x => f₁ x - f₃ x) =O[l] g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

theorem IsLittleO.triangle (h₁ : (fun x => f₁ x - f₂ x) =o[l] g)
    (h₂ : (fun x => f₂ x - f₃ x) =o[l] g) : (fun x => f₁ x - f₃ x) =o[l] g :=
  (h₁.add h₂).congr_left fun _x => sub_add_sub_cancel _ _ _

theorem IsBigO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =O[l] g) : f₁ =O[l] g ↔ f₂ =O[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩

theorem IsLittleO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =o[l] g) : f₁ =o[l] g ↔ f₂ =o[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun _x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun _x => sub_add_cancel _ _⟩

end IsBigOOAsRel

/-! ### Zero and other constants -/

section ZeroConst

variable (g g' l)

theorem isLittleO_zero : (fun _x => (0 : E')) =o[l] g' :=
  IsLittleO.of_bound fun c hc =>
    univ_mem' fun x => by simpa using mul_nonneg hc.le (norm_nonneg <| g' x)

theorem isBigOWith_zero (hc : 0 ≤ c) : IsBigOWith c l (fun _x => (0 : E')) g' :=
  IsBigOWith.of_bound <| univ_mem' fun x => by simpa using mul_nonneg hc (norm_nonneg <| g' x)

theorem isBigOWith_zero' : IsBigOWith 0 l (fun _x => (0 : E')) g :=
  IsBigOWith.of_bound <| univ_mem' fun x => by simp

theorem isBigO_zero : (fun _x => (0 : E')) =O[l] g :=
  isBigO_iff_isBigOWith.2 ⟨0, isBigOWith_zero' _ _⟩

theorem isBigO_refl_left : (fun x => f' x - f' x) =O[l] g' :=
  (isBigO_zero g' l).congr_left fun _x => (sub_self _).symm

theorem isLittleO_refl_left : (fun x => f' x - f' x) =o[l] g' :=
  (isLittleO_zero g' l).congr_left fun _x => (sub_self _).symm

variable {g g' l}

@[simp]
theorem isBigOWith_zero_right_iff : (IsBigOWith c l f'' fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 := by
  simp only [IsBigOWith_def, norm_zero, mul_zero, norm_le_zero_iff, EventuallyEq, Pi.zero_apply]

@[simp]
theorem isBigO_zero_right_iff : (f'' =O[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h =>
    let ⟨_c, hc⟩ := h.isBigOWith
    isBigOWith_zero_right_iff.1 hc,
    fun h => (isBigOWith_zero_right_iff.2 h : IsBigOWith 1 _ _ _).isBigO⟩

@[simp]
theorem isLittleO_zero_right_iff : (f'' =o[l] fun _x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h => isBigO_zero_right_iff.1 h.isBigO,
   fun h => IsLittleO.of_isBigOWith fun _c _hc => isBigOWith_zero_right_iff.2 h⟩

theorem isBigOWith_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    IsBigOWith (‖c‖ / ‖c'‖) l (fun _x : α => c) fun _x => c' := by
  simp only [IsBigOWith_def]
  apply univ_mem'
  intro x
  rw [mem_ofPred, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hc')]

theorem isBigO_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    (fun _x : α => c) =O[l] fun _x => c' :=
  (isBigOWith_const_const c hc' l).isBigO

@[simp]
theorem isBigO_const_const_iff {c : E''} {c' : F''} (l : Filter α) [l.NeBot] :
    ((fun _x : α => c) =O[l] fun _x => c') ↔ c' = 0 → c = 0 := by
  rcases eq_or_ne c' 0 with (rfl | hc')
  · simp [EventuallyEq]
  · simp [hc', isBigO_const_const _ hc']

@[simp]
theorem isBigO_pure {x} : f'' =O[pure x] g'' ↔ g'' x = 0 → f'' x = 0 :=
  calc
    f'' =O[pure x] g'' ↔ (fun _y : α => f'' x) =O[pure x] fun _ => g'' x := isBigO_congr rfl rfl
    _ ↔ g'' x = 0 → f'' x = 0 := isBigO_const_const_iff _

end ZeroConst

/-! ### Sum -/

section Sum

variable {ι : Type*} {A : ι → α → E'} {C : ι → ℝ} {s : Finset ι}

@[to_fun] theorem IsBigOWith.sum (h : ∀ i ∈ s, IsBigOWith (C i) l (A i) g) :
    IsBigOWith (∑ i ∈ s, C i) l (∑ i ∈ s, A i) g := by
  induction s using Finset.cons_induction with
  | empty =>
      rw [Finset.sum_empty]
      apply isBigOWith_zero'
  | cons i s is IH =>
    simp only [Finset.sum_cons, Finset.forall_mem_cons] at h ⊢
    exact h.1.add (IH h.2)

@[to_fun] theorem IsBigO.sum (h : ∀ i ∈ s, A i =O[l] g) : (∑ i ∈ s, A i) =O[l] g := by
  simp only [IsBigO_def] at *
  choose! C hC using h
  exact ⟨_, IsBigOWith.sum hC⟩

@[to_fun] theorem IsLittleO.sum (h : ∀ i ∈ s, A i =o[l] g') : (∑ i ∈ s, A i) =o[l] g' := by
  exact Finset.sum_induction A (· =o[l] g') (fun _ _ ↦ .add) (isLittleO_zero ..) h

variable {B : ι → α → ℝ}

/-- If each term `A i` of a sum `IsBigO` of `B i`, then the sum of the `A i` `IsBigO` of the sum
of the norms of the `B i`. -/
theorem IsBigOWith.sum_congr
    (hAB : ∀ i ∈ s, IsBigOWith (C i) l (A i) (B i)) :
    IsBigOWith (sSup (C '' s)) l (fun H ↦ ∑ i ∈ s, A i H) (fun H ↦ ∑ i ∈ s, ‖B i H‖) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [isBigOWith_zero]
  simp only [IsBigOWith_def] at *
  filter_upwards [(eventually_all_finset s).mpr hAB]
    with x hx
  calc
    ‖∑ i ∈ s, A i x‖ ≤ ∑ i ∈ s, ‖A i x‖ := norm_sum_le ..
    _ ≤ ∑ i ∈ s, C i * ‖B i x‖ := Finset.sum_le_sum (fun j hj ↦ hx j hj)
    _ ≤ ∑ i ∈ s, sSup (C '' s) * ‖B i x‖ := by
        refine Finset.sum_le_sum ?_
        intro j hj; gcongr
        rw [← s.sup'_eq_csSup_image hs, Finset.le_sup'_iff]; use j
    _ = sSup (C '' s) * ∑ i ∈ s, ‖B i x‖ := (Finset.mul_sum ..).symm
    _ = sSup (C '' s) * ‖∑ i ∈ s, ‖B i x‖‖ := by
      congr; rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]

theorem IsBigO.sum_congr (hAB : ∀ i ∈ s, A i =O[l] B i) :
    (fun H => ∑ i ∈ s, A i H) =O[l] fun H => ∑ i ∈ s, ‖B i H‖ := by
  simp only [IsBigO_def] at *
  choose! C hC using hAB
  exact ⟨_, IsBigOWith.sum_congr hC⟩

theorem IsLittleO.sum_congr (hAB : ∀ i ∈ s, A i =o[l] B i) :
    (fun H => ∑ i ∈ s, A i H) =o[l] fun H => ∑ i ∈ s, ‖B i H‖ := by
  induction s using Finset.cons_induction with
  | empty => simp [isLittleO_zero]
  | cons i s his h =>
  simp_rw [Finset.sum_cons]
  calc (fun H => A i H + ∑ j ∈ s, A j H)
      =o[l] fun H => ‖B i H‖ + ‖∑ j ∈ s, ‖B j H‖‖ :=
          (hAB i (by simp)).add_add (h (fun j hj => hAB j (by simp [hj])))
    _ =ᶠ[l] fun H => ‖B i H‖ + ∑ j ∈ s, ‖B j H‖ := by
        refine Eventually.of_forall fun H ↦ congr_arg (‖B i H‖ + ·) ?_
        exact Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)

/-- Similar to `IsBigOWith.sum_congr` except the index set can change in the sum. This requires the
constant in `hAB` to be independent of the index `i` and also the big-O relationship to "kick in"
at the same point along the running variable. Hence the `⊤` in `⊤ ×ˢ l`. -/
theorem IsBigOWith.sum_congr' {C : ℝ} {i : α → Finset ι}
    (hAB : IsBigOWith C (⊤ ×ˢ l) A.uncurry B.uncurry) :
    IsBigOWith C l (fun H => ∑ j ∈ i H, A j H) (fun H => ∑ j ∈ i H, ‖B j H‖) := by
  simp only [IsBigOWith_def] at *
  obtain ⟨s₁, hs₁, s₂, hs₂, hbound⟩ := Filter.eventually_prod_iff.mp hAB
  filter_upwards [hs₂] with H hH
  calc
    ‖∑ j ∈ i H, A j H‖ ≤ ∑ j ∈ i H, ‖A j H‖ := norm_sum_le ..
    _ ≤ ∑ j ∈ i H, C * ‖B j H‖ :=
        Finset.sum_le_sum fun j _ => hbound (Filter.eventually_top.mp hs₁ j) hH
    _ = C * ∑ j ∈ i H, ‖B j H‖ := (Finset.mul_sum ..).symm
    _ = C * ‖∑ j ∈ i H, ‖B j H‖‖ := by
        congr; rw [Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))]

theorem IsBigO.sum_congr' {i : α → Finset ι} (hAB : A.uncurry =O[⊤ ×ˢ l] B.uncurry) :
    (fun H => ∑ j ∈ i H, A j H) =O[l] (fun H => ∑ j ∈ i H, ‖B j H‖) := by
  simp only [IsBigO_def]
  obtain ⟨C, hC⟩ := hAB.isBigOWith
  exact ⟨C, hC.sum_congr'⟩

theorem IsLittleO.sum_congr' {i : α → Finset ι} (hAB : A.uncurry =o[⊤ ×ˢ l] B.uncurry) :
    (fun H => ∑ j ∈ i H, A j H) =o[l] (fun H => ∑ j ∈ i H, ‖B j H‖) := by
  rw [isLittleO_iff_forall_isBigOWith] at *
  intro c hc
  exact (hAB hc).sum_congr'

end Sum

end Asymptotics
