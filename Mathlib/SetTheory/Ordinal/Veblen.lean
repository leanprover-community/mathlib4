/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.SetTheory.Ordinal.FixedPoint

/-!
# Veblen hierarchy

We define the two-argument Veblen function, which satisfes `veblen 0 a = ω ^ a` and that for
`a ≠ 0`, `veblen a` enumerates the common fixed points of `veblen b` for `b < a`.

## Main definitions

* `veblenWith`: The Veblen hierarchy with a specified initial function.
* `veblen`: The Veblen hierarchy starting with `ω ^ ·`.

## Todo

- Define the epsilon numbers and gamma numbers.
- Prove that `ε₀` and `Γ₀` are countable.
- Prove that the exponential principal ordinals are the epsilon ordinals (and 0, 1, 2, ω).
- Prove that the ordinals principal under `veblen` are the gamma ordinals (and 0).
-/

noncomputable section

universe u

namespace Ordinal

variable {f : Ordinal.{u} → Ordinal.{u}} {o a b c d : Ordinal.{u}}

/-! ### Veblen function with a given starting function -/

section veblenWith

/-- `veblenWith f o` is the `o`-th function in the Veblen hierarchy starting with `f`. This is
defined so that

- `veblenWith f 0 = f`.
- `veblenWith f a` enumerates the common fixed points of `veblenWith f b` for `b < a` when `a ≠ 0`.
-/
@[pp_nodot]
def veblenWith (f : Ordinal.{u} → Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} → Ordinal.{u} :=
  if o = 0 then f else derivFamily fun (⟨x, _⟩ : Set.Iio o) ↦ veblenWith f x
termination_by o

@[simp]
theorem veblenWith_zero (f : Ordinal → Ordinal) : veblenWith f 0 = f := by
  rw [veblenWith, if_pos rfl]

theorem veblenWith_of_ne_zero (f : Ordinal → Ordinal) (h : o ≠ 0) :
    veblenWith f o = derivFamily fun x : Set.Iio o ↦ veblenWith f x.1 := by
  rw [veblenWith, if_neg h]

/-- `veblenWith f o` is always normal for `o ≠ 0`. -/
theorem isNormal_veblenWith' (f : Ordinal → Ordinal) (h : o ≠ 0) : IsNormal (veblenWith f o) := by
  rw [veblenWith_of_ne_zero f h]
  exact isNormal_derivFamily _

variable (hf : IsNormal f)
include hf

/-- `veblenWith f o` is always normal whenever `f` is. -/
theorem isNormal_veblenWith (o : Ordinal) : IsNormal (veblenWith f o) := by
  obtain rfl | h := eq_or_ne o 0
  · rwa [veblenWith_zero]
  · exact isNormal_veblenWith' f h

theorem veblenWith_veblenWith_of_lt (h : a < b) (c : Ordinal) :
    veblenWith f a (veblenWith f b c) = veblenWith f b c := by
  let x : {a // a < b} := ⟨a, h⟩
  rw [veblenWith_of_ne_zero f h.bot_lt.ne',
    derivFamily_fp (f := fun y : Set.Iio b ↦ veblenWith f y.1) (i := x)]
  exact isNormal_veblenWith hf x

theorem veblenWith_succ (o : Ordinal) : veblenWith f (Order.succ o) = deriv (veblenWith f o) := by
  rw [deriv_eq_enumOrd (isNormal_veblenWith hf o), veblenWith_of_ne_zero f (succ_ne_zero _),
    derivFamily_eq_enumOrd]
  · apply congr_arg
    ext a
    rw [Set.mem_iInter]
    use fun ha ↦ ha ⟨o, Order.lt_succ o⟩
    rintro (ha : _ = _) ⟨b, hb : b < _⟩
    obtain rfl | hb := Order.lt_succ_iff_eq_or_lt.1 hb
    · rw [Function.mem_fixedPoints_iff, ha]
    · rw [← ha]
      exact veblenWith_veblenWith_of_lt hf hb _
  · exact fun a ↦ isNormal_veblenWith hf a

theorem veblenWith_right_strictMono (o : Ordinal) : StrictMono (veblenWith f o) := by
  obtain rfl | h := eq_or_ne o 0
  · rw [veblenWith_zero]
    exact hf.strictMono
  · rw [veblenWith_of_ne_zero f h]
    exact derivFamily_strictMono _

theorem veblenWith_lt_veblenWith_right_iff : veblenWith f o a < veblenWith f o b ↔ a < b :=
  (veblenWith_right_strictMono hf o).lt_iff_lt

theorem veblenWith_le_veblenWith_right_iff : veblenWith f o a ≤ veblenWith f o b ↔ a ≤ b :=
  (veblenWith_right_strictMono hf o).le_iff_le

theorem veblenWith_injective (o : Ordinal) : Function.Injective (veblenWith f o) :=
  (veblenWith_right_strictMono hf o).injective

theorem veblenWith_inj : veblenWith f o a = veblenWith f o b ↔ a = b :=
  (veblenWith_injective hf o).eq_iff

theorem right_le_veblenWith (a b : Ordinal) : b ≤ veblenWith f a b :=
  (veblenWith_right_strictMono hf a).le_apply

theorem veblenWith_left_monotone (o : Ordinal) : Monotone (veblenWith f · o) := by
  rw [monotone_iff_forall_lt]
  intro a b h
  rw [← veblenWith_veblenWith_of_lt hf h]
  exact (veblenWith_right_strictMono hf a).monotone (right_le_veblenWith hf b o)

theorem veblenWith_pos (hp : 0 < f 0) (a b : Ordinal) : 0 < veblenWith f a b := by
  have H (b) : 0 < veblenWith f 0 b := by
    rw [veblenWith_zero]
    exact hp.trans_le (hf.monotone (Ordinal.zero_le _))
  obtain rfl | h := Ordinal.eq_zero_or_pos a
  · exact H b
  · rw [← veblenWith_veblenWith_of_lt hf h]
    exact H _

theorem veblenWith_zero_strictMono (hp : 0 < f 0) : StrictMono (veblenWith f · 0) := by
  intro a b h
  dsimp only
  rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_lt_veblenWith_right_iff hf]
  exact veblenWith_pos hf hp b 0

theorem veblenWith_zero_lt_iff (hp : 0 < f 0) : veblenWith f a 0 < veblenWith f b 0 ↔ a < b :=
  (veblenWith_zero_strictMono hf hp).lt_iff_lt

theorem veblenWith_zero_le_iff (hp : 0 < f 0) : veblenWith f a 0 ≤ veblenWith f b 0 ↔ a ≤ b :=
  (veblenWith_zero_strictMono hf hp).le_iff_le

theorem veblenWith_zero_inj (hp : 0 < f 0) : veblenWith f a 0 = veblenWith f b 0 ↔ a = b :=
  (veblenWith_zero_strictMono hf hp).injective.eq_iff

theorem left_le_veblenWith (hp : 0 < f 0) (a b : Ordinal) : a ≤ veblenWith f a b :=
  (veblenWith_zero_strictMono hf hp).le_apply.trans <|
    (veblenWith_right_strictMono hf _).monotone (Ordinal.zero_le _)

theorem isNormal_veblenWith_zero (hp : 0 < f 0) : IsNormal (veblenWith f · 0) := by
  rw [isNormal_iff_strictMono_limit]
  refine ⟨veblenWith_zero_strictMono hf hp, fun o ho a IH ↦ ?_⟩
  rw [veblenWith_of_ne_zero f ho.pos.ne', derivFamily_zero]
  apply nfpFamily_le fun l ↦ ?_
  suffices ∃ b < o, List.foldr _ 0 l ≤ veblenWith f b 0 by
    obtain ⟨b, hb, hb'⟩ := this
    exact hb'.trans (IH b hb)
  induction l with
  | nil => use 0; simp [ho.pos]
  | cons a l IH =>
    obtain ⟨b, hb, hb'⟩ := IH
    refine ⟨_, ho.succ_lt (max_lt a.2 hb), ((veblenWith_right_strictMono hf _).monotone <|
      hb'.trans <| veblenWith_left_monotone hf _ <|
        (le_max_right a.1 b).trans (Order.le_succ _)).trans ?_⟩
    rw [veblenWith_veblenWith_of_lt hf]
    rw [Order.lt_succ_iff]
    exact le_max_left _ b

/-- `veblenWith f a b < veblenWith f c d` iff one of the following holds:
* `a = c` and `b < d`
* `a < c` and `b < veblenWith f c d`
* `a > c` and `veblenWith f a b < d` -/
theorem veblenWith_lt_veblenWith_iff : veblenWith f a b < veblenWith f c d ↔
    a = c ∧ b < d ∨ a < c ∧ b < veblenWith f c d ∨ c < a ∧ veblenWith f a b < d := by
  obtain h | rfl | h := lt_trichotomy a c
  · simp_rw [h, h.ne, h.not_lt, false_and, false_or, or_false, true_and]
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_lt_veblenWith_right_iff hf]
  · simp [veblenWith_lt_veblenWith_right_iff hf]
  · simp_rw [h, h.ne', h.not_lt, false_and, false_or, true_and]
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_lt_veblenWith_right_iff hf]

/-- `veblenWith f a b ≤ veblenWith f c d` iff one of the following holds:
* `a = c` and `b ≤ d`
* `a < c` and `b ≤ veblenWith f c d`
* `a > c` and `veblenWith f a b ≤ d` -/
theorem veblenWith_le_veblenWith_iff : veblenWith f a b ≤ veblenWith f c d ↔
    a = c ∧ b ≤ d ∨ a < c ∧ b ≤ veblenWith f c d ∨ c < a ∧ veblenWith f a b ≤ d := by
  obtain h | rfl | h := lt_trichotomy a c
  · simp_rw [h, h.ne, h.not_lt, false_and, false_or, or_false, true_and]
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_le_veblenWith_right_iff hf]
  · simp [veblenWith_le_veblenWith_right_iff hf]
  · simp_rw [h, h.ne', h.not_lt, false_and, false_or, true_and]
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_le_veblenWith_right_iff hf]

/-- `veblenWith f a b = veblenWith f c d` iff one of the following holds:
* `a = c` and `b = d`
* `a < c` and `b = veblenWith f c d`
* `a > c` and `veblenWith f a b = d` -/
theorem veblenWith_eq_veblenWith_iff : veblenWith f a b = veblenWith f c d ↔
    a = c ∧ b = d ∨ a < c ∧ b = veblenWith f c d ∨ c < a ∧ veblenWith f a b = d := by
  obtain h | rfl | h := lt_trichotomy a c
  · simp_rw [h, h.ne, h.not_lt, false_and, false_or, or_false, true_and]
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_inj hf]
  · simp [veblenWith_inj hf]
  · simp_rw [h, h.ne', h.not_lt, false_and, false_or, true_and]
    conv_lhs => rw [← veblenWith_veblenWith_of_lt hf h, veblenWith_inj hf]

end veblenWith

/-! ### Veblen function -/

section veblen

private theorem isNormal_omega0_opow : IsNormal fun a ↦ ω ^ a := isNormal_opow one_lt_omega0
private theorem omega0_opow_zero_pos : 0 < ω ^ (0 : Ordinal) := by simp

/-- `veblen o` is the `o`-th function in the Veblen hierarchy starting with `ω ^ ·`. That is:

- `veblen 0 a = ω ^ a`.
- `veblen a` enumerates the fixed points of `veblen b` for `b < a` when `a ≠ 0`.
-/
@[pp_nodot]
def veblen : Ordinal.{u} → Ordinal.{u} → Ordinal.{u} :=
  veblenWith (ω ^ ·)

@[simp]
theorem veblen_zero : veblen 0 = fun a ↦ ω ^ a := by
  rw [veblen, veblenWith_zero]

theorem veblen_zero_apply (o : Ordinal) : veblen 0 o = ω ^ o := by
  rw [veblen_zero]

theorem veblen_of_ne_zero (h : o ≠ 0) : veblen o = derivFamily fun x : Set.Iio o ↦ veblen x.1 :=
  veblenWith_of_ne_zero _ h

theorem isNormal_veblen (o : Ordinal) : IsNormal (veblen o) :=
  isNormal_veblenWith isNormal_omega0_opow o

theorem veblen_veblen_of_lt (h : a < b) (c : Ordinal) : veblen a (veblen b c) = veblen b c :=
  veblenWith_veblenWith_of_lt isNormal_omega0_opow h c

theorem veblen_succ (o : Ordinal) : veblen (Order.succ o) = deriv (veblen o) :=
  veblenWith_succ isNormal_omega0_opow o

theorem veblen_right_strictMono (o : Ordinal) : StrictMono (veblen o) :=
  veblenWith_right_strictMono isNormal_omega0_opow o

@[simp]
theorem veblen_lt_veblen_right_iff : veblen o a < veblen o b ↔ a < b :=
  veblenWith_lt_veblenWith_right_iff isNormal_omega0_opow

@[simp]
theorem veblen_le_veblen_right_iff : veblen o a ≤ veblen o b ↔ a ≤ b :=
  veblenWith_le_veblenWith_right_iff isNormal_omega0_opow

theorem veblen_injective (o : Ordinal) : Function.Injective (veblen o) :=
  veblenWith_injective isNormal_omega0_opow o

@[simp]
theorem veblen_inj : veblen o a = veblen o b ↔ a = b :=
  (veblen_injective o).eq_iff

theorem right_le_veblen (a b : Ordinal) : b ≤ veblen a b :=
  right_le_veblenWith isNormal_omega0_opow a b

theorem veblen_left_monotone (o : Ordinal) : Monotone (veblen · o) :=
  veblenWith_left_monotone isNormal_omega0_opow o

@[simp]
theorem veblen_pos (a b : Ordinal) : 0 < veblen a b :=
  veblenWith_pos isNormal_omega0_opow omega0_opow_zero_pos a b

theorem veblen_zero_strictMono : StrictMono (veblen · 0) :=
  veblenWith_zero_strictMono isNormal_omega0_opow omega0_opow_zero_pos

@[simp]
theorem veblen_zero_lt_iff : veblen a 0 < veblen b 0 ↔ a < b :=
  veblen_zero_strictMono.lt_iff_lt

@[simp]
theorem veblen_zero_le_iff : veblen a 0 ≤ veblen b 0 ↔ a ≤ b :=
  veblen_zero_strictMono.le_iff_le

@[simp]
theorem veblen_zero_inj : veblen a 0 = veblen b 0 ↔ a = b :=
  veblen_zero_strictMono.injective.eq_iff

theorem left_le_veblen (a b : Ordinal) : a ≤ veblen a b :=
  left_le_veblenWith isNormal_omega0_opow omega0_opow_zero_pos a b

theorem isNormal_veblen_zero : IsNormal (veblen · 0) :=
  isNormal_veblenWith_zero isNormal_omega0_opow omega0_opow_zero_pos

/-- `veblen a b < veblen c d` iff one of the following holds:
* `a = c` and `b < d`
* `a < c` and `b < veblen c d`
* `a > c` and `veblen a b < d` -/
theorem veblen_lt_veblen_iff :
    veblen a b < veblen c d ↔ a = c ∧ b < d ∨ a < c ∧ b < veblen c d ∨ c < a ∧ veblen a b < d :=
  veblenWith_lt_veblenWith_iff isNormal_omega0_opow

/-- `veblen a b ≤ veblen c d` iff one of the following holds:
* `a = c` and `b ≤ d`
* `a < c` and `b ≤ veblen c d`
* `a > c` and `veblen a b ≤ d` -/
theorem veblen_le_veblen_iff :
    veblen a b ≤ veblen c d ↔ a = c ∧ b ≤ d ∨ a < c ∧ b ≤ veblen c d ∨ c < a ∧ veblen a b ≤ d :=
  veblenWith_le_veblenWith_iff isNormal_omega0_opow

/-- `veblen a b = veblen c d` iff one of the following holds:
* `a = c` and `b = d`
* `a < c` and `b = veblen c d`
* `a > c` and `veblen a b = d` -/
theorem veblen_eq_veblen_iff :
    veblen a b = veblen c d ↔ a = c ∧ b = d ∨ a < c ∧ b = veblen c d ∨ c < a ∧ veblen a b = d :=
 veblenWith_eq_veblenWith_iff isNormal_omega0_opow

end veblen
end Ordinal
