/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.Arith

/-!
# Ring and field operations on asymptotic relations

This file develops the behavior of `IsBigOWith`, `IsBigO`, and `IsLittleO` under
multiplication by constants, multiplication of functions, powers, inversion, and division.
-/

@[expose] public section

assert_not_exists IsBoundedSMul Summable OpenPartialHomeomorph BoundedLENhdsClass

open Filter

namespace Asymptotics

variable {α E F R 𝕜 𝕜' : Type*}

variable [Norm E] [Norm F] [SeminormedRing R]
variable {S : Type*} [NormedRing S] [NormMulClass S]
variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜']
variable {c c' : ℝ} {f : α → E} {g : α → F} {l : Filter α}

/-! ### Multiplication by a constant -/

theorem isBigOWith_const_mul_self (c : R) (f : α → R) (l : Filter α) :
    IsBigOWith ‖c‖ l (fun x => c * f x) f :=
  isBigOWith_of_le' _ fun _x => norm_mul_le _ _

theorem isBigO_const_mul_self (c : R) (f : α → R) (l : Filter α) : (fun x => c * f x) =O[l] f :=
  (isBigOWith_const_mul_self c f l).isBigO

theorem IsBigOWith.const_mul_left {f : α → R} (h : IsBigOWith c l f g) (c' : R) :
    IsBigOWith (‖c'‖ * c) l (fun x => c' * f x) g :=
  (isBigOWith_const_mul_self c' f l).trans h (norm_nonneg c')

theorem IsBigO.const_mul_left {f : α → R} (h : f =O[l] g) (c' : R) : (fun x => c' * f x) =O[l] g :=
  let ⟨_c, hc⟩ := h.isBigOWith
  (hc.const_mul_left c').isBigO

theorem isBigOWith_self_const_mul' (u : Rˣ) (f : α → R) (l : Filter α) :
    IsBigOWith ‖(↑u⁻¹ : R)‖ l f fun x => ↑u * f x :=
  (isBigOWith_const_mul_self ↑u⁻¹ (fun x ↦ ↑u * f x) l).congr_left
    fun x ↦ u.inv_mul_cancel_left (f x)

theorem isBigOWith_self_const_mul {c : S} (hc : c ≠ 0) (f : α → S) (l : Filter α) :
    IsBigOWith ‖c‖⁻¹ l f fun x ↦ c * f x := by
  simp [IsBigOWith, inv_mul_cancel_left₀ (norm_ne_zero_iff.mpr hc)]

theorem isBigO_self_const_mul' {c : R} (hc : IsUnit c) (f : α → R) (l : Filter α) :
    f =O[l] fun x => c * f x :=
  let ⟨u, hu⟩ := hc
  hu ▸ (isBigOWith_self_const_mul' u f l).isBigO

theorem isBigO_self_const_mul {c : S} (hc : c ≠ 0) (f : α → S) (l : Filter α) :
    f =O[l] fun x ↦ c * f x :=
  (isBigOWith_self_const_mul hc f l).isBigO

theorem isBigO_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans, fun h => h.const_mul_left c⟩

theorem isBigO_const_mul_left_iff {f : α → S} {c : S} (hc : c ≠ 0) :
    (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(isBigO_self_const_mul hc f l).trans, (isBigO_const_mul_self c f l).trans⟩

theorem IsLittleO.const_mul_left {f : α → R} (h : f =o[l] g) (c : R) : (fun x => c * f x) =o[l] g :=
  (isBigO_const_mul_self c f l).trans_isLittleO h

theorem isLittleO_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(isBigO_self_const_mul' hc f l).trans_isLittleO, fun h => h.const_mul_left c⟩

theorem isLittleO_const_mul_left_iff {f : α → S} {c : S} (hc : c ≠ 0) :
    (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(isBigO_self_const_mul hc f l).trans_isLittleO, (isBigO_const_mul_self c f l).trans_isLittleO⟩

theorem IsBigOWith.of_const_mul_right {g : α → R} {c : R} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f fun x => c * g x) : IsBigOWith (c' * ‖c‖) l f g :=
  h.trans (isBigOWith_const_mul_self c g l) hc'

theorem IsBigO.of_const_mul_right {g : α → R} {c : R} (h : f =O[l] fun x => c * g x) : f =O[l] g :=
  let ⟨_c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.of_const_mul_right cnonneg).isBigO

theorem IsBigOWith.const_mul_right' {g : α → R} {u : Rˣ} {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖(↑u⁻¹ : R)‖) l f fun x => ↑u * g x :=
  h.trans (isBigOWith_self_const_mul' _ _ _) hc'

theorem IsBigOWith.const_mul_right {g : α → S} {c : S} (hc : c ≠ 0) {c' : ℝ} (hc' : 0 ≤ c')
    (h : IsBigOWith c' l f g) : IsBigOWith (c' * ‖c‖⁻¹) l f fun x => c * g x :=
  h.trans (isBigOWith_self_const_mul hc g l) hc'

theorem IsBigO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  h.trans (isBigO_self_const_mul' hc g l)

theorem IsBigO.const_mul_right {g : α → S} {c : S} (hc : c ≠ 0) (h : f =O[l] g) :
    f =O[l] fun x => c * g x :=
  match h.exists_nonneg with
  | ⟨_, hd, hd'⟩ => (hd'.const_mul_right hc hd).isBigO

theorem isBigO_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

theorem isBigO_const_mul_right_iff {g : α → S} {c : S} (hc : c ≠ 0) :
    (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h ↦ h.of_const_mul_right, fun h ↦ h.const_mul_right hc⟩

theorem IsLittleO.of_const_mul_right {g : α → R} {c : R} (h : f =o[l] fun x => c * g x) :
    f =o[l] g :=
  h.trans_isBigO (isBigO_const_mul_self c g l)

theorem IsLittleO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.trans_isBigO (isBigO_self_const_mul' hc g l)

theorem IsLittleO.const_mul_right {g : α → S} {c : S} (hc : c ≠ 0) (h : f =o[l] g) :
    f =o[l] fun x => c * g x :=
  h.trans_isBigO <| isBigO_self_const_mul hc g l

theorem isLittleO_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

theorem isLittleO_const_mul_right_iff {g : α → S} {c : S} (hc : c ≠ 0) :
    (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h ↦ h.of_const_mul_right, fun h ↦ h.trans_isBigO (isBigO_self_const_mul hc g l)⟩

/-! ### Multiplication -/

theorem IsBigOWith.mul {f₁ f₂ : α → R} {g₁ g₂ : α → S} {c₁ c₂ : ℝ} (h₁ : IsBigOWith c₁ l f₁ g₁)
    (h₂ : IsBigOWith c₂ l f₂ g₂) :
    IsBigOWith (c₁ * c₂) l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x := by
  simp only [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_trans (norm_mul_le _ _)
  convert! mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_mul, mul_mul_mul_comm]

theorem IsBigO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =O[l] fun x => g₁ x * g₂ x :=
  let ⟨_c, hc⟩ := h₁.isBigOWith
  let ⟨_c', hc'⟩ := h₂.isBigOWith
  (hc.mul hc').isBigO

theorem IsBigO.mul_isLittleO {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel₀ _ (ne_of_gt c'pos))

theorem IsLittleO.mul_isBigO {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x ↦ f₁ x * f₂ x) =o[l] fun x ↦ g₁ x * g₂ x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel₀ _ (ne_of_gt c'pos))

theorem IsLittleO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → S} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x ↦ f₁ x * f₂ x) =o[l] fun x ↦ g₁ x * g₂ x :=
  h₁.mul_isBigO h₂.isBigO

theorem IsBigOWith.pow' [NormOneClass S] {f : α → R} {g : α → S} (h : IsBigOWith c l f g) :
    ∀ n : ℕ, IsBigOWith (Nat.casesOn n ‖(1 : R)‖ fun n ↦ c ^ (n + 1))
      l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by
    have : Nontrivial S := NormOneClass.nontrivial
    simpa using isBigOWith_const_const (1 : R) (one_ne_zero' S) l
  | 1 => by simpa
  | n + 2 => by simpa [pow_succ] using (IsBigOWith.pow' h (n + 1)).mul h

theorem IsBigOWith.pow [NormOneClass R] [NormOneClass S]
    {f : α → R} {g : α → S} (h : IsBigOWith c l f g) :
    ∀ n : ℕ, IsBigOWith (c ^ n) l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by simpa using h.pow' 0
  | n + 1 => h.pow' (n + 1)

theorem IsBigOWith.of_pow [NormOneClass S] {n : ℕ} {f : α → S} {g : α → R}
    (h : IsBigOWith c l (f ^ n) (g ^ n)) (hn : n ≠ 0) (hc : c ≤ c' ^ n) (hc' : 0 ≤ c') :
    IsBigOWith c' l f g :=
  IsBigOWith.of_bound <| (h.weaken hc).bound.mono fun x hx ↦
    le_of_pow_le_pow_left₀ hn (by positivity) <|
      calc
        ‖f x‖ ^ n = ‖f x ^ n‖ := (norm_pow _ _).symm
        _ ≤ c' ^ n * ‖g x ^ n‖ := hx
        _ ≤ c' ^ n * ‖g x‖ ^ n := by gcongr; exact norm_pow_le' _ hn.bot_lt
        _ = (c' * ‖g x‖) ^ n := (mul_pow _ _ _).symm

theorem IsBigO.pow [NormOneClass S] {f : α → R} {g : α → S} (h : f =O[l] g) (n : ℕ) :
    (fun x => f x ^ n) =O[l] fun x => g x ^ n :=
  let ⟨_C, hC⟩ := h.isBigOWith
  isBigO_iff_isBigOWith.2 ⟨_, hC.pow' n⟩

theorem IsLittleO.pow {f : α → R} {g : α → S} (h : f =o[l] g) {n : ℕ} (hn : 0 < n) :
    (fun x => f x ^ n) =o[l] fun x => g x ^ n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'; clear hn
  induction n with
  | zero => simpa only [pow_one]
  | succ n ihn => convert! ihn.mul h <;> simp [pow_succ]

theorem IsLittleO.of_pow [NormOneClass S] {f : α → S} {g : α → R} {n : ℕ}
    (h : (f ^ n) =o[l] (g ^ n)) (hn : n ≠ 0) : f =o[l] g :=
  IsLittleO.of_isBigOWith fun _c hc => (h.def' <| pow_pos hc _).of_pow hn le_rfl hc.le

/-! ### Inverse -/

theorem IsBigOWith.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : IsBigOWith c l f g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : IsBigOWith c l (fun x => (g x)⁻¹) fun x => (f x)⁻¹ := by
  refine IsBigOWith.of_bound (h.bound.mp (h₀.mono fun x h₀ hle => ?_))
  rcases eq_or_ne (f x) 0 with hx | hx
  · simp only [hx, h₀ hx, inv_zero, norm_zero, mul_zero, le_rfl]
  · have hc : 0 < c := pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le hle) (norm_nonneg _)
    replace hle := inv_anti₀ (norm_pos_iff.2 hx) hle
    simpa only [norm_inv, mul_inv, ← div_eq_inv_mul, div_le_iff₀ hc] using! hle

theorem IsBigO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =O[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =O[l] fun x => (f x)⁻¹ :=
  let ⟨_c, hc⟩ := h.isBigOWith
  (hc.inv_rev h₀).isBigO

theorem IsLittleO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =o[l] g)
    (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) : (fun x => (g x)⁻¹) =o[l] fun x => (f x)⁻¹ :=
  IsLittleO.of_isBigOWith fun _c hc => (h.def' hc).inv_rev h₀

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `IsBigOWith` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/

section EventuallyMulDivCancel

variable {u v : α → 𝕜}

theorem IsBigOWith.eventually_mul_div_cancel (h : IsBigOWith c l u v) : u / v * v =ᶠ[l] u :=
  Eventually.mono h.bound fun y hy => div_mul_cancel_of_imp fun hv => by simpa [hv] using hy

/-- If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsBigO.eventually_mul_div_cancel (h : u =O[l] v) : u / v * v =ᶠ[l] u :=
  let ⟨_c, hc⟩ := h.isBigOWith
  hc.eventually_mul_div_cancel

/-- If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsLittleO.eventually_mul_div_cancel (h : u =o[l] v) : u / v * v =ᶠ[l] u :=
  (h.forall_isBigOWith zero_lt_one).eventually_mul_div_cancel

end EventuallyMulDivCancel

end Asymptotics
