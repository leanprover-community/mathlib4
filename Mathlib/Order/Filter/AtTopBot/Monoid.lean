/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Algebra.Order.Monoid.OrderDual
import Mathlib.Order.Filter.AtTopBot

/-!
# Convergence to ±infinity in ordered commutative monoids
-/

variable {α M : Type*}

namespace Filter

section OrderedCommMonoid

variable [OrderedCommMonoid M] {l : Filter α} {f g : α → M}

@[to_additive]
theorem Tendsto.one_eventuallyLE_mul_atTop (hf : 1 ≤ᶠ[l] f) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  tendsto_atTop_mono' l (hf.mono fun _ ↦ le_mul_of_one_le_left') hg

@[deprecated (since := "2024-11-21")]
alias tendsto_atTop_add_nonneg_left' := Tendsto.zero_eventuallyLE_add_atTop

@[to_additive]
theorem Tendsto.eventuallyLE_one_mul_atBot (hf : f ≤ᶠ[l] 1) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  hg.one_eventuallyLE_mul_atTop (M := Mᵒᵈ) hf

@[deprecated (since := "2024-11-21")]
alias tendsto_atBot_add_nonpos_left' := Tendsto.eventuallyLE_zero_add_atBot

@[to_additive]
theorem Tendsto.one_le_mul_atTop (hf : ∀ x, 1 ≤ f x) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  hg.one_eventuallyLE_mul_atTop (.of_forall hf)

@[to_additive]
theorem Tendsto.le_one_mul_atBot (hf : ∀ x, f x ≤ 1) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  hg.eventuallyLE_one_mul_atBot (.of_forall hf)

@[to_additive]
theorem Tendsto.atTop_mul_one_eventuallyLE (hf : Tendsto f l atTop) (hg : 1 ≤ᶠ[l] g) :
    Tendsto (fun x => f x * g x) l atTop :=
  tendsto_atTop_mono' l (hg.mono fun _ => le_mul_of_one_le_right') hf

@[to_additive]
theorem Tendsto.atBot_mul_eventuallyLE_one (hf : Tendsto f l atBot) (hg : g ≤ᶠ[l] 1) :
    Tendsto (fun x => f x * g x) l atBot :=
  hf.atTop_mul_one_eventuallyLE (M := Mᵒᵈ) hg

@[to_additive]
theorem Tendsto.atTop_mul_one_le (hf : Tendsto f l atTop) (hg : ∀ x, 1 ≤ g x) :
    Tendsto (fun x => f x * g x) l atTop :=
  hf.atTop_mul_one_eventuallyLE <| .of_forall hg

@[to_additive]
theorem Tendsto.atBot_mul_le_one (hf : Tendsto f l atBot) (hg : ∀ x, g x ≤ 1) :
    Tendsto (fun x => f x * g x) l atBot :=
  hf.atBot_mul_eventuallyLE_one (.of_forall hg)

@[to_additive]
theorem Tendsto.atTop_mul_atTop (hf : Tendsto f l atTop) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x * g x) l atTop :=
  hf.atTop_mul_one_eventuallyLE <| hg.eventually_ge_atTop 1

@[to_additive]
theorem Tendsto.atBot_mul_atBot (hf : Tendsto f l atBot) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x * g x) l atBot :=
  hf.atTop_mul_atTop (M := Mᵒᵈ) hg

@[to_additive nsmul_atTop]
theorem Tendsto.atTop_pow (hf : Tendsto f l atTop) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun x => f x ^ n) l atTop := by
  refine tendsto_atTop_mono' _ ((hf.eventually_ge_atTop 1).mono fun x hx ↦ ?_) hf
  simpa only [pow_one] using pow_le_pow_right' hx hn

@[to_additive nsmul_atBot]
theorem Tendsto.atBot_pow (hf : Tendsto f l atBot) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun x => f x ^ n) l atBot :=
  @Tendsto.atTop_pow α Mᵒᵈ _ l f hf n hn

end OrderedCommMonoid

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid M] {l : Filter α} {f g : α → M}

@[to_additive]
theorem Tendsto.atTop_of_const_mul (C : M) (hf : Tendsto (C * f ·) l atTop) : Tendsto f l atTop :=
  tendsto_atTop.2 fun b ↦ (tendsto_atTop.1 hf (C * b)).mono fun _ ↦ le_of_mul_le_mul_left'

@[to_additive]
theorem Tendsto.atBot_of_const_mul (C : M) (hf : Tendsto (C * f ·) l atBot) : Tendsto f l atBot :=
  hf.atTop_of_const_mul (M := Mᵒᵈ)

@[to_additive]
theorem Tendsto.atTop_of_mul_const (C : M) (hf : Tendsto (f · * C) l atTop) : Tendsto f l atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (b * C)).mono fun _ => le_of_mul_le_mul_right'

@[to_additive]
theorem Tendsto.atBot_of_mul_const (C : M) (hf : Tendsto (f · * C) l atBot) : Tendsto f l atBot :=
  hf.atTop_of_mul_const (M := Mᵒᵈ)

@[to_additive]
theorem Tendsto.atTop_of_eventuallyLE_const_mul (C : M) (hC : f ≤ᶠ[l] fun _ ↦ C)
    (h : Tendsto (fun x => f x * g x) l atTop) : Tendsto g l atTop :=
  .atTop_of_const_mul C <| tendsto_atTop_mono' l (hC.mono fun x hx => mul_le_mul_right' hx (g x)) h

@[to_additive]
theorem Tendsto.atBot_of_const_eventuallyLE_mul (C : M) (hC : (fun _ ↦ C) ≤ᶠ[l] f)
    (h : Tendsto (fun x => f x * g x) l atBot) : Tendsto g l atBot :=
  h.atTop_of_eventuallyLE_const_mul (M := Mᵒᵈ) C hC

@[to_additive]
theorem Tendsto.atTop_of_le_const_mul (C) (hC : ∀ x, f x ≤ C) :
    Tendsto (fun x => f x * g x) l atTop → Tendsto g l atTop :=
  .atTop_of_eventuallyLE_const_mul C (.of_forall hC)

@[to_additive]
theorem Tendsto.atBot_of_const_le_mul (C) (hC : ∀ x, C ≤ f x) :
    Tendsto (fun x => f x * g x) l atBot → Tendsto g l atBot :=
  .atTop_of_le_const_mul (M := Mᵒᵈ) C hC

theorem Tendsto.atTop_of_mul_eventuallyLE_const (C) (hC : g ≤ᶠ[l] fun _ ↦ C)
    (h : Tendsto (fun x => f x * g x) l atTop) : Tendsto f l atTop :=
  .atTop_of_mul_const C (tendsto_atTop_mono' l (hC.mono fun x hx => mul_le_mul_left' hx (f x)) h)

theorem tendsto_atBot_of_add_bdd_below_right' (C) (hC : ∀ᶠ x in l, C ≤ g x)
    (h : Tendsto (fun x => f x + g x) l atBot) : Tendsto f l atBot :=
  tendsto_atBot_of_add_const_right C
    (tendsto_atBot_mono' l (hC.mono fun x hx => add_le_add_left hx (f x)) h)

theorem tendsto_atTop_of_add_bdd_above_right (C) (hC : ∀ x, g x ≤ C) :
    Tendsto (fun x => f x + g x) l atTop → Tendsto f l atTop :=
  tendsto_atTop_of_add_bdd_above_right' C (univ_mem' hC)

-- Porting note: the "order dual" trick timeouts
theorem tendsto_atBot_of_add_bdd_below_right (C) (hC : ∀ x, C ≤ g x) :
    Tendsto (fun x => f x + g x) l atBot → Tendsto f l atBot :=
  tendsto_atBot_of_add_bdd_below_right' C (univ_mem' hC)

end OrderedCancelAddCommMonoid

end Filter
