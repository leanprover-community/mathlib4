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

variable {α β : Type*}

namespace Filter

section OrderedAddCommMonoid

variable [OrderedAddCommMonoid β] {l : Filter α} {f g : α → β}

theorem tendsto_atTop_add_nonneg_left' (hf : ∀ᶠ x in l, 0 ≤ f x) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x + g x) l atTop :=
  tendsto_atTop_mono' l (hf.mono fun _ => le_add_of_nonneg_left) hg

theorem tendsto_atBot_add_nonpos_left' (hf : ∀ᶠ x in l, f x ≤ 0) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x + g x) l atBot :=
  @tendsto_atTop_add_nonneg_left' _ βᵒᵈ _ _ _ _ hf hg

theorem tendsto_atTop_add_nonneg_left (hf : ∀ x, 0 ≤ f x) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x + g x) l atTop :=
  tendsto_atTop_add_nonneg_left' (Eventually.of_forall hf) hg

theorem tendsto_atBot_add_nonpos_left (hf : ∀ x, f x ≤ 0) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x + g x) l atBot :=
  @tendsto_atTop_add_nonneg_left _ βᵒᵈ _ _ _ _ hf hg

theorem tendsto_atTop_add_nonneg_right' (hf : Tendsto f l atTop) (hg : ∀ᶠ x in l, 0 ≤ g x) :
    Tendsto (fun x => f x + g x) l atTop :=
  tendsto_atTop_mono' l (monotone_mem (fun _ => le_add_of_nonneg_right) hg) hf

theorem tendsto_atBot_add_nonpos_right' (hf : Tendsto f l atBot) (hg : ∀ᶠ x in l, g x ≤ 0) :
    Tendsto (fun x => f x + g x) l atBot :=
  @tendsto_atTop_add_nonneg_right' _ βᵒᵈ _ _ _ _ hf hg

theorem tendsto_atTop_add_nonneg_right (hf : Tendsto f l atTop) (hg : ∀ x, 0 ≤ g x) :
    Tendsto (fun x => f x + g x) l atTop :=
  tendsto_atTop_add_nonneg_right' hf (Eventually.of_forall hg)

theorem tendsto_atBot_add_nonpos_right (hf : Tendsto f l atBot) (hg : ∀ x, g x ≤ 0) :
    Tendsto (fun x => f x + g x) l atBot :=
  @tendsto_atTop_add_nonneg_right _ βᵒᵈ _ _ _ _ hf hg

theorem tendsto_atTop_add (hf : Tendsto f l atTop) (hg : Tendsto g l atTop) :
    Tendsto (fun x => f x + g x) l atTop :=
  tendsto_atTop_add_nonneg_left' (tendsto_atTop.mp hf 0) hg

theorem tendsto_atBot_add (hf : Tendsto f l atBot) (hg : Tendsto g l atBot) :
    Tendsto (fun x => f x + g x) l atBot :=
  @tendsto_atTop_add _ βᵒᵈ _ _ _ _ hf hg

theorem Tendsto.nsmul_atTop (hf : Tendsto f l atTop) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun x => n • f x) l atTop :=
  tendsto_atTop.2 fun y =>
    (tendsto_atTop.1 hf y).mp <|
      (tendsto_atTop.1 hf 0).mono fun x h₀ hy =>
        calc
          y ≤ f x := hy
          _ = 1 • f x := (one_nsmul _).symm
          _ ≤ n • f x := nsmul_le_nsmul_left h₀ hn

theorem Tendsto.nsmul_atBot (hf : Tendsto f l atBot) {n : ℕ} (hn : 0 < n) :
    Tendsto (fun x => n • f x) l atBot :=
  @Tendsto.nsmul_atTop α βᵒᵈ _ l f hf n hn

end OrderedAddCommMonoid

section OrderedCancelAddCommMonoid

variable [OrderedCancelAddCommMonoid β] {l : Filter α} {f g : α → β}

theorem tendsto_atTop_of_add_const_left (C : β) (hf : Tendsto (fun x => C + f x) l atTop) :
    Tendsto f l atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (C + b)).mono fun _ => le_of_add_le_add_left

-- Porting note: the "order dual" trick timeouts
theorem tendsto_atBot_of_add_const_left (C : β) (hf : Tendsto (fun x => C + f x) l atBot) :
    Tendsto f l atBot :=
  tendsto_atBot.2 fun b => (tendsto_atBot.1 hf (C + b)).mono fun _ => le_of_add_le_add_left

theorem tendsto_atTop_of_add_const_right (C : β) (hf : Tendsto (fun x => f x + C) l atTop) :
    Tendsto f l atTop :=
  tendsto_atTop.2 fun b => (tendsto_atTop.1 hf (b + C)).mono fun _ => le_of_add_le_add_right

-- Porting note: the "order dual" trick timeouts
theorem tendsto_atBot_of_add_const_right (C : β) (hf : Tendsto (fun x => f x + C) l atBot) :
    Tendsto f l atBot :=
  tendsto_atBot.2 fun b => (tendsto_atBot.1 hf (b + C)).mono fun _ => le_of_add_le_add_right

theorem tendsto_atTop_of_add_bdd_above_left' (C) (hC : ∀ᶠ x in l, f x ≤ C)
    (h : Tendsto (fun x => f x + g x) l atTop) : Tendsto g l atTop :=
  tendsto_atTop_of_add_const_left C
    (tendsto_atTop_mono' l (hC.mono fun x hx => add_le_add_right hx (g x)) h)

-- Porting note: the "order dual" trick timeouts
theorem tendsto_atBot_of_add_bdd_below_left' (C) (hC : ∀ᶠ x in l, C ≤ f x)
    (h : Tendsto (fun x => f x + g x) l atBot) : Tendsto g l atBot :=
  tendsto_atBot_of_add_const_left C
    (tendsto_atBot_mono' l (hC.mono fun x hx => add_le_add_right hx (g x)) h)

theorem tendsto_atTop_of_add_bdd_above_left (C) (hC : ∀ x, f x ≤ C) :
    Tendsto (fun x => f x + g x) l atTop → Tendsto g l atTop :=
  tendsto_atTop_of_add_bdd_above_left' C (univ_mem' hC)

-- Porting note: the "order dual" trick timeouts
theorem tendsto_atBot_of_add_bdd_below_left (C) (hC : ∀ x, C ≤ f x) :
    Tendsto (fun x => f x + g x) l atBot → Tendsto g l atBot :=
  tendsto_atBot_of_add_bdd_below_left' C (univ_mem' hC)

theorem tendsto_atTop_of_add_bdd_above_right' (C) (hC : ∀ᶠ x in l, g x ≤ C)
    (h : Tendsto (fun x => f x + g x) l atTop) : Tendsto f l atTop :=
  tendsto_atTop_of_add_const_right C
    (tendsto_atTop_mono' l (hC.mono fun x hx => add_le_add_left hx (f x)) h)

-- Porting note: the "order dual" trick timeouts
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
