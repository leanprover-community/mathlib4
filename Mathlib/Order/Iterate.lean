/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathlib.Logic.Function.Iterate
import Mathlib.Order.Monotone.Basic

#align_import order.iterate from "leanprover-community/mathlib"@"2258b40dacd2942571c8ce136215350c702dc78f"

/-!
# Inequalities on iterates

In this file we prove some inequalities comparing `f^[n] x` and `g^[n] x` where `f` and `g` are
two self-maps that commute with each other.

Current selection of inequalities is motivated by formalization of the rotation number of
a circle homeomorphism.
-/

set_option autoImplicit true


open Function

open Function (Commute)

namespace Monotone

variable [Preorder α] {f : α → α} {x y : ℕ → α}

/-!
### Comparison of two sequences

If $f$ is a monotone function, then $∀ k, x_{k+1} ≤ f(x_k)$ implies that $x_k$ grows slower than
$f^k(x_0)$, and similarly for the reversed inequalities. If $x_k$ and $y_k$ are two sequences such
that $x_{k+1} ≤ f(x_k)$ and $y_{k+1} ≥ f(y_k)$ for all $k < n$, then $x_0 ≤ y_0$ implies
$x_n ≤ y_n$, see `Monotone.seq_le_seq`.

If some of the inequalities in this lemma are strict, then we have $x_n < y_n$. The rest of the
lemmas in this section formalize this fact for different inequalities made strict.
-/


theorem seq_le_seq (hf : Monotone f) (n : ℕ) (h₀ : x 0 ≤ y 0) (hx : ∀ k < n, x (k + 1) ≤ f (x k))
    (hy : ∀ k < n, f (y k) ≤ y (k + 1)) : x n ≤ y n := by
  induction' n with n ihn
  -- ⊢ x Nat.zero ≤ y Nat.zero
  · exact h₀
    -- 🎉 no goals
  · refine' (hx _ n.lt_succ_self).trans ((hf $ ihn _ _).trans (hy _ n.lt_succ_self))
    -- ⊢ ∀ (k : ℕ), k < n → x (k + 1) ≤ f (x k)
    exact fun k hk => hx _ (hk.trans n.lt_succ_self)
    -- ⊢ ∀ (k : ℕ), k < n → f (y k) ≤ y (k + 1)
    exact fun k hk => hy _ (hk.trans n.lt_succ_self)
    -- 🎉 no goals
#align monotone.seq_le_seq Monotone.seq_le_seq

theorem seq_pos_lt_seq_of_lt_of_le (hf : Monotone f) {n : ℕ} (hn : 0 < n) (h₀ : x 0 ≤ y 0)
    (hx : ∀ k < n, x (k + 1) < f (x k)) (hy : ∀ k < n, f (y k) ≤ y (k + 1)) : x n < y n := by
  induction' n with n ihn
  -- ⊢ x Nat.zero < y Nat.zero
  · exact hn.false.elim
    -- 🎉 no goals
  suffices x n ≤ y n from (hx n n.lt_succ_self).trans_le ((hf this).trans $ hy n n.lt_succ_self)
  -- ⊢ x n ≤ y n
  cases n with
  | zero => exact h₀
  | succ n =>
    refine' (ihn n.zero_lt_succ (fun k hk => hx _ _) fun k hk => hy _ _).le <;>
    exact hk.trans n.succ.lt_succ_self
#align monotone.seq_pos_lt_seq_of_lt_of_le Monotone.seq_pos_lt_seq_of_lt_of_le

theorem seq_pos_lt_seq_of_le_of_lt (hf : Monotone f) {n : ℕ} (hn : 0 < n) (h₀ : x 0 ≤ y 0)
    (hx : ∀ k < n, x (k + 1) ≤ f (x k)) (hy : ∀ k < n, f (y k) < y (k + 1)) : x n < y n :=
  hf.dual.seq_pos_lt_seq_of_lt_of_le hn h₀ hy hx
#align monotone.seq_pos_lt_seq_of_le_of_lt Monotone.seq_pos_lt_seq_of_le_of_lt

theorem seq_lt_seq_of_lt_of_le (hf : Monotone f) (n : ℕ) (h₀ : x 0 < y 0)
    (hx : ∀ k < n, x (k + 1) < f (x k)) (hy : ∀ k < n, f (y k) ≤ y (k + 1)) : x n < y n := by
  cases n
  -- ⊢ x Nat.zero < y Nat.zero
  exacts [h₀, hf.seq_pos_lt_seq_of_lt_of_le (Nat.zero_lt_succ _) h₀.le hx hy]
  -- 🎉 no goals
#align monotone.seq_lt_seq_of_lt_of_le Monotone.seq_lt_seq_of_lt_of_le

theorem seq_lt_seq_of_le_of_lt (hf : Monotone f) (n : ℕ) (h₀ : x 0 < y 0)
    (hx : ∀ k < n, x (k + 1) ≤ f (x k)) (hy : ∀ k < n, f (y k) < y (k + 1)) : x n < y n :=
  hf.dual.seq_lt_seq_of_lt_of_le n h₀ hy hx
#align monotone.seq_lt_seq_of_le_of_lt Monotone.seq_lt_seq_of_le_of_lt

/-!
### Iterates of two functions

In this section we compare the iterates of a monotone function `f : α → α` to iterates of any
function `g : β → β`. If `h : β → α` satisfies `h ∘ g ≤ f ∘ h`, then `h (g^[n] x)` grows slower
than `f^[n] (h x)`, and similarly for the reversed inequality.

Then we specialize these two lemmas to the case `β = α`, `h = id`.
-/


variable {g : β → β} {h : β → α}

open Function

theorem le_iterate_comp_of_le (hf : Monotone f) (H : h ∘ g ≤ f ∘ h) (n : ℕ) :
    h ∘ g^[n] ≤ f^[n] ∘ h := fun x => by
  apply hf.seq_le_seq n <;> intros <;>
                            -- ⊢ (h ∘ g^[0]) x ≤ (f^[0] ∘ h) x
                            -- ⊢ (h ∘ g^[k✝ + 1]) x ≤ f ((h ∘ g^[k✝]) x)
                            -- ⊢ f ((f^[k✝] ∘ h) x) ≤ (f^[k✝ + 1] ∘ h) x
    simp [iterate_succ', -iterate_succ, comp_apply, id_eq, le_refl]
    -- 🎉 no goals
    -- ⊢ h (g (g^[k✝] x)) ≤ f (h (g^[k✝] x))
    -- 🎉 no goals
  case hx => exact H _
  -- 🎉 no goals
  -- 🎉 no goals
#align monotone.le_iterate_comp_of_le Monotone.le_iterate_comp_of_le

theorem iterate_comp_le_of_le (hf : Monotone f) (H : f ∘ h ≤ h ∘ g) (n : ℕ) :
    f^[n] ∘ h ≤ h ∘ g^[n] :=
  hf.dual.le_iterate_comp_of_le H n
#align monotone.iterate_comp_le_of_le Monotone.iterate_comp_le_of_le

/-- If `f ≤ g` and `f` is monotone, then `f^[n] ≤ g^[n]`. -/
theorem iterate_le_of_le {g : α → α} (hf : Monotone f) (h : f ≤ g) (n : ℕ) : f^[n] ≤ g^[n] :=
  hf.iterate_comp_le_of_le h n
#align monotone.iterate_le_of_le Monotone.iterate_le_of_le

/-- If `f ≤ g` and `g` is monotone, then `f^[n] ≤ g^[n]`. -/
theorem le_iterate_of_le {g : α → α} (hg : Monotone g) (h : f ≤ g) (n : ℕ) : f^[n] ≤ g^[n] :=
  hg.dual.iterate_le_of_le h n
#align monotone.le_iterate_of_le Monotone.le_iterate_of_le

end Monotone

/-!
### Comparison of iterations and the identity function

If $f(x) ≤ x$ for all $x$ (we express this as `f ≤ id` in the code), then the same is true for
any iterate of $f$, and similarly for the reversed inequality.
-/


namespace Function

section Preorder

variable [Preorder α] {f : α → α}

/-- If $x ≤ f x$ for all $x$ (we write this as `id ≤ f`), then the same is true for any iterate
`f^[n]` of `f`. -/
theorem id_le_iterate_of_id_le (h : id ≤ f) (n : ℕ) : id ≤ f^[n] := by
  simpa only [iterate_id] using monotone_id.iterate_le_of_le h n
  -- 🎉 no goals
#align function.id_le_iterate_of_id_le Function.id_le_iterate_of_id_le

theorem iterate_le_id_of_le_id (h : f ≤ id) (n : ℕ) : f^[n] ≤ id :=
  @id_le_iterate_of_id_le αᵒᵈ _ f h n
#align function.iterate_le_id_of_le_id Function.iterate_le_id_of_le_id

theorem monotone_iterate_of_id_le (h : id ≤ f) : Monotone fun m => f^[m] :=
  monotone_nat_of_le_succ $ fun n x => by
    rw [iterate_succ_apply']
    -- ⊢ f^[n] x ≤ f (f^[n] x)
    exact h _
    -- 🎉 no goals
#align function.monotone_iterate_of_id_le Function.monotone_iterate_of_id_le

theorem antitone_iterate_of_le_id (h : f ≤ id) : Antitone fun m => f^[m] := fun m n hmn =>
  @monotone_iterate_of_id_le αᵒᵈ _ f h m n hmn
#align function.antitone_iterate_of_le_id Function.antitone_iterate_of_le_id

end Preorder

/-!
### Iterates of commuting functions

If `f` and `g` are monotone and commute, then `f x ≤ g x` implies `f^[n] x ≤ g^[n] x`, see
`Function.Commute.iterate_le_of_map_le`. We also prove two strict inequality versions of this lemma,
as well as `iff` versions.
-/


namespace Commute

section Preorder

variable [Preorder α] {f g : α → α}

theorem iterate_le_of_map_le (h : Commute f g) (hf : Monotone f) (hg : Monotone g) {x}
    (hx : f x ≤ g x) (n : ℕ) : f^[n] x ≤ g^[n] x := by
  apply hf.seq_le_seq n
  · rfl
    -- 🎉 no goals
  · intros; rw [iterate_succ_apply']
    -- ⊢ f^[k✝ + 1] x ≤ f (f^[k✝] x)
            -- 🎉 no goals
  · intros; simp [h.iterate_right _ _, hg.iterate _ hx];
    -- ⊢ f (g^[k✝] x) ≤ g^[k✝ + 1] x
            -- 🎉 no goals
#align function.commute.iterate_le_of_map_le Function.Commute.iterate_le_of_map_le

theorem iterate_pos_lt_of_map_lt (h : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x}
    (hx : f x < g x) {n} (hn : 0 < n) : f^[n] x < g^[n] x := by
  apply hf.seq_pos_lt_seq_of_le_of_lt hn
  · rfl
    -- 🎉 no goals
  · intros; rw [iterate_succ_apply']
    -- ⊢ f^[k✝ + 1] x ≤ f (f^[k✝] x)
            -- 🎉 no goals
  · intros; simp [h.iterate_right _ _, hg.iterate _ hx]
    -- ⊢ f (g^[k✝] x) < g^[k✝ + 1] x
            -- 🎉 no goals
#align function.commute.iterate_pos_lt_of_map_lt Function.Commute.iterate_pos_lt_of_map_lt

theorem iterate_pos_lt_of_map_lt' (h : Commute f g) (hf : StrictMono f) (hg : Monotone g) {x}
    (hx : f x < g x) {n} (hn : 0 < n) : f^[n] x < g^[n] x :=
  @iterate_pos_lt_of_map_lt αᵒᵈ _ g f h.symm hg.dual hf.dual x hx n hn
#align function.commute.iterate_pos_lt_of_map_lt' Function.Commute.iterate_pos_lt_of_map_lt'

end Preorder

variable [LinearOrder α] {f g : α → α}

theorem iterate_pos_lt_iff_map_lt (h : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n}
    (hn : 0 < n) : f^[n] x < g^[n] x ↔ f x < g x := by
  rcases lt_trichotomy (f x) (g x) with (H | H | H)
  · simp only [*, iterate_pos_lt_of_map_lt]
    -- 🎉 no goals
  · simp only [*, h.iterate_eq_of_map_eq, lt_irrefl]
    -- 🎉 no goals
  · simp only [lt_asymm H, lt_asymm (h.symm.iterate_pos_lt_of_map_lt' hg hf H hn)]
    -- 🎉 no goals
#align function.commute.iterate_pos_lt_iff_map_lt Function.Commute.iterate_pos_lt_iff_map_lt

theorem iterate_pos_lt_iff_map_lt' (h : Commute f g) (hf : StrictMono f) (hg : Monotone g) {x n}
    (hn : 0 < n) : f^[n] x < g^[n] x ↔ f x < g x :=
  @iterate_pos_lt_iff_map_lt αᵒᵈ _ _ _ h.symm hg.dual hf.dual x n hn
#align function.commute.iterate_pos_lt_iff_map_lt' Function.Commute.iterate_pos_lt_iff_map_lt'

theorem iterate_pos_le_iff_map_le (h : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n}
    (hn : 0 < n) : f^[n] x ≤ g^[n] x ↔ f x ≤ g x := by
  simpa only [not_lt] using not_congr (h.symm.iterate_pos_lt_iff_map_lt' hg hf hn)
  -- 🎉 no goals
#align function.commute.iterate_pos_le_iff_map_le Function.Commute.iterate_pos_le_iff_map_le

theorem iterate_pos_le_iff_map_le' (h : Commute f g) (hf : StrictMono f) (hg : Monotone g) {x n}
    (hn : 0 < n) : f^[n] x ≤ g^[n] x ↔ f x ≤ g x := by
  simpa only [not_lt] using not_congr (h.symm.iterate_pos_lt_iff_map_lt hg hf hn)
  -- 🎉 no goals
#align function.commute.iterate_pos_le_iff_map_le' Function.Commute.iterate_pos_le_iff_map_le'

theorem iterate_pos_eq_iff_map_eq (h : Commute f g) (hf : Monotone f) (hg : StrictMono g) {x n}
    (hn : 0 < n) : f^[n] x = g^[n] x ↔ f x = g x := by
  simp only [le_antisymm_iff, h.iterate_pos_le_iff_map_le hf hg hn,
    h.symm.iterate_pos_le_iff_map_le' hg hf hn]
#align function.commute.iterate_pos_eq_iff_map_eq Function.Commute.iterate_pos_eq_iff_map_eq

end Commute

end Function

namespace Monotone

variable [Preorder α] {f : α → α} {x : α}

/-- If `f` is a monotone map and `x ≤ f x` at some point `x`, then the iterates `f^[n] x` form
a monotone sequence. -/
theorem monotone_iterate_of_le_map (hf : Monotone f) (hx : x ≤ f x) : Monotone fun n => f^[n] x :=
  monotone_nat_of_le_succ $ fun n => by
    rw [iterate_succ_apply]
    -- ⊢ f^[n] x ≤ f^[n] (f x)
    exact hf.iterate n hx
    -- 🎉 no goals
#align monotone.monotone_iterate_of_le_map Monotone.monotone_iterate_of_le_map

/-- If `f` is a monotone map and `f x ≤ x` at some point `x`, then the iterates `f^[n] x` form
an antitone sequence. -/
theorem antitone_iterate_of_map_le (hf : Monotone f) (hx : f x ≤ x) : Antitone fun n => f^[n] x :=
  hf.dual.monotone_iterate_of_le_map hx
#align monotone.antitone_iterate_of_map_le Monotone.antitone_iterate_of_map_le

end Monotone

namespace StrictMono

variable [Preorder α] {f : α → α} {x : α}

/-- If `f` is a strictly monotone map and `x < f x` at some point `x`, then the iterates `f^[n] x`
form a strictly monotone sequence. -/
theorem strictMono_iterate_of_lt_map (hf : StrictMono f) (hx : x < f x) :
    StrictMono fun n => f^[n] x :=
  strictMono_nat_of_lt_succ $ fun n => by
    rw [iterate_succ_apply]
    -- ⊢ f^[n] x < f^[n] (f x)
    exact hf.iterate n hx
    -- 🎉 no goals
#align strict_mono.strict_mono_iterate_of_lt_map StrictMono.strictMono_iterate_of_lt_map

/-- If `f` is a strictly antitone map and `f x < x` at some point `x`, then the iterates `f^[n] x`
form a strictly antitone sequence. -/
theorem strictAnti_iterate_of_map_lt (hf : StrictMono f) (hx : f x < x) :
    StrictAnti fun n => f^[n] x :=
  hf.dual.strictMono_iterate_of_lt_map hx
#align strict_mono.strict_anti_iterate_of_map_lt StrictMono.strictAnti_iterate_of_map_lt

end StrictMono
