/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Order.BoundedOrder

/-!
# The natural numbers form a linear order

This file contains the linear order instance on the natural numbers.

See note [foundational algebra order theory].
-/

open Function

variable {α : Type*} {β : Type*}

namespace Nat

instance instOrderBot : OrderBot ℕ where
  bot := 0
  bot_le := zero_le
#align nat.order_bot Nat.instOrderBot

/-! ### Miscellaneous lemmas -/

-- We want to use this lemma earlier than the lemma simp can prove it with
@[simp, nolint simpNF] protected lemma bot_eq_zero : ⊥ = 0 := rfl

instance instLinearOrder : LinearOrder ℕ where
  le := Nat.le
  le_refl := @Nat.le_refl
  le_trans := @Nat.le_trans
  le_antisymm := @Nat.le_antisymm
  le_total := @Nat.le_total
  lt := Nat.lt
  lt_iff_le_not_le := @Nat.lt_iff_le_not_le
  decidableLT := inferInstance
  decidableLE := inferInstance
  decidableEq := inferInstance
#align nat.linear_order Nat.instLinearOrder

instance : DistribLattice ℕ := inferInstance

instance lt.isWellOrder : IsWellOrder ℕ (· < ·) where
#align nat.lt.is_well_order Nat.lt.isWellOrder

end Nat

/-! ### Monotonicity in `ℕ` and `ℤ` -/

section Preorder

variable [Preorder α]

theorem Nat.rel_of_forall_rel_succ_of_le_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℕ → β} {a : ℕ}
    (h : ∀ n, a ≤ n → r (f n) (f (n + 1))) ⦃b c : ℕ⦄ (hab : a ≤ b) (hbc : b < c) :
    r (f b) (f c) := by
  induction' hbc with k b_lt_k r_b_k
  exacts [h _ hab, _root_.trans r_b_k (h _ (hab.trans_lt b_lt_k).le)]
#align nat.rel_of_forall_rel_succ_of_le_of_lt Nat.rel_of_forall_rel_succ_of_le_of_lt

theorem Nat.rel_of_forall_rel_succ_of_le_of_le (r : β → β → Prop) [IsRefl β r] [IsTrans β r]
    {f : ℕ → β} {a : ℕ} (h : ∀ n, a ≤ n → r (f n) (f (n + 1)))
    ⦃b c : ℕ⦄ (hab : a ≤ b) (hbc : b ≤ c) : r (f b) (f c) :=
  hbc.eq_or_lt.elim (fun h ↦ h ▸ refl _) (Nat.rel_of_forall_rel_succ_of_le_of_lt r h hab)
#align nat.rel_of_forall_rel_succ_of_le_of_le Nat.rel_of_forall_rel_succ_of_le_of_le

theorem Nat.rel_of_forall_rel_succ_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℕ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℕ⦄ (hab : a < b) : r (f a) (f b) :=
  Nat.rel_of_forall_rel_succ_of_le_of_lt r (fun n _ ↦ h n) le_rfl hab
#align nat.rel_of_forall_rel_succ_of_lt Nat.rel_of_forall_rel_succ_of_lt

theorem Nat.rel_of_forall_rel_succ_of_le (r : β → β → Prop) [IsRefl β r] [IsTrans β r] {f : ℕ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℕ⦄ (hab : a ≤ b) : r (f a) (f b) :=
  Nat.rel_of_forall_rel_succ_of_le_of_le r (fun n _ ↦ h n) le_rfl hab
#align nat.rel_of_forall_rel_succ_of_le Nat.rel_of_forall_rel_succ_of_le

theorem monotone_nat_of_le_succ {f : ℕ → α} (hf : ∀ n, f n ≤ f (n + 1)) : Monotone f :=
  Nat.rel_of_forall_rel_succ_of_le (· ≤ ·) hf
#align monotone_nat_of_le_succ monotone_nat_of_le_succ

theorem antitone_nat_of_succ_le {f : ℕ → α} (hf : ∀ n, f (n + 1) ≤ f n) : Antitone f :=
  @monotone_nat_of_le_succ αᵒᵈ _ _ hf
#align antitone_nat_of_succ_le antitone_nat_of_succ_le

theorem strictMono_nat_of_lt_succ {f : ℕ → α} (hf : ∀ n, f n < f (n + 1)) : StrictMono f :=
  Nat.rel_of_forall_rel_succ_of_lt (· < ·) hf
#align strict_mono_nat_of_lt_succ strictMono_nat_of_lt_succ

theorem strictAnti_nat_of_succ_lt {f : ℕ → α} (hf : ∀ n, f (n + 1) < f n) : StrictAnti f :=
  @strictMono_nat_of_lt_succ αᵒᵈ _ f hf
#align strict_anti_nat_of_succ_lt strictAnti_nat_of_succ_lt

namespace Nat

/-- If `α` is a preorder with no maximal elements, then there exists a strictly monotone function
`ℕ → α` with any prescribed value of `f 0`. -/
theorem exists_strictMono' [NoMaxOrder α] (a : α) : ∃ f : ℕ → α, StrictMono f ∧ f 0 = a := by
  choose g hg using fun x : α ↦ exists_gt x
  exact ⟨fun n ↦ Nat.recOn n a fun _ ↦ g, strictMono_nat_of_lt_succ fun n ↦ hg _, rfl⟩
#align nat.exists_strict_mono' Nat.exists_strictMono'

/-- If `α` is a preorder with no maximal elements, then there exists a strictly antitone function
`ℕ → α` with any prescribed value of `f 0`. -/
theorem exists_strictAnti' [NoMinOrder α] (a : α) : ∃ f : ℕ → α, StrictAnti f ∧ f 0 = a :=
  exists_strictMono' (OrderDual.toDual a)
#align nat.exists_strict_anti' Nat.exists_strictAnti'

variable (α)

/-- If `α` is a nonempty preorder with no maximal elements, then there exists a strictly monotone
function `ℕ → α`. -/
theorem exists_strictMono [Nonempty α] [NoMaxOrder α] : ∃ f : ℕ → α, StrictMono f :=
  let ⟨a⟩ := ‹Nonempty α›
  let ⟨f, hf, _⟩ := exists_strictMono' a
  ⟨f, hf⟩
#align nat.exists_strict_mono Nat.exists_strictMono

/-- If `α` is a nonempty preorder with no minimal elements, then there exists a strictly antitone
function `ℕ → α`. -/
theorem exists_strictAnti [Nonempty α] [NoMinOrder α] : ∃ f : ℕ → α, StrictAnti f :=
  exists_strictMono αᵒᵈ
#align nat.exists_strict_anti Nat.exists_strictAnti

end Nat

theorem Int.rel_of_forall_rel_succ_of_lt (r : β → β → Prop) [IsTrans β r] {f : ℤ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℤ⦄ (hab : a < b) : r (f a) (f b) := by
  rcases lt.dest hab with ⟨n, rfl⟩
  clear hab
  induction' n with n ihn
  · rw [Int.ofNat_one]
    apply h
  · rw [Int.ofNat_succ, ← Int.add_assoc]
    exact _root_.trans ihn (h _)
#align int.rel_of_forall_rel_succ_of_lt Int.rel_of_forall_rel_succ_of_lt

theorem Int.rel_of_forall_rel_succ_of_le (r : β → β → Prop) [IsRefl β r] [IsTrans β r] {f : ℤ → β}
    (h : ∀ n, r (f n) (f (n + 1))) ⦃a b : ℤ⦄ (hab : a ≤ b) : r (f a) (f b) :=
  hab.eq_or_lt.elim (fun h ↦ h ▸ refl _) fun h' ↦ Int.rel_of_forall_rel_succ_of_lt r h h'
#align int.rel_of_forall_rel_succ_of_le Int.rel_of_forall_rel_succ_of_le

theorem monotone_int_of_le_succ {f : ℤ → α} (hf : ∀ n, f n ≤ f (n + 1)) : Monotone f :=
  Int.rel_of_forall_rel_succ_of_le (· ≤ ·) hf
#align monotone_int_of_le_succ monotone_int_of_le_succ

theorem antitone_int_of_succ_le {f : ℤ → α} (hf : ∀ n, f (n + 1) ≤ f n) : Antitone f :=
  Int.rel_of_forall_rel_succ_of_le (· ≥ ·) hf
#align antitone_int_of_succ_le antitone_int_of_succ_le

theorem strictMono_int_of_lt_succ {f : ℤ → α} (hf : ∀ n, f n < f (n + 1)) : StrictMono f :=
  Int.rel_of_forall_rel_succ_of_lt (· < ·) hf
#align strict_mono_int_of_lt_succ strictMono_int_of_lt_succ

theorem strictAnti_int_of_succ_lt {f : ℤ → α} (hf : ∀ n, f (n + 1) < f n) : StrictAnti f :=
  Int.rel_of_forall_rel_succ_of_lt (· > ·) hf
#align strict_anti_int_of_succ_lt strictAnti_int_of_succ_lt

namespace Int

variable (α) [Preorder α] [Nonempty α] [NoMinOrder α] [NoMaxOrder α]

/-- If `α` is a nonempty preorder with no minimal or maximal elements, then there exists a strictly
monotone function `f : ℤ → α`. -/
theorem exists_strictMono : ∃ f : ℤ → α, StrictMono f := by
  inhabit α
  rcases Nat.exists_strictMono' (default : α) with ⟨f, hf, hf₀⟩
  rcases Nat.exists_strictAnti' (default : α) with ⟨g, hg, hg₀⟩
  refine ⟨fun n ↦ Int.casesOn n f fun n ↦ g (n + 1), strictMono_int_of_lt_succ ?_⟩
  rintro (n | _ | n)
  · exact hf n.lt_succ_self
  · show g 1 < f 0
    rw [hf₀, ← hg₀]
    exact hg Nat.zero_lt_one
  · exact hg (Nat.lt_succ_self _)
#align int.exists_strict_mono Int.exists_strictMono

/-- If `α` is a nonempty preorder with no minimal or maximal elements, then there exists a strictly
antitone function `f : ℤ → α`. -/
theorem exists_strictAnti : ∃ f : ℤ → α, StrictAnti f :=
  exists_strictMono αᵒᵈ
#align int.exists_strict_anti Int.exists_strictAnti

end Int

-- TODO@Yael: Generalize the following four to succ orders
/-- If `f` is a monotone function from `ℕ` to a preorder such that `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
theorem Monotone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : Monotone f) (n : ℕ) {x : α} (h1 : f n < x)
    (h2 : x < f (n + 1)) (a : ℕ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_le (Nat.le_of_lt_succ <| hf.reflect_lt h2)
#align monotone.ne_of_lt_of_lt_nat Monotone.ne_of_lt_of_lt_nat

/-- If `f` is an antitone function from `ℕ` to a preorder such that `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
theorem Antitone.ne_of_lt_of_lt_nat {f : ℕ → α} (hf : Antitone f) (n : ℕ) {x : α}
    (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℕ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_le (Nat.le_of_lt_succ <| hf.reflect_lt h1)
#align antitone.ne_of_lt_of_lt_nat Antitone.ne_of_lt_of_lt_nat

/-- If `f` is a monotone function from `ℤ` to a preorder and `x` lies between `f n` and
  `f (n + 1)`, then `x` doesn't lie in the range of `f`. -/
theorem Monotone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Monotone f) (n : ℤ) {x : α} (h1 : f n < x)
    (h2 : x < f (n + 1)) (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h1).not_le (Int.le_of_lt_add_one <| hf.reflect_lt h2)
#align monotone.ne_of_lt_of_lt_int Monotone.ne_of_lt_of_lt_int

/-- If `f` is an antitone function from `ℤ` to a preorder and `x` lies between `f (n + 1)` and
`f n`, then `x` doesn't lie in the range of `f`. -/
theorem Antitone.ne_of_lt_of_lt_int {f : ℤ → α} (hf : Antitone f) (n : ℤ) {x : α}
    (h1 : f (n + 1) < x) (h2 : x < f n) (a : ℤ) : f a ≠ x := by
  rintro rfl
  exact (hf.reflect_lt h2).not_le (Int.le_of_lt_add_one <| hf.reflect_lt h1)
#align antitone.ne_of_lt_of_lt_int Antitone.ne_of_lt_of_lt_int

theorem StrictMono.id_le {φ : ℕ → ℕ} (h : StrictMono φ) : ∀ n, n ≤ φ n := fun n ↦
  Nat.recOn n (Nat.zero_le _) fun n hn ↦ Nat.succ_le_of_lt (hn.trans_lt <| h <| Nat.lt_succ_self n)
#align strict_mono.id_le StrictMono.id_le

end Preorder
