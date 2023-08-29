/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Logic.Function.Conjugate

#align_import logic.function.iterate from "leanprover-community/mathlib"@"792a2a264169d64986541c6f8f7e3bbb6acb6295"

/-!
# Iterations of a function

In this file we prove simple properties of `Nat.iterate f n` a.k.a. `f^[n]`:

* `iterate_zero`, `iterate_succ`, `iterate_succ'`, `iterate_add`, `iterate_mul`:
  formulas for `f^[0]`, `f^[n+1]` (two versions), `f^[n+m]`, and `f^[n*m]`;

* `iterate_id` : `id^[n]=id`;

* `Injective.iterate`, `Surjective.iterate`, `Bijective.iterate` :
  iterates of an injective/surjective/bijective function belong to the same class;

* `LeftInverse.iterate`, `RightInverse.iterate`, `Commute.iterate_left`, `Commute.iterate_right`,
  `Commute.iterate_iterate`:
  some properties of pairs of functions survive under iterations

* `iterate_fixed`, `Function.Semiconj.iterate_*`, `Function.Semiconj₂.iterate`:
  if `f` fixes a point (resp., semiconjugates unary/binary operations), then so does `f^[n]`.

-/


universe u v

variable {α : Type u} {β : Type v}

namespace Function

open Function (Commute)

variable (f : α → α)

@[simp]
theorem iterate_zero : f^[0] = id :=
  rfl
#align function.iterate_zero Function.iterate_zero

theorem iterate_zero_apply (x : α) : f^[0] x = x :=
  rfl
#align function.iterate_zero_apply Function.iterate_zero_apply

@[simp]
theorem iterate_succ (n : ℕ) : f^[n.succ] = f^[n] ∘ f :=
  rfl
#align function.iterate_succ Function.iterate_succ

theorem iterate_succ_apply (n : ℕ) (x : α) : f^[n.succ] x = f^[n] (f x) :=
  rfl
#align function.iterate_succ_apply Function.iterate_succ_apply

@[simp]
theorem iterate_id (n : ℕ) : (id : α → α)^[n] = id :=
  Nat.recOn n rfl fun n ihn ↦ by rw [iterate_succ, ihn, comp.left_id]
                                 -- 🎉 no goals
#align function.iterate_id Function.iterate_id

theorem iterate_add (m : ℕ) : ∀ n : ℕ, f^[m + n] = f^[m] ∘ f^[n]
  | 0 => rfl
  | Nat.succ n => by rw [Nat.add_succ, iterate_succ, iterate_succ, iterate_add m n]; rfl
                     -- ⊢ (f^[m] ∘ f^[n]) ∘ f = f^[m] ∘ f^[n] ∘ f
                                                                                     -- 🎉 no goals
#align function.iterate_add Function.iterate_add

theorem iterate_add_apply (m n : ℕ) (x : α) : f^[m + n] x = f^[m] (f^[n] x) := by
  rw [iterate_add f m n]
  -- ⊢ (f^[m] ∘ f^[n]) x = f^[m] (f^[n] x)
  rfl
  -- 🎉 no goals
#align function.iterate_add_apply Function.iterate_add_apply

@[simp]
theorem iterate_one : f^[1] = f :=
  funext fun _ ↦ rfl
#align function.iterate_one Function.iterate_one

theorem iterate_mul (m : ℕ) : ∀ n, f^[m * n] = f^[m]^[n]
  | 0 => by simp only [Nat.mul_zero, iterate_zero]
            -- 🎉 no goals
  | n + 1 => by simp only [Nat.mul_succ, Nat.mul_one, iterate_one, iterate_add, iterate_mul m n]
                -- 🎉 no goals
#align function.iterate_mul Function.iterate_mul

variable {f}

theorem iterate_fixed {x} (h : f x = x) (n : ℕ) : f^[n] x = x :=
  Nat.recOn n rfl fun n ihn ↦ by rw [iterate_succ_apply, h, ihn]
                                 -- 🎉 no goals
#align function.iterate_fixed Function.iterate_fixed

theorem Injective.iterate (Hinj : Injective f) (n : ℕ) : Injective f^[n] :=
  Nat.recOn n injective_id fun _ ihn ↦ ihn.comp Hinj
#align function.injective.iterate Function.Injective.iterate

theorem Surjective.iterate (Hsurj : Surjective f) (n : ℕ) : Surjective f^[n] :=
  Nat.recOn n surjective_id fun _ ihn ↦ ihn.comp Hsurj
#align function.surjective.iterate Function.Surjective.iterate

theorem Bijective.iterate (Hbij : Bijective f) (n : ℕ) : Bijective f^[n] :=
  ⟨Hbij.1.iterate n, Hbij.2.iterate n⟩
#align function.bijective.iterate Function.Bijective.iterate

namespace Semiconj

theorem iterate_right {f : α → β} {ga : α → α} {gb : β → β} (h : Semiconj f ga gb) (n : ℕ) :
    Semiconj f ga^[n] gb^[n] :=
  Nat.recOn n id_right fun _ ihn ↦ ihn.comp_right h
#align function.semiconj.iterate_right Function.Semiconj.iterate_right

theorem iterate_left {g : ℕ → α → α} (H : ∀ n, Semiconj f (g n) (g <| n + 1)) (n k : ℕ) :
    Semiconj f^[n] (g k) (g <| n + k) := by
  induction' n with n ihn generalizing k
  -- ⊢ Semiconj f^[Nat.zero] (g k) (g (Nat.zero + k))
  · rw [Nat.zero_add]
    -- ⊢ Semiconj f^[Nat.zero] (g k) (g k)
    exact id_left
    -- 🎉 no goals
  · rw [Nat.succ_eq_add_one, Nat.add_right_comm, Nat.add_assoc]
    -- ⊢ Semiconj f^[n + 1] (g k) (g (n + (k + 1)))
    exact (H k).comp_left (ihn (k + 1))
    -- 🎉 no goals
#align function.semiconj.iterate_left Function.Semiconj.iterate_left

end Semiconj

namespace Commute

variable {g : α → α}

theorem iterate_right (h : Commute f g) (n : ℕ) : Commute f g^[n] :=
  Semiconj.iterate_right h n
#align function.commute.iterate_right Function.Commute.iterate_right

theorem iterate_left (h : Commute f g) (n : ℕ) : Commute f^[n] g :=
  (h.symm.iterate_right n).symm
#align function.commute.iterate_left Function.Commute.iterate_left

theorem iterate_iterate (h : Commute f g) (m n : ℕ) : Commute f^[m] g^[n] :=
  (h.iterate_left m).iterate_right n
#align function.commute.iterate_iterate Function.Commute.iterate_iterate

theorem iterate_eq_of_map_eq (h : Commute f g) (n : ℕ) {x} (hx : f x = g x) :
    f^[n] x = g^[n] x :=
  Nat.recOn n rfl fun n ihn ↦ by
    simp only [iterate_succ_apply, hx, (h.iterate_left n).eq, ihn, ((refl g).iterate_right n).eq]
    -- 🎉 no goals
#align function.commute.iterate_eq_of_map_eq Function.Commute.iterate_eq_of_map_eq

theorem comp_iterate (h : Commute f g) (n : ℕ) : (f ∘ g)^[n] = f^[n] ∘ g^[n] := by
  induction' n with n ihn
  -- ⊢ (f ∘ g)^[Nat.zero] = f^[Nat.zero] ∘ g^[Nat.zero]
  · rfl
    -- 🎉 no goals
  funext x
  -- ⊢ (f ∘ g)^[Nat.succ n] x = (f^[Nat.succ n] ∘ g^[Nat.succ n]) x
  simp only [ihn, (h.iterate_right n).eq, iterate_succ, comp_apply]
  -- 🎉 no goals
#align function.commute.comp_iterate Function.Commute.comp_iterate

variable (f)

theorem iterate_self (n : ℕ) : Commute f^[n] f :=
  (refl f).iterate_left n
#align function.commute.iterate_self Function.Commute.iterate_self

theorem self_iterate (n : ℕ) : Commute f f^[n] :=
  (refl f).iterate_right n
#align function.commute.self_iterate Function.Commute.self_iterate

theorem iterate_iterate_self (m n : ℕ) : Commute f^[m] f^[n] :=
  (refl f).iterate_iterate m n
#align function.commute.iterate_iterate_self Function.Commute.iterate_iterate_self

end Commute

theorem Semiconj₂.iterate {f : α → α} {op : α → α → α} (hf : Semiconj₂ f op op) (n : ℕ) :
    Semiconj₂ f^[n] op op :=
  Nat.recOn n (Semiconj₂.id_left op) fun _ ihn ↦ ihn.comp hf
#align function.semiconj₂.iterate Function.Semiconj₂.iterate

variable (f)

theorem iterate_succ' (n : ℕ) : f^[n.succ] = f ∘ f^[n] := by
  rw [iterate_succ, (Commute.self_iterate f n).comp_eq]
  -- 🎉 no goals
#align function.iterate_succ' Function.iterate_succ'

theorem iterate_succ_apply' (n : ℕ) (x : α) : f^[n.succ] x = f (f^[n] x) := by
  rw [iterate_succ']
  -- ⊢ (f ∘ f^[n]) x = f (f^[n] x)
  rfl
  -- 🎉 no goals
#align function.iterate_succ_apply' Function.iterate_succ_apply'

theorem iterate_pred_comp_of_pos {n : ℕ} (hn : 0 < n) : f^[n.pred] ∘ f = f^[n] := by
  rw [← iterate_succ, Nat.succ_pred_eq_of_pos hn]
  -- 🎉 no goals
#align function.iterate_pred_comp_of_pos Function.iterate_pred_comp_of_pos

theorem comp_iterate_pred_of_pos {n : ℕ} (hn : 0 < n) : f ∘ f^[n.pred] = f^[n] := by
  rw [← iterate_succ', Nat.succ_pred_eq_of_pos hn]
  -- 🎉 no goals
#align function.comp_iterate_pred_of_pos Function.comp_iterate_pred_of_pos

/-- A recursor for the iterate of a function. -/
def Iterate.rec (p : α → Sort*) {f : α → α} (h : ∀ a, p a → p (f a)) {a : α} (ha : p a) (n : ℕ) :
    p (f^[n] a) :=
  match n with
  | 0 => ha
  | m+1 => Iterate.rec p h (h _ ha) m
#align function.iterate.rec Function.Iterate.rec

theorem Iterate.rec_zero (p : α → Sort*) {f : α → α} (h : ∀ a, p a → p (f a)) {a : α} (ha : p a) :
    Iterate.rec p h ha 0 = ha :=
  rfl
#align function.iterate.rec_zero Function.Iterate.rec_zero

variable {f} {m n : ℕ} {a : α}

theorem LeftInverse.iterate {g : α → α} (hg : LeftInverse g f) (n : ℕ) :
    LeftInverse g^[n] f^[n] :=
  Nat.recOn n (fun _ ↦ rfl) fun n ihn ↦ by
    rw [iterate_succ', iterate_succ]
    -- ⊢ LeftInverse (g ∘ g^[n]) (f^[n] ∘ f)
    exact ihn.comp hg
    -- 🎉 no goals
#align function.left_inverse.iterate Function.LeftInverse.iterate

theorem RightInverse.iterate {g : α → α} (hg : RightInverse g f) (n : ℕ) :
    RightInverse g^[n] f^[n] :=
  LeftInverse.iterate hg n
#align function.right_inverse.iterate Function.RightInverse.iterate

theorem iterate_comm (f : α → α) (m n : ℕ) : f^[n]^[m] = f^[m]^[n] :=
  (iterate_mul _ _ _).symm.trans (Eq.trans (by rw [Nat.mul_comm]) (iterate_mul _ _ _))
                                               -- 🎉 no goals
#align function.iterate_comm Function.iterate_comm

theorem iterate_commute (m n : ℕ) : Commute (fun f : α → α ↦ f^[m]) fun f ↦ f^[n] :=
  fun f ↦ iterate_comm f m n
#align function.iterate_commute Function.iterate_commute

lemma iterate_add_eq_iterate (hf : Injective f) : f^[m + n] a = f^[n] a ↔ f^[m] a = a :=
  Iff.trans (by rw [←iterate_add_apply, Nat.add_comm]) (hf.iterate n).eq_iff
                -- 🎉 no goals
#align function.iterate_add_eq_iterate Function.iterate_add_eq_iterate

alias ⟨iterate_cancel_of_add, _⟩ := iterate_add_eq_iterate
#align function.iterate_cancel_of_add Function.iterate_cancel_of_add

lemma iterate_cancel (hf : Injective f) (ha : f^[m] a = f^[n] a) : f^[m - n] a = a := by
  obtain h | h := le_total m n
  -- ⊢ f^[m - n] a = a
  { simp [Nat.sub_eq_zero_of_le h] }
  -- ⊢ f^[m - n] a = a
  { exact iterate_cancel_of_add hf (by rwa [Nat.sub_add_cancel h]) }
  -- 🎉 no goals
#align function.iterate_cancel Function.iterate_cancel

end Function

namespace List

open Function

theorem foldl_const (f : α → α) (a : α) (l : List β) :
    l.foldl (fun b _ ↦ f b) a = f^[l.length] a := by
  induction' l with b l H generalizing a
  -- ⊢ foldl (fun b x => f b) a [] = f^[length []] a
  · rfl
    -- 🎉 no goals
  · rw [length_cons, foldl, iterate_succ_apply, H]
    -- 🎉 no goals
#align list.foldl_const List.foldl_const

theorem foldr_const (f : β → β) (b : β) : ∀ l : List α, l.foldr (fun _ ↦ f) b = f^[l.length] b
  | [] => rfl
  | a :: l => by rw [length_cons, foldr, foldr_const f b l, iterate_succ_apply']
                 -- 🎉 no goals
#align list.foldr_const List.foldr_const

end List
