/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov

! This file was ported from Lean 3 source module logic.function.iterate
! leanprover-community/mathlib commit c4658a649d216f57e99621708b09dcb3dcccbd23
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Logic.Function.Conjugate

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
  if `f` fixes a point (resp., semiconjugates unary/binary operarations), then so does `f^[n]`.

-/


universe u v

variable {α : Type u} {β : Type v}

namespace Function

variable (f : α → α)

@[simp]
theorem iterate_zero : f^[0] = id :=
  rfl

theorem iterate_zero_apply (x : α) : (f^[0]) x = x :=
  rfl

@[simp]
theorem iterate_succ (n : ℕ) : f^[n.succ] = f^[n] ∘ f :=
  rfl

theorem iterate_succ_apply (n : ℕ) (x : α) : (f^[n.succ]) x = (f^[n]) (f x) :=
  rfl

@[simp]
theorem iterate_id (n : ℕ) : (id : α → α)^[n] = id :=
  Nat.recOn n rfl fun n ihn ↦ by rw [iterate_succ, ihn, comp.left_id]

theorem iterate_add (m : ℕ) : ∀ n : ℕ, f^[m + n] = f^[m] ∘ f^[n]
  | 0 => rfl
  | Nat.succ n => by rw [Nat.add_succ, iterate_succ, iterate_succ, iterate_add m n]; rfl

theorem iterate_add_apply (m n : ℕ) (x : α) : (f^[m + n]) x = (f^[m]) ((f^[n]) x) := by
  rw [iterate_add f m n]
  rfl

@[simp]
theorem iterate_one : f^[1] = f :=
  funext fun _ ↦ rfl

theorem iterate_mul (m : ℕ) : ∀ n, f^[m * n] = f^[m]^[n]
  | 0 => by simp only [Nat.mul_zero, iterate_zero]
  | n + 1 => by simp only [Nat.mul_succ, Nat.mul_one, iterate_one, iterate_add, iterate_mul m n]

variable {f}

theorem iterate_fixed {x} (h : f x = x) (n : ℕ) : (f^[n]) x = x :=
  Nat.recOn n rfl fun n ihn ↦ by rw [iterate_succ_apply, h, ihn]

theorem Injective.iterate (Hinj : Injective f) (n : ℕ) : Injective (f^[n]) :=
  Nat.recOn n injective_id fun _ ihn ↦ ihn.comp Hinj

theorem Surjective.iterate (Hsurj : Surjective f) (n : ℕ) : Surjective (f^[n]) :=
  Nat.recOn n surjective_id fun _ ihn ↦ ihn.comp Hsurj

theorem Bijective.iterate (Hbij : Bijective f) (n : ℕ) : Bijective (f^[n]) :=
  ⟨Hbij.1.iterate n, Hbij.2.iterate n⟩

namespace Semiconj

theorem iterate_right {f : α → β} {ga : α → α} {gb : β → β} (h : Semiconj f ga gb) (n : ℕ) :
    Semiconj f (ga^[n]) (gb^[n]) :=
  Nat.recOn n id_right fun _ ihn ↦ ihn.comp_right h

theorem iterate_left {g : ℕ → α → α} (H : ∀ n, Semiconj f (g n) (g <| n + 1)) (n k : ℕ) :
    Semiconj (f^[n]) (g k) (g <| n + k) := by
  induction' n with n ihn generalizing k
  · rw [Nat.zero_add]
    exact id_left

  · rw [Nat.succ_eq_add_one, Nat.add_right_comm, Nat.add_assoc]
    exact (H k).comp_left (ihn (k + 1))


end Semiconj

namespace Commute

variable {g : α → α}

theorem iterate_right (h : Commute f g) (n : ℕ) : Commute f (g^[n]) :=
  Semiconj.iterate_right h n

theorem iterate_left (h : Commute f g) (n : ℕ) : Commute (f^[n]) g :=
  (h.symm.iterate_right n).symm

theorem iterate_iterate (h : Commute f g) (m n : ℕ) : Commute (f^[m]) (g^[n]) :=
  (h.iterate_left m).iterate_right n

theorem iterate_eq_of_map_eq (h : Commute f g) (n : ℕ) {x} (hx : f x = g x) :
    (f^[n]) x = (g^[n]) x :=
  Nat.recOn n rfl fun n ihn ↦ by
    simp only [iterate_succ_apply, hx, (h.iterate_left n).eq, ihn, ((refl g).iterate_right n).eq]

theorem comp_iterate (h : Commute f g) (n : ℕ) : (f ∘ g)^[n] = f^[n] ∘ g^[n] := by
  induction' n with n ihn
  · rfl

  funext x
  simp only [ihn, (h.iterate_right n).eq, iterate_succ, comp_apply]

variable (f)

theorem iterate_self (n : ℕ) : Commute (f^[n]) f :=
  (refl f).iterate_left n

theorem self_iterate (n : ℕ) : Commute f (f^[n]) :=
  (refl f).iterate_right n

theorem iterate_iterate_self (m n : ℕ) : Commute (f^[m]) (f^[n]) :=
  (refl f).iterate_iterate m n

end Commute

theorem Semiconj₂.iterate {f : α → α} {op : α → α → α} (hf : Semiconj₂ f op op) (n : ℕ) :
    Semiconj₂ (f^[n]) op op :=
  Nat.recOn n (Semiconj₂.id_left op) fun _ ihn ↦ ihn.comp hf

variable (f)

theorem iterate_succ' (n : ℕ) : f^[n.succ] = f ∘ f^[n] := by
  rw [iterate_succ, (Commute.self_iterate f n).comp_eq]

theorem iterate_succ_apply' (n : ℕ) (x : α) : (f^[n.succ]) x = f ((f^[n]) x) := by
  rw [iterate_succ']
  rfl

theorem iterate_pred_comp_of_pos {n : ℕ} (hn : 0 < n) : f^[n.pred] ∘ f = f^[n] := by
  rw [← iterate_succ, Nat.succ_pred_eq_of_pos hn]

theorem comp_iterate_pred_of_pos {n : ℕ} (hn : 0 < n) : f ∘ f^[n.pred] = f^[n] := by
  rw [← iterate_succ', Nat.succ_pred_eq_of_pos hn]

/-- A recursor for the iterate of a function. -/
noncomputable
def Iterate.rec (p : α → Sort _) {f : α → α} (h : ∀ a, p a → p (f a)) {a : α} (ha : p a) (n : ℕ) :
    p ((f^[n]) a) :=
  Nat.rec ha
    (fun m ↦ by
      rw [iterate_succ']
      exact h _)
    n

theorem Iterate.rec_zero (p : α → Sort _) {f : α → α} (h : ∀ a, p a → p (f a)) {a : α} (ha : p a) :
    Iterate.rec p h ha 0 = ha :=
  rfl

variable {f}

theorem LeftInverse.iterate {g : α → α} (hg : LeftInverse g f) (n : ℕ) :
    LeftInverse (g^[n]) (f^[n]) :=
  Nat.recOn n (fun _ ↦ rfl) fun n ihn ↦ by
    rw [iterate_succ', iterate_succ]
    exact ihn.comp hg

theorem RightInverse.iterate {g : α → α} (hg : RightInverse g f) (n : ℕ) :
    RightInverse (g^[n]) (f^[n]) :=
  LeftInverse.iterate hg n

theorem iterate_comm (f : α → α) (m n : ℕ) : f^[n]^[m] = f^[m]^[n] :=
  (iterate_mul _ _ _).symm.trans (Eq.trans (by rw [Nat.mul_comm]) (iterate_mul _ _ _))

theorem iterate_commute (m n : ℕ) : Commute (fun f : α → α ↦ f^[m]) fun f ↦ f^[n] :=
  fun f ↦ iterate_comm f m n

end Function

namespace List

open Function

theorem foldl_const (f : α → α) (a : α) (l : List β) :
    l.foldl (fun b _ ↦ f b) a = (f^[l.length]) a := by
  induction' l with b l H generalizing a
  · rfl

  · rw [length_cons, foldl, iterate_succ_apply, H]


theorem foldr_const (f : β → β) (b : β) : ∀ l : List α, l.foldr (fun _ ↦ f) b = (f^[l.length]) b
  | [] => rfl
  | a :: l => by rw [length_cons, foldr, foldr_const f b l, iterate_succ_apply']

end List
