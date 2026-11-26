/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.SpectralSequence.PageInfinity
public import Mathlib.Order.Preorder.Finite

/-!
# Convergence of spectral sequences

-/

@[expose] public section

namespace CategoryTheory

open Category Limits Preadditive

variable {C : Type*} [Category* C] [Abelian C]
  (ι : Type*) {c : ℤ → ComplexShape ι} {r₀ : ℤ}

namespace SpectralSequence

variable {σ : Type*} (α : σ → Type*) [∀ n, LinearOrder (α n)]

structure ConvergenceStripes where
  pred (n : σ) (i : α n) : WithBot (α n)
  pred_lt n (i : α n) : pred n i < WithBot.some i := by aesop
  stripe : ι → σ
  position (n : σ) (i : α n) : ι
  stripe_position (n : σ) (i : α n) : stripe (position n i) = n := by grind
  discrete (n : σ) (i j : α n) (h₁ : pred n i < WithBot.some j) : i ≤ j
  finite_icc' (n : σ) (i j : α n) (hij : i ≤ j) : (Set.Icc i j).Finite

variable {α}

@[simps, implicit_reducible]
def cohomologicalStripes :
    ConvergenceStripes (ℤ × ℤ) (fun (_ : ℤ) ↦ ℤ) where
  stripe pq := pq.1 + pq.2
  position n i := ⟨n + 1 - i, i - 1⟩
  pred n i := WithBot.some (i - 1)
  discrete n (i j : ℤ) h := by
    simp at h
    lia
  finite_icc' _ i j hij := by
    obtain ⟨d, rfl⟩ := Int.le.dest hij
    refine Finite.of_surjective
      (fun (k : Fin (d + 1)) ↦ ⟨i + k, ⟨by lia, by have := k.is_lt; lia⟩⟩)
      (fun ⟨x, h₁, h₂⟩ ↦ ?_)
    obtain ⟨k, rfl⟩ := Int.le.dest h₁
    exact ⟨⟨k, by lia⟩, rfl⟩

@[simps, implicit_reducible]
def cohomomologicalStripesFin (l : ℕ) :
    ConvergenceStripes (ℤ × Fin l) (fun (_ : ℤ) ↦ Fin l) where
  stripe pq := pq.1 + pq.2.val
  pred _ j := match j with
    | ⟨0, _⟩   => ⊥
    | ⟨j + 1, _⟩ => WithBot.some ⟨j, by lia⟩
  pred_lt n := by rintro ⟨_ | _⟩ <;> simp
  position n i := ⟨n - i.val, i⟩
  discrete := by rintro n _ ⟨_, _⟩ _; aesop
  finite_icc' _ _ _ _ := .of_injective Subtype.val (fun _ _ _ ↦ by grind)

@[simps, implicit_reducible]
def cohomologicalStripesNat :
    ConvergenceStripes (ℕ × ℕ) (fun (n : ℕ) ↦ Fin (n + 1)) where
  stripe pq := pq.1 + pq.2
  pred n i := match i with
    | 0 => ⊥
    | ⟨j + 1, hj⟩ => WithBot.some ⟨j, by omega⟩
  pred_lt n i := by obtain ⟨_ | _, _⟩ := i <;> aesop
  position n i := ⟨n - i.val, i.val⟩
  discrete := by rintro n ⟨_ | _, _⟩ ⟨_, _⟩ _ <;> aesop
  finite_icc' n i j hij := Set.toFinite _

variable {ι}

namespace ConvergenceStripes

variable (s : ConvergenceStripes ι α)

attribute [simp] stripe_position

lemma stripe_eq (n : σ) (i : α n) (pq : ι) (hpq : s.position n i = pq) :
    s.stripe pq = n := by
  simp [← hpq]

include s in
lemma finite_icc (n : σ) (i j : α n) : (Set.Icc i j).Finite := by
  by_cases hij : i ≤ j
  · exact s.finite_icc' n i j hij
  · simp [Set.Icc_eq_empty hij]

end ConvergenceStripes

end SpectralSequence

end CategoryTheory
