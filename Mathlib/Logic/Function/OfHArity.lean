/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/

import Mathlib.Logic.Function.OfArity
import Mathlib.Data.Fin.VecNotation

/-! # Function types of a given heterogeneous arity

This provides `FunctionOfHArity`, such that `OfHArity ![α, β] τ = α → β → τ`.
Note that it is often preferable to use `((i : Fin n) → p i) → τ` in place of `OfArity p τ`.

## Main definitions

* `Function.OfHArity p τ`: `n`-ary function `p 0 → p 1 → ... → p (n - 1) → β`.
-/

universe u

namespace Function

open Matrix (vecCons vecHead vecTail vecEmpty)

/-- The type of `n`-ary functions `p 0 → p 1 → ... → p (n - 1) → τ`. -/
def OfHArity : {n : ℕ} → (Fin n → Type u) → Type u → Type u
  | 0    , _, τ => τ
  | n + 1, p, τ => vecHead p → @OfHArity n (vecTail p) τ

@[simp]
theorem ofHArity_zero (p : Fin 0 → Type u) (τ : Type u) : OfHArity p τ = τ := rfl

theorem ofHArity_nil (τ : Type u) : OfHArity ![] τ = τ := ofHArity_zero ![] τ

@[simp low] -- prefer `ofHArity_cons` when it (syntactically) applies
theorem ofHArity_succ {n} (p : Fin (n + 1) → Type u) (τ : Type u) :
    OfHArity p τ = (vecHead p → OfHArity (vecTail p) τ) := rfl

@[simp]
theorem ofHArity_cons {n} (α : Type u) (p : Fin n → Type u) (τ : Type u) :
    OfHArity (vecCons α p) τ = (α → OfHArity p τ) := ofHArity_succ _ τ

@[simps!]
def ofHArity_zero_equiv (p : Fin 0 → Type u) (τ : Type u) :
    OfHArity p τ ≃ τ := Equiv.refl _

@[simps!]
def ofHArity_nil_equiv (τ : Type u) : OfHArity ![] τ ≃ τ :=
  ofHArity_zero_equiv ![] τ

@[simps!]
def ofHArity_succ_equiv {n} (p : Fin (n + 1) → Type u) (τ : Type u) :
    OfHArity p τ ≃ (vecHead p → OfHArity (vecTail p) τ) := Equiv.refl _

@[simps!]
def ofHArity_cons_equiv {n} (α : Type u) (p : Fin n → Type u) (τ : Type u) :
    OfHArity (vecCons α p) τ ≃ (α → OfHArity p τ) := ofHArity_succ_equiv _ _

-- not a definitional equality, generally prefer `ofHArity_fin_const_equiv`
lemma ofHArity_fin_const {n} (α β : Type u) :
    OfHArity (fun (_ : Fin n) => α) β = OfArity α β n :=
  match n with
  | 0   => Eq.refl β
  | n+1 => congrArg (α → .) (@ofHArity_fin_const n α β)

def ofHArity_fin_const_equiv : {n : ℕ} → (α β : Type u) →
    OfHArity (fun (_ : Fin n) => α) β ≃ OfArity α β n
  | 0,   _, β => .refl β
  | n+1, α, β => .arrowCongr (.refl α) (@ofHArity_fin_const_equiv n α β)

namespace OfHArity

/-- Constant `n`-ary function with value `t`. -/
def const : {n : ℕ} → (p : Fin n → Type u) → {τ : Type u} → (t : τ) → OfHArity p τ
  | 0,     _, _, t => t
  | n + 1, p, τ, t => fun _ => @const n (vecTail p) τ t

@[simp]
theorem const_zero (p : Fin 0 → Type u) {τ : Type u} (t : τ) : const p t = t :=
  rfl

@[simp]
theorem const_succ {n} (p : Fin (n + 1) → Type u) {τ : Type u} (t : τ) :
    const p t = fun _ => const (vecTail p) t := rfl

theorem const_succ_apply {n} (p : Fin (n + 1) → Type u) {τ : Type u} (t : τ)
    (x : p 0) : const p t x = const (vecTail p) t := rfl

instance OfHArity.inhabited {n} {p : Fin n → Type u} {τ} [Inhabited τ] :
    Inhabited (OfHArity p τ) := ⟨const p default⟩

end OfHArity

end Function
