/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Mathlib.LinearAlgebra.Basis
import Mathlib.LinearAlgebra.Multilinear.Basic

#align_import linear_algebra.multilinear.basis from "leanprover-community/mathlib"@"ce11c3c2a285bbe6937e26d9792fda4e51f3fe1a"

/-!
# Multilinear maps in relation to bases.

This file proves lemmas about the action of multilinear maps on basis vectors.

## TODO

 * Refactor the proofs in terms of bases of tensor products, once there is an equivalent of
   `Basis.tensorProduct` for `pi_tensor_product`.

-/


open MultilinearMap

variable {R : Type*} {ι : Type*} {n : ℕ} {M : Fin n → Type*} {M₂ : Type*} {M₃ : Type*}

variable [CommSemiring R] [AddCommMonoid M₂] [AddCommMonoid M₃] [∀ i, AddCommMonoid (M i)]

variable [∀ i, Module R (M i)] [Module R M₂] [Module R M₃]

/-- Two multilinear maps indexed by `Fin n` are equal if they are equal when all arguments are
basis vectors. -/
theorem Basis.ext_multilinear_fin {f g : MultilinearMap R M M₂} {ι₁ : Fin n → Type*}
    (e : ∀ i, Basis (ι₁ i) R (M i))
    (h : ∀ v : ∀ i, ι₁ i, (f fun i => e i (v i)) = g fun i => e i (v i)) : f = g := by
  induction' n with m hm
  -- ⊢ f = g
  · ext x
    -- ⊢ ↑f x = ↑g x
    convert h finZeroElim
    -- 🎉 no goals
  · apply Function.LeftInverse.injective uncurry_curryLeft
    -- ⊢ (fun x => curryLeft x) f = (fun x => curryLeft x) g
    refine' Basis.ext (e 0) _
    -- ⊢ ∀ (i : ι₁ 0), ↑((fun x => curryLeft x) f) (↑(e 0) i) = ↑((fun x => curryLeft …
    intro i
    -- ⊢ ↑((fun x => curryLeft x) f) (↑(e 0) i) = ↑((fun x => curryLeft x) g) (↑(e 0) …
    apply hm (Fin.tail e)
    -- ⊢ ∀ (v : (i : Fin m) → ι₁ (Fin.succ i)), (↑(↑((fun x => curryLeft x) f) (↑(e 0 …
    intro j
    -- ⊢ (↑(↑((fun x => curryLeft x) f) (↑(e 0) i)) fun i => ↑(Fin.tail e i) (j i)) = …
    convert h (Fin.cons i j)
    -- ⊢ (↑(↑((fun x => curryLeft x) f) (↑(e 0) i)) fun i => ↑(Fin.tail e i) (j i)) = …
    iterate 2
      rw [curryLeft_apply]
      congr 1 with x
      refine' Fin.cases rfl (fun x => _) x
      dsimp [Fin.tail]
      rw [Fin.cons_succ, Fin.cons_succ]
#align basis.ext_multilinear_fin Basis.ext_multilinear_fin

/-- Two multilinear maps indexed by a `Fintype` are equal if they are equal when all arguments
are basis vectors. Unlike `Basis.ext_multilinear_fin`, this only uses a single basis; a
dependently-typed version would still be true, but the proof would need a dependently-typed
version of `dom_dom_congr`. -/
theorem Basis.ext_multilinear [Finite ι] {f g : MultilinearMap R (fun _ : ι => M₂) M₃} {ι₁ : Type*}
    (e : Basis ι₁ R M₂) (h : ∀ v : ι → ι₁, (f fun i => e (v i)) = g fun i => e (v i)) : f = g := by
  cases nonempty_fintype ι
  -- ⊢ f = g
  exact
    (domDomCongr_eq_iff (Fintype.equivFin ι) f g).mp
      (Basis.ext_multilinear_fin (fun _ => e) fun i => h (i ∘ _))
#align basis.ext_multilinear Basis.ext_multilinear
