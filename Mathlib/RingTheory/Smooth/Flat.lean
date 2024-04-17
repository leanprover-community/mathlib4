/-
Copyright (c) 2022 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Algebra.RestrictScalars
import Mathlib.Algebra.Lie.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Set.Pointwise.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

universe u v

namespace Algebra

variable (A : Type u) [CommRing A]
variable (B : Type u) [CommRing B] [Algebra A B] [FormallySmooth A B]
variable (n : ℕ)

local notation "R" => MvPolynomial (Fin n) A

variable (f : MvPolynomial (Fin n) A →ₐ[A] B) (hf : Function.Surjective f)

local notation "I" => RingHom.ker f

noncomputable def section_aux : (m : ℕ) → B →ₐ[A] R ⧸ (I^(m+1))
  | Nat.zero => by
      let f' := Ideal.quotientKerAlgEquivOfSurjective hf
      rw [pow_one]
      exact f'.symm.toAlgHom
  | Nat.succ k => by
      let T := R ⧸ (I^(k+2))
      let J : Ideal T := Ideal.map (Ideal.Quotient.mk (I^(k+2))) I
      have hn : IsNilpotent J:= sorry
      let p : B →ₐ[A] R ⧸ (I^(k+1)) := section_aux k
      let e : R ⧸ (I^(k+1)) →ₐ[A] T⧸J := sorry
      let q : B →ₐ[A] T⧸J := e.comp p
      exact FormallySmooth.lift J hn q
