/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# Products of subalgebras

In this file we define the product of subalgebras as a subalgebra of the product algebra.

## Main definitions

 * `Subalgebra.pi`: the product of subalgebras.
-/

open Algebra

namespace Subalgebra
variable {ι R : Type*} {S : ι → Type*} [CommSemiring R] [∀ i, Semiring (S i)] [∀ i, Algebra R (S i)]
  {t : Set ι} {s s₁ s₂ : ∀ i, Subalgebra R (S i)} {x : ∀ i, S i}

/-- The product of subalgebras as a subalgebra. -/
@[simps coe toSubsemiring]
def pi (t : Set ι) (s : ∀ i, Subalgebra R (S i)) : Subalgebra R (Π i, S i) where
  __ := Submodule.pi t fun i ↦ (s i).toSubmodule
  mul_mem' hx hy i hi := (s i).mul_mem (hx i hi) (hy i hi)
  algebraMap_mem' _ i _ := (s i).algebraMap_mem _

@[simp] lemma mem_pi : x ∈ pi t s ↔ ∀ i ∈ t, x i ∈ s i := .rfl

open Subalgebra in
@[simp] lemma pi_toSubmodule : toSubmodule (pi t s) = .pi t fun i ↦ (s i).toSubmodule := rfl

@[simp]
lemma pi_top (t : Set ι) : pi t (fun i ↦ (⊤ : Subalgebra R (S i))) = ⊤ :=
  SetLike.coe_injective <| Set.pi_univ _

@[gcongr] lemma pi_mono (h : ∀ i ∈ t, s₁ i ≤ s₂ i) : pi t s₁ ≤ pi t s₂ := Set.pi_mono h

end Subalgebra
