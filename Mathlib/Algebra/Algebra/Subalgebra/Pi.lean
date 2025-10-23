/-
Copyright (c) 2024 Yaël Dillies, Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Andrew Yang
-/
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
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
  {s : Set ι} {t t₁ t₂ : ∀ i, Subalgebra R (S i)} {x : ∀ i, S i}

/-- The product of subalgebras as a subalgebra. -/
@[simps coe toSubsemiring]
def pi (s : Set ι) (t : ∀ i, Subalgebra R (S i)) : Subalgebra R (Π i, S i) where
  __ := Submodule.pi s fun i ↦ (t i).toSubmodule
  mul_mem' hx hy i hi := (t i).mul_mem (hx i hi) (hy i hi)
  algebraMap_mem' _ i _ := (t i).algebraMap_mem _

@[simp] lemma mem_pi : x ∈ pi s t ↔ ∀ i ∈ s, x i ∈ t i := .rfl

open Subalgebra in
@[simp] lemma pi_toSubmodule : toSubmodule (pi s t) = .pi s fun i ↦ (t i).toSubmodule := rfl

@[simp]
lemma pi_top (s : Set ι) : pi s (fun i ↦ (⊤ : Subalgebra R (S i))) = ⊤ :=
  SetLike.coe_injective <| Set.pi_univ _

@[gcongr] lemma pi_mono (h : ∀ i ∈ s, t₁ i ≤ t₂ i) : pi s t₁ ≤ pi s t₂ := Set.pi_mono h

end Subalgebra
