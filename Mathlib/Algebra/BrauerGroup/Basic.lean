/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib.RingTheory.SimpleRing.TensorProduct
import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Central.TensorProduct
import Mathlib.RingTheory.SimpleRing.Congr

/-!
# Basic facts/instances about BrauerGroup and Central Simple Algebras over field K



-/
variable (K : Type*) [Field K]

suppress_compilation

open scoped TensorProduct

lemma IsBrauerEquivalent.ofAlgEquiv {A B : CSA K} (e : A ≃ₐ[K] B): IsBrauerEquivalent A B :=
  ⟨1, 1, one_ne_zero, one_ne_zero, ⟨e.mapMatrix⟩⟩

namespace CentralSimple

abbrev one : CSA K := ⟨AlgebraCat.of K K⟩

abbrev ofAlgEquiv {A : CSA K} (A' : Type*) [Ring A'] [Algebra K A'] (e : A ≃ₐ[K] A') : CSA K := {
  __ := AlgebraCat.of K A',
  isCentral := .of_algEquiv K A A' e
  isSimple := .of_ringEquiv e.toRingEquiv inferInstance
  fin_dim := e.toLinearEquiv.finiteDimensional
  }

def mul (A B : CSA K) : CSA K := ⟨AlgebraCat.of K (A ⊗[K] B)⟩

end CentralSimple

instance : One (BrauerGroup K) := ⟨Quotient.mk (Brauer.CSA_Setoid K) (CentralSimple.one K)⟩
