/-
Copyright (c) 2025 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Jujian Zhang
-/
import Mathlib

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
  isCentral := Algebra.IsCentral.of_algEquiv K A A' e
  isSimple := by sorry
  fin_dim := by sorry
  }

def mul (A B : CSA K) : CSA K := {
  __ := AlgebraCat.of K (A ⊗[K] B)
  isCentral := sorry
  isSimple := sorry
}

end CentralSimple

instance : One (BrauerGroup K) := ⟨Quotient.mk (Brauer.CSA_Setoid K) (CentralSimple.one K)⟩
