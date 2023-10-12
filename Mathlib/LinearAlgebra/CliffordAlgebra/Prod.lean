/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.TensorProduct.Graded
import Mathlib.LinearAlgebra.QuadraticForm.Graded

/-!
# Clifford algebras of a direct sum of two vector spaces

We show that the clifford algebra of a direct sum is the super tensor product of the clifford
algebras.

-/

variable {R M₁ M₂  : Type*}
variable [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [Module R M] [Module R M₂]

variable (Q₁ : QuadraticForm R M₁) (Q₂ : QuadraticForm R M₂)

namespace CliffordAlgebra

def ofProd : CliffordAlgebra (Q₁.prod Q₂) →ₐ[R] (evenOdd Q₁ ⊗'[R] evenOdd Q₂) :=
  lift _ ⟨_, _⟩

def toProd : evenOdd Q₁ ⊗'[R] evenOdd Q₂ →ₐ[R] CliffordAlgebra (Q₁.prod Q₂) :=
  SuperTensorAlgebra.lift _ _ _ _ _

def prodEquiv : CliffordAlgebra (Q₁.prod Q₂) ≃ₐ[R] (evenOdd Q₁ ⊗'[R] evenOdd Q₂) :=
  AlgEquiv.ofAlgHom
    (ofProd Q₁ Q₂)
    (toProd Q₁ Q₂)
    _
    _

end CliffordAlgebra
