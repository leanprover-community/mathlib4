/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!

# Stability of finiteness conditions in commutative algebra

In this file we show that `Algebra.FiniteType` and `Algebra.FinitePresentation` are
stable under base change.

-/

open scoped TensorProduct

universe w₁ w₂ w₃

variable {R : Type w₁} [CommRing R]
variable {A : Type w₂} [CommRing A] [Algebra R A]
variable (B : Type w₃) [CommRing B] [Algebra R B]

namespace Algebra

namespace FiniteType

theorem baseChangeAux_surj {σ : Type*} {f : MvPolynomial σ R →ₐ[R] A} (hf : Function.Surjective f) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id B B) f) := by
  change Function.Surjective (TensorProduct.map (AlgHom.id R B) f)
  apply TensorProduct.map_surjective
  · exact Function.RightInverse.surjective (congrFun rfl)
  · exact hf

instance baseChange [hfa : FiniteType R A] : Algebra.FiniteType B (B ⊗[R] A) := by
  rw [iff_quotient_mvPolynomial''] at *
  obtain ⟨n, f, hf⟩ := hfa
  let g : B ⊗[R] MvPolynomial (Fin n) R →ₐ[B] B ⊗[R] A :=
    Algebra.TensorProduct.map (AlgHom.id B B) f
  have : Function.Surjective g := baseChangeAux_surj B hf
  use n, AlgHom.comp g (MvPolynomial.algebraTensorAlgEquiv R B).symm.toAlgHom
  simpa

end FiniteType

namespace FinitePresentation

instance baseChange [FinitePresentation R A] : FinitePresentation B (B ⊗[R] A) := by
  obtain ⟨n, f, hsurj, hfg⟩ := ‹FinitePresentation R A›
  let g : B ⊗[R] MvPolynomial (Fin n) R →ₐ[B] B ⊗[R] A :=
    Algebra.TensorProduct.map (AlgHom.id B B) f
  have hgsurj : Function.Surjective g := Algebra.FiniteType.baseChangeAux_surj B hsurj
  have hker_eq : RingHom.ker g = Ideal.map Algebra.TensorProduct.includeRight (RingHom.ker f) :=
    Algebra.TensorProduct.lTensor_ker f hsurj
  have hfgg : Ideal.FG (RingHom.ker g) := by
    rw [hker_eq]
    exact Ideal.FG.map hfg _
  let g' : MvPolynomial (Fin n) B →ₐ[B] B ⊗[R] A :=
    AlgHom.comp g (MvPolynomial.algebraTensorAlgEquiv R B).symm.toAlgHom
  refine ⟨n, g', ?_, Ideal.fg_ker_comp _ _ ?_ hfgg ?_⟩
  · simp_all [g, g']
  · change Ideal.FG (RingHom.ker (AlgEquiv.symm (MvPolynomial.algebraTensorAlgEquiv R B)))
    simp only [RingHom.ker_equiv]
    exact Submodule.fg_bot
  · simpa using EquivLike.surjective _

end FinitePresentation

end Algebra
