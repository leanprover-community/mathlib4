import Mathlib.Data.MvPolynomial.Basic
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

universe u v w

open TensorProduct

section

variable (σ : Type v)
variable (R : Type u) [CommRing R]
variable (A : Type w) [CommRing A] [Algebra R A]

private noncomputable def MvPolynomial.baseChangeAux :
    A ⊗[R] (MvPolynomial σ R) →ₐ[A] MvPolynomial σ A :=
  Algebra.TensorProduct.lift
    (Algebra.ofId A (MvPolynomial σ A))
    (mapAlgHom <| Algebra.ofId R A) <| by
  intro a P
  exact Algebra.commutes a (eval₂ (RingHom.comp C (algebraMap R A)) X P)

private noncomputable def MvPolynomial.baseChangeAuxInv :
    MvPolynomial σ A →ₐ[A] A ⊗[R] (MvPolynomial σ R) :=
  MvPolynomial.aeval (fun s ↦ 1 ⊗ₜ X s)

noncomputable def MvPolynomial.baseChange :
    A ⊗[R] MvPolynomial σ R ≃ₐ[A] MvPolynomial σ A := AlgEquiv.ofAlgHom 
  (baseChangeAux σ R A)
  (baseChangeAuxInv σ R A)
  (by ext s; simp [baseChangeAux, baseChangeAuxInv])
  (by ext s; simp [baseChangeAux, baseChangeAuxInv])

end

section

variable {R : Type u} [CommRing R]
variable {A : Type v} [CommRing A] [Algebra R A]
variable (B : Type w) [CommRing B] [Algebra R B]

private noncomputable abbrev FiniteType.baseChangeAux {n : ℕ}
    (f : MvPolynomial (Fin n) R →ₐ[R] A) :
    B ⊗[R] MvPolynomial (Fin n) R →ₐ[B] B ⊗[R] A :=
  Algebra.TensorProduct.map (AlgHom.id B B) f

private theorem FiniteType.baseChangeAux_surj {n : ℕ}
    {f : MvPolynomial (Fin n) R →ₐ[R] A} (hf : Function.Surjective f) :
    Function.Surjective (FiniteType.baseChangeAux B f) := by
  let h : B ⊗[R] MvPolynomial (Fin n) R →ₗ[R] B ⊗[R] A :=
    TensorProduct.map (AlgHom.id R B) f
  show Function.Surjective h
  apply TensorProduct.map_surjective
  exact Function.RightInverse.surjective (congrFun rfl)
  exact hf

theorem FiniteType.baseChange (hfa : Algebra.FiniteType R A) :
    Algebra.FiniteType B (B ⊗[R] A) := by
  rw [Algebra.FiniteType.iff_quotient_mvPolynomial''] at *
  obtain ⟨n, f, hf⟩ := hfa
  use n
  let g : B ⊗[R] MvPolynomial (Fin n) R →ₐ[B] B ⊗[R] A := baseChangeAux B f
  have : Function.Surjective g := baseChangeAux_surj B hf
  use AlgHom.comp g (MvPolynomial.baseChange (Fin n) R B).symm
  simp_all only [AlgHom.coe_comp, AlgHom.coe_coe, EquivLike.surjective_comp, g]

theorem FinitePresentation.baseChange (hfa : Algebra.FinitePresentation R A) :
    Algebra.FinitePresentation B (B ⊗[R] A) := by
  obtain ⟨n, f, hsurj, hfg⟩ := hfa
  let g : B ⊗[R] MvPolynomial (Fin n) R →ₐ[B] B ⊗[R] A :=
    FiniteType.baseChangeAux B f
  have hgsurj : Function.Surjective g := FiniteType.baseChangeAux_surj B hsurj
  have hker_eq : RingHom.ker (Algebra.TensorProduct.map (AlgHom.id B B) f)
      = Ideal.map Algebra.TensorProduct.includeRight (RingHom.ker f) :=
    Algebra.TensorProduct.lTensor_ker f hsurj
  have hfgg : Ideal.FG (RingHom.ker g) := by
    rw [hker_eq]
    exact Ideal.FG.map hfg _
  let g' : MvPolynomial (Fin n) B →ₐ[B] B ⊗[R] A :=
    AlgHom.comp g (MvPolynomial.baseChange (Fin n) R B).symm
  refine ⟨n, g', ?_, Ideal.fg_ker_comp _ _ ?_ hfgg ?_⟩
  · simp_all only [AlgHom.coe_comp, AlgHom.coe_coe, EquivLike.surjective_comp, g, g']
  · show Ideal.FG (RingHom.ker (AlgEquiv.symm (MvPolynomial.baseChange (Fin n) R B)))
    simp only [RingHom.ker_equiv]
    exact Submodule.fg_bot
  · simp only [AlgEquiv.toAlgHom_toRingHom, RingHom.coe_coe]
    exact EquivLike.surjective _

end
