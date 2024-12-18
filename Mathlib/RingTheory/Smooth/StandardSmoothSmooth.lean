/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.Kaehler
import Mathlib.Algebra.Module.LocalizedModule.Basic

/-!
# Smooth and locally standard smooth
-/

noncomputable section

universe u

section

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]
variable [Module.Finite R M]
variable (s : Set M) (hs : Submodule.span R s = ⊤)

lemma exists_basis_of_projective_of_span (p : Ideal R) [p.IsPrime] :
    ∃ (t : Set M) (f : R) (hp : f ∉ p)
      (b : Basis t (Localization.Away f) (LocalizedModule (Submonoid.powers f) M)),
      t ⊆ s ∧ (∀ m, b m = LocalizedModule.mk m.val 1) :=
  sorry

end

open TensorProduct

namespace Algebra

open MvPolynomial

section

namespace Generators

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T]
  (P : Generators R S) (Q : Generators S T)

def _root_.Algebra.Extension.Cotangent.lift (P : Extension R S) {M : Type*} [AddCommGroup M]
    [Module S M] [Module R M] [IsScalarTower R S M] [Module P.Ring M]
    [IsScalarTower P.Ring S M]
    (f : P.ker →ₗ[P.Ring] M) (hf : ∀ x : P.ker, x.val ∈ P.ker ^ 2 → f x = 0) :
    P.Cotangent →ₗ[S] M :=
  let g := Submodule.liftQ (P.ker • ⊤ : Submodule P.Ring P.ker) f <| by
    intro x hx
    have : x.val ∈ P.ker ^ 2 := sorry
    exact hf x this
  { __ := g.toAddMonoidHom,
    map_smul' := by
      intro m x
      dsimp
      show g (P.σ m • x.val) = m • g x
      rw [map_smul]
      show P.σ m • g x = m • g x
      conv_rhs => rw [← P.algebraMap_σ m, ← mul_one (algebraMap P.Ring S _)]
      rw [← Algebra.smul_def, IsScalarTower.smul_assoc]
      simp
      }

open Extension

/-- Given generators `R[X] → S` and `S[Y] → T`, this is the algebra map
`R[X,Y] → T ⊗[R] R[X]`. -/
def compRingToTensorRing : (Q.comp P).Ring →ₐ[R] T ⊗[R] P.Ring :=
  (aevalTower (IsScalarTower.toAlgHom R T _) (fun i ↦ 1 ⊗ₜ X i)).comp
    (aeval (Sum.elim (C ∘ Q.val) X))

@[simp]
lemma compRingToTensorRing_X_inr (i : P.vars) :
    compRingToTensorRing P Q (X (Sum.inr i)) = 1 ⊗ₜ X i := by
  simp [compRingToTensorRing]

@[simp]
lemma compRingToTensorRing_X_inl (i : Q.vars) :
    compRingToTensorRing P Q (X (Sum.inl i)) = Q.val i ⊗ₜ 1 := by
  simp [compRingToTensorRing]

def tensorRingEval : T ⊗[R] P.Ring →ₐ[R] T :=
  Algebra.TensorProduct.lift (AlgHom.id R T)
    ((IsScalarTower.toAlgHom R S T).comp (aeval P.val))
    (fun _ _ ↦ Commute.all _ _)

@[simp]
lemma tensorRingEval_tmul (t : T) (x : P.Ring) :
    tensorRingEval P (t ⊗ₜ x) = t * algebraMap S T (aeval P.val x) :=
  rfl

lemma tensorRingEval_comp_compRingToTensorRing :
    (tensorRingEval P).comp (compRingToTensorRing P Q) = aeval (Q.comp P).val := by
  ext (i|j)
  · simp
  · simp

lemma aux1_mem_ker (x : (Q.comp P).Ring) (hx : x ∈ (Q.comp P).ker) :
    compRingToTensorRing P Q x ∈ Set.range ((P.ker.subtype.restrictScalars R).lTensor T) := by
  have : (tensorRingEval P) (compRingToTensorRing P Q x) = 0 := by
    rw [← AlgHom.comp_apply, tensorRingEval_comp_compRingToTensorRing]
    exact hx


def compKerToTensorKer : (Q.comp P).ker →ₗ[R] T ⊗[R] P.ker := sorry

def kerToTensorCotangent : (Q.comp P).ker →ₗ[R] T ⊗[S] P.toExtension.Cotangent := sorry

noncomputable
def aux :
    (Q.comp P).ker →ₗ[(Q.comp P).Ring]
      T ⊗[R] P.toExtension.Cotangent × Q.toExtension.Cotangent where
  toFun := fun ⟨(x : MvPolynomial _ R), hx⟩ ↦
    ⟨1 ⊗ₜ Cotangent.mk ⟨aeval (Sum.elim (C ∘ Q.val) X) x, sorry⟩,
      Cotangent.mk ⟨aeval (Sum.elim X (C ∘ P.val)) x, sorry⟩⟩
  map_add' := sorry
  map_smul' := sorry

noncomputable
def compCotangent : (Q.comp P).toExtension.Cotangent →ₗ[T]
    T ⊗[S] P.toExtension.Cotangent × Q.toExtension.Cotangent := by
  fapply Extension.Cotangent.lift
  · sorry
  sorry

def compCotangentEquiv :
    (Q.comp P).toExtension.Cotangent ≃ₗ[T]
      T ⊗[R] P.toExtension.Cotangent × Q.toExtension.Cotangent :=
  sorry

end Generators

end

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Smooth R S]

end Algebra
