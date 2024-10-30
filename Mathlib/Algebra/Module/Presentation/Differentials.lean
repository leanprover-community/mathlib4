/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import Mathlib.Algebra.Module.Presentation.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Presentation

/-!
# Presentation of the module of differentials

Given a presentation of a `R`-algebra `S`, we obtain a presentation
of the `S`-module `Ω[S⁄R]`.

-/

universe w' t w u v

-- to be moved
section

variable (R : Type*) {A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  (surj : Function.Surjective (algebraMap A B))
  (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [Module B M] [IsScalarTower A B M]

/-- Assume that a morphism of `R`-algebras from `A` to `B` is surjective, then
`R`-derivations of a `B`-module `M` identify to `R`-derivations of `M` as a `A`-module
which vanishes on the kernel ideal of `algebraMap A B`. -/
@[simps! apply_coe]
noncomputable def Derivation.equivOfSurjective :
    Derivation R B M ≃
      { d : Derivation R A M // ∀ (x : RingHom.ker (algebraMap A B)), d x = 0 } :=
  Equiv.ofBijective (fun d ↦ ⟨d.compAlgebraMap A, fun ⟨x, hx⟩ ↦ by
      simp only [RingHom.mem_ker] at hx
      simp only [compAlgebraMap_apply, hx, map_zero]⟩) (by
    constructor
    · intro d₁ d₂ h
      simp only [Subtype.mk.injEq] at h
      ext b
      obtain ⟨a, rfl⟩ := surj b
      exact DFunLike.congr_fun h a
    · intro d
      obtain ⟨s, hs⟩ := surj.hasRightInverse
      let d' : B → M := fun b ↦ d.1 (s b)
      have h : ∀ (a : A), d' (algebraMap A B a) = d.1 a := fun a ↦ by
        dsimp [d']
        rw [← sub_eq_zero, ← map_sub]
        refine d.2 ⟨_, by simp only [RingHom.mem_ker, map_sub, hs _, sub_self]⟩
      exact
         ⟨{ toFun := d'
            map_add' := fun x y ↦ by
              obtain ⟨x, rfl⟩ := surj x
              obtain ⟨y, rfl⟩ := surj y
              rw [← map_add, h, h, h, map_add]
            map_one_eq_zero' := by
              dsimp
              rw [← RingHom.map_one, h, map_one_eq_zero]
            map_smul' := fun r x ↦ by
              obtain ⟨x, rfl⟩ := surj x
              dsimp
              rw [h, ← map_smul, ← h, Algebra.smul_def, Algebra.smul_def, map_mul,
                IsScalarTower.algebraMap_apply R A B]
            leibniz' := fun x y ↦ by
              obtain ⟨x, rfl⟩ := surj x
              obtain ⟨y, rfl⟩ := surj y
              dsimp
              rw [← map_mul, h, leibniz, h, h, algebra_compatible_smul B x,
                algebra_compatible_smul B y]}, by aesop⟩)

end

-- to be moved
section

variable {R : Type u} {S : Type v} [CommSemiring R] [CommSemiring S] [Algebra R S]
  (α : Type*) (M : Type*) [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  (v : α → M) (l : α →₀ R)

@[simp]
lemma Finsupp.linearCombination_mapRange_algebraMap :
    Finsupp.linearCombination S v
      (Finsupp.mapRange (algebraMap R S) (by simp) l) =
        Finsupp.linearCombination R v l := by
  apply Finsupp.induction_linear (p := fun (l : α →₀ R) ↦ Finsupp.linearCombination S v _ = _)
  · simp
  · intro f g hf hg
    rw [map_add, Finsupp.mapRange_add (by simp), map_add, hf, hg]
  · simp

end

namespace Algebra.Presentation

open KaehlerDifferential

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  (pres : Algebra.Presentation.{t, w} R S)

/-- The shape of the presentation by generators and relations of the `S`-module `Ω[S⁄R]`
that is obtained from a presentation of `S` as a `R`-algebra. -/
@[simps G R]
noncomputable def differentialsRelations : Module.Relations S where
  G := pres.vars
  R := pres.rels
  relation r :=
    Finsupp.mapRange (algebraMap pres.Ring S) (by simp)
      ((mvPolynomialBasis R pres.vars).repr (D _ _ (pres.relation r)))

lemma linearCombination_repr_differential
    (ω : Ω[MvPolynomial pres.vars R⁄R]) :
    Finsupp.linearCombination S (fun g ↦ (D R S) (pres.val g))
      (Finsupp.mapRange (algebraMap pres.Ring S) (by simp)
        ((mvPolynomialBasis R pres.vars).repr ω)) =
    KaehlerDifferential.map R R pres.Ring S ω := by
  obtain ⟨v, rfl⟩ := (mvPolynomialBasis R pres.vars).repr.symm.surjective ω
  rw [Basis.repr_symm_apply, Basis.repr_linearCombination,
    Finsupp.apply_linearCombination, Finsupp.linearCombination_mapRange_algebraMap]
  congr
  aesop

/-- The `S`-module `Ω[S⁄R]` contains an obvious solution to the system of linear
equations `pres.differentialsRelations.Solution` when `pres` is a presentation
of `S` as a `R`-algebra. -/
noncomputable def differentialsSolution :
    pres.differentialsRelations.Solution (Ω[S⁄R]) where
  var g := D _ _ (pres.val g)
  linearCombination_var_relation (r : pres.rels) := by
    simp only [differentialsRelations, linearCombination_repr_differential,
      map_D, Generators.algebraMap_apply, aeval_val_relation, map_zero]

/-- The `S`-module `Ω[S⁄R]` admits a presentation by generators and relations that
is determined by a presentation of `S` as a `R`-algebra. -/
def isPresentationCoreDifferentialsSolution :
    Module.Relations.Solution.IsPresentationCore.{w'}
      pres.differentialsSolution := sorry

lemma differentialsSolution_isPresentation :
    pres.differentialsSolution.IsPresentation :=
  pres.isPresentationCoreDifferentialsSolution.isPresentation

/-- The presentation of the `S`-module `Ω[S⁄R]` deduced from a presentation
of `S` as a `R`-algebra. -/
noncomputable def differentials : Module.Presentation S (Ω[S⁄R]) where
  toSolution := differentialsSolution pres
  toIsPresentation := pres.differentialsSolution_isPresentation

end Algebra.Presentation
