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

namespace Derivation

variable {R : Type*} {A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {M : Type*} [AddCommGroup M] [Module R M] [Module A M]
  (d : Derivation R A M) (B : Type*) [CommRing B] [Algebra A B]
  [Module B M] [IsScalarTower A B M]

/-- Given `d : Derivation R A M`, when `B` is an `A`-algebra and `M` is a `B`-module,
this is the ideal of `A` consisting of the elements that are both in the
kernel `algebraMap A B` and the kernel of `d`. -/
def kerInterKer :
    Ideal A where
  carrier x := algebraMap A B x = 0 ∧ d x = 0
  add_mem' := by
    rintro x y ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    exact ⟨by simp [h₁, h₃], by simp [h₂, h₄]⟩
  zero_mem' := ⟨by simp, by simp⟩
  smul_mem' := by
    rintro a x ⟨h₁, h₂⟩
    constructor
    · simp [h₁]
    · rw [smul_eq_mul, leibniz, h₂, smul_zero, zero_add,
        algebra_compatible_smul B, h₁, zero_smul]

lemma kerInterKer_le_ringHom_ker :
    d.kerInterKer B ≤ RingHom.ker (algebraMap A B) :=
  fun _ ⟨h₁, _⟩ ↦ h₁

lemma ringHom_ker_eq_kerInterKer_iff :
    RingHom.ker (algebraMap A B) = d.kerInterKer B ↔
      RingHom.ker (algebraMap A B) ≤ d.kerInterKer B :=
  ⟨fun h ↦ by rw [h], fun h ↦ le_antisymm h (kerInterKer_le_ringHom_ker _ _)⟩

lemma ringHom_ker_eq_kerInterKer_of_span_eq_ker {G : Set A}
    (hG : Ideal.span G = RingHom.ker (algebraMap A B)) (h : ∀ (g : G), d g = 0) :
    RingHom.ker (algebraMap A B) = d.kerInterKer B := by
  rw [ringHom_ker_eq_kerInterKer_iff, ← hG, Ideal.span_le]
  exact fun g hg ↦ ⟨(Ideal.ext_iff.1 hG g).1 (Ideal.subset_span hg), h ⟨g, hg⟩⟩

end Derivation

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
      { d : Derivation R A M // RingHom.ker (algebraMap A B) = d.kerInterKer B } :=
  Equiv.ofBijective (fun d ↦ ⟨d.compAlgebraMap A, by
      refine le_antisymm (fun x hx ↦ ?_) (Derivation.kerInterKer_le_ringHom_ker _ _)
      simp only [RingHom.mem_ker] at hx
      exact ⟨hx, by rw [compAlgebraMap_apply, hx, map_zero]⟩⟩) (by
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
        exact ((Ideal.ext_iff.1 d.2 _).1 (by simp [hs _])).2
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
  apply Finsupp.induction_linear
    (p := fun (l : α →₀ R) ↦ Finsupp.linearCombination S v _ = _)
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

section

variable {N : Type w'} [AddCommGroup N]
  [Module pres.Ring N]

-- these lemmas needs some clarification
lemma linearCombination_aux₃
    (φ : Ω[MvPolynomial pres.vars R⁄R] →ₗ[MvPolynomial pres.vars R] N)
    (ω : Ω[MvPolynomial pres.vars R⁄R]) :
    (Finsupp.linearCombination pres.Ring fun g ↦ φ (D _ _ (MvPolynomial.X g)))
    ((mvPolynomialBasis R pres.vars).repr ω) = φ ω := by
  erw [← Finsupp.apply_linearCombination]
  congr 1
  obtain ⟨s, rfl⟩ := (mvPolynomialBasis R pres.vars).repr.symm.surjective ω
  simp
  congr 2
  ext g
  simp

variable [Module R N]
  [IsScalarTower R pres.Ring N]

lemma linearCombination_aux₂
    (d : Derivation R (MvPolynomial pres.vars R) N)
    (ω : Ω[MvPolynomial pres.vars R⁄R]) :
    (Finsupp.linearCombination pres.Ring fun g ↦ d (MvPolynomial.X g))
    ((mvPolynomialBasis R pres.vars).repr ω) =
    d.liftKaehlerDifferential ω := by
  rw [← linearCombination_aux₃]
  simp only [Derivation.liftKaehlerDifferential_comp_D]

variable [Module S N]
  [IsScalarTower pres.Ring S N]

lemma linearCombination_aux₁
    (d : Derivation R (MvPolynomial pres.vars R) N) (r : pres.Ring) :
    Finsupp.linearCombination S (fun g ↦ d (MvPolynomial.X g))
      (Finsupp.mapRange (algebraMap pres.Ring S) (by simp)
        ((mvPolynomialBasis R pres.vars).repr (D _ _ r))) =
      d r := by
  rw [Finsupp.linearCombination_mapRange_algebraMap,
    linearCombination_aux₂, Derivation.liftKaehlerDifferential_comp_D]

lemma linearCombination_aux₀ (s : pres.vars → N) (r : pres.Ring) :
    Finsupp.linearCombination S s
      (Finsupp.mapRange (algebraMap pres.Ring S) (by simp)
        ((mvPolynomialBasis R pres.vars).repr (D _ _ r))) =
      MvPolynomial.mkDerivation R s r := by
  simp only [← linearCombination_aux₁ pres (MvPolynomial.mkDerivation R s) r,
    Finsupp.linearCombination_mapRange_algebraMap, MvPolynomial.mkDerivation_X]

@[simp]
lemma linearCombination_differentialsRelations_relation
    (s : pres.vars → N) (r : pres.rels) :
    Finsupp.linearCombination S s (pres.differentialsRelations.relation r) =
      (MvPolynomial.mkDerivation R s) (pres.relation r) := by
  dsimp [differentialsRelations]
  rw [linearCombination_aux₀]

noncomputable def differentialsRelationsSolutionEquivSubtype :
    pres.differentialsRelations.Solution N ≃
      { d : Derivation R pres.Ring N //
        RingHom.ker (algebraMap pres.Ring S) = d.kerInterKer S } where
  toFun s := ⟨MvPolynomial.mkDerivation R s.var, by
    rw [Derivation.ringHom_ker_eq_kerInterKer_of_span_eq_ker (R := R) (M := N)
      (hG := pres.span_range_relation_eq_ker)]
    rintro ⟨_, ⟨r, rfl⟩⟩
    simpa using s.linearCombination_var_relation r⟩
  invFun := fun ⟨d, hd⟩ ↦
    { var := fun g ↦ d (MvPolynomial.X g)
      linearCombination_var_relation := fun r ↦ by
        have : d (pres.relation r) = 0 :=
          ((Ideal.ext_iff.1 hd _).1 ((Ideal.ext_iff.1 pres.span_range_relation_eq_ker _).1
            (Ideal.subset_span (Set.mem_range_self r)))).2
        dsimp
        rw [linearCombination_differentialsRelations_relation, ← this]
        congr
        ext g
        rw [MvPolynomial.mkDerivation_X] }
  left_inv s := by aesop
  right_inv := fun ⟨d, hd⟩ ↦ by aesop

noncomputable def differentialsRelationsSolutionEquiv :
    pres.differentialsRelations.Solution N ≃
      Derivation R S N :=
  pres.differentialsRelationsSolutionEquivSubtype.trans
    (Derivation.equivOfSurjective R pres.algebraMap_surjective N).symm

lemma differentialsRelationsSolutionEquiv_symm_naturality
    (d : Derivation R S N) [IsScalarTower R S N]
    {N' : Type*} [AddCommGroup N'] [Module S N'] [Module pres.Ring N']
    [Module R N'] [IsScalarTower R S N'] [IsScalarTower R pres.Ring N']
    [IsScalarTower pres.Ring S N'] (φ : N →ₗ[S] N') :
    pres.differentialsRelationsSolutionEquiv.symm (LinearMap.compDer φ d) =
    (pres.differentialsRelationsSolutionEquiv.symm d).postcomp φ := by
  rfl

end

/-- The `S`-module `Ω[S⁄R]` contains an obvious solution to the system of linear
equations `pres.differentialsRelations.Solution` when `pres` is a presentation
of `S` as a `R`-algebra. -/
noncomputable def differentialsSolution :
    pres.differentialsRelations.Solution (Ω[S⁄R]) :=
  pres.differentialsRelationsSolutionEquiv.symm (D R S)

@[nolint unusedArguments]
def algebraize (_ : Presentation R S)
    (N : Type w') [AddCommGroup N] [Module S N] := N

section

variable {N : Type w'} [AddCommGroup N] [Module S N]

instance : AddCommGroup (algebraize pres N) :=
  inferInstanceAs (AddCommGroup N)

instance : Module S (algebraize pres N) :=
  inferInstanceAs (Module S N)

instance : Module R (algebraize pres N) :=
  Module.compHom N (algebraMap R S)

instance : Module pres.Ring (algebraize pres N) :=
  Module.compHom N (algebraMap pres.Ring S)

instance : IsScalarTower R S (algebraize pres N) :=
  IsScalarTower.of_algebraMap_smul (by intros; rfl)

instance : IsScalarTower pres.Ring S (algebraize pres N) :=
  IsScalarTower.of_algebraMap_smul (by intros; rfl)

instance : IsScalarTower R pres.Ring (algebraize pres N) :=
  IsScalarTower.of_algebraMap_smul
    (by simp [← IsScalarTower.algebraMap_smul S])

lemma compatibility₂
    (s : pres.differentialsRelations.Solution (algebraize pres N)) :
    pres.differentialsSolution.postcomp
      (pres.differentialsRelationsSolutionEquiv s).liftKaehlerDifferential = s := by
  obtain ⟨d, rfl⟩ := pres.differentialsRelationsSolutionEquiv.symm.surjective s
  simp only [Equiv.apply_symm_apply]
  dsimp [differentialsSolution]
  rw [← pres.differentialsRelationsSolutionEquiv_symm_naturality (D R S)
    d.liftKaehlerDifferential]
  congr
  aesop

lemma compatibility₁
    (s : pres.differentialsRelations.Solution (algebraize pres N)) (g : pres.vars) :
    (pres.differentialsRelationsSolutionEquiv s).liftKaehlerDifferential
      (pres.differentialsSolution.var g) = s.var g :=
  Module.Relations.Solution.congr_var (compatibility₂ pres s) g

end

/-- The `S`-module `Ω[S⁄R]` admits a presentation by generators and relations that
is determined by a presentation of `S` as a `R`-algebra. -/
noncomputable def isPresentationCoreDifferentialsSolution :
    Module.Relations.Solution.IsPresentationCore.{w'}
      pres.differentialsSolution where
  desc {N _ _} s := by
    change Ω[S⁄R] →ₗ[S] algebraize pres N
    exact Derivation.liftKaehlerDifferential
      (pres.differentialsRelationsSolutionEquiv s)
  postcomp_desc {N _ _} s := by
    ext g
    exact compatibility₁ pres s g
  postcomp_injective {N _ _ f f' h} := by
    change Ω[S⁄R] →ₗ[S] algebraize pres N at f f'
    apply (KaehlerDifferential.linearMapEquivDerivation _ _ ).injective
    apply pres.differentialsRelationsSolutionEquiv.symm.injective
    ext g
    exact Module.Relations.Solution.congr_var h g

lemma differentialsSolution_isPresentation :
    pres.differentialsSolution.IsPresentation :=
  pres.isPresentationCoreDifferentialsSolution.isPresentation

/-- The presentation of the `S`-module `Ω[S⁄R]` deduced from a presentation
of `S` as a `R`-algebra. -/
noncomputable def differentials : Module.Presentation S (Ω[S⁄R]) where
  toSolution := differentialsSolution pres
  toIsPresentation := pres.differentialsSolution_isPresentation

end Algebra.Presentation
