module

public import Mathlib

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

universe u

variable {R S : CommRingCat.{u}} (f : R ⟶ S)

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The natural isomorphism between the two right adjoints: taking global sections over
`Spec S` and restricting scalars along `f` agrees with pushing forward along `Spec f` and
then taking global sections over `Spec R`. -/
noncomputable abbrev pushforwardCompModuleSpecΓFunctorIso :
    pushforward (Spec.map f) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars f.hom :=
  Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso f)
    ((sheafSections (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R)).obj (.op ⊤))

/-- Base change compatibility of the tilde functor: for a ring homomorphism `f : R ⟶ S`,
extending scalars and then taking the associated sheaf over `Spec S` is naturally isomorphic
to taking the associated sheaf over `Spec R` and then pulling back along `Spec f`. -/
noncomputable abbrev extendScalarsCompTildeFunctorIso :
    ModuleCat.extendScalars f.hom ⋙ tilde.functor S ≅
      tilde.functor R ⋙ pullback (Spec.map f) :=
  (conjugateIsoEquiv (tilde.adjunction.comp (pullbackPushforwardAdjunction (Spec.map f)))
    ((ModuleCat.extendRestrictScalarsAdj f.hom).comp tilde.adjunction)).symm
    (pushforwardCompModuleSpecΓFunctorIso f)

noncomputable def magic₁ [IsOpenImmersion (Spec.map f)] :
    pullback (Spec.map f) ≅ restrictFunctor (Spec.map f) :=
  (restrictFunctorIsoPullback (Spec.map f)).symm
