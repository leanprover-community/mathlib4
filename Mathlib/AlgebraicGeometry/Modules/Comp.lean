module

public import Mathlib

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Scheme.Modules

universe u

variable {R R' : CommRingCat.{u}} (f : R ⟶ R')

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The natural isomorphism between the two right adjoints: taking global sections over
`Spec S` and restricting scalars along `f` agrees with pushing forward along `Spec f` and
then taking global sections over `Spec R`. -/
abbrev pushforwardCompModuleSpecΓFunctorIso :
    pushforward (Spec.map f) ⋙ moduleSpecΓFunctor ≅
      moduleSpecΓFunctor ⋙ ModuleCat.restrictScalars f.hom :=
  Functor.isoWhiskerRight (pushforwardCompModulesSpecToSheafIso f)
    ((sheafSections (Opens.grothendieckTopology (Spec R)) (ModuleCat.{u} R)).obj (.op ⊤))

/-- Base change compatibility of the tilde functor: for a ring homomorphism `f : R ⟶ S`,
extending scalars and then taking the associated sheaf over `Spec S` is naturally isomorphic
to taking the associated sheaf over `Spec R` and then pulling back along `Spec f`. -/
abbrev extendScalarsCompTildeFunctorIso :
    ModuleCat.extendScalars f.hom ⋙ tilde.functor R' ≅
      tilde.functor R ⋙ pullback (Spec.map f) :=
  (conjugateIsoEquiv (tilde.adjunction.comp (pullbackPushforwardAdjunction (Spec.map f)))
    ((ModuleCat.extendRestrictScalarsAdj f.hom).comp tilde.adjunction)).symm
    (pushforwardCompModuleSpecΓFunctorIso f)

variable (S : Submonoid R)

def localizedModuleFunctorExtendScalarsIso :
    ModuleCat.localizedModuleFunctor S ≅
      ModuleCat.extendScalars (algebraMap R (Localization S)) := sorry
