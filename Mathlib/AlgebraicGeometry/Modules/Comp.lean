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

open scoped ModuleCat.Algebra in
def localizedModuleFunctorExtendScalarsIso :
    ModuleCat.localizedModuleFunctor.{u} S ≅
      ModuleCat.extendScalars (algebraMap R (Localization S)) := by
  letI : IsScalarTower R (Localization S)
      ((ModuleCat.restrictScalars (algebraMap R (Localization S))).obj
        (ModuleCat.of (Localization S) (Localization S))) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e (M : ModuleCat.{u} R) :
      (ModuleCat.localizedModuleFunctor S).obj M ≃ₗ[Localization S]
        (ModuleCat.extendScalars (algebraMap R (Localization S))).obj M :=
    (Shrink.linearEquiv (Localization S) (LocalizedModule S M)).trans <|
      (LocalizedModule.equivTensorProduct S M).trans <|
        (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) (LinearEquiv.refl R M) :
          TensorProduct R (Localization S) M ≃ₗ[Localization S]
            (ModuleCat.extendScalars (algebraMap R (Localization S))).obj M)
  have e_apply_mk (M : ModuleCat.{u} R) (m : M) :
      e M (M.localizedModuleMkLinearMap S m) =
        (show (ModuleCat.extendScalars (algebraMap R (Localization S))).obj M from
        (TensorProduct.mk R
          ((ModuleCat.restrictScalars (algebraMap R (Localization S))).obj
            (ModuleCat.of (Localization S) (Localization S))) M
          (show (ModuleCat.restrictScalars (algebraMap R (Localization S))).obj
            (ModuleCat.of (Localization S) (Localization S)) from (1 : Localization S))) m) := by
    dsimp [e, ModuleCat.localizedModuleMkLinearMap]
    have hshrink :
        (Shrink.linearEquiv (Localization S) (LocalizedModule S M))
          (((Shrink.linearEquiv R (LocalizedModule S M)).symm.toLinearMap.comp
            (LocalizedModule.mkLinearMap S M)) m) =
          (LocalizedModule.mkLinearMap S M) m := by
      change (equivShrink (LocalizedModule S M)).symm
          (equivShrink (LocalizedModule S M) ((LocalizedModule.mkLinearMap S M) m)) =
        (LocalizedModule.mkLinearMap S M) m
      simp
    change
      (show (ModuleCat.extendScalars (algebraMap R (Localization S))).obj M from
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) (LinearEquiv.refl R M) :
          TensorProduct R (Localization S) M ≃ₗ[Localization S]
            (ModuleCat.extendScalars (algebraMap R (Localization S))).obj M))
        ((LocalizedModule.equivTensorProduct S M)
          ((Shrink.linearEquiv (Localization S) (LocalizedModule S M))
            (((Shrink.linearEquiv R (LocalizedModule S M)).symm.toLinearMap.comp
              (LocalizedModule.mkLinearMap S M)) m)))) =
      (show (ModuleCat.extendScalars (algebraMap R (Localization S))).obj M from
      (TensorProduct.mk R
        ((ModuleCat.restrictScalars (algebraMap R (Localization S))).obj
          (ModuleCat.of (Localization S) (Localization S))) M
        (show (ModuleCat.restrictScalars (algebraMap R (Localization S))).obj
          (ModuleCat.of (Localization S) (Localization S)) from (1 : Localization S))) m)
    rw [hshrink]
    simp [Localization.mk_one_eq_algebraMap, LinearEquiv.refl_apply]
    rfl
  refine NatIso.ofComponents (fun M => LinearEquiv.toModuleIso <| e M) ?_
  intro X Y g
  letI : Module R ((ModuleCat.localizedModuleFunctor S).obj X) :=
    inferInstanceAs (Module R (X.localizedModule S))
  letI : IsScalarTower R (Localization S) ((ModuleCat.localizedModuleFunctor S).obj X) :=
    inferInstanceAs (IsScalarTower R (Localization S) (X.localizedModule S))
  letI : Module R ((ModuleCat.localizedModuleFunctor S).obj Y) :=
    inferInstanceAs (Module R (Y.localizedModule S))
  letI : IsScalarTower R (Localization S) ((ModuleCat.localizedModuleFunctor S).obj Y) :=
    inferInstanceAs (IsScalarTower R (Localization S) (Y.localizedModule S))
  letI : Module R ((ModuleCat.extendScalars (algebraMap R (Localization S))).obj Y) :=
    Module.compHom _ (algebraMap R (Localization S))
  letI : IsScalarTower R (Localization S)
      ((ModuleCat.extendScalars (algebraMap R (Localization S))).obj Y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let targetMap : Y →ₗ[R]
      (ModuleCat.extendScalars (algebraMap R (Localization S))).obj Y :=
    ((e Y).restrictScalars R).toLinearMap.comp (Y.localizedModuleMkLinearMap S)
  haveI : IsLocalizedModule S targetMap := by
    dsimp [targetMap]
    exact IsLocalizedModule.of_linearEquiv
      (S := S) (f := Y.localizedModuleMkLinearMap S) ((e Y).restrictScalars R)
  apply ModuleCat.hom_ext
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext S (X.localizedModuleMkLinearMap S) targetMap
  ext m
  change (e Y)
      (((ModuleCat.localizedModuleFunctor S).map g) (X.localizedModuleMkLinearMap S m)) =
    ((ModuleCat.extendScalars (algebraMap R (Localization S))).map g)
      ((e X) (X.localizedModuleMkLinearMap S m))
  simp only [ModuleCat.localizedModuleFunctor, ModuleCat.localizedModuleMap,
    ModuleCat.hom_ofHom, IsLocalizedModule.mapExtendScalars_apply_apply,
    IsLocalizedModule.map_apply]
  change (e Y) (show Y.localizedModule S from Y.localizedModuleMkLinearMap S (g m)) =
    ((ModuleCat.extendScalars (algebraMap R (Localization S))).map g)
      ((e X) (show X.localizedModule S from X.localizedModuleMkLinearMap S m))
  rw [e_apply_mk Y (g m), e_apply_mk X m]
  rfl
