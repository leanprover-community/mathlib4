import Mathlib.Condensed.LocallyConstant
import Mathlib.Condensed.Module
import Mathlib.Condensed.Light.Module
import Mathlib.Topology.LocallyConstant.Algebra

universe w u

open CategoryTheory LocallyConstant CompHausLike Functor Category Functor

attribute [local instance] ConcreteCategory.instFunLike

variable {P : TopCat.{u} → Prop}

namespace Condensed.LocallyConstantModule

variable (R : Type (max u w)) [Ring R]

/--
The functor from the category of `R`-modules to presheaves on `CompHaus` given by locally constant
maps.
-/
@[simps]
def functorToPresheaves : ModuleCat.{max u w} R ⥤ ((CompHausLike.{u} P)ᵒᵖ ⥤ ModuleCat R) where
  obj X := {
    obj := fun ⟨S⟩ ↦ ModuleCat.of R (LocallyConstant S X)
    map := fun f ↦ comapₗ R f.unop }
  map f := { app := fun S ↦ mapₗ R f }

variable [HasExplicitFiniteCoproducts.{0} P] [HasExplicitPullbacks.{u} P]
  (hs : ∀ ⦃X Y : CompHausLike P⦄ (f : X ⟶ Y), EffectiveEpi f → Function.Surjective f)

/-- `Condensed.LocallyConstantModule.functorToPresheaves` lands in condensed modules. -/
@[simps]
def functor :
    have := CompHausLike.preregular hs
    ModuleCat R ⥤ Sheaf (coherentTopology (CompHausLike.{u} P)) (ModuleCat R) where
  obj X := {
    val := (functorToPresheaves.{w, u} R).obj X
    cond := by
      have := CompHausLike.preregular hs
      apply Presheaf.isSheaf_coherent_of_hasPullbacks_of_comp (s :=
        CategoryTheory.forget (ModuleCat R))
      exact ((Condensed.LocallyConstant.functor P hs).obj _).cond }
  map f := ⟨(functorToPresheaves.{w, u} R).map f⟩

end Condensed.LocallyConstantModule

namespace CondensedMod

variable (R : Type (u+1)) [Ring R]

abbrev LocallyConstant.functor : ModuleCat R ⥤ CondensedMod.{u} R :=
  Condensed.LocallyConstantModule.functor.{u+1, u} R
    (fun _ _ _ ↦ ((CompHaus.effectiveEpi_tfae _).out 0 2).mp)

def LocallyConstant.functorIsoDiscrete_components (M : ModuleCat R) :
    (functor R).obj M ≅ (Condensed.discrete _).obj M := by
  simp only [functor, Condensed.LocallyConstantModule.functor, Condensed.discrete_obj]
  have : (Condensed.forget R).ReflectsIsomorphisms :=
    inferInstanceAs (sheafCompose _ _).ReflectsIsomorphisms
  sorry

def LocallyConstant.functorIsoDiscrete : functor R ≅ Condensed.discrete _ :=
  sorry

end CondensedMod

namespace LightCondMod

variable (R : Type u) [Ring R]

abbrev LocallyConstant.functor : ModuleCat R ⥤ LightCondMod.{u} R :=
  Condensed.LocallyConstantModule.functor.{u, u} R
    (fun _ _ _ ↦ (LightProfinite.effectiveEpi_iff_surjective _).mp)

def LocallyConstant.functorIsoDiscrete : functor R ≅ LightCondensed.discrete _ := sorry

end LightCondMod
