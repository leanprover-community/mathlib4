import Mathlib.CategoryTheory.Abelian.Basic

/-!
# `FGModuleCat K` is an abelian category.

-/

@[expose] public section

noncomputable section

universe v u

open CategoryTheory Limits

namespace FGModuleCat

variable {k : Type u} [Ring k] [IsNoetherianRing k]

instance {X Y : FGModuleCat k} (f : X ⟶ Y) : IsIso (Abelian.coimageImageComparison f) :=
  have := IsIso.of_isIso_fac_right (Abelian.PreservesCoimage.hom_coimageImageComparison
      (forget₂ (FGModuleCat k) (ModuleCat k)) f).symm
  Functor.FullyFaithful.isIso_of_isIso_map (ModuleCat.isFG k).fullyFaithfulι _

instance : Abelian (FGModuleCat k) := Abelian.ofCoimageImageComparisonIsIso

end FGModuleCat
