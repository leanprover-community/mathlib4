import Mathlib.AlgebraicGeometry.AlgebraicCycle.Sheaf

open AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (F : X.Modules)

noncomputable
def l (U : TopologicalSpace.Opens ↑X) (x : ↑X) (hx : x ∈ U) :
    Module Γ(X, U) ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
  Module.compHom ↑(TopCat.Presheaf.stalk F.val.presheaf x) (X.ringCatSheaf.presheaf.germ U x hx).hom

noncomputable
def germModuleHom (U : TopologicalSpace.Opens ↑X) (x : ↑X) (hx : x ∈ U) :
    letI := l F U x hx
    Γ(F, U) →ₗ[Γ(X, U)] ↑(TopCat.Presheaf.stalk F.val.presheaf x) :=
  letI := l F U x hx
  {
    __ := (TopCat.Presheaf.germ F.val.presheaf U x hx).hom
    map_smul' := PresheafOfModules.germ_ringCat_smul F.val x U hx
  }
