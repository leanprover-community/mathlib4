/-!

# Light condensed `R`-modules

This file defines light condensed modules over a ring `R`.

## Main results

* Light condensed `R`-modules form an abelian category.

* The forgetful functor from light condensed `R`-modules to light condensed sets has a left
  adjoint, sending a light condensed set to the corresponding *free* light condensed `R`-module.
-/

@[expose] public section


universe u

open CategoryTheory

variable (R : Type u) [Ring R]

/--
The category of light condensed `R`-modules, defined as sheaves of `R`-modules over
`LightProfinite.{u}` with respect to the coherent Grothendieck topology.
-/
abbrev LightCondMod := LightCondensed.{u} (ModuleCat.{u} R)

noncomputable instance : Abelian (LightCondMod.{u} R) := sheafIsAbelian

/-- The forgetful functor from light condensed `R`-modules to light condensed sets. -/
@[simps! obj_val_map map_val_app]
def LightCondensed.forget : LightCondMod R ⥤ LightCondSet :=
  sheafCompose _ (CategoryTheory.forget _)

/--
The left adjoint to the forgetful functor. The *free light condensed `R`-module* on a light
condensed set.
-/
noncomputable
def LightCondensed.free : LightCondSet ⥤ LightCondMod R :=
  Sheaf.composeAndSheafify _ (ModuleCat.free R)

/-- The condensed version of the free-forgetful adjunction. -/
noncomputable
def LightCondensed.freeForgetAdjunction : free R ⊣ forget R := Sheaf.adjunction _ (ModuleCat.adj R)

/--
The category of light condensed abelian groups, defined as sheaves of `ℤ`-modules over
`LightProfinite.{0}` with respect to the coherent Grothendieck topology.
-/
abbrev LightCondAb := LightCondMod ℤ

noncomputable example : Abelian LightCondAb := inferInstance

namespace LightCondMod

lemma hom_naturality_apply {X Y : LightCondMod.{u} R} (f : X ⟶ Y) {S T : LightProfiniteᵒᵖ}
    (g : S ⟶ T) (x : X.val.obj S) : f.val.app T (X.val.map g x) = Y.val.map g (f.val.app S x) :=
  NatTrans.naturality_apply f.val g x

end LightCondMod
