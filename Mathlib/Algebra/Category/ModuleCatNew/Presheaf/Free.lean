import Mathlib.Algebra.Category.ModuleCatNew.Presheaf.Basic
import Mathlib.Algebra.Category.ModuleCatNew.Free

universe u v₁ u₁

open CategoryTheory

namespace PresheafOfModulesNew

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

variable {R} in
@[simps]
noncomputable def freeObj (F : Cᵒᵖ ⥤ Type u) : PresheafOfModulesNew.{u} R where
  obj := fun X ↦ (ModuleCatNew.free (R.obj X)).obj (F.obj X)
  map := fun {X Y} f ↦ ModuleCatNew.freeDesc
      (fun x ↦ ModuleCatNew.freeMk (R := R.obj Y) (F.map f x))

@[simps]
noncomputable def free : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModulesNew.{u} R where
  obj := freeObj
  map {F G} φ :=
    { app := fun X ↦ (ModuleCatNew.free (R.obj X)).map (φ.app X)
      naturality := fun {X Y} f ↦ by
        ext x
        simp only [comp_apply, ModuleCatNew.freeDesc_apply, ModuleCatNew.restrictScalars_map,
          ModuleCatNew.free_map_apply]
        congr
        exact NatTrans.naturality_apply φ f x }

end PresheafOfModulesNew
