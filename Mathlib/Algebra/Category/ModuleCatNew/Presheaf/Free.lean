import Mathlib.Algebra.Category.ModuleCatNew.Presheaf.Basic
import Mathlib.Algebra.Category.ModuleCatNew.Free

universe u v₁ u₁

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

-- with `ModuleCatNew.free` irreducible, this is 2440218 heartbeats
-- with `ModuleCatNew.free` not irreducible, this is 2630801 heartbeats
-- why is this so slow?
set_option maxHeartbeats 3200000 in
noncomputable def free : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R where
  obj F :=
    { obj := fun X ↦ (ModuleCatNew.free (R.obj X)).obj (F.obj X)
      map := fun {X Y} f ↦ ModuleCatNew.freeDesc
          (fun x ↦ ModuleCatNew.freeMk (R := R.obj Y) (F.map f x)) }
  map {F G} φ :=
    { app := fun X ↦ (ModuleCatNew.free (R.obj X)).map (φ.app X)
      naturality := fun {X Y} f ↦ by
        ext x
        simp only [comp_apply, ModuleCatNew.freeDesc_apply, ModuleCatNew.restrictScalars_map,
          ModuleCatNew.free_map_apply]
        congr
        exact NatTrans.naturality_apply φ f x }

end PresheafOfModules
