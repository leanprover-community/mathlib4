import Mathlib.Algebra.Category.ModuleCat.PresheafNew.Basic
import Mathlib.Algebra.Category.ModuleCat.Adjunctions

universe u v₁ u₁

open CategoryTheory

namespace ModuleCat

section

variable {R : Type u} [Ring R]

noncomputable def freeMk {X : Type u} (x : X) : (free R).obj X := Finsupp.single x 1

@[ext 1200]
lemma free_hom_ext {X : Type u} {M : ModuleCat.{u} R} {f g : (free R).obj X ⟶ M}
    (h : ∀ (x : X), f (freeMk x) = g (freeMk x)) :
    f = g :=
  (Finsupp.lhom_ext' (fun x ↦ LinearMap.ext_ring (h x)))

noncomputable def freeDesc {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) :
    (free R).obj X ⟶ M :=
  Finsupp.lift M R X f

@[simp]
lemma freeDesc_apply {X : Type u} {M : ModuleCat.{u} R} (f : X ⟶ M) (x : X) :
    freeDesc f (freeMk x : of R (X →₀ R)) = f x := by
  dsimp [freeDesc]
  erw [Finsupp.lift_apply, Finsupp.sum_single_index]
  all_goals simp

@[simp]
lemma free_map_apply {X Y : Type u} (f : X → Y) (x : X) :
    (free R).map f (freeMk x) = freeMk (f x) := by
  apply Finsupp.mapDomain_single

end

end ModuleCat

namespace PresheafOfModulesNew

variable {C : Type u₁} [Category.{v₁} C] (R : Cᵒᵖ ⥤ RingCat.{u})

variable {R} in
@[simps]
noncomputable def freeObj (F : Cᵒᵖ ⥤ Type u) : PresheafOfModulesNew.{u} R where
  obj := fun X ↦ (ModuleCat.free (R.obj X)).obj (F.obj X)
  map := fun {X Y} f ↦ ModuleCat.freeDesc
      (fun x ↦ ModuleCat.freeMk (R := R.obj Y) (F.map f x))
  map_id X := by ext; simp
  map_comp _ _ := by ext; dsimp; simp

@[simps]
noncomputable def free : (Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModulesNew.{u} R where
  obj := freeObj
  map {F G} φ :=
    { app := fun X ↦ (ModuleCat.free (R.obj X)).map (φ.app X)
      naturality := fun {X Y} f ↦ by
        dsimp
        ext x
        simp only [ModuleCat.coe_comp, Function.comp_apply, ModuleCat.freeDesc_apply,
          ModuleCat.restrictScalars.map_apply, ModuleCat.free_map_apply]
        congr 1
        exact NatTrans.naturality_apply φ f x }

end PresheafOfModulesNew
