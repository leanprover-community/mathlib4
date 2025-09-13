import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Over

universe v u v₁ u₁

open CategoryTheory Opposite Bicategory

variable {C : Type u} [Category.{v} C]

def homPreSheaf (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) (U : C) (x y : S.obj ⟨op U⟩) :
    Opposite (Over U) ⥤ Type v₁ where
  obj V := (S.map ⟨V.unop.hom.op⟩).obj x ⟶ (S.map ⟨V.unop.hom.op⟩).obj y
  map {V V'} g := by
    let f : Discrete (op U ⟶ op (unop V).left) := ⟨V.unop.hom.op⟩
    let f' : Discrete (op U ⟶ op (unop V').left) := ⟨V'.unop.hom.op⟩
    let g' : Discrete (op (unop V).left ⟶ op (unop V').left) := ⟨g.unop.left.op⟩
    have w : f.as ≫ g'.as = f'.as := by
      simp [f, f', g']
      rw [← op_comp]; simp
    let α := S.mapComp f g'
    intro ϕ
    let gϕ := (S.map g').map ϕ
    let eq : ∀ x, (S.map f').obj x ≅ (S.map (f ≫ g')).obj x :=
      fun x ↦ eqToIso (by congr; apply Discrete.ext; simp [w])
    exact (eq x).hom ≫ α.hom.app x ≫ gϕ ≫ α.inv.app y ≫ (eq y).inv

  map_id := by
    rintro ⟨⟨X, _, f⟩⟩
    ext g
    simp only [Functor.id_obj, Functor.const_obj_obj, unop_id, Over.id_left, op_id, eqToIso.hom,
      Cat.comp_obj, eqToIso.inv, types_id_apply]
    dsimp at f g
    erw [Pseudofunctor.mapComp_id_right_hom]
    dsimp only [Cat.comp_app, Cat.comp_obj, Cat.id_obj, Cat.whiskerLeft_app]
    simp only [Category.assoc]
    erw [Pseudofunctor.mapComp_id_right_inv]
    dsimp only [Cat.comp_app, Cat.comp_obj, Cat.id_obj, Cat.whiskerLeft_app]
    simp only [Category.assoc, NatTrans.naturality_assoc, Cat.id_obj, Cat.id_map,
      Iso.inv_hom_id_app_assoc]
    rw [Cat.rightUnitor_inv_app]
    rw [Cat.rightUnitor_hom_app]
    simp only [Cat.comp_obj, Cat.id_obj, eqToHom_refl, Category.id_comp]
    simp only [Pseudofunctor.map₂_right_unitor, Cat.comp_app, Cat.comp_obj, Cat.id_obj,
      Cat.whiskerLeft_app, Category.assoc]
    -- rw [Cat.rightUnitor_inv_app]
    rw [Cat.rightUnitor_hom_app]
    simp only [Cat.comp_obj, Cat.id_obj, eqToHom_refl, Category.id_comp]
    have : (S.map₂ (ρ_ (⟨f.op⟩ : Discrete (op U ⟶ op X))).hom).app x ≫ (ρ_ (S.map (⟨f.op⟩ : Discrete (op U ⟶ op X)))).inv.app x = sorry := by
      rw [Cat.rightUnitor_inv_app]
      sorry
    -- let _ := g.w

  map_comp := _

variable {J : GrothendieckTopology C}

structure IsStack (S : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v₁, u₁}) where
  isSheafOfHom : ∀ (U : C) (x y : S.obj ⟨op U⟩), Presieve.IsSheaf (J.over U) (homPreSheaf S U x y)
