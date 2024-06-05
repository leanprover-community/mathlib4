import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.ChosenFiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.CategoryTheory.Limits.Presheaf

namespace CategoryTheory

universe w v v' u u'

open MonoidalCategory

class ChosenCartesianClosed (C : Type u) [Category.{v} C] where
  [chosenFiniteProducts: ChosenFiniteProducts C]
  rightAdj (X : C) : C ⥤ C
  adj (X : C) : @tensorLeft _ _ (monoidalOfHasFiniteProducts _) X ⊣ rightAdj X

namespace ChosenCartesianClosed

instance (C : Type u) [Category.{v} C] [i : ChosenCartesianClosed C] : ChosenFiniteProducts C :=
  i.chosenFiniteProducts

noncomputable section

def ofCartesianClosed (C : Type u) [Category.{v} C] [Limits.HasFiniteProducts C]
    [CartesianClosed C] : ChosenCartesianClosed C :=
  letI _ := ChosenFiniteProducts.ofFiniteProducts C
  letI _ : MonoidalCategory C := monoidalOfHasFiniteProducts C
{ rightAdj := fun X ↦ ihom X
  adj := fun X ↦ ihom.adjunction X
}

instance (C : Type u) [Category.{v} C] [ChosenCartesianClosed C] : CartesianClosed C :=
  letI _ : MonoidalCategory C := monoidalOfHasFiniteProducts C
  {
    closed := fun X ↦ {
      rightAdj := rightAdj X
      adj := adj X }
  }

--variable (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] [ChosenCartesianClosed C]

--instance (c : C) : Closed c := sorry

end

end ChosenCartesianClosed

noncomputable section

open Simplicial SimplexCategory SSet

def SSetIHom (X Y : SSet) : SSet where
  obj := fun ⟨n⟩ ↦ Δ[len n] ⊗ X ⟶ Y
  map := fun f g ↦ standardSimplex.map f.unop ▷ X ≫ g

def SSetRightAdj (X : SSet) : SSet ⥤ SSet where
  obj Y := SSetIHom X Y
  map f := { app := fun _ h ↦ h ≫ f }

def aux1 {X Y Z : SSet} (f : X ⊗ Y ⟶ Z) (n : SimplexCategoryᵒᵖ) (Yn: Y.obj n) :
    (SSetIHom X Z).obj n where
  app := fun m ⟨g, Xm⟩ ↦ f.app m (Xm, Y.map g.down.op Yn)
  naturality l m h := by
    ext ⟨g, Xl⟩
    change f.app m (X.map h Xl, Y.map ((standardSimplex.obj n.unop).map h g).down.op Yn) = _
    have H := f.naturality h
    apply_fun (fun f ↦ f (Xl, Y.map g.down.op Yn)) at H
    dsimp [standardSimplex, yoneda, SSet.uliftFunctor]
    aesop

def aux2 {X Y Z : SSet} (f : X ⊗ Y ⟶ Z) : Y ⟶ SSetIHom X Z where
  app n Yn := aux1 f n Yn
  naturality n m g := by
    ext Yn
    dsimp [SSetRightAdj, SSetIHom]
    ext l ⟨h, Xl⟩
    change _ = (aux1 f n Yn).app l ((standardSimplex.map g.unop ▷ X).app l (h, Xl))
    dsimp [aux1, standardSimplex, yoneda, SSet.uliftFunctor]
    aesop

def aux3 {X Y Z : SSet} (f : Y ⟶ SSetIHom X Z) : X ⊗ Y ⟶ Z where
  app n x := (f.app n x.2).app n (standardSimplex.objMk OrderHom.id, x.1)
  naturality n m g := by
    dsimp
    ext ⟨Xn, Yn⟩
    change (f.app m ((Y.map g Yn))).app m (_, X.map g Xn) = Z.map g ((f.app n Yn).app n (_, Xn))
    have b := f.naturality g
    apply_fun (fun f ↦ (f Yn).app m (standardSimplex.objMk OrderHom.id, X.map g Xn)) at b
    have a := (f.app n Yn).naturality g
    apply_fun (fun f ↦ f (standardSimplex.objMk OrderHom.id, Xn)) at a
    simp only [mk_len, types_comp_apply] at a b
    rw [b, ← a]
    rfl

@[ext]
lemma ext {X Y : SSet} {n : SimplexCategoryᵒᵖ} {f g : (SSetIHom X Y).obj n} :
    f.app = g.app → f = g := NatTrans.ext _ _

def SSetAdj (X : SSet) : tensorLeft X ⊣ SSetRightAdj X where
  homEquiv Y Z := {
    toFun := fun f ↦ aux2 f
    invFun := fun f ↦ aux3 f
    left_inv := fun f ↦ by
      ext n ⟨Xn, Yn⟩
      change f.app n (Xn, Y.map (𝟙 _) Yn) = _
      aesop
    right_inv := fun f ↦ by
      dsimp [aux1, aux2, aux3]
      ext n Yn m ⟨g, Xm⟩
      have b := f.naturality g.down.op
      apply_fun (fun f ↦ (f Yn).app m (standardSimplex.objMk OrderHom.id, Xm)) at b
      dsimp at b
      rw [b]
      change (f.app n Yn).app m ({ down := 𝟙 _ ≫ g.down }, Xm) = _
      aesop
  }
  unit := {
    app := fun Y ↦ aux2 (𝟙 _)
    naturality := fun Y Z f ↦ by
      ext n Yn
      change (aux1 (𝟙 (X ⊗ Z)) n (f.app n Yn)) = ((SSetRightAdj X).map (X ◁ f)).app n (aux1 (𝟙 (X ⊗ Y)) n Yn)
      ext m ⟨g, Xm⟩
      change (Xm, Z.map g.down.op (f.app n Yn)) = (X ◁ f).app m (Xm, Y.map g.down.op Yn)
      simp only [Opposite.op_unop, mk_len, yoneda_obj_obj, whiskerLeft_app_apply, Prod.mk.injEq,
        true_and]
      exact Eq.symm (FunctorToTypes.naturality Y Z f g.down.op Yn)
  }
  counit := { app := fun Y ↦ aux3 (𝟙 _) }

instance : MonoidalClosed SSet where
  closed X := {
    rightAdj := SSetRightAdj X
    adj := SSetAdj X
  }

variable {C : Type u} [Category.{v} C]

def UliftFunctor : (Cᵒᵖ ⥤ Type v) ⥤ Cᵒᵖ ⥤ Type max u v :=
  (whiskeringRight _ _ _).obj uliftFunctor.{u, v}

def yonedaLift {C : Type u} [Category.{v} C] : C ⥤ Cᵒᵖ ⥤ Type (max u v) :=
    yoneda ⋙ UliftFunctor.{v, u}

def IHom (F G : Cᵒᵖ ⥤ Type max u v) : Cᵒᵖ ⥤ Type max u v where
  obj c := (yonedaLift.obj c.unop) ⊗ F ⟶ G
  map := fun f g ↦ yonedaLift.map f.unop ▷ F ≫ g

def RightAdj (F : Cᵒᵖ ⥤ Type max u v) : (Cᵒᵖ ⥤ Type max u v) ⥤ Cᵒᵖ ⥤ Type max u v where
  obj G := IHom F G
  map f := { app := fun _ h ↦ h ≫ f }

def Aux1 {F G H : Cᵒᵖ ⥤ Type max u v} (f : F ⊗ G ⟶ H) (c : Cᵒᵖ) (Gc: G.obj c) :
    (IHom F H).obj c where
  app := fun d ⟨g, Fd⟩ ↦ f.app d (Fd, G.map g.down.op Gc)
  naturality a b h := by
    ext ⟨g, Fa⟩
    change f.app b (F.map h Fa, G.map ((yonedaLift.obj c.unop).map h g).down.op Gc) = _
    have := f.naturality h
    apply_fun (fun f ↦ f (Fa, G.map g.down.op Gc)) at this
    dsimp [yonedaLift, UliftFunctor]
    aesop
