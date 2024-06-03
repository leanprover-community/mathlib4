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

variable (C : Type u) [Category.{v} C] [ChosenFiniteProducts C] [ChosenCartesianClosed C]

instance (c : C) : Closed c := sorry

example (D : Type u') [Category.{v'} D] : ChosenFiniteProducts (D ⥤ C) := inferInstance

instance (D : Type u') [Category.{v'} D] (F : D ⥤ C) : Closed F where
  rightAdj := {
    obj := fun G ↦ {
      obj := fun d ↦ F.obj d ⟶[C] G.obj d
      map := by
        intro d d' f
        dsimp
        have a := (ihom (F.obj d')).map (G.map f)
        have b := (MonoidalClosed.pre (F.map f)).app (G.obj d')
        have c := a ≫ b
        sorry
    }
    map := sorry
  }
  adj := sorry
end

noncomputable section

open Simplicial SimplexCategory SSet

def SSetIHom (X Y : SSet) : SSet where
  obj := fun ⟨n⟩ ↦ (Δ[len n] ⊗ X) ⟶ Y
  map := fun f g ↦ standardSimplex.map f.unop ▷ X ≫ g

def SSetRightAdj (X : SSet) : SSet ⥤ SSet where
  obj Y := SSetIHom X Y
  map f := { app := fun _ h ↦ h ≫ f }

def aux1 {X Y Z : SSet} (f : X ⊗ Y ⟶ Z) (n : SimplexCategoryᵒᵖ) (Yn: Y.obj n) :
    standardSimplex.obj n.unop ⊗ X ⟶ Z where
  app := fun m ⟨g, Xm⟩ ↦ f.app m (Xm, Y.map g.down.op Yn)
  naturality l m h := by
    ext ⟨g, Xl⟩
    dsimp
    change f.app m (X.map h Xl, Y.map ((standardSimplex.obj n.unop).map h g).down.op Yn) = _
    have H := f.naturality h
    apply_fun (fun f ↦ f (Xl, Y.map g.down.op Yn)) at H
    dsimp [standardSimplex, yoneda, SSet.uliftFunctor]
    aesop

def aux2 {X Y Z : SSet} (f : X ⊗ Y ⟶ Z) : Y ⟶ ((SSetRightAdj X).obj Z) where
  app n Yn := aux1 f n Yn
  naturality n m g := by
    ext Yn
    dsimp [SSetRightAdj, SSetIHom]
    ext l ⟨h, Xl⟩
    change _ = (aux1 f n Yn).app l ((standardSimplex.map g.unop ▷ X).app l (h, Xl))
    dsimp [aux1, standardSimplex, yoneda, SSet.uliftFunctor]
    aesop

def need {X Y Z : SSet} (f : Y ⟶ (SSetRightAdj X).obj Z) (n m : SimplexCategoryᵒᵖ) (g : n ⟶ m)
    (Xn : X.obj n) (Yn : Y.obj n) :
    (f.app m (Y.map g Yn)).app m (Equiv.ulift.symm (Hom.mk OrderHom.id), X.map g Xn) = (f.app n Yn).app m (Equiv.ulift.symm g.unop, X.map g Xn) := by
  sorry

def aux3 {X Y Z : SSet} (f : Y ⟶ (SSetRightAdj X).obj Z) : (tensorLeft X).obj Y ⟶ Z where
  app := fun n ⟨Xn, Yn⟩ ↦ (f.app n Yn).app n (Equiv.ulift.symm (Hom.mk OrderHom.id), Xn)
  naturality n m g := by
    ext ⟨Xn, Yn⟩
    let id_n : Δ[n.unop.len].obj n := Equiv.ulift.symm (Hom.mk OrderHom.id)
    let id_m : Δ[m.unop.len].obj m := Equiv.ulift.symm (Hom.mk OrderHom.id)
    change (f.app m ((Y.map g Yn))).app m (id_m, X.map g Xn) = Z.map g ((f.app n Yn).app n (id_n, Xn))
    have a := (f.app n Yn).naturality g
    apply_fun (fun f ↦ f (id_n, Xn)) at a
    simp only [mk_len, yoneda_obj_obj, types_comp_apply] at a
    rw [← a]
    change _ = (f.app n Yn).app m (Δ[n.unop.len].map g (id_n), X.map g Xn)
    have : (Δ[n.unop.len].map g (id_n)).down.op = g :=
      Eq.symm (eq_of_comp_right_eq fun {X} ↦ congrFun rfl)
    rw [← this]
    simp [mk_len, yoneda_obj_obj, standardSimplex, SSet.uliftFunctor]
    have hh : g.unop ≫ id_n.down ≫ id_n.down = g.unop := Eq.symm
      (Hom.ext g.unop (g.unop ≫ id_n.down ≫ id_n.down)
        (congrArg Hom.toOrderHom (congrArg Quiver.Hom.unop (id (Eq.symm this)))))
    rw [hh]
    have h : Y.map id_n.down.op Yn = Yn := sorry
    have lol : X.map id_n.down.op Xn = Xn := sorry
    rw [h, lol]
    exact need f n m g Xn Yn

def SSetAdj (X : SSet) : tensorLeft X ⊣ SSetRightAdj X where
  homEquiv Y Z := {
    toFun := fun f ↦ aux2 f
    invFun := fun f ↦ aux3 f
    left_inv := fun f ↦ by
      ext n ⟨Xn, Yn⟩
      change f.app n (Xn, Y.map (𝟙 _) Yn) = _
      rw [FunctorToTypes.map_id_apply Y Yn]
    right_inv := fun f ↦ by
      ext n Yn
      dsimp [aux2, aux1, aux3]
      have := (f.app n Yn).app n
      dsimp [SSetRightAdj, SSetIHom] at this
      sorry
  }
  unit := sorry
  counit := sorry
  homEquiv_unit := sorry
  homEquiv_counit := sorry

/-
variable (X Y : SSet)

def IHom_eval (X Y : SSet) : X ⊗ SSetIHom X Y ⟶ Y where
  app n := fun ⟨x, f⟩ ↦ by
    refine f.app n ⟨?_, x⟩
    exact standardSimplex.objMk (OrderHom.id)
  naturality n m g := by
    ext ⟨x, f⟩
    have := f.naturality g
    apply_fun (fun f => f (standardSimplex.objMk OrderHom.id, x)) at this
    dsimp at this ⊢
    rw [← this]
    rfl

@[simp]
def IHomCostruct (X Y : SSet) : CostructuredArrow (tensorLeft X) Y :=
  CostructuredArrow.mk (IHom_eval X Y)

def uniqhom (X Y : SSet) : (A : CostructuredArrow (tensorLeft X) Y) → A ⟶ (IHomCostruct X Y) := by
  rintro ⟨A, h1, h2, h3⟩
  refine {
    left := {
      app := by
        intro n a
        refine ⟨?_, ?_⟩
        rintro m ⟨g', x⟩
        have g := (standardSimplex.objEquiv n.unop m).toFun g'
        exact h2 m (x, A.map g.op a)

        intro c d f
        ext ⟨nc, Xc⟩
        dsimp only [mk_len, Opposite.op_unop, Equiv.toFun_as_coe, types_comp_apply]
        let P := standardSimplex.objEquiv
        have h := h3 f
        apply_fun (fun f ↦ f (Xc, A.map ((P n.unop c) nc).op a)) at h
        dsimp only [tensorLeft_obj, Functor.const_obj_obj, Opposite.op_unop, types_comp_apply] at h
        rw [← h]
        have : ((standardSimplex.obj n.unop ⊗ X).map f (nc, Xc)) = ⟨(standardSimplex.obj n.unop).map f nc, X.map f Xc⟩ := rfl
        rw [this]
        simp
        change h2 d (X.map f Xc, A.map ((P n.unop d) ((standardSimplex.obj n.unop).map f nc)).op a) = _
        change _ = h2 d (X.map f Xc, A.map f (A.map ((P n.unop c) nc).op a))
        have Q : A.map f (A.map ((P n.unop c) nc).op a) = A.map ((P n.unop d) ((standardSimplex.obj n.unop).map f nc)).op a := by
          sorry
        rw [Q]
      naturality := sorry
    }
    right := 𝟙 _
  }

def costruct_isterminal (X Y : SSet) : Limits.IsTerminal (IHomCostruct X Y) := by
  apply Limits.IsTerminal.ofUniqueHom (uniqhom X Y)
  intro A f
  sorry

lemma costruct_terminal : ∀ A, Limits.HasTerminal (CostructuredArrow (tensorLeft X) A) := fun A ↦ by
  sorry

#check @rightAdjointOfCostructuredArrowTerminalsAux _ _ _ _ (tensorLeft X) (costruct_terminal X) Y

end
-/
