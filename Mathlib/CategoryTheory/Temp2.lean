import Mathlib.CategoryTheory.Monoidal.FunctorCategory
import Mathlib.CategoryTheory.Monoidal.Types.Basic
import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.Tactic.ApplyFun

namespace CategoryTheory

universe w v u

open MonoidalCategory

variable {C : Type u} [Category.{v} C]

namespace FunctorToTypes

def uliftFunctor : (C ⥤ Type v) ⥤ C ⥤ Type max u v w :=
  (whiskeringRight _ _ _).obj (CategoryTheory.uliftFunctor.{u, v} ⋙ CategoryTheory.uliftFunctor.{w, max u v})

def coyonedaLift {C : Type u} [Category.{v} C] : Cᵒᵖ ⥤ C ⥤ Type (max u v w) :=
    coyoneda ⋙ uliftFunctor.{w, v, u}

noncomputable section

def ihom (F G : C ⥤ Type max u v w) : C ⥤ Type max u v w where
  obj c := (coyonedaLift.obj (.op c)) ⊗ F ⟶ G
  map := fun f g ↦ coyonedaLift.map (.op f) ▷ F ≫ g

def rightAdj (F : C ⥤ Type max u v w) : (C ⥤ Type max u v w) ⥤ C ⥤ Type max u v w where
  obj G := ihom F G
  map f := { app := fun _ h ↦ h ≫ f }

def homEquiv_toFun_app {F G H : C ⥤ Type max u v w} (f : F ⊗ G ⟶ H) {c : C} (Gc: G.obj c) :
    (ihom F H).obj c where
  app := fun d ⟨g, Fd⟩ ↦ f.app d (Fd, G.map g.down.down Gc)
  naturality a b h := by
    ext ⟨g, Fa⟩
    have := f.naturality h
    apply_fun (fun f ↦ f (Fa, G.map g.down.down Gc)) at this
    dsimp only [coyonedaLift, uliftFunctor]
    aesop

def homEquiv_toFun {F G H : C ⥤ Type max u v w} (f : F ⊗ G ⟶ H) : G ⟶ ihom F H where
  app c Gc := homEquiv_toFun_app f Gc
  naturality c d g := by
    ext Gc
    dsimp [rightAdj, ihom]
    ext e ⟨h, Fe⟩
    simp [coyonedaLift, uliftFunctor, homEquiv_toFun_app]

def homEquiv_invFun {F G H : C ⥤ Type max u v w} (f : G ⟶ ihom F H) : F ⊗ G ⟶ H where
  app c x := (f.app c x.2).app c (Equiv.ulift.symm (Equiv.ulift.symm (𝟙 c)), x.1)
  naturality c d g := by
    ext ⟨Fc, Gc⟩
    simp only [Monoidal.tensorObj_obj, Monoidal.tensorObj_map, coyoneda_obj_obj, types_comp_apply,
      tensor_apply]
    have b := f.naturality g
    apply_fun (fun f ↦ (f Gc).app d (Equiv.ulift.symm (Equiv.ulift.symm (𝟙 d)), F.map g Fc)) at b
    have a := (f.app c Gc).naturality g
    apply_fun (fun f ↦ f (Equiv.ulift.symm (Equiv.ulift.symm (𝟙 c)), Fc)) at a
    dsimp only [coyoneda_obj_obj, types_comp_apply] at a b ⊢
    rw [b, ← a]
    simp [ihom, coyonedaLift, uliftFunctor]

@[ext]
lemma ext {F G : C ⥤ Type max u v w} {c : C} {f g : (ihom F G).obj c} :
    f.app = g.app → f = g := NatTrans.ext _ _

def homEquiv (F G H : C ⥤ Type (max u v w)) : (F ⊗ G ⟶ H) ≃ (G ⟶ (rightAdj F).obj H) where
  toFun := homEquiv_toFun
  invFun := homEquiv_invFun
  left_inv _ := by ext ; simp [homEquiv_invFun, homEquiv_toFun, homEquiv_toFun_app]
  right_inv f := by
    ext c Gc d ⟨g, Fd⟩
    have b := f.naturality g.down.down
    apply_fun (fun f ↦ (f Gc).app d (Equiv.ulift.symm (Equiv.ulift.symm (𝟙 d)), Fd)) at b
    dsimp [rightAdj, ihom, coyonedaLift, uliftFunctor] at b ⊢
    aesop

def adj (F : C ⥤ Type max u v w) : tensorLeft F ⊣ rightAdj F where
  homEquiv G H := homEquiv F G H
  unit := {
    app := fun g ↦ homEquiv_toFun (𝟙 _)
    naturality := fun G H f ↦ by
      ext c Gc
      dsimp [rightAdj, homEquiv_toFun, homEquiv_toFun_app]
      ext d ⟨g, Fd⟩
      dsimp only [Monoidal.tensorObj_obj, comp, Monoidal.whiskerLeft_app, whiskerLeft_apply]
      rw [Eq.symm (FunctorToTypes.naturality G H f g.down.down Gc)]
  }
  counit := { app := fun G ↦ homEquiv_invFun (𝟙 _) }

end
