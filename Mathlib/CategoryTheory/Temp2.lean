import Mathlib.CategoryTheory.Closed.Cartesian
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal

namespace CategoryTheory

universe w v u

open MonoidalCategory

variable {C : Type u} [Category.{v} C]

namespace FunctorToTypes

@[simp]
lemma whiskerLeft_app_apply (F : C ⥤ Type max u v w) {G H : C ⥤ Type max u v w} (g : G ⟶ H)
    {c : C} (x : (F ⊗ G).obj c) :
    (F ◁ g).app c x = ⟨x.1, g.app c x.2⟩ := rfl

@[simp]
lemma whiskerRight_app_apply {F G : C ⥤ Type max u v w} (f : F ⟶ G) (H : C ⥤ Type max u v w)
    {c : C} (x : (F ⊗ H).obj c) :
    (f ▷ H).app c x = ⟨f.app c x.1, x.2⟩ := rfl

def uliftFunctor : (C ⥤ Type v) ⥤ C ⥤ Type max u v w :=
  (whiskeringRight _ _ _).obj (CategoryTheory.uliftFunctor.{u, v} ⋙ CategoryTheory.uliftFunctor.{w, max u v})

@[simp]
lemma uliftFunctor_apply1 (f : C ⥤ Type v) :
    (uliftFunctor.obj f) = f ⋙ (CategoryTheory.uliftFunctor.{u, v} ⋙ CategoryTheory.uliftFunctor.{w, max u v}) := rfl

@[simp]
lemma uliftFunctor_apply2 (f : C ⥤ Type v) (c : C) :
    (uliftFunctor.obj f).obj c = (CategoryTheory.uliftFunctor.{w, max u v}).obj ((CategoryTheory.uliftFunctor.{u, v}).obj (f.obj c)) := rfl

def coyonedaLift {C : Type u} [Category.{v} C] : Cᵒᵖ ⥤ C ⥤ Type (max u v w) :=
    coyoneda ⋙ uliftFunctor.{w, v, u}

noncomputable section

def ihom (F G : C ⥤ Type max u v w) : C ⥤ Type max u v w where
  obj c := (coyonedaLift.obj (.op c)) ⊗ F ⟶ G
  map := fun f g ↦ coyonedaLift.map (.op f) ▷ F ≫ g

def rightAdj (F : C ⥤ Type max u v w) : (C ⥤ Type max u v w) ⥤ C ⥤ Type max u v w where
  obj G := ihom F G
  map f := { app := fun _ h ↦ h ≫ f }

def aux1 {F G H : C ⥤ Type max u v w} (f : F ⊗ G ⟶ H) (c : C) (Gc: G.obj c) :
    (ihom F H).obj c where
  app := fun d ⟨g, Fd⟩ ↦ f.app d (Fd, G.map g.down.down Gc)
  naturality a b h := by
    ext ⟨g, Fa⟩
    change f.app b (F.map h Fa, G.map ((coyonedaLift.obj (.op c)).map h g).down.down Gc) = _
    have := f.naturality h
    apply_fun (fun f ↦ f (Fa, G.map g.down.down Gc)) at this
    dsimp [coyonedaLift, uliftFunctor]
    aesop

def aux2 {F G H : C ⥤ Type max u v w} (f : F ⊗ G ⟶ H) : G ⟶ ihom F H where
  app c Gc := aux1 f c Gc
  naturality c d g := by
    ext Gc
    dsimp [rightAdj, ihom]
    ext e ⟨h, Fe⟩
    change f.app e (Fe, G.map h.down.down (G.map g Gc)) = f.app e (Fe, G.map (g ≫ h.down.down) Gc)
    simp only [coyoneda_obj_obj, FunctorToTypes.map_comp_apply]

def aux3 {F G H : C ⥤ Type max u v w} (f : G ⟶ ihom F H) : F ⊗ G ⟶ H where
  app c x := (f.app c x.2).app c (Equiv.ulift.symm (Equiv.ulift.symm (𝟙 c)), x.1)
  naturality c d g := by
    dsimp
    ext ⟨Fc, Gc⟩
    change (f.app d ((G.map g Gc))).app d (_, F.map g Fc) = H.map g ((f.app c Gc).app c (_, Fc))
    have b := f.naturality g
    apply_fun (fun f ↦ (f Gc).app d (Equiv.ulift.symm (Equiv.ulift.symm (𝟙 d)), F.map g Fc)) at b
    have a := (f.app c Gc).naturality g
    apply_fun (fun f ↦ f (Equiv.ulift.symm (Equiv.ulift.symm (𝟙 c)), Fc)) at a
    simp only [coyoneda_obj_obj, types_comp_apply] at a b
    rw [b, ← a]
    simp only [coyonedaLift, uliftFunctor, Functor.comp_obj, whiskeringRight_obj_obj, ihom,
      Functor.comp_map, whiskeringRight_obj_map, coyoneda_obj_obj, Equiv.ulift,
      Equiv.coe_fn_symm_mk, comp, whiskerRight_app_apply]
    suffices h : ((whiskerRight (coyoneda.map g.op) (CategoryTheory.uliftFunctor.{u, v}.comp CategoryTheory.uliftFunctor.{w, max u v}) ▷ F).app d ({ down := { down := 𝟙 d } }, F.map g Fc)) = (((coyoneda.obj { unop := c }).comp (CategoryTheory.uliftFunctor.{u, v}.comp CategoryTheory.uliftFunctor.{w, max u v}) ⊗ F).map g ({ down := { down := 𝟙 c } }, Fc)) by
      aesop
    simp only [Functor.comp_obj, coyoneda_obj_obj, whiskerRight_app_apply]
    change _ = (((coyoneda.obj { unop := c }).comp (CategoryTheory.uliftFunctor.{u, v}.comp CategoryTheory.uliftFunctor.{w, max u v})).map g { down := { down := 𝟙 c } }, F.map g Fc)
    simp only [Functor.comp_obj, coyoneda_obj_obj, whiskerRight_app_apply, Functor.comp_map,
      uliftFunctor_map, coyoneda_obj_map, Category.id_comp]
    sorry

@[ext]
lemma ext {F G : C ⥤ Type max u v w} {c : C} {f g : (ihom F G).obj c} :
    f.app = g.app → f = g := NatTrans.ext _ _

def adj (F : C ⥤ Type max u v w) : tensorLeft F ⊣ rightAdj F where
  homEquiv G H := {
    toFun := fun f ↦ aux2 f
    invFun := fun f ↦ aux3 f
    left_inv := fun f ↦ by
      ext c ⟨Fc, Gc⟩
      change f.app c (Fc, G.map (𝟙 _) Gc) = _
      aesop
    right_inv := fun f ↦ by
      dsimp [aux1, aux2, aux3]
      ext c Gc d ⟨g, Fd⟩
      have b := f.naturality g.down.down
      apply_fun (fun f ↦ (f Gc).app d (Equiv.ulift.symm (Equiv.ulift.symm (𝟙 d)), Fd)) at b
      dsimp at b
      rw [b]
      dsimp [rightAdj, ihom, coyonedaLift, uliftFunctor]
      sorry
      --simp only [Category.comp_id]
      --rfl
  }
  unit := {
    app := fun g ↦ aux2 (𝟙 _)
    naturality := fun G H f ↦ by
      ext c Gc
      change (aux1 (𝟙 (F ⊗ H)) c (f.app c Gc)) = ((rightAdj F).map (F ◁ f)).app c (aux1 (𝟙 (F ⊗ G)) c Gc)
      ext d ⟨g, Fd⟩
      change (Fd, H.map g.down.down (f.app c Gc)) = (F ◁ f).app d (Fd, G.map g.down.down Gc)
      simp only [coyoneda_obj_obj, whiskerLeft_app_apply]

      sorry
      --exact Eq.symm (FunctorToTypes.naturality G H f g.down.down Gc)
  }
  counit := { app := fun G ↦ aux3 (𝟙 _) }

end
