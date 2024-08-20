import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone

universe u v

open CategoryTheory

variable {C : Type u} [Category.{v, u} C]

structure leftLiftingData {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) where
  lift : X ⟶ Y
  w : lift ≫ g = f

@[simp]
lemma leftLiftingData.apply_w  {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z} (l :leftLiftingData f g) :
  l.lift ≫ g = f := l.w


def forkConeToPullbackCone.π.app {X Y Z : C} {f e : X ⟶ Z} {g : Y ⟶ Z} (l : leftLiftingData e g)
  (s : Limits.Fork f e) (j : Limits.WalkingCospan) :
  ((Functor.const Limits.WalkingCospan).obj s.pt).obj j ⟶ (Limits.cospan f g).obj j :=
    match j with
    | none => s.π.app Limits.WalkingParallelPair.one
    | some .left => s.ι
    | some .right => s.ι ≫ l.lift

@[simp]
lemma forkConeToPullbackCone.π.app_none {X Y Z : C} {f e : X ⟶ Z} {g : Y ⟶ Z}
  (l : leftLiftingData e g) (s : Limits.Fork f e) :
    app l s none = s.π.app Limits.WalkingParallelPair.one := rfl

@[simp]
lemma forkConeToPullbackCone.π.app_some_left {X Y Z : C} {f e : X ⟶ Z} {g : Y ⟶ Z}
  (l : leftLiftingData e g) (s : Limits.Fork f e) :
    app l s (some .left) =  s.ι := rfl

@[simp]
lemma forkConeToPullbackCone.π.app_some_righ {X Y Z : C} {f e : X ⟶ Z} {g : Y ⟶ Z}
  (l : leftLiftingData e g) (s : Limits.Fork f e) :
    app l s (some .right) =  s.ι ≫ l.lift := rfl

def forkConeToPullbackCone.π.naturality {X Y Z : C} {f e : X ⟶ Z} {g : Y ⟶ Z}
  (l : leftLiftingData e g) (s : Limits.Fork f e) {j₁ j₂ : Limits.WalkingCospan} (h : j₁ ⟶ j₂) :
  ((Functor.const Limits.WalkingCospan).obj s.pt).map h ≫ (fun x ↦ π.app l s x) j₂ =
    (fun x ↦ π.app l s x) j₁ ≫ (Limits.cospan f g).map h := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
    cases h with
    | id =>
      simp only [Limits.WidePullbackShape.hom_id, Functor.map_id, Category.comp_id]
    | _ j =>
      simp only [Limits.cospan_one, app_none, Limits.Fork.app_one_eq_ι_comp_left,
        Functor.const_obj_obj, Limits.parallelPair_obj_zero]
      cases j with
      | left =>
        simp only [Limits.cospan_left, app_some_left, Limits.cospan_map_inl]
      | right =>
        simp only [Limits.cospan_right, app_some_righ, Functor.const_obj_obj,
          Limits.parallelPair_obj_zero, Limits.cospan_map_inr, Category.assoc,
          leftLiftingData.apply_w, ← Limits.Fork.app_one_eq_ι_comp_right,
          Limits.Fork.app_one_eq_ι_comp_left, Functor.const_obj_obj, Limits.parallelPair_obj_zero]

def forkConeToPullbackCone.π {X Y Z : C} {f e : X ⟶ Z} {g : Y ⟶ Z}
  (s : Limits.Fork f e) (l : leftLiftingData e g) :
  (Functor.const Limits.WalkingCospan).obj s.pt ⟶ Limits.cospan f g where
    app _ := forkConeToPullbackCone.π.app l _ _
    naturality _ _ _ := forkConeToPullbackCone.π.naturality l s _

def forkConeToPullbackCone {X Y Z : C} {f e : X ⟶ Z} {g : Y ⟶ Z}
  (s : Limits.Fork f e) (l : leftLiftingData e g) : Limits.PullbackCone f g where
    pt := s.pt
    π := forkConeToPullbackCone.π s l


-- def pullbackConeToForkCone {X Y Z : C} {f e : X ⟶ Z} {g : Y ⟶ Z}
--   (s : Limits.PullbackCone f g) (l : leftLiftingData f e g) :


-- def forkConeToPullbackCone
--   (c : Limits.Cone (Limits.parallelPair (Limits.terminal.from X ≫ s.map) (s.c f))) :
--   CategoryTheory.Limits.PullbackCone (s.c f) s.map where
--     pt := c.pt
--     π := by

--       sorry
