import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Whiskering

universe v w w' u

open CategoryTheory

namespace Grp

-- The universe lift functor for groups is faithful. -/
@[to_additive
  "The universe lift functor for additive groups is faithful."]
instance : uliftFunctor.{u, v}.Faithful where
  map_injective := by
    intro X Y f g
    intro heq
    ext a
    apply_fun (fun h ↦ h {down := a}) at heq
    change Equiv.ulift.symm (f a) = Equiv.ulift.symm (g a) at heq
    exact (EmbeddingLike.apply_eq_iff_eq _).mp heq

-- The universe lift functor for groups is full. -/
@[to_additive
  "The universe lift functor for additive groups is full."]
instance : uliftFunctor.{u, v}.Full where
  map_surjective {X Y} f :=
    ⟨ofHom (MonoidHom.mk (OneHom.mk (fun x => (f (ULift.up x)).down)
          (by change (f 1).down = ?_; rw [f.map_one]; rfl))
          (fun _ _ ↦ by simp only [uliftFunctor_obj, coe_of];
                        change (f (_ * _)).down = _; rw [f.map_mul]; rfl)), rfl⟩

def yoneda_comp_uliftFunctor (X : Grp.{u}) :
    yoneda.obj X ⋙ CategoryTheory.uliftFunctor.{v,u} ≅ Grp.uliftFunctor.{v,u}.op ⋙
    yoneda.obj (Grp.uliftFunctor.{v,u}.obj X) := sorry

/- Doesn't type check (need to apply `uliftFunctor` on `Cᵒᵖ` too).
def yoneda_comp_uliftFunctor :
    yoneda.{u} ⋙ ((whiskeringRight (Grp.{u})ᵒᵖ _ _).obj CategoryTheory.uliftFunctor.{v,u}) ≅
    Grp.uliftFunctor.{u,v} ⋙ yoneda (C := Grp.{u}) := sorry
-/

end Grp

namespace CommGrp

-- The universe lift functor for commutative groups is faithful. -/
@[to_additive
  "The universe lift functor for commutative additive groups is faithful."]
instance : uliftFunctor.{u, v}.Faithful where
  map_injective := by
    intro X Y f g
    intro heq
    ext a
    apply_fun (fun h ↦ h {down := a}) at heq
    change Equiv.ulift.symm (f a) = Equiv.ulift.symm (g a) at heq
    exact (EmbeddingLike.apply_eq_iff_eq _).mp heq

-- The universe lift functor for commutative groups is full. -/
@[to_additive
  "The universe lift functor for commutative additive groups is full."]
instance : uliftFunctor.{u, v}.Full where
  map_surjective {X Y} f :=
    ⟨ofHom (MonoidHom.mk (OneHom.mk (fun x => (f (ULift.up x)).down)
          (by change (f 1).down = ?_; rw [f.map_one]; rfl))
          (fun _ _ ↦ by simp only [uliftFunctor_obj, coe_of];
                        change (f (_ * _)).down = _; rw [f.map_mul]; rfl)), rfl⟩

def yoneda_comp_uliftFunctor (X : CommGrp.{u}) :
    yoneda.obj X ⋙ CategoryTheory.uliftFunctor.{v,u} ≅ CommGrp.uliftFunctor.{v,u}.op ⋙
    yoneda.obj (CommGrp.uliftFunctor.{v,u}.obj X) := sorry

end CommGrp

#min_imports
