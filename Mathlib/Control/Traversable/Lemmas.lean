/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Applicative
import Mathlib.Control.Traversable.Basic

/-!
# Traversing collections

This file proves basic properties of traversable and applicative functors and defines
`PureTransformation F`, the natural applicative transformation from the identity functor to `F`.

## References

Inspired by [The Essence of the Iterator Pattern][gibbons2009].
-/


universe u

open LawfulTraversable

open Function hiding comp

open Functor

attribute [functor_norm] LawfulTraversable.naturality

attribute [simp] LawfulTraversable.id_traverse

namespace Traversable

variable {t : Type u → Type u}
variable [Traversable t] [LawfulTraversable t]
variable (F G : Type u → Type u)
variable [Applicative F] [LawfulApplicative F]
variable [Applicative G] [LawfulApplicative G]
variable {α β γ : Type u}
variable (g : α → F β)
variable (f : β → γ)

/-- The natural applicative transformation from the identity functor
to `F`, defined by `pure : Π {α}, α → F α`. -/
def PureTransformation :
    ApplicativeTransformation Id F where
  app := @pure F _
  preserves_pure' _ := rfl
  preserves_seq' f x := by
    simp only [map_pure, seq_pure]
    rfl

@[simp]
theorem pureTransformation_apply {α} (x : id α) : PureTransformation F x = pure x :=
  rfl

variable {F G}

theorem map_eq_traverse_id : map (f := t) f = Id.run ∘ traverse (pure ∘ f) :=
  funext fun y => (traverse_eq_map_id f y).symm

theorem map_traverse (x : t α) : map f <$> traverse g x = traverse (map f ∘ g) x := by
  rw [map_eq_traverse_id f]
  refine (comp_traverse (pure ∘ f) g x).symm.trans ?_
  congr; apply Comp.applicative_comp_id

theorem traverse_map (f : β → F γ) (g : α → β) (x : t α) :
    traverse f (g <$> x) = traverse (f ∘ g) x := by
  rw [@map_eq_traverse_id t _ _ _ _ g]
  refine (comp_traverse (G := Id) f (pure ∘ g) x).symm.trans ?_
  congr; apply Comp.applicative_id_comp

theorem pure_traverse (x : t α) : traverse pure x = (pure x : F (t α)) := by
  have : traverse pure x = pure (traverse (m := Id) pure x) :=
      (naturality (PureTransformation F) pure x).symm
  rwa [id_traverse] at this

theorem id_sequence (x : t α) : sequence (f := Id) (pure <$> x) = pure x := by
  simp [sequence, traverse_map, id_traverse]

theorem comp_sequence (x : t (F (G α))) :
    sequence (Comp.mk <$> x) = Comp.mk (sequence <$> sequence x) := by
  simp only [sequence, traverse_map, id_comp]; rw [← comp_traverse]; simp [map_id]

theorem naturality' (η : ApplicativeTransformation F G) (x : t (F α)) :
    η (sequence x) = sequence (@η _ <$> x) := by simp [sequence, naturality, traverse_map]

@[functor_norm]
theorem traverse_id : traverse pure = (pure : t α → Id (t α)) := by
  ext
  exact id_traverse _

@[functor_norm]
theorem traverse_comp (g : α → F β) (h : β → G γ) :
    traverse (Comp.mk ∘ map h ∘ g) =
      (Comp.mk ∘ map (traverse h) ∘ traverse g : t α → Comp F G (t γ)) := by
  ext
  exact comp_traverse _ _ _

theorem traverse_eq_map_id' (f : β → γ) :
    traverse (m := Id) (pure ∘ f) = pure ∘ (map f : t β → t γ) := by
  ext
  exact traverse_eq_map_id _ _

-- @[functor_norm]
theorem traverse_map' (g : α → β) (h : β → G γ) :
    traverse (h ∘ g) = (traverse h ∘ map g : t α → G (t γ)) := by
  ext
  rw [comp_apply, traverse_map]

theorem map_traverse' (g : α → G β) (h : β → γ) :
    traverse (map h ∘ g) = (map (map h) ∘ traverse g : t α → G (t γ)) := by
  ext
  rw [comp_apply, map_traverse]

theorem naturality_pf (η : ApplicativeTransformation F G) (f : α → F β) :
    traverse (@η _ ∘ f) = @η _ ∘ (traverse f : t α → F (t β)) := by
  ext
  rw [comp_apply, naturality]

end Traversable
