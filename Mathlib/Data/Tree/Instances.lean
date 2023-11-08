/-
Copyright (c) 2023 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.Data.Tree.Defs
import Mathlib.Control.Traversable.Basic

namespace Tree

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

instance : Inhabited (Tree α) := ⟨nil⟩

@[simp] theorem default_def {α} : (default : Tree α) = nil := rfl

instance : Pure Tree := ⟨Tree.ret⟩

@[simp] theorem pure_def {α} : (pure : α → Tree α) = Tree.ret := rfl

instance : Functor Tree where
  map := Tree.map

@[simp] theorem map_id : ∀ (t : Tree α), map id t = t
  | nil => rfl
  | node a l r => congr_arg₂ (node a) (map_id l) (map_id r)

@[simp] theorem map_map (g : β → γ) (f : α → β)
  : ∀ (t : Tree α), map g (map f t) = map (g ∘ f) t
  | nil => rfl
  | node a l r => congr_arg₂ (node (g (f a))) (map_map g f l) (map_map g f r)

instance : LawfulFunctor Tree where
  map_const := by intros; dsimp only [Functor.mapConst, Functor.map]
  id_map := map_id
  comp_map g f t := Eq.symm $ map_map f g t

@[simp]
theorem fmap_def {α β} {t : Tree α} (f : α → β) : f <$> t = t.map f := rfl

instance : Traversable Tree := ⟨Tree.traverse⟩

@[simp]
theorem id_traverse : ∀ (t : Tree α), Tree.traverse (pure : α → Id α) t = t
  | nil => rfl
  | node a l r => congr_arg₂ (node a) (id_traverse l) (id_traverse r)

@[simp]
theorem comp_traverse {F G} [Applicative F] [Applicative G]
  [LawfulApplicative F] [LawfulApplicative G] {α β γ}
  (f : β → F γ) (g : α → G β)
  : ∀ (t : Tree α), Tree.traverse (Functor.Comp.mk ∘ Functor.map f ∘ g) t
                  = Functor.Comp.mk (Tree.traverse f <$> Tree.traverse g t)
  | nil => Eq.symm $ map_pure _ _
  | node a l r => by
    rw [traverse, traverse, map_seq, map_seq,
        comp_traverse f g l, comp_traverse f g r]
    simp [functor_norm, Functor.Comp.instApplicativeComp,
          Functor.Comp.map, Functor.Comp.seq, Functor.Comp.mk]
    exact rfl

@[simp]
theorem traverse_eq_map_id (f : α → β)
  : ∀ (t : Tree α), Tree.traverse (@pure Id _ β ∘ f) t = id.mk (Tree.map f t)
  | nil => rfl
  | node a l r => congr_arg₂ (fun l' r' => node <$> pure (f a) <*> l' <*> r')
                             (traverse_eq_map_id f l) (traverse_eq_map_id f r)

instance : LawfulTraversable Tree where
  id_traverse := Tree.id_traverse
  comp_traverse := Tree.comp_traverse
  traverse_eq_map_id := Tree.traverse_eq_map_id
  naturality := by
    intros F G _ _ _ _ η α β f t
    induction' t with a l r ihₗ ihᵣ
    . rw [Traversable.traverse, instTraversableTree]
      simp only [Tree.traverse]
      rw [ApplicativeTransformation.preserves_pure']
    . rw [Traversable.traverse, instTraversableTree]
      simp only [Tree.traverse]
      rw [ApplicativeTransformation.preserves_seq',
          ApplicativeTransformation.preserves_seq']
      simp only [ApplicativeTransformation.app_eq_coe, Function.comp_apply]
      rw [ApplicativeTransformation.preserves_map]
      congr <;> ext <;> assumption

end Tree
