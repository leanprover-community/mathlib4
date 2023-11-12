/-
Copyright (c) 2023 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
import Mathlib.Data.Tree.Defs
import Mathlib.Control.Fold
import Mathlib.Control.Bitraversable.Basic

namespace Tree

universe u v w

variable (o : Tree.VisitOrder) {α : Type u} {β : Type v} {γ : Type w}

instance : Inhabited (Tree α) := ⟨nil⟩

@[simp] theorem default_def {α} : (default : Tree α) = nil := rfl

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

def depthFirstTraversable : Traversable Tree := ⟨depthFirst o⟩

@[simp]
theorem id_traverse (t : Tree α) : depthFirst o (m := Id) pure t = t := by
  dsimp only [depthFirst]
  induction' t with a l r ihₗ ihᵣ; exact rfl
  dsimp [depthFirst.go]
  rw [ihₗ, ihᵣ]
  cases o <;> exact rfl

@[simp]
theorem comp_traverse {F G} [Applicative F] [Applicative G]
  [LawfulApplicative F] [LawfulApplicative G] {α β γ} (f : β → F γ) (g : α → G β)
  (t : Tree α) : depthFirst o (Functor.Comp.mk ∘ Functor.map f ∘ g) t
               = Functor.Comp.mk (depthFirst o f <$> depthFirst o g t) := by
  dsimp only [depthFirst]
  induction' t with a l r ihₗ ihᵣ
  . exact Eq.symm $ map_pure _ _
  . dsimp [depthFirst.go]
    rw [ihₗ, ihᵣ]
    generalize h1 : depthFirst.go (@depthFirst.branch_step o) f = e1
    generalize h2 : depthFirst.go (@depthFirst.branch_step o) g = e2
    cases o <;> dsimp only [depthFirst.branch_step] <;> subst h1 <;> subst h2
            <;> rw [map_seq, map_seq]
            <;> simp [functor_norm, Functor.Comp.instApplicativeComp,
                      Functor.Comp.map, Functor.Comp.seq, Functor.Comp.mk]
            <;> exact rfl

@[simp]
theorem traverse_eq_map_id (f : α → β) (t : Tree α)
  : depthFirst o (@pure Id _ β ∘ f) t = id.mk (map f t) := by
  dsimp only [depthFirst]
  induction' t with a l r ihₗ ihᵣ; exact rfl
  dsimp [depthFirst.go]
  rw [ihₗ, ihᵣ]
  cases o <;> exact rfl

def depthFirstLawfulTraversable : @LawfulTraversable Tree (depthFirstTraversable o) := by
  letI := depthFirstTraversable o
  refine ⟨Tree.id_traverse o, Tree.comp_traverse o, Tree.traverse_eq_map_id o, ?_⟩
  intros F G _ _ _ _ η α β f t
  dsimp only [depthFirstTraversable, depthFirst]
  induction' t with a l r ihₗ ihᵣ <;> dsimp only [depthFirst.go]
  . rw [ApplicativeTransformation.preserves_pure']
  . generalize h : depthFirst.go (@depthFirst.branch_step o) f = e
    cases o <;> dsimp only [depthFirst.branch_step] <;> subst h
    <;> simp only [ApplicativeTransformation.preserves_seq, Function.comp_apply,
                   ApplicativeTransformation.preserves_map,
                   ApplicativeTransformation.app_eq_coe, ihₗ, ihᵣ]
    <;> exact rfl

@[inline]
def foldMap.branch_step {ω : Type u} [Mul ω] : ω → ω → ω → ω :=
  match o with
  | VisitOrder.Node1st => fun x y z => x * y * z
  | VisitOrder.Node2nd => fun x y z => y * x * z
  | VisitOrder.Node3rd => fun x y z => y * z * x

@[simp]
lemma foldMap_def {ω : Type u} [One ω] [Mul ω] (f : α → ω) (t : Tree α)
  : @Traversable.foldMap _ (depthFirstTraversable o) _ _ _ _ f t
    = Tree.rec (1 : ω) (fun a _ _ => foldMap.branch_step o (f a)) t := by
  induction' t with a l r ihₗ ihᵣ; exact rfl
  dsimp only []
  rw [← ihₗ, ← ihᵣ]
  cases o <;> exact rfl

@[simp]
lemma toList_def (t : Tree α)
  : @Traversable.toList _ _ (depthFirstTraversable o) t
  = Tree.rec [] (fun a _ _ => @foldMap.branch_step o _ ⟨List.append⟩ [a]) t := by
    rw [@Traversable.toList_spec _ _ (depthFirstTraversable o)
                                     (depthFirstLawfulTraversable o),
        Tree.foldMap_def]
    induction' t with x l r ihₗ ihᵣ; exact rfl
    cases o <;> simp [*] <;> exact rfl

end Tree

namespace Tree'

-- universe u v w

variable (o : Tree.VisitOrder) {L : Type _} {N : Type _}
  {L' : Type _} {N' : Type _} {L'' : Type _} {N'' : Type _}

instance [Inhabited L] : Inhabited (Tree' L N) := ⟨leaf default⟩

@[simp]
theorem default_def [Inhabited L] : (default : Tree' L N) = leaf default := rfl

instance : Bifunctor Tree' where
  bimap := Tree'.bimap

@[simp] theorem id_bimap : ∀ (t : Tree' L N), bimap id id t = t
  | leaf _ => rfl
  | branch y l r => congr_arg₂ (branch y) (id_bimap l) (id_bimap r)

@[simp] theorem bimap_bimap (f₁ : L → L') (f₂ : L' → L'') (g₁ : N → N') (g₂ : N' → N'')
  : ∀ (t : Tree' L N), bimap f₂ g₂ (bimap f₁ g₁ t) = bimap (f₂ ∘ f₁) (g₂ ∘ g₁) t
  | leaf _ => rfl
  | branch y l r => congr_arg₂ (branch (g₂ (g₁ y))) (bimap_bimap f₁ f₂ g₁ g₂ l)
                                                    (bimap_bimap f₁ f₂ g₁ g₂ r)

instance : LawfulBifunctor Tree' where
  id_bimap := id_bimap
  bimap_bimap := bimap_bimap

@[simp]
theorem bimap_def {t : Tree' L N} (f : L → L') (g : N → N')
  : bimap f g t = t.bimap f g := rfl

def depthFirstBitraversable : Bitraversable Tree' := ⟨depthFirst o⟩

@[simp]
theorem id_bitraverse (t : Tree' L N) : depthFirst o (m := Id) pure pure t = t := by
  dsimp only [depthFirst]
  induction' t with _ y l r ihₗ ihᵣ; exact rfl
  dsimp [depthFirst.go]
  rw [ihₗ, ihᵣ]
  cases o <;> exact rfl

open Functor (Comp map)

@[simp]
theorem comp_bitraverse.{u, v, w}
  {F : Type (max v u) → Type (max v u)} {G : Type (max v u) → Type w}
  [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G]
  {L N L' N' L'' N''}
  (f₂ : L' → F L'') (f₁ : N' → F N'') (g₂ : L → G L') (g₁ : N → G N') (t : Tree' L N)
  : @depthFirst.{u, v, w} o (Comp G F) _ _ _ _ _ (Comp.mk ∘ map f₂ ∘ g₂) (Comp.mk ∘ map f₁ ∘ g₁) t
    = Comp.mk (@Functor.map G _ _ _ (depthFirst o f₂ f₁) (depthFirst o g₂ g₁ t)) := by
  dsimp only [depthFirst]
  induction' t with _ y l r ihₗ ihᵣ
  . dsimp only [depthFirst.branch_step, depthFirst.go, Function.comp_apply]
    rw [← comp_map, Comp.map_mk, ← comp_map]
    exact rfl
  . dsimp [depthFirst.go]
    rw [ihₗ, ihᵣ]
    generalize h1 : depthFirst.go (@depthFirst.branch_step.{max u v, max u v, max u v} o) f₂ f₁ = e1
    generalize h2 : depthFirst.go (@depthFirst.branch_step.{u, v, w} o) g₂ g₁ = e2
    cases o <;> dsimp only [depthFirst.branch_step] <;> subst h1 <;> subst h2
            <;> simp only [Comp.instApplicativeComp, Comp.map, Comp.mk,
                           Comp.seq, Functor.map_map, seq_map_assoc, map_seq]
            <;> exact rfl

@[simp]
theorem bitraverse_eq_bimap_id (f : L → L') (g : N → N') (t : Tree' L N)
  : depthFirst o (m := Id) (pure ∘ f) (pure ∘ g) t = pure (bimap f g t) := by
  dsimp only [depthFirst]
  induction' t with x y l r ihₗ ihᵣ; exact rfl
  dsimp [depthFirst.go]
  rw [ihₗ, ihᵣ]
  cases o <;> exact rfl

def depthFirstLawfulTraversable.{u}
   : @LawfulBitraversable Tree' (depthFirstBitraversable.{u, u} o) := by
  letI := depthFirstBitraversable.{u, u} o
  refine ⟨Tree'.id_bitraverse.{u, u} o, Tree'.comp_bitraverse o,
          Tree'.bitraverse_eq_bimap_id o, ?_⟩

  intros F G _ _ _ _ η L N L' N' f g t
  dsimp only [depthFirstBitraversable, depthFirst]
  induction' t with x y l r ihₗ ihᵣ <;> dsimp only [depthFirst.go]
  . apply ApplicativeTransformation.preserves_map.{u, u, u}
  . generalize h : depthFirst.go.{u, u, u} (@depthFirst.branch_step.{u, u, u} o) f g = e1
    cases o <;> dsimp only [depthFirst.branch_step] <;> subst h
            <;> simp only [ApplicativeTransformation.preserves_seq, Function.comp_apply,
                          ApplicativeTransformation.preserves_map, inline,
                          ApplicativeTransformation.app_eq_coe, ihₗ, ihᵣ]
            <;> exact rfl

end Tree'
