/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Bitraversable.Lemmas
import Mathlib.Control.Traversable.Lemmas

#align_import control.bitraversable.instances from "leanprover-community/mathlib"@"1e7f6b9a746d445350890f3ad5236f3fc686c103"

/-!
# Bitraversable instances

This file provides `Bitraversable` instances for concrete bifunctors:
* `Prod`
* `Sum`
* `Functor.Const`
* `flip`
* `Function.bicompl`
* `Function.bicompr`

## References

* Hackage: <https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable functor bifunctor applicative
-/


universe u v w

variable {t : Type u → Type u → Type u} [Bitraversable t]

section

variable {F : Type u → Type u} [Applicative F]

/-- The bitraverse function for `α × β`. -/
def Prod.bitraverse {α α' β β'} (f : α → F α') (f' : β → F β') : α × β → F (α' × β')
  | (x, y) => Prod.mk <$> f x <*> f' y
#align prod.bitraverse Prod.bitraverse

instance : Bitraversable Prod where bitraverse := @Prod.bitraverse

instance : LawfulBitraversable Prod := by
  constructor <;> intros <;> casesm _ × _ <;>
    simp [bitraverse, Prod.bitraverse, functor_norm] <;> rfl

open Functor

/-- The bitraverse function for `α ⊕ β`. -/
def Sum.bitraverse {α α' β β'} (f : α → F α') (f' : β → F β') : Sum α β → F (Sum α' β')
  | Sum.inl x => Sum.inl <$> f x
  | Sum.inr x => Sum.inr <$> f' x
#align sum.bitraverse Sum.bitraverse

instance : Bitraversable Sum where bitraverse := @Sum.bitraverse

instance : LawfulBitraversable Sum := by
  constructor <;> intros <;> casesm _ ⊕ _ <;>
    simp [bitraverse, Sum.bitraverse, functor_norm] <;> rfl


set_option linter.unusedVariables false in
/-- The bitraverse function for `Const`. It throws away the second map. -/
@[nolint unusedArguments]
def Const.bitraverse {F : Type u → Type u} [Applicative F] {α α' β β'} (f : α → F α')
    (f' : β → F β') : Const α β → F (Const α' β') :=
  f
#align const.bitraverse Const.bitraverse

instance Bitraversable.const : Bitraversable Const where bitraverse := @Const.bitraverse
#align bitraversable.const Bitraversable.const

instance LawfulBitraversable.const : LawfulBitraversable Const := by
  constructor <;> intros <;> simp [bitraverse, Const.bitraverse, functor_norm] <;> rfl
#align is_lawful_bitraversable.const LawfulBitraversable.const

/-- The bitraverse function for `flip`. -/
nonrec def flip.bitraverse {α α' β β'} (f : α → F α') (f' : β → F β') :
    flip t α β → F (flip t α' β') :=
  (bitraverse f' f : t β α → F (t β' α'))
#align flip.bitraverse flip.bitraverse

instance Bitraversable.flip : Bitraversable (flip t) where bitraverse := @flip.bitraverse t _
#align bitraversable.flip Bitraversable.flip

open LawfulBitraversable

instance LawfulBitraversable.flip [LawfulBitraversable t] : LawfulBitraversable (flip t) := by
  constructor <;> intros <;> casesm LawfulBitraversable t <;> apply_assumption only [*]
#align is_lawful_bitraversable.flip LawfulBitraversable.flip

open Bitraversable Functor

instance (priority := 10) Bitraversable.traversable {α} : Traversable (t α) where
  traverse := @tsnd t _ _
#align bitraversable.traversable Bitraversable.traversable

instance (priority := 10) Bitraversable.isLawfulTraversable [LawfulBitraversable t] {α} :
    LawfulTraversable (t α) := by
  constructor <;> intros <;>
    simp [traverse, comp_tsnd, functor_norm]
  · simp only [tsnd_eq_snd_id, Id.pure_eq]; rfl
  · simp [tsnd, binaturality, Function.comp, functor_norm]
#align bitraversable.is_lawful_traversable Bitraversable.isLawfulTraversable

end

open Bifunctor Traversable LawfulTraversable LawfulBitraversable

open Function (bicompl bicompr)

section Bicompl

variable (F G : Type u → Type u) [Traversable F] [Traversable G]

/-- The bitraverse function for `bicompl`. -/
nonrec def Bicompl.bitraverse {m} [Applicative m] {α β α' β'} (f : α → m β) (f' : α' → m β') :
    bicompl t F G α α' → m (bicompl t F G β β') :=
  (bitraverse (traverse f) (traverse f') : t (F α) (G α') → m _)
#align bicompl.bitraverse Bicompl.bitraverse

instance : Bitraversable (bicompl t F G) where bitraverse := @Bicompl.bitraverse t _ F G _ _

instance [LawfulTraversable F] [LawfulTraversable G] [LawfulBitraversable t] :
    LawfulBitraversable (bicompl t F G) := by
  constructor <;> intros <;>
    simp [bitraverse, Bicompl.bitraverse, bimap, traverse_id, bitraverse_id_id, comp_bitraverse,
      functor_norm]
  · simp [traverse_eq_map_id', bitraverse_eq_bimap_id]
  · dsimp only [bicompl]
    simp [binaturality, naturality_pf]

end Bicompl

section Bicompr

variable (F : Type u → Type u) [Traversable F]

/-- The bitraverse function for `bicompr`. -/
nonrec def Bicompr.bitraverse {m} [Applicative m] {α β α' β'} (f : α → m β) (f' : α' → m β') :
    bicompr F t α α' → m (bicompr F t β β') :=
  (traverse (bitraverse f f') : F (t α α') → m _)
#align bicompr.bitraverse Bicompr.bitraverse

instance : Bitraversable (bicompr F t) where bitraverse := @Bicompr.bitraverse t _ F _

instance [LawfulTraversable F] [LawfulBitraversable t] : LawfulBitraversable (bicompr F t) := by
  constructor <;> intros <;>
    simp [bitraverse, Bicompr.bitraverse, bitraverse_id_id, functor_norm]
  · simp only [bitraverse_eq_bimap_id', traverse_eq_map_id', Function.comp_apply, Id.pure_eq]; rfl
  · dsimp only [bicompr]
    simp [naturality, binaturality']

end Bicompr
