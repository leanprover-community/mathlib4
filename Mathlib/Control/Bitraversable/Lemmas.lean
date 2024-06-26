/-
Copyright (c) 2019 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Control.Bitraversable.Basic

#align_import control.bitraversable.lemmas from "leanprover-community/mathlib"@"58581d0fe523063f5651df0619be2bf65012a94a"

/-!
# Bitraversable Lemmas

## Main definitions
  * tfst - traverse on first functor argument
  * tsnd - traverse on second functor argument

## Lemmas

Combination of
  * bitraverse
  * tfst
  * tsnd

with the applicatives `id` and `comp`

## References

 * Hackage: <https://hackage.haskell.org/package/base-4.12.0.0/docs/Data-Bitraversable.html>

## Tags

traversable bitraversable functor bifunctor applicative


-/


universe u

variable {t : Type u → Type u → Type u} [Bitraversable t]
variable {β : Type u}

namespace Bitraversable

open Functor LawfulApplicative

variable {F G : Type u → Type u} [Applicative F] [Applicative G]

/-- traverse on the first functor argument -/
abbrev tfst {α α'} (f : α → F α') : t α β → F (t α' β) :=
  bitraverse f pure
#align bitraversable.tfst Bitraversable.tfst

/-- traverse on the second functor argument -/
abbrev tsnd {α α'} (f : α → F α') : t β α → F (t β α') :=
  bitraverse pure f
#align bitraversable.tsnd Bitraversable.tsnd

variable [LawfulBitraversable t] [LawfulApplicative F] [LawfulApplicative G]

@[higher_order tfst_id]
theorem id_tfst : ∀ {α β} (x : t α β), tfst (F := Id) pure x = pure x :=
  id_bitraverse
#align bitraversable.id_tfst Bitraversable.id_tfst

@[higher_order tsnd_id]
theorem id_tsnd : ∀ {α β} (x : t α β), tsnd (F := Id) pure x = pure x :=
  id_bitraverse
#align bitraversable.id_tsnd Bitraversable.id_tsnd

@[higher_order tfst_comp_tfst]
theorem comp_tfst {α₀ α₁ α₂ β} (f : α₀ → F α₁) (f' : α₁ → G α₂) (x : t α₀ β) :
    Comp.mk (tfst f' <$> tfst f x) = tfst (Comp.mk ∘ map f' ∘ f) x := by
  rw [← comp_bitraverse]
  simp only [Function.comp, tfst, map_pure, Pure.pure]
#align bitraversable.comp_tfst Bitraversable.comp_tfst

@[higher_order tfst_comp_tsnd]
theorem tfst_tsnd {α₀ α₁ β₀ β₁} (f : α₀ → F α₁) (f' : β₀ → G β₁) (x : t α₀ β₀) :
    Comp.mk (tfst f <$> tsnd f' x)
      = bitraverse (Comp.mk ∘ pure ∘ f) (Comp.mk ∘ map pure ∘ f') x := by
  rw [← comp_bitraverse]
  simp only [Function.comp, map_pure]
#align bitraversable.tfst_tsnd Bitraversable.tfst_tsnd

@[higher_order tsnd_comp_tfst]
theorem tsnd_tfst {α₀ α₁ β₀ β₁} (f : α₀ → F α₁) (f' : β₀ → G β₁) (x : t α₀ β₀) :
    Comp.mk (tsnd f' <$> tfst f x)
      = bitraverse (Comp.mk ∘ map pure ∘ f) (Comp.mk ∘ pure ∘ f') x := by
  rw [← comp_bitraverse]
  simp only [Function.comp, map_pure]
#align bitraversable.tsnd_tfst Bitraversable.tsnd_tfst

@[higher_order tsnd_comp_tsnd]
theorem comp_tsnd {α β₀ β₁ β₂} (g : β₀ → F β₁) (g' : β₁ → G β₂) (x : t α β₀) :
    Comp.mk (tsnd g' <$> tsnd g x) = tsnd (Comp.mk ∘ map g' ∘ g) x := by
  rw [← comp_bitraverse]
  simp only [Function.comp, map_pure]
  rfl
#align bitraversable.comp_tsnd Bitraversable.comp_tsnd

open Bifunctor

-- Porting note: This private theorem wasn't needed
-- private theorem pure_eq_id_mk_comp_id {α} : pure = id.mk ∘ @id α := rfl

open Function

@[higher_order]
theorem tfst_eq_fst_id {α α' β} (f : α → α') (x : t α β) :
    tfst (F := Id) (pure ∘ f) x = pure (fst f x) := by
  apply bitraverse_eq_bimap_id
#align bitraversable.tfst_eq_fst_id Bitraversable.tfst_eq_fst_id

@[higher_order]
theorem tsnd_eq_snd_id {α β β'} (f : β → β') (x : t α β) :
    tsnd (F := Id) (pure ∘ f) x = pure (snd f x) := by
  apply bitraverse_eq_bimap_id
#align bitraversable.tsnd_eq_snd_id Bitraversable.tsnd_eq_snd_id

attribute [functor_norm] comp_bitraverse comp_tsnd comp_tfst tsnd_comp_tsnd tsnd_comp_tfst
  tfst_comp_tsnd tfst_comp_tfst bitraverse_comp bitraverse_id_id tfst_id tsnd_id

end Bitraversable
