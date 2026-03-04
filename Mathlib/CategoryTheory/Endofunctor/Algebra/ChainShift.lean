/-
Copyright (c) 2026 Larsen Close. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Larsen Close
-/
module

public import Mathlib.CategoryTheory.Endofunctor.Algebra.InitialChain
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Preserves.Basic

/-!
# Shifted chain colimit equivalence

Given a cocone over the initial chain `⊥ → F(⊥) → F²(⊥) → ⋯` with colimit `L`,
we construct a cocone over the "shifted" chain `F(⊥) → F²(⊥) → F³(⊥) → ⋯`
(equivalently, the composite functor `initialChain F ⋙ F`) with the same point `L`.

The key result is that if the original cocone is a colimit, then the shifted cocone
is also a colimit. This is the foundation for constructing the Adamek algebra.

## Main definitions

- `CategoryTheory.Endofunctor.shiftCocone` : shifted cocone from a cocone over the initial chain
- `CategoryTheory.Endofunctor.extendCocone` : extend a cocone over the shifted chain to the full
  chain

## Main results

- `CategoryTheory.Endofunctor.shiftCoconeIsColimit` : the shifted cocone is a colimit when the
  original is

## References

- [J. Adamek, *Free algebras and automata realizations in the language of categories and
  functors*][adamek1974]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor

universe v u

variable {C : Type u} [Category.{v} C]
variable (F : C ⥤ C) [HasInitial C]

/-- Given a cocone over the initial chain with point `L`, construct a cocone
over `initialChain F ⋙ F` (the shifted chain) with the same point `L`.
The legs are the original cocone legs shifted by one: `ι_{n+1}` for each `n`. -/
noncomputable def shiftCocone (c : Cocone (initialChain F)) :
    Cocone (initialChain F ⋙ F) where
  pt := c.pt
  ι :=
  { app := fun n => c.ι.app (n + 1)
    naturality := by
      intro m n α
      simp only [Functor.comp_obj, Functor.comp_map, Functor.const_obj_obj,
        Functor.const_obj_map, Category.comp_id]
      have hle := leOfHom α
      rw [show (initialChain F).map α = (initialChain F).map (homOfLE hle) from
        congr_arg _ (Subsingleton.elim _ _)]
      rw [← initialChain_map_succ_eq F hle]
      exact c.w (homOfLE (Nat.succ_le_succ hle)) }

@[simp]
lemma shiftCocone_ι_app (c : Cocone (initialChain F)) (n : ℕ) :
    (shiftCocone F c).ι.app n = c.ι.app (n + 1) := rfl

/-- Extend a cocone over the shifted chain to one over the full initial chain,
by adding `initial.to` as the zeroth leg. -/
noncomputable def extendCocone (s : Cocone (initialChain F ⋙ F)) :
    Cocone (initialChain F) where
  pt := s.pt
  ι :=
  { app := fun n =>
      match n with
      | 0 => initial.to s.pt
      | n + 1 => s.ι.app n
    naturality := by
      intro m n α
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
      match m, n with
      | 0, 0 =>
        rw [show α = 𝟙 _ from Subsingleton.elim _ _, Functor.map_id, Category.id_comp]
      | 0, (n + 1) =>
        exact initial.hom_ext _ _
      | (m + 1), (n + 1) =>
        have hle := Nat.le_of_succ_le_succ (leOfHom α)
        rw [show (initialChain F).map α =
          (initialChain F).map (homOfLE (Nat.succ_le_succ hle)) from
          congr_arg _ (Subsingleton.elim _ _)]
        rw [initialChain_map_succ_eq F hle]
        have := s.w (homOfLE hle)
        simp only [Functor.comp_obj, Functor.comp_map, Functor.const_obj_obj] at this
        exact this }

/-- If `c` is a colimit cocone for the initial chain, then `shiftCocone F c` is a
colimit cocone for `initialChain F ⋙ F`. -/
noncomputable def shiftCoconeIsColimit (c : Cocone (initialChain F))
    (hc : IsColimit c) : IsColimit (shiftCocone F c) where
  desc s := hc.desc (extendCocone F s)
  fac s n := by
    simp only [shiftCocone_ι_app]
    exact hc.fac (extendCocone F s) (n + 1)
  uniq s g hg := by
    apply hc.uniq (extendCocone F s)
    intro n
    match n with
    | 0 => exact initial.hom_ext _ _
    | n + 1 => exact hg n

end CategoryTheory.Endofunctor
