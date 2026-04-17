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

Given an initial object `X` and a cocone over the initial chain
`X → F(X) → F²(X) → ⋯` with colimit `L`, we construct a cocone over the
"shifted" chain (the composite functor `initialChain F hX ⋙ F`) with the
same point `L`.

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
variable (F : C ⥤ C) {X : C} (hX : IsInitial X)

/-- Given a cocone over the initial chain with point `L`, construct a cocone
over `initialChain F hX ⋙ F` (the shifted chain) with the same point `L`.
The legs are the original cocone legs shifted by one: `ι_{n+1}` for each `n`. -/
noncomputable def shiftCocone (c : Cocone (initialChain F hX)) :
    Cocone (initialChain F hX ⋙ F) where
  pt := c.pt
  ι := NatTrans.ofSequence
    (fun n => c.ι.app (n + 1))
    (fun n => by
      simp only [Functor.comp_obj, Functor.comp_map, Functor.const_obj_obj,
        Functor.const_obj_map, Category.comp_id]
      rw [← initialChain_map_succ_eq F hX (n.le_add_right 1)]
      exact c.w (homOfLE (Nat.succ_le_succ (n.le_add_right 1))))

@[simp]
lemma shiftCocone_ι_app (c : Cocone (initialChain F hX)) (n : ℕ) :
    (shiftCocone F hX c).ι.app n = c.ι.app (n + 1) := rfl

/-- Extend a cocone over the shifted chain to one over the full initial chain,
by adding `hX.to` as the zeroth leg. -/
noncomputable def extendCocone (s : Cocone (initialChain F hX ⋙ F)) :
    Cocone (initialChain F hX) where
  pt := s.pt
  ι := NatTrans.ofSequence
    (fun n => match n with
      | 0 => hX.to s.pt
      | n + 1 => s.ι.app n)
    (fun n => by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
      cases n with
      | zero => exact hX.hom_ext _ _
      | succ k =>
        rw [show (homOfLE ((k + 1).le_add_right 1) : (k + 1 : ℕ) ⟶ (k + 2 : ℕ)) =
            homOfLE (Nat.succ_le_succ (k.le_add_right 1)) from Subsingleton.elim _ _,
          initialChain_map_succ_eq F hX (k.le_add_right 1)]
        have := s.w (homOfLE (k.le_add_right 1))
        simp only [Functor.comp_obj, Functor.comp_map] at this
        exact this)

/-- If `c` is a colimit cocone for the initial chain, then `shiftCocone F hX c` is a
colimit cocone for `initialChain F hX ⋙ F`. -/
noncomputable def shiftCoconeIsColimit (c : Cocone (initialChain F hX))
    (hc : IsColimit c) : IsColimit (shiftCocone F hX c) where
  desc s := hc.desc (extendCocone F hX s)
  fac s n := by
    simp only [shiftCocone_ι_app]
    exact hc.fac (extendCocone F hX s) (n + 1)
  uniq s g hg := by
    apply hc.uniq (extendCocone F hX s)
    intro n
    match n with
    | 0 => exact hX.hom_ext _ _
    | n + 1 => exact hg n

end CategoryTheory.Endofunctor
