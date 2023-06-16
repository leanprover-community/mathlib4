/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Snoc

/-!

  This file establishes a set of normalization lemmas for `map`/`mapAccumr`/`fold` operations
  on vectors (and instances of these operations with muliple inputs)

-/

namespace Vector
  /-!
  ## Normalization
  Try to rewrite all operations in terms of `mapAccumr`
  -/
  section Norm

    section Unary
      variable (xs : Vector α n)

      @[aesop norm]
      theorem map_to_mapAccumr (f : α → β) :
          map f xs = (mapAccumr (fun x _ => (⟨⟩, f x)) xs ()).snd := by
        induction xs using revInductionOn <;> simp_all

    end Unary

    section Binary
      variable (xs : Vector α n) (ys : Vector β n)

      @[aesop norm]
      theorem map₂_to_mapAccumr₂ (f : α → β → γ) :
          map₂ f xs ys = (mapAccumr₂ (fun x y _ => (⟨⟩, f x y)) xs ys ()).snd := by
        induction xs, ys using revInductionOn₂ <;> simp_all

    end Binary

  end Norm


  /-!
  ## Fold nested `mapAccumr`s into one
  -/
  section Fold

    section Unary
      variable (xs : Vector α n) (f₁ : β → σ₁ → σ₁ × γ) (f₂ : α → σ₂ → σ₂ × β)

      protected abbrev mapAccumr_mapAccumr.g (x : α) (s : σ₁ × σ₂) :=
        let r₂ := f₂ x s.snd
        let r₁ := f₁ r₂.snd s.fst
        ((r₁.fst, r₂.fst), r₁.snd)

      @[simp]
      theorem mapAccumr_mapAccumr : (mapAccumr f₁ (mapAccumr f₂ xs s₂).snd s₁)
                                    = let m := (mapAccumr (mapAccumr_mapAccumr.g f₁ f₂) xs (s₁, s₂))
                                      (m.fst.fst, m.snd) := by
        induction xs using Vector.revInductionOn generalizing s₁ s₂ <;> simp_all

    end Unary

    section Binary
      variable (xs : Vector α n) (ys : Vector β n)
      variable (f₁ : β' → β → σ₁ → σ₁ × γ) (f₂ : α → σ₂ → σ₂ × β')

      protected abbrev mapAccumr₂_mapAccumr_left.g (x : α) (y : β) (s : σ₁ × σ₂) :=
        let r₂ := f₂ x s.snd
        let r₁ := f₁ r₂.snd y s.fst
        ((r₁.fst, r₂.fst), r₁.snd)

      @[simp]
      theorem mapAccumr₂_mapAccumr_left :
          (mapAccumr₂ f₁ (mapAccumr f₂ xs s₂).snd ys s₁)
          = let m := (mapAccumr₂ (mapAccumr₂_mapAccumr_left.g f₁ f₂) xs ys (s₁, s₂))
            (m.fst.fst, m.snd) := by
        induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all



      variable (f₁ : β → γ → σ₁ → σ₁ × ζ) (f₂ : α → σ₂ → σ₂ × γ)

      protected abbrev mapAccumr₂_mapAccumr_right.g (x : α) (y : β) (s : σ₁ × σ₂) :=
        let r₂ := f₂ x s.snd
        let r₁ := f₁ y r₂.snd s.fst
        ((r₁.fst, r₂.fst), r₁.snd)

      @[simp]
      theorem mapAccumr₂_mapAccumr_right :
          (mapAccumr₂ f₁ ys (mapAccumr f₂ xs s₂).snd s₁)
          = let m := (mapAccumr₂ (mapAccumr₂_mapAccumr_right.g f₁ f₂) xs ys (s₁, s₂))
            (m.fst.fst, m.snd) := by
        induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all


      variable (zs : Vector γ n)

      -- @[simp]
      -- theorem mapAccumr₂_mapAccumr₂_left_left :
      --     (mapAccumr₂ f₁ (mapAccumr₂ f₂ xs ys s₂) xs s₁)
      --     = let m := (mapAccumr)

    end Binary

  end Fold


  /-!
  ## Redundant state optimization
  If an accumulation function `f`, given an initial state `s`, produces `s` as its output state
  for all possible input bits, then the state is redundant and can be optimized out
  -/
  section RedundantState

    @[simp]
    theorem mapAccumr_redundant_state (f : α → σ → σ × β) (s : σ) (h : ∀ a, (f a s).fst = s) :
        mapAccumr f xs s = (s, (mapAccumr (fun x _ => ((), (f x s).snd)) xs ()).snd) := by
      induction xs using revInductionOn <;> simp_all

    @[simp]
    theorem mapAccumr₂_redundant_state (f : α → β → σ → σ × γ) (s : σ) (h : ∀ a b, (f a b s).fst = s) :
        mapAccumr₂ f xs ys s = (s, (mapAccumr₂ (fun x y _ => ((), (f x y s).snd)) xs ys ()).snd) := by
      induction xs, ys using revInductionOn₂ <;> simp_all

  end RedundantState


end Vector
