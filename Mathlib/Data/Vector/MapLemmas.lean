/-
Copyright (c) 2023 Alex Keizer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Keizer
-/
import Mathlib.Data.Vector.Basic
import Mathlib.Data.Vector.Snoc


/-!
  This file establishes a set of normalization lemmas for `map`/`mapAccumr` operations on vectors
-/

namespace Vector

/-!
## Normalization
Rewrite applications of `map` in terms of `mapAccumr` with `Unit` state
-/
section Norm

  theorem map_to_mapAccumr (xs : Vector α n) (f : α → β) :
      map f xs = (mapAccumr (fun x _ => (⟨⟩, f x)) xs ()).snd := by
    induction xs using revInductionOn <;> simp_all

  theorem map₂_to_mapAccumr₂ (xs : Vector α n) (ys : Vector β n) (f : α → β → γ) :
      map₂ f xs ys = (mapAccumr₂ (fun x y _ => (⟨⟩, f x y)) xs ys ()).snd := by
    induction xs, ys using revInductionOn₂ <;> simp_all

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


@[simp]
theorem mapAccumr_map (f₂ : α → β) :
    (mapAccumr f₁ (map f₂ xs) s) = (mapAccumr (fun x s => f₁ (f₂ x) s) xs s) := by
  induction xs using Vector.revInductionOn generalizing s <;> simp_all

@[simp]
theorem map_mapAccumr (f₁ : β → γ) :
    (map f₁ (mapAccumr f₂ xs s).snd) = (mapAccumr (fun x s =>
        let r := (f₂ x s); (r.fst, f₁ r.snd)
      ) xs s).snd := by
  induction xs using Vector.revInductionOn generalizing s <;> simp_all

@[simp]
theorem map_map (f₁ : β → γ) (f₂ : α → β) :
    map f₁ (map f₂ xs) = map (fun x => f₁ <| f₂ x) xs := by
  induction xs using Vector.inductionOn <;> simp_all

end Unary



section Binary
variable (xs : Vector α n) (ys : Vector β n)
variable (f₁ : γ → β → σ₁ → σ₁ × ζ) (f₂ : α → σ₂ → σ₂ × γ)

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

@[simp]
theorem map₂_map_left (f₁ : γ → β → ζ) (f₂ : α → γ) :
    map₂ f₁ (map f₂ xs) ys = map₂ (fun x y => f₁ (f₂ x) y) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all



variable (f₁ : α → γ → σ₁ → σ₁ × ζ) (f₂ : β → σ₂ → σ₂ × γ)

protected abbrev mapAccumr₂_mapAccumr_right.g (x : α) (y : β) (s : σ₁ × σ₂) :=
  let r₂ := f₂ y s.snd
  let r₁ := f₁ x r₂.snd s.fst
  ((r₁.fst, r₂.fst), r₁.snd)

@[simp]
theorem mapAccumr₂_mapAccumr_right :
    (mapAccumr₂ f₁ xs (mapAccumr f₂ ys s₂).snd s₁)
    = let m := (mapAccumr₂ (mapAccumr₂_mapAccumr_right.g f₁ f₂) xs ys (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
theorem map₂_map_right (f₁ : α → γ → ζ) (f₂ : β → γ) :
    map₂ f₁ xs (map f₂ ys) = map₂ (fun x y => f₁ x (f₂ y)) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all


variable (f₁ : γ → σ₁ → σ₁ × ζ) (f₂ : α → β → σ₂ → σ₂ × γ)

protected abbrev mapAccumr_mapAccumr₂.g (x : α) (y : β) (s : σ₁ × σ₂) :=
  let r₂ := f₂ x y s.snd
  let r₁ := f₁ r₂.snd s.fst
  ((r₁.fst, r₂.fst), r₁.snd)

@[simp]
theorem mapAccumr_mapAccumr₂ :
    (mapAccumr f₁ (mapAccumr₂ f₂ xs ys s₂).snd s₁)
    = let m := mapAccumr₂ (mapAccumr_mapAccumr₂.g f₁ f₂) xs ys (s₁, s₂);
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
theorem map_map₂ (f₁ : γ → ζ) (f₂ : α → β → γ) :
    map f₁ (map₂ f₂ xs ys) = map₂ (fun x y => f₁ <| f₂ x y) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]
theorem mapAccumr₂_mapAccumr₂_left_left (f₁ : γ → α → σ₁ → σ₁ × φ)
                                        (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ (mapAccumr₂ f₂ xs ys s₂).snd xs s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ r₂.snd x s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂);
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
theorem mapAccumr₂_mapAccumr₂_left_right  (f₁ : γ → β → σ₁ → σ₁ × φ)
                                          (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ (mapAccumr₂ f₂ xs ys s₂).snd ys s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ r₂.snd y s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂);
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
theorem mapAccumr₂_mapAccumr₂_right_left  (f₁ : α → γ → σ₁ → σ₁ × φ)
                                          (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ xs (mapAccumr₂ f₂ xs ys s₂).snd s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ x r₂.snd s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂);
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
theorem mapAccumr₂_mapAccumr₂_right_right (f₁ : β → γ → σ₁ → σ₁ × φ)
                                          (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ ys (mapAccumr₂ f₂ xs ys s₂).snd s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ y r₂.snd s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂);
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all


end Binary


end Fold


/-!
## Redundant state or input optimizations

The following section are collection of rewrites to simplify, or even get rid, redundant
accumulation state, or redundant inputs
-/
section RedundantState
variable (xs : Vector α n) (ys : Vector β n)

/--
  If an accumulation function `f`, given an initial state `s`, produces `s` as its output state
  for all possible input bits, then the state is redundant and can be optimized out
-/
@[simp]
theorem mapAccumr_redundant_state (f : α → σ → σ × β) (s : σ) (h : ∀ a, (f a s).fst = s) :
    mapAccumr f xs s = (s, (map (fun x => (f x s).snd) xs)) := by
  clear ys
  induction xs using revInductionOn <;> simp_all

/--
  If an accumulation function `f`, given an initial state `s`, produces `s` as its output state
  for all possible input bits, then the state is redundant and can be optimized out
-/
@[simp]
theorem mapAccumr₂_redundant_state (f : α → β → σ → σ × γ) (s : σ) (h : ∀ a b, (f a b s).fst = s) :
    mapAccumr₂ f xs ys s = (s, (map₂ (fun x y => (f x y s).snd) xs ys)) := by
  induction xs, ys using revInductionOn₂ <;> simp_all

/-- If `f` takes a pair of states, but always returns the same value for both elements of the
    pair, then we can simplify to just a single element of state
  -/
@[simp]
theorem mapAccumr_redundant_pair (f : α → (σ × σ) → (σ × σ) × β)
                              (h : ∀ x s, let s' := (f x (s, s)).fst; s'.fst = s'.snd)
                            : mapAccumr f xs (s, s) = (
                                let m := mapAccumr (fun x s => let r := f x (s, s);
                                                              (r.fst.fst, r.snd)
                                                    ) xs s
                                ((m.fst, m.fst), m.snd)
                              ) := by
  clear ys
  induction xs using Vector.revInductionOn generalizing s
  case nil => rfl
  case snoc xs x ih =>
    specialize h x s
    revert h
    simp_all
    rcases (f x (s, s)) with ⟨⟨s₁, s₂⟩, y⟩
    simp_all

/-- If `f` takes a pair of states, but always returns the same value for both elements of the
    pair, then we can simplify to just a single element of state
  -/
@[simp]
theorem mapAccumr₂_redundant_pair (f : α → β → (σ × σ) → (σ × σ) × γ)
                              (h : ∀ x y s, let s' := (f x y (s, s)).fst; s'.fst = s'.snd)
                            : mapAccumr₂ f xs ys (s, s) = (
                                let m := mapAccumr₂ (fun x y s => let r := f x y (s, s);
                                                                  (r.fst.fst, r.snd)
                                                    ) xs ys s
                                ((m.fst, m.fst), m.snd)
                              ) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s
  case nil => rfl
  case snoc xs ys x y ih =>
    specialize h x y s
    revert h
    simp_all
    rcases (f x y (s, s)) with ⟨⟨s₁, s₂⟩, y⟩
    simp_all


/--
  If `f` returns the same output and next state for every value of it's first argument, then
  `xs : Vector` is ignored, and we can rewrite `mapAccumr₂` into `map`
-/
@[simp]
theorem mapAccumr₂_unused_input_left  [Inhabited α]
                                      (f : α → β → σ → σ × γ)
                                      (h : ∀ a b s, f Inhabited.default b s = f a b s) :
    mapAccumr₂ f xs ys s = mapAccumr (fun b s => f Inhabited.default b s) ys s := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s
  case nil => rfl
  case snoc xs ys x y ih =>
    simp[h x y s, ih]

/--
  If `f` returns the same output and next state for every value of it's second argument, then
  `ys : Vector` is ignored, and we can rewrite `mapAccumr₂` into `map`
-/
@[simp]
theorem mapAccumr₂_unused_input_right [Inhabited β]
                                      (f : α → β → σ → σ × γ)
                                      (h : ∀ a b s, f a Inhabited.default s = f a b s) :
    mapAccumr₂ f xs ys s = mapAccumr (fun a s => f a Inhabited.default s) xs s := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s
  case nil => rfl
  case snoc xs ys x y ih =>
    simp[h x y s, ih]

end RedundantState


end Vector
