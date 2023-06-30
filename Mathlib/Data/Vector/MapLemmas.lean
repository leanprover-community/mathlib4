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
## Fold nested `mapAccumr`s into one
-/
section Fold

section Unary
variable (xs : Vector α n) (f₁ : β → σ₁ → σ₁ × γ) (f₂ : α → σ₂ → σ₂ × β)

@[simp]
theorem mapAccumr_mapAccumr :
    mapAccumr f₁ (mapAccumr f₂ xs s₂).snd s₁
    = let m := (mapAccumr (fun x s =>
        let r₂ := f₂ x s.snd
        let r₁ := f₁ r₂.snd s.fst
        ((r₁.fst, r₂.fst), r₁.snd)
      ) xs (s₁, s₂))
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

@[simp]
theorem mapAccumr₂_mapAccumr_left (f₁ : γ → β → σ₁ → σ₁ × ζ) (f₂ : α → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ (mapAccumr f₂ xs s₂).snd ys s₁)
    = let m := (mapAccumr₂ (fun x y s =>
          let r₂ := f₂ x s.snd
          let r₁ := f₁ r₂.snd y s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
theorem map₂_map_left (f₁ : γ → β → ζ) (f₂ : α → γ) :
    map₂ f₁ (map f₂ xs) ys = map₂ (fun x y => f₁ (f₂ x) y) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all



@[simp]
theorem mapAccumr₂_mapAccumr_right (f₁ : α → γ → σ₁ → σ₁ × ζ) (f₂ : β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ xs (mapAccumr f₂ ys s₂).snd s₁)
    = let m := (mapAccumr₂ (fun x y s =>
          let r₂ := f₂ y s.snd
          let r₁ := f₁ x r₂.snd s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂))
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
theorem map₂_map_right (f₁ : α → γ → ζ) (f₂ : β → γ) :
    map₂ f₁ xs (map f₂ ys) = map₂ (fun x y => f₁ x (f₂ y)) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all



@[simp]
theorem mapAccumr_mapAccumr₂ (f₁ : γ → σ₁ → σ₁ × ζ) (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr f₁ (mapAccumr₂ f₂ xs ys s₂).snd s₁)
    = let m := mapAccumr₂ (fun x y s =>
          let r₂ := f₂ x y s.snd
          let r₁ := f₁ r₂.snd s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂);
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all

@[simp]
theorem map_map₂ (f₁ : γ → ζ) (f₂ : α → β → γ) :
    map f₁ (map₂ f₂ xs ys) = map₂ (fun x y => f₁ <| f₂ x y) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all

@[simp]
theorem mapAccumr₂_mapAccumr₂_left_left (f₁ : γ → α → σ₁ → σ₁ × φ) (f₂ : α → β → σ₂ → σ₂ × γ) :
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
theorem mapAccumr₂_mapAccumr₂_left_right
  (f₁ : γ → β → σ₁ → σ₁ × φ) (f₂ : α → β → σ₂ → σ₂ × γ) :
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
## Bisimulations
We can prove two applications of `mapAccumr` equal by providing a bisimulation relation that relates
the initial states.

That is, by providing a relation `R : σ₁ → σ₁ → Prop` such that `R s₁ s₂` implies that `R` also
relates any pair of states reachable by applying `f₁` to `s₁` and `f₂` to `s₂`, with any possible
input values.
-/

section Bisim

theorem mapAccumr_bisim (xs : Vector α n) (f₁ : α → σ₁ → σ₁ × β) (f₂ : α → σ₂ → σ₂ × β) (s₁ : σ₁)
    (s₂ : σ₂) (h : ∃ R : σ₁ → σ₂ → Prop, R s₁ s₂ ∧
      ∀ {s q} a, R s q → R (f₁ a s).1 (f₂ a q).1 ∧ (f₁ a s).2 = (f₂ a q).2) :
    (mapAccumr f₁ xs s₁).2 = (mapAccumr f₂ xs s₂).2 := by
  rcases h with ⟨R, h₀, hR⟩
  induction xs using Vector.revInductionOn generalizing s₁ s₂
  next => rfl
  next xs x ih =>
    rcases (hR x h₀) with ⟨hR, _⟩
    simp only [mapAccumr_snoc, ih _ _ hR]
    congr 1

theorem mapAccumr₂_bisim (xs : Vector α n) (ys : Vector β n) (f₁ : α → β → σ₁ → σ₁ × γ)
    (f₂ : α → β → σ₂ → σ₂ × γ) (s₁ : σ₁) (s₂ : σ₂)
    (h : ∃ R : σ₁ → σ₂ → Prop, R s₁ s₂ ∧
      ∀ {s q} a b, R s q → R (f₁ a b s).1 (f₂ a b q).1 ∧ (f₁ a b s).2 = (f₂ a b q).2) :
    (mapAccumr₂ f₁ xs ys s₁).2 = (mapAccumr₂ f₂ xs ys s₂).2 := by
  rcases h with ⟨R, h₀, hR⟩
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂
  next => rfl
  next xs ys x y ih =>
    rcases (hR x y h₀) with ⟨hR, _⟩
    simp only [mapAccumr₂_snoc, ih _ _ hR]
    congr 1
end Bisim

/-!
## Redundant state optimization

The following section are collection of rewrites to simplify, or even get rid, redundant
accumulation state
-/
section RedundantState
variable {xs : Vector α n} {ys : Vector β n}


/--
  If there is a set of states that is closed under `f`, and such that `f` produces that same output
  for all states in this set, then the state is not actually needed.
  Hence, then we can rewrite `mapAccumr` into just `map`
-/
theorem mapAccumr_eq_map {f : α → σ → σ × β} {s₀ : σ} (S : Set σ) (h₀ : s₀ ∈ S)
    (closure : ∀ a s, s ∈ S → (f a s).1 ∈ S)
    (out : ∀ a s s', s ∈ S → s' ∈ S → (f a s).2 = (f a s').2) :
    ∃ s_out ∈ S, (mapAccumr f xs s₀) = (s_out, map (f · s₀ |>.snd) xs) := by
  clear ys
  induction xs using revInductionOn generalizing s₀
  next =>
    use s₀
    simp[h₀]
  next xs x ih =>
    specialize closure x _ h₀
    rcases @ih (f x s₀).1 closure with ⟨s_out, hs, ih⟩
    use s_out, hs
    simp only [mapAccumr_snoc, ih, map_snoc]
    congr
    funext x'
    rw [out x' s₀ (f x s₀).1 h₀ closure]

/--
  If there is a set of states that is closed under `f`, and such that `f` produces that same output
  for all states in this set, then the state is not actually needed.
  Hence, then we can rewrite `mapAccumr₂` into just `map₂`
-/
theorem mapAccumr₂_eq_map₂ {f : α → β → σ → σ × γ} {s₀ : σ} (S : Set σ) (h₀ : s₀ ∈ S)
    (closure : ∀ a b s, s ∈ S → (f a b s).1 ∈ S)
    (out : ∀ a b s s', s ∈ S → s' ∈ S → (f a b s).2 = (f a b s').2) :
    ∃ s_out ∈ S, (mapAccumr₂ f xs ys s₀) = (s_out, map₂ (f · · s₀ |>.snd) xs ys) := by
  induction xs, ys using revInductionOn₂ generalizing s₀
  next =>
    use s₀
    simp[h₀]
  next xs ys x y ih =>
    specialize closure x y _ h₀
    specialize @ih (f x y s₀).1 closure
    rcases ih with ⟨s_out, hs, ih⟩
    use s_out, hs
    simp[ih]
    congr
    funext x' y'
    rw [out x' y' s₀ (f x y s₀).1 h₀ closure]

/--
  If an accumulation function `f`, given an initial state `s`, produces `s` as its output state
  for all possible input bits, then the state is redundant and can be optimized out
-/
@[simp]
theorem mapAccumr_eq_map_of_constant_state (f : α → σ → σ × β) (s : σ) (h : ∀ a, (f a s).fst = s) :
    mapAccumr f xs s = (s, (map (fun x => (f x s).snd) xs)) := by
  clear ys
  induction xs using revInductionOn <;> simp_all

/--
  If an accumulation function `f`, given an initial state `s`, produces `s` as its output state
  for all possible input bits, then the state is redundant and can be optimized out
-/
@[simp]
theorem mapAccumr₂_eq_map₂_of_constant_state (f : α → β → σ → σ × γ) (s : σ)
    (h : ∀ a b, (f a b s).fst = s) :
    mapAccumr₂ f xs ys s = (s, (map₂ (fun x y => (f x y s).snd) xs ys)) := by
  induction xs, ys using revInductionOn₂ <;> simp_all

/-- If `f` takes a pair of states, but always returns the same value for both elements of the
    pair, then we can simplify to just a single element of state
  -/
@[simp]
theorem mapAccumr_redundant_pair (f : α → (σ × σ) → (σ × σ) × β)
    (h : ∀ x s, let s' := (f x (s, s)).fst; s'.fst = s'.snd) :
    mapAccumr f xs (s, s)
    = let m := mapAccumr (fun x s =>
          let r := f x (s, s);
          (r.fst.fst, r.snd)
        ) xs s
      ((m.fst, m.fst), m.snd) := by
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
    (h : ∀ x y s, let s' := (f x y (s, s)).fst; s'.fst = s'.snd) :
    mapAccumr₂ f xs ys (s, s) =
      let m := mapAccumr₂ (fun x y s =>
        let r := f x y (s, s);
        (r.fst.fst, r.snd)
      ) xs ys s
      ((m.fst, m.fst), m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s
  case nil => rfl
  case snoc xs ys x y ih =>
    specialize h x y s
    revert h
    simp_all
    rcases (f x y (s, s)) with ⟨⟨s₁, s₂⟩, y⟩
    simp_all

end RedundantState



/-!
## Unused input optimizations
-/
section UnusedInput
variable {xs : Vector α n} {ys : Vector β n}

/--
  If `f` returns the same output and next state for every value of it's first argument, then
  `xs : Vector` is ignored, and we can rewrite `mapAccumr₂` into `map`
-/
@[simp]
theorem mapAccumr₂_unused_input_left [Inhabited α] (f : α → β → σ → σ × γ)
    (h : ∀ a b s, f default b s = f a b s) :
    mapAccumr₂ f xs ys s = mapAccumr (fun b s => f default b s) ys s := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s
  case nil => rfl
  case snoc xs ys x y ih =>
    simp[h x y s, ih]

/--
  If `f` returns the same output and next state for every value of it's second argument, then
  `ys : Vector` is ignored, and we can rewrite `mapAccumr₂` into `map`
-/
@[simp]
theorem mapAccumr₂_unused_input_right [Inhabited β] (f : α → β → σ → σ × γ)
    (h : ∀ a b s, f a default s = f a b s) :
    mapAccumr₂ f xs ys s = mapAccumr (fun a s => f a default s) xs s := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s
  case nil => rfl
  case snoc xs ys x y ih =>
    simp[h x y s, ih]

end UnusedInput



/-!
## Commutativity
-/
section Comm
variable (xs ys : Vector α n)

theorem map₂_comm (f : α → α → β) (comm : ∀ a₁ a₂, f a₁ a₂ = f a₂ a₁) :
    map₂ f xs ys = map₂ f ys xs := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all

theorem mapAccumr₂_comm (f : α → α → σ → σ × γ) (comm : ∀ a₁ a₂ s, f a₁ a₂ s = f a₂ a₁ s) :
    mapAccumr₂ f xs ys s = mapAccumr₂ f ys xs s := by
  induction xs, ys using Vector.inductionOn₂ generalizing s <;> simp_all

end Comm



/-!
## Argument Flipping
-/
section Flip
variable (xs : Vector α n) (ys : Vector β n)

theorem map₂_flip (f : α → β → γ) :
    map₂ f xs ys = map₂ (flip f) ys xs := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all[flip]


theorem mapAccumr₂_flip (f : α → β → σ → σ × γ) :
    mapAccumr₂ f xs ys s = mapAccumr₂ (flip f) ys xs s := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all[flip]

end Flip


end Vector
