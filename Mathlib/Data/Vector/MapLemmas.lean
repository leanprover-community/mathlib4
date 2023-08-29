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

set_option autoImplicit true

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
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals

@[simp]
theorem mapAccumr_map (f₂ : α → β) :
    (mapAccumr f₁ (map f₂ xs) s) = (mapAccumr (fun x s => f₁ (f₂ x) s) xs s) := by
  induction xs using Vector.revInductionOn generalizing s <;> simp_all
  -- ⊢ mapAccumr f₁ (map f₂ nil) s = mapAccumr (fun x s => f₁ (f₂ x) s) nil s
                                                              -- 🎉 no goals
                                                              -- 🎉 no goals

@[simp]
theorem map_mapAccumr (f₁ : β → γ) :
    (map f₁ (mapAccumr f₂ xs s).snd) = (mapAccumr (fun x s =>
        let r := (f₂ x s); (r.fst, f₁ r.snd)
      ) xs s).snd := by
  induction xs using Vector.revInductionOn generalizing s <;> simp_all
                                                              -- 🎉 no goals
                                                              -- 🎉 no goals

@[simp]
theorem map_map (f₁ : β → γ) (f₂ : α → β) :
    map f₁ (map f₂ xs) = map (fun x => f₁ <| f₂ x) xs := by
  induction xs using Vector.inductionOn <;> simp_all
  -- ⊢ map f₁ (map f₂ nil) = map (fun x => f₁ (f₂ x)) nil
                                            -- 🎉 no goals
                                            -- 🎉 no goals

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
                                                                       -- 🎉 no goals
                                                                       -- 🎉 no goals

@[simp]
theorem map₂_map_left (f₁ : γ → β → ζ) (f₂ : α → γ) :
    map₂ f₁ (map f₂ xs) ys = map₂ (fun x y => f₁ (f₂ x) y) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all
  -- ⊢ map₂ f₁ (map f₂ nil) nil = map₂ (fun x y => f₁ (f₂ x) y) nil nil
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals

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
                                                                       -- 🎉 no goals
                                                                       -- 🎉 no goals

@[simp]
theorem map₂_map_right (f₁ : α → γ → ζ) (f₂ : β → γ) :
    map₂ f₁ xs (map f₂ ys) = map₂ (fun x y => f₁ x (f₂ y)) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all
  -- ⊢ map₂ f₁ nil (map f₂ nil) = map₂ (fun x y => f₁ x (f₂ y)) nil nil
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals

@[simp]
theorem mapAccumr_mapAccumr₂ (f₁ : γ → σ₁ → σ₁ × ζ) (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr f₁ (mapAccumr₂ f₂ xs ys s₂).snd s₁)
    = let m := mapAccumr₂ (fun x y s =>
          let r₂ := f₂ x y s.snd
          let r₁ := f₁ r₂.snd s.fst
          ((r₁.fst, r₂.fst), r₁.snd)
        ) xs ys (s₁, s₂)
      (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all
                                                                       -- 🎉 no goals
                                                                       -- 🎉 no goals

@[simp]
theorem map_map₂ (f₁ : γ → ζ) (f₂ : α → β → γ) :
    map f₁ (map₂ f₂ xs ys) = map₂ (fun x y => f₁ <| f₂ x y) xs ys := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all
  -- ⊢ map f₁ (map₂ f₂ nil nil) = map₂ (fun x y => f₁ (f₂ x y)) nil nil
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals

@[simp]
theorem mapAccumr₂_mapAccumr₂_left_left (f₁ : γ → α → σ₁ → σ₁ × φ) (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ (mapAccumr₂ f₂ xs ys s₂).snd xs s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ r₂.snd x s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all
                                                                       -- 🎉 no goals
                                                                       -- 🎉 no goals

@[simp]
theorem mapAccumr₂_mapAccumr₂_left_right
  (f₁ : γ → β → σ₁ → σ₁ × φ) (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ (mapAccumr₂ f₂ xs ys s₂).snd ys s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ r₂.snd y s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all
                                                                       -- 🎉 no goals
                                                                       -- 🎉 no goals

@[simp]
theorem mapAccumr₂_mapAccumr₂_right_left (f₁ : α → γ → σ₁ → σ₁ × φ) (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ xs (mapAccumr₂ f₂ xs ys s₂).snd s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ x r₂.snd s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all
                                                                       -- 🎉 no goals
                                                                       -- 🎉 no goals

@[simp]
theorem mapAccumr₂_mapAccumr₂_right_right (f₁ : β → γ → σ₁ → σ₁ × φ) (f₂ : α → β → σ₂ → σ₂ × γ) :
    (mapAccumr₂ f₁ ys (mapAccumr₂ f₂ xs ys s₂).snd s₁)
    = let m := mapAccumr₂ (fun x y (s₁, s₂) =>
                let r₂ := f₂ x y s₂
                let r₁ := f₁ y r₂.snd s₁
                ((r₁.fst, r₂.fst), r₁.snd)
              )
            xs ys (s₁, s₂)
    (m.fst.fst, m.snd) := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂ <;> simp_all
                                                                       -- 🎉 no goals
                                                                       -- 🎉 no goals

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
variable {xs : Vector α n}

theorem mapAccumr_bisim {f₁ : α → σ₁ → σ₁ × β} {f₂ : α → σ₂ → σ₂ × β} {s₁ : σ₁} {s₂ : σ₂}
      (R : σ₁ → σ₂ → Prop) (h₀ : R s₁ s₂)
      (hR : ∀ {s q} a, R s q → R (f₁ a s).1 (f₂ a q).1 ∧ (f₁ a s).2 = (f₂ a q).2) :
    R (mapAccumr f₁ xs s₁).fst (mapAccumr f₂ xs s₂).fst
    ∧ (mapAccumr f₁ xs s₁).snd = (mapAccumr f₂ xs s₂).snd := by
  induction xs using Vector.revInductionOn generalizing s₁ s₂
  -- ⊢ R (mapAccumr f₁ nil s₁).fst (mapAccumr f₂ nil s₂).fst ∧ (mapAccumr f₁ nil s₁ …
  next => exact ⟨h₀, rfl⟩
  -- ⊢ R (mapAccumr f₁ (snoc xs✝ x✝) s₁).fst (mapAccumr f₂ (snoc xs✝ x✝) s₂).fst ∧  …
  next xs x ih =>
    rcases (hR x h₀) with ⟨hR, _⟩
    simp only [mapAccumr_snoc, ih hR, true_and]
    congr 1

theorem mapAccumr_bisim_tail {f₁ : α → σ₁ → σ₁ × β} {f₂ : α → σ₂ → σ₂ × β} {s₁ : σ₁} {s₂ : σ₂}
    (h : ∃ R : σ₁ → σ₂ → Prop, R s₁ s₂ ∧
      ∀ {s q} a, R s q → R (f₁ a s).1 (f₂ a q).1 ∧ (f₁ a s).2 = (f₂ a q).2) :
    (mapAccumr f₁ xs s₁).snd = (mapAccumr f₂ xs s₂).snd := by
  rcases h with ⟨R, h₀, hR⟩
  -- ⊢ (mapAccumr f₁ xs s₁).snd = (mapAccumr f₂ xs s₂).snd
  exact (mapAccumr_bisim R h₀ hR).2
  -- 🎉 no goals

theorem mapAccumr₂_bisim {ys : Vector β n} {f₁ : α → β → σ₁ → σ₁ × γ}
    {f₂ : α → β → σ₂ → σ₂ × γ} {s₁ : σ₁} {s₂ : σ₂}
    (R : σ₁ → σ₂ → Prop) (h₀ : R s₁ s₂)
    (hR :  ∀ {s q} a b, R s q → R (f₁ a b s).1 (f₂ a b q).1 ∧ (f₁ a b s).2 = (f₂ a b q).2) :
    R (mapAccumr₂ f₁ xs ys s₁).1 (mapAccumr₂ f₂ xs ys s₂).1
    ∧ (mapAccumr₂ f₁ xs ys s₁).2 = (mapAccumr₂ f₂ xs ys s₂).2 := by
  induction xs, ys using Vector.revInductionOn₂ generalizing s₁ s₂
  -- ⊢ R (mapAccumr₂ f₁ nil nil s₁).fst (mapAccumr₂ f₂ nil nil s₂).fst ∧ (mapAccumr …
  next => exact ⟨h₀, rfl⟩
  -- ⊢ R (mapAccumr₂ f₁ (snoc xs✝ x✝) (snoc ys✝ y✝) s₁).fst (mapAccumr₂ f₂ (snoc xs …
  next xs ys x y ih =>
    rcases (hR x y h₀) with ⟨hR, _⟩
    simp only [mapAccumr₂_snoc, ih hR, true_and]
    congr 1

theorem mapAccumr₂_bisim_tail {ys : Vector β n} {f₁ : α → β → σ₁ → σ₁ × γ}
    {f₂ : α → β → σ₂ → σ₂ × γ} {s₁ : σ₁} {s₂ : σ₂}
    (h : ∃ R : σ₁ → σ₂ → Prop, R s₁ s₂ ∧
      ∀ {s q} a b, R s q → R (f₁ a b s).1 (f₂ a b q).1 ∧ (f₁ a b s).2 = (f₂ a b q).2) :
    (mapAccumr₂ f₁ xs ys s₁).2 = (mapAccumr₂ f₂ xs ys s₂).2 := by
  rcases h with ⟨R, h₀, hR⟩
  -- ⊢ (mapAccumr₂ f₁ xs ys s₁).snd = (mapAccumr₂ f₂ xs ys s₂).snd
  exact (mapAccumr₂_bisim R h₀ hR).2
  -- 🎉 no goals

end Bisim

/-!
## Redundant state optimization

The following section are collection of rewrites to simplify, or even get rid, redundant
accumulation state
-/
section RedundantState
variable {xs : Vector α n} {ys : Vector β n}

protected theorem map_eq_mapAccumr :
    map f xs = (mapAccumr (fun x (_ : Unit) ↦ ((), f x)) xs ()).snd := by
  clear ys
  -- ⊢ map f xs = (mapAccumr (fun x x_1 => ((), f x)) xs ()).snd
  induction xs using Vector.revInductionOn <;> simp_all
  -- ⊢ map f nil = (mapAccumr (fun x x_1 => ((), f x)) nil ()).snd
                                               -- 🎉 no goals
                                               -- 🎉 no goals

/--
  If there is a set of states that is closed under `f`, and such that `f` produces that same output
  for all states in this set, then the state is not actually needed.
  Hence, then we can rewrite `mapAccumr` into just `map`
-/
theorem mapAccumr_eq_map {f : α → σ → σ × β} {s₀ : σ} (S : Set σ) (h₀ : s₀ ∈ S)
    (closure : ∀ a s, s ∈ S → (f a s).1 ∈ S)
    (out : ∀ a s s', s ∈ S → s' ∈ S → (f a s).2 = (f a s').2) :
    (mapAccumr f xs s₀).snd = map (f · s₀ |>.snd) xs := by
  rw[Vector.map_eq_mapAccumr]
  -- ⊢ (mapAccumr f xs s₀).snd = (mapAccumr (fun x x_1 => ((), (f x s₀).snd)) xs () …
  apply mapAccumr_bisim_tail
  -- ⊢ ∃ R, R s₀ () ∧ ∀ {s : σ} {q : Unit} (a : α), R s q → R (f a s).fst ((), (f a …
  use fun s _ => s ∈ S, h₀
  -- ⊢ ∀ {s : σ} {q : Unit} (a : α), s ∈ S → (f a s).fst ∈ S ∧ (f a s).snd = ((), ( …
  exact @fun s _q a h => ⟨closure a s h, out a s s₀ h h₀⟩
  -- 🎉 no goals

protected theorem map₂_eq_mapAccumr₂ :
    map₂ f xs ys = (mapAccumr₂ (fun x y (_ : Unit) ↦ ((), f x y)) xs ys ()).snd := by
  induction xs, ys using Vector.revInductionOn₂ <;> simp_all
  -- ⊢ map₂ f nil nil = (mapAccumr₂ (fun x y x_1 => ((), f x y)) nil nil ()).snd
                                                    -- 🎉 no goals
                                                    -- 🎉 no goals

/--
  If there is a set of states that is closed under `f`, and such that `f` produces that same output
  for all states in this set, then the state is not actually needed.
  Hence, then we can rewrite `mapAccumr₂` into just `map₂`
-/
theorem mapAccumr₂_eq_map₂ {f : α → β → σ → σ × γ} {s₀ : σ} (S : Set σ) (h₀ : s₀ ∈ S)
    (closure : ∀ a b s, s ∈ S → (f a b s).1 ∈ S)
    (out : ∀ a b s s', s ∈ S → s' ∈ S → (f a b s).2 = (f a b s').2) :
    (mapAccumr₂ f xs ys s₀).snd = map₂ (f · · s₀ |>.snd) xs ys := by
  rw[Vector.map₂_eq_mapAccumr₂]
  -- ⊢ (mapAccumr₂ f xs ys s₀).snd = (mapAccumr₂ (fun x y x_1 => ((), (f x y s₀).sn …
  apply mapAccumr₂_bisim_tail
  -- ⊢ ∃ R, R s₀ () ∧ ∀ {s : σ} {q : Unit} (a : α) (b : β), R s q → R (f a b s).fst …
  use fun s _ => s ∈ S, h₀
  -- ⊢ ∀ {s : σ} {q : Unit} (a : α) (b : β), s ∈ S → (f a b s).fst ∈ S ∧ (f a b s). …
  exact @fun s _q a b h => ⟨closure a b s h, out a b s s₀ h h₀⟩
  -- 🎉 no goals

/--
  If an accumulation function `f`, given an initial state `s`, produces `s` as its output state
  for all possible input bits, then the state is redundant and can be optimized out
-/
@[simp]
theorem mapAccumr_eq_map_of_constant_state (f : α → σ → σ × β) (s : σ) (h : ∀ a, (f a s).fst = s) :
    mapAccumr f xs s = (s, (map (fun x => (f x s).snd) xs)) := by
  clear ys
  -- ⊢ mapAccumr f xs s = (s, map (fun x => (f x s).snd) xs)
  induction xs using revInductionOn <;> simp_all
  -- ⊢ mapAccumr f nil s = (s, map (fun x => (f x s).snd) nil)
                                        -- 🎉 no goals
                                        -- 🎉 no goals

/--
  If an accumulation function `f`, given an initial state `s`, produces `s` as its output state
  for all possible input bits, then the state is redundant and can be optimized out
-/
@[simp]
theorem mapAccumr₂_eq_map₂_of_constant_state (f : α → β → σ → σ × γ) (s : σ)
    (h : ∀ a b, (f a b s).fst = s) :
    mapAccumr₂ f xs ys s = (s, (map₂ (fun x y => (f x y s).snd) xs ys)) := by
  induction xs, ys using revInductionOn₂ <;> simp_all
  -- ⊢ mapAccumr₂ f nil nil s = (s, map₂ (fun x y => (f x y s).snd) nil nil)
                                             -- 🎉 no goals
                                             -- 🎉 no goals

/--
  If an accumulation function `f`, produces the same output bits regardless of accumulation state,
  then the state is redundant and can be optimized out
-/
@[simp]
theorem mapAccumr_eq_map_of_unused_state (f : α → σ → σ × β) (s : σ)
    (h : ∀ a s s', (f a s).snd = (f a s').snd) :
    (mapAccumr f xs s).snd = (map (fun x => (f x s).snd) xs) :=
  mapAccumr_eq_map (fun _ => true) rfl (fun _ _ _ => rfl) (fun a s s' _ _ => h a s s')


/--
  If an accumulation function `f`, produces the same output bits regardless of accumulation state,
  then the state is redundant and can be optimized out
-/
@[simp]
theorem mapAccumr₂_eq_map₂_of_unused_state (f : α → β → σ → σ × γ) (s : σ)
    (h : ∀ a b s s', (f a b s).snd = (f a b s').snd) :
    (mapAccumr₂ f xs ys s).snd = (map₂ (fun x y => (f x y s).snd) xs ys) :=
  mapAccumr₂_eq_map₂ (fun _ => true) rfl (fun _ _ _ _ => rfl) (fun a b s s' _ _ => h a b s s')


/-- If `f` takes a pair of states, but always returns the same value for both elements of the
    pair, then we can simplify to just a single element of state
  -/
@[simp]
theorem mapAccumr_redundant_pair (f : α → (σ × σ) → (σ × σ) × β)
    (h : ∀ x s, (f x (s, s)).fst.fst = (f x (s, s)).fst.snd) :
    (mapAccumr f xs (s, s)).snd = (mapAccumr (fun x (s : σ) =>
      (f x (s, s) |>.fst.fst, f x (s, s) |>.snd)
    ) xs s).snd :=
  mapAccumr_bisim_tail <| by
    use fun (s₁, s₂) s => s₂ = s ∧ s₁ = s
    -- ⊢ (match (s, s) with
    simp_all
    -- 🎉 no goals

/-- If `f` takes a pair of states, but always returns the same value for both elements of the
    pair, then we can simplify to just a single element of state
  -/
@[simp]
theorem mapAccumr₂_redundant_pair (f : α → β → (σ × σ) → (σ × σ) × γ)
    (h : ∀ x y s, let s' := (f x y (s, s)).fst; s'.fst = s'.snd) :
    (mapAccumr₂ f xs ys (s, s)).snd = (mapAccumr₂ (fun x y (s : σ) =>
      (f x y (s, s) |>.fst.fst, f x y (s, s) |>.snd)
    ) xs ys s).snd :=
  mapAccumr₂_bisim_tail <| by
    use fun (s₁, s₂) s => s₂ = s ∧ s₁ = s
    -- ⊢ (match (s, s) with
    simp_all
    -- 🎉 no goals

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
  -- ⊢ mapAccumr₂ f nil nil s = mapAccumr (fun b s => f default b s) nil s
  case nil => rfl
  -- ⊢ mapAccumr₂ f (snoc xs✝ x✝) (snoc ys✝ y✝) s = mapAccumr (fun b s => f default …
  -- 🎉 no goals
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
  -- ⊢ mapAccumr₂ f nil nil s = mapAccumr (fun a s => f a default s) nil s
  case nil => rfl
  -- ⊢ mapAccumr₂ f (snoc xs✝ x✝) (snoc ys✝ y✝) s = mapAccumr (fun a s => f a defau …
  -- 🎉 no goals
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
  -- ⊢ map₂ f nil nil = map₂ f nil nil
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals

theorem mapAccumr₂_comm (f : α → α → σ → σ × γ) (comm : ∀ a₁ a₂ s, f a₁ a₂ s = f a₂ a₁ s) :
    mapAccumr₂ f xs ys s = mapAccumr₂ f ys xs s := by
  induction xs, ys using Vector.inductionOn₂ generalizing s <;> simp_all
  -- ⊢ mapAccumr₂ f nil nil s = mapAccumr₂ f nil nil s
                                                                -- 🎉 no goals
                                                                -- 🎉 no goals

end Comm

/-!
## Argument Flipping
-/
section Flip
variable (xs : Vector α n) (ys : Vector β n)

theorem map₂_flip (f : α → β → γ) :
    map₂ f xs ys = map₂ (flip f) ys xs := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all[flip]
  -- ⊢ map₂ f nil nil = map₂ (flip f) nil nil
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals

theorem mapAccumr₂_flip (f : α → β → σ → σ × γ) :
    mapAccumr₂ f xs ys s = mapAccumr₂ (flip f) ys xs s := by
  induction xs, ys using Vector.inductionOn₂ <;> simp_all[flip]
  -- ⊢ mapAccumr₂ f nil nil s = mapAccumr₂ (flip f) nil nil s
                                                 -- 🎉 no goals
                                                 -- 🎉 no goals

end Flip

end Vector
