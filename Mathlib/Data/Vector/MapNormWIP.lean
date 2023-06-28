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
  /--
    Given a nested vector, where the inner vectors are non-empty, we can separate the head and tail
    of each inner vector
  -/
  def dest_nested : {m : ℕ} → Vector (Vector α (n+1)) m → Vector α m × Vector (Vector α n) m
    | 0,    _             => (Vector.nil, Vector.nil)
    | _+1,  ⟨v :: vs, h⟩  =>
        let r := dest_nested ⟨vs, by simp_all[h]⟩
        (
          v.head ::ᵥ r.1,
          v.tail ::ᵥ r.2
        )

  /--
    Given a nested vector, where the inner vectors are non-empty, return a vector with the head of
    each inner vector
  -/
  def head_nested (vs : Vector (Vector α (n+1)) m) : Vector α m :=
    (dest_nested vs).fst

  /--
    Given a nested vector, where the inner vectors are non-empty, return a nested vector with the
    tail of each inner vector
  -/
  def tail_nested (vs : Vector (Vector α (n+1)) m) : Vector (Vector α n) m :=
    (dest_nested vs).snd

  /--
    Map an `n`-ary function over `n` vectors
  -/
  def mapₙ {n : ℕ} (f : Vector α n → β) : {m : ℕ} → Vector (Vector α m) n → Vector β m
    | 0,   _  => Vector.nil
    | _+1, vs => f vs.head_nested ::ᵥ mapₙ f vs.tail_nested

  /--
    Map an `n`-ary function over `n` vectors, right-to-left, while accumulating a state.
    Returns both the final state, and the mapped vector
  -/
  def mapAccumrₙ {n : ℕ} (f : Vector α n → σ → σ × β) :
      {m : ℕ} → Vector (Vector α m) n → σ → σ × Vector β m
    | 0,   _,   s => (s, Vector.nil)
    | _+1, vs,  s =>
        let r := mapAccumrₙ f vs.tail_nested s
        let z := f vs.head_nested r.1
        (z.1, z.2 ::ᵥ r.2)

  /-!
  ## Normalization
  Try to rewrite all operations in terms of `mapAccumr`
  -/
  section Norm

    section Unary
      variable (xs : Vector α n)

      -- @[aesop norm]
      theorem map_to_mapAccumr (f : α → β) :
          map f xs = (mapAccumr (fun x _ => (⟨⟩, f x)) xs ()).snd := by
        induction xs using revInductionOn <;> simp_all

    end Unary

    section Binary
      variable (xs : Vector α n) (ys : Vector β n)

      -- @[aesop norm]
      theorem map₂_to_mapAccumr₂ (f : α → β → γ) :
          map₂ f xs ys = (mapAccumr₂ (fun x y _ => (⟨⟩, f x y)) xs ys ()).snd := by
        induction xs, ys using revInductionOn₂ <;> simp_all

    end Binary

    section NAry
      variable (xs : Vector (Vector α m) n)

    end NAry

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
  ## Redundant state optimization
  If an accumulation function `f`, given an initial state `s`, produces `s` as its output state
  for all possible input bits, then the state is redundant and can be optimized out
  -/
  section RedundantState
    variable (xs : Vector α n) (ys : Vector β n)

    @[simp]
    theorem mapAccumr_redundant_state (f : α → σ → σ × β) (s : σ) (h : ∀ a, (f a s).fst = s) :
        mapAccumr f xs s = (s, (map (fun x => (f x s).snd) xs)) := by
      clear ys
      induction xs using revInductionOn <;> simp_all

    @[simp]
    theorem mapAccumr₂_redundant_state (f : α → β → σ → σ × γ) (s : σ) (h : ∀ a b, (f a b s).fst = s) :
        mapAccumr₂ f xs ys s = (s, (map₂ (fun x y => (f x y s).snd) xs ys)) := by
      induction xs, ys using revInductionOn₂ <;> simp_all

    /-- If `f` takes a pair of states, but always returns the same value for both elements of the
        pair, then we don't actually need the pair
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
        pair, then we don't actually need the pair
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


    -- @[simp]
    theorem mapAccumr₂_unused_input_left  [Inhabited α]
                                          (f : α → β → σ → σ × γ)
                                          (h : ∀ a b s, f Inhabited.default b s = f a b s) :
        mapAccumr₂ f xs ys s = mapAccumr (fun b s => f Inhabited.default b s) ys s := by
      induction xs, ys using Vector.revInductionOn₂ generalizing s
      case nil => rfl
      case snoc xs ys x y ih =>
        simp[h x y s, ih]

    -- @[simp]
    theorem mapAccumr₂_unused_input_right [Inhabited β]
                                          (f : α → β → σ → σ × γ)
                                          (h : ∀ a b s, f a Inhabited.default s = f a b s) :
        mapAccumr₂ f xs ys s = mapAccumr (fun a s => f a Inhabited.default s) xs s := by
      induction xs, ys using Vector.revInductionOn₂ generalizing s
      case nil => rfl
      case snoc xs ys x y ih =>
        simp[h x y s, ih]

  end RedundantState



  /-
  ### Bisimulation
  When are two `mapAccumr` applications equal
  -/
  section Congr
    section Unary
      variable (xs : Vector α n) (f : α → σ → σ × β) (g : α → σ' → σ' × β)

      @[simp, aesop 90%]
      theorem mapAccumr_bisim_snd (R : σ → σ' → Prop)
                                  (h : ∀ x s s', R s s' →
                                        R (f x s).fst (g x s').fst ∧ (f x s).snd = (g x s').snd) :
          ∀ s s', R s s' → (mapAccumr f xs s).snd = (mapAccumr g xs s').snd := by
        induction xs using revInductionOn
        case nil => intros; rfl
        case snoc xs x ih =>
          intros s s' hR;
          rcases (h x s s' hR) with ⟨hR1, hR2⟩
          specialize ih _ _ hR1
          simp_all


      -- @[simp, aesop 90%]
      -- theorem mapAccumr_map_congr_fun (f : α → σ → σ × α) (h : ∀ xs c, (f xs c).snd = g xs) :
      --     (mapAccumr f xs c).snd = map g xs := by
      --   induction xs using revInductionOn generalizing c <;> simp[*]

      -- @[simp, aesop 90%]
      -- theorem mapAccumr_map_congr_fun' (f : α → σ → σ × α) (c : σ) (h : ∀ xs, (f xs c) = (c, g xs)) :
      --     (mapAccumr f xs c).snd = map g xs := by
      --   induction xs using revInductionOn generalizing c <;> simp[*]
    end Unary

    section Binary
      variable (xs : Vector α n) (ys : Vector β n) (f : α → β → σ → σ × γ) (g : α → β → σ' → σ' × γ)

      @[simp, aesop 90%]
      theorem mapAccumr₂_bisim_snd (R : σ → σ' → Prop)
                                  (h : ∀ x y s s', R s s' →
                                        R (f x y s).fst (g x y s').fst ∧ (f x y s).snd = (g x y s').snd) :
          ∀ s s', R s s' → (mapAccumr₂ f xs ys s).snd = (mapAccumr₂ g xs ys s').snd := by
        induction xs, ys using revInductionOn₂
        case nil => intros; rfl
        case snoc xs ys x y ih =>
          intros s s' hR;
          rcases (h x y s s' hR) with ⟨hR1, hR2⟩
          specialize ih _ _ hR1
          simp_all

      -- @[simp, aesop 90%]
      -- theorem mapAccumr₂_congr_fun_snd (h : f = g) :
      --     (Vector.mapAccumr₂ f xs ys c).snd = (Vector.mapAccumr₂ g xs ys c).snd := by
      --   congr

      -- @[simp, aesop 90%]
      -- theorem mapAccumr₂_congr_fun_symm_snd (h : ∀ x y, f x y = g y x) :
      --     (Vector.mapAccumr₂ f xs ys c).snd = (Vector.mapAccumr₂ g ys xs c).snd := by
      --   induction xs, ys using Vector.revInductionOn₂ generalizing c <;> simp[*]

    end Binary
  end Congr
end Vector
