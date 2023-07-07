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


end Vector
