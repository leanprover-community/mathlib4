/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Batteries.Data.Fin.Lemmas
public import Mathlib.Order.Fin.Basic
public import Mathlib.Order.MinMax

/-!
# Lemmas about `Fin.clamp`

-/

namespace Fin

<<<<<<< HEAD
public lemma clamp_mono {m : ℕ} : Monotone (fun n ↦ clamp n m) := by
=======
public lemma clamp_monotone {m : ℕ} : Monotone (fun n ↦ clamp n m) := by
>>>>>>> origin/spectral-sequences-2-cycles-2
  intro a b h
  rw [le_iff_val_le_val]
  exact min_le_min_right m h

<<<<<<< HEAD
public lemma clamp_eq_last (n m : ℕ) (hnm : m ≤ n) :
=======
public lemma clamp_eq_last (n m : ℕ) (hmn : m ≤ n) :
>>>>>>> origin/spectral-sequences-2-cycles-2
    clamp n m = last _ := by
  ext
  simpa

end Fin
