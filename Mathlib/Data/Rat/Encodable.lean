/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Logic.Encodable.Basic
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.NNRat.Defs

/-! # The rationals are `Encodable`.

As a consequence we also get the instance `Countable ℚ`.

This is kept separate from `Data.Rat.Defs` in order to minimize imports.
-/

@[expose] public section


namespace Rat

instance : Encodable ℚ :=
  Encodable.ofEquiv (Σ n : ℤ, { d : ℕ // 0 < d ∧ n.natAbs.Coprime d })
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, Nat.pos_of_ne_zero c, d⟩,
      fun ⟨a, b, c, d⟩ => ⟨a, b, Nat.pos_iff_ne_zero.mp c, d⟩,
      fun _ => rfl, fun ⟨_, _, _, _⟩ => rfl⟩

end Rat

namespace NNRat

instance : Encodable ℚ≥0 :=
  Encodable.ofEquiv (Σ n : ℕ, { d : ℕ // 0 < d ∧ n.Coprime d })
    ⟨fun q => ⟨q.num, q.den, q.den_pos, q.coprime_num_den⟩,
      fun ⟨num, den, prop⟩ => ⟨⟨num, den, Nat.pos_iff_ne_zero.mp prop.1, prop.2⟩,
        Rat.num_nonneg.mp (Int.natCast_nonneg num)⟩,
      fun ⟨⟨num, _, _, _⟩, hq⟩ => by lift num to ℕ using Rat.num_nonneg.mpr hq; rfl,
      Eq.refl⟩

end NNRat
