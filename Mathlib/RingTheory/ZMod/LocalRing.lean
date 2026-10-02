/-
Copyright (c) 2026 Nicola Falciola. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicola Falciola
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# `ZMod (p ^ r)` is a local ring

For a prime `p` and `r ≠ 0`, the reduction map `ZMod (p ^ r) →+* ZMod p` is a local ring
homomorphism into a field, hence `ZMod (p ^ r)` is a local ring.

-/

public section

namespace ZMod

/-- For `r ≠ 0`, the reduction `ZMod (n ^ r) →+* ZMod n` is a local ring homomorphism. -/
theorem isLocalHom_castHom_pow {n r : ℕ} [NeZero n] (hr : r ≠ 0) :
    IsLocalHom (castHom (dvd_pow_self n hr) (ZMod n)) where
  map_nonunit x := by
    obtain ⟨_, rfl⟩ := natCast_zmod_surjective x
    simp [isUnit_iff_coprime, Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hr)]

/-- `ZMod (p ^ r)` is a local ring for `p` prime and `r ≠ 0`. -/
instance isLocalRing_pow (p r : ℕ) [Fact p.Prime] [NeZero r] : IsLocalRing (ZMod (p ^ r)) :=
  have := isLocalHom_castHom_pow (n := p) (NeZero.ne r)
  (castHom (dvd_pow_self p (NeZero.ne r)) (ZMod p)).domain_isLocalRing

end ZMod
