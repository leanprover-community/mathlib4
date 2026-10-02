/-
Copyright (c) 2026 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.Matrix.Cartan
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import Mathlib.LinearAlgebra.RootSystem.OfBilinear

/-!
# The classification of root systems.

-/

namespace RootPairing

variable
  {ι : Type*} [Finite ι]
  {K : Type*} [Field K] [CharZero K]
  {M : Type*} [AddCommGroup M] [Module K M]
  {N : Type*} [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N}

def Base.HasCM {n : Type*} [P.IsCrystallographic] (bs : P.Base) (A : Matrix n n ℤ) :=
  ∃ e, bs.cartanMatrix.reindex e e = A

/-! *Uniqueness*

Note that we already have `RootPairing.Base.equivOfCartanMatrixEq` so the statement below about
Cartan matrices really is all that is required. Note also that the triple-bond case is essentially
`RootPairing.IsG2.card_base_support_eq_two` (+ related API).

-/

theorem_wanted Base.hasCM_A_or_B_or_C_or_D_or_E_or_F_or_G
    [P.IsReduced] [P.IsCrystallographic] [P.IsIrreducible] [P.IsRootSystem]
    (bs : P.Base) :
    (∃ n, bs.HasCM (CartanMatrix.A n)) ∨
    (∃ n, bs.HasCM (CartanMatrix.B n)) ∨
    (∃ n, bs.HasCM (CartanMatrix.C n)) ∨
    (∃ n, bs.HasCM (CartanMatrix.D n)) ∨
    bs.HasCM (CartanMatrix.E 6) ∨
    bs.HasCM (CartanMatrix.E 7) ∨
    bs.HasCM (CartanMatrix.E 8) ∨
    bs.HasCM CartanMatrix.F₄ ∨
    bs.HasCM CartanMatrix.G₂

/-! *Existence*

Probably the best route is to construct these by developing further API for `RootPairing.ofBilinear`
and then invoking it with appropriate matrices over `ℤ`.

-/

variable (ι K M N) (n : ℕ) [NeZero n]

def_wanted a : RootPairing (Fin <| n * (n + 1)) K M N
instance_wanted : (❰a❱ K M N n).IsReduced
instance_wanted : (❰a❱ K M N n).IsIrreducible
instance_wanted : (❰a❱ K M N n).IsValuedIn ℤ
instance_wanted : (❰a❱ K M N n).IsRootSystem
theorem_wanted a_hasCM_a : ∀ bs : (❰a❱ K M N n).Base, bs.HasCM (CartanMatrix.A n)

def_wanted b : RootPairing (Fin <| 2 * n * n) K M N
instance_wanted : (❰b❱ K M N n).IsReduced
instance_wanted : (❰b❱ K M N n).IsIrreducible
instance_wanted : (❰b❱ K M N n).IsValuedIn ℤ
instance_wanted : (❰b❱ K M N n).IsRootSystem
theorem_wanted b_hasCM_b : ∀ bs : (❰b❱ K M N n).Base, bs.HasCM (CartanMatrix.B n)

def_wanted c : RootPairing (Fin <| 2 * n * n) K M N
instance_wanted : (❰c❱ K M N n).IsReduced
instance_wanted : (❰c❱ K M N n).IsIrreducible
instance_wanted : (❰c❱ K M N n).IsValuedIn ℤ
instance_wanted : (❰c❱ K M N n).IsRootSystem
theorem_wanted c_hasCM_c : ∀ bs : (❰c❱ K M N n).Base, bs.HasCM (CartanMatrix.C n)

def_wanted d : RootPairing (Fin <| 2 * n * (n - 1)) K M N
instance_wanted : (❰d❱ K M N n).IsReduced
theorem_wanted d_isIrreducible (hn : n ≠ 2) : (❰d❱ K M N n).IsIrreducible
instance_wanted : (❰d❱ K M N n).IsValuedIn ℤ
instance_wanted : (❰d❱ K M N n).IsRootSystem
theorem_wanted d_hasCM_d : ∀ bs : (❰d❱ K M N n).Base, bs.HasCM (CartanMatrix.D n)

def_wanted e₆ : RootPairing (Fin 72) K M N
instance_wanted : (❰e₆❱ K M N).IsReduced
instance_wanted : (❰e₆❱ K M N).IsIrreducible
instance_wanted : (❰e₆❱ K M N).IsValuedIn ℤ
instance_wanted : (❰e₆❱ K M N).IsRootSystem
theorem_wanted e₆_hasCM_e₆ : ∀ bs : (❰e₆❱ K M N).Base, bs.HasCM (CartanMatrix.E 6)

def_wanted e₇ : RootPairing (Fin 126) K M N
instance_wanted : (❰e₇❱ K M N).IsReduced
instance_wanted : (❰e₇❱ K M N).IsIrreducible
instance_wanted : (❰e₇❱ K M N).IsValuedIn ℤ
instance_wanted : (❰e₇❱ K M N).IsRootSystem
theorem_wanted e₇_hasCM_e₇ : ∀ bs : (❰e₇❱ K M N).Base, bs.HasCM (CartanMatrix.E 7)

def_wanted e₈ : RootPairing (Fin 240) K M N
instance_wanted : (❰e₈❱ K M N).IsReduced
instance_wanted : (❰e₈❱ K M N).IsIrreducible
instance_wanted : (❰e₈❱ K M N).IsValuedIn ℤ
instance_wanted : (❰e₈❱ K M N).IsRootSystem
theorem_wanted e₈_hasCM_e₈ : ∀ bs : (❰e₈❱ K M N).Base, bs.HasCM (CartanMatrix.E 8)

def_wanted f₄ : RootPairing (Fin 48) K M N
instance_wanted : (❰f₄❱ K M N).IsReduced
instance_wanted : (❰f₄❱ K M N).IsIrreducible
instance_wanted : (❰f₄❱ K M N).IsValuedIn ℤ
instance_wanted : (❰f₄❱ K M N).IsRootSystem
theorem_wanted f₄_hasCM_f₄ : ∀ bs : (❰f₄❱ K M N).Base, bs.HasCM CartanMatrix.F₄

def_wanted g₂ : RootPairing (Fin 12) K M N
instance_wanted : (❰g₂❱ K M N).IsReduced
instance_wanted : (❰g₂❱ K M N).IsIrreducible
instance_wanted : (❰g₂❱ K M N).IsValuedIn ℤ
instance_wanted : (❰g₂❱ K M N).IsRootSystem
theorem_wanted g₂_hasCM_g₂ : ∀ bs : (❰g₂❱ K M N).Base, bs.HasCM CartanMatrix.G₂

end RootPairing
