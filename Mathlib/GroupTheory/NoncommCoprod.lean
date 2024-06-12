/-
Copyright (c) 2023 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
import Mathlib.Algebra.Group.Commute.Hom
import Mathlib.Algebra.Group.Prod

/-!
# Canonical homomorphism from a pair of monoids

This file defines the construction of the canonical homomorphism from a pair of monoids.

Given two morphisms of monoids `f : M →* P` and `g : N →* P` where elements in the images
of the two morphisms commute, we obtain a canonical morphism
`MonoidHom.noncommCoprod : M × N →* P` whose composition with `inl M N` coincides with `f`
and whose composition with `inr M N` coincides with `g`.

There is an analogue `MulHom.noncommCoprod` when `f` and `g` are only `MulHom`s.

## Main theorems:

* `noncommCoprod_comp_inr` and `noncommCoprod_comp_inl` prove that the compositions
  of `MonoidHom.noncommCoprod f g _` with `inl M N` and `inr M N` coincide with `f` and `g`.
* `comp_noncommCoprod` proves that the composition of a morphism of monoids `h`
  with `noncommCoprod f g _` coincides with `noncommCoprod (h.comp f) (h.comp g)`.

For a product of a family of morphisms of monoids, see `MonoidHom.noncommPiCoprod`.
-/

assert_not_exists MonoidWithZero

namespace MulHom

variable {M N P : Type*} [Mul M] [Mul N] [Semigroup P]
  (f : M →ₙ* P) (g : N →ₙ* P) (comm : ∀ m n, Commute (f m) (g n))

/-- Coproduct of two `MulHom`s with the same codomain with `Commute` assumption:
  `f.noncommCoprod g _ (p : M × N) = f p.1 * g p.2`.
  (For the commutative case, use `MulHom.coprod`) -/
@[to_additive (attr := simps)
    "Coproduct of two `AddHom`s with the same codomain with `AddCommute` assumption:
    `f.noncommCoprod g _ (p : M × N) = f p.1 + g p.2`.
    (For the commutative case, use `AddHom.coprod`)"]
def noncommCoprod : M × N →ₙ* P where
  toFun mn := f mn.fst * g mn.snd
  map_mul' mn mn' := by simpa using (comm _ _).mul_mul_mul_comm _ _

@[to_additive]
theorem comp_noncommCoprod {Q : Type*} [Semigroup Q] (h : P →ₙ* Q) :
    h.comp (f.noncommCoprod g comm) =
      (h.comp f).noncommCoprod (h.comp g) (fun m n ↦ (comm m n).map h) :=
  ext fun _ => map_mul h _ _

end MulHom

namespace MonoidHom

variable {M N P : Type*} [MulOneClass M] [MulOneClass N] [Monoid P]
  (f : M →* P) (g : N →* P) (comm : ∀ m n, Commute (f m) (g n))

/-- Coproduct of two `MonoidHom`s with the same codomain,
  with a commutation assumption:
  `f.noncommCoprod g _ (p : M × N) = f p.1 * g p.2`.
  (Noncommutative case; in the commutative case, use `MonoidHom.coprod`.)-/
@[to_additive (attr := simps)
    "Coproduct of two `AddMonoidHom`s with the same codomain,
    with a commutation assumption:
    `f.noncommCoprod g (p : M × N) = f p.1 + g p.2`.
    (Noncommutative case; in the commutative case, use `AddHom.coprod`.)"]
def noncommCoprod : M × N →* P where
  toFun := fun mn ↦ (f mn.fst) * (g mn.snd)
  map_one' := by simp only [Prod.fst_one, Prod.snd_one, map_one, mul_one]
  __ := f.toMulHom.noncommCoprod g.toMulHom comm

@[to_additive (attr := simp)]
theorem noncommCoprod_comp_inl : (f.noncommCoprod g comm).comp (inl M N) = f :=
  ext fun x => by simp

@[to_additive (attr := simp)]
theorem noncommCoprod_comp_inr : (f.noncommCoprod g comm).comp (inr M N) = g :=
  ext fun x => by simp

@[to_additive (attr := simp)]
theorem noncommCoprod_unique (f : M × N →* P) :
    (f.comp (inl M N)).noncommCoprod (f.comp (inr M N)) (fun _ _ => (commute_inl_inr _ _).map f)
      = f :=
  ext fun x => by simp [coprod_apply, inl_apply, inr_apply, ← map_mul]

@[to_additive (attr := simp)]
theorem noncommCoprod_inl_inr {M N : Type*} [Monoid M] [Monoid N]:
    (inl M N).noncommCoprod (inr M N) commute_inl_inr = id (M × N) :=
  noncommCoprod_unique <| .id (M × N)

@[to_additive]
theorem comp_noncommCoprod {Q : Type*} [Monoid Q] (h : P →* Q) :
    h.comp (f.noncommCoprod g comm) =
      (h.comp f).noncommCoprod (h.comp g) (fun m n ↦ (comm m n).map h) :=
  ext fun x => by simp

end MonoidHom
