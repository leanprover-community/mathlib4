/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.GroupTheory.Congruence
import Mathlib.GroupTheory.Submonoid.Membership
import Mathlib.Algebra.Group.Units

#align_import group_theory.monoid_localization from "leanprover-community/mathlib"@"10ee941346c27bdb5e87bb3535100c0b1f08ac41"

/-!
# Localizations of commutative monoids

Localizing a commutative ring at one of its submonoids does not rely on the ring's addition, so
we can generalize localizations to commutative monoids.

We characterize the localization of a commutative monoid `M` at a submonoid `S` up to
isomorphism; that is, a commutative monoid `N` is the localization of `M` at `S` iff we can find a
monoid homomorphism `f : M →* N` satisfying 3 properties:
1. For all `y ∈ S`, `f y` is a unit;
2. For all `z : N`, there exists `(x, y) : M × S` such that `z * f y = f x`;
3. For all `x, y : M`, `f x = f y` iff there exists `c ∈ S` such that `x * c = y * c`.

Given such a localization map `f : M →* N`, we can define the surjection
`Submonoid.LocalizationMap.mk'` sending `(x, y) : M × S` to `f x * (f y)⁻¹`, and
`Submonoid.LocalizationMap.lift`, the homomorphism from `N` induced by a homomorphism from `M` which
maps elements of `S` to invertible elements of the codomain. Similarly, given commutative monoids
`P, Q`, a submonoid `T` of `P` and a localization map for `T` from `P` to `Q`, then a homomorphism
`g : M →* P` such that `g(S) ⊆ T` induces a homomorphism of localizations, `LocalizationMap.map`,
from `N` to `Q`.  We treat the special case of localizing away from an element in the sections
`AwayMap` and `Away`.

We also define the quotient of `M × S` by the unique congruence relation (equivalence relation
preserving a binary operation) `r` such that for any other congruence relation `s` on `M × S`
satisfying '`∀ y ∈ S`, `(1, 1) ∼ (y, y)` under `s`', we have that `(x₁, y₁) ∼ (x₂, y₂)` by `s`
whenever `(x₁, y₁) ∼ (x₂, y₂)` by `r`. We show this relation is equivalent to the standard
localization relation.
This defines the localization as a quotient type, `Localization`, but the majority of
subsequent lemmas in the file are given in terms of localizations up to isomorphism, using maps
which satisfy the characteristic predicate.

The Grothendieck group construction corresponds to localizing at the top submonoid, namely making
every element invertible.

## Implementation notes

In maths it is natural to reason up to isomorphism, but in Lean we cannot naturally `rewrite` one
structure with an isomorphic one; one way around this is to isolate a predicate characterizing
a structure up to isomorphism, and reason about things that satisfy the predicate.

The infimum form of the localization congruence relation is chosen as 'canonical' here, since it
shortens some proofs.

To apply a localization map `f` as a function, we use `f.toMap`, as coercions don't work well for
this structure.

To reason about the localization as a quotient type, use `mk_eq_monoidOf_mk'` and associated
lemmas. These show the quotient map `mk : M → S → Localization S` equals the
surjection `LocalizationMap.mk'` induced by the map
`Localization.monoidOf : Submonoid.LocalizationMap S (Localization S)` (where `of` establishes the
localization as a quotient type satisfies the characteristic predicate). The lemma
`mk_eq_monoidOf_mk'` hence gives you access to the results in the rest of the file, which are about
the `LocalizationMap.mk'` induced by any localization map.

## TODO

* Show that the localization at the top monoid is a group.
* Generalise to (nonempty) subsemigroups.
* If we acquire more bundlings, we can make `Localization.mkOrderEmbedding` be an ordered monoid
  embedding.

## Tags
localization, monoid localization, quotient monoid, congruence relation, characteristic predicate,
commutative monoid, grothendieck group
-/

open Function
namespace AddSubmonoid

variable {M : Type*} [AddCommMonoid M] (S : AddSubmonoid M) (N : Type*) [AddCommMonoid N]

/-- The type of AddMonoid homomorphisms satisfying the characteristic predicate: if `f : M →+ N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
-- Porting note: This linter does not exist yet
-- @[nolint has_nonempty_instance]
structure LocalizationMap extends AddMonoidHom M N where
  map_add_units' : ∀ y : S, IsAddUnit (toFun y)
  surj' : ∀ z : N, ∃ x : M × S, z + toFun x.2 = toFun x.1
  eq_iff_exists' : ∀ x y, toFun x = toFun y ↔ ∃ c : S, ↑c + x = ↑c + y
#align add_submonoid.localization_map AddSubmonoid.LocalizationMap

-- Porting note: no docstrings for AddSubmonoid.LocalizationMap
attribute [nolint docBlame] AddSubmonoid.LocalizationMap.map_add_units'
  AddSubmonoid.LocalizationMap.surj' AddSubmonoid.LocalizationMap.eq_iff_exists'

/-- The AddMonoidHom underlying a `LocalizationMap` of `AddCommMonoid`s. -/
add_decl_doc LocalizationMap.toAddMonoidHom

end AddSubmonoid

section CommMonoid

variable {M : Type*} [CommMonoid M] (S : Submonoid M) (N : Type*) [CommMonoid N] {P : Type*}
  [CommMonoid P]

namespace Submonoid

/-- The type of monoid homomorphisms satisfying the characteristic predicate: if `f : M →* N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
-- Porting note: This linter does not exist yet
-- @[nolint has_nonempty_instance]
structure LocalizationMap extends MonoidHom M N where
  map_units' : ∀ y : S, IsUnit (toFun y)
  surj' : ∀ z : N, ∃ x : M × S, z * toFun x.2 = toFun x.1
  eq_iff_exists' : ∀ x y, toFun x = toFun y ↔ ∃ c : S, ↑c * x = c * y
#align submonoid.localization_map Submonoid.LocalizationMap

-- Porting note: no docstrings for Submonoid.LocalizationMap
attribute [nolint docBlame] Submonoid.LocalizationMap.map_units' Submonoid.LocalizationMap.surj'
  Submonoid.LocalizationMap.eq_iff_exists'

attribute [to_additive] Submonoid.LocalizationMap

-- Porting note: this translation already exists
-- attribute [to_additive] Submonoid.LocalizationMap.toMonoidHom

/-- The monoid hom underlying a `LocalizationMap`. -/
add_decl_doc LocalizationMap.toMonoidHom

end Submonoid

namespace Localization

-- Porting note: this does not work so it is done explicitly instead
-- run_cmd to_additive.map_namespace `Localization `AddLocalization
-- run_cmd Elab.Command.liftCoreM <| ToAdditive.insertTranslation `Localization `AddLocalization

/-- The congruence relation on `M × S`, `M` a `CommMonoid` and `S` a submonoid of `M`, whose
quotient is the localization of `M` at `S`, defined as the unique congruence relation on
`M × S` such that for any other congruence relation `s` on `M × S` where for all `y ∈ S`,
`(1, 1) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
`(x₁, y₁) ∼ (x₂, y₂)` by `s`. -/
@[to_additive AddLocalization.r
    "The congruence relation on `M × S`, `M` an `AddCommMonoid` and `S` an `add_submonoid` of `M`,
whose quotient is the localization of `M` at `S`, defined as the unique congruence relation on
`M × S` such that for any other congruence relation `s` on `M × S` where for all `y ∈ S`,
`(0, 0) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
`(x₁, y₁) ∼ (x₂, y₂)` by `s`."]
def r (S : Submonoid M) : Con (M × S) :=
  sInf { c | ∀ y : S, c 1 (y, y) }
#align localization.r Localization.r
#align add_localization.r AddLocalization.r

/-- An alternate form of the congruence relation on `M × S`, `M` a `CommMonoid` and `S` a
submonoid of `M`, whose quotient is the localization of `M` at `S`. -/
@[to_additive AddLocalization.r'
    "An alternate form of the congruence relation on `M × S`, `M` a `CommMonoid` and `S` a
submonoid of `M`, whose quotient is the localization of `M` at `S`."]
def r' : Con (M × S) := by
  -- note we multiply by `c` on the left so that we can later generalize to `•`
  refine
    { r := fun a b : M × S ↦ ∃ c : S, ↑c * (↑b.2 * a.1) = c * (a.2 * b.1)
      iseqv := ⟨fun a ↦ ⟨1, rfl⟩, fun ⟨c, hc⟩ ↦ ⟨c, hc.symm⟩, ?_⟩
      mul' := ?_ }
  · rintro a b c ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    -- ⊢ ∃ c_1, ↑c_1 * (↑c.snd * a.fst) = ↑c_1 * (↑a.snd * c.fst)
    use t₂ * t₁ * b.2
    -- ⊢ ↑(t₂ * t₁ * b.snd) * (↑c.snd * a.fst) = ↑(t₂ * t₁ * b.snd) * (↑a.snd * c.fst)
    simp only [Submonoid.coe_mul]
    -- ⊢ ↑t₂ * ↑t₁ * ↑b.snd * (↑c.snd * a.fst) = ↑t₂ * ↑t₁ * ↑b.snd * (↑a.snd * c.fst)
    calc
      (t₂ * t₁ * b.2 : M) * (c.2 * a.1) = t₂ * c.2 * (t₁ * (b.2 * a.1)) := by ac_rfl
      _ = t₁ * a.2 * (t₂ * (c.2 * b.1)) := by rw [ht₁]; ac_rfl
      _ = t₂ * t₁ * b.2 * (a.2 * c.1) := by rw [ht₂]; ac_rfl
  · rintro a b c d ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    -- ⊢ Setoid.r (a * c) (b * d)
    use t₂ * t₁
    -- ⊢ ↑(t₂ * t₁) * (↑(b * d).snd * (a * c).fst) = ↑(t₂ * t₁) * (↑(a * c).snd * (b  …
    calc
      (t₂ * t₁ : M) * (b.2 * d.2 * (a.1 * c.1)) = t₂ * (d.2 * c.1) * (t₁ * (b.2 * a.1)) := by ac_rfl
      _ = (t₂ * t₁ : M) * (a.2 * c.2 * (b.1 * d.1)) := by rw [ht₁, ht₂]; ac_rfl
#align localization.r' Localization.r'
#align add_localization.r' AddLocalization.r'

/-- The congruence relation used to localize a `CommMonoid` at a submonoid can be expressed
equivalently as an infimum (see `Localization.r`) or explicitly
(see `Localization.r'`). -/
@[to_additive AddLocalization.r_eq_r'
    "The additive congruence relation used to localize an `AddCommMonoid` at a submonoid can be
expressed equivalently as an infimum (see `AddLocalization.r`) or explicitly
(see `AddLocalization.r'`)."]
theorem r_eq_r' : r S = r' S :=
  le_antisymm (sInf_le fun _ ↦ ⟨1, by simp⟩) <|
                                      -- 🎉 no goals
    le_sInf fun b H ⟨p, q⟩ ⟨x, y⟩ ⟨t, ht⟩ ↦ by
      rw [← one_mul (p, q), ← one_mul (x, y)]
      -- ⊢ ↑b (1 * (p, q)) (1 * (x, y))
      refine b.trans (b.mul (H (t * y)) (b.refl _)) ?_
      -- ⊢ ↑b ((↑(t * y), t * y) * (p, q)) (1 * (x, y))
      convert b.symm (b.mul (H (t * q)) (b.refl (x, y))) using 1
      -- ⊢ (↑(t * y), t * y) * (p, q) = (↑(t * q), t * q) * (x, y)
      dsimp only [Prod.mk_mul_mk, Submonoid.coe_mul] at ht ⊢
      -- ⊢ (↑t * ↑y * p, t * y * q) = (↑t * ↑q * x, t * q * y)
      simp_rw [mul_assoc, ht, mul_comm y q]
      -- 🎉 no goals
#align localization.r_eq_r' Localization.r_eq_r'
#align add_localization.r_eq_r' AddLocalization.r_eq_r'

variable {S}

@[to_additive AddLocalization.r_iff_exists]
theorem r_iff_exists {x y : M × S} : r S x y ↔ ∃ c : S, ↑c * (↑y.2 * x.1) = c * (x.2 * y.1) := by
  rw [r_eq_r' S]; rfl
  -- ⊢ ↑(r' S) x y ↔ ∃ c, ↑c * (↑y.snd * x.fst) = ↑c * (↑x.snd * y.fst)
                  -- 🎉 no goals
#align localization.r_iff_exists Localization.r_iff_exists
#align add_localization.r_iff_exists AddLocalization.r_iff_exists

end Localization

/-- The localization of a `CommMonoid` at one of its submonoids (as a quotient type). -/
@[to_additive AddLocalization
    "The localization of an `AddCommMonoid` at one of its submonoids (as a quotient type)."]
def Localization := (Localization.r S).Quotient
#align localization Localization
#align add_localization AddLocalization

namespace Localization

@[to_additive]
instance inhabited : Inhabited (Localization S) := Con.Quotient.inhabited
#align localization.inhabited Localization.inhabited
#align add_localization.inhabited AddLocalization.inhabited

/-- Multiplication in a `Localization` is defined as `⟨a, b⟩ * ⟨c, d⟩ = ⟨a * c, b * d⟩`. -/
@[to_additive "Addition in an `AddLocalization` is defined as `⟨a, b⟩ + ⟨c, d⟩ = ⟨a + c, b + d⟩`.
Should not be confused with the ring localization counterpart `Localization.add`, which maps
`⟨a, b⟩ + ⟨c, d⟩` to `⟨d * a + b * c, b * d⟩`."]
protected irreducible_def mul : Localization S → Localization S → Localization S :=
  (r S).commMonoid.mul
#align localization.mul Localization.mul
#align add_localization.add AddLocalization.add

@[to_additive]
instance : Mul (Localization S) := ⟨Localization.mul S⟩

/-- The identity element of a `Localization` is defined as `⟨1, 1⟩`. -/
@[to_additive "The identity element of an `AddLocalization` is defined as `⟨0, 0⟩`.

Should not be confused with the ring localization counterpart `Localization.zero`,
which is defined as `⟨0, 1⟩`."]
protected irreducible_def one : Localization S := (r S).commMonoid.one
#align localization.one Localization.one
#align add_localization.zero AddLocalization.zero

@[to_additive]
instance : One (Localization S) := ⟨Localization.one S⟩

/-- Exponentiation in a `Localization` is defined as `⟨a, b⟩ ^ n = ⟨a ^ n, b ^ n⟩`.

This is a separate `irreducible` def to ensure the elaborator doesn't waste its time
trying to unify some huge recursive definition with itself, but unfolded one step less.
-/
@[to_additive "Multiplication with a natural in an `AddLocalization` is defined as
`n • ⟨a, b⟩ = ⟨n • a, n • b⟩`.

This is a separate `irreducible` def to ensure the elaborator doesn't waste its time
trying to unify some huge recursive definition with itself, but unfolded one step less."]
protected irreducible_def npow : ℕ → Localization S → Localization S := (r S).commMonoid.npow
#align localization.npow Localization.npow
#align add_localization.nsmul AddLocalization.nsmul

@[to_additive]
instance commMonoid : CommMonoid (Localization S) where
  mul := (· * ·)
  one := 1
  mul_assoc x y z := show (x.mul S y).mul S z = x.mul S (y.mul S z) by
    rw [Localization.mul]; apply (r S).commMonoid.mul_assoc
    -- ⊢ Mul.mul (Mul.mul x y) z = Mul.mul x (Mul.mul y z)
                           -- 🎉 no goals
  mul_comm x y := show x.mul S y = y.mul S x by
    rw [Localization.mul]; apply (r S).commMonoid.mul_comm
    -- ⊢ Mul.mul x y = Mul.mul y x
                           -- 🎉 no goals
    -- ⊢ Mul.mul x One.one = x
                                             -- 🎉 no goals
    -- ⊢ Mul.mul One.one x = x
                                             -- 🎉 no goals
  mul_one x := show x.mul S (.one S) = x by
    rw [Localization.mul, Localization.one]; apply (r S).commMonoid.mul_one
  one_mul x := show (Localization.one S).mul S x = x by
    rw [Localization.mul, Localization.one]; apply (r S).commMonoid.one_mul
  npow := Localization.npow S
    -- ⊢ Monoid.npow 0 x = One.one
                                              -- 🎉 no goals
  npow_zero x := show Localization.npow S 0 x = .one S by
    rw [Localization.npow, Localization.one]; apply (r S).commMonoid.npow_zero
    -- ⊢ Monoid.npow (Nat.succ n) x = Mul.mul x (Monoid.npow n x)
                                              -- 🎉 no goals
  npow_succ n x := show .npow S n.succ x = x.mul S (.npow S n x) by
    rw [Localization.npow, Localization.mul]; apply (r S).commMonoid.npow_succ

variable {S}

/-- Given a `CommMonoid` `M` and submonoid `S`, `mk` sends `x : M`, `y ∈ S` to the equivalence
class of `(x, y)` in the localization of `M` at `S`. -/
@[to_additive
    "Given an `AddCommMonoid` `M` and submonoid `S`, `mk` sends `x : M`, `y ∈ S` to
the equivalence class of `(x, y)` in the localization of `M` at `S`."]
def mk (x : M) (y : S) : Localization S := (r S).mk' (x, y)
#align localization.mk Localization.mk
#align add_localization.mk AddLocalization.mk

@[to_additive]
theorem mk_eq_mk_iff {a c : M} {b d : S} : mk a b = mk c d ↔ r S ⟨a, b⟩ ⟨c, d⟩ := (r S).eq
#align localization.mk_eq_mk_iff Localization.mk_eq_mk_iff
#align add_localization.mk_eq_mk_iff AddLocalization.mk_eq_mk_iff

universe u

/-- Dependent recursion principle for `Localizations`: given elements `f a b : p (mk a b)`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d` (with the correct coercions),
then `f` is defined on the whole `Localization S`. -/
@[to_additive (attr := elab_as_elim)
    "Dependent recursion principle for `AddLocalizations`: given elements `f a b : p (mk a b)`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d` (with the correct coercions),
then `f` is defined on the whole `AddLocalization S`."]
def rec {p : Localization S → Sort u} (f : ∀ (a : M) (b : S), p (mk a b))
    (H : ∀ {a c : M} {b d : S} (h : r S (a, b) (c, d)),
      (Eq.ndrec (f a b) (mk_eq_mk_iff.mpr h) : p (mk c d)) = f c d) (x) : p x :=
  Quot.rec (fun y ↦ Eq.ndrec (f y.1 y.2) (by rfl)) (fun y z h ↦ by cases y; cases z; exact H h) x
                                             -- 🎉 no goals
                                                                   -- ⊢ (_ : Quot.mk Setoid.r (fst✝, snd✝) = Quot.mk Setoid.r z) ▸ (fun y => (_ : mk …
                                                                            -- ⊢ (_ : Quot.mk Setoid.r (fst✝¹, snd✝¹) = Quot.mk Setoid.r (fst✝, snd✝)) ▸ (fun …
                                                                                     -- 🎉 no goals
#align localization.rec Localization.rec
#align add_localization.rec AddLocalization.rec

/-- Copy of `Quotient.recOnSubsingleton₂` for `Localization` -/
@[to_additive (attr := elab_as_elim) "Copy of `Quotient.recOnSubsingleton₂` for `AddLocalization`"]
def recOnSubsingleton₂ {r : Localization S → Localization S → Sort u}
    [h : ∀ (a c : M) (b d : S), Subsingleton (r (mk a b) (mk c d))] (x y : Localization S)
    (f : ∀ (a c : M) (b d : S), r (mk a b) (mk c d)) : r x y :=
  @Quotient.recOnSubsingleton₂' _ _ _ _ r (Prod.rec fun _ _ => Prod.rec fun _ _ => h _ _ _ _) x y
    (Prod.rec fun _ _ => Prod.rec fun _ _ => f _ _ _ _)
#align localization.rec_on_subsingleton₂ Localization.recOnSubsingleton₂
#align add_localization.rec_on_subsingleton₂ AddLocalization.recOnSubsingleton₂

@[to_additive]
theorem mk_mul (a c : M) (b d : S) : mk a b * mk c d = mk (a * c) (b * d) :=
  show Localization.mul S _ _ = _ by rw [Localization.mul]; rfl
                                     -- ⊢ Mul.mul (mk a b) (mk c d) = mk (a * c) (b * d)
                                                            -- 🎉 no goals
#align localization.mk_mul Localization.mk_mul
#align add_localization.mk_add AddLocalization.mk_add

@[to_additive]
theorem mk_one : mk 1 (1 : S) = 1 :=
  show mk _ _ = .one S by rw [Localization.one]; rfl
                          -- ⊢ mk 1 1 = One.one
                                                 -- 🎉 no goals
#align localization.mk_one Localization.mk_one
#align add_localization.mk_zero AddLocalization.mk_zero

@[to_additive]
theorem mk_pow (n : ℕ) (a : M) (b : S) : mk a b ^ n = mk (a ^ n) (b ^ n) :=
  show Localization.npow S _ _ = _ by rw [Localization.npow]; rfl
                                      -- ⊢ Monoid.npow n (mk a b) = mk (a ^ n) (b ^ n)
                                                              -- 🎉 no goals
#align localization.mk_pow Localization.mk_pow
#align add_localization.mk_nsmul AddLocalization.mk_nsmul

-- Porting note: mathport translated `rec` to `ndrec` in the name of this lemma
@[to_additive (attr := simp)]
theorem ndrec_mk {p : Localization S → Sort u} (f : ∀ (a : M) (b : S), p (mk a b)) (H) (a : M)
    (b : S) : (rec f H (mk a b) : p (mk a b)) = f a b := rfl
#align localization.rec_mk Localization.ndrec_mk
#align add_localization.rec_mk AddLocalization.ndrec_mk

/-- Non-dependent recursion principle for localizations: given elements `f a b : p`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d`,
then `f` is defined on the whole `Localization S`. -/
-- Porting note: the attribute `elab_as_elim` fails with `unexpected eliminator resulting type p`
-- @[to_additive (attr := elab_as_elim)
@[to_additive
    "Non-dependent recursion principle for `AddLocalization`s: given elements `f a b : p`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d`,
then `f` is defined on the whole `Localization S`."]
def liftOn {p : Sort u} (x : Localization S) (f : M → S → p)
    (H : ∀ {a c : M} {b d : S} (_ : r S (a, b) (c, d)), f a b = f c d) : p :=
  rec f (fun h ↦ (by simpa only [eq_rec_constant] using H h)) x
                     -- 🎉 no goals
#align localization.lift_on Localization.liftOn
#align add_localization.lift_on AddLocalization.liftOn

@[to_additive]
theorem liftOn_mk {p : Sort u} (f : ∀ (_a : M) (_b : S), p) (H) (a : M) (b : S) :
    liftOn (mk a b) f H = f a b := rfl
#align localization.lift_on_mk Localization.liftOn_mk
#align add_localization.lift_on_mk AddLocalization.liftOn_mk

@[to_additive (attr := elab_as_elim)]
theorem ind {p : Localization S → Prop} (H : ∀ y : M × S, p (mk y.1 y.2)) (x) : p x :=
  rec (fun a b ↦ H (a, b)) (fun _ ↦ rfl) x
#align localization.ind Localization.ind
#align add_localization.ind AddLocalization.ind

@[to_additive (attr := elab_as_elim)]
theorem induction_on {p : Localization S → Prop} (x) (H : ∀ y : M × S, p (mk y.1 y.2)) : p x :=
  ind H x
#align localization.induction_on Localization.induction_on
#align add_localization.induction_on AddLocalization.induction_on

/-- Non-dependent recursion principle for localizations: given elements `f x y : p`
for all `x` and `y`, such that `r S x x'` and `r S y y'` implies `f x y = f x' y'`,
then `f` is defined on the whole `Localization S`. -/
-- Porting note: the attribute `elab_as_elim` fails with `unexpected eliminator resulting type p`
-- @[to_additive (attr := elab_as_elim)
@[to_additive
    "Non-dependent recursion principle for localizations: given elements `f x y : p`
for all `x` and `y`, such that `r S x x'` and `r S y y'` implies `f x y = f x' y'`,
then `f` is defined on the whole `Localization S`."]
def liftOn₂ {p : Sort u} (x y : Localization S) (f : M → S → M → S → p)
    (H : ∀ {a a' b b' c c' d d'} (_ : r S (a, b) (a', b')) (_ : r S (c, d) (c', d')),
      f a b c d = f a' b' c' d') : p :=
  liftOn x (fun a b ↦ liftOn y (f a b) fun hy ↦ H ((r S).refl _) hy) fun hx ↦
    induction_on y fun ⟨_, _⟩ ↦ H hx ((r S).refl _)
#align localization.lift_on₂ Localization.liftOn₂
#align add_localization.lift_on₂ AddLocalization.liftOn₂

@[to_additive]
theorem liftOn₂_mk {p : Sort*} (f : M → S → M → S → p) (H) (a c : M) (b d : S) :
    liftOn₂ (mk a b) (mk c d) f H = f a b c d := rfl
#align localization.lift_on₂_mk Localization.liftOn₂_mk
#align add_localization.lift_on₂_mk AddLocalization.liftOn₂_mk

@[to_additive (attr := elab_as_elim)]
theorem induction_on₂ {p : Localization S → Localization S → Prop} (x y)
    (H : ∀ x y : M × S, p (mk x.1 x.2) (mk y.1 y.2)) : p x y :=
  induction_on x fun x ↦ induction_on y <| H x
#align localization.induction_on₂ Localization.induction_on₂
#align add_localization.induction_on₂ AddLocalization.induction_on₂

@[to_additive (attr := elab_as_elim)]
theorem induction_on₃ {p : Localization S → Localization S → Localization S → Prop} (x y z)
    (H : ∀ x y z : M × S, p (mk x.1 x.2) (mk y.1 y.2) (mk z.1 z.2)) : p x y z :=
  induction_on₂ x y fun x y ↦ induction_on z <| H x y
#align localization.induction_on₃ Localization.induction_on₃
#align add_localization.induction_on₃ AddLocalization.induction_on₃

@[to_additive]
theorem one_rel (y : S) : r S 1 (y, y) := fun _ hb ↦ hb y
#align localization.one_rel Localization.one_rel
#align add_localization.zero_rel AddLocalization.zero_rel

@[to_additive]
theorem r_of_eq {x y : M × S} (h : ↑y.2 * x.1 = ↑x.2 * y.1) : r S x y :=
  r_iff_exists.2 ⟨1, by rw [h]⟩
                        -- 🎉 no goals
#align localization.r_of_eq Localization.r_of_eq
#align add_localization.r_of_eq AddLocalization.r_of_eq

@[to_additive]
theorem mk_self (a : S) : mk (a : M) a = 1 := by
  symm
  -- ⊢ 1 = mk (↑a) a
  rw [← mk_one, mk_eq_mk_iff]
  -- ⊢ ↑(r S) (1, 1) (↑a, a)
  exact one_rel a
  -- 🎉 no goals
#align localization.mk_self Localization.mk_self
#align add_localization.mk_self AddLocalization.mk_self

section Scalar

variable {R R₁ R₂ : Type*}

/-- Scalar multiplication in a monoid localization is defined as `c • ⟨a, b⟩ = ⟨c • a, b⟩`. -/
protected irreducible_def smul [SMul R M] [IsScalarTower R M M] (c : R) (z : Localization S) :
  Localization S :=
    Localization.liftOn z (fun a b ↦ mk (c • a) b)
      (fun {a a' b b'} h ↦ mk_eq_mk_iff.2 (by
        cases' b with b hb
        -- ⊢ ↑(r S) (c • a, { val := b, property := hb }) (c • a', b')
        cases' b' with b' hb'
        -- ⊢ ↑(r S) (c • a, { val := b, property := hb }) (c • a', { val := b', property  …
        rw [r_eq_r'] at h ⊢
        -- ⊢ ↑(r' S) (c • a, { val := b, property := hb }) (c • a', { val := b', property …
        cases' h with t ht
        -- ⊢ ↑(r' S) (c • a, { val := b, property := hb }) (c • a', { val := b', property …
        use t
        -- ⊢ ↑t * (↑(c • a', { val := b', property := hb' }).snd * (c • a, { val := b, pr …
        dsimp only [Subtype.coe_mk] at ht ⊢
        -- ⊢ ↑t * (b' * c • a) = ↑t * (b * c • a')
-- TODO: this definition should take `SMulCommClass R M M` instead of `IsScalarTower R M M` if
-- we ever want to generalize to the non-commutative case.
        haveI : SMulCommClass R M M :=
          ⟨fun r m₁ m₂ ↦ by simp_rw [smul_eq_mul, mul_comm m₁, smul_mul_assoc]⟩
        simp only [mul_smul_comm, ht]))
        -- 🎉 no goals
#align localization.smul Localization.smul

instance instSMulLocalization [SMul R M] [IsScalarTower R M M] : SMul R (Localization S) where
  smul := Localization.smul

theorem smul_mk [SMul R M] [IsScalarTower R M M] (c : R) (a b) :
    c • (mk a b : Localization S) = mk (c • a) b := by
 simp only [HSMul.hSMul, instHSMul, SMul.smul, instSMulLocalization, Localization.smul]
 -- ⊢ liftOn (mk a b) (fun a b => mk (SMul.smul c a) b) (_ : ∀ {a c_1 : M} {b d :  …
 show liftOn (mk a b) (fun a b => mk (c • a) b) _ = _
 -- ⊢ liftOn (mk a b) (fun a b => mk (c • a) b) (_ : ∀ {a c_1 : M} {b d : { x // x …
 exact liftOn_mk (fun a b => mk (c • a) b) _ a b
 -- 🎉 no goals
#align localization.smul_mk Localization.smul_mk

instance [SMul R₁ M] [SMul R₂ M] [IsScalarTower R₁ M M] [IsScalarTower R₂ M M]
  [SMulCommClass R₁ R₂ M] : SMulCommClass R₁ R₂ (Localization S) where
  smul_comm s t := Localization.ind <| Prod.rec fun r x ↦ by simp only [smul_mk, smul_comm s t r]
                                                             -- 🎉 no goals

instance [SMul R₁ M] [SMul R₂ M] [IsScalarTower R₁ M M] [IsScalarTower R₂ M M] [SMul R₁ R₂]
  [IsScalarTower R₁ R₂ M] : IsScalarTower R₁ R₂ (Localization S) where
  smul_assoc s t := Localization.ind <| Prod.rec fun r x ↦ by simp only [smul_mk, smul_assoc s t r]
                                                              -- 🎉 no goals

instance smulCommClass_right {R : Type*} [SMul R M] [IsScalarTower R M M] :
  SMulCommClass R (Localization S) (Localization S) where
  smul_comm s :=
      Localization.ind <|
        Prod.rec fun r₁ x₁ ↦
          Localization.ind <|
            Prod.rec fun r₂ x₂ ↦ by
              simp only [smul_mk, smul_eq_mul, mk_mul, mul_comm r₁, smul_mul_assoc]
              -- 🎉 no goals
#align localization.smul_comm_class_right Localization.smulCommClass_right

instance isScalarTower_right {R : Type*} [SMul R M] [IsScalarTower R M M] :
  IsScalarTower R (Localization S) (Localization S) where
  smul_assoc s :=
    Localization.ind <|
      Prod.rec fun r₁ x₁ ↦
        Localization.ind <|
          Prod.rec fun r₂ x₂ ↦ by simp only [smul_mk, smul_eq_mul, mk_mul, smul_mul_assoc]
                                  -- 🎉 no goals
#align localization.is_scalar_tower_right Localization.isScalarTower_right

instance [SMul R M] [SMul Rᵐᵒᵖ M] [IsScalarTower R M M] [IsScalarTower Rᵐᵒᵖ M M]
  [IsCentralScalar R M] : IsCentralScalar R (Localization S) where
  op_smul_eq_smul s :=
    Localization.ind <| Prod.rec fun r x ↦ by simp only [smul_mk, op_smul_eq_smul]
                                              -- 🎉 no goals

instance [Monoid R] [MulAction R M] [IsScalarTower R M M] : MulAction R (Localization S) where
  one_smul :=
    Localization.ind <|
      Prod.rec <| by
        intros
        -- ⊢ 1 • mk (fst✝, snd✝).fst (fst✝, snd✝).snd = mk (fst✝, snd✝).fst (fst✝, snd✝). …
        simp only [Localization.smul_mk, one_smul]
        -- 🎉 no goals
  mul_smul s₁ s₂ :=
    Localization.ind <|
      Prod.rec <| by
        intros
        -- ⊢ (s₁ * s₂) • mk (fst✝, snd✝).fst (fst✝, snd✝).snd = s₁ • s₂ • mk (fst✝, snd✝) …
        simp only [Localization.smul_mk, mul_smul]
        -- 🎉 no goals

instance [Monoid R] [MulDistribMulAction R M] [IsScalarTower R M M] :
    MulDistribMulAction R (Localization S) where
  smul_one s := by simp only [← Localization.mk_one, Localization.smul_mk, smul_one]
                   -- 🎉 no goals
  smul_mul s x y :=
    Localization.induction_on₂ x y <|
      Prod.rec fun r₁ x₁ ↦
                                -- 🎉 no goals
        Prod.rec fun r₂ x₂ ↦ by simp only [Localization.smul_mk, Localization.mk_mul, smul_mul']

end Scalar

end Localization

variable {S N}

namespace MonoidHom

/-- Makes a localization map from a `CommMonoid` hom satisfying the characteristic predicate. -/
@[to_additive
    "Makes a localization map from an `AddCommMonoid` hom satisfying the characteristic predicate."]
def toLocalizationMap (f : M →* N) (H1 : ∀ y : S, IsUnit (f y))
    (H2 : ∀ z, ∃ x : M × S, z * f x.2 = f x.1) (H3 : ∀ x y, f x = f y ↔ ∃ c : S, ↑c * x = ↑c * y) :
    Submonoid.LocalizationMap S N :=
  { f with
    map_units' := H1
    surj' := H2
    eq_iff_exists' := H3 }
#align monoid_hom.to_localization_map MonoidHom.toLocalizationMap
#align add_monoid_hom.to_localization_map AddMonoidHom.toLocalizationMap

end MonoidHom

namespace Submonoid

namespace LocalizationMap

/-- Short for `toMonoidHom`; used to apply a localization map as a function. -/
@[to_additive "Short for `toAddMonoidHom`; used to apply a localization map as a function."]
abbrev toMap (f : LocalizationMap S N) := f.toMonoidHom
#align submonoid.localization_map.to_map Submonoid.LocalizationMap.toMap
#align add_submonoid.localization_map.to_map AddSubmonoid.LocalizationMap.toMap

@[to_additive (attr := ext)]
theorem ext {f g : LocalizationMap S N} (h : ∀ x, f.toMap x = g.toMap x) : f = g := by
  rcases f with ⟨⟨⟩⟩
  -- ⊢ { toMonoidHom := { toOneHom := toOneHom✝, map_mul' := map_mul'✝ }, map_units …
  rcases g with ⟨⟨⟩⟩
  -- ⊢ { toMonoidHom := { toOneHom := toOneHom✝¹, map_mul' := map_mul'✝¹ }, map_uni …
  simp only [mk.injEq, MonoidHom.mk.injEq]
  -- ⊢ toOneHom✝¹ = toOneHom✝
  exact OneHom.ext h
  -- 🎉 no goals
#align submonoid.localization_map.ext Submonoid.LocalizationMap.ext
#align add_submonoid.localization_map.ext AddSubmonoid.LocalizationMap.ext

@[to_additive]
theorem ext_iff {f g : LocalizationMap S N} : f = g ↔ ∀ x, f.toMap x = g.toMap x :=
  ⟨fun h _ ↦ h ▸ rfl, ext⟩
#align submonoid.localization_map.ext_iff Submonoid.LocalizationMap.ext_iff
#align add_submonoid.localization_map.ext_iff AddSubmonoid.LocalizationMap.ext_iff

@[to_additive]
theorem toMap_injective : Function.Injective (@LocalizationMap.toMap _ _ S N _) :=
  fun _ _ h ↦ ext <| FunLike.ext_iff.1 h
#align submonoid.localization_map.to_map_injective Submonoid.LocalizationMap.toMap_injective
#align add_submonoid.localization_map.to_map_injective AddSubmonoid.LocalizationMap.toMap_injective

@[to_additive]
theorem map_units (f : LocalizationMap S N) (y : S) : IsUnit (f.toMap y) :=
  f.2 y
#align submonoid.localization_map.map_units Submonoid.LocalizationMap.map_units
#align add_submonoid.localization_map.map_add_units AddSubmonoid.LocalizationMap.map_addUnits

@[to_additive]
theorem surj (f : LocalizationMap S N) (z : N) : ∃ x : M × S, z * f.toMap x.2 = f.toMap x.1 :=
  f.3 z
#align submonoid.localization_map.surj Submonoid.LocalizationMap.surj
#align add_submonoid.localization_map.surj AddSubmonoid.LocalizationMap.surj

@[to_additive]
theorem eq_iff_exists (f : LocalizationMap S N) {x y} :
    f.toMap x = f.toMap y ↔ ∃ c : S, ↑c * x = c * y := f.4 x y
#align submonoid.localization_map.eq_iff_exists Submonoid.LocalizationMap.eq_iff_exists
#align add_submonoid.localization_map.eq_iff_exists AddSubmonoid.LocalizationMap.eq_iff_exists

/-- Given a localization map `f : M →* N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`. -/
@[to_additive
    "Given a localization map `f : M →+ N`, a section function sending `z : N`
to some `(x, y) : M × S` such that `f x - f y = z`."]
noncomputable def sec (f : LocalizationMap S N) (z : N) : M × S := Classical.choose <| f.surj z
#align submonoid.localization_map.sec Submonoid.LocalizationMap.sec
#align add_submonoid.localization_map.sec AddSubmonoid.LocalizationMap.sec

@[to_additive]
theorem sec_spec {f : LocalizationMap S N} (z : N) :
    z * f.toMap (f.sec z).2 = f.toMap (f.sec z).1 := Classical.choose_spec <| f.surj z
#align submonoid.localization_map.sec_spec Submonoid.LocalizationMap.sec_spec
#align add_submonoid.localization_map.sec_spec AddSubmonoid.LocalizationMap.sec_spec

@[to_additive]
theorem sec_spec' {f : LocalizationMap S N} (z : N) :
    f.toMap (f.sec z).1 = f.toMap (f.sec z).2 * z := by rw [mul_comm, sec_spec]
                                                        -- 🎉 no goals
#align submonoid.localization_map.sec_spec' Submonoid.LocalizationMap.sec_spec'
#align add_submonoid.localization_map.sec_spec' AddSubmonoid.LocalizationMap.sec_spec'

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that `f(S) ⊆ Nˣ`, for all
`w, z : N` and `y ∈ S`, we have `w * (f y)⁻¹ = z ↔ w = f y * z`. -/
@[to_additive
    "Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ AddUnits N`, for all `w, z : N` and `y ∈ S`, we have `w - f y = z ↔ w = f y + z`."]
theorem mul_inv_left {f : M →* N} (h : ∀ y : S, IsUnit (f y)) (y : S) (w z : N) :
    w * (IsUnit.liftRight (f.restrict S) h y)⁻¹ = z ↔ w = f y * z := by
  rw [mul_comm]
  -- ⊢ ↑(↑(IsUnit.liftRight (MonoidHom.restrict f S) h) y)⁻¹ * w = z ↔ w = ↑f ↑y * z
  exact Units.inv_mul_eq_iff_eq_mul (IsUnit.liftRight (f.restrict S) h y)
  -- 🎉 no goals
#align submonoid.localization_map.mul_inv_left Submonoid.LocalizationMap.mul_inv_left
#align add_submonoid.localization_map.add_neg_left AddSubmonoid.LocalizationMap.add_neg_left

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that `f(S) ⊆ Nˣ`, for all
`w, z : N` and `y ∈ S`, we have `z = w * (f y)⁻¹ ↔ z * f y = w`. -/
@[to_additive
    "Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ AddUnits N`, for all `w, z : N` and `y ∈ S`, we have `z = w - f y ↔ z + f y = w`."]
theorem mul_inv_right {f : M →* N} (h : ∀ y : S, IsUnit (f y)) (y : S) (w z : N) :
    z = w * (IsUnit.liftRight (f.restrict S) h y)⁻¹ ↔ z * f y = w := by
  rw [eq_comm, mul_inv_left h, mul_comm, eq_comm]
  -- 🎉 no goals
#align submonoid.localization_map.mul_inv_right Submonoid.LocalizationMap.mul_inv_right
#align add_submonoid.localization_map.add_neg_right AddSubmonoid.LocalizationMap.add_neg_right

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ Nˣ`, for all `x₁ x₂ : M` and `y₁, y₂ ∈ S`, we have
`f x₁ * (f y₁)⁻¹ = f x₂ * (f y₂)⁻¹ ↔ f (x₁ * y₂) = f (x₂ * y₁)`. -/
@[to_additive (attr := simp)
    "Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ AddUnits N`, for all `x₁ x₂ : M` and `y₁, y₂ ∈ S`, we have
`f x₁ - f y₁ = f x₂ - f y₂ ↔ f (x₁ + y₂) = f (x₂ + y₁)`."]
theorem mul_inv {f : M →* N} (h : ∀ y : S, IsUnit (f y)) {x₁ x₂} {y₁ y₂ : S} :
    f x₁ * (IsUnit.liftRight (f.restrict S) h y₁)⁻¹ =
        f x₂ * (IsUnit.liftRight (f.restrict S) h y₂)⁻¹ ↔
      f (x₁ * y₂) = f (x₂ * y₁) := by
  rw [mul_inv_right h, mul_assoc, mul_comm _ (f y₂), ← mul_assoc, mul_inv_left h, mul_comm x₂,
    f.map_mul, f.map_mul]
#align submonoid.localization_map.mul_inv Submonoid.LocalizationMap.mul_inv
#align add_submonoid.localization_map.add_neg AddSubmonoid.LocalizationMap.add_neg

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that `f(S) ⊆ Nˣ`, for all
`y, z ∈ S`, we have `(f y)⁻¹ = (f z)⁻¹ → f y = f z`. -/
@[to_additive
    "Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ AddUnits N`, for all `y, z ∈ S`, we have `- (f y) = - (f z) → f y = f z`."]
theorem inv_inj {f : M →* N} (hf : ∀ y : S, IsUnit (f y)) {y z : S}
    (h : (IsUnit.liftRight (f.restrict S) hf y)⁻¹ = (IsUnit.liftRight (f.restrict S) hf z)⁻¹) :
      f y = f z := by
  rw [← mul_one (f y), eq_comm, ← mul_inv_left hf y (f z) 1, h]
  -- ⊢ ↑f ↑z * ↑(↑(IsUnit.liftRight (MonoidHom.restrict f S) hf) z)⁻¹ = 1
  exact Units.inv_mul (IsUnit.liftRight (f.restrict S) hf z)⁻¹
  -- 🎉 no goals
#align submonoid.localization_map.inv_inj Submonoid.LocalizationMap.inv_inj
#align add_submonoid.localization_map.neg_inj AddSubmonoid.LocalizationMap.neg_inj

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that `f(S) ⊆ Nˣ`, for all
`y ∈ S`, `(f y)⁻¹` is unique. -/
@[to_additive
    "Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ AddUnits N`, for all `y ∈ S`, `- (f y)` is unique."]
theorem inv_unique {f : M →* N} (h : ∀ y : S, IsUnit (f y)) {y : S} {z : N} (H : f y * z = 1) :
    (IsUnit.liftRight (f.restrict S) h y)⁻¹ = z := by
  rw [← one_mul _⁻¹, Units.val_mul, mul_inv_left]
  -- ⊢ ↑1 = ↑f ↑y * z
  exact H.symm
  -- 🎉 no goals
#align submonoid.localization_map.inv_unique Submonoid.LocalizationMap.inv_unique
#align add_submonoid.localization_map.neg_unique AddSubmonoid.LocalizationMap.neg_unique

variable (f : LocalizationMap S N)

@[to_additive]
theorem map_right_cancel {x y} {c : S} (h : f.toMap (c * x) = f.toMap (c * y)) :
    f.toMap x = f.toMap y := by
  rw [f.toMap.map_mul, f.toMap.map_mul] at h
  -- ⊢ ↑(toMap f) x = ↑(toMap f) y
  cases' f.map_units c with u hu
  -- ⊢ ↑(toMap f) x = ↑(toMap f) y
  rw [← hu] at h
  -- ⊢ ↑(toMap f) x = ↑(toMap f) y
  exact (Units.mul_right_inj u).1 h
  -- 🎉 no goals
#align submonoid.localization_map.map_right_cancel Submonoid.LocalizationMap.map_right_cancel
#align add_submonoid.localization_map.map_right_cancel AddSubmonoid.LocalizationMap.map_right_cancel

@[to_additive]
theorem map_left_cancel {x y} {c : S} (h : f.toMap (x * c) = f.toMap (y * c)) :
    f.toMap x = f.toMap y :=
  f.map_right_cancel <| by rw [mul_comm _ x, mul_comm _ y, h]
                           -- 🎉 no goals
#align submonoid.localization_map.map_left_cancel Submonoid.LocalizationMap.map_left_cancel
#align add_submonoid.localization_map.map_left_cancel AddSubmonoid.LocalizationMap.map_left_cancel

/-- Given a localization map `f : M →* N`, the surjection sending `(x, y) : M × S` to
`f x * (f y)⁻¹`. -/
@[to_additive
      "Given a localization map `f : M →+ N`, the surjection sending `(x, y) : M × S`
to `f x - f y`."]
noncomputable def mk' (f : LocalizationMap S N) (x : M) (y : S) : N :=
  f.toMap x * ↑(IsUnit.liftRight (f.toMap.restrict S) f.map_units y)⁻¹
#align submonoid.localization_map.mk' Submonoid.LocalizationMap.mk'
#align add_submonoid.localization_map.mk' AddSubmonoid.LocalizationMap.mk'

@[to_additive]
theorem mk'_mul (x₁ x₂ : M) (y₁ y₂ : S) : f.mk' (x₁ * x₂) (y₁ * y₂) = f.mk' x₁ y₁ * f.mk' x₂ y₂ :=
  (mul_inv_left f.map_units _ _ _).2 <|
    show _ = _ * (_ * _ * (_ * _)) by
      rw [← mul_assoc, ← mul_assoc, mul_inv_right f.map_units, mul_assoc, mul_assoc,
          mul_comm _ (f.toMap x₂), ← mul_assoc, ← mul_assoc, mul_inv_right f.map_units,
          Submonoid.coe_mul, f.toMap.map_mul, f.toMap.map_mul]
      ac_rfl
      -- 🎉 no goals
#align submonoid.localization_map.mk'_mul Submonoid.LocalizationMap.mk'_mul
#align add_submonoid.localization_map.mk'_add AddSubmonoid.LocalizationMap.mk'_add

@[to_additive]
theorem mk'_one (x) : f.mk' x (1 : S) = f.toMap x := by
  rw [mk', MonoidHom.map_one]
  -- ⊢ ↑(toMap f) x * ↑1⁻¹ = ↑(toMap f) x
  exact mul_one _
  -- 🎉 no goals
#align submonoid.localization_map.mk'_one Submonoid.LocalizationMap.mk'_one
#align add_submonoid.localization_map.mk'_zero AddSubmonoid.LocalizationMap.mk'_zero

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, for all `z : N` we have that if
`x : M, y ∈ S` are such that `z * f y = f x`, then `f x * (f y)⁻¹ = z`. -/
@[to_additive (attr := simp)
    "Given a localization map `f : M →+ N` for a Submonoid `S ⊆ M`, for all `z : N`
we have that if `x : M, y ∈ S` are such that `z + f y = f x`, then `f x - f y = z`."]
theorem mk'_sec (z : N) : f.mk' (f.sec z).1 (f.sec z).2 = z :=
  show _ * _ = _ by rw [← sec_spec, mul_inv_left, mul_comm]
                    -- 🎉 no goals
#align submonoid.localization_map.mk'_sec Submonoid.LocalizationMap.mk'_sec
#align add_submonoid.localization_map.mk'_sec AddSubmonoid.LocalizationMap.mk'_sec

@[to_additive]
theorem mk'_surjective (z : N) : ∃ (x : _) (y : S), f.mk' x y = z :=
  ⟨(f.sec z).1, (f.sec z).2, f.mk'_sec z⟩
#align submonoid.localization_map.mk'_surjective Submonoid.LocalizationMap.mk'_surjective
#align add_submonoid.localization_map.mk'_surjective AddSubmonoid.LocalizationMap.mk'_surjective

@[to_additive]
theorem mk'_spec (x) (y : S) : f.mk' x y * f.toMap y = f.toMap x :=
  show _ * _ * _ = _ by rw [mul_assoc, mul_comm _ (f.toMap y), ← mul_assoc, mul_inv_left, mul_comm]
                        -- 🎉 no goals
#align submonoid.localization_map.mk'_spec Submonoid.LocalizationMap.mk'_spec
#align add_submonoid.localization_map.mk'_spec AddSubmonoid.LocalizationMap.mk'_spec

@[to_additive]
theorem mk'_spec' (x) (y : S) : f.toMap y * f.mk' x y = f.toMap x := by rw [mul_comm, mk'_spec]
                                                                        -- 🎉 no goals
#align submonoid.localization_map.mk'_spec' Submonoid.LocalizationMap.mk'_spec'
#align add_submonoid.localization_map.mk'_spec' AddSubmonoid.LocalizationMap.mk'_spec'

@[to_additive]
theorem eq_mk'_iff_mul_eq {x} {y : S} {z} : z = f.mk' x y ↔ z * f.toMap y = f.toMap x :=
  ⟨fun H ↦ by rw [H, mk'_spec], fun H ↦ by erw [mul_inv_right, H]⟩
              -- 🎉 no goals
                                           -- 🎉 no goals
#align submonoid.localization_map.eq_mk'_iff_mul_eq Submonoid.LocalizationMap.eq_mk'_iff_mul_eq
#align add_submonoid.localization_map.eq_mk'_iff_add_eq AddSubmonoid.LocalizationMap.eq_mk'_iff_add_eq

@[to_additive]
theorem mk'_eq_iff_eq_mul {x} {y : S} {z} : f.mk' x y = z ↔ f.toMap x = z * f.toMap y := by
  rw [eq_comm, eq_mk'_iff_mul_eq, eq_comm]
  -- 🎉 no goals
#align submonoid.localization_map.mk'_eq_iff_eq_mul Submonoid.LocalizationMap.mk'_eq_iff_eq_mul
#align add_submonoid.localization_map.mk'_eq_iff_eq_add AddSubmonoid.LocalizationMap.mk'_eq_iff_eq_add

@[to_additive]
theorem mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : S} :
    f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ f.toMap (y₂ * x₁) = f.toMap (y₁ * x₂) :=
  ⟨fun H ↦ by
    rw [f.toMap.map_mul, f.toMap.map_mul, f.mk'_eq_iff_eq_mul.1 H,← mul_assoc, mk'_spec',
      mul_comm ((toMap f) x₂) _],
    fun H ↦ by
    rw [mk'_eq_iff_eq_mul, mk', mul_assoc, mul_comm _ (f.toMap y₁), ← mul_assoc, ←
      f.toMap.map_mul, mul_comm x₂, ← H, ← mul_comm x₁, f.toMap.map_mul,
      mul_inv_right f.map_units]⟩
#align submonoid.localization_map.mk'_eq_iff_eq Submonoid.LocalizationMap.mk'_eq_iff_eq
#align add_submonoid.localization_map.mk'_eq_iff_eq AddSubmonoid.LocalizationMap.mk'_eq_iff_eq

@[to_additive]
theorem mk'_eq_iff_eq' {x₁ x₂} {y₁ y₂ : S} :
    f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ f.toMap (x₁ * y₂) = f.toMap (x₂ * y₁) := by
  simp only [f.mk'_eq_iff_eq, mul_comm]
  -- 🎉 no goals
#align submonoid.localization_map.mk'_eq_iff_eq' Submonoid.LocalizationMap.mk'_eq_iff_eq'
#align add_submonoid.localization_map.mk'_eq_iff_eq' AddSubmonoid.LocalizationMap.mk'_eq_iff_eq'

@[to_additive]
protected theorem eq {a₁ b₁} {a₂ b₂ : S} :
    f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ ∃ c : S, ↑c * (↑b₂ * a₁) = c * (a₂ * b₁) :=
  f.mk'_eq_iff_eq.trans <| f.eq_iff_exists
#align submonoid.localization_map.eq Submonoid.LocalizationMap.eq
#align add_submonoid.localization_map.eq AddSubmonoid.LocalizationMap.eq

@[to_additive]
protected theorem eq' {a₁ b₁} {a₂ b₂ : S} :
    f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ Localization.r S (a₁, a₂) (b₁, b₂) := by
  rw [f.eq, Localization.r_iff_exists]
  -- 🎉 no goals
#align submonoid.localization_map.eq' Submonoid.LocalizationMap.eq'
#align add_submonoid.localization_map.eq' AddSubmonoid.LocalizationMap.eq'

@[to_additive]
theorem eq_iff_eq (g : LocalizationMap S P) {x y} : f.toMap x = f.toMap y ↔ g.toMap x = g.toMap y :=
  f.eq_iff_exists.trans g.eq_iff_exists.symm
#align submonoid.localization_map.eq_iff_eq Submonoid.LocalizationMap.eq_iff_eq
#align add_submonoid.localization_map.eq_iff_eq AddSubmonoid.LocalizationMap.eq_iff_eq

@[to_additive]
theorem mk'_eq_iff_mk'_eq (g : LocalizationMap S P) {x₁ x₂} {y₁ y₂ : S} :
    f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ g.mk' x₁ y₁ = g.mk' x₂ y₂ :=
  f.eq'.trans g.eq'.symm
#align submonoid.localization_map.mk'_eq_iff_mk'_eq Submonoid.LocalizationMap.mk'_eq_iff_mk'_eq
#align add_submonoid.localization_map.mk'_eq_iff_mk'_eq AddSubmonoid.LocalizationMap.mk'_eq_iff_mk'_eq

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, for all `x₁ : M` and `y₁ ∈ S`,
if `x₂ : M, y₂ ∈ S` are such that `f x₁ * (f y₁)⁻¹ * f y₂ = f x₂`, then there exists `c ∈ S`
such that `x₁ * y₂ * c = x₂ * y₁ * c`. -/
@[to_additive
    "Given a Localization map `f : M →+ N` for a Submonoid `S ⊆ M`, for all `x₁ : M`
and `y₁ ∈ S`, if `x₂ : M, y₂ ∈ S` are such that `(f x₁ - f y₁) + f y₂ = f x₂`, then there exists
`c ∈ S` such that `x₁ + y₂ + c = x₂ + y₁ + c`."]
theorem exists_of_sec_mk' (x) (y : S) :
    ∃ c : S, ↑c * (↑(f.sec <| f.mk' x y).2 * x) = c * (y * (f.sec <| f.mk' x y).1) :=
  f.eq_iff_exists.1 <| f.mk'_eq_iff_eq.1 <| (mk'_sec _ _).symm
#align submonoid.localization_map.exists_of_sec_mk' Submonoid.LocalizationMap.exists_of_sec_mk'
#align add_submonoid.localization_map.exists_of_sec_mk' AddSubmonoid.LocalizationMap.exists_of_sec_mk'

@[to_additive]
theorem mk'_eq_of_eq {a₁ b₁ : M} {a₂ b₂ : S} (H : ↑a₂ * b₁ = ↑b₂ * a₁) :
    f.mk' a₁ a₂ = f.mk' b₁ b₂ :=
  f.mk'_eq_iff_eq.2 <| H ▸ rfl
#align submonoid.localization_map.mk'_eq_of_eq Submonoid.LocalizationMap.mk'_eq_of_eq
#align add_submonoid.localization_map.mk'_eq_of_eq AddSubmonoid.LocalizationMap.mk'_eq_of_eq

@[to_additive]
theorem mk'_eq_of_eq' {a₁ b₁ : M} {a₂ b₂ : S} (H : b₁ * ↑a₂ = a₁ * ↑b₂) :
    f.mk' a₁ a₂ = f.mk' b₁ b₂ :=
  f.mk'_eq_of_eq <| by simpa only [mul_comm] using H
                       -- 🎉 no goals
#align submonoid.localization_map.mk'_eq_of_eq' Submonoid.LocalizationMap.mk'_eq_of_eq'
#align add_submonoid.localization_map.mk'_eq_of_eq' AddSubmonoid.LocalizationMap.mk'_eq_of_eq'

@[to_additive (attr := simp)]
theorem mk'_self' (y : S) : f.mk' (y : M) y = 1 :=
  show _ * _ = _ by rw [mul_inv_left, mul_one]
                    -- 🎉 no goals
#align submonoid.localization_map.mk'_self' Submonoid.LocalizationMap.mk'_self'
#align add_submonoid.localization_map.mk'_self' AddSubmonoid.LocalizationMap.mk'_self'

@[to_additive (attr := simp)]
theorem mk'_self (x) (H : x ∈ S) : f.mk' x ⟨x, H⟩ = 1 := mk'_self' f ⟨x, H⟩
#align submonoid.localization_map.mk'_self Submonoid.LocalizationMap.mk'_self
#align add_submonoid.localization_map.mk'_self AddSubmonoid.LocalizationMap.mk'_self

@[to_additive]
theorem mul_mk'_eq_mk'_of_mul (x₁ x₂) (y : S) : f.toMap x₁ * f.mk' x₂ y = f.mk' (x₁ * x₂) y := by
  rw [← mk'_one, ← mk'_mul, one_mul]
  -- 🎉 no goals
#align submonoid.localization_map.mul_mk'_eq_mk'_of_mul Submonoid.LocalizationMap.mul_mk'_eq_mk'_of_mul
#align add_submonoid.localization_map.add_mk'_eq_mk'_of_add AddSubmonoid.LocalizationMap.add_mk'_eq_mk'_of_add

@[to_additive]
theorem mk'_mul_eq_mk'_of_mul (x₁ x₂) (y : S) : f.mk' x₂ y * f.toMap x₁ = f.mk' (x₁ * x₂) y := by
  rw [mul_comm, mul_mk'_eq_mk'_of_mul]
  -- 🎉 no goals
#align submonoid.localization_map.mk'_mul_eq_mk'_of_mul Submonoid.LocalizationMap.mk'_mul_eq_mk'_of_mul
#align add_submonoid.localization_map.mk'_add_eq_mk'_of_add AddSubmonoid.LocalizationMap.mk'_add_eq_mk'_of_add

@[to_additive]
theorem mul_mk'_one_eq_mk' (x) (y : S) : f.toMap x * f.mk' 1 y = f.mk' x y := by
  rw [mul_mk'_eq_mk'_of_mul, mul_one]
  -- 🎉 no goals
#align submonoid.localization_map.mul_mk'_one_eq_mk' Submonoid.LocalizationMap.mul_mk'_one_eq_mk'
#align add_submonoid.localization_map.add_mk'_zero_eq_mk' AddSubmonoid.LocalizationMap.add_mk'_zero_eq_mk'

@[to_additive (attr := simp)]
theorem mk'_mul_cancel_right (x : M) (y : S) : f.mk' (x * y) y = f.toMap x := by
  rw [← mul_mk'_one_eq_mk', f.toMap.map_mul, mul_assoc, mul_mk'_one_eq_mk', mk'_self', mul_one]
  -- 🎉 no goals
#align submonoid.localization_map.mk'_mul_cancel_right Submonoid.LocalizationMap.mk'_mul_cancel_right
#align add_submonoid.localization_map.mk'_add_cancel_right AddSubmonoid.LocalizationMap.mk'_add_cancel_right

@[to_additive]
theorem mk'_mul_cancel_left (x) (y : S) : f.mk' ((y : M) * x) y = f.toMap x := by
  rw [mul_comm, mk'_mul_cancel_right]
  -- 🎉 no goals
#align submonoid.localization_map.mk'_mul_cancel_left Submonoid.LocalizationMap.mk'_mul_cancel_left
#align add_submonoid.localization_map.mk'_add_cancel_left AddSubmonoid.LocalizationMap.mk'_add_cancel_left

@[to_additive]
theorem isUnit_comp (j : N →* P) (y : S) : IsUnit (j.comp f.toMap y) :=
  ⟨Units.map j <| IsUnit.liftRight (f.toMap.restrict S) f.map_units y,
    show j _ = j _ from congr_arg j <| IsUnit.coe_liftRight (f.toMap.restrict S) f.map_units _⟩
#align submonoid.localization_map.is_unit_comp Submonoid.LocalizationMap.isUnit_comp
#align add_submonoid.localization_map.is_add_unit_comp AddSubmonoid.LocalizationMap.isAddUnit_comp

variable {g : M →* P}

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a map of `CommMonoid`s
`g : M →* P` such that `g(S) ⊆ Units P`, `f x = f y → g x = g y` for all `x y : M`. -/
@[to_additive
    "Given a Localization map `f : M →+ N` for a Submonoid `S ⊆ M` and a map of
`AddCommMonoid`s `g : M →+ P` such that `g(S) ⊆ AddUnits P`, `f x = f y → g x = g y`
for all `x y : M`."]
theorem eq_of_eq (hg : ∀ y : S, IsUnit (g y)) {x y} (h : f.toMap x = f.toMap y) : g x = g y := by
  obtain ⟨c, hc⟩ := f.eq_iff_exists.1 h
  -- ⊢ ↑g x = ↑g y
  rw [← one_mul (g x), ← IsUnit.liftRight_inv_mul (g.restrict S) hg c]
  -- ⊢ ↑(↑(IsUnit.liftRight (MonoidHom.restrict g S) hg) c)⁻¹ * ↑(MonoidHom.restric …
  show _ * g c * _ = _
  -- ⊢ ↑(↑(IsUnit.liftRight (MonoidHom.restrict g S) hg) c)⁻¹ * ↑g ↑c * ↑g x = ↑g y
  rw [mul_assoc, ← g.map_mul, hc, mul_comm, mul_inv_left hg, g.map_mul]
  -- 🎉 no goals
#align submonoid.localization_map.eq_of_eq Submonoid.LocalizationMap.eq_of_eq
#align add_submonoid.localization_map.eq_of_eq AddSubmonoid.LocalizationMap.eq_of_eq

/-- Given `CommMonoid`s `M, P`, Localization maps `f : M →* N, k : P →* Q` for Submonoids
`S, T` respectively, and `g : M →* P` such that `g(S) ⊆ T`, `f x = f y` implies
`k (g x) = k (g y)`. -/
@[to_additive
    "Given `AddCommMonoid`s `M, P`, Localization maps `f : M →+ N, k : P →+ Q` for Submonoids
`S, T` respectively, and `g : M →+ P` such that `g(S) ⊆ T`, `f x = f y`
implies `k (g x) = k (g y)`."]
theorem comp_eq_of_eq {T : Submonoid P} {Q : Type*} [CommMonoid Q] (hg : ∀ y : S, g y ∈ T)
    (k : LocalizationMap T Q) {x y} (h : f.toMap x = f.toMap y) : k.toMap (g x) = k.toMap (g y) :=
  f.eq_of_eq (fun y : S ↦ show IsUnit (k.toMap.comp g y) from k.map_units ⟨g y, hg y⟩) h
#align submonoid.localization_map.comp_eq_of_eq Submonoid.LocalizationMap.comp_eq_of_eq
#align add_submonoid.localization_map.comp_eq_of_eq AddSubmonoid.LocalizationMap.comp_eq_of_eq

variable (hg : ∀ y : S, IsUnit (g y))

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a map of `CommMonoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` sending `z : N` to `g x * (g y)⁻¹`, where `(x, y) : M × S` are such that
`z = f x * (f y)⁻¹`. -/
@[to_additive
    "Given a localization map `f : M →+ N` for a submonoid `S ⊆ M` and a map of
`AddCommMonoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism
induced from `N` to `P` sending `z : N` to `g x - g y`, where `(x, y) : M × S` are such that
`z = f x - f y`."]
noncomputable def lift : N →* P where
  toFun z := g (f.sec z).1 * (IsUnit.liftRight (g.restrict S) hg (f.sec z).2)⁻¹
  map_one' := by rw [mul_inv_left, mul_one]; exact f.eq_of_eq hg (by rw [← sec_spec, one_mul])
                 -- ⊢ ↑g (sec f 1).fst = ↑g ↑(sec f 1).snd
                                             -- 🎉 no goals
  map_mul' x y := by
    dsimp only
    -- ⊢ ↑g (sec f (x * y)).fst * ↑(↑(IsUnit.liftRight (MonoidHom.restrict g S) hg) ( …
    rw [mul_inv_left hg, ← mul_assoc, ← mul_assoc, mul_inv_right hg, mul_comm _ (g (f.sec y).1), ←
      mul_assoc, ← mul_assoc, mul_inv_right hg]
    repeat' rw [← g.map_mul]
    -- ⊢ ↑g ((sec f (x * y)).fst * ↑(sec f y).snd * ↑(sec f x).snd) = ↑g ((sec f y).f …
    exact f.eq_of_eq hg (by simp_rw [f.toMap.map_mul, sec_spec']; ac_rfl)
    -- 🎉 no goals
#align submonoid.localization_map.lift Submonoid.LocalizationMap.lift
#align add_submonoid.localization_map.lift AddSubmonoid.LocalizationMap.lift

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a map of `CommMonoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : M, y ∈ S`. -/
@[to_additive
    "Given a Localization map `f : M →+ N` for a Submonoid `S ⊆ M` and a map of
`AddCommMonoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism
induced from `N` to `P` maps `f x - f y` to `g x - g y` for all `x : M, y ∈ S`."]
theorem lift_mk' (x y) : f.lift hg (f.mk' x y) = g x * (IsUnit.liftRight (g.restrict S) hg y)⁻¹ :=
  (mul_inv hg).2 <|
    f.eq_of_eq hg <| by
      simp_rw [f.toMap.map_mul, sec_spec', mul_assoc, f.mk'_spec, mul_comm]
      -- 🎉 no goals
#align submonoid.localization_map.lift_mk' Submonoid.LocalizationMap.lift_mk'
#align add_submonoid.localization_map.lift_mk' AddSubmonoid.LocalizationMap.lift_mk'

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v : P`, we have
`f.lift hg z = v ↔ g x = g y * v`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
    "Given a Localization map `f : M →+ N` for a Submonoid `S ⊆ M`, if an
`AddCommMonoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all
`z : N, v : P`, we have `f.lift hg z = v ↔ g x = g y + v`, where `x : M, y ∈ S` are such that
`z + f y = f x`."]
theorem lift_spec (z v) : f.lift hg z = v ↔ g (f.sec z).1 = g (f.sec z).2 * v :=
  mul_inv_left hg _ _ v
#align submonoid.localization_map.lift_spec Submonoid.LocalizationMap.lift_spec
#align add_submonoid.localization_map.lift_spec AddSubmonoid.LocalizationMap.lift_spec

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v w : P`, we have
`f.lift hg z * w = v ↔ g x * w = g y * v`, where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
    "Given a Localization map `f : M →+ N` for a Submonoid `S ⊆ M`, if an `AddCommMonoid` map
`g : M →+ P` induces a map `f.lift hg : N →+ P` then for all
`z : N, v w : P`, we have `f.lift hg z + w = v ↔ g x + w = g y + v`, where `x : M, y ∈ S` are such
that `z + f y = f x`."]
theorem lift_spec_mul (z w v) : f.lift hg z * w = v ↔ g (f.sec z).1 * w = g (f.sec z).2 * v := by
  erw [mul_comm, ← mul_assoc, mul_inv_left hg, mul_comm]
  -- 🎉 no goals
#align submonoid.localization_map.lift_spec_mul Submonoid.LocalizationMap.lift_spec_mul
#align add_submonoid.localization_map.lift_spec_add AddSubmonoid.LocalizationMap.lift_spec_add

@[to_additive]
theorem lift_mk'_spec (x v) (y : S) : f.lift hg (f.mk' x y) = v ↔ g x = g y * v := by
  rw [f.lift_mk' hg]; exact mul_inv_left hg _ _ _
  -- ⊢ ↑g x * ↑(↑(IsUnit.liftRight (MonoidHom.restrict g S) hg) y)⁻¹ = v ↔ ↑g x = ↑ …
                      -- 🎉 no goals
#align submonoid.localization_map.lift_mk'_spec Submonoid.LocalizationMap.lift_mk'_spec
#align add_submonoid.localization_map.lift_mk'_spec AddSubmonoid.LocalizationMap.lift_mk'_spec

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`f.lift hg z * g y = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
    "Given a Localization map `f : M →+ N` for a Submonoid `S ⊆ M`, if an `AddCommMonoid`
map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we have
`f.lift hg z + g y = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`."]
theorem lift_mul_right (z) : f.lift hg z * g (f.sec z).2 = g (f.sec z).1 := by
  erw [mul_assoc, IsUnit.liftRight_inv_mul, mul_one]
  -- 🎉 no goals
#align submonoid.localization_map.lift_mul_right Submonoid.LocalizationMap.lift_mul_right
#align add_submonoid.localization_map.lift_add_right AddSubmonoid.LocalizationMap.lift_add_right

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`g y * f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
    "Given a Localization map `f : M →+ N` for a Submonoid `S ⊆ M`, if an `AddCommMonoid` map
`g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we have
`g y + f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`."]
theorem lift_mul_left (z) : g (f.sec z).2 * f.lift hg z = g (f.sec z).1 := by
  rw [mul_comm, lift_mul_right]
  -- 🎉 no goals
#align submonoid.localization_map.lift_mul_left Submonoid.LocalizationMap.lift_mul_left
#align add_submonoid.localization_map.lift_add_left AddSubmonoid.LocalizationMap.lift_add_left

@[to_additive (attr := simp)]
theorem lift_eq (x : M) : f.lift hg (f.toMap x) = g x := by
  rw [lift_spec, ← g.map_mul]; exact f.eq_of_eq hg (by rw [sec_spec', f.toMap.map_mul])
  -- ⊢ ↑g (sec f (↑(toMap f) x)).fst = ↑g (↑(sec f (↑(toMap f) x)).snd * x)
                               -- 🎉 no goals
#align submonoid.localization_map.lift_eq Submonoid.LocalizationMap.lift_eq
#align add_submonoid.localization_map.lift_eq AddSubmonoid.LocalizationMap.lift_eq

@[to_additive]
theorem lift_eq_iff {x y : M × S} :
    f.lift hg (f.mk' x.1 x.2) = f.lift hg (f.mk' y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) := by
  rw [lift_mk', lift_mk', mul_inv hg]
  -- 🎉 no goals
#align submonoid.localization_map.lift_eq_iff Submonoid.LocalizationMap.lift_eq_iff
#align add_submonoid.localization_map.lift_eq_iff AddSubmonoid.LocalizationMap.lift_eq_iff

@[to_additive (attr := simp)]
theorem lift_comp : (f.lift hg).comp f.toMap = g := by ext; exact f.lift_eq hg _
                                                       -- ⊢ ↑(MonoidHom.comp (lift f hg) (toMap f)) x✝ = ↑g x✝
                                                            -- 🎉 no goals
#align submonoid.localization_map.lift_comp Submonoid.LocalizationMap.lift_comp
#align add_submonoid.localization_map.lift_comp AddSubmonoid.LocalizationMap.lift_comp

@[to_additive (attr := simp)]
theorem lift_of_comp (j : N →* P) : f.lift (f.isUnit_comp j) = j := by
  ext
  -- ⊢ ↑(lift f (_ : ∀ (y : { x // x ∈ S }), IsUnit (↑(MonoidHom.comp j (toMap f))  …
  rw [lift_spec]
  -- ⊢ ↑(MonoidHom.comp j (toMap f)) (sec f x✝).fst = ↑(MonoidHom.comp j (toMap f)) …
  show j _ = j _ * _
  -- ⊢ ↑j (↑(toMap f) (sec f x✝).fst) = ↑j (↑(toMap f) ↑(sec f x✝).snd) * ↑j x✝
  erw [← j.map_mul, sec_spec']
  -- 🎉 no goals
#align submonoid.localization_map.lift_of_comp Submonoid.LocalizationMap.lift_of_comp
#align add_submonoid.localization_map.lift_of_comp AddSubmonoid.LocalizationMap.lift_of_comp

@[to_additive]
theorem epic_of_localizationMap {j k : N →* P} (h : ∀ a, j.comp f.toMap a = k.comp f.toMap a) :
    j = k := by
  rw [← f.lift_of_comp j, ← f.lift_of_comp k]
  -- ⊢ lift f (_ : ∀ (y : { x // x ∈ S }), IsUnit (↑(MonoidHom.comp j (toMap f)) ↑y …
  congr 1 with x; exact h x
  -- ⊢ ↑(MonoidHom.comp j (toMap f)) x = ↑(MonoidHom.comp k (toMap f)) x
                  -- 🎉 no goals
#align submonoid.localization_map.epic_of_localization_map Submonoid.LocalizationMap.epic_of_localizationMap
#align add_submonoid.localization_map.epic_of_localization_map AddSubmonoid.LocalizationMap.epic_of_localizationMap

@[to_additive]
theorem lift_unique {j : N →* P} (hj : ∀ x, j (f.toMap x) = g x) : f.lift hg = j := by
  ext
  -- ⊢ ↑(lift f hg) x✝ = ↑j x✝
  rw [lift_spec, ← hj, ← hj, ← j.map_mul]
  -- ⊢ ↑j (↑(toMap f) (sec f x✝).fst) = ↑j (↑(toMap f) ↑(sec f x✝).snd * x✝)
  apply congr_arg
  -- ⊢ ↑(toMap f) (sec f x✝).fst = ↑(toMap f) ↑(sec f x✝).snd * x✝
  rw [← sec_spec']
  -- 🎉 no goals
#align submonoid.localization_map.lift_unique Submonoid.LocalizationMap.lift_unique
#align add_submonoid.localization_map.lift_unique AddSubmonoid.LocalizationMap.lift_unique

@[to_additive (attr := simp)]
theorem lift_id (x) : f.lift f.map_units x = x :=
  FunLike.ext_iff.1 (f.lift_of_comp <| MonoidHom.id N) x
#align submonoid.localization_map.lift_id Submonoid.LocalizationMap.lift_id
#align add_submonoid.localization_map.lift_id AddSubmonoid.LocalizationMap.lift_id

/-- Given two Localization maps `f : M →* N, k : M →* P` for a Submonoid `S ⊆ M`, the hom
from `P` to `N` induced by `f` is left inverse to the hom from `N` to `P` induced by `k`. -/
@[to_additive (attr := simp)
    "Given two Localization maps `f : M →+ N, k : M →+ P` for a Submonoid `S ⊆ M`, the hom
from `P` to `N` induced by `f` is left inverse to the hom from `N` to `P` induced by `k`."]
theorem lift_left_inverse {k : LocalizationMap S P} (z : N) :
    k.lift f.map_units (f.lift k.map_units z) = z := by
  rw [lift_spec]
  -- ⊢ ↑(toMap f) (sec k (↑(lift f (_ : ∀ (y : { x // x ∈ S }), IsUnit (↑(toMap k)  …
  cases' f.surj z with x hx
  -- ⊢ ↑(toMap f) (sec k (↑(lift f (_ : ∀ (y : { x // x ∈ S }), IsUnit (↑(toMap k)  …
  conv_rhs =>
    congr
    next => skip
    rw [f.eq_mk'_iff_mul_eq.2 hx]
  rw [mk', ← mul_assoc, mul_inv_right f.map_units, ← f.toMap.map_mul, ← f.toMap.map_mul]
  -- ⊢ ↑(toMap f) ((sec k (↑(lift f (_ : ∀ (y : { x // x ∈ S }), IsUnit (↑(toMap k) …
  apply k.eq_of_eq f.map_units
  -- ⊢ ↑(toMap k) ((sec k (↑(lift f (_ : ∀ (y : { x // x ∈ S }), IsUnit (↑(toMap k) …
  rw [k.toMap.map_mul, k.toMap.map_mul, ← sec_spec, mul_assoc, lift_spec_mul]
  -- ⊢ ↑(toMap k) (sec f z).fst * (↑(toMap k) ↑(sec k (↑(lift f (_ : ∀ (y : { x //  …
  repeat' rw [← k.toMap.map_mul]
  -- ⊢ ↑(toMap k) ((sec f z).fst * (↑(sec k (↑(lift f (_ : ∀ (y : { x // x ∈ S }),  …
  apply f.eq_of_eq k.map_units
  -- ⊢ ↑(toMap f) ((sec f z).fst * (↑(sec k (↑(lift f (_ : ∀ (y : { x // x ∈ S }),  …
  repeat' rw [f.toMap.map_mul]
  -- ⊢ ↑(toMap f) (sec f z).fst * (↑(toMap f) ↑(sec k (↑(lift f (_ : ∀ (y : { x //  …
  rw [sec_spec', ← hx]
  -- ⊢ ↑(toMap f) ↑(sec f z).snd * z * (↑(toMap f) ↑(sec k (↑(lift f (_ : ∀ (y : {  …
  ac_rfl
  -- 🎉 no goals
#align submonoid.localization_map.lift_left_inverse Submonoid.LocalizationMap.lift_left_inverse
#align add_submonoid.localization_map.lift_left_inverse AddSubmonoid.LocalizationMap.lift_left_inverse

@[to_additive]
theorem lift_surjective_iff :
    Function.Surjective (f.lift hg) ↔ ∀ v : P, ∃ x : M × S, v * g x.2 = g x.1 := by
  constructor
  -- ⊢ Surjective ↑(lift f hg) → ∀ (v : P), ∃ x, v * ↑g ↑x.snd = ↑g x.fst
  · intro H v
    -- ⊢ ∃ x, v * ↑g ↑x.snd = ↑g x.fst
    obtain ⟨z, hz⟩ := H v
    -- ⊢ ∃ x, v * ↑g ↑x.snd = ↑g x.fst
    obtain ⟨x, hx⟩ := f.surj z
    -- ⊢ ∃ x, v * ↑g ↑x.snd = ↑g x.fst
    use x
    -- ⊢ v * ↑g ↑x.snd = ↑g x.fst
    rw [← hz, f.eq_mk'_iff_mul_eq.2 hx, lift_mk', mul_assoc, mul_comm _ (g ↑x.2)]
    -- ⊢ ↑g x.fst * (↑g ↑x.snd * ↑(↑(IsUnit.liftRight (MonoidHom.restrict g S) hg) x. …
    erw [IsUnit.mul_liftRight_inv (g.restrict S) hg, mul_one]
    -- 🎉 no goals
  · intro H v
    -- ⊢ ∃ a, ↑(lift f hg) a = v
    obtain ⟨x, hx⟩ := H v
    -- ⊢ ∃ a, ↑(lift f hg) a = v
    use f.mk' x.1 x.2
    -- ⊢ ↑(lift f hg) (mk' f x.fst x.snd) = v
    rw [lift_mk', mul_inv_left hg, mul_comm, ← hx]
    -- 🎉 no goals
#align submonoid.localization_map.lift_surjective_iff Submonoid.LocalizationMap.lift_surjective_iff
#align add_submonoid.localization_map.lift_surjective_iff AddSubmonoid.LocalizationMap.lift_surjective_iff

@[to_additive]
theorem lift_injective_iff :
    Function.Injective (f.lift hg) ↔ ∀ x y, f.toMap x = f.toMap y ↔ g x = g y := by
  constructor
  -- ⊢ Injective ↑(lift f hg) → ∀ (x y : M), ↑(toMap f) x = ↑(toMap f) y ↔ ↑g x = ↑ …
  · intro H x y
    -- ⊢ ↑(toMap f) x = ↑(toMap f) y ↔ ↑g x = ↑g y
    constructor
    -- ⊢ ↑(toMap f) x = ↑(toMap f) y → ↑g x = ↑g y
    · exact f.eq_of_eq hg
      -- 🎉 no goals
    · intro h
      -- ⊢ ↑(toMap f) x = ↑(toMap f) y
      rw [← f.lift_eq hg, ← f.lift_eq hg] at h
      -- ⊢ ↑(toMap f) x = ↑(toMap f) y
      exact H h
      -- 🎉 no goals
  · intro H z w h
    -- ⊢ z = w
    obtain ⟨_, _⟩ := f.surj z
    -- ⊢ z = w
    obtain ⟨_, _⟩ := f.surj w
    -- ⊢ z = w
    rw [← f.mk'_sec z, ← f.mk'_sec w]
    -- ⊢ mk' f (sec f z).fst (sec f z).snd = mk' f (sec f w).fst (sec f w).snd
    exact (mul_inv f.map_units).2 ((H _ _).2 <| (mul_inv hg).1 h)
    -- 🎉 no goals
#align submonoid.localization_map.lift_injective_iff Submonoid.LocalizationMap.lift_injective_iff
#align add_submonoid.localization_map.lift_injective_iff AddSubmonoid.LocalizationMap.lift_injective_iff

variable {T : Submonoid P} (hy : ∀ y : S, g y ∈ T) {Q : Type*} [CommMonoid Q]
  (k : LocalizationMap T Q)

/-- Given a `CommMonoid` homomorphism `g : M →* P` where for Submonoids `S ⊆ M, T ⊆ P` we have
`g(S) ⊆ T`, the induced Monoid homomorphism from the Localization of `M` at `S` to the
Localization of `P` at `T`: if `f : M →* N` and `k : P →* Q` are Localization maps for `S` and
`T` respectively, we send `z : N` to `k (g x) * (k (g y))⁻¹`, where `(x, y) : M × S` are such
that `z = f x * (f y)⁻¹`. -/
@[to_additive
    "Given an `AddCommMonoid` homomorphism `g : M →+ P` where for Submonoids `S ⊆ M, T ⊆ P` we have
`g(S) ⊆ T`, the induced AddMonoid homomorphism from the Localization of `M` at `S` to the
Localization of `P` at `T`: if `f : M →+ N` and `k : P →+ Q` are Localization maps for `S` and
`T` respectively, we send `z : N` to `k (g x) - k (g y)`, where `(x, y) : M × S` are such
that `z = f x - f y`."]
noncomputable def map : N →* Q :=
  @lift _ _ _ _ _ _ _ f (k.toMap.comp g) fun y ↦ k.map_units ⟨g y, hy y⟩
#align submonoid.localization_map.map Submonoid.LocalizationMap.map
#align add_submonoid.localization_map.map AddSubmonoid.LocalizationMap.map

variable {k}

@[to_additive]
theorem map_eq (x) : f.map hy k (f.toMap x) = k.toMap (g x) :=
  f.lift_eq (fun y ↦ k.map_units ⟨g y, hy y⟩) x
#align submonoid.localization_map.map_eq Submonoid.LocalizationMap.map_eq
#align add_submonoid.localization_map.map_eq AddSubmonoid.LocalizationMap.map_eq

@[to_additive (attr := simp)]
theorem map_comp : (f.map hy k).comp f.toMap = k.toMap.comp g :=
  f.lift_comp fun y ↦ k.map_units ⟨g y, hy y⟩
#align submonoid.localization_map.map_comp Submonoid.LocalizationMap.map_comp
#align add_submonoid.localization_map.map_comp AddSubmonoid.LocalizationMap.map_comp

@[to_additive]
theorem map_mk' (x) (y : S) : f.map hy k (f.mk' x y) = k.mk' (g x) ⟨g y, hy y⟩ := by
  rw [map, lift_mk', mul_inv_left]
  -- ⊢ ↑(MonoidHom.comp (toMap k) g) x = ↑(MonoidHom.comp (toMap k) g) ↑y * mk' k ( …
  · show k.toMap (g x) = k.toMap (g y) * _
    -- ⊢ ↑(toMap k) (↑g x) = ↑(toMap k) (↑g ↑y) * mk' k (↑g x) { val := ↑g ↑y, proper …
    rw [mul_mk'_eq_mk'_of_mul]
    -- ⊢ ↑(toMap k) (↑g x) = mk' k (↑g ↑y * ↑g x) { val := ↑g ↑y, property := (_ : ↑g …
    exact (k.mk'_mul_cancel_left (g x) ⟨g y, hy y⟩).symm
    -- 🎉 no goals
#align submonoid.localization_map.map_mk' Submonoid.LocalizationMap.map_mk'
#align add_submonoid.localization_map.map_mk' AddSubmonoid.LocalizationMap.map_mk'

/-- Given Localization maps `f : M →* N, k : P →* Q` for Submonoids `S, T` respectively, if a
`CommMonoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
`u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) * u` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
    "Given Localization maps `f : M →+ N, k : P →+ Q` for Submonoids `S, T` respectively, if an
`AddCommMonoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`,
`u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) + u` where `x : M, y ∈ S` are such that
`z + f y = f x`."]
theorem map_spec (z u) : f.map hy k z = u ↔ k.toMap (g (f.sec z).1) = k.toMap (g (f.sec z).2) * u :=
  f.lift_spec (fun y ↦ k.map_units ⟨g y, hy y⟩) _ _
#align submonoid.localization_map.map_spec Submonoid.LocalizationMap.map_spec
#align add_submonoid.localization_map.map_spec AddSubmonoid.LocalizationMap.map_spec

/-- Given Localization maps `f : M →* N, k : P →* Q` for Submonoids `S, T` respectively, if a
`CommMonoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `f.map hy k z * k (g y) = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
    "Given Localization maps `f : M →+ N, k : P →+ Q` for Submonoids `S, T` respectively, if an
`AddCommMonoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`,
we have `f.map hy k z + k (g y) = k (g x)` where `x : M, y ∈ S` are such that
`z + f y = f x`."]
theorem map_mul_right (z) : f.map hy k z * k.toMap (g (f.sec z).2) = k.toMap (g (f.sec z).1) :=
  f.lift_mul_right (fun y ↦ k.map_units ⟨g y, hy y⟩) _
#align submonoid.localization_map.map_mul_right Submonoid.LocalizationMap.map_mul_right
#align add_submonoid.localization_map.map_add_right AddSubmonoid.LocalizationMap.map_add_right

/-- Given Localization maps `f : M →* N, k : P →* Q` for Submonoids `S, T` respectively, if a
`CommMonoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `k (g y) * f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
    "Given Localization maps `f : M →+ N, k : P →+ Q` for Submonoids `S, T` respectively if an
`AddCommMonoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`,
we have `k (g y) + f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that
`z + f y = f x`."]
theorem map_mul_left (z) : k.toMap (g (f.sec z).2) * f.map hy k z = k.toMap (g (f.sec z).1) := by
  rw [mul_comm, f.map_mul_right]
  -- 🎉 no goals
#align submonoid.localization_map.map_mul_left Submonoid.LocalizationMap.map_mul_left
#align add_submonoid.localization_map.map_add_left AddSubmonoid.LocalizationMap.map_add_left

@[to_additive (attr := simp)]
theorem map_id (z : N) : f.map (fun y ↦ show MonoidHom.id M y ∈ S from y.2) f z = z :=
  f.lift_id z
#align submonoid.localization_map.map_id Submonoid.LocalizationMap.map_id
#align add_submonoid.localization_map.map_id AddSubmonoid.LocalizationMap.map_id

/-- If `CommMonoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive
    "If `AddCommMonoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`."]
theorem map_comp_map {A : Type*} [CommMonoid A] {U : Submonoid A} {R} [CommMonoid R]
    (j : LocalizationMap U R) {l : P →* A} (hl : ∀ w : T, l w ∈ U) :
    (k.map hl j).comp (f.map hy k) =
    f.map (fun x ↦ show l.comp g x ∈ U from hl ⟨g x, hy x⟩) j := by
  ext z
  -- ⊢ ↑(MonoidHom.comp (map k hl j) (map f hy k)) z = ↑(map f (_ : ∀ (x : { x // x …
  show j.toMap _ * _ = j.toMap (l _) * _
  -- ⊢ ↑(toMap j) (↑l (sec k (↑(map f hy k) z)).fst) * ↑(↑(IsUnit.liftRight (Monoid …
  rw [mul_inv_left, ← mul_assoc, mul_inv_right]
  -- ⊢ ↑(toMap j) (↑l (sec k (↑(map f hy k) z)).fst) * ↑(MonoidHom.comp (toMap j) ( …
  show j.toMap _ * j.toMap (l (g _)) = j.toMap (l _) * _
  -- ⊢ ↑(toMap j) (↑l (sec k (↑(map f hy k) z)).fst) * ↑(toMap j) (↑l (↑g ↑(sec f z …
  rw [← j.toMap.map_mul, ← j.toMap.map_mul, ← l.map_mul, ← l.map_mul]
  -- ⊢ ↑(toMap j) (↑l ((sec k (↑(map f hy k) z)).fst * ↑g ↑(sec f z).snd)) = ↑(toMa …
  exact
    k.comp_eq_of_eq hl j
      (by rw [k.toMap.map_mul, k.toMap.map_mul, sec_spec', mul_assoc, map_mul_right])
#align submonoid.localization_map.map_comp_map Submonoid.LocalizationMap.map_comp_map
#align add_submonoid.localization_map.map_comp_map AddSubmonoid.LocalizationMap.map_comp_map

/-- If `CommMonoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive
    "If `AddCommMonoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`."]
theorem map_map {A : Type*} [CommMonoid A] {U : Submonoid A} {R} [CommMonoid R]
    (j : LocalizationMap U R) {l : P →* A} (hl : ∀ w : T, l w ∈ U) (x) :
    k.map hl j (f.map hy k x) = f.map (fun x ↦ show l.comp g x ∈ U from hl ⟨g x, hy x⟩) j x := by
-- Porting note: Lean has a hard time figuring out what the implicit arguments should be
-- when calling `map_comp_map`. Hence the original line below has to be replaced by a much more
-- explicit one
--  rw [← f.map_comp_map hy j hl]
  rw [← @map_comp_map M _ S N _ P _ f g T hy Q _ k A _ U R _ j l hl]
  -- ⊢ ↑(map k hl j) (↑(map f hy k) x) = ↑(MonoidHom.comp (map k hl j) (map f hy k) …
  simp only [MonoidHom.coe_comp, comp_apply]
  -- 🎉 no goals
#align submonoid.localization_map.map_map Submonoid.LocalizationMap.map_map
#align add_submonoid.localization_map.map_map AddSubmonoid.LocalizationMap.map_map

section AwayMap

variable (x : M)

/-- Given `x : M`, the type of `CommMonoid` homomorphisms `f : M →* N` such that `N`
is isomorphic to the Localization of `M` at the Submonoid generated by `x`. -/
@[to_additive (attr := reducible)
    "Given `x : M`, the type of `AddCommMonoid` homomorphisms `f : M →+ N` such that `N`
is isomorphic to the localization of `M` at the AddSubmonoid generated by `x`."]
def AwayMap (N' : Type*) [CommMonoid N'] := LocalizationMap (powers x) N'
#align submonoid.localization_map.away_map Submonoid.LocalizationMap.AwayMap
#align add_submonoid.localization_map.away_map AddSubmonoid.LocalizationMap.AwayMap

variable (F : AwayMap x N)

/-- Given `x : M` and a Localization map `F : M →* N` away from `x`, `invSelf` is `(F x)⁻¹`. -/
noncomputable def AwayMap.invSelf : N := F.mk' 1 ⟨x, mem_powers _⟩
#align submonoid.localization_map.away_map.inv_self Submonoid.LocalizationMap.AwayMap.invSelf

/-- Given `x : M`, a Localization map `F : M →* N` away from `x`, and a map of `CommMonoid`s
`g : M →* P` such that `g x` is invertible, the homomorphism induced from `N` to `P` sending
`z : N` to `g y * (g x)⁻ⁿ`, where `y : M, n : ℕ` are such that `z = F y * (F x)⁻ⁿ`. -/
noncomputable def AwayMap.lift (hg : IsUnit (g x)) : N →* P :=
  Submonoid.LocalizationMap.lift F fun y ↦
    show IsUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      -- ⊢ IsUnit (↑g ↑y)
      rw [← hn, g.map_pow]
      -- ⊢ IsUnit (↑g x ^ n)
      exact IsUnit.pow n hg
      -- 🎉 no goals
#align submonoid.localization_map.away_map.lift Submonoid.LocalizationMap.AwayMap.lift

@[simp]
theorem AwayMap.lift_eq (hg : IsUnit (g x)) (a : M) : F.lift x hg (F.toMap a) = g a :=
  Submonoid.LocalizationMap.lift_eq _ _ _
#align submonoid.localization_map.away_map.lift_eq Submonoid.LocalizationMap.AwayMap.lift_eq

@[simp]
theorem AwayMap.lift_comp (hg : IsUnit (g x)) : (F.lift x hg).comp F.toMap = g :=
  Submonoid.LocalizationMap.lift_comp _ _
#align submonoid.localization_map.away_map.lift_comp Submonoid.LocalizationMap.AwayMap.lift_comp

/-- Given `x y : M` and Localization maps `F : M →* N, G : M →* P` away from `x` and `x * y`
respectively, the homomorphism induced from `N` to `P`. -/
noncomputable def awayToAwayRight (y : M) (G : AwayMap (x * y) P) : N →* P :=
  F.lift x <|
    show IsUnit (G.toMap x) from
      isUnit_of_mul_eq_one (G.toMap x) (G.mk' y ⟨x * y, mem_powers _⟩) <| by
        rw [mul_mk'_eq_mk'_of_mul, mk'_self]
        -- 🎉 no goals
#align submonoid.localization_map.away_to_away_right Submonoid.LocalizationMap.awayToAwayRight

end AwayMap

end LocalizationMap

end Submonoid

namespace AddSubmonoid

namespace LocalizationMap

section AwayMap

variable {A : Type*} [AddCommMonoid A] (x : A) {B : Type*} [AddCommMonoid B] (F : AwayMap x B)
  {C : Type*} [AddCommMonoid C] {g : A →+ C}

/-- Given `x : A` and a Localization map `F : A →+ B` away from `x`, `neg_self` is `- (F x)`. -/
noncomputable def AwayMap.negSelf : B :=
  F.mk' 0 ⟨x, mem_multiples _⟩
#align add_submonoid.localization_map.away_map.neg_self AddSubmonoid.LocalizationMap.AwayMap.negSelf

/-- Given `x : A`, a localization map `F : A →+ B` away from `x`, and a map of `AddCommMonoid`s
`g : A →+ C` such that `g x` is invertible, the homomorphism induced from `B` to `C` sending
`z : B` to `g y - n • g x`, where `y : A, n : ℕ` are such that `z = F y - n • F x`. -/
noncomputable def AwayMap.lift (hg : IsAddUnit (g x)) : B →+ C :=
  AddSubmonoid.LocalizationMap.lift F fun y ↦
    show IsAddUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      -- ⊢ IsAddUnit (↑g ↑y)
      rw [← hn]
      -- ⊢ IsAddUnit (↑g ((fun i => i • x) n))
      dsimp
      -- ⊢ IsAddUnit (↑g (n • x))
      rw [g.map_nsmul]
      -- ⊢ IsAddUnit (n • ↑g x)
      exact IsAddUnit.map (nsmulAddMonoidHom n : C →+ C) hg
      -- 🎉 no goals
#align add_submonoid.localization_map.away_map.lift AddSubmonoid.LocalizationMap.AwayMap.lift

@[simp]
theorem AwayMap.lift_eq (hg : IsAddUnit (g x)) (a : A) : F.lift x hg (F.toMap a) = g a :=
  AddSubmonoid.LocalizationMap.lift_eq _ _ _
#align add_submonoid.localization_map.away_map.lift_eq AddSubmonoid.LocalizationMap.AwayMap.lift_eq

@[simp]
theorem AwayMap.lift_comp (hg : IsAddUnit (g x)) : (F.lift x hg).comp F.toMap = g :=
  AddSubmonoid.LocalizationMap.lift_comp _ _
#align add_submonoid.localization_map.away_map.lift_comp AddSubmonoid.LocalizationMap.AwayMap.lift_comp

/-- Given `x y : A` and Localization maps `F : A →+ B, G : A →+ C` away from `x` and `x + y`
respectively, the homomorphism induced from `B` to `C`. -/
noncomputable def awayToAwayRight (y : A) (G : AwayMap (x + y) C) : B →+ C :=
  F.lift x <|
    show IsAddUnit (G.toMap x) from
      isAddUnit_of_add_eq_zero (G.toMap x) (G.mk' y ⟨x + y, mem_multiples _⟩) <| by
        rw [add_mk'_eq_mk'_of_add, mk'_self]
        -- 🎉 no goals
#align add_submonoid.localization_map.away_to_away_right AddSubmonoid.LocalizationMap.awayToAwayRight

end AwayMap

end LocalizationMap

end AddSubmonoid

namespace Submonoid

namespace LocalizationMap

variable (f : S.LocalizationMap N) {g : M →* P} (hg : ∀ y : S, IsUnit (g y)) {T : Submonoid P}
  {Q : Type*} [CommMonoid Q]

/-- If `f : M →* N` and `k : M →* P` are Localization maps for a Submonoid `S`, we get an
isomorphism of `N` and `P`. -/
@[to_additive
    "If `f : M →+ N` and `k : M →+ R` are Localization maps for an AddSubmonoid `S`, we get an
isomorphism of `N` and `R`."]
noncomputable def mulEquivOfLocalizations (k : LocalizationMap S P) : N ≃* P :=
{ toFun := f.lift k.map_units
  invFun := k.lift f.map_units
  left_inv := f.lift_left_inverse
  right_inv := k.lift_left_inverse
  map_mul' := MonoidHom.map_mul _ }
#align submonoid.localization_map.mul_equiv_of_localizations Submonoid.LocalizationMap.mulEquivOfLocalizations
#align add_submonoid.localization_map.add_equiv_of_localizations AddSubmonoid.LocalizationMap.addEquivOfLocalizations

@[to_additive (attr := simp)]
theorem mulEquivOfLocalizations_apply {k : LocalizationMap S P} {x} :
    f.mulEquivOfLocalizations k x = f.lift k.map_units x := rfl
#align submonoid.localization_map.mul_equiv_of_localizations_apply Submonoid.LocalizationMap.mulEquivOfLocalizations_apply
#align add_submonoid.localization_map.add_equiv_of_localizations_apply AddSubmonoid.LocalizationMap.addEquivOfLocalizations_apply

@[to_additive (attr := simp)]
theorem mulEquivOfLocalizations_symm_apply {k : LocalizationMap S P} {x} :
    (f.mulEquivOfLocalizations k).symm x = k.lift f.map_units x := rfl
#align submonoid.localization_map.mul_equiv_of_localizations_symm_apply Submonoid.LocalizationMap.mulEquivOfLocalizations_symm_apply
#align add_submonoid.localization_map.add_equiv_of_localizations_symm_apply AddSubmonoid.LocalizationMap.addEquivOfLocalizations_symm_apply

@[to_additive]
theorem mulEquivOfLocalizations_symm_eq_mulEquivOfLocalizations {k : LocalizationMap S P} :
    (k.mulEquivOfLocalizations f).symm = f.mulEquivOfLocalizations k := rfl
#align submonoid.localization_map.mul_equiv_of_localizations_symm_eq_mul_equiv_of_localizations Submonoid.LocalizationMap.mulEquivOfLocalizations_symm_eq_mulEquivOfLocalizations
#align add_submonoid.localization_map.add_equiv_of_localizations_symm_eq_add_equiv_of_localizations AddSubmonoid.LocalizationMap.addEquivOfLocalizations_symm_eq_addEquivOfLocalizations

/-- If `f : M →* N` is a Localization map for a Submonoid `S` and `k : N ≃* P` is an isomorphism
of `CommMonoid`s, `k ∘ f` is a Localization map for `M` at `S`. -/
@[to_additive
    "If `f : M →+ N` is a Localization map for a Submonoid `S` and `k : N ≃+ P` is an isomorphism
of `AddCommMonoid`s, `k ∘ f` is a Localization map for `M` at `S`."]
def ofMulEquivOfLocalizations (k : N ≃* P) : LocalizationMap S P :=
  (k.toMonoidHom.comp f.toMap).toLocalizationMap (fun y ↦ isUnit_comp f k.toMonoidHom y)
    (fun v ↦
      let ⟨z, hz⟩ := k.toEquiv.surjective v
      let ⟨x, hx⟩ := f.surj z
      ⟨x, show v * k _ = k _ by rw [← hx, k.map_mul, ← hz]; rfl⟩)
                                -- ⊢ ↑k.toEquiv z * ↑k (↑(toMap f) ↑x.snd) = ↑k z * ↑k (↑(toMap f) ↑x.snd)
                                                            -- 🎉 no goals
    fun x y ↦ k.apply_eq_iff_eq.trans f.eq_iff_exists
#align submonoid.localization_map.of_mul_equiv_of_localizations Submonoid.LocalizationMap.ofMulEquivOfLocalizations
#align add_submonoid.localization_map.of_add_equiv_of_localizations AddSubmonoid.LocalizationMap.ofAddEquivOfLocalizations

@[to_additive (attr := simp)]
theorem ofMulEquivOfLocalizations_apply {k : N ≃* P} (x) :
    (f.ofMulEquivOfLocalizations k).toMap x = k (f.toMap x) := rfl
#align submonoid.localization_map.of_mul_equiv_of_localizations_apply Submonoid.LocalizationMap.ofMulEquivOfLocalizations_apply
#align add_submonoid.localization_map.of_add_equiv_of_localizations_apply AddSubmonoid.LocalizationMap.ofAddEquivOfLocalizations_apply

@[to_additive]
theorem ofMulEquivOfLocalizations_eq {k : N ≃* P} :
    (f.ofMulEquivOfLocalizations k).toMap = k.toMonoidHom.comp f.toMap := rfl
#align submonoid.localization_map.of_mul_equiv_of_localizations_eq Submonoid.LocalizationMap.ofMulEquivOfLocalizations_eq
#align add_submonoid.localization_map.of_add_equiv_of_localizations_eq AddSubmonoid.LocalizationMap.ofAddEquivOfLocalizations_eq

@[to_additive]
theorem symm_comp_ofMulEquivOfLocalizations_apply {k : N ≃* P} (x) :
    k.symm ((f.ofMulEquivOfLocalizations k).toMap x) = f.toMap x := k.symm_apply_apply (f.toMap x)
#align submonoid.localization_map.symm_comp_of_mul_equiv_of_localizations_apply Submonoid.LocalizationMap.symm_comp_ofMulEquivOfLocalizations_apply
#align add_submonoid.localization_map.symm_comp_of_add_equiv_of_localizations_apply AddSubmonoid.LocalizationMap.symm_comp_ofAddEquivOfLocalizations_apply

@[to_additive]
theorem symm_comp_ofMulEquivOfLocalizations_apply' {k : P ≃* N} (x) :
    k ((f.ofMulEquivOfLocalizations k.symm).toMap x) = f.toMap x := k.apply_symm_apply (f.toMap x)
#align submonoid.localization_map.symm_comp_of_mul_equiv_of_localizations_apply' Submonoid.LocalizationMap.symm_comp_ofMulEquivOfLocalizations_apply'
#align add_submonoid.localization_map.symm_comp_of_add_equiv_of_localizations_apply' AddSubmonoid.LocalizationMap.symm_comp_ofAddEquivOfLocalizations_apply'

@[to_additive]
theorem ofMulEquivOfLocalizations_eq_iff_eq {k : N ≃* P} {x y} :
    (f.ofMulEquivOfLocalizations k).toMap x = y ↔ f.toMap x = k.symm y :=
  k.toEquiv.eq_symm_apply.symm
#align submonoid.localization_map.of_mul_equiv_of_localizations_eq_iff_eq Submonoid.LocalizationMap.ofMulEquivOfLocalizations_eq_iff_eq
#align add_submonoid.localization_map.of_add_equiv_of_localizations_eq_iff_eq AddSubmonoid.LocalizationMap.ofAddEquivOfLocalizations_eq_iff_eq

@[to_additive addEquivOfLocalizations_right_inv]
theorem mulEquivOfLocalizations_right_inv (k : LocalizationMap S P) :
    f.ofMulEquivOfLocalizations (f.mulEquivOfLocalizations k) = k :=
  toMap_injective <| f.lift_comp k.map_units
#align submonoid.localization_map.mul_equiv_of_localizations_right_inv Submonoid.LocalizationMap.mulEquivOfLocalizations_right_inv
#align add_submonoid.localization_map.add_equiv_of_localizations_right_inv AddSubmonoid.LocalizationMap.addEquivOfLocalizations_right_inv

-- @[simp] -- Porting note: simp can prove this
@[to_additive addEquivOfLocalizations_right_inv_apply]
theorem mulEquivOfLocalizations_right_inv_apply {k : LocalizationMap S P} {x} :
    (f.ofMulEquivOfLocalizations (f.mulEquivOfLocalizations k)).toMap x = k.toMap x := by simp
                                                                                          -- 🎉 no goals
#align submonoid.localization_map.mul_equiv_of_localizations_right_inv_apply Submonoid.LocalizationMap.mulEquivOfLocalizations_right_inv_apply
#align add_submonoid.localization_map.add_equiv_of_localizations_right_inv_apply AddSubmonoid.LocalizationMap.addEquivOfLocalizations_right_inv_apply

@[to_additive]
theorem mulEquivOfLocalizations_left_inv (k : N ≃* P) :
    f.mulEquivOfLocalizations (f.ofMulEquivOfLocalizations k) = k :=
  FunLike.ext _ _ fun x ↦ FunLike.ext_iff.1 (f.lift_of_comp k.toMonoidHom) x
#align submonoid.localization_map.mul_equiv_of_localizations_left_inv Submonoid.LocalizationMap.mulEquivOfLocalizations_left_inv
#align add_submonoid.localization_map.add_equiv_of_localizations_left_neg AddSubmonoid.LocalizationMap.addEquivOfLocalizations_left_neg

-- @[simp] -- Porting note: simp can prove this
@[to_additive]
theorem mulEquivOfLocalizations_left_inv_apply {k : N ≃* P} (x) :
    f.mulEquivOfLocalizations (f.ofMulEquivOfLocalizations k) x = k x := by simp
                                                                            -- 🎉 no goals
#align submonoid.localization_map.mul_equiv_of_localizations_left_inv_apply Submonoid.LocalizationMap.mulEquivOfLocalizations_left_inv_apply
#align add_submonoid.localization_map.add_equiv_of_localizations_left_neg_apply AddSubmonoid.LocalizationMap.addEquivOfLocalizations_left_neg_apply

@[to_additive (attr := simp)]
theorem ofMulEquivOfLocalizations_id : f.ofMulEquivOfLocalizations (MulEquiv.refl N) = f := by
  ext; rfl
  -- ⊢ ↑(toMap (ofMulEquivOfLocalizations f (MulEquiv.refl N))) x✝ = ↑(toMap f) x✝
       -- 🎉 no goals
#align submonoid.localization_map.of_mul_equiv_of_localizations_id Submonoid.LocalizationMap.ofMulEquivOfLocalizations_id
#align add_submonoid.localization_map.of_add_equiv_of_localizations_id AddSubmonoid.LocalizationMap.ofAddEquivOfLocalizations_id

@[to_additive]
theorem ofMulEquivOfLocalizations_comp {k : N ≃* P} {j : P ≃* Q} :
    (f.ofMulEquivOfLocalizations (k.trans j)).toMap =
      j.toMonoidHom.comp (f.ofMulEquivOfLocalizations k).toMap :=
  by ext; rfl
     -- ⊢ ↑(toMap (ofMulEquivOfLocalizations f (MulEquiv.trans k j))) x✝ = ↑(MonoidHom …
          -- 🎉 no goals
#align submonoid.localization_map.of_mul_equiv_of_localizations_comp Submonoid.LocalizationMap.ofMulEquivOfLocalizations_comp
#align add_submonoid.localization_map.of_add_equiv_of_localizations_comp AddSubmonoid.LocalizationMap.ofAddEquivOfLocalizations_comp

/-- Given `CommMonoid`s `M, P` and Submonoids `S ⊆ M, T ⊆ P`, if `f : M →* N` is a Localization
map for `S` and `k : P ≃* M` is an isomorphism of `CommMonoid`s such that `k(T) = S`, `f ∘ k`
is a Localization map for `T`. -/
@[to_additive
    "Given `AddCommMonoid`s `M, P` and `AddSubmonoid`s `S ⊆ M, T ⊆ P`, if `f : M →* N` is a
    Localization map for `S` and `k : P ≃+ M` is an isomorphism of `AddCommMonoid`s such that
    `k(T) = S`, `f ∘ k` is a Localization map for `T`."]
def ofMulEquivOfDom {k : P ≃* M} (H : T.map k.toMonoidHom = S) : LocalizationMap T N :=
  let H' : S.comap k.toMonoidHom = T :=
    H ▸ (SetLike.coe_injective <| T.1.1.preimage_image_eq k.toEquiv.injective)
  (f.toMap.comp k.toMonoidHom).toLocalizationMap
    (fun y ↦
      let ⟨z, hz⟩ := f.map_units ⟨k y, H ▸ Set.mem_image_of_mem k y.2⟩
      ⟨z, hz⟩)
    (fun z ↦
      let ⟨x, hx⟩ := f.surj z
      let ⟨v, hv⟩ := k.toEquiv.surjective x.1
      let ⟨w, hw⟩ := k.toEquiv.surjective x.2
      ⟨(v, ⟨w, H' ▸ show k w ∈ S from hw.symm ▸ x.2.2⟩),
        show z * f.toMap (k.toEquiv w) = f.toMap (k.toEquiv v) by erw [hv, hw, hx]⟩)
                                                                  -- 🎉 no goals
    fun x y ↦
    show f.toMap _ = f.toMap _ ↔ _ by
      erw [f.eq_iff_exists]
      -- ⊢ (∃ c, ↑c * ↑(MulEquiv.toMonoidHom k) x = ↑c * ↑(MulEquiv.toMonoidHom k) y) ↔ …
      exact
        ⟨fun ⟨c, hc⟩ ↦
          let ⟨d, hd⟩ := k.toEquiv.surjective c
          ⟨⟨d, H' ▸ show k d ∈ S from hd.symm ▸ c.2⟩, by
            erw [← hd, ← k.map_mul, ← k.map_mul] at hc; exact k.toEquiv.injective hc⟩,
          fun ⟨c, hc⟩ ↦
          ⟨⟨k c, H ▸ Set.mem_image_of_mem k c.2⟩, by
            erw [← k.map_mul]; rw [hc, k.map_mul]; rfl⟩⟩
#align submonoid.localization_map.of_mul_equiv_of_dom Submonoid.LocalizationMap.ofMulEquivOfDom
#align add_submonoid.localization_map.of_add_equiv_of_dom AddSubmonoid.LocalizationMap.ofAddEquivOfDom

@[to_additive (attr := simp)]
theorem ofMulEquivOfDom_apply {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x) :
    (f.ofMulEquivOfDom H).toMap x = f.toMap (k x) := rfl
#align submonoid.localization_map.of_mul_equiv_of_dom_apply Submonoid.LocalizationMap.ofMulEquivOfDom_apply
#align add_submonoid.localization_map.of_add_equiv_of_dom_apply AddSubmonoid.LocalizationMap.ofAddEquivOfDom_apply

@[to_additive]
theorem ofMulEquivOfDom_eq {k : P ≃* M} (H : T.map k.toMonoidHom = S) :
    (f.ofMulEquivOfDom H).toMap = f.toMap.comp k.toMonoidHom :=rfl
#align submonoid.localization_map.of_mul_equiv_of_dom_eq Submonoid.LocalizationMap.ofMulEquivOfDom_eq
#align add_submonoid.localization_map.of_add_equiv_of_dom_eq AddSubmonoid.LocalizationMap.ofAddEquivOfDom_eq

@[to_additive]
theorem ofMulEquivOfDom_comp_symm {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x) :
    (f.ofMulEquivOfDom H).toMap (k.symm x) = f.toMap x :=
  congr_arg f.toMap <| k.apply_symm_apply x
#align submonoid.localization_map.of_mul_equiv_of_dom_comp_symm Submonoid.LocalizationMap.ofMulEquivOfDom_comp_symm
#align add_submonoid.localization_map.of_add_equiv_of_dom_comp_symm AddSubmonoid.LocalizationMap.ofAddEquivOfDom_comp_symm

@[to_additive]
theorem ofMulEquivOfDom_comp {k : M ≃* P} (H : T.map k.symm.toMonoidHom = S) (x) :
    (f.ofMulEquivOfDom H).toMap (k x) = f.toMap x := congr_arg f.toMap <| k.symm_apply_apply x
#align submonoid.localization_map.of_mul_equiv_of_dom_comp Submonoid.LocalizationMap.ofMulEquivOfDom_comp
#align add_submonoid.localization_map.of_add_equiv_of_dom_comp AddSubmonoid.LocalizationMap.ofAddEquivOfDom_comp

/-- A special case of `f ∘ id = f`, `f` a Localization map. -/
@[to_additive (attr := simp) "A special case of `f ∘ id = f`, `f` a Localization map."]
theorem ofMulEquivOfDom_id :
    f.ofMulEquivOfDom
        (show S.map (MulEquiv.refl M).toMonoidHom = S from
          Submonoid.ext fun x ↦ ⟨fun ⟨_, hy, h⟩ ↦ h ▸ hy, fun h ↦ ⟨x, h, rfl⟩⟩) = f :=
  by ext; rfl
     -- ⊢ ↑(toMap (ofMulEquivOfDom f (_ : Submonoid.map (MulEquiv.toMonoidHom (MulEqui …
          -- 🎉 no goals
#align submonoid.localization_map.of_mul_equiv_of_dom_id Submonoid.LocalizationMap.ofMulEquivOfDom_id
#align add_submonoid.localization_map.of_add_equiv_of_dom_id AddSubmonoid.LocalizationMap.ofAddEquivOfDom_id

/-- Given Localization maps `f : M →* N, k : P →* U` for Submonoids `S, T` respectively, an
isomorphism `j : M ≃* P` such that `j(S) = T` induces an isomorphism of localizations `N ≃* U`. -/
@[to_additive
    "Given Localization maps `f : M →+ N, k : P →+ U` for Submonoids `S, T` respectively, an
isomorphism `j : M ≃+ P` such that `j(S) = T` induces an isomorphism of localizations `N ≃+ U`."]
noncomputable def mulEquivOfMulEquiv (k : LocalizationMap T Q) {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) : N ≃* Q :=
  f.mulEquivOfLocalizations <| k.ofMulEquivOfDom H
#align submonoid.localization_map.mul_equiv_of_mul_equiv Submonoid.LocalizationMap.mulEquivOfMulEquiv
#align add_submonoid.localization_map.add_equiv_of_add_equiv AddSubmonoid.LocalizationMap.addEquivOfAddEquiv

@[to_additive (attr := simp)]
theorem mulEquivOfMulEquiv_eq_map_apply {k : LocalizationMap T Q} {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) (x) :
    f.mulEquivOfMulEquiv k H x =
      f.map (fun y : S ↦ show j.toMonoidHom y ∈ T from H ▸ Set.mem_image_of_mem j y.2) k x := rfl
#align submonoid.localization_map.mul_equiv_of_mul_equiv_eq_map_apply Submonoid.LocalizationMap.mulEquivOfMulEquiv_eq_map_apply
#align add_submonoid.localization_map.add_equiv_of_add_equiv_eq_map_apply AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_eq_map_apply

@[to_additive]
theorem mulEquivOfMulEquiv_eq_map {k : LocalizationMap T Q} {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) :
    (f.mulEquivOfMulEquiv k H).toMonoidHom =
      f.map (fun y : S ↦ show j.toMonoidHom y ∈ T from H ▸ Set.mem_image_of_mem j y.2) k := rfl
#align submonoid.localization_map.mul_equiv_of_mul_equiv_eq_map Submonoid.LocalizationMap.mulEquivOfMulEquiv_eq_map
#align add_submonoid.localization_map.add_equiv_of_add_equiv_eq_map AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_eq_map

@[to_additive (attr := simp, nolint simpNF)]
theorem mulEquivOfMulEquiv_eq {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
    (x) :
    f.mulEquivOfMulEquiv k H (f.toMap x) = k.toMap (j x) :=
  f.map_eq (fun y : S ↦ H ▸ Set.mem_image_of_mem j y.2) _
#align submonoid.localization_map.mul_equiv_of_mul_equiv_eq Submonoid.LocalizationMap.mulEquivOfMulEquiv_eq
#align add_submonoid.localization_map.add_equiv_of_add_equiv_eq AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_eq

@[to_additive (attr := simp, nolint simpNF)]
theorem mulEquivOfMulEquiv_mk' {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
    (x y) :
    f.mulEquivOfMulEquiv k H (f.mk' x y) = k.mk' (j x) ⟨j y, H ▸ Set.mem_image_of_mem j y.2⟩ :=
  f.map_mk' (fun y : S ↦ H ▸ Set.mem_image_of_mem j y.2) _ _
#align submonoid.localization_map.mul_equiv_of_mul_equiv_mk' Submonoid.LocalizationMap.mulEquivOfMulEquiv_mk'
#align add_submonoid.localization_map.add_equiv_of_add_equiv_mk' AddSubmonoid.LocalizationMap.addEquivOfAddEquiv_mk'

@[to_additive (attr := simp, nolint simpNF)]
theorem of_mulEquivOfMulEquiv_apply {k : LocalizationMap T Q} {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) (x) :
    (f.ofMulEquivOfLocalizations (f.mulEquivOfMulEquiv k H)).toMap x = k.toMap (j x) :=
  ext_iff.1 (f.mulEquivOfLocalizations_right_inv (k.ofMulEquivOfDom H)) x
#align submonoid.localization_map.of_mul_equiv_of_mul_equiv_apply Submonoid.LocalizationMap.of_mulEquivOfMulEquiv_apply
#align add_submonoid.localization_map.of_add_equiv_of_add_equiv_apply AddSubmonoid.LocalizationMap.of_addEquivOfAddEquiv_apply

@[to_additive]
theorem of_mulEquivOfMulEquiv {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T) :
    (f.ofMulEquivOfLocalizations (f.mulEquivOfMulEquiv k H)).toMap = k.toMap.comp j.toMonoidHom :=
  MonoidHom.ext <| f.of_mulEquivOfMulEquiv_apply H
#align submonoid.localization_map.of_mul_equiv_of_mul_equiv Submonoid.LocalizationMap.of_mulEquivOfMulEquiv
#align add_submonoid.localization_map.of_add_equiv_of_add_equiv AddSubmonoid.LocalizationMap.of_addEquivOfAddEquiv

end LocalizationMap

end Submonoid

namespace Localization

variable (S)

/-- Natural homomorphism sending `x : M`, `M` a `CommMonoid`, to the equivalence class of
`(x, 1)` in the Localization of `M` at a Submonoid. -/
@[to_additive
    "Natural homomorphism sending `x : M`, `M` an `AddCommMonoid`, to the equivalence class of
`(x, 0)` in the Localization of `M` at a Submonoid."]
def monoidOf : Submonoid.LocalizationMap S (Localization S) :=
  { (r S).mk'.comp <| MonoidHom.inl M
        S with
    toFun := fun x ↦ mk x 1
    map_one' := mk_one
    map_mul' := fun x y ↦ by dsimp only; rw [mk_mul, mul_one]
                             -- ⊢ mk (x * y) 1 = mk x 1 * mk y 1
                                         -- 🎉 no goals
    map_units' := fun y ↦
      isUnit_iff_exists_inv.2 ⟨mk 1 y, by dsimp only; rw [mk_mul, mul_one, one_mul, mk_self]⟩
                                          -- ⊢ mk (↑y) 1 * mk 1 y = 1
                                                      -- 🎉 no goals
    surj' := fun z ↦ induction_on z fun x ↦
      ⟨x, by dsimp only; rw [mk_mul, mul_comm x.fst, ← mk_mul, mk_self, one_mul]⟩
             -- ⊢ mk x.fst x.snd * mk (↑x.snd) 1 = mk x.fst 1
                         -- 🎉 no goals
    eq_iff_exists' := fun x y ↦
      mk_eq_mk_iff.trans <|
        r_iff_exists.trans <|
          show (∃ c : S, ↑c * (1 * x) = c * (1 * y)) ↔ _ by rw [one_mul, one_mul] }
                                                            -- 🎉 no goals
#align localization.monoid_of Localization.monoidOf
#align add_localization.add_monoid_of AddLocalization.addMonoidOf

variable {S}

@[to_additive]
theorem mk_one_eq_monoidOf_mk (x) : mk x 1 = (monoidOf S).toMap x := rfl
#align localization.mk_one_eq_monoid_of_mk Localization.mk_one_eq_monoidOf_mk
#align add_localization.mk_zero_eq_add_monoid_of_mk AddLocalization.mk_zero_eq_addMonoidOf_mk

@[to_additive]
theorem mk_eq_monoidOf_mk'_apply (x y) : mk x y = (monoidOf S).mk' x y :=
  show _ = _ * _ from
    (Submonoid.LocalizationMap.mul_inv_right (monoidOf S).map_units _ _ _).2 <| by
      rw [← mk_one_eq_monoidOf_mk, ← mk_one_eq_monoidOf_mk, mk_mul x y y 1, mul_comm y 1]
      -- ⊢ mk (x * ↑y) (1 * y) = mk x 1
      conv => rhs; rw [← mul_one 1]; rw [← mul_one x]
      -- ⊢ mk (x * ↑y) (1 * y) = mk (x * 1) (1 * 1)
      exact mk_eq_mk_iff.2 (Con.symm _ <| (Localization.r S).mul (Con.refl _ (x, 1)) <| one_rel _)
      -- 🎉 no goals
#align localization.mk_eq_monoid_of_mk'_apply Localization.mk_eq_monoidOf_mk'_apply
#align add_localization.mk_eq_add_monoid_of_mk'_apply AddLocalization.mk_eq_addMonoidOf_mk'_apply

@[to_additive (attr := simp)]
theorem mk_eq_monoidOf_mk' : mk = (monoidOf S).mk' :=
  funext fun _ ↦ funext fun _ ↦ mk_eq_monoidOf_mk'_apply _ _
#align localization.mk_eq_monoid_of_mk' Localization.mk_eq_monoidOf_mk'
#align add_localization.mk_eq_add_monoid_of_mk' AddLocalization.mk_eq_addMonoidOf_mk'

universe u

@[to_additive (attr := simp)]
theorem liftOn_mk' {p : Sort u} (f : ∀ (_ : M) (_ : S), p) (H) (a : M) (b : S) :
    liftOn ((monoidOf S).mk' a b) f H = f a b := by rw [← mk_eq_monoidOf_mk', liftOn_mk]
                                                    -- 🎉 no goals
#align localization.lift_on_mk' Localization.liftOn_mk'
#align add_localization.lift_on_mk' AddLocalization.liftOn_mk'

@[to_additive (attr := simp)]
theorem liftOn₂_mk' {p : Sort*} (f : M → S → M → S → p) (H) (a c : M) (b d : S) :
    liftOn₂ ((monoidOf S).mk' a b) ((monoidOf S).mk' c d) f H = f a b c d := by
  rw [← mk_eq_monoidOf_mk', liftOn₂_mk]
  -- 🎉 no goals
#align localization.lift_on₂_mk' Localization.liftOn₂_mk'
#align add_localization.lift_on₂_mk' AddLocalization.liftOn₂_mk'

variable (f : Submonoid.LocalizationMap S N)

/-- Given a Localization map `f : M →* N` for a Submonoid `S`, we get an isomorphism between
the Localization of `M` at `S` as a quotient type and `N`. -/
@[to_additive
    "Given a Localization map `f : M →+ N` for a Submonoid `S`, we get an isomorphism between
the Localization of `M` at `S` as a quotient type and `N`."]
noncomputable def mulEquivOfQuotient (f : Submonoid.LocalizationMap S N) : Localization S ≃* N :=
  (monoidOf S).mulEquivOfLocalizations f
#align localization.mul_equiv_of_quotient Localization.mulEquivOfQuotient
#align add_localization.add_equiv_of_quotient AddLocalization.addEquivOfQuotient

variable {f}

-- Porting note: dsimp can not prove this
@[to_additive (attr := simp, nolint simpNF)]
theorem mulEquivOfQuotient_apply (x) : mulEquivOfQuotient f x = (monoidOf S).lift f.map_units x :=
  rfl
#align localization.mul_equiv_of_quotient_apply Localization.mulEquivOfQuotient_apply
#align add_localization.add_equiv_of_quotient_apply AddLocalization.addEquivOfQuotient_apply

@[to_additive (attr := simp, nolint simpNF)]
theorem mulEquivOfQuotient_mk' (x y) : mulEquivOfQuotient f ((monoidOf S).mk' x y) = f.mk' x y :=
  (monoidOf S).lift_mk' _ _ _
#align localization.mul_equiv_of_quotient_mk' Localization.mulEquivOfQuotient_mk'
#align add_localization.add_equiv_of_quotient_mk' AddLocalization.addEquivOfQuotient_mk'

@[to_additive]
theorem mulEquivOfQuotient_mk (x y) : mulEquivOfQuotient f (mk x y) = f.mk' x y := by
  rw [mk_eq_monoidOf_mk'_apply]; exact mulEquivOfQuotient_mk' _ _
  -- ⊢ ↑(mulEquivOfQuotient f) (Submonoid.LocalizationMap.mk' (monoidOf S) x y) = S …
                                 -- 🎉 no goals
#align localization.mul_equiv_of_quotient_mk Localization.mulEquivOfQuotient_mk
#align add_localization.add_equiv_of_quotient_mk AddLocalization.addEquivOfQuotient_mk

-- @[simp] -- Porting note: simp can prove this
@[to_additive]
theorem mulEquivOfQuotient_monoidOf (x) : mulEquivOfQuotient f ((monoidOf S).toMap x) = f.toMap x :=
  by simp
     -- 🎉 no goals
#align localization.mul_equiv_of_quotient_monoid_of Localization.mulEquivOfQuotient_monoidOf
#align add_localization.add_equiv_of_quotient_add_monoid_of AddLocalization.addEquivOfQuotient_addMonoidOf

@[to_additive (attr := simp)]
theorem mulEquivOfQuotient_symm_mk' (x y) :
    (mulEquivOfQuotient f).symm (f.mk' x y) = (monoidOf S).mk' x y :=
  f.lift_mk' (monoidOf S).map_units _ _
#align localization.mul_equiv_of_quotient_symm_mk' Localization.mulEquivOfQuotient_symm_mk'
#align add_localization.add_equiv_of_quotient_symm_mk' AddLocalization.addEquivOfQuotient_symm_mk'

@[to_additive]
theorem mulEquivOfQuotient_symm_mk (x y) : (mulEquivOfQuotient f).symm (f.mk' x y) = mk x y := by
  rw [mk_eq_monoidOf_mk'_apply]; exact mulEquivOfQuotient_symm_mk' _ _
  -- ⊢ ↑(MulEquiv.symm (mulEquivOfQuotient f)) (Submonoid.LocalizationMap.mk' f x y …
                                 -- 🎉 no goals
#align localization.mul_equiv_of_quotient_symm_mk Localization.mulEquivOfQuotient_symm_mk
#align add_localization.add_equiv_of_quotient_symm_mk AddLocalization.addEquivOfQuotient_symm_mk

@[to_additive (attr := simp)]
theorem mulEquivOfQuotient_symm_monoidOf (x) :
    (mulEquivOfQuotient f).symm (f.toMap x) = (monoidOf S).toMap x :=
  f.lift_eq (monoidOf S).map_units _
#align localization.mul_equiv_of_quotient_symm_monoid_of Localization.mulEquivOfQuotient_symm_monoidOf
#align add_localization.add_equiv_of_quotient_symm_add_monoid_of AddLocalization.addEquivOfQuotient_symm_addMonoidOf

section Away

variable (x : M)

/-- Given `x : M`, the Localization of `M` at the Submonoid generated by `x`, as a quotient. -/
@[to_additive (attr := reducible)
    "Given `x : M`, the Localization of `M` at the Submonoid generated by `x`, as a quotient."]
def Away :=
  Localization (Submonoid.powers x)
#align localization.away Localization.Away
#align add_localization.away AddLocalization.Away

/-- Given `x : M`, `invSelf` is `x⁻¹` in the Localization (as a quotient type) of `M` at the
Submonoid generated by `x`. -/
@[to_additive
    "Given `x : M`, `negSelf` is `-x` in the Localization (as a quotient type) of `M` at the
Submonoid generated by `x`."]
def Away.invSelf : Away x :=
  mk 1 ⟨x, Submonoid.mem_powers _⟩
#align localization.away.inv_self Localization.Away.invSelf
#align add_localization.away.neg_self AddLocalization.Away.negSelf

/-- Given `x : M`, the natural hom sending `y : M`, `M` a `CommMonoid`, to the equivalence class
of `(y, 1)` in the Localization of `M` at the Submonoid generated by `x`. -/
@[to_additive (attr := reducible)
    "Given `x : M`, the natural hom sending `y : M`, `M` an `AddCommMonoid`, to the equivalence
class of `(y, 0)` in the Localization of `M` at the Submonoid generated by `x`."]
def Away.monoidOf : Submonoid.LocalizationMap.AwayMap x (Away x) :=
  Localization.monoidOf (Submonoid.powers x)
#align localization.away.monoid_of Localization.Away.monoidOf
#align add_localization.away.add_monoid_of AddLocalization.Away.addMonoidOf

-- @[simp] -- Porting note: simp can prove this
@[to_additive]
theorem Away.mk_eq_monoidOf_mk' : mk = (Away.monoidOf x).mk' := by simp
                                                                   -- 🎉 no goals
#align localization.away.mk_eq_monoid_of_mk' Localization.Away.mk_eq_monoidOf_mk'
#align add_localization.away.mk_eq_add_monoid_of_mk' AddLocalization.Away.mk_eq_addMonoidOf_mk'

/-- Given `x : M` and a Localization map `f : M →* N` away from `x`, we get an isomorphism between
the Localization of `M` at the Submonoid generated by `x` as a quotient type and `N`. -/
@[to_additive
    "Given `x : M` and a Localization map `f : M →+ N` away from `x`, we get an isomorphism between
the Localization of `M` at the Submonoid generated by `x` as a quotient type and `N`."]
noncomputable def Away.mulEquivOfQuotient (f : Submonoid.LocalizationMap.AwayMap x N) :
    Away x ≃* N :=
  Localization.mulEquivOfQuotient f
#align localization.away.mul_equiv_of_quotient Localization.Away.mulEquivOfQuotient
#align add_localization.away.add_equiv_of_quotient AddLocalization.Away.addEquivOfQuotient

end Away

end Localization

end CommMonoid

section CommMonoidWithZero

variable {M : Type*} [CommMonoidWithZero M] (S : Submonoid M) (N : Type*) [CommMonoidWithZero N]
  {P : Type*} [CommMonoidWithZero P]

namespace Submonoid

/-- The type of homomorphisms between monoids with zero satisfying the characteristic predicate:
if `f : M →*₀ N` satisfies this predicate, then `N` is isomorphic to the localization of `M` at
`S`. -/
-- Porting note: This linter does not exist yet
-- @[nolint has_nonempty_instance]
structure LocalizationWithZeroMap extends LocalizationMap S N where
  map_zero' : toFun 0 = 0
#align submonoid.localization_with_zero_map Submonoid.LocalizationWithZeroMap

-- Porting note: no docstrings for LocalizationWithZeroMap.map_zero'
attribute [nolint docBlame] LocalizationWithZeroMap.toLocalizationMap
  LocalizationWithZeroMap.map_zero'

variable {S N}

/-- The monoid with zero hom underlying a `LocalizationMap`. -/
def LocalizationWithZeroMap.toMonoidWithZeroHom (f : LocalizationWithZeroMap S N) : M →*₀ N :=
  { f with }
#align submonoid.localization_with_zero_map.to_monoid_with_zero_hom Submonoid.LocalizationWithZeroMap.toMonoidWithZeroHom

end Submonoid

namespace Localization

/-- The zero element in a Localization is defined as `(0, 1)`.

Should not be confused with `AddLocalization.zero` which is `(0, 0)`. -/
protected irreducible_def zero : Localization S :=
  mk 0 1
#align localization.zero Localization.zero

instance : Zero (Localization S) := ⟨Localization.zero S⟩

variable {S}

theorem mk_zero (x : S) : mk 0 (x : S) = 0 :=
  calc
    mk 0 x = mk 0 1 := mk_eq_mk_iff.mpr (r_of_eq (by simp))
                                                     -- 🎉 no goals
    _ = Localization.zero S := (Localization.zero_def S).symm

instance : CommMonoidWithZero (Localization S) where
  zero_mul := fun x ↦ Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, zero_mul, r_of_eq]
    -- 🎉 no goals
  mul_zero := fun x ↦ Localization.induction_on x fun y => by
    simp only [← Localization.mk_zero y.2, mk_mul, mk_eq_mk_iff, mul_zero, zero_mul, r_of_eq]
    -- 🎉 no goals
#align localization.mk_zero Localization.mk_zero

theorem liftOn_zero {p : Type*} (f : ∀ (_ : M) (_ : S), p) (H) : liftOn 0 f H = f 0 1 := by
  rw [← mk_zero 1, liftOn_mk]
  -- 🎉 no goals
#align localization.lift_on_zero Localization.liftOn_zero

end Localization

variable {S N}

namespace Submonoid

@[simp]
theorem LocalizationMap.sec_zero_fst {f : LocalizationMap S N} : f.toMap (f.sec 0).fst = 0 := by
  rw [LocalizationMap.sec_spec', mul_zero]
  -- 🎉 no goals
#align submonoid.localization_map.sec_zero_fst Submonoid.LocalizationMap.sec_zero_fst

namespace LocalizationWithZeroMap

/-- Given a Localization map `f : M →*₀ N` for a Submonoid `S ⊆ M` and a map of
`CommMonoidWithZero`s `g : M →*₀ P` such that `g y` is invertible for all `y : S`, the
homomorphism induced from `N` to `P` sending `z : N` to `g x * (g y)⁻¹`, where `(x, y) : M × S`
are such that `z = f x * (f y)⁻¹`. -/
noncomputable def lift (f : LocalizationWithZeroMap S N) (g : M →*₀ P)
    (hg : ∀ y : S, IsUnit (g y)) : N →*₀ P :=
  { @LocalizationMap.lift _ _ _ _ _ _ _ f.toLocalizationMap g.toMonoidHom hg with
    map_zero' := by
      erw [LocalizationMap.lift_spec f.toLocalizationMap hg 0 0]
      -- ⊢ ↑↑g (LocalizationMap.sec f.toLocalizationMap 0).fst = ↑↑g ↑(LocalizationMap. …
      rw [mul_zero, ← map_zero g, ← g.toMonoidHom_coe]
      -- ⊢ ↑↑g (LocalizationMap.sec f.toLocalizationMap 0).fst = OneHom.toFun (↑↑g) 0
      refine f.toLocalizationMap.eq_of_eq hg ?_
      -- ⊢ ↑(LocalizationMap.toMap f.toLocalizationMap) (LocalizationMap.sec f.toLocali …
      rw [LocalizationMap.sec_zero_fst]
      -- ⊢ 0 = ↑(LocalizationMap.toMap f.toLocalizationMap) 0
      exact f.toMonoidWithZeroHom.map_zero.symm }
      -- 🎉 no goals
#align submonoid.localization_with_zero_map.lift Submonoid.LocalizationWithZeroMap.lift

end LocalizationWithZeroMap

end Submonoid

end CommMonoidWithZero

namespace Localization

variable {α : Type*} [CancelCommMonoid α] {s : Submonoid α} {a₁ b₁ : α} {a₂ b₂ : s}

@[to_additive]
theorem mk_left_injective (b : s) : Injective fun a => mk a b := fun c d h => by
  -- porting note: times out unless we add this `have`. Even `infer_instance` times out here.
  have : Nonempty s := One.nonempty
  -- ⊢ c = d
  simpa [-mk_eq_monoidOf_mk', mk_eq_mk_iff, r_iff_exists] using h
  -- 🎉 no goals
#align localization.mk_left_injective Localization.mk_left_injective
#align add_localization.mk_left_injective AddLocalization.mk_left_injective

@[to_additive]
theorem mk_eq_mk_iff' : mk a₁ a₂ = mk b₁ b₂ ↔ ↑b₂ * a₁ = a₂ * b₁ := by
  -- porting note: times out unless we add this `have`. Even `inferInstance` times out here.
  have : Nonempty s := One.nonempty
  -- ⊢ mk a₁ a₂ = mk b₁ b₂ ↔ ↑b₂ * a₁ = ↑a₂ * b₁
  simp_rw [mk_eq_mk_iff, r_iff_exists, mul_left_cancel_iff, exists_const]
  -- 🎉 no goals
#align localization.mk_eq_mk_iff' Localization.mk_eq_mk_iff'
#align add_localization.mk_eq_mk_iff' AddLocalization.mk_eq_mk_iff'

@[to_additive]
instance decidableEq [DecidableEq α] : DecidableEq (Localization s) := fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_eq_mk_iff'
#align localization.decidable_eq Localization.decidableEq
#align add_localization.decidable_eq AddLocalization.decidableEq

end Localization

/-! ### Order -/

namespace Localization

variable {α : Type*}

section OrderedCancelCommMonoid

variable [OrderedCancelCommMonoid α] {s : Submonoid α} {a₁ b₁ : α} {a₂ b₂ : s}

@[to_additive]
instance le : LE (Localization s) :=
  ⟨fun a b =>
    Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ ≤ a₂ * b₁)
      @fun a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ hab hcd => propext $ by
        obtain ⟨e, he⟩ := r_iff_exists.1 hab
        -- ⊢ (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ ≤ ↑a₂ * b₁) a₁ a₂ c₁ c₂ ↔ (fun a₁ a₂ b₁ b₂ => ↑ …
        obtain ⟨f, hf⟩ := r_iff_exists.1 hcd
        -- ⊢ (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ ≤ ↑a₂ * b₁) a₁ a₂ c₁ c₂ ↔ (fun a₁ a₂ b₁ b₂ => ↑ …
        simp only [mul_right_inj] at he hf
        -- ⊢ (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ ≤ ↑a₂ * b₁) a₁ a₂ c₁ c₂ ↔ (fun a₁ a₂ b₁ b₂ => ↑ …
        dsimp
        -- ⊢ ↑c₂ * a₁ ≤ ↑a₂ * c₁ ↔ ↑d₂ * b₁ ≤ ↑b₂ * d₁
        rw [← mul_le_mul_iff_right, mul_right_comm, ← hf, mul_right_comm, mul_right_comm (a₂ : α),
          mul_le_mul_iff_right, ← mul_le_mul_iff_left, mul_left_comm, he, mul_left_comm,
          mul_left_comm (b₂ : α), mul_le_mul_iff_left]⟩

@[to_additive]
instance lt : LT (Localization s) :=
  ⟨fun a b =>
    Localization.liftOn₂ a b (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ < a₂ * b₁)
      @fun a₁ b₁ a₂ b₂ c₁ d₁ c₂ d₂ hab hcd => propext $ by
        obtain ⟨e, he⟩ := r_iff_exists.1 hab
        -- ⊢ (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ < ↑a₂ * b₁) a₁ a₂ c₁ c₂ ↔ (fun a₁ a₂ b₁ b₂ => ↑ …
        obtain ⟨f, hf⟩ := r_iff_exists.1 hcd
        -- ⊢ (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ < ↑a₂ * b₁) a₁ a₂ c₁ c₂ ↔ (fun a₁ a₂ b₁ b₂ => ↑ …
        simp only [mul_right_inj] at he hf
        -- ⊢ (fun a₁ a₂ b₁ b₂ => ↑b₂ * a₁ < ↑a₂ * b₁) a₁ a₂ c₁ c₂ ↔ (fun a₁ a₂ b₁ b₂ => ↑ …
        dsimp
        -- ⊢ ↑c₂ * a₁ < ↑a₂ * c₁ ↔ ↑d₂ * b₁ < ↑b₂ * d₁
        rw [← mul_lt_mul_iff_right, mul_right_comm, ← hf, mul_right_comm, mul_right_comm (a₂ : α),
          mul_lt_mul_iff_right, ← mul_lt_mul_iff_left, mul_left_comm, he, mul_left_comm,
          mul_left_comm (b₂ : α), mul_lt_mul_iff_left]⟩

@[to_additive]
theorem mk_le_mk : mk a₁ a₂ ≤ mk b₁ b₂ ↔ ↑b₂ * a₁ ≤ a₂ * b₁ :=
  Iff.rfl
#align localization.mk_le_mk Localization.mk_le_mk
#align add_localization.mk_le_mk AddLocalization.mk_le_mk

@[to_additive]
theorem mk_lt_mk : mk a₁ a₂ < mk b₁ b₂ ↔ ↑b₂ * a₁ < a₂ * b₁ :=
  Iff.rfl
#align localization.mk_lt_mk Localization.mk_lt_mk
#align add_localization.mk_lt_mk AddLocalization.mk_lt_mk

-- declaring this separately to the instance below makes things faster
@[to_additive]
instance partialOrder : PartialOrder (Localization s) where
  le := (· ≤ ·)
  lt := (· < ·)
  le_refl a := Localization.induction_on a fun a => le_rfl
  le_trans a b c :=
    Localization.induction_on₃ a b c fun a b c hab hbc => by
      simp only [mk_le_mk] at hab hbc ⊢
      -- ⊢ ↑c.snd * a.fst ≤ ↑a.snd * c.fst
      refine' le_of_mul_le_mul_left' _
      -- ⊢ α
      · exact ↑b.2
        -- 🎉 no goals
      rw [mul_left_comm]
      -- ⊢ ↑c.snd * (↑b.snd * a.fst) ≤ ↑b.snd * (↑a.snd * c.fst)
      refine' (mul_le_mul_left' hab _).trans _
      -- ⊢ ↑c.snd * (↑a.snd * b.fst) ≤ ↑b.snd * (↑a.snd * c.fst)
      rwa [mul_left_comm, mul_left_comm (b.2 : α), mul_le_mul_iff_left]
      -- 🎉 no goals
  le_antisymm a b := by
    induction' a using Localization.rec with a₁ a₂
    -- ⊢ mk a₁ a₂ ≤ b → b ≤ mk a₁ a₂ → mk a₁ a₂ = b
    induction' b using Localization.rec with b₁ b₂
    simp_rw [mk_le_mk, mk_eq_mk_iff, r_iff_exists]
    exact fun hab hba => ⟨1, by rw [hab.antisymm hba]⟩
    -- ⊢ (_ : mk a₁ a₂ ≤ mk c✝ d✝ → mk c✝ d✝ ≤ mk a₁ a₂ → mk a₁ a₂ = mk c✝ d✝) = (_ : …
    all_goals intros; rfl
    -- 🎉 no goals
  lt_iff_le_not_le a b := Localization.induction_on₂ a b fun a b => lt_iff_le_not_le

@[to_additive]
instance orderedCancelCommMonoid : OrderedCancelCommMonoid (Localization s) :=
  { Localization.commMonoid s,
    Localization.partialOrder with
    mul_le_mul_left := fun a b =>
      Localization.induction_on₂ a b fun a b hab c =>
        Localization.induction_on c fun c => by
          simp only [mk_mul, mk_le_mk, Submonoid.coe_mul, mul_mul_mul_comm _ _ c.1] at hab ⊢
          -- ⊢ ↑c.snd * c.fst * (↑b.snd * a.fst) ≤ ↑c.snd * c.fst * (↑a.snd * b.fst)
          exact mul_le_mul_left' hab _
          -- 🎉 no goals
    le_of_mul_le_mul_left := fun a b c =>
      Localization.induction_on₃ a b c fun a b c hab => by
        simp only [mk_mul, mk_le_mk, Submonoid.coe_mul, mul_mul_mul_comm _ _ a.1] at hab ⊢
        -- ⊢ ↑c.snd * b.fst ≤ ↑b.snd * c.fst
        exact le_of_mul_le_mul_left' hab }
        -- 🎉 no goals

@[to_additive]
instance decidableLE [DecidableRel ((· ≤ ·) : α → α → Prop)] :
    DecidableRel ((· ≤ ·) : Localization s → Localization s → Prop) := fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_le_mk
#align localization.decidable_le Localization.decidableLE
#align add_localization.decidable_le AddLocalization.decidableLE

@[to_additive]
instance decidableLT [DecidableRel ((· < ·) : α → α → Prop)] :
    DecidableRel ((· < ·) : Localization s → Localization s → Prop) := fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_lt_mk
#align localization.decidable_lt Localization.decidableLT
#align add_localization.decidable_lt AddLocalization.decidableLT

/-- An ordered cancellative monoid injects into its localization by sending `a` to `a / b`. -/
@[to_additive (attr := simps!) "An ordered cancellative monoid injects into its localization by
sending `a` to `a - b`."]
def mkOrderEmbedding (b : s) : α ↪o Localization s where
  toFun a := mk a b
  inj' := mk_left_injective _
  map_rel_iff' {a b} := by simp [-mk_eq_monoidOf_mk', mk_le_mk]
                           -- 🎉 no goals
#align localization.mk_order_embedding Localization.mkOrderEmbedding
#align add_localization.mk_order_embedding AddLocalization.mkOrderEmbedding

end OrderedCancelCommMonoid

@[to_additive]
instance [LinearOrderedCancelCommMonoid α] {s : Submonoid α} :
    LinearOrderedCancelCommMonoid (Localization s) :=
  { Localization.orderedCancelCommMonoid with
    le_total := fun a b =>
      Localization.induction_on₂ a b fun _ _ => by
        simp_rw [mk_le_mk]
        -- ⊢ ↑x✝.snd * x✝¹.fst ≤ ↑x✝¹.snd * x✝.fst ∨ ↑x✝¹.snd * x✝.fst ≤ ↑x✝.snd * x✝¹.fst
        exact le_total _ _
        -- 🎉 no goals
    decidableLE := Localization.decidableLE
    decidableLT := Localization.decidableLT  -- porting note: was wrong in mathlib3
    decidableEq := Localization.decidableEq }

end Localization
