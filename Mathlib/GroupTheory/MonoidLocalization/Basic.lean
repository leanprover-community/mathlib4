/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Submonoid.Operations
public import Mathlib.Algebra.Regular.Basic
public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.GroupTheory.OreLocalization.Basic

/-!
# Localizations of commutative monoids

Localizing a commutative ring at one of its submonoids does not rely on the ring's addition, so
we can generalize localizations to commutative monoids.

We characterize the localization of a commutative monoid `M` at a submonoid `S` up to
isomorphism; that is, a commutative monoid `N` is the localization of `M` at `S` iff we can find a
monoid homomorphism `f : M →* N` satisfying 3 properties:
1. For all `y ∈ S`, `f y` is a unit;
2. For all `z : N`, there exists `(x, y) : M × S` such that `z * f y = f x`;
3. For all `x, y : M` such that `f x = f y`, there exists `c ∈ S` such that `x * c = y * c`.
   (The converse is a consequence of 1.)

Given such a localization map `f : M →* N`, we can define the surjection
`Submonoid.LocalizationMap.mk'` sending `(x, y) : M × S` to `f x * (f y)⁻¹`, and
`Submonoid.LocalizationMap.lift`, the homomorphism from `N` induced by a homomorphism from `M` which
maps elements of `S` to invertible elements of the codomain. Similarly, given commutative monoids
`P, Q`, a submonoid `T` of `P` and a localization map for `T` from `P` to `Q`, then a homomorphism
`g : M →* P` such that `g(S) ⊆ T` induces a homomorphism of localizations, `LocalizationMap.map`,
from `N` to `Q`.

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

@[expose] public section

assert_not_exists MonoidWithZero Ring

open Function
namespace AddSubmonoid

variable {M : Type*} [AddCommMonoid M] (S : AddSubmonoid M) (N : Type*) [AddCommMonoid N]

/-- The type of AddMonoid homomorphisms satisfying the characteristic predicate: if `f : M →+ N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
structure LocalizationMap extends AddMonoidHom M N where
  map_add_units' : ∀ y : S, IsAddUnit (toFun y)
  surj' : ∀ z : N, ∃ x : M × S, z + toFun x.2 = toFun x.1
  exists_of_eq : ∀ x y, toFun x = toFun y → ∃ c : S, ↑c + x = ↑c + y

/-- The AddMonoidHom underlying a `LocalizationMap` of `AddCommMonoid`s. -/
add_decl_doc LocalizationMap.toAddMonoidHom

end AddSubmonoid

section CommMonoid

variable {M : Type*} [CommMonoid M] (S : Submonoid M) (N : Type*) [CommMonoid N] {P : Type*}
  [CommMonoid P]

namespace Submonoid

/-- The type of monoid homomorphisms satisfying the characteristic predicate: if `f : M →* N`
satisfies this predicate, then `N` is isomorphic to the localization of `M` at `S`. -/
structure LocalizationMap extends MonoidHom M N where
  map_units' : ∀ y : S, IsUnit (toFun y)
  surj' : ∀ z : N, ∃ x : M × S, z * toFun x.2 = toFun x.1
  exists_of_eq : ∀ x y, toFun x = toFun y → ∃ c : S, ↑c * x = c * y

attribute [to_additive] Submonoid.LocalizationMap

/-- The monoid hom underlying a `LocalizationMap`. -/
add_decl_doc LocalizationMap.toMonoidHom

end Submonoid

namespace Localization

/- Ensure that `@[to_additive]` uses the right namespace before the definition of `Localization`. -/
insert_to_additive_translation Localization AddLocalization

/-- The congruence relation on `M × S`, `M` a `CommMonoid` and `S` a submonoid of `M`, whose
quotient is the localization of `M` at `S`, defined as the unique congruence relation on
`M × S` such that for any other congruence relation `s` on `M × S` where for all `y ∈ S`,
`(1, 1) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
`(x₁, y₁) ∼ (x₂, y₂)` by `s`. -/
@[to_additive
/-- The congruence relation on `M × S`, `M` an `AddCommMonoid` and `S` an `AddSubmonoid` of `M`,
whose quotient is the localization of `M` at `S`, defined as the unique congruence relation on
`M × S` such that for any other congruence relation `s` on `M × S` where for all `y ∈ S`,
`(0, 0) ∼ (y, y)` under `s`, we have that `(x₁, y₁) ∼ (x₂, y₂)` by `r` implies
`(x₁, y₁) ∼ (x₂, y₂)` by `s`. -/]
def r (S : Submonoid M) : Con (M × S) :=
  sInf { c | ∀ y : S, c 1 (y, y) }

/-- An alternate form of the congruence relation on `M × S`, `M` a `CommMonoid` and `S` a
submonoid of `M`, whose quotient is the localization of `M` at `S`. -/
@[to_additive
/-- An alternate form of the congruence relation on `M × S`, `M` a `CommMonoid` and `S` a
submonoid of `M`, whose quotient is the localization of `M` at `S`. -/]
def r' : Con (M × S) := by
  -- note we multiply by `c` on the left so that we can later generalize to `•`
  refine
    { r := fun a b : M × S ↦ ∃ c : S, ↑c * (↑b.2 * a.1) = c * (a.2 * b.1)
      iseqv := ⟨fun a ↦ ⟨1, rfl⟩, fun ⟨c, hc⟩ ↦ ⟨c, hc.symm⟩, ?_⟩
      mul' := ?_ }
  · rintro a b c ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    use t₂ * t₁ * b.2
    simp only [Submonoid.coe_mul]
    calc
      (t₂ * t₁ * b.2 : M) * (c.2 * a.1) = t₂ * c.2 * (t₁ * (b.2 * a.1)) := by ac_rfl
      _ = t₁ * a.2 * (t₂ * (c.2 * b.1)) := by rw [ht₁]; ac_rfl
      _ = t₂ * t₁ * b.2 * (a.2 * c.1) := by rw [ht₂]; ac_rfl
  · rintro a b c d ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
    use t₂ * t₁
    calc
      (t₂ * t₁ : M) * (b.2 * d.2 * (a.1 * c.1)) = t₂ * (d.2 * c.1) * (t₁ * (b.2 * a.1)) := by ac_rfl
      _ = (t₂ * t₁ : M) * (a.2 * c.2 * (b.1 * d.1)) := by rw [ht₁, ht₂]; ac_rfl

/-- The congruence relation used to localize a `CommMonoid` at a submonoid can be expressed
equivalently as an infimum (see `Localization.r`) or explicitly
(see `Localization.r'`). -/
@[to_additive
/-- The additive congruence relation used to localize an `AddCommMonoid` at a submonoid can be
expressed equivalently as an infimum (see `AddLocalization.r`) or explicitly
(see `AddLocalization.r'`). -/]
theorem r_eq_r' : r S = r' S :=
  le_antisymm (sInf_le fun _ ↦ ⟨1, by simp⟩) <|
    le_sInf fun b H ⟨p, q⟩ ⟨x, y⟩ ⟨t, ht⟩ ↦ by
      rw [← one_mul (p, q), ← one_mul (x, y)]
      refine b.trans (b.mul (H (t * y)) (b.refl _)) ?_
      convert b.symm (b.mul (H (t * q)) (b.refl (x, y))) using 1
      dsimp only [Prod.mk_mul_mk, Submonoid.coe_mul] at ht ⊢
      simp_rw [mul_assoc, ht, mul_comm y q]

variable {S}

@[to_additive]
theorem r_iff_exists {x y : M × S} : r S x y ↔ ∃ c : S, ↑c * (↑y.2 * x.1) = c * (x.2 * y.1) := by
  simp only [r_eq_r' S, r', Con.rel_mk]

@[to_additive]
theorem r_iff_oreEqv_r {x y : M × S} : r S x y ↔ (OreLocalization.oreEqv S M).r x y := by
  simp only [r_iff_exists, Subtype.exists, exists_prop, OreLocalization.oreEqv, smul_eq_mul,
    Submonoid.mk_smul]
  constructor
  · rintro ⟨u, hu, e⟩
    exact ⟨_, mul_mem hu x.2.2, u * y.2, by rw [mul_assoc, mul_assoc, ← e], mul_right_comm _ _ _⟩
  · rintro ⟨u, hu, v, e₁, e₂⟩
    exact ⟨u, hu, by rw [← mul_assoc, e₂, mul_right_comm, ← e₁, mul_assoc, mul_comm y.1]⟩

end Localization

/-- The localization of a `CommMonoid` at one of its submonoids (as a quotient type). -/
@[to_additive AddLocalization
/-- The localization of an `AddCommMonoid` at one of its submonoids (as a quotient type). -/]
abbrev Localization := OreLocalization S M

namespace Localization

variable {S}

/-- Given a `CommMonoid` `M` and submonoid `S`, `mk` sends `x : M`, `y ∈ S` to the equivalence
class of `(x, y)` in the localization of `M` at `S`. -/
@[to_additive
/-- Given an `AddCommMonoid` `M` and submonoid `S`, `mk` sends `x : M`, `y ∈ S` to
the equivalence class of `(x, y)` in the localization of `M` at `S`. -/]
def mk (x : M) (y : S) : Localization S := x /ₒ y

@[to_additive]
theorem mk_eq_mk_iff {a c : M} {b d : S} : mk a b = mk c d ↔ r S ⟨a, b⟩ ⟨c, d⟩ := by
  simp only [mk, OreLocalization.oreDiv_eq_iff, r_iff_oreEqv_r, OreLocalization.oreEqv]

universe u

/-- Dependent recursion principle for `Localizations`: given elements `f a b : p (mk a b)`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d` (with the correct coercions),
then `f` is defined on the whole `Localization S`. -/
@[to_additive (attr := elab_as_elim)
/-- Dependent recursion principle for `AddLocalizations`: given elements `f a b : p (mk a b)`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d` (with the correct coercions),
then `f` is defined on the whole `AddLocalization S`. -/]
def rec {p : Localization S → Sort u} (f : ∀ (a : M) (b : S), p (mk a b))
    (H : ∀ {a c : M} {b d : S} (h : r S (a, b) (c, d)),
      (Eq.ndrec (f a b) (mk_eq_mk_iff.mpr h) : p (mk c d)) = f c d) (x) : p x :=
  Quot.rec (fun y ↦ Eq.ndrec (f y.1 y.2) (by rfl))
    (fun y z h ↦ by cases y; cases z; exact H (r_iff_oreEqv_r.mpr h)) x

/-- Copy of `Quotient.recOnSubsingleton₂` for `Localization` -/
@[to_additive (attr := elab_as_elim)
/-- Copy of `Quotient.recOnSubsingleton₂` for `AddLocalization` -/]
def recOnSubsingleton₂ {r : Localization S → Localization S → Sort u}
    [h : ∀ (a c : M) (b d : S), Subsingleton (r (mk a b) (mk c d))] (x y : Localization S)
    (f : ∀ (a c : M) (b d : S), r (mk a b) (mk c d)) : r x y :=
  @Quotient.recOnSubsingleton₂' _ _ _ _ r (Prod.rec fun _ _ => Prod.rec fun _ _ => h _ _ _ _) x y
    (Prod.rec fun _ _ => Prod.rec fun _ _ => f _ _ _ _)

@[to_additive]
theorem mk_mul (a c : M) (b d : S) : mk a b * mk c d = mk (a * c) (b * d) :=
  mul_comm b d ▸ OreLocalization.oreDiv_mul_oreDiv

unseal OreLocalization.one in
@[to_additive]
theorem mk_one : mk 1 (1 : S) = 1 := OreLocalization.one_def

@[to_additive]
theorem mk_pow (n : ℕ) (a : M) (b : S) : mk a b ^ n = mk (a ^ n) (b ^ n) := by
  induction n <;> simp [pow_succ, *, ← mk_mul, ← mk_one]

@[to_additive]
theorem mk_prod {ι} (t : Finset ι) (f : ι → M) (s : ι → S) :
    ∏ i ∈ t, mk (f i) (s i) = mk (∏ i ∈ t, f i) (∏ i ∈ t, s i) := by
  classical
  induction t using Finset.induction_on <;> simp [mk_one, Finset.prod_insert, *, mk_mul]

@[to_additive (attr := simp)]
theorem ndrec_mk {p : Localization S → Sort u} (f : ∀ (a : M) (b : S), p (mk a b)) (H) (a : M)
    (b : S) : (rec f H (mk a b) : p (mk a b)) = f a b := rfl

/-- Non-dependent recursion principle for localizations: given elements `f a b : p`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d`,
then `f` is defined on the whole `Localization S`. -/
@[to_additive
/-- Non-dependent recursion principle for `AddLocalization`s: given elements `f a b : p`
for all `a b`, such that `r S (a, b) (c, d)` implies `f a b = f c d`,
then `f` is defined on the whole `Localization S`. -/]
def liftOn {p : Sort u} (x : Localization S) (f : M → S → p)
    (H : ∀ {a c : M} {b d : S}, r S (a, b) (c, d) → f a b = f c d) : p :=
  rec f (fun h ↦ (by simpa only [eq_rec_constant] using H h)) x

@[to_additive]
theorem liftOn_mk {p : Sort u} (f : M → S → p) (H) (a : M) (b : S) :
    liftOn (mk a b) f H = f a b := rfl

@[to_additive (attr := elab_as_elim, induction_eliminator, cases_eliminator)]
theorem ind {p : Localization S → Prop} (H : ∀ y : M × S, p (mk y.1 y.2)) (x) : p x :=
  rec (fun a b ↦ H (a, b)) (fun _ ↦ rfl) x

@[to_additive (attr := elab_as_elim)]
theorem induction_on {p : Localization S → Prop} (x) (H : ∀ y : M × S, p (mk y.1 y.2)) : p x :=
  ind H x

/-- Non-dependent recursion principle for localizations: given elements `f x y : p`
for all `x` and `y`, such that `r S x x'` and `r S y y'` implies `f x y = f x' y'`,
then `f` is defined on the whole `Localization S`. -/
@[to_additive
/-- Non-dependent recursion principle for localizations: given elements `f x y : p`
for all `x` and `y`, such that `r S x x'` and `r S y y'` implies `f x y = f x' y'`,
then `f` is defined on the whole `Localization S`. -/]
def liftOn₂ {p : Sort u} (x y : Localization S) (f : M → S → M → S → p)
    (H : ∀ {a a' b b' c c' d d'}, r S (a, b) (a', b') → r S (c, d) (c', d') →
      f a b c d = f a' b' c' d') : p :=
  liftOn x (fun a b ↦ liftOn y (f a b) fun hy ↦ H ((r S).refl _) hy) fun hx ↦
    induction_on y fun ⟨_, _⟩ ↦ H hx ((r S).refl _)

@[to_additive]
theorem liftOn₂_mk {p : Sort*} (f : M → S → M → S → p) (H) (a c : M) (b d : S) :
    liftOn₂ (mk a b) (mk c d) f H = f a b c d := rfl

@[to_additive (attr := elab_as_elim)]
theorem induction_on₂ {p : Localization S → Localization S → Prop} (x y)
    (H : ∀ x y : M × S, p (mk x.1 x.2) (mk y.1 y.2)) : p x y :=
  induction_on x fun x ↦ induction_on y <| H x

@[to_additive (attr := elab_as_elim)]
theorem induction_on₃ {p : Localization S → Localization S → Localization S → Prop} (x y z)
    (H : ∀ x y z : M × S, p (mk x.1 x.2) (mk y.1 y.2) (mk z.1 z.2)) : p x y z :=
  induction_on₂ x y fun x y ↦ induction_on z <| H x y

@[to_additive]
theorem one_rel (y : S) : r S 1 (y, y) := fun _ hb ↦ hb y

@[to_additive]
theorem r_of_eq {x y : M × S} (h : ↑y.2 * x.1 = ↑x.2 * y.1) : r S x y :=
  r_iff_exists.2 ⟨1, by rw [h]⟩

@[to_additive]
theorem mk_self (a : S) : mk (a : M) a = 1 := by
  symm
  rw [← mk_one, mk_eq_mk_iff]
  exact one_rel a

@[to_additive (attr := simp)]
lemma mk_self_mk (a : M) (haS : a ∈ S) : mk a ⟨a, haS⟩ = 1 :=
  mk_self ⟨a, haS⟩

/-- `Localization.mk` as a monoid hom. -/
@[to_additive (attr := simps) /-- `Localization.mk` as a monoid hom. -/]
def mkHom : M × S →* Localization S where
  toFun x := mk x.1 x.2
  map_one' := mk_one
  map_mul' _ _ := (mk_mul ..).symm

@[to_additive]
lemma mkHom_surjective : Surjective (mkHom (S := S)) := by rintro ⟨x, y⟩; exact ⟨⟨x, y⟩, rfl⟩

section Scalar

variable {R R₁ R₂ : Type*}

theorem smul_mk [SMul R M] [IsScalarTower R M M] (c : R) (a b) :
    c • (mk a b : Localization S) = mk (c • a) b := by
  rw [mk, mk, ← OreLocalization.smul_one_oreDiv_one_smul, OreLocalization.oreDiv_smul_oreDiv]
  change (c • 1) • a /ₒ (b * 1) = _
  rw [smul_assoc, one_smul, mul_one]

-- move me
instance {R M : Type*} [CommMonoid M] [SMul R M] [IsScalarTower R M M] : SMulCommClass R M M where
  smul_comm r s x := by
    rw [← one_smul M (s • x), ← smul_assoc, smul_comm, smul_assoc, one_smul]

-- Note: Previously there was a `MulDistribMulAction R (Localization S)`.
-- It was removed as it is not the correct action.

end Scalar

end Localization

variable {S N}

namespace MonoidHom

/-- Makes a localization map from a `CommMonoid` hom satisfying the characteristic predicate. -/
@[to_additive /-- Makes a localization map from an `AddCommMonoid` hom satisfying the
characteristic predicate. -/]
def toLocalizationMap (f : M →* N) (H1 : ∀ y : S, IsUnit (f y))
    (H2 : ∀ z, ∃ x : M × S, z * f x.2 = f x.1) (H3 : ∀ x y, f x = f y → ∃ c : S, ↑c * x = ↑c * y) :
    Submonoid.LocalizationMap S N :=
  { f with
    map_units' := H1
    surj' := H2
    exists_of_eq := H3 }

end MonoidHom

namespace Submonoid

namespace LocalizationMap

/-- Short for `toMonoidHom`; used to apply a localization map as a function. -/
@[to_additive /-- Short for `toAddMonoidHom`; used to apply a localization map as a function. -/]
abbrev toMap (f : LocalizationMap S N) := f.toMonoidHom

attribute [deprecated toMonoidHom (since := "2025-08-13")] toMap
attribute [deprecated AddSubmonoid.LocalizationMap.toAddMonoidHom (since := "2025-08-13")]
  AddSubmonoid.LocalizationMap.toMap

@[to_additive]
theorem toMonoidHom_injective : Injective (toMonoidHom : LocalizationMap S N → M →* N) :=
  fun f g ↦ by cases f; congr!

@[deprecated (since := "2025-08-13")] alias toMap_injective := toMonoidHom_injective

@[to_additive] instance : FunLike (LocalizationMap S N) M N where
  coe f := f.toMonoidHom
  coe_injective' := DFunLike.coe_injective.comp toMonoidHom_injective

@[to_additive] instance : MonoidHomClass (LocalizationMap S N) M N where
  map_one f := f.toMonoidHom.map_one
  map_mul f := f.toMonoidHom.map_mul

@[to_additive (attr := simp)] lemma toMonoidHom_apply (f : LocalizationMap S N) (x : M) :
    f.toMonoidHom x = f x := rfl

@[to_additive (attr := ext)]
theorem ext {f g : LocalizationMap S N} (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

@[to_additive]
theorem map_units (f : LocalizationMap S N) (y : S) : IsUnit (f y) :=
  f.2 y

@[to_additive]
theorem surj (f : LocalizationMap S N) (z : N) : ∃ x : M × S, z * f x.2 = f x.1 :=
  f.3 z

/-- Given a localization map `f : M →* N`, and `z w : N`, there exist `z' w' : M` and `d : S`
such that `f z' / f d = z` and `f w' / f d = w`. -/
@[to_additive
/-- Given a localization map `f : M →+ N`, and `z w : N`, there exist `z' w' : M` and `d : S`
such that `f z' - f d = z` and `f w' - f d = w`. -/]
theorem surj₂ (f : LocalizationMap S N) (z w : N) : ∃ z' w' : M, ∃ d : S,
    (z * f d = f z') ∧ (w * f d = f w') := by
  let ⟨a, ha⟩ := surj f z
  let ⟨b, hb⟩ := surj f w
  refine ⟨a.1 * b.2, a.2 * b.1, a.2 * b.2, ?_, ?_⟩
  · simp_rw [mul_def, map_mul, ← ha]
    exact (mul_assoc z _ _).symm
  · simp_rw [mul_def, map_mul, ← hb]
    exact mul_left_comm w _ _

@[to_additive]
theorem eq_iff_exists (f : LocalizationMap S N) {x y} :
    f x = f y ↔ ∃ c : S, ↑c * x = c * y := Iff.intro (f.4 x y)
  fun ⟨c, h⟩ ↦ by
    replace h := congr_arg f h
    rw [map_mul, map_mul] at h
    exact (f.map_units c).mul_right_inj.mp h

/-- Given a localization map `f : M →* N`, a section function sending `z : N` to some
`(x, y) : M × S` such that `f x * (f y)⁻¹ = z`. -/
@[to_additive
/-- Given a localization map `f : M →+ N`, a section function sending `z : N`
to some `(x, y) : M × S` such that `f x - f y = z`. -/]
noncomputable def sec (f : LocalizationMap S N) (z : N) : M × S := Classical.choose <| f.surj z

@[to_additive]
theorem sec_spec {f : LocalizationMap S N} (z : N) :
    z * f (f.sec z).2 = f (f.sec z).1 := Classical.choose_spec <| f.surj z

@[to_additive]
theorem sec_spec' {f : LocalizationMap S N} (z : N) :
    f (f.sec z).1 = f (f.sec z).2 * z := by rw [mul_comm, sec_spec]

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that `f(S) ⊆ Nˣ`, for all
`w, z : N` and `y ∈ S`, we have `w * (f y)⁻¹ = z ↔ w = f y * z`. -/
@[to_additive
/-- Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that `f(S) ⊆ AddUnits N`, for all
`w, z : N` and `y ∈ S`, we have `w - f y = z ↔ w = f y + z`. -/]
theorem mul_inv_left {f : M →* N} (h : ∀ y : S, IsUnit (f y)) (y : S) (w z : N) :
    w * (IsUnit.liftRight (f.restrict S) h y)⁻¹ = z ↔ w = f y * z := by
  rw [mul_comm]
  exact Units.inv_mul_eq_iff_eq_mul (IsUnit.liftRight (f.restrict S) h y)

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that `f(S) ⊆ Nˣ`, for all
`w, z : N` and `y ∈ S`, we have `z = w * (f y)⁻¹ ↔ z * f y = w`. -/
@[to_additive
/-- Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that `f(S) ⊆ AddUnits N`, for all
`w, z : N` and `y ∈ S`, we have `z = w - f y ↔ z + f y = w`. -/]
theorem mul_inv_right {f : M →* N} (h : ∀ y : S, IsUnit (f y)) (y : S) (w z : N) :
    z = w * (IsUnit.liftRight (f.restrict S) h y)⁻¹ ↔ z * f y = w := by
  rw [eq_comm, mul_inv_left h, mul_comm, eq_comm]

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ Nˣ`, for all `x₁ x₂ : M` and `y₁, y₂ ∈ S`, we have
`f x₁ * (f y₁)⁻¹ = f x₂ * (f y₂)⁻¹ ↔ f (x₁ * y₂) = f (x₂ * y₁)`. -/
@[to_additive (attr := simp)
/-- Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ AddUnits N`, for all `x₁ x₂ : M` and `y₁, y₂ ∈ S`, we have
`f x₁ - f y₁ = f x₂ - f y₂ ↔ f (x₁ + y₂) = f (x₂ + y₁)`. -/]
theorem mul_inv {f : M →* N} (h : ∀ y : S, IsUnit (f y)) {x₁ x₂} {y₁ y₂ : S} :
    f x₁ * (IsUnit.liftRight (f.restrict S) h y₁)⁻¹ =
        f x₂ * (IsUnit.liftRight (f.restrict S) h y₂)⁻¹ ↔
      f (x₁ * y₂) = f (x₂ * y₁) := by
  rw [mul_inv_right h, mul_assoc, mul_comm _ (f y₂), ← mul_assoc, mul_inv_left h, mul_comm x₂,
    f.map_mul, f.map_mul]

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that `f(S) ⊆ Nˣ`, for all
`y, z ∈ S`, we have `(f y)⁻¹ = (f z)⁻¹ → f y = f z`. -/
@[to_additive
/-- Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ AddUnits N`, for all `y, z ∈ S`, we have `- (f y) = - (f z) → f y = f z`. -/]
theorem inv_inj {f : M →* N} (hf : ∀ y : S, IsUnit (f y)) {y z : S}
    (h : (IsUnit.liftRight (f.restrict S) hf y)⁻¹ = (IsUnit.liftRight (f.restrict S) hf z)⁻¹) :
      f y = f z := by
  rw [← mul_one (f y), eq_comm, ← mul_inv_left hf y (f z) 1, h]
  exact Units.inv_mul (IsUnit.liftRight (f.restrict S) hf z)⁻¹

/-- Given a MonoidHom `f : M →* N` and Submonoid `S ⊆ M` such that `f(S) ⊆ Nˣ`, for all
`y ∈ S`, `(f y)⁻¹` is unique. -/
@[to_additive
/-- Given an AddMonoidHom `f : M →+ N` and Submonoid `S ⊆ M` such that
`f(S) ⊆ AddUnits N`, for all `y ∈ S`, `- (f y)` is unique. -/]
theorem inv_unique {f : M →* N} (h : ∀ y : S, IsUnit (f y)) {y : S} {z : N} (H : f y * z = 1) :
    (IsUnit.liftRight (f.restrict S) h y)⁻¹ = z := by
  rw [← one_mul _⁻¹, Units.val_mul, mul_inv_left]
  exact H.symm

variable (f : LocalizationMap S N)

@[to_additive]
theorem map_right_cancel {x y} {c : S} (h : f (c * x) = f (c * y)) :
    f x = f y := by
  rw [map_mul, map_mul] at h
  let ⟨u, hu⟩ := f.map_units c
  rw [← hu] at h
  exact (Units.mul_right_inj u).1 h

@[to_additive]
theorem map_left_cancel {x y} {c : S} (h : f (x * c) = f (y * c)) :
    f x = f y :=
  f.map_right_cancel (c := c) <| by rw [mul_comm _ x, mul_comm _ y, h]

/-- Given a localization map `f : M →* N`, the surjection sending `(x, y) : M × S` to
`f x * (f y)⁻¹`. -/
@[to_additive
/-- Given a localization map `f : M →+ N`, the surjection sending `(x, y) : M × S` to
`f x - f y`. -/]
noncomputable def mk' (f : LocalizationMap S N) (x : M) (y : S) : N :=
  f x * ↑(IsUnit.liftRight (f.restrict S) f.map_units y)⁻¹

@[to_additive]
lemma mk'_mul (x₁ x₂ : M) (y₁ y₂ : S) : f.mk' (x₁ * x₂) (y₁ * y₂) = f.mk' x₁ y₁ * f.mk' x₂ y₂ := by
  refine (mul_inv_left f.map_units _ _ _).2 ?_
  simp only [map_mul, coe_mul, toMonoidHom_apply, mk', IsUnit.liftRight, Units.liftRight,
    MonoidHom.restrict_apply, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [mul_mul_mul_comm (f x₁), mul_left_comm, mul_mul_mul_comm (f y₁)]
  simp

@[to_additive]
theorem mk'_one (x) : f.mk' x (1 : S) = f x := by
  rw [mk', map_one]
  exact mul_one _

/-- Given a localization map `f : M →* N` for a submonoid `S ⊆ M`, for all `z : N` we have that if
`x : M, y ∈ S` are such that `z * f y = f x`, then `f x * (f y)⁻¹ = z`. -/
@[to_additive (attr := simp)
/-- Given a localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, for all `z : N`
we have that if `x : M, y ∈ S` are such that `z + f y = f x`, then `f x - f y = z`. -/]
theorem mk'_sec (z : N) : f.mk' (f.sec z).1 (f.sec z).2 = z :=
  show _ * _ = _ by rw [← sec_spec, mul_inv_left, mul_comm]; dsimp

@[to_additive]
theorem mk'_surjective (z : N) : ∃ (x : _) (y : S), f.mk' x y = z :=
  ⟨(f.sec z).1, (f.sec z).2, f.mk'_sec z⟩

@[to_additive]
theorem mk'_spec (x) (y : S) : f.mk' x y * f y = f x :=
  show _ * _ * _ = _ by rw [mul_assoc, mul_comm _ (f y), ← mul_assoc, mul_inv_left, mul_comm]; dsimp

@[to_additive]
theorem mk'_spec' (x) (y : S) : f y * f.mk' x y = f x := by rw [mul_comm, mk'_spec]

@[to_additive]
theorem eq_mk'_iff_mul_eq {x} {y : S} {z} : z = f.mk' x y ↔ z * f y = f x :=
  ⟨fun H ↦ by rw [H, mk'_spec], fun H ↦ by rwa [mk', mul_inv_right]⟩

@[to_additive]
theorem mk'_eq_iff_eq_mul {x} {y : S} {z} : f.mk' x y = z ↔ f x = z * f y := by
  rw [eq_comm, eq_mk'_iff_mul_eq, eq_comm]

@[to_additive]
theorem mk'_eq_iff_eq {x₁ x₂} {y₁ y₂ : S} :
    f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ f (y₂ * x₁) = f (y₁ * x₂) where
  mp H := by
    rw [map_mul f, map_mul f, f.mk'_eq_iff_eq_mul.1 H,← mul_assoc, mk'_spec', mul_comm (f x₂)]
  mpr H := by
    rw [mk'_eq_iff_eq_mul, mk', mul_assoc, mul_comm _ (f y₁), ← mul_assoc, ← map_mul f, mul_comm x₂,
      ← H, ← mul_comm x₁, map_mul f, mul_inv_right f.map_units, toMonoidHom_apply]

@[to_additive]
theorem mk'_eq_iff_eq' {x₁ x₂} {y₁ y₂ : S} :
    f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ f (x₁ * y₂) = f (x₂ * y₁) := by
  simp only [f.mk'_eq_iff_eq, mul_comm]

@[to_additive]
protected theorem eq {a₁ b₁} {a₂ b₂ : S} :
    f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ ∃ c : S, ↑c * (↑b₂ * a₁) = c * (a₂ * b₁) :=
  f.mk'_eq_iff_eq.trans <| f.eq_iff_exists

@[to_additive]
protected theorem eq' {a₁ b₁} {a₂ b₂ : S} :
    f.mk' a₁ a₂ = f.mk' b₁ b₂ ↔ Localization.r S (a₁, a₂) (b₁, b₂) := by
  rw [f.eq, Localization.r_iff_exists]

@[to_additive]
theorem eq_iff_eq (g : LocalizationMap S P) {x y} : f x = f y ↔ g x = g y :=
  f.eq_iff_exists.trans g.eq_iff_exists.symm

@[to_additive]
theorem mk'_eq_iff_mk'_eq (g : LocalizationMap S P) {x₁ x₂} {y₁ y₂ : S} :
    f.mk' x₁ y₁ = f.mk' x₂ y₂ ↔ g.mk' x₁ y₁ = g.mk' x₂ y₂ :=
  f.eq'.trans g.eq'.symm

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, for all `x₁ : M` and `y₁ ∈ S`,
if `x₂ : M, y₂ ∈ S` are such that `f x₁ * (f y₁)⁻¹ * f y₂ = f x₂`, then there exists `c ∈ S`
such that `x₁ * y₂ * c = x₂ * y₁ * c`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for a Submonoid `S ⊆ M`, for all `x₁ : M`
and `y₁ ∈ S`, if `x₂ : M, y₂ ∈ S` are such that `(f x₁ - f y₁) + f y₂ = f x₂`, then there exists
`c ∈ S` such that `x₁ + y₂ + c = x₂ + y₁ + c`. -/]
theorem exists_of_sec_mk' (x) (y : S) :
    ∃ c : S, ↑c * (↑(f.sec <| f.mk' x y).2 * x) = c * (y * (f.sec <| f.mk' x y).1) :=
  f.eq_iff_exists.1 <| f.mk'_eq_iff_eq.1 <| (mk'_sec _ _).symm

@[to_additive]
theorem mk'_eq_of_eq {a₁ b₁ : M} {a₂ b₂ : S} (H : ↑a₂ * b₁ = ↑b₂ * a₁) :
    f.mk' a₁ a₂ = f.mk' b₁ b₂ :=
  f.mk'_eq_iff_eq.2 <| H ▸ rfl

@[to_additive]
theorem mk'_eq_of_eq' {a₁ b₁ : M} {a₂ b₂ : S} (H : b₁ * ↑a₂ = a₁ * ↑b₂) :
    f.mk' a₁ a₂ = f.mk' b₁ b₂ :=
  f.mk'_eq_of_eq <| by simpa only [mul_comm] using H

@[to_additive]
theorem mk'_cancel (a : M) (b c : S) :
    f.mk' (a * c) (b * c) = f.mk' a b :=
  mk'_eq_of_eq' f (by rw [Submonoid.coe_mul, mul_comm (b : M), mul_assoc])

@[to_additive]
theorem mk'_eq_of_same {a b} {d : S} :
    f.mk' a d = f.mk' b d ↔ ∃ c : S, c * a = c * b := by
  rw [mk'_eq_iff_eq', map_mul, map_mul, ← eq_iff_exists f]
  exact (map_units f d).mul_left_inj

@[to_additive (attr := simp)]
theorem mk'_self' (y : S) : f.mk' (y : M) y = 1 :=
  show _ * _ = _ by rw [mul_inv_left, mul_one]; dsimp

@[to_additive (attr := simp)]
theorem mk'_self (x) (H : x ∈ S) : f.mk' x ⟨x, H⟩ = 1 := mk'_self' f ⟨x, H⟩

@[to_additive]
theorem mul_mk'_eq_mk'_of_mul (x₁ x₂) (y : S) : f x₁ * f.mk' x₂ y = f.mk' (x₁ * x₂) y := by
  rw [← mk'_one, ← mk'_mul, one_mul]

@[to_additive]
theorem mk'_mul_eq_mk'_of_mul (x₁ x₂) (y : S) : f.mk' x₂ y * f x₁ = f.mk' (x₁ * x₂) y := by
  rw [mul_comm, mul_mk'_eq_mk'_of_mul]

@[to_additive]
theorem mul_mk'_one_eq_mk' (x) (y : S) : f x * f.mk' 1 y = f.mk' x y := by
  rw [mul_mk'_eq_mk'_of_mul, mul_one]

@[to_additive (attr := simp)]
theorem mk'_mul_cancel_right (x : M) (y : S) : f.mk' (x * y) y = f x := by
  rw [← mul_mk'_one_eq_mk', map_mul, mul_assoc, mul_mk'_one_eq_mk', mk'_self', mul_one]

@[to_additive]
theorem mk'_mul_cancel_left (x) (y : S) : f.mk' ((y : M) * x) y = f x := by
  rw [mul_comm, mk'_mul_cancel_right]

@[to_additive]
theorem isUnit_comp (j : N →* P) (y : S) : IsUnit (j.comp f.toMonoidHom y) :=
  ⟨Units.map j <| IsUnit.liftRight (f.restrict S) f.map_units y,
    show j _ = j _ from congr_arg j <| IsUnit.coe_liftRight (f.restrict S) f.map_units _⟩

variable {g : M →* P}

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a map of `CommMonoid`s
`g : M →* P` such that `g(S) ⊆ Units P`, `f x = f y → g x = g y` for all `x y : M`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M` and a map of
`AddCommMonoid`s `g : M →+ P` such that `g(S) ⊆ AddUnits P`, `f x = f y → g x = g y`
for all `x y : M`. -/]
theorem eq_of_eq (hg : ∀ y : S, IsUnit (g y)) {x y} (h : f x = f y) : g x = g y := by
  obtain ⟨c, hc⟩ := f.eq_iff_exists.1 h
  rw [← one_mul (g x), ← IsUnit.liftRight_inv_mul (g.restrict S) hg c]
  change _ * g c * _ = _
  rw [mul_assoc, ← g.map_mul, hc, mul_comm, mul_inv_left hg, g.map_mul]

/-- Given `CommMonoid`s `M, P`, Localization maps `f : M →* N, k : P →* Q` for Submonoids
`S, T` respectively, and `g : M →* P` such that `g(S) ⊆ T`, `f x = f y` implies
`k (g x) = k (g y)`. -/
@[to_additive
/-- Given `AddCommMonoid`s `M, P`, Localization maps `f : M →+ N, k : P →+ Q` for AddSubmonoids
`S, T` respectively, and `g : M →+ P` such that `g(S) ⊆ T`, `f x = f y`
implies `k (g x) = k (g y)`. -/]
theorem comp_eq_of_eq {T : Submonoid P} {Q : Type*} [CommMonoid Q] (hg : ∀ y : S, g y ∈ T)
    (k : LocalizationMap T Q) {x y} (h : f x = f y) : k (g x) = k (g y) :=
  f.eq_of_eq (fun y : S ↦ show IsUnit (k.comp g y) from k.map_units ⟨g y, hg y⟩) h

variable (hg : ∀ y : S, IsUnit (g y))

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a map of `CommMonoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` sending `z : N` to `g x * (g y)⁻¹`, where `(x, y) : M × S` are such that
`z = f x * (f y)⁻¹`. -/
@[to_additive
/-- Given a localization map `f : M →+ N` for a submonoid `S ⊆ M` and a map of
`AddCommMonoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism
induced from `N` to `P` sending `z : N` to `g x - g y`, where `(x, y) : M × S` are such that
`z = f x - f y`. -/]
noncomputable def lift : N →* P where
  toFun z := g (f.sec z).1 * (IsUnit.liftRight (g.restrict S) hg (f.sec z).2)⁻¹
  map_one' := by rw [mul_inv_left, mul_one]; exact f.eq_of_eq hg (by rw [← sec_spec, one_mul])
  map_mul' x y := by
    rw [mul_inv_left hg, ← mul_assoc, ← mul_assoc, mul_inv_right hg, mul_comm _ (g (f.sec y).1), ←
      mul_assoc, ← mul_assoc, mul_inv_right hg]
    repeat rw [← g.map_mul]
    refine f.eq_of_eq hg ?_
    simp_rw [map_mul, sec_spec', ← toMonoidHom_apply]
    ac_rfl

@[to_additive]
lemma lift_apply (z) :
    f.lift hg z = g (f.sec z).1 * (IsUnit.liftRight (g.restrict S) hg (f.sec z).2)⁻¹ :=
  rfl

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a map of `CommMonoid`s
`g : M →* P` such that `g y` is invertible for all `y : S`, the homomorphism induced from
`N` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : M, y ∈ S`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M` and a map of
`AddCommMonoid`s `g : M →+ P` such that `g y` is invertible for all `y : S`, the homomorphism
induced from `N` to `P` maps `f x - f y` to `g x - g y` for all `x : M, y ∈ S`. -/]
theorem lift_mk' (x y) : f.lift hg (f.mk' x y) = g x * (IsUnit.liftRight (g.restrict S) hg y)⁻¹ :=
  (mul_inv hg).2 <|
    f.eq_of_eq hg <| by
      simp_rw [map_mul, sec_spec', mul_assoc, f.mk'_spec, mul_comm]

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M` and a localization map
`g : M →* P` for the same submonoid, the homomorphism induced from
`N` to `P` maps `f x * (f y)⁻¹` to `g x * (g y)⁻¹` for all `x : M, y ∈ S`. -/
@[to_additive (attr := simp)
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M` and a localization map
`g : M →+ P` for the same submonoid, the homomorphism
induced from `N` to `P` maps `f x - f y` to `g x - g y` for all `x : M, y ∈ S`. -/]
theorem lift_localizationMap_mk' (g : S.LocalizationMap P) (x y) :
    f.lift g.map_units (f.mk' x y) = g.mk' x y :=
  f.lift_mk' _ _ _

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v : P`, we have
`f.lift hg z = v ↔ g x = g y * v`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, if an
`AddCommMonoid` map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all
`z : N, v : P`, we have `f.lift hg z = v ↔ g x = g y + v`, where `x : M, y ∈ S` are such that
`z + f y = f x`. -/]
theorem lift_spec (z v) : f.lift hg z = v ↔ g (f.sec z).1 = g (f.sec z).2 * v :=
  mul_inv_left hg _ _ v

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N, v w : P`, we have
`f.lift hg z * w = v ↔ g x * w = g y * v`, where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, if an `AddCommMonoid` map
`g : M →+ P` induces a map `f.lift hg : N →+ P` then for all
`z : N, v w : P`, we have `f.lift hg z + w = v ↔ g x + w = g y + v`, where `x : M, y ∈ S` are such
that `z + f y = f x`. -/]
theorem lift_spec_mul (z w v) : f.lift hg z * w = v ↔ g (f.sec z).1 * w = g (f.sec z).2 * v := by
  rw [mul_comm, lift_apply, ← mul_assoc, mul_inv_left hg, mul_comm]

@[to_additive]
theorem lift_mk'_spec (x v) (y : S) : f.lift hg (f.mk' x y) = v ↔ g x = g y * v := by
  rw [f.lift_mk' hg]; exact mul_inv_left hg _ _ _

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`f.lift hg z * g y = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, if an `AddCommMonoid`
map `g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we have
`f.lift hg z + g y = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`. -/]
theorem lift_mul_right (z) : f.lift hg z * g (f.sec z).2 = g (f.sec z).1 := by
  rw [lift_apply, mul_assoc, ← g.restrict_apply, IsUnit.liftRight_inv_mul, mul_one]

/-- Given a Localization map `f : M →* N` for a Submonoid `S ⊆ M`, if a `CommMonoid` map
`g : M →* P` induces a map `f.lift hg : N →* P` then for all `z : N`, we have
`g y * f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z * f y = f x`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for an AddSubmonoid `S ⊆ M`, if an `AddCommMonoid` map
`g : M →+ P` induces a map `f.lift hg : N →+ P` then for all `z : N`, we have
`g y + f.lift hg z = g x`, where `x : M, y ∈ S` are such that `z + f y = f x`. -/]
theorem lift_mul_left (z) : g (f.sec z).2 * f.lift hg z = g (f.sec z).1 := by
  rw [mul_comm, lift_mul_right]

@[to_additive (attr := simp)]
theorem lift_eq (x : M) : f.lift hg (f x) = g x := by
  rw [lift_spec, ← g.map_mul]; exact f.eq_of_eq hg (by rw [sec_spec', map_mul])

@[to_additive]
theorem lift_eq_iff {x y : M × S} :
    f.lift hg (f.mk' x.1 x.2) = f.lift hg (f.mk' y.1 y.2) ↔ g (x.1 * y.2) = g (y.1 * x.2) := by
  rw [lift_mk', lift_mk', mul_inv hg]

@[to_additive (attr := simp)]
theorem lift_comp : (f.lift hg).comp f.toMonoidHom = g := by ext; exact f.lift_eq hg _

@[to_additive (attr := simp)]
theorem lift_of_comp (j : N →* P) : f.lift (f.isUnit_comp j) = j := by
  ext; simp_rw [lift_spec, j.comp_apply, ← map_mul, toMonoidHom_apply, sec_spec']

@[to_additive]
theorem epic_of_localizationMap {P : Type*} [Monoid P] {j k : N →* P}
    (h : j.comp f.toMonoidHom = k.comp f.toMonoidHom) : j = k := by
  ext n
  obtain ⟨⟨m, s⟩, hn : n * f s = f m⟩ := f.surj n
  replace h (a) : j (f a) = k (f a) := congr($h a)
  exact ((f.map_units s).map j).mul_left_inj.mp <| by rw [← j.map_mul, h, ← k.map_mul, hn, h m]

@[to_additive]
theorem lift_unique {j : N →* P} (hj : ∀ x, j (f x) = g x) : f.lift hg = j := by
  ext
  rw [lift_spec, ← hj, ← hj, ← j.map_mul]
  apply congr_arg
  rw [← sec_spec']

@[to_additive (attr := simp)]
theorem lift_id (x) : f.lift f.map_units x = x :=
  DFunLike.ext_iff.1 (f.lift_of_comp <| MonoidHom.id N) x

/-- Given Localization maps `f : M →* N` for a Submonoid `S ⊆ M` and
`k : M →* Q` for a Submonoid `T ⊆ M`, such that `S ≤ T`, and we have
`l : M →* A`, the composition of the induced map `f.lift` for `k` with
the induced map `k.lift` for `l` is equal to the induced map `f.lift` for `l`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N` for a Submonoid `S ⊆ M` and
`k : M →+ Q` for a Submonoid `T ⊆ M`, such that `S ≤ T`, and we have
`l : M →+ A`, the composition of the induced map `f.lift` for `k` with
the induced map `k.lift` for `l` is equal to the induced map `f.lift` for `l` -/]
theorem lift_comp_lift {T : Submonoid M} (hST : S ≤ T) {Q : Type*} [CommMonoid Q]
    (k : LocalizationMap T Q) {A : Type*} [CommMonoid A] {l : M →* A}
    (hl : ∀ w : T, IsUnit (l w)) :
    (k.lift hl).comp (f.lift (map_units k ⟨_, hST ·.2⟩)) =
    f.lift (hl ⟨_, hST ·.2⟩) := .symm <|
  lift_unique _ _ fun x ↦ by rw [← toMonoidHom_apply, ← MonoidHom.comp_apply,
    MonoidHom.comp_assoc, lift_comp, lift_comp]

@[to_additive]
theorem lift_comp_lift_eq {Q : Type*} [CommMonoid Q] (k : LocalizationMap S Q)
    {A : Type*} [CommMonoid A] {l : M →* A} (hl : ∀ w : S, IsUnit (l w)) :
    (k.lift hl).comp (f.lift k.map_units) = f.lift hl :=
  lift_comp_lift f le_rfl k hl

/-- Given two Localization maps `f : M →* N, k : M →* P` for a Submonoid `S ⊆ M`, the hom
from `P` to `N` induced by `f` is left inverse to the hom from `N` to `P` induced by `k`. -/
@[to_additive (attr := simp)
/-- Given two Localization maps `f : M →+ N, k : M →+ P` for a Submonoid `S ⊆ M`, the hom
from `P` to `N` induced by `f` is left inverse to the hom from `N` to `P` induced by `k`. -/]
theorem lift_left_inverse {k : LocalizationMap S P} (z : N) :
    k.lift f.map_units (f.lift k.map_units z) = z :=
  (DFunLike.congr_fun (lift_comp_lift_eq f k f.map_units) z).trans (lift_id f z)

@[to_additive]
theorem lift_surjective_iff :
    Function.Surjective (f.lift hg) ↔ ∀ v : P, ∃ x : M × S, v * g x.2 = g x.1 := by
  constructor
  · intro H v
    obtain ⟨z, hz⟩ := H v
    obtain ⟨x, hx⟩ := f.surj z
    use x
    rw [← hz, f.eq_mk'_iff_mul_eq.2 hx, lift_mk', mul_assoc, mul_comm _ (g ↑x.2),
      ← MonoidHom.restrict_apply, IsUnit.mul_liftRight_inv (g.restrict S) hg, mul_one]
  · intro H v
    obtain ⟨x, hx⟩ := H v
    use f.mk' x.1 x.2
    rw [lift_mk', mul_inv_left hg, mul_comm, ← hx]

@[to_additive]
theorem lift_injective_iff :
    Function.Injective (f.lift hg) ↔ ∀ x y, f x = f y ↔ g x = g y := by
  constructor
  · intro H x y
    constructor
    · exact f.eq_of_eq hg
    · intro h
      rw [← f.lift_eq hg, ← f.lift_eq hg] at h
      exact H h
  · intro H z w h
    obtain ⟨_, _⟩ := f.surj z
    obtain ⟨_, _⟩ := f.surj w
    rw [← f.mk'_sec z, ← f.mk'_sec w]
    exact (mul_inv f.map_units).2 ((H _ _).2 <| (mul_inv hg).1 h)

variable {T : Submonoid P} (hy : ∀ y : S, g y ∈ T) {Q : Type*} [CommMonoid Q]
  (k : LocalizationMap T Q)

/-- Given a `CommMonoid` homomorphism `g : M →* P` where for Submonoids `S ⊆ M, T ⊆ P` we have
`g(S) ⊆ T`, the induced Monoid homomorphism from the Localization of `M` at `S` to the
Localization of `P` at `T`: if `f : M →* N` and `k : P →* Q` are Localization maps for `S` and
`T` respectively, we send `z : N` to `k (g x) * (k (g y))⁻¹`, where `(x, y) : M × S` are such
that `z = f x * (f y)⁻¹`. -/
@[to_additive
/-- Given an `AddCommMonoid` homomorphism `g : M →+ P` where for AddSubmonoids `S ⊆ M, T ⊆ P` we
have `g(S) ⊆ T`, the induced AddMonoid homomorphism from the Localization of `M` at `S` to the
Localization of `P` at `T`: if `f : M →+ N` and `k : P →+ Q` are Localization maps for `S` and
`T` respectively, we send `z : N` to `k (g x) - k (g y)`, where `(x, y) : M × S` are such
that `z = f x - f y`. -/]
noncomputable def map : N →* Q :=
  @lift _ _ _ _ _ _ _ f (k.toMonoidHom.comp g) fun y ↦ k.map_units ⟨g y, hy y⟩

variable {k}

@[to_additive (attr := simp)]
theorem map_eq (x) : f.map hy k (f x) = k (g x) :=
  f.lift_eq (fun y ↦ k.map_units ⟨g y, hy y⟩) x

@[to_additive (attr := simp)]
theorem map_comp : (f.map hy k).comp f.toMonoidHom = k.toMonoidHom.comp g :=
  f.lift_comp fun y ↦ k.map_units ⟨g y, hy y⟩

@[to_additive (attr := simp)]
theorem map_mk' (x) (y : S) : f.map hy k (f.mk' x y) = k.mk' (g x) ⟨g y, hy y⟩ := by
  rw [map, lift_mk', mul_inv_left]
  change k (g x) = k (g y) * _
  rw [mul_mk'_eq_mk'_of_mul]
  exact (k.mk'_mul_cancel_left (g x) ⟨g y, hy y⟩).symm

/-- Given Localization maps `f : M →* N, k : P →* Q` for Submonoids `S, T` respectively, if a
`CommMonoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
`u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) * u` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N, k : P →+ Q` for AddSubmonoids `S, T` respectively, if an
`AddCommMonoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`,
`u : Q`, we have `f.map hy k z = u ↔ k (g x) = k (g y) + u` where `x : M, y ∈ S` are such that
`z + f y = f x`. -/]
theorem map_spec (z u) : f.map hy k z = u ↔ k (g (f.sec z).1) = k (g (f.sec z).2) * u :=
  f.lift_spec (fun y ↦ k.map_units ⟨g y, hy y⟩) _ _

/-- Given Localization maps `f : M →* N, k : P →* Q` for Submonoids `S, T` respectively, if a
`CommMonoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `f.map hy k z * k (g y) = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N, k : P →+ Q` for AddSubmonoids `S, T` respectively, if an
`AddCommMonoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`,
we have `f.map hy k z + k (g y) = k (g x)` where `x : M, y ∈ S` are such that
`z + f y = f x`. -/]
theorem map_mul_right (z) : f.map hy k z * k (g (f.sec z).2) = k (g (f.sec z).1) :=
  f.lift_mul_right (fun y ↦ k.map_units ⟨g y, hy y⟩) _

/-- Given Localization maps `f : M →* N, k : P →* Q` for Submonoids `S, T` respectively, if a
`CommMonoid` homomorphism `g : M →* P` induces a `f.map hy k : N →* Q`, then for all `z : N`,
we have `k (g y) * f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that
`z * f y = f x`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N, k : P →+ Q` for AddSubmonoids `S, T` respectively if an
`AddCommMonoid` homomorphism `g : M →+ P` induces a `f.map hy k : N →+ Q`, then for all `z : N`,
we have `k (g y) + f.map hy k z = k (g x)` where `x : M, y ∈ S` are such that
`z + f y = f x`. -/]
theorem map_mul_left (z) : k (g (f.sec z).2) * f.map hy k z = k (g (f.sec z).1) := by
  rw [mul_comm, f.map_mul_right]

@[to_additive (attr := simp)]
theorem map_id (z : N) : f.map (fun y ↦ show MonoidHom.id M y ∈ S from y.2) f z = z :=
  f.lift_id z

/-- If `CommMonoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive
/-- If `AddCommMonoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/]
theorem map_comp_map {A : Type*} [CommMonoid A] {U : Submonoid A} {R} [CommMonoid R]
    (j : LocalizationMap U R) {l : P →* A} (hl : ∀ w : T, l w ∈ U) :
    (k.map hl j).comp (f.map hy k) =
    f.map (fun x ↦ show l.comp g x ∈ U from hl ⟨g x, hy x⟩) j := by
  ext z
  change j _ * _ = j (l _) * _
  rw [mul_inv_left, ← mul_assoc, mul_inv_right]
  change j _ * j (l (g _)) = j (l _) * _
  rw [← map_mul j, ← map_mul j, ← l.map_mul, ← l.map_mul]
  refine k.comp_eq_of_eq hl j ?_
  rw [map_mul k, map_mul k, sec_spec', mul_assoc, map_mul_right]

/-- If `CommMonoid` homs `g : M →* P, l : P →* A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/
@[to_additive
/-- If `AddCommMonoid` homs `g : M →+ P, l : P →+ A` induce maps of localizations, the composition
of the induced maps equals the map of localizations induced by `l ∘ g`. -/]
theorem map_map {A : Type*} [CommMonoid A] {U : Submonoid A} {R} [CommMonoid R]
    (j : LocalizationMap U R) {l : P →* A} (hl : ∀ w : T, l w ∈ U) (x) :
    k.map hl j (f.map hy k x) = f.map (fun x ↦ show l.comp g x ∈ U from hl ⟨g x, hy x⟩) j x := by
  -- Porting note: need to specify `k` explicitly
  rw [← f.map_comp_map (k := k) hy j hl]
  simp only [MonoidHom.coe_comp, comp_apply]

/-- Given an injective `CommMonoid` homomorphism `g : M →* P`, and a submonoid `S ⊆ M`,
the induced monoid homomorphism from the localization of `M` at `S` to the
localization of `P` at `g S`, is injective.
-/
@[to_additive /-- Given an injective `AddCommMonoid` homomorphism `g : M →+ P`, and a
submonoid `S ⊆ M`, the induced monoid homomorphism from the localization of `M` at `S`
to the localization of `P` at `g S`, is injective. -/]
theorem map_injective_of_injective (hg : Injective g) (k : LocalizationMap (S.map g) Q) :
    Injective (map f (apply_coe_mem_map g S) k) := fun z w hizw ↦ by
  set i := map f (apply_coe_mem_map g S) k
  have ifkg (a : M) : i (f a) = k (g a) := map_eq f (apply_coe_mem_map g S) a
  let ⟨z', w', x, hxz, hxw⟩ := surj₂ f z w
  have : k (g z') = k (g w') := by
    rw [← ifkg, ← ifkg, ← hxz, ← hxw, map_mul, map_mul, hizw]
  obtain ⟨⟨_, c, hc, rfl⟩, eq⟩ := k.exists_of_eq _ _ this
  simp_rw [← map_mul, hg.eq_iff] at eq
  rw [← (f.map_units x).mul_left_inj, hxz, hxw, f.eq_iff_exists]
  exact ⟨⟨c, hc⟩, eq⟩

/-- Given a surjective `CommMonoid` homomorphism `g : M →* P`, and a submonoid `S ⊆ M`,
the induced monoid homomorphism from the localization of `M` at `S` to the
localization of `P` at `g S`, is surjective.
-/
@[to_additive /-- Given a surjective `AddCommMonoid` homomorphism `g : M →+ P`, and a
submonoid `S ⊆ M`, the induced monoid homomorphism from the localization of `M` at `S`
to the localization of `P` at `g S`, is surjective. -/]
theorem map_surjective_of_surjective (hg : Surjective g) (k : LocalizationMap (S.map g) Q) :
    Surjective (map f (apply_coe_mem_map g S) k) := fun z ↦ by
  obtain ⟨y, ⟨y', s, hs, rfl⟩, rfl⟩ := k.mk'_surjective z
  obtain ⟨x, rfl⟩ := hg y
  use f.mk' x ⟨s, hs⟩
  rw [map_mk']

end LocalizationMap

end Submonoid

namespace Submonoid

namespace LocalizationMap

variable (f : S.LocalizationMap N) {g : M →* P} (hg : ∀ y : S, IsUnit (g y)) {T : Submonoid P}
  {Q : Type*} [CommMonoid Q]

/-- If `f : M →* N` and `k : M →* P` are Localization maps for a Submonoid `S`, we get an
isomorphism of `N` and `P`. -/
@[to_additive
/-- If `f : M →+ N` and `k : M →+ R` are Localization maps for an AddSubmonoid `S`, we get an
isomorphism of `N` and `R`. -/]
noncomputable def mulEquivOfLocalizations (k : LocalizationMap S P) : N ≃* P :=
{ toFun := f.lift k.map_units
  invFun := k.lift f.map_units
  left_inv := f.lift_left_inverse
  right_inv := k.lift_left_inverse
  map_mul' := map_mul _ }

@[to_additive (attr := simp)]
theorem mulEquivOfLocalizations_apply {k : LocalizationMap S P} {x} :
    f.mulEquivOfLocalizations k x = f.lift k.map_units x := rfl

@[to_additive (attr := simp)]
theorem mulEquivOfLocalizations_symm_apply {k : LocalizationMap S P} {x} :
    (f.mulEquivOfLocalizations k).symm x = k.lift f.map_units x := rfl

@[to_additive]
theorem mulEquivOfLocalizations_symm_eq_mulEquivOfLocalizations {k : LocalizationMap S P} :
    (k.mulEquivOfLocalizations f).symm = f.mulEquivOfLocalizations k := rfl

/-- If `f : M →* N` is a Localization map for a Submonoid `S` and `k : N ≃* P` is an isomorphism
of `CommMonoid`s, `k ∘ f` is a Localization map for `M` at `S`. -/
@[to_additive
/-- If `f : M →+ N` is a Localization map for a Submonoid `S` and `k : N ≃+ P` is an isomorphism
of `AddCommMonoid`s, `k ∘ f` is a Localization map for `M` at `S`. -/]
def ofMulEquivOfLocalizations (k : N ≃* P) : LocalizationMap S P :=
  (k.toMonoidHom.comp f.toMonoidHom).toLocalizationMap (fun y ↦ isUnit_comp f k.toMonoidHom y)
    (fun v ↦
      let ⟨z, hz⟩ := k.surjective v
      let ⟨x, hx⟩ := f.surj z
      ⟨x, show v * k (f _) = k (f _) by rw [← hx, map_mul, ← hz]⟩)
    fun x y ↦ (k.apply_eq_iff_eq.trans f.eq_iff_exists).1

@[to_additive (attr := simp)]
theorem ofMulEquivOfLocalizations_apply {k : N ≃* P} (x) :
    f.ofMulEquivOfLocalizations k x = k (f x) := rfl

@[to_additive]
theorem ofMulEquivOfLocalizations_eq {k : N ≃* P} :
    (f.ofMulEquivOfLocalizations k).toMonoidHom = k.toMonoidHom.comp f.toMonoidHom := rfl

@[to_additive]
theorem symm_comp_ofMulEquivOfLocalizations_apply {k : N ≃* P} (x) :
    k.symm (f.ofMulEquivOfLocalizations k x) = f x := k.symm_apply_apply (f x)

@[to_additive]
theorem symm_comp_ofMulEquivOfLocalizations_apply' {k : P ≃* N} (x) :
    k (f.ofMulEquivOfLocalizations k.symm x) = f x := k.apply_symm_apply (f x)

@[to_additive]
theorem ofMulEquivOfLocalizations_eq_iff_eq {k : N ≃* P} {x y} :
    f.ofMulEquivOfLocalizations k x = y ↔ f x = k.symm y :=
  k.toEquiv.eq_symm_apply.symm

@[to_additive addEquivOfLocalizations_right_inv]
theorem mulEquivOfLocalizations_right_inv (k : LocalizationMap S P) :
    f.ofMulEquivOfLocalizations (f.mulEquivOfLocalizations k) = k :=
  toMonoidHom_injective <| f.lift_comp k.map_units

@[to_additive addEquivOfLocalizations_right_inv_apply]
theorem mulEquivOfLocalizations_right_inv_apply {k : LocalizationMap S P} {x} :
    f.ofMulEquivOfLocalizations (f.mulEquivOfLocalizations k) x = k x := by simp

@[to_additive]
theorem mulEquivOfLocalizations_left_inv (k : N ≃* P) :
    f.mulEquivOfLocalizations (f.ofMulEquivOfLocalizations k) = k :=
  DFunLike.ext _ _ fun x ↦ DFunLike.ext_iff.1 (f.lift_of_comp k.toMonoidHom) x

@[to_additive]
theorem mulEquivOfLocalizations_left_inv_apply {k : N ≃* P} (x) :
    f.mulEquivOfLocalizations (f.ofMulEquivOfLocalizations k) x = k x := by simp

@[to_additive (attr := simp)]
theorem ofMulEquivOfLocalizations_id : f.ofMulEquivOfLocalizations (MulEquiv.refl N) = f := by
  ext; rfl

@[to_additive]
theorem ofMulEquivOfLocalizations_comp {k : N ≃* P} {j : P ≃* Q} :
    (f.ofMulEquivOfLocalizations (k.trans j)).toMonoidHom =
      j.toMonoidHom.comp (f.ofMulEquivOfLocalizations k).toMonoidHom := by
  ext; rfl

/-- Given `CommMonoid`s `M, P` and Submonoids `S ⊆ M, T ⊆ P`, if `f : M →* N` is a Localization
map for `S` and `k : P ≃* M` is an isomorphism of `CommMonoid`s such that `k(T) = S`, `f ∘ k`
is a Localization map for `T`. -/
@[to_additive
/-- Given `AddCommMonoid`s `M, P` and `AddSubmonoid`s `S ⊆ M, T ⊆ P`, if `f : M →* N` is a
Localization map for `S` and `k : P ≃+ M` is an isomorphism of `AddCommMonoid`s such that
`k(T) = S`, `f ∘ k` is a Localization map for `T`. -/]
def ofMulEquivOfDom {k : P ≃* M} (H : T.map k.toMonoidHom = S) : LocalizationMap T N :=
  have H' : S.comap k.toMonoidHom = T :=
    H ▸ (SetLike.coe_injective <| T.1.1.preimage_image_eq k.toEquiv.injective)
  (f.toMonoidHom.comp k.toMonoidHom).toLocalizationMap
    (fun y ↦
      let ⟨z, hz⟩ := f.map_units ⟨k y, H ▸ Set.mem_image_of_mem k y.2⟩
      ⟨z, hz⟩)
    (fun z ↦
      let ⟨x, hx⟩ := f.surj z
      let ⟨v, hv⟩ := k.surjective x.1
      let ⟨w, hw⟩ := k.surjective x.2
      ⟨(v, ⟨w, H' ▸ show k w ∈ S from hw.symm ▸ x.2.2⟩), by
        simp_rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hv, hw, hx]⟩)
    fun x y ↦ by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, f.eq_iff_exists]
      rintro ⟨c, hc⟩
      let ⟨d, hd⟩ := k.surjective c
      refine ⟨⟨d, H' ▸ show k d ∈ S from hd.symm ▸ c.2⟩, ?_⟩
      rw [← hd, ← map_mul k, ← map_mul k] at hc; exact k.injective hc

@[to_additive (attr := simp)]
theorem ofMulEquivOfDom_apply {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x) :
    f.ofMulEquivOfDom H x = f (k x) := rfl

@[to_additive]
theorem ofMulEquivOfDom_eq {k : P ≃* M} (H : T.map k.toMonoidHom = S) :
    (f.ofMulEquivOfDom H).toMonoidHom = f.toMonoidHom.comp k.toMonoidHom := rfl

@[to_additive]
theorem ofMulEquivOfDom_comp_symm {k : P ≃* M} (H : T.map k.toMonoidHom = S) (x) :
    f.ofMulEquivOfDom H (k.symm x) = f x :=
  congr_arg f <| k.apply_symm_apply x

@[to_additive]
theorem ofMulEquivOfDom_comp {k : M ≃* P} (H : T.map k.symm.toMonoidHom = S) (x) :
    f.ofMulEquivOfDom H (k x) = f x := congr_arg f <| k.symm_apply_apply x

/-- A special case of `f ∘ id = f`, `f` a Localization map. -/
@[to_additive (attr := simp) /-- A special case of `f ∘ id = f`, `f` a Localization map. -/]
theorem ofMulEquivOfDom_id :
    f.ofMulEquivOfDom
        (show S.map (MulEquiv.refl M).toMonoidHom = S from
          Submonoid.ext fun x ↦ ⟨fun ⟨_, hy, h⟩ ↦ h ▸ hy, fun h ↦ ⟨x, h, rfl⟩⟩) = f := by
  ext; rfl

/-- Given Localization maps `f : M →* N, k : P →* U` for Submonoids `S, T` respectively, an
isomorphism `j : M ≃* P` such that `j(S) = T` induces an isomorphism of localizations `N ≃* U`. -/
@[to_additive
/-- Given Localization maps `f : M →+ N, k : P →+ U` for Submonoids `S, T` respectively, an
isomorphism `j : M ≃+ P` such that `j(S) = T` induces an isomorphism of localizations `N ≃+ U`. -/]
noncomputable def mulEquivOfMulEquiv (k : LocalizationMap T Q) {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) : N ≃* Q :=
  f.mulEquivOfLocalizations <| k.ofMulEquivOfDom H

@[to_additive (attr := simp)]
theorem mulEquivOfMulEquiv_eq_map_apply {k : LocalizationMap T Q} {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) (x) :
    f.mulEquivOfMulEquiv k H x =
      f.map (fun y : S ↦ show j.toMonoidHom y ∈ T from H ▸ Set.mem_image_of_mem j y.2) k x := rfl

@[to_additive]
theorem mulEquivOfMulEquiv_eq_map {k : LocalizationMap T Q} {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) :
    (f.mulEquivOfMulEquiv k H).toMonoidHom =
      f.map (fun y : S ↦ show j.toMonoidHom y ∈ T from H ▸ Set.mem_image_of_mem j y.2) k := rfl

@[to_additive]
theorem mulEquivOfMulEquiv_eq {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
    (x) :
    f.mulEquivOfMulEquiv k H (f x) = k (j x) :=
  f.map_eq (fun y : S ↦ H ▸ Set.mem_image_of_mem j y.2) _

@[to_additive]
theorem mulEquivOfMulEquiv_mk' {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T)
    (x y) :
    f.mulEquivOfMulEquiv k H (f.mk' x y) = k.mk' (j x) ⟨j y, H ▸ Set.mem_image_of_mem j y.2⟩ :=
  f.map_mk' (fun y : S ↦ H ▸ Set.mem_image_of_mem j y.2) _ _

@[to_additive]
theorem of_mulEquivOfMulEquiv_apply {k : LocalizationMap T Q} {j : M ≃* P}
    (H : S.map j.toMonoidHom = T) (x) :
    f.ofMulEquivOfLocalizations (f.mulEquivOfMulEquiv k H) x = k (j x) :=
  Submonoid.LocalizationMap.ext_iff.1 (f.mulEquivOfLocalizations_right_inv (k.ofMulEquivOfDom H)) x

@[to_additive]
theorem of_mulEquivOfMulEquiv {k : LocalizationMap T Q} {j : M ≃* P} (H : S.map j.toMonoidHom = T) :
    (f.ofMulEquivOfLocalizations (f.mulEquivOfMulEquiv k H)).toMonoidHom =
      k.toMonoidHom.comp j.toMonoidHom :=
  MonoidHom.ext <| f.of_mulEquivOfMulEquiv_apply H

end LocalizationMap

end Submonoid

namespace Localization

variable (S) in
/-- Natural homomorphism sending `x : M`, `M` a `CommMonoid`, to the equivalence class of
`(x, 1)` in the Localization of `M` at a Submonoid. -/
@[to_additive
/-- Natural homomorphism sending `x : M`, `M` an `AddCommMonoid`, to the equivalence class of
`(x, 0)` in the Localization of `M` at a Submonoid. -/]
def monoidOf : Submonoid.LocalizationMap S (Localization S) :=
  { (r S).mk'.comp <| MonoidHom.inl M S with
    toFun := fun x ↦ mk x 1
    map_one' := mk_one
    map_mul' := fun x y ↦ by rw [mk_mul, mul_one]
    map_units' := fun y ↦
      isUnit_iff_exists_inv.2 ⟨mk 1 y, by rw [mk_mul, mul_one, one_mul, mk_self]⟩
    surj' := fun z ↦ induction_on z fun x ↦
      ⟨x, by rw [mk_mul, mul_comm x.fst, ← mk_mul, mk_self, one_mul]⟩
    exists_of_eq := fun x y ↦ Iff.mp <| mk_eq_mk_iff.trans <| r_iff_exists.trans <| by simp }

@[to_additive]
theorem mk_one_eq_monoidOf_mk (x) : mk x 1 = monoidOf S x := rfl

@[to_additive]
theorem mk_eq_monoidOf_mk'_apply (x y) : mk x y = (monoidOf S).mk' x y :=
  show _ = _ * _ from
    (Submonoid.LocalizationMap.mul_inv_right (monoidOf S).map_units _ _ _).2 <| by
      dsimp
      rw [← mk_one_eq_monoidOf_mk, ← mk_one_eq_monoidOf_mk, mk_mul x y y 1, mul_comm y 1]
      conv => rhs; rw [← mul_one 1]; rw [← mul_one x]
      exact mk_eq_mk_iff.2 (Con.symm _ <| (Localization.r S).mul (Con.refl _ (x, 1)) <| one_rel _)

@[to_additive]
theorem mk_eq_monoidOf_mk' : mk = (monoidOf S).mk' :=
  funext fun _ ↦ funext fun _ ↦ mk_eq_monoidOf_mk'_apply _ _

universe u

@[to_additive (attr := simp)]
theorem liftOn_mk' {p : Sort u} (f : M → S → p) (H) (a : M) (b : S) :
    liftOn ((monoidOf S).mk' a b) f H = f a b := by rw [← mk_eq_monoidOf_mk', liftOn_mk]

@[to_additive (attr := simp)]
theorem liftOn₂_mk' {p : Sort*} (f : M → S → M → S → p) (H) (a c : M) (b d : S) :
    liftOn₂ ((monoidOf S).mk' a b) ((monoidOf S).mk' c d) f H = f a b c d := by
  rw [← mk_eq_monoidOf_mk', liftOn₂_mk]

variable (f : Submonoid.LocalizationMap S N)

/-- Given a Localization map `f : M →* N` for a Submonoid `S`, we get an isomorphism between
the Localization of `M` at `S` as a quotient type and `N`. -/
@[to_additive
/-- Given a Localization map `f : M →+ N` for a Submonoid `S`, we get an isomorphism between
the Localization of `M` at `S` as a quotient type and `N`. -/]
noncomputable def mulEquivOfQuotient (f : Submonoid.LocalizationMap S N) : Localization S ≃* N :=
  (monoidOf S).mulEquivOfLocalizations f

variable {f}

@[to_additive (attr := simp)]
theorem mulEquivOfQuotient_apply (x) : mulEquivOfQuotient f x = (monoidOf S).lift f.map_units x :=
  rfl

@[to_additive]
theorem mulEquivOfQuotient_mk' (x y) : mulEquivOfQuotient f ((monoidOf S).mk' x y) = f.mk' x y :=
  (monoidOf S).lift_mk' _ _ _

@[to_additive]
theorem mulEquivOfQuotient_mk (x y) : mulEquivOfQuotient f (mk x y) = f.mk' x y := by
  rw [mk_eq_monoidOf_mk'_apply]; exact mulEquivOfQuotient_mk' _ _

@[to_additive]
theorem mulEquivOfQuotient_monoidOf (x) : mulEquivOfQuotient f (monoidOf S x) = f x := by simp

@[to_additive (attr := simp)]
theorem mulEquivOfQuotient_symm_mk' (x y) :
    (mulEquivOfQuotient f).symm (f.mk' x y) = (monoidOf S).mk' x y :=
  f.lift_mk' (monoidOf S).map_units _ _

@[to_additive]
theorem mulEquivOfQuotient_symm_mk (x y) : (mulEquivOfQuotient f).symm (f.mk' x y) = mk x y := by
  rw [mk_eq_monoidOf_mk'_apply]; exact mulEquivOfQuotient_symm_mk' _ _

@[to_additive (attr := simp)]
theorem mulEquivOfQuotient_symm_monoidOf (x) : (mulEquivOfQuotient f).symm (f x) = monoidOf S x :=
  f.lift_eq (monoidOf S).map_units _

/-- The localization of a torsion-free monoid is torsion-free. -/
@[to_additive /-- The localization of a torsion-free monoid is torsion-free. -/]
instance instIsMulTorsionFree [IsMulTorsionFree M] : IsMulTorsionFree <| Localization S where
  pow_left_injective n hn := by
    rintro ⟨a⟩ ⟨b⟩ (hab : mk a.1 a.2 ^ n = mk b.1 b.2 ^ n)
    change mk a.1 a.2 = mk b.1 b.2
    simp only [mk_pow, mk_eq_mk_iff, r_iff_exists, SubmonoidClass.coe_pow, Subtype.exists,
      exists_prop] at hab ⊢
    obtain ⟨c, hc, hab⟩ := hab
    refine ⟨c, hc, pow_left_injective hn ?_⟩
    obtain _ | n := n
    · simp
    · simp [mul_pow, pow_succ c, mul_assoc, hab]

end Localization

end CommMonoid

namespace Localization

variable {α : Type*} [CommMonoid α] [IsCancelMul α] {s : Submonoid α} {a₁ b₁ : α} {a₂ b₂ : s}

@[to_additive]
theorem mk_left_injective (b : s) : Injective fun a => mk a b := fun c d h => by
  simpa [mk_eq_mk_iff, r_iff_exists] using h

@[to_additive]
theorem mk_eq_mk_iff' : mk a₁ a₂ = mk b₁ b₂ ↔ ↑b₂ * a₁ = a₂ * b₁ := by
  simp_rw [mk_eq_mk_iff, r_iff_exists, mul_left_cancel_iff, exists_const]

@[to_additive]
instance decidableEq [DecidableEq α] : DecidableEq (Localization s) := fun a b =>
  Localization.recOnSubsingleton₂ a b fun _ _ _ _ => decidable_of_iff' _ mk_eq_mk_iff'

end Localization

namespace OreLocalization

variable (R) [CommMonoid R] (S : Submonoid R)

/-- The morphism `numeratorHom` is a monoid localization map in the case of commutative `R`. -/
protected def localizationMap : S.LocalizationMap R[S⁻¹] := Localization.monoidOf S

/-- If `R` is commutative, Ore localization and monoid localization are isomorphic. -/
protected noncomputable def equivMonoidLocalization : Localization S ≃* R[S⁻¹] := MulEquiv.refl _

end OreLocalization

namespace Submonoid.LocalizationMap

variable {M N : Type*} [CommMonoid M] {S : Submonoid M} [CommMonoid N]

@[to_additive] theorem injective_iff (f : LocalizationMap S N) :
    Injective f ↔ ∀ ⦃x⦄, x ∈ S → IsRegular x := by
  simp_rw [Commute.isRegular_iff (Commute.all _), IsLeftRegular,
    Injective, LocalizationMap.eq_iff_exists, exists_imp, Subtype.forall]
  exact forall₂_swap

@[to_additive] theorem top_injective_iff (f : (⊤ : Submonoid M).LocalizationMap N) :
    Injective f ↔ IsCancelMul M := by
  simp [injective_iff, isCancelMul_iff_forall_isRegular]

@[to_additive] theorem map_isRegular (f : LocalizationMap S N) {m : M}
    (hm : IsRegular m) : IsRegular (f m) := by
  refine (Commute.isRegular_iff (Commute.all _)).mpr fun n₁ n₂ eq ↦ ?_
  have ⟨ms₁, eq₁⟩ := f.surj n₁
  have ⟨ms₂, eq₂⟩ := f.surj n₂
  rw [← (f.map_units (ms₁.2 * ms₂.2)).mul_left_inj, Submonoid.coe_mul]
  replace eq := congr($eq * f (ms₁.2 * ms₂.2))
  simp_rw [mul_assoc] at eq
  rw [map_mul, ← mul_assoc n₁, eq₁, ← mul_assoc n₂, mul_right_comm n₂, eq₂] at eq ⊢
  simp_rw [← map_mul, eq_iff_exists] at eq ⊢
  simp_rw [mul_left_comm _ m] at eq
  exact eq.imp fun _ ↦ (hm.1 ·)

@[to_additive] theorem isCancelMul (f : LocalizationMap S N) [IsCancelMul M] : IsCancelMul N := by
  simp_rw [isCancelMul_iff_forall_isRegular, Commute.isRegular_iff (Commute.all _),
    ← Commute.isRightRegular_iff (Commute.all _)]
  intro n
  have ⟨ms, eq⟩ := f.surj n
  exact (eq ▸ f.map_isRegular (isCancelMul_iff_forall_isRegular.mp ‹_› ms.1)).2.of_mul

end Submonoid.LocalizationMap
