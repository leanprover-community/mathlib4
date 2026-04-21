/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Mapping properties of monoid localizations

Given an `S`-localization map `f : M →* N`, we can define `Submonoid.LocalizationMap.lift`, the
homomorphism from `N` induced by a homomorphism from `M` which maps elements of `S` to invertible
elements of the codomain. Similarly, given commutative monoids `P, Q`, a submonoid `T` of `P` and a
localization map for `T` from `P` to `Q`, then a homomorphism `g : M →* P` such that `g(S) ⊆ T`
induces a homomorphism of localizations, `LocalizationMap.map`, from `N` to `Q`.

## Tags

localization, monoid localization, quotient monoid, congruence relation, characteristic predicate,
commutative monoid, grothendieck group
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

assert_not_exists MonoidWithZero Ring

open Function

section CommMonoid

variable {M : Type*} [CommMonoid M] (S : Submonoid M) (N : Type*) [CommMonoid N] {P : Type*}
  [CommMonoid P]

variable {S N}

namespace Submonoid

namespace LocalizationMap

variable (f : LocalizationMap S N)

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
  f.eq_of_eq (fun y : S ↦ show IsUnit (k.toMonoidHom.comp g y) from k.map_units ⟨g y, hg y⟩) h

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

@[to_additive] theorem map_injective_of_surjOn_or_injective
    (or : (S : Set M).SurjOn g T ∨ Injective k) (hg : Injective g) :
    Injective (f.map hy k) := fun z w hizw ↦ by
  set i := f.map hy k
  have ifkg (a : M) : i (f a) = k (g a) := f.map_eq hy a
  have ⟨z', w', x, hxz, hxw⟩ := surj₂ f z w
  have : k (g z') = k (g w') := by rw [← ifkg, ← ifkg, ← hxz, ← hxw, map_mul, map_mul, hizw]
  obtain surj | inj := or
  · have ⟨⟨c, hc'⟩, eq⟩ := k.exists_of_eq this
    obtain ⟨c, hc, rfl⟩ := surj hc'
    simp_rw [← map_mul, hg.eq_iff] at eq
    rw [← (f.map_units x).mul_left_inj, hxz, hxw, f.eq_iff_exists]
    exact ⟨⟨c, hc⟩, eq⟩
  · apply (f.map_units x).mul_right_cancel
    rw [hxz, hxw, hg (inj this)]

@[to_additive] theorem map_surjective_of_surjOn (surj : (S : Set M).SurjOn g T)
    (hg : Surjective g) : Surjective (f.map hy k) := fun z ↦ by
  obtain ⟨y, ⟨t, ht⟩, rfl⟩ := k.mk'_surjective z
  obtain ⟨s, hs, rfl⟩ := surj ht
  obtain ⟨x, rfl⟩ := hg y
  use f.mk' x ⟨s, hs⟩
  rw [map_mk']

/-- Given an injective `CommMonoid` homomorphism `g : M →* P`, and a submonoid `S ⊆ M`,
the induced monoid homomorphism from the localization of `M` at `S` to the
localization of `P` at `g S`, is injective.
-/
@[to_additive /-- Given an injective `AddCommMonoid` homomorphism `g : M →+ P`, and a
submonoid `S ⊆ M`, the induced monoid homomorphism from the localization of `M` at `S`
to the localization of `P` at `g S`, is injective. -/]
theorem map_injective_of_injective (hg : Injective g) (k : LocalizationMap (S.map g) Q) :
    Injective (map f (apply_coe_mem_map g S) k) :=
  f.map_injective_of_surjOn_or_injective _ (.inl <| Set.surjOn_image ..) hg

/-- Given a surjective `CommMonoid` homomorphism `g : M →* P`, and a submonoid `S ⊆ M`,
the induced monoid homomorphism from the localization of `M` at `S` to the
localization of `P` at `g S`, is surjective.
-/
@[to_additive /-- Given a surjective `AddCommMonoid` homomorphism `g : M →+ P`, and a
submonoid `S ⊆ M`, the induced monoid homomorphism from the localization of `M` at `S`
to the localization of `P` at `g S`, is surjective. -/]
theorem map_surjective_of_surjective (hg : Surjective g) (k : LocalizationMap (S.map g) Q) :
    Surjective (map f (apply_coe_mem_map g S) k) :=
  f.map_surjective_of_surjOn _ (Set.surjOn_image ..) hg

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

@[to_additive (attr := simp)]
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
        simp_rw [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, hv, hw]
        dsimp
        rw [hx]⟩)
    fun x y ↦ by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe, toMonoidHom_apply, toMonoidHom_apply, f.eq_iff_exists]
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

end Localization

end CommMonoid
