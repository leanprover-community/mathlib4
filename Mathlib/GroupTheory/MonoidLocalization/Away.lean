/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.GroupTheory.MonoidLocalization.Basic

/-!
# Localizing commutative monoids away from an element

We treat the special case of localizing away from an element in the sections
`AwayMap` and `Away`.

## Tags
localization, monoid localization, quotient monoid, congruence relation, characteristic predicate,
commutative monoid, grothendieck group
-/

assert_not_exists MonoidWithZero

open Function

section CommMonoid

variable {M : Type*} [CommMonoid M] {S : Submonoid M} {N : Type*} [CommMonoid N] {P : Type*}
  [CommMonoid P]

namespace Submonoid

namespace LocalizationMap

section AwayMap

variable {g : M →* P} (hg : ∀ y : S, IsUnit (g y))
variable (x : M)

/-- Given `x : M`, the type of `CommMonoid` homomorphisms `f : M →* N` such that `N`
is isomorphic to the Localization of `M` at the Submonoid generated by `x`. -/
@[to_additive
    "Given `x : M`, the type of `AddCommMonoid` homomorphisms `f : M →+ N` such that `N`
is isomorphic to the localization of `M` at the AddSubmonoid generated by `x`."]
abbrev AwayMap (N' : Type*) [CommMonoid N'] := LocalizationMap (powers x) N'

variable (F : AwayMap x N)

/-- Given `x : M` and a Localization map `F : M →* N` away from `x`, `invSelf` is `(F x)⁻¹`. -/
noncomputable def AwayMap.invSelf : N := F.mk' 1 ⟨x, mem_powers _⟩

/-- Given `x : M`, a Localization map `F : M →* N` away from `x`, and a map of `CommMonoid`s
`g : M →* P` such that `g x` is invertible, the homomorphism induced from `N` to `P` sending
`z : N` to `g y * (g x)⁻ⁿ`, where `y : M, n : ℕ` are such that `z = F y * (F x)⁻ⁿ`. -/
noncomputable def AwayMap.lift (hg : IsUnit (g x)) : N →* P :=
  Submonoid.LocalizationMap.lift F fun y ↦
    show IsUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn, g.map_pow]
      exact IsUnit.pow n hg

@[simp]
theorem AwayMap.lift_eq (hg : IsUnit (g x)) (a : M) : F.lift x hg (F.toMap a) = g a :=
  Submonoid.LocalizationMap.lift_eq _ _ _

@[simp]
theorem AwayMap.lift_comp (hg : IsUnit (g x)) : (F.lift x hg).comp F.toMap = g :=
  Submonoid.LocalizationMap.lift_comp _ _

/-- Given `x y : M` and Localization maps `F : M →* N, G : M →* P` away from `x` and `x * y`
respectively, the homomorphism induced from `N` to `P`. -/
noncomputable def awayToAwayRight (y : M) (G : AwayMap (x * y) P) : N →* P :=
  F.lift x <|
    show IsUnit (G.toMap x) from
      isUnit_of_mul_eq_one (G.toMap x) (G.mk' y ⟨x * y, mem_powers _⟩) <| by
        rw [mul_mk'_eq_mk'_of_mul, mk'_self]

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

/-- Given `x : A`, a localization map `F : A →+ B` away from `x`, and a map of `AddCommMonoid`s
`g : A →+ C` such that `g x` is invertible, the homomorphism induced from `B` to `C` sending
`z : B` to `g y - n • g x`, where `y : A, n : ℕ` are such that `z = F y - n • F x`. -/
noncomputable def AwayMap.lift (hg : IsAddUnit (g x)) : B →+ C :=
  AddSubmonoid.LocalizationMap.lift F fun y ↦
    show IsAddUnit (g y.1) by
      obtain ⟨n, hn⟩ := y.2
      rw [← hn]
      dsimp
      rw [g.map_nsmul]
      exact IsAddUnit.map (nsmulAddMonoidHom n : C →+ C) hg

@[simp]
theorem AwayMap.lift_eq (hg : IsAddUnit (g x)) (a : A) : F.lift x hg (F.toMap a) = g a :=
  AddSubmonoid.LocalizationMap.lift_eq _ _ _

@[simp]
theorem AwayMap.lift_comp (hg : IsAddUnit (g x)) : (F.lift x hg).comp F.toMap = g :=
  AddSubmonoid.LocalizationMap.lift_comp _ _

/-- Given `x y : A` and Localization maps `F : A →+ B, G : A →+ C` away from `x` and `x + y`
respectively, the homomorphism induced from `B` to `C`. -/
noncomputable def awayToAwayRight (y : A) (G : AwayMap (x + y) C) : B →+ C :=
  F.lift x <|
    show IsAddUnit (G.toMap x) from
      isAddUnit_of_add_eq_zero (G.toMap x) (G.mk' y ⟨x + y, mem_multiples _⟩) <| by
        rw [add_mk'_eq_mk'_of_add, mk'_self]

end AwayMap

end LocalizationMap

end AddSubmonoid

namespace Localization

section Away

variable (x : M)

/-- Given `x : M`, the Localization of `M` at the Submonoid generated by `x`, as a quotient. -/
@[to_additive
    "Given `x : M`, the Localization of `M` at the Submonoid generated by `x`, as a quotient."]
abbrev Away :=
  Localization (Submonoid.powers x)

/-- Given `x : M`, `invSelf` is `x⁻¹` in the Localization (as a quotient type) of `M` at the
Submonoid generated by `x`. -/
@[to_additive
    "Given `x : M`, `negSelf` is `-x` in the Localization (as a quotient type) of `M` at the
Submonoid generated by `x`."]
def Away.invSelf : Away x :=
  mk 1 ⟨x, Submonoid.mem_powers _⟩

/-- Given `x : M`, the natural hom sending `y : M`, `M` a `CommMonoid`, to the equivalence class
of `(y, 1)` in the Localization of `M` at the Submonoid generated by `x`. -/
@[to_additive
    "Given `x : M`, the natural hom sending `y : M`, `M` an `AddCommMonoid`, to the equivalence
class of `(y, 0)` in the Localization of `M` at the Submonoid generated by `x`."]
abbrev Away.monoidOf : Submonoid.LocalizationMap.AwayMap x (Away x) :=
  Localization.monoidOf (Submonoid.powers x)

@[to_additive]
theorem Away.mk_eq_monoidOf_mk' : mk = (Away.monoidOf x).mk' := by
  simp [Localization.mk_eq_monoidOf_mk']

/-- Given `x : M` and a Localization map `f : M →* N` away from `x`, we get an isomorphism between
the Localization of `M` at the Submonoid generated by `x` as a quotient type and `N`. -/
@[to_additive
    "Given `x : M` and a Localization map `f : M →+ N` away from `x`, we get an isomorphism between
the Localization of `M` at the Submonoid generated by `x` as a quotient type and `N`."]
noncomputable def Away.mulEquivOfQuotient (f : Submonoid.LocalizationMap.AwayMap x N) :
    Away x ≃* N :=
  Localization.mulEquivOfQuotient f

end Away

end Localization

end CommMonoid
