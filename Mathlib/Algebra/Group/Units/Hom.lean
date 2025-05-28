/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Chris Hughes, Kevin Buzzard
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Units.Basic

/-!
# Monoid homomorphisms and units

This file allows to lift monoid homomorphisms to group homomorphisms of their units subgroups. It
also contains unrelated results about `Units` that depend on `MonoidHom`.

## Main declarations

* `Units.map`: Turn a homomorphism from `α` to `β` monoids into a homomorphism from `αˣ` to `βˣ`.
* `MonoidHom.toHomUnits`: Turn a homomorphism from a group `α` to `β` into a homomorphism from
  `α` to `βˣ`.
* `IsLocalHom`: A predicate on monoid maps, requiring that it maps nonunits
  to nonunits. For local rings, this means that the image of the unique maximal ideal is again
  contained in the unique maximal ideal. This is developed earlier, and in the generality of
  monoids, as it allows its use in non-local-ring related contexts, but it does have the
  strange consequence that it does not require local rings, or even rings.

## TODO

The results that don't mention homomorphisms should be proved (earlier?) in a different file and be
used to golf the basic `Group` lemmas.

Add a `@[to_additive]` version of `IsLocalHom`.
-/

assert_not_exists MonoidWithZero DenselyOrdered

open Function

universe u v w

namespace MonoidHom

variable {M N G} [Monoid M] [Monoid N] [Monoid G]

@[to_additive]
def liftLeft (f : M →* N) {p : M →* G} (hp : Function.Surjective p) (g : G → N)
    (h : ∀ x, g (p x) = f x) : G →* N where
  toFun := g
  map_one' := by
    have h := h 1
    simp only [map_one] at h
    assumption
  map_mul' x y := by
    rcases hp x with ⟨_, rfl⟩
    rcases hp y with ⟨_, rfl⟩
    simp_rw [← p.map_mul, h, f.map_mul]

@[to_additive]
def liftRight (f : M →* N) {p : G →* N} (hp : Function.Injective p) (g : M → G)
    (h : ∀ x, p (g x) = f x) : M →* G where
  toFun := g
  map_one' := hp (by simp_rw [h, map_one])
  map_mul' x y := hp (by simp_rw [map_mul, h, map_mul])

end MonoidHom

section MonoidHomClass

/-- If two homomorphisms from a division monoid to a monoid are equal at a unit `x`, then they are
equal at `x⁻¹`. -/
@[to_additive
  "If two homomorphisms from a subtraction monoid to an additive monoid are equal at an
  additive unit `x`, then they are equal at `-x`."]
theorem IsUnit.eq_on_inv {F G N} [DivisionMonoid G] [Monoid N] [FunLike F G N]
    [MonoidHomClass F G N] {x : G} (hx : IsUnit x) (f g : F) (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
  left_inv_eq_right_inv (map_mul_eq_one f hx.inv_mul_cancel)
    (h.symm ▸ map_mul_eq_one g (hx.mul_inv_cancel))

/-- If two homomorphism from a group to a monoid are equal at `x`, then they are equal at `x⁻¹`. -/
@[to_additive
    "If two homomorphism from an additive group to an additive monoid are equal at `x`,
    then they are equal at `-x`."]
theorem eq_on_inv {F G M} [Group G] [Monoid M] [FunLike F G M] [MonoidHomClass F G M]
    (f g : F) {x : G} (h : f x = g x) : f x⁻¹ = g x⁻¹ :=
  (Group.isUnit x).eq_on_inv f g h


end MonoidHomClass

@[to_additive (attr := simps!)]
def MonoidHom.mkUnit {G M : Type*} [Group G] [Monoid M] (f : G →* M) (x : G) : Mˣ :=
  Units.mk _ _ (map_mul_eq_one f (mul_inv_cancel x)) (map_mul_eq_one f (inv_mul_cancel x))

namespace Units

variable {α : Type*} (M : Type u) {N : Type v} {P : Type w} [Monoid M] [Monoid N] [Monoid P]

/-- Coercion `Mˣ → M` as a monoid homomorphism. -/
@[to_additive "Coercion `AddUnits M → M` as an AddMonoid homomorphism."]
def coeHom : Mˣ →* M where
  toFun := Units.val; map_one' := val_one; map_mul' := val_mul

variable {M}

@[to_additive (attr := simp)]
theorem coeHom_apply (x : Mˣ) : coeHom M x = ↑x := rfl

@[to_additive]
theorem coeHom_injective : Function.Injective (coeHom M) := Units.ext

@[to_additive]
theorem coeHom_inj {x y} : coeHom M x = coeHom M y ↔ x = y := coeHom_injective.eq_iff

section DivisionMonoid

variable [DivisionMonoid α]

@[to_additive (attr := simp, norm_cast)]
theorem val_zpow_eq_zpow_val : ∀ (u : αˣ) (n : ℤ), ((u ^ n : αˣ) : α) = (u : α) ^ n :=
  (Units.coeHom α).map_zpow

@[to_additive (attr := simp)]
theorem _root_.map_units_inv {F : Type*} [FunLike F M α] [MonoidHomClass F M α]
    (f : F) (u : Units M) :
    f ↑u⁻¹ = (f u)⁻¹ := ((f : M →* α).comp (Units.coeHom M)).map_inv u

end DivisionMonoid

/-- If a map `g : M → Nˣ` agrees with a homomorphism `f : M →* N`, then
this map is a monoid homomorphism too. -/
@[to_additive
  "If a map `g : M → AddUnits N` agrees with a homomorphism `f : M →+ N`, then this map
  is an AddMonoid homomorphism too."]
def liftRight (f : M →* N) (g : M → Nˣ) (h : ∀ x, g x = f x) : M →* Nˣ :=
  f.liftRight coeHom_injective _ h

@[to_additive (attr := simp)]
theorem liftRight_apply {f : M →* N} {g : M → Nˣ} (h : ∀ x, g x = f x) (x) :
    liftRight f g h x = g x := rfl

@[to_additive (attr := simp)]
theorem inv_liftRight_apply {f : M →* N} {g : M → Nˣ} (h : ∀ x, g x = f x) (x) :
    (liftRight f g h x)⁻¹ = (g x)⁻¹ := rfl

@[to_additive (attr := simp)]
theorem mul_liftRight_inv {f : M →* N} {g : M → Nˣ} (h : ∀ x, g x = f x) (x) :
    f x * ↑(liftRight f g h x)⁻¹ = 1 := h x ▸ Units.mul_inv _

@[to_additive (attr := simp)]
theorem liftRight_inv_mul {f : M →* N} {g : M → Nˣ} (h : ∀ x, g x = f x) (x) :
    ↑(liftRight f g h x)⁻¹ * f x = 1 := h x ▸ Units.inv_mul _

theorem coeHom_comp_liftRight {f : M →* N} {g : M → Nˣ} (h : ∀ x, g x = f x) :
    (coeHom N).comp (liftRight f g h) = f := MonoidHom.ext h

/-- If `f` is a homomorphism from a group `G` to a monoid `M`,
then its image lies in the units of `M`,
and `f.toHomUnits` is the corresponding monoid homomorphism from `G` to `Mˣ`. -/
@[to_additive
  "If `f` is a homomorphism from an additive group `G` to an additive monoid `M`,
  then its image lies in the `AddUnits` of `M`,
  and `f.toHomUnits` is the corresponding homomorphism from `G` to `AddUnits M`."]
def _root_.MonoidHom.toHomUnits {G M : Type*} [Group G] [Monoid M] (f : G →* M) : G →* Mˣ :=
  f.liftRight coeHom_injective f.mkUnit fun _ => rfl

@[to_additive (attr := simp)]
theorem coe_toHomUnits {G M : Type*} [Group G] [Monoid M] (f : G →* M) (g : G) :
    (f.toHomUnits g : M) = f g := rfl

theorem coeHom_comp_toHomUnits {G M : Type*} [Group G] [Monoid M] (f : G →* M) :
  (coeHom M).comp f.toHomUnits = f := rfl

/-- The group homomorphism on units induced by a `MonoidHom`. -/
@[to_additive
  "The additive homomorphism on `AddUnit`s induced by an `AddMonoidHom`."]
def map (f : M →* N) : Mˣ →* Nˣ := (f.comp (coeHom M)).toHomUnits

@[to_additive (attr := simp)]
theorem coe_map (f : M →* N) (x : Mˣ) : ↑(map f x) = f x := rfl

@[to_additive (attr := simp)]
theorem coe_map_inv (f : M →* N) (u : Mˣ) : ↑(map f u)⁻¹ = f ↑u⁻¹ := rfl

@[to_additive (attr := simp)]
lemma map_mk (f : M →* N) (val inv : M) (val_inv inv_val) :
    map f (mk val inv val_inv inv_val) = mk (f val) (f inv)
      (by rw [← f.map_mul, val_inv, f.map_one]) (by rw [← f.map_mul, inv_val, f.map_one]) := rfl

@[to_additive (attr := simp)]
theorem map_comp (f : M →* N) (g : N →* P) : map (g.comp f) = (map g).comp (map f) := rfl

@[to_additive]
lemma map_injective {f : M →* N} (hf : Function.Injective f) :
    Function.Injective (map f) := fun _ _ e => ext (hf (congr_arg val e))

variable (M)

@[to_additive (attr := simp)]
theorem map_id : map (MonoidHom.id M) = MonoidHom.id Mˣ := rfl

@[to_additive (attr := simp)]
theorem map_one : map (1 : M →* N) = 1 := rfl

end Units

namespace IsUnit

variable {F G M N : Type*} [FunLike F M N] [FunLike G N M]

section Monoid

variable [Monoid M] [Monoid N]

@[to_additive]
theorem map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : IsUnit (f x) := by
  rcases h with ⟨y, rfl⟩; exact (Units.map (f : M →* N) y).isUnit

@[to_additive]
theorem of_leftInverse [MonoidHomClass G N M] {f : F} {x : M} (g : G)
    (hfg : Function.LeftInverse g f) (h : IsUnit (f x)) : IsUnit x := by
  simpa only [hfg x] using h.map g

/-- Prefer `IsLocalHom.of_leftInverse`, but we can't get rid of this because of `ToAdditive`. -/
@[to_additive]
theorem _root_.isUnit_map_of_leftInverse [MonoidHomClass F M N] [MonoidHomClass G N M]
    {f : F} {x : M} (g : G) (hfg : Function.LeftInverse g f) :
    IsUnit (f x) ↔ IsUnit x := ⟨of_leftInverse g hfg, map _⟩

/-- If a homomorphism `f : M →* N` sends each element to an `IsUnit`, then it can be lifted
to `f : M →* Nˣ`. See also `Units.liftRight` for a computable version. -/
@[to_additive
  "If a homomorphism `f : M →+ N` sends each element to an `IsAddUnit`, then it can be
  lifted to `f : M →+ AddUnits N`. See also `AddUnits.liftRight` for a computable version."]
noncomputable def liftRight (f : M →* N) (hf : ∀ x, IsUnit (f x)) : M →* Nˣ :=
  (Units.liftRight f fun x => (hf x).unit) fun _ => rfl

@[to_additive]
theorem coe_liftRight (f : M →* N) (hf : ∀ x, IsUnit (f x)) (x) :
    (IsUnit.liftRight f hf x : N) = f x := rfl

@[to_additive (attr := simp)]
theorem mul_liftRight_inv (f : M →* N) (h : ∀ x, IsUnit (f x)) (x) :
    f x * ↑(IsUnit.liftRight f h x)⁻¹ = 1 := Units.mul_liftRight_inv (by intro; rfl) x

@[to_additive (attr := simp)]
theorem liftRight_inv_mul (f : M →* N) (h : ∀ x, IsUnit (f x)) (x) :
    ↑(IsUnit.liftRight f h x)⁻¹ * f x = 1 := Units.liftRight_inv_mul (by intro; rfl) x

end Monoid
end IsUnit

section IsLocalHom

variable {G R S T F : Type*}

variable [Monoid R] [Monoid S] [Monoid T] [FunLike F R S]

/-- A local ring homomorphism is a map `f` between monoids such that `a` in the domain
  is a unit if `f a` is a unit for any `a`. See `IsLocalRing.local_hom_TFAE` for other equivalent
  definitions in the local ring case - from where this concept originates, but it is useful in
  other contexts, so we allow this generalisation in mathlib. -/
class IsLocalHom (f : F) : Prop where
  /-- A local homomorphism `f : R ⟶ S` will send nonunits of `R` to nonunits of `S`. -/
  map_nonunit : ∀ a, IsUnit (f a) → IsUnit a

@[simp]
theorem IsUnit.of_map (f : F) [IsLocalHom f] (a : R) (h : IsUnit (f a)) : IsUnit a :=
  IsLocalHom.map_nonunit a h

-- TODO : remove alias, change the parenthesis of `f` and `a`
alias isUnit_of_map_unit := IsUnit.of_map

variable [MonoidHomClass F R S]

@[simp]
theorem isUnit_map_iff (f : F) [IsLocalHom f] (a : R) : IsUnit (f a) ↔ IsUnit a :=
  ⟨IsLocalHom.map_nonunit a, IsUnit.map f⟩

theorem isLocalHom_of_leftInverse [FunLike G S R] [MonoidHomClass G S R]
    {f : F} (g : G) (hfg : Function.LeftInverse g f) : IsLocalHom f where
  map_nonunit a ha := by rwa [isUnit_map_of_leftInverse g hfg] at ha

@[instance]
theorem MonoidHom.isLocalHom_comp (g : S →* T) (f : R →* S) [IsLocalHom g]
    [IsLocalHom f] : IsLocalHom (g.comp f) where
  map_nonunit a := IsLocalHom.map_nonunit a ∘ IsLocalHom.map_nonunit (f := g) (f a)

-- see note [lower instance priority]
@[instance 100]
theorem isLocalHom_toMonoidHom (f : F) [IsLocalHom f] :
    IsLocalHom (f : R →* S) :=
  ⟨IsLocalHom.map_nonunit (f := f)⟩

theorem MonoidHom.isLocalHom_of_comp (f : R →* S) (g : S →* T) [IsLocalHom (g.comp f)] :
    IsLocalHom f :=
  ⟨fun _ ha => (isUnit_map_iff (g.comp f) _).mp (ha.map g)⟩

end IsLocalHom
