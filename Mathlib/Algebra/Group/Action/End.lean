/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Yury Kudryashov
-/
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.GroupTheory.Perm.Basic

/-!
# Endomorphisms, homomorphisms and group actions

This file defines `Function.End` as the monoid of endomorphisms on a type,
and provides results relating group actions with these endomorphisms.

## Notation

- `a • b` is used as notation for `SMul.smul a b`.
- `a +ᵥ b` is used as notation for `VAdd.vadd a b`.

## Implementation details

This file should avoid depending on other parts of `GroupTheory`, to avoid import cycles.
More sophisticated lemmas belong in `GroupTheory.GroupAction`.

## Tags

group action
-/

assert_not_exists MonoidWithZero

open Function (Injective Surjective)

variable {G M N O α : Type*}

section CompatibleScalar

/-- If the multiplicative action of `M` on `N` is compatible with multiplication on `N`, then
`fun x ↦ x • 1` is a monoid homomorphism from `M` to `N`. -/
@[to_additive (attr := simps)
"If the additive action of `M` on `N` is compatible with addition on `N`, then
`fun x ↦ x +ᵥ 0` is an additive monoid homomorphism from `M` to `N`."]
def MonoidHom.smulOneHom {M N} [Monoid M] [MulOneClass N] [MulAction M N] [IsScalarTower M N N] :
    M →* N where
  toFun x := x • (1 : N)
  map_one' := one_smul _ _
  map_mul' x y := by rw [smul_one_mul, smul_smul]

/-- A monoid homomorphism between two monoids M and N can be equivalently specified by a
multiplicative action of M on N that is compatible with the multiplication on N. -/
@[to_additive
"A monoid homomorphism between two additive monoids M and N can be equivalently
specified by an additive action of M on N that is compatible with the addition on N."]
def monoidHomEquivMulActionIsScalarTower (M N) [Monoid M] [Monoid N] :
    (M →* N) ≃ {_inst : MulAction M N // IsScalarTower M N N} where
  toFun f := ⟨MulAction.compHom N f, SMul.comp.isScalarTower _⟩
  invFun := fun ⟨_, _⟩ ↦ MonoidHom.smulOneHom
  left_inv f := MonoidHom.ext fun m ↦ mul_one (f m)
  right_inv := fun ⟨_, _⟩ ↦ Subtype.ext <| MulAction.ext <| funext₂ <| smul_one_smul N

end CompatibleScalar

variable (α) in
/-- The monoid of endomorphisms.

Note that this is generalized by `CategoryTheory.End` to categories other than `Type u`. -/
protected def Function.End := α → α

instance : Monoid (Function.End α) where
  one := id
  mul := (· ∘ ·)
  mul_assoc _ _ _ := rfl
  mul_one _ := rfl
  one_mul _ := rfl
  npow n f := f^[n]
  npow_succ _ _ := Function.iterate_succ _ _

instance : Inhabited (Function.End α) := ⟨1⟩

/-- The tautological action by `Function.End α` on `α`.

This is generalized to bundled endomorphisms by:
* `Equiv.Perm.applyMulAction`
* `AddMonoid.End.applyDistribMulAction`
* `AddMonoid.End.applyModule`
* `AddAut.applyDistribMulAction`
* `MulAut.applyMulDistribMulAction`
* `LinearEquiv.applyDistribMulAction`
* `LinearMap.applyModule`
* `RingHom.applyMulSemiringAction`
* `RingAut.applyMulSemiringAction`
* `AlgEquiv.applyMulSemiringAction`
-/
instance Function.End.applyMulAction : MulAction (Function.End α) α where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The tautological additive action by `Additive (Function.End α)` on `α`. -/
instance Function.End.applyAddAction : AddAction (Additive (Function.End α)) α := inferInstance

@[simp] lemma Function.End.smul_def (f : Function.End α) (a : α) : f • a = f a := rfl

--TODO - This statement should be somethting like `toFun (f * g) = toFun f ∘ toFun g`
lemma Function.End.mul_def (f g : Function.End α) : (f * g) = f ∘ g := rfl

--TODO - This statement should be somethting like `toFun 1 = id`
lemma Function.End.one_def : (1 : Function.End α) = id := rfl

/-- `Function.End.applyMulAction` is faithful. -/
instance Function.End.apply_FaithfulSMul : FaithfulSMul (Function.End α) α where
  eq_of_smul_eq_smul := funext

/-- The monoid hom representing a monoid action.

When `M` is a group, see `MulAction.toPermHom`. -/
def MulAction.toEndHom [Monoid M] [MulAction M α] : M →* Function.End α where
  toFun := (· • ·)
  map_one' := funext (one_smul M)
  map_mul' x y := funext (mul_smul x y)

/-- The additive monoid hom representing an additive monoid action.

When `M` is a group, see `AddAction.toPermHom`. -/
def AddAction.toEndHom [AddMonoid M] [AddAction M α] : M →+ Additive (Function.End α) :=
  MonoidHom.toAdditive'' MulAction.toEndHom

/-- The monoid action induced by a monoid hom to `Function.End α`

See note [reducible non-instances]. -/
abbrev MulAction.ofEndHom [Monoid M] (f : M →* Function.End α) : MulAction M α := .compHom α f

/-- Given an action of an additive group `α` on a set `β`, each `g : α` defines a permutation of
`β`. -/
@[simps!]
def AddAction.toPermHom (α : Type*) [AddGroup α] [AddAction α β] :
    α →+ Additive (Equiv.Perm β) :=
  MonoidHom.toAdditive'' <| MulAction.toPermHom (Multiplicative α) β

/-- Given an action of a group `G` on a type `α`, each `g : G` defines a permutation of `α`. -/
@[simps]
def MulAction.toPermHom [Group G] [MulAction G α] : G →* Equiv.Perm α where
  toFun := MulAction.toPerm
  map_one' := Equiv.ext <| one_smul α
  map_mul' u₁ u₂ := Equiv.ext <| mul_smul (u₁ : α) u₂

section MulDistribMulAction
variable [Monoid M] [Monoid N] [Monoid O] [MulDistribMulAction M N] [MulDistribMulAction N O]

/-- Pullback a multiplicative distributive multiplicative action along an injective monoid
homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Injective.mulDistribMulAction [SMul M O] (f : O →* N) (hf : Injective f)
  (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M O where
  __ := hf.mulAction f smul
  smul_mul c x y := hf <| by simp only [smul, f.map_mul, smul_mul']
  smul_one c := hf <| by simp only [smul, f.map_one, smul_one]

/-- Pushforward a multiplicative distributive multiplicative action along a surjective monoid
homomorphism.
See note [reducible non-instances]. -/
protected abbrev Function.Surjective.mulDistribMulAction [SMul M O] (f : N →* O) (hf : Surjective f)
    (smul : ∀ (c : M) (x), f (c • x) = c • f x) : MulDistribMulAction M O where
  __ := hf.mulAction f smul
  smul_mul c := by simp only [hf.forall, smul_mul', ← smul, ← f.map_mul, implies_true]
  smul_one c := by rw [← f.map_one, ← smul, smul_one]

variable (N) in
/-- Scalar multiplication by `r` as a `MonoidHom`. -/
def MulDistribMulAction.toMonoidHom (r : M) : N →* N where
  toFun := (r • ·)
  map_one' := smul_one r
  map_mul' := smul_mul' r

@[simp]
lemma MulDistribMulAction.toMonoidHom_apply (r : M) (x : N) : toMonoidHom N r x = r • x := rfl

@[simp] lemma smul_pow' (r : M) (x : N) (n : ℕ) : r • x ^ n = (r • x) ^ n :=
  (MulDistribMulAction.toMonoidHom ..).map_pow ..

end MulDistribMulAction

section MulDistribMulAction
variable [Monoid M] [Group G] [MulDistribMulAction M G]

@[simp]
lemma smul_inv' (r : M) (x : G) : r • x⁻¹ = (r • x)⁻¹ :=
  (MulDistribMulAction.toMonoidHom G r).map_inv x

lemma smul_div' (r : M) (x y : G) : r • (x / y) = r • x / r • y :=
  map_div (MulDistribMulAction.toMonoidHom G r) x y

end MulDistribMulAction

section MulDistribMulAction
variable [Group G] [Monoid M] [MulDistribMulAction G M]
variable (M)

/-- Each element of the group defines a multiplicative monoid isomorphism.

This is a stronger version of `MulAction.toPerm`. -/
@[simps (config := { simpRhs := true })]
def MulDistribMulAction.toMulEquiv (x : G) : M ≃* M :=
  { MulDistribMulAction.toMonoidHom M x, MulAction.toPermHom G M x with }

end MulDistribMulAction
