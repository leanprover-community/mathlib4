/-
Copyright (c) 2025 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.GroupTheory.GroupAction.Hom

/-!
# Equivariant homomorphisms

## Main definitions

* `MulActionEquiv φ X Y`, the type of equivariant isomorphisms from `X` to `Y`,
  where `φ : M ≃ N` is an equivalence, `M` acting on the type `X` and `N` acting on the type of `Y`.
  `AddActionEquiv φ X Y` is its additive version.

The above types have corresponding classes:
* `MulActionEquivClass F φ X Y` states that `F` is a type of bundled `X ≃ Y` isoms
  which are `φ`-equivariant;
  `AddActionEquivClass F φ X Y` is its additive version.

## Notation

We introduce the following notation to code equivariant isomorphisms
(the subscript index `ₑ` is for *equivariant*) :
* `X ≃ₑ[φ] Y` is `MulActionEquiv φ X Y` and `AddActionEquiv φ X Y`

When `M = N` and `φ = MulEquiv.refl M`, we provide the backward compatible notation :
* `X ≃[M] Y` is `MulActionHom (Equiv.refl M) X Y` and `AddActionHom (Equiv.refl M) X Y`

The notation for `MulActionHom` and `AddActionHom` is the same, because it is unlikely
that it could lead to confusion — unless one needs types `M` and `X` with simultaneous
instances of `Mul M`, `Add M`, `SMul M X` and `VAdd M X`…

## TODO
* `DistribMulActionEquiv φ A B` (`A ≃ₑ+[φ] B`)
  the type of equivariant additive monoid isomorphisms from `A` to `B`,
  where `φ : M ≃ N` is an isomorphism of monoids,
  `M` acting on the additive monoid `A` and `N` acting on the additive monoid of `B`
* `SMulSemiringEquiv φ R S`, the type of equivariant ring isomorphisms
  from `R` to `S`, where `φ : M → N` is an isomorphism of monoids,
  `M` acting on the ring `R` and `N` acting on the ring `S`.
* `DistribMulActionEquivClass F φ A B` states that `F` is a type of bundled `A ≃ B` isoms
  preserving the additive monoid structure and `φ`-equivariant
* `SMulSemiringEquivClass F φ R S` states that `F` is a type of bundled `R ≃ S` isoms
  preserving the ring structure and `φ`-equivariant

* `A ≃+[M] B` is `DistribMulActionHom (MulEquiv.refl M) A B`
* `R ≃+*[M] S` is `MulSemiringActionHom (MulEquiv.refl M) R S`

-/

@[expose] public section

assert_not_exists Submonoid

section MulActionEquiv

variable {M' : Type*}
variable {M : Type*} {N : Type*} {P : Type*}
variable (φ : M ≃ N) (ψ : N ≃ P) (χ : M ≃ P)
variable (X : Type*) [SMul M X] [SMul M' X]
variable (Y : Type*) [SMul N Y] [SMul M' Y]
variable (Z : Type*) [SMul P Z]

/-- Equivariant functions :
When `φ : M ≃ N` is an equivalence, and types `X` and `Y` are endowed with additive actions
of `M` and `N`, an equivalence `f : X ≃ Y` is `φ`-equivariant if `f (m +ᵥ x) = (φ m) +ᵥ (f x)`. -/
structure AddActionEquiv (φ : M ≃ N) (X : Type*) [VAdd M X] (Y : Type*) [VAdd N Y] where
  /-- The underlying function. -/
  protected toEquiv : X ≃ Y
  /-- The proposition that the function commutes with the additive actions. -/
  protected map_vadd' : ∀ (m : M) (x : X), toEquiv (m +ᵥ x) = (φ m) +ᵥ toEquiv x

/-- Equivariant functions :
When `φ : M ≃ N` is an equivalence, and types `X` and `Y` are endowed with actions of `M` and `N`,
an equivalence `f : X ≃ Y` is `φ`-equivariant if `f (m • x) = (φ m) • (f x)`. -/
@[to_additive]
structure MulActionEquiv where
  /-- The underlying function. -/
  protected toEquiv : X ≃ Y
  /-- The proposition that the function commutes with the actions. -/
  protected map_smul' : ∀ (m : M) (x : X), toEquiv (m • x) = (φ m) • toEquiv x

/- Porting note: local notation given a name, conflict with Algebra.Hom.GroupAction
see https://github.com/leanprover/lean4/issues/2000 -/
/-- `φ`-equivariant functions `X ≃ Y`,
where `φ : M ≃ N`, where `M` and `N` act on `X` and `Y` respectively. -/
notation:25 (name := «MulActionEquivLocal≺») X " ≃ₑ[" φ:25 "] " Y:0 => MulActionEquiv φ X Y

/-- `M`-equivariant equivalences `X ≃ Y` with respect to the action of `M`.
This is the same as `X ≃ₑ[Equiv.refl M] Y`. -/
notation:25
  (name := «MulActionEquivIdLocal≺») X " ≃[" M:25 "] " Y:0 => MulActionEquiv (Equiv.refl M) X Y

/-- `φ`-equivariant equivalences `X ≃ Y`,
where `φ : M ≃ N`, where `M` and `N` act additively on `X` and `Y` respectively

We use the same notation as for multiplicative actions, as conflicts are unlikely. -/
notation:25 (name := «AddActionEquivLocal≺») X " ≃ₑ[" φ:25 "] " Y:0 => AddActionEquiv φ X Y

/-- `M`-equivariant equivalences `X ≃ Y` with respect to the additive action of `M`.
This is the same as `X ≃ₑ[Equiv.refl M] Y`.

We use the same notation as for multiplicative actions, as conflicts are unlikely. -/
notation:25
  (name := «AddActionEquivIdLocal≺») X " ≃[" M:25 "] " Y:0 => AddActionEquiv (Equiv.refl M) X Y

/-- `AddActionSemiEquivClass F φ X Y` states that
  `F` is a type of ismorphisms which are `φ`-equivariant.

You should extend this class when you extend `AddActionEquiv`. -/
class AddActionSemiEquivClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M ≃ N))
    (X Y : outParam Type*) [VAdd M X] [VAdd N Y] [EquivLike F X Y] : Prop where
  /-- The proposition that the function preserves the action. -/
  map_vaddₛₗ : ∀ (f : F) (c : M) (x : X), f (c +ᵥ x) = (φ c) +ᵥ (f x)

/-- `MulActionSemiEquivClass F φ X Y` states that
  `F` is a type of isomorphisms which are `φ`-equivariant.

You should extend this class when you extend `MulActionEquiv`. -/
@[to_additive]
class MulActionSemiEquivClass (F : Type*)
    {M N : outParam Type*} (φ : outParam (M ≃ N))
    (X Y : outParam Type*) [SMul M X] [SMul N Y] [EquivLike F X Y] : Prop where
  /-- The proposition that the function preserves the action. -/
  map_smulₛₗ : ∀ (f : F) (c : M) (x : X), f (c • x) = (φ c) • (f x)

export MulActionSemiEquivClass (map_smulₛₗ)
export AddActionSemiEquivClass (map_vaddₛₗ)

@[to_additive]
instance (F : Type*) [EquivLike F X Y] [MulActionSemiEquivClass F φ X Y] :
    MulActionSemiHomClass F φ X Y where
  map_smulₛₗ := MulActionSemiEquivClass.map_smulₛₗ

/-- `MulActionEquivClass F M X Y` states that `F` is a type of
isomorphisms which are equivariant with respect to actions of `M`
This is an abbreviation of `MulActionSemiEquivClass`. -/
@[to_additive /-- `MulActionEquivClass F M X Y` states that `F` is a type of
isomorphisms which are equivariant with respect to actions of `M`
This is an abbreviation of `MulActionSemiEquivClass`. -/]
abbrev MulActionEquivClass (F : Type*) (M : outParam Type*)
    (X Y : outParam Type*) [SMul M X] [SMul M Y] [EquivLike F X Y] :=
  MulActionSemiEquivClass F (Equiv.refl M) X Y

@[to_additive] instance : EquivLike (MulActionEquiv φ X Y) X Y where
  coe f := MulActionEquiv.toEquiv f
  inv f := (MulActionEquiv.toEquiv f).symm
  left_inv f x := by simp
  right_inv f x := by simp
  coe_injective' f g h hs := by
    cases f
    cases g
    simp only [MulActionEquiv.mk.injEq]
    ext
    simp [h]

@[to_additive]
instance : MulActionSemiEquivClass (X ≃ₑ[φ] Y) φ X Y where
  map_smulₛₗ := MulActionEquiv.map_smul'

initialize_simps_projections MulActionEquiv (toEquiv → apply)
initialize_simps_projections AddActionEquiv (toEquiv → apply)

end MulActionEquiv
