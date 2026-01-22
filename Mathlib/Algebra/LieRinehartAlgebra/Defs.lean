/-
Copyright (c) 2025 Sven Holtrop and Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Holtrop, Leonid Ryvkin
-/
module

public import Mathlib.RingTheory.Derivation.Lie

/-!
# Lie-Rinehart algebras
This file defines Lie-Rinehart algebras and their morphisms. It also shows that the derivations of
a commutative algebra over a commutative Ring form such a Lie-Rinehart algebra.
Lie-Rinehart algebras appear in differential geometry as section spaces of Lie algebroids and
singular foliations. The typical Cartan calculus of differential geometry can be restated fully in
terms of the Chevalley-Eilenberg algebra of a Lie-Rinehart algebra.

## References

* Rinehart, G. S., Differential forms on general commutative algebras. Zbl 0113.26204
Trans. Am. Math. Soc. 108, 195-222 (1963).

## Tags

Lie-Rinehart algebra
Derivation
-/

@[expose] public section

/-- A Lie-Reinhart ring is a pair consisting of a commutative ring `A` and a Lie ring `L` such that
`A` and `L` are each a module over the other, satisfying compatibility conditions. -/
class LieRinehartRing (A L : Type*) [CommRing A] [LieRing L]
    [Module A L] [LieRingModule L A] : Prop where
  lie_smul_eq_mul (a b : A) (x : L) : ⁅a • x, b⁆ = a * ⁅x, b⁆
  leibniz_mul_right (x : L) (a b : A) : ⁅x, a * b⁆ = a • ⁅x, b⁆ + ⁅x, a⁆ * b
  leibniz_smul_right (x y : L) (a : A) : ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y

/-- A Lie-Reinhart algebra with coefficients in a commutative ring `R`, is a pair consisting of a
commutative `R`-algebra `A` and a Lie algebra `L` with coefficients in `R`, such that `A` and `L`
are each a module over the other, satisfying compatibility conditions.

As shown below, this data determines a linear map `L → Derivation R A A` satisfying a Leibniz-like
compatibility condition. This could even be taken as a definition, however the definition here has
the advantage of being `Prop`-valued, thus mitigating potential diamonds. -/
class LieRinehartAlgebra (R A L : Type*) [CommRing A] [LieRing L]
    [Module A L] [LieRingModule L A] [LieRinehartRing A L]
    [CommRing R] [Algebra R A] [LieAlgebra R L] : Prop extends
    IsScalarTower R A L, LieModule R L A

namespace LieRinehartAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

instance : LieRinehartRing A (Derivation R A A) where
  lie_smul_eq_mul _ _ _ := rfl
  leibniz_mul_right _ _ _ := by simp [CommMonoid.mul_comm]
  leibniz_smul_right _ _ _ := by ext; simp [Derivation.commutator_apply]; ring

/-- The derivations of a commutative Algebra themselves form a LieRinehart-Algebra. -/
instance : LieRinehartAlgebra R A (Derivation R A A) where


variable {R : Type*} [CommRing R]

variable {A L : Type*} [CommRing A] [Algebra R A]
  [LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L] [LieRingModule L A]
  [LieModule R L A] [LieRinehartAlgebra R A L]

variable {A' L' : Type*} [CommRing A'] [Algebra R A']
  [LieRing L'] [Module A' L'] [LieAlgebra R L'] [IsScalarTower R A' L'] [LieRingModule L' A']
  [LieModule R L' A'] [LieRinehartAlgebra R A' L']

variable {A'' L'' : Type*} [CommRing A''] [Algebra R A'']
  [LieRing L''] [Module A'' L''] [LieAlgebra R L''] [IsScalarTower R A'' L'']
  [LieRingModule L'' A''] [LieModule R L'' A''] [LieRinehartAlgebra R A'' L'']

variable (σ : A →ₐ[R] A')
variable (σ' : A' →ₐ[R] A'')
/-- A homomorphism of Lie-Rinehart algebras `(A,L)`, `(A',L')` consists of an algebra map
`σ : A → A'` and an `A`-linear map `F : L → L'` which is also a Lie algebra homomorphism and is
compatible with the anchors.
-/
structure Hom (σ : A →ₐ[R] A') (L L' : Type*) [LieRing L] [Module A L] [LieAlgebra R L]
    [IsScalarTower R A L] [LieRingModule L A] [LieModule R L A] [LieRinehartAlgebra R A L]
    [LieRing L'] [Module A' L'] [LieAlgebra R L'] [IsScalarTower R A' L'] [LieRingModule L' A']
    [LieModule R L' A'] [LieRinehartAlgebra R A' L']
    extends LinearMap (R := A) (S := A') σ.toRingHom L L' where
  map_lie' : ∀ (x y : L), toLinearMap ⁅x, y⁆ = ⁅toLinearMap x, toLinearMap y⁆
  anchor_comp: ∀ (a : A) (l : L), σ (⁅l, a⁆) = ⁅(toLinearMap l), (σ a)⁆

@[inherit_doc]
scoped notation:25 L " →ₗ⁅" σ:25 "⁆ " L':0 => LieRinehartAlgebra.Hom σ L L'

instance : CoeFun (L →ₗ⁅σ⁆ L') (fun _ => L → L') := ⟨fun f => f.toLinearMap⟩


lemma anchor_comp (f : L →ₗ⁅σ⁆ L') (l : L) (a : A): σ ⁅l, a⁆ = ⁅f l, σ a⁆ := f.anchor_comp a l


/-- Recovers the Lie algebra morphism underlying a Lie-Rinehart algebra homomorphism
-/
def Hom.toLieHom (f : L →ₗ⁅σ⁆ L') : L →ₗ⁅R⁆ L' where
  __ := f
  map_smul' _ _ := by simp [← IsScalarTower.algebraMap_smul A]


/-- The module homomorphism and the Lie algebra homomorphism undelying a Lie-Rinehart homomorphism
are the same function
-/
@[simp]
lemma linearMap_eq_lieHom (f : L →ₗ⁅σ⁆ L') (x : L) : f.toLinearMap x = (f.toLieHom) x := rfl


/-- The composition of Lie-Rinehart algebra homomorphisms is again a homomorphism
-/
def Hom.comp (f : L →ₗ⁅σ⁆ L') (g : L' →ₗ⁅σ'⁆ L'') : L →ₗ⁅(AlgHom.comp σ' σ)⁆ L'' where
  toLinearMap := g.toLinearMap.comp f.toLinearMap
  map_lie' _ _ := by
    dsimp
    repeat rw [linearMap_eq_lieHom]
    simp
  anchor_comp _ _ := by
    dsimp
    repeat rw [← anchor_comp]

/-- The identity morphism of a Lie-Rinehart algebra over the identity algebra homomorphism of the
underlying algebra.
-/
def Hom.id : L →ₗ⁅AlgHom.id R A⁆ L where
  __ := LinearMap.id
  map_lie' _ _ := rfl
  anchor_comp a l:= AlgHom.id_apply ⁅l, a⁆


variable (R A L) in
/-- The anchor of a given Lie-Rinehart algebra `L` over `A` interpreted as a Lie-Rinehart morphism
to the module of derivations of `A`.
-/
def anchor [LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L]
    [LieRingModule L A] [LieModule R L A] [LieRinehartAlgebra R A L] :
    L →ₗ⁅AlgHom.id R A⁆ (Derivation R A A) where
  toFun x := Derivation.mk' ((LieModule.toEnd R L A) x) fun a b ↦ by
      simpa [← smul_eq_mul, LieRinehartAlgebra.leibnizA R] using CommMonoid.mul_comm ⁅x, a⁆ b
  map_add' _ _ := by ext a; simp
  map_smul' _ _ := by ext a; simp [LieRinehartAlgebra.left_linearity R]
  map_lie' _ _ := by ext a; simp [Derivation.commutator_apply]
  anchor_comp := by simp

@[simp]
lemma anchor_derivation : anchor R A (Derivation R A A) = Hom.id :=
  rfl

end LieRinehartAlgebra
