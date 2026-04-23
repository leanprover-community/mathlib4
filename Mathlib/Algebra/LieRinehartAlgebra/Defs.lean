/-
Copyright (c) 2025 Sven Holtrop and Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Holtrop, Leonid Ryvkin
-/
module

public import Mathlib.RingTheory.Derivation.Lie
public meta import Mathlib.Tactic.ToAdditive
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SetLike

/-!
# Lie-Rinehart algebras

This file defines Lie-Rinehart algebras and their morphisms. It also shows that the derivations of
a commutative algebra over a commutative Ring form such a Lie-Rinehart algebra.
Lie-Rinehart algebras appear in differential geometry as section spaces of Lie algebroids and
singular foliations. The typical Cartan calculus of differential geometry can be restated fully in
terms of the Chevalley-Eilenberg algebra of a Lie-Rinehart algebra.

## References

* [Rinehart, G. S., Differential forms on general commutative algebras. Zbl 0113.26204
  Trans. Am. Math. Soc. 108, 195-222 (1963).][rinehart_1963]

-/

@[expose] public section

/-- A Lie-Rinehart ring is a pair consisting of a commutative ring `A` and a Lie ring `L` such that
`A` and `L` are each a module over the other, satisfying compatibility conditions. -/
class LieRinehartRing (A L : Type*) [CommRing A] [LieRing L]
    [Module A L] [LieRingModule L A] : Prop where
  lie_smul_eq_mul' (a b : A) (x : L) : ⁅a • x, b⁆ = a * ⁅x, b⁆
  leibniz_mul_right' (x : L) (a b : A) : ⁅x, a * b⁆ = a • ⁅x, b⁆ + ⁅x, a⁆ * b
  leibniz_smul_right' (x y : L) (a : A) : ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y

/-- A Lie-Rinehart algebra with coefficients in a commutative ring `R`, is a pair consisting of a
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

variable {R A₁ L₁ A₂ L₂ A₃ L₃ : Type*} [CommRing R]
  [CommRing A₁] [LieRing L₁] [Module A₁ L₁] [LieRingModule L₁ A₁]
  [CommRing A₂] [LieRing L₂] [Module A₂ L₂] [LieRingModule L₂ A₂]
  [CommRing A₃] [LieRing L₃] [Module A₃ L₃] [LieRingModule L₃ A₃]
  [Algebra R A₁] [LieAlgebra R L₁] [Algebra R A₂] [LieAlgebra R L₂]
  [Algebra R A₃] [LieAlgebra R L₃]
  {σ₁₂ : A₁ →ₐ[R] A₂} {σ₂₃ : A₂ →ₐ[R] A₃}

@[simp] lemma LieRinehartRing.lie_smul_eq_mul [LieRinehartRing A₁ L₁] (a b : A₁) (x : L₁) :
  ⁅a • x, b⁆ = a * ⁅x, b⁆ := LieRinehartRing.lie_smul_eq_mul' a b x

@[simp] lemma LieRinehartRing.leibniz_mul_right [LieRinehartRing A₁ L₁] (x : L₁) (a b : A₁) :
  ⁅x, a * b⁆ = a • ⁅x, b⁆ + ⁅x, a⁆ * b := LieRinehartRing.leibniz_mul_right' x a b

@[simp] lemma LieRinehartRing.leibniz_smul_right [LieRinehartRing A₁ L₁] (x y : L₁) (a : A₁) :
  ⁅x, a • y⁆ = a • ⁅x, y⁆ + ⁅x, a⁆ • y := LieRinehartRing.leibniz_smul_right' x y a

instance : LieRinehartRing A₁ (Derivation R A₁ A₁) where
  lie_smul_eq_mul' _ _ _ := rfl
  leibniz_mul_right' _ _ _ := by simp; ring
  leibniz_smul_right' _ _ _ := by ext; simp [Derivation.commutator_apply]; ring

/-- The derivations of a commutative Algebra themselves form a LieRinehart-Algebra. -/
instance : LieRinehartAlgebra R A₁ (Derivation R A₁ A₁) where

/-- A morphism of Lie-Rinehart algebras, from `(A₁, L₁)` to `(A₂, L₂)`, consists of a pair of maps
`(σ, F)` where `σ : A₁ → A₂` is a morphism of algebras and `F` is a morphism of Lie algebras, which
respect the module structures.

Here we define the type of such morphisms with fixed `σ` (which can be regarded as functions
`L₁ → L₂`). In the future it may be useful to define the type of such morphisms with fixed `F`
(which can be regarded as functions `A₁ → A₂`) and the type of all such morphisms (which can be
regarded as functions `A₁ × L₁ → A₂ × L₂`). -/
structure Hom (σ : A₁ →ₐ[R] A₂) (L₁ L₂ : Type*)
    [LieRing L₁] [Module A₁ L₁] [LieRingModule L₁ A₁] [LieAlgebra R L₁]
    [LieRing L₂] [Module A₂ L₂] [LieRingModule L₂ A₂] [LieAlgebra R L₂]
    extends L₁ →ₗ⁅R⁆ L₂ where
  map_smul_apply' (a : A₁) (x : L₁) : toLieHom (a • x) = σ a • toLieHom x
  apply_lie' (a : A₁) (x : L₁) : σ ⁅x, a⁆ = ⁅toLieHom x, σ a⁆

@[inherit_doc]
scoped notation:25 L " →ₗ⁅" σ:25 "⁆ " L₂:0 => LieRinehartAlgebra.Hom σ L L₂

namespace Hom

instance : CoeFun (L₁ →ₗ⁅σ₁₂⁆ L₂) (fun _ => L₁ → L₂) := ⟨fun f => f.toLieHom⟩

/-- This is `LieRinehartAlgebra.Hom.map_smul_apply'` restated using the coercion to function rather
than `LieRinehartAlgebra.Hom.toLieHom`. -/
lemma map_smul_apply (f : L₁ →ₗ⁅σ₁₂⁆ L₂) (a : A₁) (x : L₁) :
    f (a • x) = σ₁₂ a • f x :=
  f.map_smul_apply' a x

/-- This is `LieRinehartAlgebra.Hom.apply_lie'` restated using the coercion to function rather
than `LieRinehartAlgebra.Hom.toLieHom`. -/
lemma apply_lie (f : L₁ →ₗ⁅σ₁₂⁆ L₂) (a : A₁) (x : L₁) :
    σ₁₂ ⁅x, a⁆ = ⁅f x, σ₁₂ a⁆ :=
  f.apply_lie' a x

/-- A morphism of Lie-Rinehart algebras as a semilinear map. -/
def toLinearMap' (f : L₁ →ₗ⁅σ₁₂⁆ L₂) : L₁ →ₛₗ[σ₁₂.toRingHom] L₂ where
  toFun := f
  map_add' := f.map_add'
  map_smul' := f.map_smul_apply

@[simp] lemma toLinearMap'_apply (f : L₁ →ₗ⁅σ₁₂⁆ L₂) (x : L₁) : f.toLinearMap' x = f x := rfl

/-- The composition of Lie-Rinehart algebra morphisms is again a morphism. -/
protected def comp (f : L₁ →ₗ⁅σ₁₂⁆ L₂) (g : L₂ →ₗ⁅σ₂₃⁆ L₃) : L₁ →ₗ⁅σ₂₃.comp σ₁₂⁆ L₃ where
  toLieHom := g.toLieHom.comp f.toLieHom
  map_smul_apply' _ _ := by simp [Hom.map_smul_apply]
  apply_lie' _ _ := by simp [f.apply_lie, g.apply_lie]

/-- The identity morphism of a Lie-Rinehart algebra over the identity algebra homomorphism of the
underlying algebra. -/
protected def id : L₁ →ₗ⁅AlgHom.id R A₁⁆ L₁ where
  __ := LieHom.id
  map_smul_apply' _ _ := by simp
  apply_lie' _ _ := by simp

end Hom

variable [LieRinehartRing A₁ L₁] [LieRinehartAlgebra R A₁ L₁]

set_option backward.isDefEq.respectTransparency false in
variable (R A₁ L₁) in
/-- The anchor of a given Lie-Rinehart algebra `L` over `A` interpreted as a Lie-Rinehart morphism
to the module of derivations of `A`. -/
def anchor : L₁ →ₗ⁅AlgHom.id R A₁⁆ Derivation R A₁ A₁ where
  toFun x := .mk' (LieModule.toEnd R L₁ A₁ x) fun a b ↦ by
    simp [mul_comm b]
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  map_lie' {_ _} := by ext; simp [Derivation.commutator_apply]
  map_smul_apply' _ _ := by ext; simp
  apply_lie' _ _ := by simp

@[simp] lemma anchor_derivation : anchor R A₁ (Derivation R A₁ A₁) = Hom.id := rfl

@[simp] lemma anchor_apply (l : L₁) (a : A₁) :
  (LieRinehartAlgebra.anchor R A₁ L₁ l) a = ⁅l, a⁆ := rfl

end LieRinehartAlgebra
