/-
Copyright (c) 2024 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Subalgebra

/-!
# Lie derivations

This file defines *Lie derivations* and establishes some basic properties.

## Main definitions

- `LieDerivation`: A Lie derivation `D` from the Lie `R`-algebra `L` to the `L`-module `M` is an
`R`-linear map that satisfies the Leibniz rule `D [a, b] = [a, D b] - [b, D a]`.
- `LieDerivation.inner`: The natural map from a Lie module to the derivations taking values in it.

## Main statements

- `LieDerivation.eqOn_lieSpan`: two Lie derivations equal on a set are equal on its Lie span.
- `LieDerivation.instLieAlgebra`: the set of Lie derivations from a Lie algebra to itself is a Lie
algebra.

## Implementation notes

- Mathematically, a Lie derivation is just a derivation on a Lie algebra. However, the current
implementation of `RingTheory.Derivation` requires a commutative associative algebra, so is
incompatible with the setting of Lie algebras. Initially, this file is a copy-pasted adaptation of
the `RingTheory.Derivation.Basic.lean` file.
- Since we don't have right actions of Lie algebras, the second term in the Leibniz rule is written
as `- [b, D a]`. Within Lie algebras, skew symmetry restores the expected definition `[D a, b]`.
-/

/-- A Lie derivation `D` from the Lie `R`-algebra `L` to the `L`-module `M` is an `R`-linear map
that satisfies the Leibniz rule `D [a, b] = [a, D b] - [b, D a]`. -/
structure LieDerivation (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
    extends L →ₗ[R] M where
  protected leibniz' (a b : L) : toLinearMap ⁅a, b⁆ = ⁅a, toLinearMap b⁆ - ⁅b, toLinearMap a⁆

/-- The `LinearMap` underlying a `LieDerivation`. -/
add_decl_doc LieDerivation.toLinearMap

namespace LieDerivation

section

variable {R L M : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

variable (D : LieDerivation R L M) {D1 D2 : LieDerivation R L M} (a b : L)

instance : FunLike (LieDerivation R L M) L M where
  coe D := D.toFun
  coe_injective' D1 D2 h := by cases D1; cases D2; congr; exact DFunLike.coe_injective h

instance instLinearMapClass : LinearMapClass (LieDerivation R L M) R L M where
  map_add D := D.toLinearMap.map_add'
  map_smulₛₗ D := D.toLinearMap.map_smul

theorem toFun_eq_coe : D.toFun = ⇑D := rfl

/-- See Note [custom simps projection] -/
def Simps.apply (D : LieDerivation R L M) : L → M := D

initialize_simps_projections LieDerivation (toFun → apply)

attribute [coe] toLinearMap

instance instCoeToLinearMap : Coe (LieDerivation R L M) (L →ₗ[R] M) :=
  ⟨fun D => D.toLinearMap⟩

@[simp]
theorem mk_coe (f : L →ₗ[R] M) (h₁) : ((⟨f, h₁⟩ : LieDerivation R L M) : L → M) = f :=
  rfl

@[simp, norm_cast]
theorem coeFn_coe (f : LieDerivation R L M) : ⇑(f : L →ₗ[R] M) = f :=
  rfl

theorem coe_injective : @Function.Injective (LieDerivation R L M) (L → M) DFunLike.coe :=
  DFunLike.coe_injective

@[ext]
theorem ext (H : ∀ a, D1 a = D2 a) : D1 = D2 :=
  DFunLike.ext _ _ H

theorem congr_fun (h : D1 = D2) (a : L) : D1 a = D2 a :=
  DFunLike.congr_fun h a

@[simp]
lemma apply_lie_eq_sub (D : LieDerivation R L M) (a b : L) :
    D ⁅a, b⁆ = ⁅a, D b⁆ - ⁅b, D a⁆ :=
  D.leibniz' a b

/-- For a Lie derivation from a Lie algebra to itself, the usual Leibniz rule holds. -/
lemma apply_lie_eq_add (D : LieDerivation R L L) (a b : L) :
    D ⁅a, b⁆ = ⁅a, D b⁆ + ⁅D a, b⁆ := by
  rw [LieDerivation.apply_lie_eq_sub, sub_eq_add_neg, lie_skew]

/-- Two Lie derivations equal on a set are equal on its Lie span. -/
theorem eqOn_lieSpan {s : Set L} (h : Set.EqOn D1 D2 s) :
    Set.EqOn D1 D2 (LieSubalgebra.lieSpan R L s) :=
    fun z hz =>
      have zero : D1 0 = D2 0 := by simp only [map_zero]
      have smul : ∀ (r : R), ∀ {x : L}, D1 x = D2 x → D1 (r • x) = D2 (r • x) :=
        fun _ _ hx => by simp only [map_smul, hx]
      have add : ∀ x y, D1 x = D2 x → D1 y = D2 y → D1 (x + y) = D2 (x + y) :=
        fun _ _ hx hy => by simp only [map_add, hx, hy]
      have lie : ∀ x y, D1 x = D2 x → D1 y = D2 y → D1 ⁅x, y⁆ = D2 ⁅x, y⁆ :=
        fun _ _ hx hy => by simp only [apply_lie_eq_sub, hx, hy]
      LieSubalgebra.lieSpan_induction R (p := fun x => D1 x = D2 x) hz h zero smul add lie

/-- If the Lie span of a set is the whole Lie algebra, then two Lie derivations equal on this set
are equal on the whole Lie algebra. -/
theorem ext_of_lieSpan_eq_top (s : Set L) (hs : LieSubalgebra.lieSpan R L s = ⊤)
    (h : Set.EqOn D1 D2 s) : D1 = D2 :=
  ext fun _ => eqOn_lieSpan h <| hs.symm ▸ trivial

instance instZero : Zero (LieDerivation R L M) where
  zero :=
    { toLinearMap := 0
      leibniz' := fun a b => by simp only [LinearMap.zero_apply, lie_zero, sub_self] }

@[simp]
theorem coe_zero : ⇑(0 : LieDerivation R L M) = 0 :=
  rfl

@[simp]
theorem coe_zero_linearMap : ↑(0 : LieDerivation R L M) = (0 : L →ₗ[R] M) :=
  rfl

theorem zero_apply (a : L) : (0 : LieDerivation R L M) a = 0 :=
  rfl

instance : Inhabited (LieDerivation R L M) :=
  ⟨0⟩

instance instAdd : Add (LieDerivation R L M) where
  add D1 D2 :=
    { toLinearMap := D1 + D2
      leibniz' := fun a b ↦ by
        simp only [LinearMap.add_apply, coeFn_coe, apply_lie_eq_sub, lie_add, add_sub_add_comm] }

@[simp]
theorem coe_add (D1 D2 : LieDerivation R L M) : ⇑(D1 + D2) = D1 + D2 :=
  rfl

@[simp]
theorem coe_add_linearMap (D1 D2 : LieDerivation R L M) : ↑(D1 + D2) = (D1 + D2 : L →ₗ[R] M) :=
  rfl

theorem add_apply : (D1 + D2) a = D1 a + D2 a :=
  rfl

protected theorem map_neg : D (-a) = -D a :=
  map_neg D a

protected theorem map_sub : D (a - b) = D a - D b :=
  map_sub D a b

instance instNeg : Neg (LieDerivation R L M) :=
  ⟨fun D =>
    mk (-D) fun a b => by
      simp only [LinearMap.neg_apply, coeFn_coe, apply_lie_eq_sub,
        neg_sub, lie_neg, sub_neg_eq_add, add_comm, ← sub_eq_add_neg] ⟩

@[simp]
theorem coe_neg (D : LieDerivation R L M) : ⇑(-D) = -D :=
  rfl

@[simp]
theorem coe_neg_linearMap (D : LieDerivation R L M) : ↑(-D) = (-D : L →ₗ[R] M) :=
  rfl

theorem neg_apply : (-D) a = -D a :=
  rfl

instance instSub : Sub (LieDerivation R L M) :=
  ⟨fun D1 D2 =>
    mk (D1 - D2 : L →ₗ[R] M) fun a b => by
      simp only [LinearMap.sub_apply, coeFn_coe, apply_lie_eq_sub, lie_sub, sub_sub_sub_comm]⟩

@[simp]
theorem coe_sub (D1 D2 : LieDerivation R L M) : ⇑(D1 - D2) = D1 - D2 :=
  rfl

@[simp]
theorem coe_sub_linearMap (D1 D2 : LieDerivation R L M) : ↑(D1 - D2) = (D1 - D2 : L →ₗ[R] M) :=
  rfl

theorem sub_apply {D1 D2 : LieDerivation R L M} : (D1 - D2) a = D1 a - D2 a :=
  rfl

section Scalar

/-- A typeclass mixin saying that scalar multiplication and Lie bracket are left commutative. -/
class SMulBracketCommClass (S L α : Type*) [SMul S α] [LieRing L] [AddCommGroup α]
    [LieRingModule L α] : Prop where
  /-- `•` and `⁅⬝, ⬝⁆`  are left commutative -/
  smul_bracket_comm : ∀ (s : S) (l : L) (a : α), s • ⁅l, a⁆ = ⁅l, s • a⁆

variable {S T : Type*}
variable [Monoid S] [DistribMulAction S M] [SMulCommClass R S M] [SMulBracketCommClass S L M]
variable [Monoid T] [DistribMulAction T M] [SMulCommClass R T M] [SMulBracketCommClass T L M]

instance instSMul : SMul S (LieDerivation R L M) where
  smul r D :=
    { toLinearMap := r • D
      leibniz' := fun a b => by simp only [LinearMap.smul_apply, coeFn_coe, apply_lie_eq_sub,
        smul_sub, SMulBracketCommClass.smul_bracket_comm] }

@[simp]
theorem coe_smul (r : S) (D : LieDerivation R L M) : ⇑(r • D) = r • ⇑D :=
  rfl

@[simp]
theorem coe_smul_linearMap (r : S) (D : LieDerivation R L M) : ↑(r • D) = r • (D : L →ₗ[R] M) :=
  rfl

theorem smul_apply (r : S) (D : LieDerivation R L M) : (r • D) a = r • D a :=
  rfl

instance instSMulBase : SMulBracketCommClass R L M := ⟨fun s l a ↦ (lie_smul s l a).symm⟩

instance instSMulNat : SMulBracketCommClass ℕ L M := ⟨fun s l a => (lie_nsmul l a s).symm⟩

instance instSMulInt : SMulBracketCommClass ℤ L M := ⟨fun s l a => (lie_zsmul l a s).symm⟩

instance instAddCommGroup : AddCommGroup (LieDerivation R L M) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

/-- `coe_fn` as an `AddMonoidHom`. -/
def coeFnAddMonoidHom : LieDerivation R L M →+ L → M where
  toFun := (↑)
  map_zero' := coe_zero
  map_add' := coe_add

instance : DistribMulAction S (LieDerivation R L M) :=
  Function.Injective.distribMulAction coeFnAddMonoidHom coe_injective coe_smul

instance [SMul S T] [IsScalarTower S T M] : IsScalarTower S T (LieDerivation R L M) :=
  ⟨fun _ _ _ => ext fun _ => smul_assoc _ _ _⟩

instance [SMulCommClass S T M] : SMulCommClass S T (LieDerivation R L M) :=
  ⟨fun _ _ _ => ext fun _ => smul_comm _ _ _⟩

end Scalar

instance instModule {S : Type*} [Semiring S] [Module S M] [SMulCommClass R S M]
    [SMulBracketCommClass S L M] : Module S (LieDerivation R L M) :=
  Function.Injective.module S coeFnAddMonoidHom coe_injective coe_smul

end

section

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The commutator of two Lie derivations on a Lie algebra is a Lie derivation. -/
instance instBracket : Bracket (LieDerivation R L L) (LieDerivation R L L) where
  bracket D1 D2 := LieDerivation.mk ⁅(D1 : Module.End R L), (D2 : Module.End R L)⁆ (fun a b => by
    simp only [Ring.lie_def, apply_lie_eq_add, coeFn_coe,
      LinearMap.sub_apply, LinearMap.mul_apply, map_add, sub_lie, lie_sub, ← lie_skew b]
    abel)

variable (D : LieDerivation R L L) {D1 D2 : LieDerivation R L L}

@[simp]
lemma commutator_coe_linear_map : ↑⁅D1, D2⁆ = ⁅(D1 : Module.End R L), (D2 : Module.End R L)⁆ :=
  rfl

lemma commutator_apply (a : L) : ⁅D1, D2⁆ a = D1 (D2 a) - D2 (D1 a) :=
  rfl

instance : LieRing (LieDerivation R L L) where
  add_lie d e f := by
    ext a; simp only [commutator_apply, add_apply, map_add]; abel
  lie_add d e f := by
    ext a; simp only [commutator_apply, add_apply, map_add]; abel
  lie_self d := by
    ext a; simp only [commutator_apply, add_apply, map_add, zero_apply]; abel
  leibniz_lie d e f := by
    ext a; simp only [commutator_apply, add_apply, sub_apply, map_sub]; abel

/-- The set of Lie derivations from a Lie algebra `L` to itself is a Lie algebra. -/
instance instLieAlgebra : LieAlgebra R (LieDerivation R L L) where
  lie_smul := fun r d e => by ext a; simp only [commutator_apply, map_smul, smul_sub, smul_apply]

@[simp] lemma lie_apply (D₁ D₂ : LieDerivation R L L) (x : L) :
    ⁅D₁, D₂⁆ x = D₁ (D₂ x) - D₂ (D₁ x) :=
  rfl

end

section

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The Lie algebra morphism from Lie derivations into linear endormophisms. -/
def toLinearMapLieHom : LieDerivation R L L →ₗ⁅R⁆ L →ₗ[R] L where
  toFun := toLinearMap
  map_add' := by intro D1 D2; dsimp
  map_smul' := by intro D1 D2; dsimp
  map_lie' := by intro D1 D2; dsimp

/-- The map from Lie derivations to linear endormophisms is injective. -/
lemma toLinearMapLieHom_injective : Function.Injective (toLinearMapLieHom R L) :=
  fun _ _ h ↦ ext fun a ↦ congrFun (congrArg DFunLike.coe h) a

/-- Lie derivations over a Noetherian Lie algebra form a Noetherian module. -/
instance instNoetherian [IsNoetherian R L] : IsNoetherian R (LieDerivation R L L) :=
  isNoetherian_of_linearEquiv (LinearEquiv.ofInjective _ (toLinearMapLieHom_injective R L)).symm

end

section Inner

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

/-- The natural map from a Lie module to the derivations taking values in it. -/
@[simps!]
def inner : M →ₗ[R] LieDerivation R L M where
  toFun m :=
    { __ := (LieModule.toEnd R L M : L →ₗ[R] Module.End R M).flip m
      leibniz' := by simp }
  map_add' m n := by ext; simp
  map_smul' t m := by ext; simp

instance instLieRingModule : LieRingModule L (LieDerivation R L M) where
  bracket x D := inner R L M (D x)
  add_lie x y D := by simp
  lie_add x D₁ D₂ := by simp
  leibniz_lie x y D := by simp

@[simp] lemma lie_lieDerivation_apply (x y : L) (D : LieDerivation R L M) :
    ⁅x, D⁆ y = ⁅y, D x⁆ :=
  rfl

@[simp] lemma lie_coe_lieDerivation_apply (x : L) (D : LieDerivation R L M) :
    ⁅x, (D : L →ₗ[R] M)⁆ = ⁅x, D⁆ := by
  ext; simp

instance instLieModule : LieModule R L (LieDerivation R L M) where
  smul_lie t x D := by ext; simp
  lie_smul t x D := by ext; simp

protected lemma leibniz_lie (x : L) (D₁ D₂ : LieDerivation R L L) :
    ⁅x, ⁅D₁, D₂⁆⁆ = ⁅⁅x, D₁⁆, D₂⁆ + ⁅D₁, ⁅x, D₂⁆⁆ := by
  ext y
  simp [-lie_skew, ← lie_skew (D₁ x) (D₂ y), ← lie_skew (D₂ x) (D₁ y), sub_eq_neg_add]

end Inner

end LieDerivation
