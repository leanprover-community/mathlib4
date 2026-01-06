/-
Copyright (c) 2025 Sven Holtrop and Leonid Ryvkin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Holtrop, Leonid Ryvkin
-/


import Mathlib.RingTheory.Derivation.Lie

/-!
# Lie Rinehart algebras
This file defines Lie-Rinehart algebras and their morphisms.
Lie Rinehart algebras appear in differential geometry as section spaces of Lie algebroids and
singular foliations. The typical Cartan calculus of differential geometry can be restated fully in
terms of the Chevalley-Eilenberg algebra of a Lie-Rinehart algebra.

## References

*

## Tags

Lie-Rinehart algebra
-/




/-- A Lie-Rinehart algebra over a commutative Ring `R` is a commutative `R`-algebra `A` together
with an `A`-module `L` equipped with a Lie bracket and a Lie algebra and module homomorphism
`ρ:L→ Der_R(A,A)` to the derivations of `A`, such that the Leibniz rule `⁅x,a•y⁆=a•⁅x,y⁆+ρ(x)(a)•y`
is satisfied.
In this version of the definition we are encoding the anchor implictly by a Lie action of L on A.
The anchor is later derived as a consequence of the definition.
-/
class LieRinehartAlgebra (R A L : Type*) [CommRing R] [CommRing A] [Algebra R A]
[LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L] [LieRingModule L A]
[LieModule R L A] where
left_linearity : ∀ (a b : A) (x : L) , ⁅a • x, b⁆ = a * ⁅x, b⁆
leibnizA : ∀ (x : L) (a : A) (b : A),  ⁅x, a•b⁆ = a•⁅x, b⁆ + ⁅x, a⁆•b
leibnizL : ∀ (x : L) (a : A) (y : L),  ⁅x, a•y⁆ = a•⁅x, y⁆ + ⁅x, a⁆•y

attribute [simp] LieRinehartAlgebra.left_linearity
attribute [simp] LieRinehartAlgebra.leibnizA
attribute [simp] LieRinehartAlgebra.leibnizL

section instDerivationLieRinehartAlgebra

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]

instance instDerLieRingModule : LieRingModule (Derivation R A A) A where
bracket := fun X a ↦ X ( a )
add_lie := by simp only [Derivation.coe_add, Pi.add_apply, implies_true]
lie_add := by simp only [map_add, implies_true]
leibniz_lie := by exact fun x y m ↦ Eq.symm (add_eq_of_eq_sub rfl)

instance : LieModule R (Derivation R A A) A where
smul_lie := by exact fun t x m ↦ rfl
lie_smul := by intros r X a; exact X.map_smul_of_tower r a

@[simp]
lemma bracketmul (X : Derivation R A A) (a : A) : ⁅ X ,a ⁆ = X a := by rfl


/-- The derivations of an Algebra form a LieRinehartAlgebra themselves
-/
instance : (LieRinehartAlgebra R A (Derivation R A A)) := {
  left_linearity := by exact fun a b x ↦ rfl
  leibnizA := by
    intros X a m
    simp only [smul_eq_mul, bracketmul, Derivation.leibniz, add_right_inj]
    exact CommMonoid.mul_comm m (X a)
  leibnizL := by
    intros X a Y
    ext b
    simp only [bracketmul, Derivation.coe_add, Derivation.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    repeat rw [Derivation.commutator_apply]
    simp only [Derivation.coe_smul, Pi.smul_apply, smul_eq_mul, Derivation.leibniz]
    ring
}

end instDerivationLieRinehartAlgebra


namespace LieRinehartAlgebra


variable {R : Type*} [CommRing R]

variable {A L : Type*} [CommRing A] [Algebra R A]
[LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L] [LieRingModule L A]
[LieModule R L A] [LieRinehartAlgebra R A L]

variable {A' L' : Type*} [CommRing A'] [Algebra R A']
[LieRing L'] [Module A' L'] [LieAlgebra R L'] [IsScalarTower R A' L'] [LieRingModule L' A']
[LieModule R L' A'] [LieRinehartAlgebra R A' L']

variable {A'' L'' : Type*} [CommRing A''] [Algebra R A'']
[LieRing L''] [Module A'' L''] [LieAlgebra R L''] [IsScalarTower R A'' L''] [LieRingModule L'' A'']
[LieModule R L'' A''] [LieRinehartAlgebra R A'' L'']

variable (σ : A →ₐ[R] A')
variable (σ' : A' →ₐ[R] A'')


/-- A homomorphism of Lie-Rinehart algebras `(A,L)`, `(A',L')` consists of an algebra map `σ:A→ A'`
and an `A`-linear map `F: L→L'` which is also a Lie algebra homomorphism and is compatible
with the anchors.
-/
structure Hom (σ : A →ₐ[R] A') (L L' : Type*) [LieRing L] [Module A L] [LieAlgebra R L]
[IsScalarTower R A L] [LieRingModule L A] [LieModule R L A] [LieRinehartAlgebra R A L] [LieRing L']
[Module A' L'] [LieAlgebra R L'] [IsScalarTower R A' L'] [LieRingModule L' A'] [LieModule R L' A']
[LieRinehartAlgebra R A' L']
extends LinearMap (R := A) (S := A') σ.toRingHom L L' where
map_lie' : ∀ (x y : L), toLinearMap ⁅x,y⁆ = ⁅ toLinearMap x, toLinearMap y ⁆
anchorcomp: ∀ (a : A) (l : L), σ (⁅l, a⁆)  =  ⁅(toLinearMap l), (σ a)⁆

@[inherit_doc]
notation:25 L " →ₗ⁅" σ:25 "⁆ " L':0 => LieRinehartAlgebra.Hom σ L L'

instance : CoeFun (L →ₗ⁅σ⁆ L') (fun _ => L → L') := ⟨fun f => f.toLinearMap⟩

@[simp]
lemma lem_map_lie (f : L →ₗ⁅σ⁆ L') (x y : L) : f (⁅x,y⁆) = ⁅ f (x), f (y) ⁆ :=
by exact f.map_lie' x y

@[simp]
lemma lem_anchorcomp (f : L →ₗ⁅σ⁆ L') (l : L) (a : A ): σ (⁅l, a⁆)  =  ⁅f (l), σ (a)⁆ :=
by exact f.anchorcomp a l


/-- Recovers the Lie algebra morphism underlying a Lie-Rinehart algbera homomorophism
-/
def Hom.toLieHom (f : L →ₗ⁅σ⁆ L') : L →ₗ⁅R⁆ L' := {
  toFun := f.toFun
  map_add' := f.map_add'
  map_smul' := by
    intros r l
    simp only [AlgHom.toRingHom_eq_coe, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
      RingHom.id_apply]
    rw [←(IsScalarTower.algebraMap_smul A r l)]
    rw [f.map_smulₛₗ]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, algebraMap_smul]
  map_lie' := by apply f.map_lie'
}

/-- The module homomorphism and the Lie algebra homomorphism undelying a Lie Rinehart homomorphism
are the same function
-/
@[simp]
theorem ModHomeqLieHom (f : L →ₗ⁅σ⁆ L') (x : L) : f.toLinearMap x = (f.toLieHom) x := by rfl


/-- The composition of Lie Rinehart algebra homomorphisms is again a homomorphism
-/
def comp (f : L →ₗ⁅σ⁆ L') (g : L' →ₗ⁅σ'⁆ L'') : L →ₗ⁅(AlgHom.comp σ' σ)⁆ L'' :=
  {
    toLinearMap := by
      haveI h: RingHomCompTriple σ.toRingHom σ'.toRingHom (σ'.comp σ).toRingHom := ⟨rfl⟩
      exact g.toLinearMap.comp f.toLinearMap
    map_lie' := by
      intros x y
      dsimp only [AlgHom.toRingHom_eq_coe, LinearMap.coe_comp, Function.comp_apply]
      repeat rw [ModHomeqLieHom]
      simp only [LieHom.map_lie]
    anchorcomp := by intros l a; dsimp; repeat rw [←lem_anchorcomp]
    }


variable (R) in
/-- The way to see an element of `L` as a derivation of `A`.
Later this will become simply `ρ(a)`
-/
abbrev derivOf (x : L) : Derivation R A A := Derivation.mk' ((LieModule.toEnd R L A) x)
  (by
    intros a b;
    dsimp only [LieModule.toEnd_apply_apply, smul_eq_mul]
    repeat rw [←smul_eq_mul]
    rw [LieRinehartAlgebra.leibnizA R x a b]
    simp only [smul_eq_mul, add_right_inj]
    exact CommMonoid.mul_comm ⁅x, a⁆ b
  )


variable (R A L) in
/-- The anchor of a given LieRinehart algebra `L` over `A` interpreted as a LieRinehart morphism to
the module of derivations of `A`.
-/
def anchor [LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L]
[LieRingModule L A] [LieModule R L A] [LieRinehartAlgebra R A L] : L →ₗ⁅AlgHom.id R A⁆
(Derivation R A A) := {
  toFun := derivOf R
  map_add' := by
    intros x y
    ext a
    simp only [Derivation.coe_mk', map_add, LinearMap.add_apply, LieModule.toEnd_apply_apply,
      Derivation.coe_add, Pi.add_apply]
  map_smul' := by
    intros a X
    ext b
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom, RingHom.id_apply,
      Derivation.coe_smul, Pi.smul_apply, smul_eq_mul]
    apply LieRinehartAlgebra.left_linearity R
  map_lie' := by
    intros x y
    ext a
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom, LinearMap.coe_mk, AddHom.coe_mk,
      Derivation.coe_mk', LieHom.map_lie, LieHom.lie_apply, LieModule.toEnd_apply_apply,
      Module.End.lie_apply]
    rw [Derivation.commutator_apply]
    dsimp only [Derivation.coe_mk', LieModule.toEnd_apply_apply]
  anchorcomp := by simp only [AlgHom.coe_id, id_eq, AlgHom.toRingHom_eq_coe, AlgHom.id_toRingHom,
    LinearMap.coe_mk, AddHom.coe_mk, bracketmul, Derivation.coe_mk', LieModule.toEnd_apply_apply,
    implies_true]
}
end LieRinehartAlgebra
