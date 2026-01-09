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
Lie Rinehart algebras appear in differential geometry as section spaces of Lie algebroids and
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

/-- A Lie-Rinehart algebra over a commutative ring `R` is a commutative `R`-algebra `A` together
with an `A`-module `L` equipped with a Lie bracket and a Lie algebra and module homomorphism
`anchor : L → Derivation R A A` to the derivations of `A`, such that the Leibniz rule
`⁅x,a•y⁆=a•⁅x,y⁆+(anchor x)(a)•y` is satisfied.
In this version of the definition we are encoding the anchor implictly by a Lie action of L on A.
The anchor is later derived as a consequence of the definition.
-/
class LieRinehartAlgebra (R A L : Type*) [CommRing R] [CommRing A] [Algebra R A]
    [LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L] [LieRingModule L A]
    [LieModule R L A] where
  left_linearity : ∀ (a b : A) (x : L) , ⁅a•x, b⁆ = a * ⁅x, b⁆
  leibnizA : ∀ (x : L) (a : A) (b : A), ⁅x, a•b⁆ = a•⁅x, b⁆ + ⁅x, a⁆•b
  leibnizL : ∀ (x : L) (a : A) (y : L), ⁅x, a•y⁆ = a•⁅x, y⁆ + ⁅x, a⁆•y

section instDerivationLieRinehartAlgebra

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [Algebra R A]

/-- The derivations of a commutative Algebra themselves form a LieRinehart-Algebra
-/
instance : (LieRinehartAlgebra R A (Derivation R A A)) :=
{ left_linearity := fun _ _ _ ↦ rfl
  leibnizA := by simp [CommMonoid.mul_comm]
  leibnizL := fun _ _ _ ↦ by
    ext b
    simp [Derivation.commutator_apply]
    ring }

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
notation:25 L " →ₗ⁅" σ:25 "⁆ " L':0 => LieRinehartAlgebra.Hom σ L L'

instance : CoeFun (L →ₗ⁅σ⁆ L') (fun _ => L → L') := ⟨fun f => f.toLinearMap⟩


lemma anchor_comp (f : L →ₗ⁅σ⁆ L') (l : L) (a : A): σ ⁅l, a⁆ = ⁅f l, σ a⁆ := f.anchor_comp a l


/-- Recovers the Lie algebra morphism underlying a Lie-Rinehart algebra homomorphism
-/
def Hom.toLieHom (f : L →ₗ⁅σ⁆ L') : L →ₗ⁅R⁆ L' := {
  toFun := f.toFun
  map_add' := f.map_add'
  map_smul' := fun _ _ ↦ by simp [←IsScalarTower.algebraMap_smul A]
  map_lie' := by apply f.map_lie'
}


/-- The module homomorphism and the Lie algebra homomorphism undelying a Lie Rinehart homomorphism
are the same function
-/
@[simp]
lemma linearMap_eq_lieHom (f : L →ₗ⁅σ⁆ L') (x : L) : f.toLinearMap x = (f.toLieHom) x := rfl



/-- The composition of Lie Rinehart algebra homomorphisms is again a homomorphism
-/
def Hom.comp (f : L →ₗ⁅σ⁆ L') (g : L' →ₗ⁅σ'⁆ L'') : L →ₗ⁅(AlgHom.comp σ' σ)⁆ L'' :={
  toLinearMap := by
    haveI h: RingHomCompTriple σ.toRingHom σ'.toRingHom (σ'.comp σ).toRingHom := ⟨rfl⟩
    exact g.toLinearMap.comp f.toLinearMap
  map_lie' := fun _ _ ↦ by
    dsimp
    repeat rw [linearMap_eq_lieHom]
    simp
  anchor_comp := fun _ _ ↦ by
    dsimp
    repeat rw [←anchor_comp]
}



variable (R) in
/-- The way to see an element of `L` as a derivation of `A`.
Later this will become simply `anchor a`
-/
abbrev derivOf (x : L) : Derivation R A A := Derivation.mk' ((LieModule.toEnd R L A) x)
  (fun a b ↦ by
    simp only [← smul_eq_mul, LieModule.toEnd_apply_apply, LieRinehartAlgebra.leibnizA R,
      add_right_inj]
    exact CommMonoid.mul_comm ⁅x, a⁆ b
  )


variable (R A L) in
/-- The anchor of a given LieRinehart algebra `L` over `A` interpreted as a Lie-Rinehart morphism to
the module of derivations of `A`.
-/
def anchor [LieRing L] [Module A L] [LieAlgebra R L] [IsScalarTower R A L]
    [LieRingModule L A] [LieModule R L A] [LieRinehartAlgebra R A L] :
    L →ₗ⁅AlgHom.id R A⁆ (Derivation R A A) :=
  { toFun := derivOf R
    map_add' := fun _ _ ↦ by ext a; simp
    map_smul' := fun _ _ ↦ by ext a; simp [LieRinehartAlgebra.left_linearity R]
    map_lie' := fun _ _ ↦ by ext a; simp [Derivation.commutator_apply]
    anchor_comp := by simp }

end LieRinehartAlgebra
