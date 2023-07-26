/-
Copyright (c) 2021 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.LinearAlgebra.Coevaluation
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.NumberTheory.AbelianLanglands.CommAlg
import Mathlib.RingTheory.FiniteType
noncomputable section

open CategoryTheory ModuleCat.monoidalCategory

open scoped Classical BigOperators

universe u

section Ring

variable (R : Type u) [CommRing R]

/-- Define `FGCommAlg` as the subtype of `ModuleCat.{u} R` of finitely generated modules. -/
def FGCommAlg :=
  FullSubcategory fun V : CommAlg.{u} R => Algebra.FiniteType R V

variable {R}

/-- A synonym for `M.obj.carrier`, which we can mark with `@[coe]`. -/
def FGCommAlg.carrier (M : FGCommAlg R) : Type u := M.obj.carrier

instance : CoeSort (FGCommAlg R) (Type u) :=
  ⟨FGCommAlg.carrier⟩

attribute [coe] FGCommAlg.carrier

@[simp] lemma obj_carrier (M : FGCommAlg R) : M.obj.carrier = M.carrier := rfl

instance (M : FGCommAlg R) : CommRing M := by
  change CommRing M.obj
  infer_instance

instance (M : FGCommAlg R) : Algebra R M := by
  change Algebra R M.obj
  infer_instance

instance : LargeCategory (FGCommAlg R) := by
  dsimp [FGCommAlg]
  infer_instance

instance {M N : FGCommAlg R} : AlgHomClass (M ⟶ N) R M N :=
  AlgHom.algHomClass

instance : ConcreteCategory (FGCommAlg R) := by
  dsimp [FGCommAlg]
  infer_instance

end Ring

namespace FGCommAlg

section Ring

variable (R : Type u) [CommRing R]

instance finiteType (V : FGCommAlg R) : Algebra.FiniteType R V :=
  V.property

instance : Inhabited (FGCommAlg R) :=
  ⟨⟨CommAlg.of R R, Algebra.FiniteType.self R⟩⟩

/-- Lift an unbundled finitely generated module to `FGCommAlg R`. -/
def of (V : Type u) [CommRing V] [Algebra R V] [Algebra.FiniteType R V] : FGCommAlg R :=
  ⟨CommAlg.of R V, by change Algebra.FiniteType R V; infer_instance⟩

instance : HasForget₂ (FGCommAlg.{u} R) (CommAlg.{u} R) := by
  dsimp [FGCommAlg]
  infer_instance

instance : Full (forget₂ (FGCommAlg R) (CommAlg.{u} R)) where
  preimage f := f

variable {R}
variable {M N : FGCommAlg R}
@[simp]
theorem id_apply (m : M) : (𝟙 M : M → M) m = m :=
  rfl

@[simp]
theorem coe_comp (f : M ⟶ N) (g : N ⟶ U) : (f ≫ g : M → U) = g ∘ f :=
  rfl

/-- Converts and isomorphism in the category `FGCommAlg R` to
a `LinearEquiv` between the underlying modules. -/
def isoToAlgEquiv {V W : FGCommAlg R} (i : V ≅ W) : V ≃ₐ[R] W :=
  ((forget₂ (FGCommAlg.{u} R) (CommAlg.{u} R)).mapIso i).toCommAlgEquiv

/-- Converts a `LinearEquiv` to an isomorphism in the category `FGCommAlg R`. -/
@[simps]
def _root_.AlgEquiv.toFGCommAlgIso
    {V W : Type u} [CommRing V] [Algebra R V] [Algebra.FiniteType R V]
    [CommRing W] [Algebra R W] [Algebra.FiniteType R W] (e : V ≃ₐ[R] W) :
    FGCommAlg.of R V ≅ FGCommAlg.of R W where
  hom := e.toAlgHom
  inv := e.symm.toAlgHom
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

instance restrictScalarsFG (R S A : Type u) [CommRing R] [CommRing S]
  [CommRing A] [Algebra R S] [Algebra S A] (hRS : Algebra.FiniteType R S)
  (hSA : Algebra.FiniteType S A) :
    Algebra.FiniteType R (RestrictScalars R S A) :=
  let _ : Algebra S (RestrictScalars R S A) := show Algebra S A by infer_instance
  Algebra.FiniteType.trans (B := RestrictScalars R S A) hRS hSA

end Ring
