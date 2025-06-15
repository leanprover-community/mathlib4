/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The category of finitely generated modules over a ring is essentially small

This file proves that `FGModuleCat R`, the category of finitely generated modules over a ring `R`,
is essentially small, by providing an explicit small model. However, for applications, it is
recommended to use the standard `CategoryTheory.SmallModel (FGModuleCat R)` instead.

-/

universe v w u

variable (R : Type u) [CommRing R]

open CategoryTheory

/-- A (category-theoretically) small version of `FGModuleCat R`. This is used to prove that
`FGModuleCat R` is essentially small. For actual use, it might be recommended to use the canonical
`CategoryTheory.SmallModel` instead of this construction. -/
structure FGModuleRepr : Type u where
  /-- The natural number `n` that defines the module as a quotient of `Fin n → R` (i.e. `R^n`). -/
  (n : ℕ)
  /-- The kernel of the surjective map from `Fin n → R` (i.e. `R^n`) to the module represented. -/
  (S : Submodule R (Fin n → R))

namespace FGModuleRepr

variable (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]

variable {R} in
/-- The finite module represented by an object of the type `FGModuleRepr R`, which is the quotient
of `Fin n → R` (i.e. $$R^n$$) by the submodule `S` provided. -/
def repr (x : FGModuleRepr R) : Type u :=
  _ ⧸ x.S

instance : CoeSort (FGModuleRepr R) (Type u) :=
  ⟨repr⟩

instance (x : FGModuleRepr R) : AddCommGroup x := by
  unfold repr; infer_instance

instance (x : FGModuleRepr R) : Module R x := by
  unfold repr; infer_instance

instance (x : FGModuleRepr R) : Module.Finite R x := by
  unfold repr; infer_instance

/-- A non-canonical representation of a finite module (as a quotient of $$R^n$$). -/
noncomputable def ofFinite : FGModuleRepr R where
  n := (Module.Finite.exists_fin_quot_equiv R M).choose
  S := (Module.Finite.exists_fin_quot_equiv R M).choose_spec.choose

/-- The non-canonical representation `ofFinite` of a finite module is actually isomorphic to
the given module. -/
noncomputable def ofFiniteEquiv : ofFinite R M ≃ₗ[R] M :=
  Classical.choice (Module.Finite.exists_fin_quot_equiv R M).choose_spec.choose_spec

instance : Category (FGModuleRepr R) :=
  InducedCategory.category fun x : FGModuleRepr R ↦ FGModuleCat.of R x

instance : SmallCategory (FGModuleRepr R) where

/-- The canonical embedding of this small category to the canonical (large) category
`FGModuleCat R`. -/
def embed : FGModuleRepr.{u} R ⥤ FGModuleCat.{max u v} R :=
  inducedFunctor _ ⋙ FGModuleCat.ulift R

instance : (embed R).IsEquivalence where
  faithful := (fullyFaithfulInducedFunctor _).faithful.comp _ _
  full := (fullyFaithfulInducedFunctor _).full.comp _ _
  essSurj := ⟨fun M ↦ ⟨ofFinite R M,
    ⟨(ULift.moduleEquiv.trans <| ofFiniteEquiv R M).toFGModuleCatIso⟩⟩⟩

end FGModuleRepr

instance : EssentiallySmall.{u} (FGModuleCat.{v} R) :=
  letI : EssentiallySmall.{u} (FGModuleCat.{max u v} R) :=
    ⟨_, _, ⟨(FGModuleRepr.embed R).asEquivalence.symm⟩⟩
  essentiallySmall_of_fully_faithful (FGModuleCat.ulift.{v, max u v} R)

open FGModuleRepr in
-- There is probably a proof using `embedIsEquivalence` or `EssentiallySmall`.
instance : (FGModuleCat.ulift.{max u v, w} R).IsEquivalence where
  essSurj := ⟨fun M ↦ ⟨(embed R).obj (ofFinite R M),
    ⟨(ULift.moduleEquiv.trans <| ULift.moduleEquiv.trans <| ofFiniteEquiv R M).toFGModuleCatIso⟩⟩⟩
