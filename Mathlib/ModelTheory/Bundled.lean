/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.ElementarySubstructures
import Mathlib.CategoryTheory.ConcreteCategory.Bundled

/-!
# Bundled First-Order Structures

This file bundles types together with their first-order structure.

## Main Definitions

- `FirstOrder.Language.Theory.ModelType` is the type of nonempty models of a particular theory.
- `FirstOrder.Language.equivSetoid` is the isomorphism equivalence relation on bundled structures.

## TODO

- Define category structures on bundled structures and models.
-/


universe u v w w' x

variable {L : FirstOrder.Language.{u, v}}

protected instance CategoryTheory.Bundled.structure {L : FirstOrder.Language.{u, v}}
    (M : CategoryTheory.Bundled.{w} L.Structure) : L.Structure M :=
  M.str

open FirstOrder Cardinal

namespace Equiv

variable (L) {M : Type w}
variable [L.Structure M] {N : Type w'} (g : M ≃ N)

/-- A type bundled with the structure induced by an equivalence. -/
@[simps]
def bundledInduced : CategoryTheory.Bundled.{w'} L.Structure :=
  ⟨N, g.inducedStructure⟩

/-- An equivalence of types as a first-order equivalence to the bundled structure on the codomain.
-/
@[simp]
def bundledInducedEquiv : M ≃[L] g.bundledInduced L :=
  g.inducedStructureEquiv

end Equiv

namespace FirstOrder

namespace Language

/-- The equivalence relation on bundled `L.Structure`s indicating that they are isomorphic. -/
instance equivSetoid : Setoid (CategoryTheory.Bundled L.Structure) where
  r M N := Nonempty (M ≃[L] N)
  iseqv :=
    ⟨fun M => ⟨Equiv.refl L M⟩, fun {_ _} => Nonempty.map Equiv.symm, fun {_ _} _ =>
      Nonempty.map2 fun MN NP => NP.comp MN⟩

variable (T : L.Theory)

namespace Theory

/-- The type of nonempty models of a first-order theory. -/
structure ModelType where
  /-- The underlying type for the models -/
  Carrier : Type w
  [struc : L.Structure Carrier]
  [is_model : T.Model Carrier]
  [nonempty' : Nonempty Carrier]

-- Porting note: In Lean4, other instances precedes `FirstOrder.Language.Theory.ModelType.struc`,
-- it's issues in `ModelTheory.Satisfiability`. So, we increase these priorities.
attribute [instance 2000] ModelType.struc ModelType.is_model ModelType.nonempty'

namespace ModelType

attribute [coe] ModelType.Carrier

instance instCoeSort : CoeSort T.ModelType (Type w) :=
  ⟨ModelType.Carrier⟩

/-- The object in the category of R-algebras associated to a type equipped with the appropriate
typeclasses. -/
def of (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M] : T.ModelType :=
  ⟨M⟩

@[simp]
theorem coe_of (M : Type w) [L.Structure M] [M ⊨ T] [Nonempty M] : (of T M : Type w) = M :=
  rfl

instance instNonempty (M : T.ModelType) : Nonempty M :=
  inferInstance

section Inhabited

attribute [local instance] Inhabited.trivialStructure

instance instInhabited : Inhabited (ModelType.{u, v, w} (∅ : L.Theory)) :=
  ⟨ModelType.of _ PUnit⟩

end Inhabited

variable {T}

/-- Maps a bundled model along a bijection. -/
def equivInduced {M : ModelType.{u, v, w} T} {N : Type w'} (e : M ≃ N) :
    ModelType.{u, v, w'} T where
  Carrier := N
  struc := e.inducedStructure
  is_model := @StrongHomClass.theory_model L M N _ e.inducedStructure T
    _ _ _ e.inducedStructureEquiv _
  nonempty' := e.symm.nonempty

instance of_small (M : Type w) [Nonempty M] [L.Structure M] [M ⊨ T] [h : Small.{w'} M] :
    Small.{w'} (ModelType.of T M) :=
  h

/-- Shrinks a small model to a particular universe. -/
noncomputable def shrink (M : ModelType.{u, v, w} T) [Small.{w'} M] : ModelType.{u, v, w'} T :=
  equivInduced (equivShrink M)

/-- Lifts a model to a particular universe. -/
def ulift (M : ModelType.{u, v, w} T) : ModelType.{u, v, max w w'} T :=
  equivInduced (Equiv.ulift.{w', w}.symm : M ≃ _)

/-- The reduct of any model of `φ.onTheory T` is a model of `T`. -/
@[simps]
def reduct {L' : Language} (φ : L →ᴸ L') (M : (φ.onTheory T).ModelType) : T.ModelType where
  Carrier := M
  struc := φ.reduct M
  nonempty' := M.nonempty'
  is_model := (@LHom.onTheory_model L L' M (φ.reduct M) _ φ _ T).1 M.is_model

/-- When `φ` is injective, `defaultExpansion` expands a model of `T` to a model of `φ.onTheory T`
  arbitrarily. -/
@[simps]
noncomputable def defaultExpansion {L' : Language} {φ : L →ᴸ L'} (h : φ.Injective)
    [∀ (n) (f : L'.Functions n), Decidable (f ∈ Set.range fun f : L.Functions n => φ.onFunction f)]
    [∀ (n) (r : L'.Relations n), Decidable (r ∈ Set.range fun r : L.Relations n => φ.onRelation r)]
    (M : T.ModelType) [Inhabited M] : (φ.onTheory T).ModelType where
  Carrier := M
  struc := φ.defaultExpansion M
  nonempty' := M.nonempty'
  is_model :=
    (@LHom.onTheory_model L L' M _ (φ.defaultExpansion M) φ (h.isExpansionOn_default M) T).2
      M.is_model

instance leftStructure {L' : Language} {T : (L.sum L').Theory} (M : T.ModelType) : L.Structure M :=
  (LHom.sumInl : L →ᴸ L.sum L').reduct M

instance rightStructure {L' : Language} {T : (L.sum L').Theory} (M : T.ModelType) :
    L'.Structure M :=
  (LHom.sumInr : L' →ᴸ L.sum L').reduct M

/-- A model of a theory is also a model of any subtheory. -/
@[simps]
def subtheoryModel (M : T.ModelType) {T' : L.Theory} (h : T' ⊆ T) : T'.ModelType where
  Carrier := M
  is_model := ⟨fun _φ hφ => realize_sentence_of_mem T (h hφ)⟩

instance subtheoryModel_models (M : T.ModelType) {T' : L.Theory} (h : T' ⊆ T) :
    M.subtheoryModel h ⊨ T :=
  M.is_model

end ModelType

variable {T}

/-- Bundles `M ⊨ T` as a `T.ModelType`. -/
def Model.bundled {M : Type w} [LM : L.Structure M] [ne : Nonempty M] (h : M ⊨ T) : T.ModelType :=
  @ModelType.of L T M LM h ne

@[simp]
theorem coe_of {M : Type w} [L.Structure M] [Nonempty M] (h : M ⊨ T) : (h.bundled : Type w) = M :=
  rfl

end Theory

/-- A structure that is elementarily equivalent to a model, bundled as a model. -/
def ElementarilyEquivalent.toModel {M : T.ModelType} {N : Type*} [LN : L.Structure N]
    (h : M ≅[L] N) : T.ModelType where
  Carrier := N
  struc := LN
  nonempty' := h.nonempty
  is_model := h.theory_model

/-- An elementary substructure of a bundled model as a bundled model. -/
def ElementarySubstructure.toModel {M : T.ModelType} (S : L.ElementarySubstructure M) :
    T.ModelType :=
  S.elementarilyEquivalent.symm.toModel T

instance ElementarySubstructure.toModel.instSmall {M : T.ModelType}
    (S : L.ElementarySubstructure M) [h : Small.{w, x} S] : Small.{w, x} (S.toModel T) :=
  h

end Language

end FirstOrder
