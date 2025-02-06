/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.ElementarySubstructures
import Mathlib.CategoryTheory.ConcreteCategory.Bundled
import Mathlib.CategoryTheory.ConcreteCategory.Basic

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

open CategoryTheory

variable {M N O : Bundled.{w} L.Structure}

instance : Category (Bundled.{w} L.Structure) where
  Hom := (· ↪[L] ·)
  id _ := Embedding.refl _ _
  comp f g := g.comp f

instance instConcreteCategory : ConcreteCategory (Bundled.{w} L.Structure) (· ↪[L] ·) where
  hom f := f
  ofHom f := f

@[simp]
theorem ConcreteCategory.comp_def (f : M ↪[L] N) (g : N ↪[L] O) :
    f ≫ g = instConcreteCategory.ofHom (g.comp f) := rfl

@[simp]
theorem ConcreteCategory.ofHom_def (f : M ↪[L] N) : instConcreteCategory.ofHom f = f := rfl

@[simp]
theorem ConcreteCategory.hom_def (f : M ⟶ N) : instConcreteCategory.hom f = f := rfl

@[simp]
theorem ConcreteCategory.id_def : 𝟙 M = Embedding.refl L M := rfl

/-- Construct a categorical isomorphism between two bundled `L.Structure`s from an equivalence. -/
def Iso.mk (f : M ≃[L] N) : M ≅ N where
  hom := f.toEmbedding
  inv := f.symm.toEmbedding
  hom_inv_id := by simp only [ConcreteCategory.comp_def, Equiv.symm_comp_self_toEmbedding,
    ConcreteCategory.ofHom_def, ConcreteCategory.id_def]

theorem Iso.bijective (f : M ≅ N) : Function.Bijective f.hom := by
  refine ⟨Embedding.injective f.hom, Function.RightInverse.surjective (g := f.inv) ?_⟩
  intro x
  change (f.inv ≫ f.hom) x = x
  simp only [Iso.inv_hom_id, ConcreteCategory.id_apply]

/-- Construct an equivalence between two bundled `L.Structure`s from a categorical isomorphism. -/
def Equiv.ofIso (f : M ≅ N) : M ≃[L] N where
  toFun := f.hom
  invFun := f.inv
  left_inv := by intro x; change (f.hom ≫ f.inv) x = x; simp only [Iso.hom_inv_id,
    ConcreteCategory.id_def, ConcreteCategory.hom_def, Embedding.refl_apply]
  right_inv := by intro x; change (f.inv ≫ f.hom) x = x; simp only [Iso.inv_hom_id,
    ConcreteCategory.id_def, ConcreteCategory.hom_def, Embedding.refl_apply]
  map_fun' := f.hom.map_fun'
  map_rel' := f.hom.map_rel'

@[simp]
theorem Equiv.ofIso_mk (f : M ≃[L] N) : Equiv.ofIso (Iso.mk f) = f := rfl

@[simp]
theorem Iso.mk_ofIso (f : M ≅ N) : Iso.mk (Equiv.ofIso f) = f := rfl

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

variable {M N P : CategoryTheory.Bundled.{w} L.Structure}

namespace Embedding

@[simp]
theorem eqToHom_comp (h : M = N) (h' : N = P) :
    (eqToHom h').comp (eqToHom h) = eqToHom (h.trans h') := eqToHom_trans h h'

@[simp]
theorem eqToHom_comp_apply (h : M = N) (h' : N = P) (m : M) :
    eqToHom h' (eqToHom h m) = eqToHom (h.trans h') m := by
  cases h
  rfl

end Embedding

namespace Equiv

/-- Equivalence between equal structures. -/
def ofEq (h : M = N) : M ≃[L] N := ofIso (eqToIso h)

@[simp]
theorem ofEq_refl : ofEq (Eq.refl M) = refl L M := rfl

@[simp]
theorem ofEq_comp (h : M = N) (h' : N = P) :
    (ofEq h').comp (ofEq h) = ofEq (h.trans h') := by
  cases h
  rfl

@[simp]
theorem ofEq_comp_apply (h : M = N) (h' : N = P) (m : M) :
    ofEq h' (ofEq h m) = ofEq (h.trans h') m := by
  cases h
  rfl

@[simp]
theorem ofEq_toEmbedding (h : M = N) :
    (ofEq h).toEmbedding = eqToHom h := rfl

end Equiv

end Language

end FirstOrder
