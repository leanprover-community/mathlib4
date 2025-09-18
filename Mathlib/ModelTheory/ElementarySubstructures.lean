/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.ElementaryMaps

/-!
# Elementary Substructures

## Main Definitions

- A `FirstOrder.Language.ElementarySubstructure` is a substructure where the realization of each
  formula agrees with the realization in the larger model.

## Main Results

- The Tarski-Vaught Test for substructures:
  `FirstOrder.Language.Substructure.isElementary_of_exists` gives a simple criterion for a
  substructure to be elementary.
-/


open FirstOrder

namespace FirstOrder

namespace Language

open Structure

variable {L : Language} {M : Type*} [L.Structure M]

/-- A substructure is elementary when every formula applied to a tuple in the substructure
  agrees with its value in the overall structure. -/
def Substructure.IsElementary (S : L.Substructure M) : Prop :=
  ∀ ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n → S), φ.Realize (((↑) : _ → M) ∘ x) ↔ φ.Realize x

variable (L M)

/-- An elementary substructure is one in which every formula applied to a tuple in the substructure
  agrees with its value in the overall structure. -/
structure ElementarySubstructure where
  /-- The underlying substructure -/
  toSubstructure : L.Substructure M
  isElementary' : toSubstructure.IsElementary

variable {L M}

namespace ElementarySubstructure

attribute [coe] toSubstructure

instance instCoe : Coe (L.ElementarySubstructure M) (L.Substructure M) :=
  ⟨ElementarySubstructure.toSubstructure⟩

instance instSetLike : SetLike (L.ElementarySubstructure M) M :=
  ⟨fun x => x.toSubstructure.carrier, fun ⟨⟨s, hs1⟩, hs2⟩ ⟨⟨t, ht1⟩, _⟩ _ => by
    congr⟩

instance inducedStructure (S : L.ElementarySubstructure M) : L.Structure S :=
  Substructure.inducedStructure

@[simp]
theorem isElementary (S : L.ElementarySubstructure M) : (S : L.Substructure M).IsElementary :=
  S.isElementary'

/-- The natural embedding of an `L.Substructure` of `M` into `M`. -/
def subtype (S : L.ElementarySubstructure M) : S ↪ₑ[L] M where
  toFun := (↑)
  map_formula' := S.isElementary

@[simp]
theorem subtype_apply {S : L.ElementarySubstructure M} {x : S} : subtype S x = x :=
  rfl

theorem subtype_injective (S : L.ElementarySubstructure M) : Function.Injective (subtype S) :=
  Subtype.coe_injective

@[simp]
theorem coe_subtype (S : L.ElementarySubstructure M) : ⇑S.subtype = Subtype.val :=
  rfl

/-- The substructure `M` of the structure `M` is elementary. -/
instance instTop : Top (L.ElementarySubstructure M) :=
  ⟨⟨⊤, fun _ _ _ => Substructure.realize_formula_top.symm⟩⟩

instance instInhabited : Inhabited (L.ElementarySubstructure M) :=
  ⟨⊤⟩

@[simp]
theorem mem_top (x : M) : x ∈ (⊤ : L.ElementarySubstructure M) :=
  Set.mem_univ x

@[simp]
theorem coe_top : ((⊤ : L.ElementarySubstructure M) : Set M) = Set.univ :=
  rfl

@[simp]
theorem realize_sentence (S : L.ElementarySubstructure M) (φ : L.Sentence) : S ⊨ φ ↔ M ⊨ φ :=
  S.subtype.map_sentence φ

@[simp]
theorem theory_model_iff (S : L.ElementarySubstructure M) (T : L.Theory) : S ⊨ T ↔ M ⊨ T := by
  simp only [Theory.model_iff, realize_sentence]

instance theory_model {T : L.Theory} [h : M ⊨ T] {S : L.ElementarySubstructure M} : S ⊨ T :=
  (theory_model_iff S T).2 h

instance instNonempty [Nonempty M] {S : L.ElementarySubstructure M} : Nonempty S :=
  (model_nonemptyTheory_iff L).1 inferInstance

theorem elementarilyEquivalent (S : L.ElementarySubstructure M) : S ≅[L] M :=
  S.subtype.elementarilyEquivalent

end ElementarySubstructure

namespace Substructure

/-- The Tarski-Vaught test for elementarity of a substructure. -/
theorem isElementary_of_exists (S : L.Substructure M)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → S) (a : M),
        φ.Realize default (Fin.snoc ((↑) ∘ x) a : _ → M) →
          ∃ b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) b : _ → M)) :
    S.IsElementary := fun _ => S.subtype.isElementary_of_exists htv

/-- Bundles a substructure satisfying the Tarski-Vaught test as an elementary substructure. -/
@[simps]
def toElementarySubstructure (S : L.Substructure M)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → S) (a : M),
        φ.Realize default (Fin.snoc ((↑) ∘ x) a : _ → M) →
          ∃ b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) b : _ → M)) :
    L.ElementarySubstructure M :=
  ⟨S, S.isElementary_of_exists htv⟩

end Substructure

end Language

end FirstOrder
