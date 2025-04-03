/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.ModelTheory.ElementaryMaps

/-!
# Elementary Substructures

## Main Definitions
* A `FirstOrder.Language.ElementarySubstructure` is a substructure where the realization of each
  formula agrees with the realization in the larger model.

## Main Results
* The Tarski-Vaught Test for substructures:
  `FirstOrder.Language.Substructure.isElementary_of_exists` gives a simple criterion for a
  substructure to be elementary.
 -/


open FirstOrder

namespace FirstOrder

namespace Language

open Structure

variable {L : Language} {M : Type*} {N : Type*} {P : Type*} {Q : Type*}
variable [L.Structure M] [L.Structure N] [L.Structure P] [L.Structure Q]

/-- A substructure is elementary when every formula applied to a tuple in the substructure
  agrees with its value in the overall structure. -/
def Substructure.IsElementary (S : L.Substructure M) : Prop :=
  ∀ ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n → S), φ.Realize (((↑) : _ → M) ∘ x) ↔ φ.Realize x
#align first_order.language.substructure.is_elementary FirstOrder.Language.Substructure.IsElementary

variable (L M)

/-- An elementary substructure is one in which every formula applied to a tuple in the substructure
  agrees with its value in the overall structure. -/
structure ElementarySubstructure where
  toSubstructure : L.Substructure M
  isElementary' : toSubstructure.IsElementary
#align first_order.language.elementary_substructure FirstOrder.Language.ElementarySubstructure
#align first_order.language.elementary_substructure.to_substructure FirstOrder.Language.ElementarySubstructure.toSubstructure
#align first_order.language.elementary_substructure.is_elementary' FirstOrder.Language.ElementarySubstructure.isElementary'

variable {L M}

namespace ElementarySubstructure

attribute [coe] toSubstructure

instance instCoe : Coe (L.ElementarySubstructure M) (L.Substructure M) :=
  ⟨ElementarySubstructure.toSubstructure⟩
#align first_order.language.elementary_substructure.first_order.language.substructure.has_coe FirstOrder.Language.ElementarySubstructure.instCoe

instance instSetLike : SetLike (L.ElementarySubstructure M) M :=
  ⟨fun x => x.toSubstructure.carrier, fun ⟨⟨s, hs1⟩, hs2⟩ ⟨⟨t, ht1⟩, _⟩ _ => by
    congr⟩
#align first_order.language.elementary_substructure.set_like FirstOrder.Language.ElementarySubstructure.instSetLike

instance inducedStructure (S : L.ElementarySubstructure M) : L.Structure S :=
  Substructure.inducedStructure
set_option linter.uppercaseLean3 false in
#align first_order.language.elementary_substructure.induced_Structure FirstOrder.Language.ElementarySubstructure.inducedStructure

@[simp]
theorem isElementary (S : L.ElementarySubstructure M) : (S : L.Substructure M).IsElementary :=
  S.isElementary'
#align first_order.language.elementary_substructure.is_elementary FirstOrder.Language.ElementarySubstructure.isElementary

/-- The natural embedding of an `L.Substructure` of `M` into `M`. -/
def subtype (S : L.ElementarySubstructure M) : S ↪ₑ[L] M where
  toFun := (↑)
  map_formula' := S.isElementary
#align first_order.language.elementary_substructure.subtype FirstOrder.Language.ElementarySubstructure.subtype

@[simp]
theorem coeSubtype {S : L.ElementarySubstructure M} : ⇑S.subtype = ((↑) : S → M) :=
  rfl
#align first_order.language.elementary_substructure.coe_subtype FirstOrder.Language.ElementarySubstructure.coeSubtype

/-- The substructure `M` of the structure `M` is elementary. -/
instance instTop : Top (L.ElementarySubstructure M) :=
  ⟨⟨⊤, fun _ _ _ => Substructure.realize_formula_top.symm⟩⟩
#align first_order.language.elementary_substructure.has_top FirstOrder.Language.ElementarySubstructure.instTop

instance instInhabited : Inhabited (L.ElementarySubstructure M) :=
  ⟨⊤⟩
#align first_order.language.elementary_substructure.inhabited FirstOrder.Language.ElementarySubstructure.instInhabited

@[simp]
theorem mem_top (x : M) : x ∈ (⊤ : L.ElementarySubstructure M) :=
  Set.mem_univ x
#align first_order.language.elementary_substructure.mem_top FirstOrder.Language.ElementarySubstructure.mem_top

@[simp]
theorem coe_top : ((⊤ : L.ElementarySubstructure M) : Set M) = Set.univ :=
  rfl
#align first_order.language.elementary_substructure.coe_top FirstOrder.Language.ElementarySubstructure.coe_top

@[simp]
theorem realize_sentence (S : L.ElementarySubstructure M) (φ : L.Sentence) : S ⊨ φ ↔ M ⊨ φ :=
  S.subtype.map_sentence φ
#align first_order.language.elementary_substructure.realize_sentence FirstOrder.Language.ElementarySubstructure.realize_sentence

@[simp]
theorem theory_model_iff (S : L.ElementarySubstructure M) (T : L.Theory) : S ⊨ T ↔ M ⊨ T := by
  simp only [Theory.model_iff, realize_sentence]
set_option linter.uppercaseLean3 false in
#align first_order.language.elementary_substructure.Theory_model_iff FirstOrder.Language.ElementarySubstructure.theory_model_iff

instance theory_model {T : L.Theory} [h : M ⊨ T] {S : L.ElementarySubstructure M} : S ⊨ T :=
  (theory_model_iff S T).2 h
set_option linter.uppercaseLean3 false in
#align first_order.language.elementary_substructure.Theory_model FirstOrder.Language.ElementarySubstructure.theory_model

instance instNonempty [Nonempty M] {S : L.ElementarySubstructure M} : Nonempty S :=
  (model_nonemptyTheory_iff L).1 inferInstance
#align first_order.language.elementary_substructure.nonempty FirstOrder.Language.ElementarySubstructure.instNonempty

theorem elementarilyEquivalent (S : L.ElementarySubstructure M) : S ≅[L] M :=
  S.subtype.elementarilyEquivalent
#align first_order.language.elementary_substructure.elementarily_equivalent FirstOrder.Language.ElementarySubstructure.elementarilyEquivalent

end ElementarySubstructure

namespace Substructure

/-- The Tarski-Vaught test for elementarity of a substructure. -/
theorem isElementary_of_exists (S : L.Substructure M)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → S) (a : M),
        φ.Realize default (Fin.snoc ((↑) ∘ x) a : _ → M) →
          ∃ b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) b : _ → M)) :
    S.IsElementary := fun _ => S.subtype.isElementary_of_exists htv
#align first_order.language.substructure.is_elementary_of_exists FirstOrder.Language.Substructure.isElementary_of_exists

/-- Bundles a substructure satisfying the Tarski-Vaught test as an elementary substructure. -/
@[simps]
def toElementarySubstructure (S : L.Substructure M)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → S) (a : M),
        φ.Realize default (Fin.snoc ((↑) ∘ x) a : _ → M) →
          ∃ b : S, φ.Realize default (Fin.snoc ((↑) ∘ x) b : _ → M)) :
    L.ElementarySubstructure M :=
  ⟨S, S.isElementary_of_exists htv⟩
#align first_order.language.substructure.to_elementary_substructure FirstOrder.Language.Substructure.toElementarySubstructure

end Substructure

end Language

end FirstOrder
