/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Fintype.Basic
import Mathlib.ModelTheory.Substructures

#align_import model_theory.elementary_maps from "leanprover-community/mathlib"@"d11893b411025250c8e61ff2f12ccbd7ee35ab15"

/-!
# Elementary Maps Between First-Order Structures

## Main Definitions
* A `FirstOrder.Language.ElementaryEmbedding` is an embedding that commutes with the
  realizations of formulas.
* The `FirstOrder.Language.elementaryDiagram` of a structure is the set of all sentences with
  parameters that the structure satisfies.
* `FirstOrder.Language.ElementaryEmbedding.ofModelsElementaryDiagram` is the canonical
elementary embedding of any structure into a model of its elementary diagram.

## Main Results
* The Tarski-Vaught Test for embeddings: `FirstOrder.Language.Embedding.isElementary_of_exists`
gives a simple criterion for an embedding to be elementary.
 -/


open FirstOrder

namespace FirstOrder

namespace Language

open Structure

variable (L : Language) (M : Type*) (N : Type*) {P : Type*} {Q : Type*}
variable [L.Structure M] [L.Structure N] [L.Structure P] [L.Structure Q]

/-- An elementary embedding of first-order structures is an embedding that commutes with the
  realizations of formulas. -/
structure ElementaryEmbedding where
  toFun : M → N
  -- Porting note:
  -- The autoparam here used to be `obviously`. We would like to replace it with `aesop`
  -- but that isn't currently sufficient.
  -- See https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Aesop.20and.20cases
  -- If that can be improved, we should change this to `by aesop` and remove the proofs below.
  map_formula' :
    ∀ ⦃n⦄ (φ : L.Formula (Fin n)) (x : Fin n → M), φ.Realize (toFun ∘ x) ↔ φ.Realize x := by
    intros; trivial
#align first_order.language.elementary_embedding FirstOrder.Language.ElementaryEmbedding
#align first_order.language.elementary_embedding.to_fun FirstOrder.Language.ElementaryEmbedding.toFun
#align first_order.language.elementary_embedding.map_formula' FirstOrder.Language.ElementaryEmbedding.map_formula'

@[inherit_doc FirstOrder.Language.ElementaryEmbedding]
scoped[FirstOrder] notation:25 A " ↪ₑ[" L "] " B => FirstOrder.Language.ElementaryEmbedding L A B

variable {L} {M} {N}

namespace ElementaryEmbedding

attribute [coe] toFun

instance instFunLike : FunLike (M ↪ₑ[L] N) M N where
  coe f := f.toFun
  coe_injective' f g h := by
    cases f
    cases g
    simp only [ElementaryEmbedding.mk.injEq]
    ext x
    exact Function.funext_iff.1 h x
#align first_order.language.elementary_embedding.fun_like FirstOrder.Language.ElementaryEmbedding.instFunLike

instance : CoeFun (M ↪ₑ[L] N) fun _ => M → N :=
  DFunLike.hasCoeToFun

@[simp]
theorem map_boundedFormula (f : M ↪ₑ[L] N) {α : Type*} {n : ℕ} (φ : L.BoundedFormula α n)
    (v : α → M) (xs : Fin n → M) : φ.Realize (f ∘ v) (f ∘ xs) ↔ φ.Realize v xs := by
  classical
    rw [← BoundedFormula.realize_restrictFreeVar Set.Subset.rfl, Set.inclusion_eq_id, iff_eq_eq]
    have h :=
      f.map_formula' ((φ.restrictFreeVar id).toFormula.relabel (Fintype.equivFin _))
        (Sum.elim (v ∘ (↑)) xs ∘ (Fintype.equivFin _).symm)
    simp only [Formula.realize_relabel, BoundedFormula.realize_toFormula, iff_eq_eq] at h
    rw [← Function.comp.assoc _ _ (Fintype.equivFin _).symm,
      Function.comp.assoc _ (Fintype.equivFin _).symm (Fintype.equivFin _),
      _root_.Equiv.symm_comp_self, Function.comp_id, Function.comp.assoc, Sum.elim_comp_inl,
      Function.comp.assoc _ _ Sum.inr, Sum.elim_comp_inr, ← Function.comp.assoc] at h
    refine h.trans ?_
    erw [Function.comp.assoc _ _ (Fintype.equivFin _), _root_.Equiv.symm_comp_self,
      Function.comp_id, Sum.elim_comp_inl, Sum.elim_comp_inr (v ∘ Subtype.val) xs,
      ← Set.inclusion_eq_id (s := (BoundedFormula.freeVarFinset φ : Set α)) Set.Subset.rfl,
      BoundedFormula.realize_restrictFreeVar Set.Subset.rfl]
#align first_order.language.elementary_embedding.map_bounded_formula FirstOrder.Language.ElementaryEmbedding.map_boundedFormula

@[simp]
theorem map_formula (f : M ↪ₑ[L] N) {α : Type*} (φ : L.Formula α) (x : α → M) :
    φ.Realize (f ∘ x) ↔ φ.Realize x := by
  rw [Formula.Realize, Formula.Realize, ← f.map_boundedFormula, Unique.eq_default (f ∘ default)]
#align first_order.language.elementary_embedding.map_formula FirstOrder.Language.ElementaryEmbedding.map_formula

theorem map_sentence (f : M ↪ₑ[L] N) (φ : L.Sentence) : M ⊨ φ ↔ N ⊨ φ := by
  rw [Sentence.Realize, Sentence.Realize, ← f.map_formula, Unique.eq_default (f ∘ default)]
#align first_order.language.elementary_embedding.map_sentence FirstOrder.Language.ElementaryEmbedding.map_sentence

theorem theory_model_iff (f : M ↪ₑ[L] N) (T : L.Theory) : M ⊨ T ↔ N ⊨ T := by
  simp only [Theory.model_iff, f.map_sentence]
set_option linter.uppercaseLean3 false in
#align first_order.language.elementary_embedding.Theory_model_iff FirstOrder.Language.ElementaryEmbedding.theory_model_iff

theorem elementarilyEquivalent (f : M ↪ₑ[L] N) : M ≅[L] N :=
  elementarilyEquivalent_iff.2 f.map_sentence
#align first_order.language.elementary_embedding.elementarily_equivalent FirstOrder.Language.ElementaryEmbedding.elementarilyEquivalent

@[simp]
theorem injective (φ : M ↪ₑ[L] N) : Function.Injective φ := by
  intro x y
  have h :=
    φ.map_formula ((var 0).equal (var 1) : L.Formula (Fin 2)) fun i => if i = 0 then x else y
  rw [Formula.realize_equal, Formula.realize_equal] at h
  simp only [Nat.one_ne_zero, Term.realize, Fin.one_eq_zero_iff, if_true, eq_self_iff_true,
    Function.comp_apply, if_false] at h
  exact h.1
#align first_order.language.elementary_embedding.injective FirstOrder.Language.ElementaryEmbedding.injective

instance embeddingLike : EmbeddingLike (M ↪ₑ[L] N) M N :=
  { show FunLike (M ↪ₑ[L] N) M N from inferInstance with injective' := injective }
#align first_order.language.elementary_embedding.embedding_like FirstOrder.Language.ElementaryEmbedding.embeddingLike

@[simp]
theorem map_fun (φ : M ↪ₑ[L] N) {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    φ (funMap f x) = funMap f (φ ∘ x) := by
  have h := φ.map_formula (Formula.graph f) (Fin.cons (funMap f x) x)
  rw [Formula.realize_graph, Fin.comp_cons, Formula.realize_graph] at h
  rw [eq_comm, h]
#align first_order.language.elementary_embedding.map_fun FirstOrder.Language.ElementaryEmbedding.map_fun

@[simp]
theorem map_rel (φ : M ↪ₑ[L] N) {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    RelMap r (φ ∘ x) ↔ RelMap r x :=
  haveI h := φ.map_formula (r.formula var) x
  h
#align first_order.language.elementary_embedding.map_rel FirstOrder.Language.ElementaryEmbedding.map_rel

instance strongHomClass : StrongHomClass L (M ↪ₑ[L] N) M N where
  map_fun := map_fun
  map_rel := map_rel
#align first_order.language.elementary_embedding.strong_hom_class FirstOrder.Language.ElementaryEmbedding.strongHomClass

@[simp]
theorem map_constants (φ : M ↪ₑ[L] N) (c : L.Constants) : φ c = c :=
  HomClass.map_constants φ c
#align first_order.language.elementary_embedding.map_constants FirstOrder.Language.ElementaryEmbedding.map_constants

/-- An elementary embedding is also a first-order embedding. -/
def toEmbedding (f : M ↪ₑ[L] N) : M ↪[L] N where
  toFun := f
  inj' := f.injective
  map_fun' {_} f x := by aesop
  map_rel' {_} R x := by aesop
#align first_order.language.elementary_embedding.to_embedding FirstOrder.Language.ElementaryEmbedding.toEmbedding

/-- An elementary embedding is also a first-order homomorphism. -/
def toHom (f : M ↪ₑ[L] N) : M →[L] N where
  toFun := f
  map_fun' {_} f x := by aesop
  map_rel' {_} R x := by aesop
#align first_order.language.elementary_embedding.to_hom FirstOrder.Language.ElementaryEmbedding.toHom

@[simp]
theorem toEmbedding_toHom (f : M ↪ₑ[L] N) : f.toEmbedding.toHom = f.toHom :=
  rfl
#align first_order.language.elementary_embedding.to_embedding_to_hom FirstOrder.Language.ElementaryEmbedding.toEmbedding_toHom

@[simp]
theorem coe_toHom {f : M ↪ₑ[L] N} : (f.toHom : M → N) = (f : M → N) :=
  rfl
#align first_order.language.elementary_embedding.coe_to_hom FirstOrder.Language.ElementaryEmbedding.coe_toHom

@[simp]
theorem coe_toEmbedding (f : M ↪ₑ[L] N) : (f.toEmbedding : M → N) = (f : M → N) :=
  rfl
#align first_order.language.elementary_embedding.coe_to_embedding FirstOrder.Language.ElementaryEmbedding.coe_toEmbedding

theorem coe_injective : @Function.Injective (M ↪ₑ[L] N) (M → N) (↑) :=
  DFunLike.coe_injective
#align first_order.language.elementary_embedding.coe_injective FirstOrder.Language.ElementaryEmbedding.coe_injective

@[ext]
theorem ext ⦃f g : M ↪ₑ[L] N⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h
#align first_order.language.elementary_embedding.ext FirstOrder.Language.ElementaryEmbedding.ext

theorem ext_iff {f g : M ↪ₑ[L] N} : f = g ↔ ∀ x, f x = g x :=
  DFunLike.ext_iff
#align first_order.language.elementary_embedding.ext_iff FirstOrder.Language.ElementaryEmbedding.ext_iff

variable (L) (M)

/-- The identity elementary embedding from a structure to itself -/
@[refl]
def refl : M ↪ₑ[L] M where toFun := id
#align first_order.language.elementary_embedding.refl FirstOrder.Language.ElementaryEmbedding.refl

variable {L} {M}

instance : Inhabited (M ↪ₑ[L] M) :=
  ⟨refl L M⟩

@[simp]
theorem refl_apply (x : M) : refl L M x = x :=
  rfl
#align first_order.language.elementary_embedding.refl_apply FirstOrder.Language.ElementaryEmbedding.refl_apply

/-- Composition of elementary embeddings -/
@[trans]
def comp (hnp : N ↪ₑ[L] P) (hmn : M ↪ₑ[L] N) : M ↪ₑ[L] P where
  toFun := hnp ∘ hmn
  map_formula' n φ x := by
    cases' hnp with _ hhnp
    cases' hmn with _ hhmn
    erw [hhnp, hhmn]
#align first_order.language.elementary_embedding.comp FirstOrder.Language.ElementaryEmbedding.comp

@[simp]
theorem comp_apply (g : N ↪ₑ[L] P) (f : M ↪ₑ[L] N) (x : M) : g.comp f x = g (f x) :=
  rfl
#align first_order.language.elementary_embedding.comp_apply FirstOrder.Language.ElementaryEmbedding.comp_apply

/-- Composition of elementary embeddings is associative. -/
theorem comp_assoc (f : M ↪ₑ[L] N) (g : N ↪ₑ[L] P) (h : P ↪ₑ[L] Q) :
    (h.comp g).comp f = h.comp (g.comp f) :=
  rfl
#align first_order.language.elementary_embedding.comp_assoc FirstOrder.Language.ElementaryEmbedding.comp_assoc

end ElementaryEmbedding

variable (L) (M)

/-- The elementary diagram of an `L`-structure is the set of all sentences with parameters it
  satisfies. -/
abbrev elementaryDiagram : L[[M]].Theory :=
  L[[M]].completeTheory M
#align first_order.language.elementary_diagram FirstOrder.Language.elementaryDiagram

/-- The canonical elementary embedding of an `L`-structure into any model of its elementary diagram
-/
@[simps]
def ElementaryEmbedding.ofModelsElementaryDiagram (N : Type*) [L.Structure N] [L[[M]].Structure N]
    [(lhomWithConstants L M).IsExpansionOn N] [N ⊨ L.elementaryDiagram M] : M ↪ₑ[L] N :=
  ⟨((↑) : L[[M]].Constants → N) ∘ Sum.inr, fun n φ x => by
    refine
      _root_.trans ?_
        ((realize_iff_of_model_completeTheory M N
              (((L.lhomWithConstants M).onBoundedFormula φ).subst
                  (Constants.term ∘ Sum.inr ∘ x)).alls).trans
          ?_)
    · simp_rw [Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_subst,
        LHom.realize_onBoundedFormula, Formula.Realize, Unique.forall_iff, Function.comp,
        Term.realize_constants]
    · simp_rw [Sentence.Realize, BoundedFormula.realize_alls, BoundedFormula.realize_subst,
        LHom.realize_onBoundedFormula, Formula.Realize, Unique.forall_iff]
      rfl⟩
#align first_order.language.elementary_embedding.of_models_elementary_diagram FirstOrder.Language.ElementaryEmbedding.ofModelsElementaryDiagram

variable {L M}

namespace Embedding

/-- The **Tarski-Vaught test** for elementarity of an embedding. -/
theorem isElementary_of_exists (f : M ↪[L] N)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → M) (a : N),
        φ.Realize default (Fin.snoc (f ∘ x) a : _ → N) →
          ∃ b : M, φ.Realize default (Fin.snoc (f ∘ x) (f b) : _ → N)) :
    ∀ {n} (φ : L.Formula (Fin n)) (x : Fin n → M), φ.Realize (f ∘ x) ↔ φ.Realize x := by
  suffices h : ∀ (n : ℕ) (φ : L.BoundedFormula Empty n) (xs : Fin n → M),
      φ.Realize (f ∘ default) (f ∘ xs) ↔ φ.Realize default xs by
    intro n φ x
    exact φ.realize_relabel_sum_inr.symm.trans (_root_.trans (h n _ _) φ.realize_relabel_sum_inr)
  refine fun n φ => φ.recOn ?_ ?_ ?_ ?_ ?_
  · exact fun {_} _ => Iff.rfl
  · intros
    simp [BoundedFormula.Realize, ← Sum.comp_elim, Embedding.realize_term]
  · intros
    simp only [BoundedFormula.Realize, ← Sum.comp_elim, realize_term]
    erw [map_rel f]
  · intro _ _ _ ih1 ih2 _
    simp [ih1, ih2]
  · intro n φ ih xs
    simp only [BoundedFormula.realize_all]
    refine ⟨fun h a => ?_, ?_⟩
    · rw [← ih, Fin.comp_snoc]
      exact h (f a)
    · contrapose!
      rintro ⟨a, ha⟩
      obtain ⟨b, hb⟩ := htv n φ.not xs a (by
          rw [BoundedFormula.realize_not, ← Unique.eq_default (f ∘ default)]
          exact ha)
      refine ⟨b, fun h => hb (Eq.mp ?_ ((ih _).2 h))⟩
      rw [Unique.eq_default (f ∘ default), Fin.comp_snoc]
#align first_order.language.embedding.is_elementary_of_exists FirstOrder.Language.Embedding.isElementary_of_exists

/-- Bundles an embedding satisfying the Tarski-Vaught test as an elementary embedding. -/
@[simps]
def toElementaryEmbedding (f : M ↪[L] N)
    (htv :
      ∀ (n : ℕ) (φ : L.BoundedFormula Empty (n + 1)) (x : Fin n → M) (a : N),
        φ.Realize default (Fin.snoc (f ∘ x) a : _ → N) →
          ∃ b : M, φ.Realize default (Fin.snoc (f ∘ x) (f b) : _ → N)) :
    M ↪ₑ[L] N :=
  ⟨f, fun _ => f.isElementary_of_exists htv⟩
#align first_order.language.embedding.to_elementary_embedding FirstOrder.Language.Embedding.toElementaryEmbedding

end Embedding

namespace Equiv

/-- A first-order equivalence is also an elementary embedding. -/
def toElementaryEmbedding (f : M ≃[L] N) : M ↪ₑ[L] N where
  toFun := f
  map_formula' n φ x := by aesop
#align first_order.language.equiv.to_elementary_embedding FirstOrder.Language.Equiv.toElementaryEmbedding

@[simp]
theorem toElementaryEmbedding_toEmbedding (f : M ≃[L] N) :
    f.toElementaryEmbedding.toEmbedding = f.toEmbedding :=
  rfl
#align first_order.language.equiv.to_elementary_embedding_to_embedding FirstOrder.Language.Equiv.toElementaryEmbedding_toEmbedding

@[simp]
theorem coe_toElementaryEmbedding (f : M ≃[L] N) :
    (f.toElementaryEmbedding : M → N) = (f : M → N) :=
  rfl
#align first_order.language.equiv.coe_to_elementary_embedding FirstOrder.Language.Equiv.coe_toElementaryEmbedding

end Equiv

@[simp]
theorem realize_term_substructure {α : Type*} {S : L.Substructure M} (v : α → S) (t : L.Term α) :
    t.realize ((↑) ∘ v) = (↑(t.realize v) : M) :=
  S.subtype.realize_term t
#align first_order.language.realize_term_substructure FirstOrder.Language.realize_term_substructure

end Language

end FirstOrder
