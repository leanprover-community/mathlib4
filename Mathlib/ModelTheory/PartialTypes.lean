/-
Copyright (c) 2026 Zikang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zikang Yu
-/
module

public import Mathlib.ModelTheory.Satisfiability

/-!
# Partial Types

This file defines partial types over a first-order theory, and over a parameter set in a
structure, as satisfiable sets of formulas.

## Main Definitions

- `FirstOrder.Language.Theory.PartialType`: a partial type over a theory `T` in variables `α`.
- `FirstOrder.Language.Theory.PartialTypeOver`: a partial type over a parameter set `A` in a
  structure `M`.

## Main Results

- `FirstOrder.Language.Theory.partialType_iff_finitelyRealizable`: a set of formulas is a partial
  type over `T` if and only if every finite subset is realized in a model of `T`.
- `FirstOrder.Language.Theory.PartialType.partialType_completeTheory_iff_finitelyRealizable`:
  over the complete theory of a structure `M`, finite realizability is equivalent to realizability
  in `M`.
- `FirstOrder.Language.Theory.PartialType.partialTypeOver_mono`: a partial type over a parameter
  set `A` can be reinterpreted over a larger parameter set `B`.
- `FirstOrder.Language.Theory.PartialType.partialTypeOver_iff_realizedIn_elementaryExtension`:
  a partial type over `A` is consistent if and only if it is realized in a model of the elementary
  diagram of the ambient structure.

## Implementation Notes

- A partial type is implemented as a `Set` of formulas together with satisfiability of the theory
  obtained by adjoining the corresponding `equivSentence`s in the language with constants.
- This theory-level presentation is chosen to stay parallel to `CompleteType`, which is also
  implemented using consistent theories in the expanded language rather than directly as sets of
  formulas.

## TODO

- Connect `T.PartialType α` and `T.CompleteType α`, for instance by formalizing how a partial type
  extends to a complete type.
-/

@[expose] public section

universe u v u' w w'

open Set

namespace FirstOrder

namespace Language

namespace Theory

variable {L : Language.{u, v}} (T : L.Theory) (α : Type w)

/-- The theory obtained from `T` by adjoining a set of formulas in variables `α`, viewed as
sentences in the language with constants for `α`. -/
def withSet {α} (S : Set (L.Formula α)) : L[[α]].Theory :=
  ((L.lhomWithConstants α).onTheory T ∪ Formula.equivSentence '' S)

/-- A partial type over `T` in variables `α` is a set of formulas consistent with `T`. -/
structure PartialType where
  /-- The underlying set of formulas. -/
  toSet : Set (L.Formula α)
  /-- Consistency with `T`, packaged as satisfiability in the language with constants for `α`. -/
  isSatisfiable' :
    (T.withSet toSet).IsSatisfiable

variable {T α}

/-- Partial types over a parameter set `A` in a structure `M`, implemented as partial types over
the complete `L[[A]]`-theory of `M`. -/
abbrev PartialTypeOver {M : Type u'} [L.Structure M] (A : Set M) (α : Type w) :=
  (L[[A]].completeTheory M).PartialType α

namespace PartialType

attribute [coe] PartialType.toSet

/-- Construct a partial type from a set of formulas via consistency. -/
def ofSet (S : Set (L.Formula α)) (hS : (T.withSet S).IsSatisfiable) :
    T.PartialType α :=
  ⟨S, hS⟩

@[simp]
theorem toSet_ofSet (S : Set (L.Formula α)) (hS : (T.withSet S).IsSatisfiable) :
    (ofSet S hS).toSet = S :=
  rfl

instance : SetLike (T.PartialType α) (L.Formula α) :=
  ⟨fun p => p.toSet, fun p q h => by
    cases p
    cases q
    congr⟩

@[simp]
theorem coe_ofSet (S : Set (L.Formula α))
    (hS : (T.withSet S).IsSatisfiable) :
    ((ofSet S hS : T.PartialType α) : Set (L.Formula α)) = S :=
  rfl

instance : PartialOrder (T.PartialType α) :=
  .ofSetLike (T.PartialType α) (L.Formula α)

/-- The theory associated to a partial type. -/
def toTheory (p : T.PartialType α) : L[[α]].Theory :=
  T.withSet p.toSet

theorem isSatisfiable (p : T.PartialType α) : p.toTheory.IsSatisfiable := by
  simpa [toTheory] using p.isSatisfiable'

theorem subset_toTheory (p : T.PartialType α) :
    (L.lhomWithConstants α).onTheory T ⊆ p.toTheory := by
  intro φ hφ
  exact Or.inl hφ

/-- The reduct to `L` of a model of `p.toTheory`, viewed as a model of `T`. -/
def reductModelType (p : T.PartialType α) (M : p.toTheory.ModelType) : T.ModelType :=
  (M.subtheoryModel p.subset_toTheory).reduct (L.lhomWithConstants α)

@[simp]
theorem coe_reductModelType (p : T.PartialType α) (M : p.toTheory.ModelType) :
    (p.reductModelType M : Type _) = M :=
  rfl

theorem mem_toTheory_of_mem (p : T.PartialType α) {φ : L.Formula α} (h : φ ∈ p) :
    Formula.equivSentence φ ∈ p.toTheory := by
  exact Or.inr ⟨φ, h, rfl⟩

/-- A tuple realizes a partial type if it realizes every formula in it. -/
def RealizedBy {M : Type w'} [L.Structure M] (p : T.PartialType α) (v : α → M) : Prop :=
  ∀ φ ∈ p, φ.Realize v

/-- A partial type is realized in a structure if some tuple realizes it. -/
def IsRealizedIn (p : T.PartialType α) (M : Type w') [L.Structure M] [M ⊨ T] [Nonempty M] :
    Prop :=
  ∃ v : α → M, p.RealizedBy v

/-- Every model of `p.toTheory` canonically realizes `p` after forgetting the added constants. -/
theorem isRealizedIn_reductModelType (p : T.PartialType α) (M : p.toTheory.ModelType) :
    p.IsRealizedIn (p.reductModelType M) := by
  refine ⟨fun a ↦ (L.con a : M), ?_⟩
  intro φ hφ
  have hφ' : M ⊨ Formula.equivSentence φ :=
    M.is_model.realize_of_mem _ (p.mem_toTheory_of_mem hφ)
  letI : (L.lhomWithConstants α).IsExpansionOn M := LHom.isExpansionOn_reduct _ _
  exact (Formula.realize_equivSentence M φ).1 hφ'

theorem exists_modelType_isRealizedIn (p : T.PartialType α) :
    ∃ M : Theory.ModelType.{u, v, max u v w} T, p.IsRealizedIn M := by
  obtain ⟨M⟩ := p.isSatisfiable
  exact ⟨p.reductModelType M, p.isRealizedIn_reductModelType M⟩

/-- Compactness for partial types: a set of formulas extends to a partial type over `T` if and
only if every finite subset is realized in some model of `T`. -/
theorem partialType_iff_finitelyRealizable
    (S : Set (L.Formula α)) :
    ((T.withSet S).IsSatisfiable) ↔
      ∀ s : Finset (L.Formula α), (↑s : Set (L.Formula α)) ⊆ S →
        ∃ M : Theory.ModelType.{u, v, max u v w} T,
          ∃ v : α → M, ∀ φ ∈ s, φ.Realize v := by
  constructor <;> intro h
  · let p := PartialType.ofSet S h
    obtain ⟨M⟩ := h
    intro s hs
    exists (p.reductModelType M)
    obtain ⟨v,hv⟩ := p.isRealizedIn_reductModelType M
    aesop
  · rw [isSatisfiable_iff_isFinitelySatisfiable]
    intro T0 hT0
    classical
    let s : Finset (L.Formula α) :=
      (T0.map (Formula.equivSentence).symm.toEmbedding).filter fun φ => φ ∈ S
    have hs : (↑s : Set (L.Formula α)) ⊆ S := by
      intro φ hφ
      simp only [Finset.coe_filter, Finset.mem_map_equiv, _root_.Equiv.symm_symm, mem_setOf_eq,
        s] at hφ
      exact hφ.2
    obtain ⟨M, v, hv⟩ := h s hs
    letI : (constantsOn α).Structure M := constantsOn.structure v
    have hM : M ⊨ (L.lhomWithConstants α).onTheory T := by
      simp only [LHom.onTheory_model]
      infer_instance
    haveI : M ⊨ (T0 : L[[α]].Theory) := by
      simp only [model_iff, SetLike.mem_coe]
      intro φ hφ
      rcases hT0 hφ with hφT | hφS
      · exact hM.realize_of_mem _ hφT
      · obtain ⟨ψ, hψS, rfl⟩ := hφS
        have hψ : ψ ∈ s := by
          simpa [s, hψS] using hφ
        exact
          (Formula.realize_equivSentence_symm M (Formula.equivSentence ψ) v).1
            (by simpa using hv ψ hψ)
    exact ⟨ModelType.of (T0 : L[[α]].Theory) M⟩

variable {M : Type u'} [L.Structure M] [Nonempty M]

theorem partialType_completeTheory_iff_finitelyRealizable
    (S : Set (L.Formula α)) :
    (((L.completeTheory M).withSet S).IsSatisfiable) ↔
      ∀ s : Finset (L.Formula α), (↑s : Set (L.Formula α)) ⊆ S →
        ∃ v : α → M, ∀ φ ∈ s, φ.Realize v := by
  classical
  constructor
  · intro h s hs
    obtain ⟨N, v, hv⟩ := (partialType_iff_finitelyRealizable S).1 h s hs
    let ψ : L.Formula α := Formula.iInf fun φ : s => (φ : L.Formula α)
    have hψN : ψ.Realize v := by
      simp only [Formula.realize_iInf, Subtype.forall, ψ]
      aesop
    have hψexN : ψ.exClosure.Realize N := by
      letI : (constantsOn α).Structure N := constantsOn.structure v
      exact Formula.realize_exClosure_of_realize_equivSentence
        ((Formula.realize_equivSentence N ψ).2 hψN)
    have hψexM : ψ.exClosure.Realize M :=
      ((L.realize_iff_of_model_completeTheory M N ψ.exClosure).1 hψexN)
    obtain ⟨vM, hvM⟩ :=
      Formula.exists_realize_equivSentence_of_realize_exClosure hψexM
    have hψM : ψ.Realize vM := by
      letI : (constantsOn α).Structure M := constantsOn.structure vM
      simpa using (Formula.realize_equivSentence M ψ).1 hvM
    exists vM
    aesop
  · intro h
    rw [partialType_iff_finitelyRealizable S]
    intro s hs
    obtain ⟨v, hv⟩ := h s hs
    letI : (constantsOn α).Structure M := constantsOn.structure v
    have hModel :
        M ⊨ (L.lhomWithConstants α).onTheory (L.completeTheory M) ∪
          Formula.equivSentence '' (↑s : Set (L.Formula α)) := by
      simp only [Theory.model_iff]
      intro φ hφ
      rcases hφ with hφT | hφS
      · exact (((LHom.onTheory_model _ _).2 inferInstance).realize_of_mem _ hφT)
      · rcases hφS with ⟨ψ, hψ, rfl⟩
        exact (Formula.realize_equivSentence M ψ).2 (hv ψ hψ)
    haveI :
        M ⊨ (L.lhomWithConstants α).onTheory (L.completeTheory M) ∪
          Formula.equivSentence '' (↑s : Set (L.Formula α)) :=
      hModel
    have hSat :
        (((L.lhomWithConstants α).onTheory (L.completeTheory M) ∪
            Formula.equivSentence '' (↑s : Set (L.Formula α))).IsSatisfiable) :=
      Theory.Model.isSatisfiable M
    exact
      (partialType_iff_finitelyRealizable (↑s : Set (L.Formula α))).1 hSat s fun _ hφ => hφ

variable {β γ : Type*}

omit [L.Structure M] [Nonempty M] in
/-- Reinterpret a set of formulas by mapping the parameter sort along `g`. -/
def mapSet (g : β → γ) (S : Set (L[[β]].Formula α)) : Set (L[[γ]].Formula α) :=
  (L.lhomWithConstantsMap g).onFormula '' S

omit [L.Structure M] [Nonempty M] in
@[simp]
theorem mem_mapSet (g : β → γ) {S : Set (L[[β]].Formula α)} {φ : L[[γ]].Formula α} :
    φ ∈ mapSet g S ↔ ∃ ψ ∈ S, (L.lhomWithConstantsMap g).onFormula ψ = φ :=
  Iff.rfl

omit [L.Structure M] in
/-- Mapping parameters along `g` preserves being a partial type over the complete theory of `M`,
provided the induced language map is an expansion on `M`. -/
theorem partialType_completeTheory_map [L[[β]].Structure M] [L[[γ]].Structure M]
    (g : β → γ) [hg : (L.lhomWithConstantsMap g).IsExpansionOn M]
    {S : Set (L[[β]].Formula α)}
    (hS : (((L[[β]].completeTheory M).withSet S).IsSatisfiable)) :
    (((L[[γ]].completeTheory M).withSet (mapSet g S)).IsSatisfiable) := by
  rw [partialType_completeTheory_iff_finitelyRealizable] at hS ⊢
  intro s hs
  classical
  let hs' : ∀ φ : s, ∃ ψ ∈ S, (L.lhomWithConstantsMap g).onFormula ψ = φ.1 := by
    intro φ
    simpa [mapSet] using hs (by simp)
  let preim : s → L[[β]].Formula α := fun φ => Classical.choose (hs' φ)
  have hpreim_mem : ∀ φ : s, preim φ ∈ S := by
    intro φ
    exact (Classical.choose_spec (hs' φ)).1
  have hpreim_eq : ∀ φ : s, (L.lhomWithConstantsMap g).onFormula (preim φ) = φ.1 := by
    intro φ
    exact (Classical.choose_spec (hs' φ)).2
  let t : Finset (L[[β]].Formula α) := s.attach.image preim
  have ht : (↑t : Set (L[[β]].Formula α)) ⊆ S := by
    intro ψ hψ
    change ψ ∈ s.attach.image preim at hψ
    rcases Finset.mem_image.mp hψ with ⟨φ, -, rfl⟩
    exact hpreim_mem φ
  obtain ⟨v, hv⟩ := hS t ht
  refine ⟨v, ?_⟩
  intro φ hφ
  have hpreim_mem_t : preim ⟨φ, hφ⟩ ∈ t := by
    change preim ⟨φ, hφ⟩ ∈ s.attach.image preim
    exact Finset.mem_image_of_mem preim (by simp)
  have hrealize_preim : (preim ⟨φ, hφ⟩).Realize v := hv _ hpreim_mem_t
  have : ((L.lhomWithConstantsMap g).onFormula (preim ⟨φ, hφ⟩)).Realize v :=
    (LHom.realize_onFormula (L.lhomWithConstantsMap g) _).2 hrealize_preim
  simpa [hpreim_eq ⟨φ, hφ⟩] using this

variable {A : Set M}

/-- Over the complete theory of a structure `M`, a set of formulas with parameters from `A`
defines a partial type if and only if every finite subset is realized in `M` itself. -/
theorem partialTypeOver_iff_finitelyRealizable
    (S : Set (L[[A]].Formula α)) :
    (((L[[A]].completeTheory M).withSet S).IsSatisfiable) ↔
      ∀ s : Finset (L[[A]].Formula α), (↑s : Set (L[[A]].Formula α)) ⊆ S →
        ∃ v : α → M,
          ∀ φ ∈ s, φ.Realize v := by
  simpa using
    (partialType_completeTheory_iff_finitelyRealizable S)

variable {B : Set M}

/-- Reinterpret a set of formulas with parameters from `A` as a set of formulas with parameters
from `B` along the inclusion. -/
def liftSet (hAB : A ⊆ B) (S : Set (L[[A]].Formula α)) : Set (L[[B]].Formula α) :=
  mapSet (Set.inclusion hAB) S

omit [L.Structure M] [Nonempty M] in
@[simp]
theorem mem_liftSet (hAB : A ⊆ B) {S : Set (L[[A]].Formula α)}
    {φ : L[[B]].Formula α} :
    φ ∈ liftSet hAB S ↔
      ∃ ψ ∈ S, (L.lhomWithConstantsMap (Set.inclusion hAB)).onFormula ψ = φ :=
  mem_mapSet (Set.inclusion hAB)

/-- A partial type over `A` stays a partial type over any larger parameter set `B`. -/
theorem partialTypeOver_mono (hAB : A ⊆ B) {S : Set (L[[A]].Formula α)}
    (hS : (((L[[A]].completeTheory M).withSet S).IsSatisfiable)) :
    (((L[[B]].completeTheory M).withSet (liftSet hAB S)).IsSatisfiable) := by
  simpa [liftSet] using
    (partialType_completeTheory_map (M := M) (g := Set.inclusion hAB) (S := S) hS)

/-- Lift a partial type over `A` to a partial type over the larger parameter set `B`. -/
def liftParams (hAB : A ⊆ B) (p : PartialTypeOver (L := L) A α) :
   PartialTypeOver (L := L) B α :=
  ofSet
    (liftSet hAB (p : Set (L[[A]].Formula α)))
    (partialTypeOver_mono (S := (p : Set (L[[A]].Formula α))) hAB p.isSatisfiable')

@[simp]
theorem coe_liftParams (hAB : A ⊆ B) (p : PartialTypeOver (L := L) A α) :
    ((liftParams hAB p : (L[[B]].completeTheory M).PartialType α) :
      Set (L[[B]].Formula α)) =
      liftSet hAB (p : Set (L[[A]].Formula α)) :=
  by rw [liftParams, coe_ofSet]

/-- A set of formulas with parameters from `A` is a partial type over `M` exactly when, after
reinterpreting those parameters as constants from `M`, it is realized in a model of the elementary
diagram of `M`. -/
theorem partialTypeOver_iff_realizedIn_elementaryExtension
    (S : Set (L[[A]].Formula α)) :
    (((L[[A]].completeTheory M).withSet S).IsSatisfiable) ↔
      ∃ N : Theory.ModelType.{max u u', v, max (max (max u u') v) w} (L.elementaryDiagram M),
        ∃ v : α → N,
          ∀ φ ∈ S,
            ((L.lhomWithConstantsMap ((↑) : A → M)).onFormula φ).Realize v := by
  classical
  constructor
  · intro hS
    let S' : Set (L[[M]].Formula α) := mapSet ((↑) : A → M) S
    haveI : (LHom.constantsOnMap ((↑) : A → M)).IsExpansionOn M :=
      constantsOnMap_isExpansionOn rfl
    haveI : (L.lhomWithConstantsMap ((↑) : A → M)).IsExpansionOn M :=
      LHom.sumMap_isExpansionOn _ _ _
    have hS' : (((L.elementaryDiagram M).withSet S').IsSatisfiable) := by
      change (((L[[M]].completeTheory M).withSet S').IsSatisfiable)
      simpa [S'] using
        (partialType_completeTheory_map ((↑) : A → M) hS)
    let p : (L.elementaryDiagram M).PartialType α := ofSet S' hS'
    obtain ⟨N, v, hv⟩ := exists_modelType_isRealizedIn p
    refine ⟨N, v, ?_⟩
    intro φ hφ
    exact hv _ (by
      change (L.lhomWithConstantsMap ((↑) : A → M)).onFormula φ ∈ S'
      exact ⟨φ, hφ, rfl⟩)
  · rintro ⟨N,v,h⟩
    rw [partialTypeOver_iff_finitelyRealizable]
    intro s hs
    let ψ : L[[A]].Formula α := Formula.iInf fun φ : s => (φ : L[[A]].Formula α)
    let ψ' : L[[M]].Formula α := (L.lhomWithConstantsMap ((↑) : A → M)).onFormula ψ
    letI : L[[↑A]].Structure ↑N :=
      (L.lhomWithConstantsMap ((↑) : A → M)).reduct ↑N
    haveI : (L.lhomWithConstantsMap ((↑) : A → M)).IsExpansionOn ↑N :=
      LHom.isExpansionOn_reduct (L.lhomWithConstantsMap ((↑) : A → M)) N
    have : ψ'.Realize v := by
      simp only [LHom.realize_onFormula, Formula.realize_iInf, Subtype.forall, ψ', ψ]
      intro φ hφ
      specialize h φ (mem_of_subset_of_mem hs hφ)
      simpa [ψ', ψ] using h
    let ψ'' : L[[M]].Sentence := ψ'.exClosure
    have hψ'' : ψ''.Realize N := by
      simp only [Formula.realize_exClosure, ψ'']
      exists v ∘ (↑)
      exact (BoundedFormula.realize_restrictFreeVar'
        (s := (ψ'.freeVarFinset : Set α)) Set.Subset.rfl (v := v)).2 this
    haveI : (L.lhomWithConstants M).IsExpansionOn ↑N :=
      LHom.isExpansionOn_reduct (L.lhomWithConstants M) N
    rw [realize_iff_of_model_completeTheory M N] at hψ''
    rw [Formula.realize_exClosure] at hψ''
    obtain ⟨w, hw⟩ := hψ''
    let vM : α → M := fun a =>
      if hmem : a ∈ ψ'.freeVarFinset then w ⟨a, hmem⟩ else Classical.choice inferInstance
    have hwEq : vM ∘ (↑) = w := by aesop
    haveI : (LHom.constantsOnMap ((↑) : A → M)).IsExpansionOn M :=
        constantsOnMap_isExpansionOn rfl
    haveI : (L.lhomWithConstantsMap ((↑) : A → M)).IsExpansionOn M :=
      LHom.sumMap_isExpansionOn _ _ _
    exists vM
    suffices hψ' : ψ'.Realize vM by
      simpa [ψ', ψ] using hψ'
    exact (BoundedFormula.realize_restrictFreeVar vM (congrFun (id (Eq.symm hwEq)))).mp hw

end PartialType

end Theory

end Language

end FirstOrder
