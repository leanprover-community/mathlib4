/-
Copyright (c) 2026 Yağız Kaan Aydoğdu, Yusuf Demir, Salih Erdem Koçak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yağız Kaan Aydoğdu, Yusuf Demir, Salih Erdem Koçak
-/
module

public import Mathlib.ModelTheory.Complexity
public import Mathlib.ModelTheory.Satisfiability
public import Mathlib.ModelTheory.ElementaryExtensionPair

/-!
# Quantifier Elimination

This file defines quantifier elimination for first-order theories and proves several standard
criteria for establishing it.

## Main Definitions

- `FirstOrder.Language.Theory.IsQFEquivalent` says that a formula is equivalent over a theory to a
  quantifier-free formula.
- `FirstOrder.Language.Theory.HasQuantifierElimination` says that every formula in finitely many
  free variables is equivalent over the theory to a quantifier-free formula.

## Main Results

- `FirstOrder.Language.Theory.isQFEquivalent_iff_realize_iff_of_embeddings` characterizes
  quantifier-free definability by invariance under embeddings from a common substructure. This
  corresponds to [Theorem 3.1.4][marker2002].
- `FirstOrder.Language.Theory.hasQuantifierElimination_iff_finite_isQFEquivalent` characterizes
  quantifier elimination by quantifier-free equivalence for every formula over a finite index type
  of variables.
- `FirstOrder.Language.Theory.hasQuantifierElimination_iff_ex_isQFEquivalent_of_isQF` characterizes
  quantifier elimination by elimination of one existential quantifier from quantifier-free
  formulas. This corresponds to [Theorem 3.1.5][marker2002].
- `FirstOrder.Language.Theory.hasQuantifierElimination_of_exists_realize_of_embeddings` is a
  witness-transfer criterion for quantifier elimination. This corresponds to
  [Theorem 3.1.6][marker2002].
- `FirstOrder.Language.Theory.hasQuantifierElimination_of_isElementaryExtensionPair` and
  `FirstOrder.Language.Theory.hasQuantifierElimination_of_isElementaryExtensionPairFG` prove
  quantifier elimination from the extension property appearing in
  [Theorem 7.11][vandendries_henson_2016] and from a finitely generated variant. The theorem
  `hasQuantifierElimination_of_isElementaryExtensionPairCardinalLTGenerated`
  gives the corresponding `< κ`-generated version.

## References

- [D. Marker, *Model Theory: An Introduction*][marker2002]
- [L. van den Dries and C. W. Henson, *Lecture Notes for Mathematics 571 Fall 2016 Model
  Theory*][vandendries_henson_2016]
-/

@[expose] public section

universe u v w u'

namespace FirstOrder

namespace Language

namespace Theory

open Structure
variable {L : Language.{u, v}}
variable {M : Type w} {N A : Type*} [L.Structure M] [L.Structure N] [L.Structure A]

/-- A formula is equivalent to a quantifier-free formula over a theory. -/
def IsQFEquivalent (T : L.Theory) {α : Type*} (φ : L.Formula α) : Prop :=
  ∃ ψ : L.Formula α, ψ.IsQF ∧ φ ⇔[T] ψ

/-- A theory has quantifier elimination if every formula is equivalent, over the theory, to a
quantifier-free formula. -/
def HasQuantifierElimination (T : L.Theory) : Prop :=
  ∀ {α : Type} (φ : L.Formula α), T.IsQFEquivalent φ

/-- Finite conjunction of a list of quantifier-free formulas bundled with an auxiliary property. -/
private def qfConj {α : Type*} {P : L.Formula α → Prop}
    (l : List {ψ : L.Formula α // ψ.IsQF ∧ P ψ}) : L.Formula α :=
  (l.map Subtype.val).foldr (· ⊓ ·) ⊤

/-- A finite conjunction of quantifier-free formulas is quantifier-free. -/
private theorem qfConj_isQF {α : Type*} {P : L.Formula α → Prop}
    (l : List {ψ : L.Formula α // ψ.IsQF ∧ P ψ}) :
    (qfConj (L := L) l).IsQF := by
  induction l with
  | nil => exact BoundedFormula.IsQF.top
  | cons ψ _ ih => simpa [qfConj] using ψ.2.1.inf ih

/-- Realizing a finite conjunction is the same as realizing every formula in the list. -/
private theorem realize_qfConj {α : Type*} {P : L.Formula α → Prop}
    (l : List {ψ : L.Formula α // ψ.IsQF ∧ P ψ}) {M : Type*} [L.Structure M]
    (v : α → M) (xs : Fin 0 → M) :
    BoundedFormula.Realize (qfConj (L := L) l) v xs ↔
      ∀ ψ ∈ l, BoundedFormula.Realize ψ.1 v xs := by
  simp [qfConj]

/-- To model a finite union of theories indexed by `Option Q`, it is enough to model the base
theory and the extra sentence for each `some q` occurring in the finite set. -/
private theorem model_iUnion_option_of_base_of_extra {α Q M : Type*} [L[[α]].Structure M]
    (U : Option Q → L[[α]].Theory) (base : L[[α]].Theory) (extra : Q → L[[α]].Sentence)
    (s : Finset (Option Q)) (hU_none : U none = base)
    (hU_some : ∀ q, U (some q) = base ∪ {extra q})
    (hbase : ∀ τ ∈ base, M ⊨ τ) (hextra : ∀ q, some q ∈ s → M ⊨ extra q) :
    M ⊨ ⋃ i ∈ s, U i := ⟨fun σ hσ => by
  simp only [Set.mem_iUnion] at hσ
  obtain ⟨i, hi, hσ⟩ := hσ
  cases i with
  | none =>
      rw [hU_none] at hσ
      exact hbase _ hσ
  | some q =>
      rw [hU_some] at hσ
      rcases hσ with hbase' | hq
      · exact hbase _ hbase'
      · rw [Set.mem_singleton_iff] at hq
        subst hq
        exact hextra q hi⟩

/-- Two terms over the generators `range v`, relabelled through a section `idx`, take equal values
at `w` iff they take equal values along the inclusion `range v → M`. This is the well-definedness
and injectivity engine of `exists_embedding_of_agree_qf`. -/
private theorem relabel_realize_eq_iff_of_agree_qf
    {α : Type*} {M N : Type*} [L.Structure M] [L.Structure N] {v : α → M} {w : α → N}
    (hQF : ∀ ψ : L.Formula α, ψ.IsQF → (ψ.Realize v ↔ ψ.Realize w))
    {idx : Set.range v → α} (hidx : ∀ x : Set.range v, v (idx x) = x)
    (t u : L.Term (Set.range v)) :
    (t.relabel idx).realize w = (u.relabel idx).realize w ↔
      t.realize ((↑) : Set.range v → M) = u.realize ((↑) : Set.range v → M) := by
  have hr : ∀ s : L.Term (Set.range v),
      (s.relabel idx).realize v = s.realize ((↑) : Set.range v → M) := fun s => by
    rw [Term.realize_relabel]
    congr 1 with x
    exact hidx x
  rw [← hr t, ← hr u]
  exact (Formula.realize_equal.symm.trans
    (Formula.realize_equal_iff_of_agree_qf hQF (t.relabel idx) (u.relabel idx)).symm).trans
    Formula.realize_equal

/-- Construct an embedding of the substructure generated by `range v` into `N` whose action on
the generators `v i` equals `w i`, given that `v` and `w` realize the same quantifier-free
formulas. -/
private theorem exists_embedding_of_agree_qf
    {α : Type*} {M N : Type*} [L.Structure M] [L.Structure N]
    (v : α → M) (w : α → N)
    (hQF : ∀ ψ : L.Formula α, ψ.IsQF → (ψ.Realize v ↔ ψ.Realize w)) :
    ∃ g : (Substructure.closure L (Set.range v) : L.Substructure M) ↪[L] N,
      ∀ i, g ⟨v i, Substructure.subset_closure ⟨i, rfl⟩⟩ = w i := by
  -- For each element of `range v`, choose an index `idx x` with `v (idx x) = x`.
  choose idx hidx using fun x : Set.range v => x.2
  -- Relabelling a term over `range v` through `idx` and realizing at `v` agrees with realizing it
  -- along the inclusion `range v → M`.
  have hterm_realize (t : L.Term (Set.range v)) :
      (t.relabel idx).realize v = t.realize ((↑) : Set.range v → M) := by
    rw [Term.realize_relabel]
    congr 1 with x
    exact hidx x
  -- Equal generators have equal images, by agreement on equality of the matching variables.
  have hvar : ∀ {i j : α}, v i = v j → w i = w j := fun {i j} hij => by
    have hv : (Term.equal (L := L) (Term.var i) (Term.var j)).Realize v := by
      simpa [Formula.realize_equal] using hij
    simpa [Formula.realize_equal] using (Formula.realize_equal_iff_of_agree_qf hQF _ _).mp hv
  let S : L.Substructure M := Substructure.closure L (Set.range v)
  -- Every element of `S` is the value of some term in the generators; pick one as `repr x`.
  choose repr hrepr using fun x : S =>
    (Substructure.mem_closure_iff_exists_term (L := L) (s := Set.range v) (x := (x : M))).mp x.2
  -- Send `x : S` to the value at `w` of its representing term; quantifier-free agreement
  -- (packaged as `relabel_realize_eq_iff_of_agree_qf`) makes this injective and a homomorphism.
  refine ⟨{
    toFun := fun x => ((repr x).relabel idx).realize w
    inj' := by
      intro x y hxy
      apply Subtype.ext
      simpa [hrepr x, hrepr y] using
        (relabel_realize_eq_iff_of_agree_qf hQF hidx (repr x) (repr y)).mp hxy
    map_fun' := by
      intro n f x
      have hfunc :
          (repr (Structure.funMap f x)).realize ((↑) : Set.range v → M) =
            (Term.func f fun i => repr (x i)).realize ((↑) : Set.range v → M) := by
        rw [hrepr (Structure.funMap f x)]
        simp only [Term.realize, hrepr]
        rfl
      simpa [Term.realize, Function.comp_def] using
        (relabel_realize_eq_iff_of_agree_qf hQF hidx _ _).mpr hfunc
    map_rel' := by
      intro n R x
      -- The substructure `RelMap` is definitionally the ambient one applied to coercions.
      change _ ↔ RelMap R fun i => ((x i : M))
      simpa [hterm_realize, hrepr, Function.comp_def] using
        (Formula.realize_rel_iff_of_agree_qf hQF R fun i => (repr (x i)).relabel idx).symm
  }, ?_⟩
  -- The generator `v i` has the same realization as the variable `xi`, so the embedding sends it
  -- to `w i`.
  intro i
  let xi : Set.range v := ⟨v i, ⟨i, rfl⟩⟩
  have hxi : (repr ⟨v i, Substructure.subset_closure ⟨i, rfl⟩⟩).realize
      ((↑) : Set.range v → M) = (Term.var (L := L) xi).realize ((↑) : Set.range v → M) := by
    simp [xi, hrepr]
  -- Unfold the application of the embedding literal definitionally.
  change ((repr ⟨v i, Substructure.subset_closure ⟨i, rfl⟩⟩).relabel idx).realize w = w i
  simpa [xi] using
    ((relabel_realize_eq_iff_of_agree_qf hQF hidx _ _).mpr hxi).trans (hvar (hidx xi))

/-- Existential form of `exists_embedding_of_agree_qf` bundling the substructure, the embedding,
and the inclusion `α → S` for `isQFEquivalent_iff_realize_iff_of_embeddings`. -/
private theorem exists_substructure_embedding_of_agree_qf
    {α : Type*} {M N : Type*} [L.Structure M] [L.Structure N]
    (v : α → M) (w : α → N)
    (hQF : ∀ ψ : L.Formula α, ψ.IsQF → (ψ.Realize v ↔ ψ.Realize w)) :
    ∃ S : L.Substructure M, ∃ g : S ↪[L] N, ∃ a : α → S,
      ((↑) ∘ a = v) ∧ g ∘ a = w := by
  obtain ⟨g, hg⟩ := exists_embedding_of_agree_qf v w hQF
  exact ⟨_, g, fun i => ⟨v i, Substructure.subset_closure ⟨i, rfl⟩⟩, rfl, funext hg⟩

/-- Henkin-style compactness core shared by the two model constructions below: given a "seed"
formula `extra` and a predicate `P` on quantifier-free formulas such that no finite conjunction of
quantifier-free `P`-formulas `θ` satisfies `extra ⟹[T] θ.not`, there is a model of `T` with
constants `v : α → K` realizing `extra` and every quantifier-free `P`-formula.

The hypothesis is the finite-consistency input to compactness: failing `extra ⟹[T] θ.not` means
some model of `T` realizes both `extra` and `θ`. -/
private theorem exists_model_realize_of_forall_not_imp_not
    {T : L.Theory} {α : Type u'} (P : L.Formula α → Prop) (extra : L.Formula α)
    (hkey : ∀ l : List {ψ : L.Formula α // ψ.IsQF ∧ P ψ}, ¬ (extra ⟹[T] (qfConj l).not)) :
    ∃ (K : Theory.ModelType.{u, v, max u v u'} T) (v : α → K),
      extra.Realize v ∧ ∀ q : {ψ : L.Formula α // ψ.IsQF ∧ P ψ}, q.1.Realize v := by
  -- Work in `L[[α]]` with a constant for each variable: the target theory is `T`, the sentence
  -- `extra`, and every quantifier-free `P`-formula; a model of it provides `v`.
  let base : L[[α]].Theory :=
    (L.lhomWithConstants α).onTheory T ∪ {Formula.equivSentence extra}
  let U : Option {ψ : L.Formula α // ψ.IsQF ∧ P ψ} → L[[α]].Theory
    | none => base
    | some q => base ∪ {Formula.equivSentence q.1}
  -- By compactness it suffices to satisfy every finite subset. An unsatisfiable finite subset `s`
  -- would give `extra ⟹[T] θ.not` for `θ` the conjunction of the formulas it mentions,
  -- contradicting `hkey`.
  have hsat : Theory.IsSatisfiable (⋃ i, U i) := by
    by_contra hsat
    rw [Theory.isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset] at hsat
    push Not at hsat
    rcases hsat with ⟨s, hs⟩
    let qfs : Finset {ψ : L.Formula α // ψ.IsQF ∧ P ψ} :=
      s.filterMap id (by intro a a' b ha ha'; simpa using ha.trans ha'.symm)
    let lqfs := qfs.toList
    apply hkey lqfs
    intro M v xs hextra
    rw [BoundedFormula.realize_not]
    intro hθ
    letI : (constantsOn α).Structure M := constantsOn.structure v
    have hθall : ∀ q ∈ lqfs, BoundedFormula.Realize q.1 v xs :=
      (realize_qfConj lqfs v xs).mp hθ
    have hbase : ∀ τ ∈ base, M ⊨ τ := by
      rintro τ (hT | hex)
      · exact ((LHom.onTheory_model _ _).mpr inferInstance).realize_of_mem _ hT
      · rw [Set.mem_singleton_iff] at hex
        subst hex
        exact (Formula.realize_equivSentence (M := M) extra).mpr
          ((Formula.boundedFormula_realize_eq_realize ..).mp hextra)
    have hmodel : M ⊨ ⋃ i ∈ s, U i := by
      refine model_iUnion_option_of_base_of_extra U base
        (fun q => Formula.equivSentence q.1) s rfl (fun _ => rfl) hbase ?_
      intro q hq
      refine (Formula.realize_equivSentence (M := M) q.1).mpr ?_
      have hqlist : q ∈ lqfs := Finset.mem_toList.mpr (by simpa [qfs] using hq)
      exact (Formula.boundedFormula_realize_eq_realize ..).mp (hθall q hqlist)
    exact hs (Theory.Model.isSatisfiable M)
  -- Reduce a model to an `L`-structure modelling `T` and read off its constants as `v`.
  obtain ⟨K⟩ := hsat
  letI : L.Structure K := (L.lhomWithConstants α).reduct K
  haveI : T.Model K := (LHom.onTheory_model _ _).mp <| K.is_model.mono fun _ hσ =>
    Set.mem_iUnion.mpr ⟨none, .inl hσ⟩
  haveI : (L.lhomWithConstants α).IsExpansionOn K := LHom.isExpansionOn_reduct _ _
  refine ⟨Theory.ModelType.of T K, fun i => (L.con i : K), ?_, fun q => ?_⟩
  · exact (Formula.realize_equivSentence (M := K) extra).mp
      (K.is_model.realize_of_mem _ (Set.mem_iUnion.mpr ⟨none, by simp [U, base]⟩))
  · exact (Formula.realize_equivSentence (M := K) q.1).mp
      (K.is_model.realize_of_mem _ (Set.mem_iUnion.mpr ⟨some q, by simp [U, base]⟩))

/-- Henkin-style construction: if `φ` is not equivalent over `T` to any quantifier-free formula,
there is a model of `T` containing constants `v0 : α → M1` that fail to realize `φ` yet realize
every quantifier-free consequence of `φ` over `T`. -/
private theorem exists_model_not_realize_with_qf_consequences
    {T : L.Theory} {α : Type u'} {φ : L.Formula α} (hqe : ¬ T.IsQFEquivalent φ) :
    ∃ (M1 : Theory.ModelType.{u, v, max u v u'} T) (v0 : α → M1), ¬ φ.Realize v0 ∧
      ∀ q : {ψ : L.Formula α // ψ.IsQF ∧ φ ⟹[T] ψ}, q.1.Realize v0 := by
  -- Apply the compactness core with seed `¬φ` and predicate "is a consequence of `φ`": a finite
  -- conjunction `θ` of consequences with `φ.not ⟹[T] θ.not`, i.e. `θ ⟹[T] φ`, would together with
  -- `φ ⟹[T] θ` make `θ` a quantifier-free equivalent of `φ`, contradicting `hqe`.
  obtain ⟨M1, v0, hnotφ, hcons⟩ :=
    exists_model_realize_of_forall_not_imp_not (fun ψ => φ ⟹[T] ψ) φ.not fun l h => by
      have hφθ : φ ⟹[T] qfConj l := fun M v xs hφ => by
        change BoundedFormula.Realize (qfConj l) v xs
        rw [realize_qfConj]
        exact fun q _ => q.2.2 M v xs hφ
      have hθφ : qfConj l ⟹[T] φ := fun M v xs hθ => by
        by_contra hφ
        exact BoundedFormula.realize_not.mp
          (h M v xs (BoundedFormula.realize_not.mpr hφ)) hθ
      exact hqe ⟨qfConj l, qfConj_isQF l, Theory.imp_antisymm hφθ hθφ⟩
  exact ⟨M1, v0, Formula.realize_not.mp hnotφ, hcons⟩

/-- Henkin-style construction: given constants `v0 : α → M1` in a model of `T` such that every
quantifier-free consequence of `φ` is realized at `v0`, there is a model `N1` of `T` with constants
`w : α → N1` realizing `φ` and agreeing with `v0` on every quantifier-free formula. -/
private theorem exists_model_realize_with_qf_realized_at
    {T : L.Theory} {α : Type u'} (φ : L.Formula α)
    {M1 : Type max u v u'} [L.Structure M1] [T.Model M1] [Nonempty M1] (v0 : α → M1)
    (hqfConseq : ∀ q : {ψ : L.Formula α // ψ.IsQF ∧ φ ⟹[T] ψ}, q.1.Realize v0) :
    ∃ (N1 : Theory.ModelType.{u, v, max u v u'} T) (w : α → N1),
      φ.Realize w ∧ ∀ ψ : L.Formula α, ψ.IsQF → (ψ.Realize v0 ↔ ψ.Realize w) := by
  -- Apply the compactness core with seed `φ` and predicate "is realized at `v0`": a finite
  -- conjunction `θ` of formulas realized at `v0` with `φ ⟹[T] θ.not` would make `θ.not` a
  -- quantifier-free consequence of `φ`, hence realized at `v0`, contradicting `θ.Realize v0`.
  obtain ⟨N1, w, hφw, hqfIncl⟩ :=
    exists_model_realize_of_forall_not_imp_not (fun ψ => ψ.Realize v0) φ fun l h => by
      have hθv0 : (qfConj l).Realize v0 := by
        change BoundedFormula.Realize (qfConj l) v0 default
        rw [realize_qfConj]
        exact fun q _ => q.2.2
      exact hqfConseq ⟨(qfConj l).not, (qfConj_isQF l).not, h⟩ hθv0
  -- Agreement on `ψ`: forward is the inclusion `hqfIncl`; the reverse applies it to `ψ.not`.
  refine ⟨N1, w, hφw, fun ψ hψ => ⟨fun hψv0 => hqfIncl ⟨ψ, hψ, hψv0⟩, fun hψw => ?_⟩⟩
  by_contra hψv0
  have hnot : (ψ.not).Realize w :=
    hqfIncl ⟨ψ.not, hψ.not, by simpa [Formula.realize_not] using hψv0⟩
  exact hnot hψw

/-- Forward direction of `isQFEquivalent_iff_realize_iff_of_embeddings`: a quantifier-free
equivalent of `φ` is preserved by embeddings, so `φ`'s realization on the image of a common
substructure agrees between any two models of `T`. -/
private theorem realize_iff_of_embeddings_of_isQFEquivalent
    {T : L.Theory} {α : Type u'} {φ : L.Formula α} (hφ : T.IsQFEquivalent φ)
    {M N A : Type (max u v u')} [L.Structure M] [L.Structure N] [L.Structure A]
    [T.Model M] [T.Model N] [Nonempty M] [Nonempty N]
    (f : A ↪[L] M) (g : A ↪[L] N) (a : α → A) :
    φ.Realize (f ∘ a) ↔ φ.Realize (g ∘ a) := by
  obtain ⟨ψ, hψ, hiff⟩ := hφ
  -- A quantifier-free `ψ` equivalent to `φ` is preserved by embeddings, so its realization depends
  -- only on the common substructure `A`, not on the model it embeds into.
  have hf : ψ.Realize (f ∘ a) ↔ ψ.Realize a := by
    simpa [Formula.Realize, Unique.eq_default (f ∘ default)] using
      hψ.realize_embedding (f := f) (v := a) (xs := default)
  have hg : ψ.Realize (g ∘ a) ↔ ψ.Realize a := by
    simpa [Formula.Realize, Unique.eq_default (g ∘ default)] using
      hψ.realize_embedding (f := g) (v := a) (xs := default)
  rw [hiff.realize_iff (M := M) (v := f ∘ a), hiff.realize_iff (M := N) (v := g ∘ a), hf, hg]

/-- Backward direction of `isQFEquivalent_iff_realize_iff_of_embeddings`: if `φ`'s realization is
invariant under any pair of embeddings from a common substructure into nonempty models of `T`,
then `φ` is quantifier-free equivalent over `T`. -/
private theorem isQFEquivalent_of_realize_iff_of_embeddings
    {T : L.Theory} {α : Type u'} {φ : L.Formula α}
    (hcommon : ∀ {M N A : Type (max u v u')} [L.Structure M] [L.Structure N] [L.Structure A]
      [T.Model M] [T.Model N] [Nonempty M] [Nonempty N]
      (f : A ↪[L] M) (g : A ↪[L] N) (a : α → A),
      φ.Realize (f ∘ a) ↔ φ.Realize (g ∘ a)) :
    T.IsQFEquivalent φ := by
  by_contra hqe
  -- Build a model where `φ` fails but every quantifier-free consequence holds, and a second model
  -- where `φ` holds and the quantifier-free type agrees with the first. The shared quantifier-free
  -- type yields a common substructure `S` embedding into both, so invariance forces `φ` at `v0`.
  obtain ⟨M1, v0, hnotφv0, hqfConseq⟩ := exists_model_not_realize_with_qf_consequences hqe
  obtain ⟨N1, w, hφw, hqfEq⟩ := exists_model_realize_with_qf_realized_at φ v0 hqfConseq
  obtain ⟨S, g, a, ha, hg⟩ := exists_substructure_embedding_of_agree_qf v0 w hqfEq
  have hsame := hcommon (M := M1.Carrier) (N := N1.Carrier) (A := S) S.subtype g a
  have hφga : φ.Realize (g ∘ a) := by simpa [hg] using hφw
  exact hnotφv0 (by simpa [ha] using hsame.mpr hφga)

/-- A formula is equivalent over `T` to a quantifier-free formula iff its truth is invariant under
pairs of embeddings from a common structure into nonempty models of `T`.

This corresponds to [Theorem 3.1.4][marker2002]. -/
theorem isQFEquivalent_iff_realize_iff_of_embeddings
    {T : L.Theory} {α : Type u'} (φ : L.Formula α) :
    T.IsQFEquivalent φ ↔
      (∀ {M N A : Type (max u v u')} [L.Structure M] [L.Structure N] [L.Structure A]
        [T.Model M] [T.Model N] [Nonempty M] [Nonempty N]
        (f : A ↪[L] M) (g : A ↪[L] N)
        (a : α → A), φ.Realize (f ∘ a) ↔ φ.Realize (g ∘ a)) := by
  refine ⟨fun hφ => ?_, isQFEquivalent_of_realize_iff_of_embeddings⟩
  intro _ _ _ _ _ _ _ _ _ _ f g a
  exact realize_iff_of_embeddings_of_isQFEquivalent hφ f g a

/-- Promote the single-bound-variable elimination hypothesis to any number of bound variables: if
existential closures of quantifier-free formulas over one bound variable are quantifier-free
equivalent over `T`, then so are existential closures of quantifier-free formulas with `n + 1`
bound variables, reduced to the last bound variable. -/
private theorem exists_qf_equiv_ex_of_isQF
    {T : L.Theory}
    (h :
      ∀ {α : Type u'} [Finite α] (θ : L.BoundedFormula α 1), θ.IsQF →
        ∃ ψ : L.Formula α, ψ.IsQF ∧ θ.ex ⇔[T] ψ)
    {α : Type u'} [Finite α] {n : ℕ} {θ : L.BoundedFormula α (n + 1)} (hθ : θ.IsQF) :
    ∃ ψ : L.BoundedFormula α n, ψ.IsQF ∧ θ.ex ⇔[T] ψ := by
  -- Keep the last of the `n + 1` bound variables as the single bound variable handled by `h`, and
  -- move the other `n` bound variables into the free index type `α ⊕ Fin n`.
  let toOne : α ⊕ Fin (n + 1) → (α ⊕ Fin n) ⊕ Fin 1 :=
    Sum.elim (fun i => Sum.inl (Sum.inl i))
      (Fin.lastCases (Sum.inr 0) fun i => Sum.inl (Sum.inr i))
  let θ' : L.BoundedFormula (α ⊕ Fin n) 1 := BoundedFormula.relabel toOne θ.toFormula
  -- Apply the one-variable hypothesis, then relabel the result back; the rest checks the bound
  -- variable lines up on both sides of the equivalence.
  obtain ⟨ψ', hψ', hθψ'⟩ := h θ' (hθ.toFormula.relabel _)
  refine ⟨BoundedFormula.relabel (id : α ⊕ Fin n → α ⊕ Fin n) ψ',
    hψ'.relabel _, fun M v xs => ?_⟩
  let v' : α ⊕ Fin n → M := Sum.elim v xs
  rw [BoundedFormula.realize_iff, BoundedFormula.realize_ex]
  simp only [BoundedFormula.realize_relabel, Function.comp_id,
    Fin.castAdd_zero, Fin.cast_refl]
  rw [Subsingleton.elim (xs ∘ Fin.natAdd n : Fin 0 → M) default]
  refine (exists_congr fun a => ?_).trans
    (BoundedFormula.realize_ex.symm.trans (BoundedFormula.realize_iff.mp (hθψ' M v' default)))
  change θ.Realize v (Fin.snoc xs a) ↔
    (BoundedFormula.relabel toOne θ.toFormula).Realize v' (Fin.snoc default a)
  rw [BoundedFormula.realize_relabel,
    show (Fin.snoc default a ∘ Fin.natAdd 1 : Fin 0 → M) = default from Subsingleton.elim _ _]
  change _ ↔ θ.toFormula.Realize _
  rw [BoundedFormula.realize_toFormula]
  refine iff_of_eq <| congrArg₂ _ ?_ ?_
  · funext i; simp [toOne, v']
  · funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [toOne, v', Fin.snoc]
    · simp [toOne, v']

/-- A theory has quantifier elimination iff every formula over a finite index type of variables is
equivalent over the theory to a quantifier-free formula: any formula has only finitely many free
variables, so the general case reduces to the finite-index case by restricting to the
free-variable subtype. -/
theorem hasQuantifierElimination_iff_finite_isQFEquivalent {T : L.Theory} :
    T.HasQuantifierElimination ↔
      ∀ {α : Type} [Finite α] (φ : L.Formula α), T.IsQFEquivalent φ := by
  refine ⟨fun h _ _ φ => h φ, fun h α φ => ?_⟩
  classical
  let S : Set α := ↑φ.freeVarFinset
  haveI : Finite S := φ.freeVarFinset.finite_toSet.to_subtype
  obtain ⟨ψ', hψ'QF, hψ'eq⟩ := h (φ.restrictFreeVar (Set.inclusion subset_rfl))
  refine ⟨ψ'.relabel ((↑) : S → α), hψ'QF.relabel _, fun M v xs => ?_⟩
  rw [BoundedFormula.realize_iff,
    ← BoundedFormula.realize_restrictFreeVar' (subset_rfl : S ⊆ S)
      (v := v) (xs := xs),
    Subsingleton.elim xs (default : Fin 0 → M)]
  exact (BoundedFormula.realize_iff.mp (hψ'eq M (v ∘ (↑)) default)).trans
    Formula.realize_relabel.symm

/-- A theory has quantifier elimination iff for every quantifier-free formula `θ` with one bound
variable, the formula `θ.ex` is equivalent over the theory to a quantifier-free formula.

This corresponds to [Theorem 3.1.5][marker2002]. -/
theorem hasQuantifierElimination_iff_ex_isQFEquivalent_of_isQF {T : L.Theory} :
    T.HasQuantifierElimination ↔
      ∀ {α : Type} [Finite α] (θ : L.BoundedFormula α 1), θ.IsQF → T.IsQFEquivalent θ.ex := by
  refine ⟨fun h _ _ θ _ => h θ.ex, fun h => ?_⟩
  refine hasQuantifierElimination_iff_finite_isQFEquivalent.mpr (fun {α} _ φ => ?_)
  -- Induct on formula structure: quantifier-free equivalence is preserved by negation, by the
  -- existential step (handled by `exists_qf_equiv_ex_of_isQF`), and along semantic equivalence.
  refine φ.induction_on_exists_not
    (P := fun {_} φ => ∃ ψ, ψ.IsQF ∧ φ ⇔[T] ψ)
    (fun hψ => ⟨_, hψ, Theory.Iff.refl _⟩) ?_ ?_ ?_
  · rintro _ φ ⟨ψ, hψ, hφψ⟩
    exact ⟨ψ.not, hψ.not, hφψ.not⟩
  · rintro _ φ ⟨ψ, hψ, hφψ⟩
    obtain ⟨χ, hχ, hψχ⟩ := exists_qf_equiv_ex_of_isQF h hψ
    exact ⟨χ, hχ, hφψ.ex.trans hψχ⟩
  · intro _ φ₁ φ₂ hφ₁φ₂
    have hφ₁φ₂T : φ₁ ⇔[T] φ₂ := fun M v xs =>
      hφ₁φ₂ (Theory.ModelType.of (∅ : L.Theory) M) v xs
    exact ⟨fun ⟨ψ, hψ, hφ₁ψ⟩ => ⟨ψ, hψ, hφ₁φ₂T.symm.trans hφ₁ψ⟩,
      fun ⟨ψ, hψ, hφ₂ψ⟩ => ⟨ψ, hψ, hφ₁φ₂T.trans hφ₂ψ⟩⟩

/-- The witness-transfer criterion for quantifier elimination: if existential witnesses for
quantifier-free formulas over tuples from a common embedded structure can be transferred between
nonempty models of `T`, then `T` has quantifier elimination.

This corresponds to [Theorem 3.1.6][marker2002]. -/
theorem hasQuantifierElimination_of_exists_realize_of_embeddings {T : L.Theory} :
    (∀ {α : Type} [Finite α] (φ : L.Formula (α ⊕ Fin 1)) (_ : φ.IsQF)
      {M N A : Type (max u v)} [L.Structure M] [L.Structure N] [L.Structure A]
      [T.Model M] [T.Model N] [Nonempty M] [Nonempty N]
      (f : A ↪[L] M) (g : A ↪[L] N) (a : α → A),
      (∃ (b : M), φ.Realize (Sum.elim (f ∘ a) (Fin.snoc default b))) →
      (∃ (c : N), φ.Realize (Sum.elim (g ∘ a) (Fin.snoc default c)))) →
    T.HasQuantifierElimination := by
  intro h
  apply hasQuantifierElimination_iff_ex_isQFEquivalent_of_isQF.mpr
  intro α _ θ hθ
  refine (isQFEquivalent_iff_realize_iff_of_embeddings (T := T) (φ := θ.ex)).mpr ?_
  intro M N A _ _ _ _ _ _ _ f g a
  let φ : L.Formula (α ⊕ Fin 1) := θ.toFormula
  have hφQF : φ.IsQF := hθ.toFormula
  simp only [Formula.Realize, BoundedFormula.realize_ex]
  refine ⟨fun ⟨b, hb⟩ => ?_, fun ⟨c, hc⟩ => ?_⟩
  · obtain ⟨c, hc⟩ := h φ hφQF f g a
      ⟨b, (BoundedFormula.realize_toFormula_snoc θ (f ∘ a) b).mpr hb⟩
    exact ⟨c, (BoundedFormula.realize_toFormula_snoc θ (g ∘ a) c).mp hc⟩
  · obtain ⟨b, hb⟩ := h φ hφQF g f a
      ⟨c, (BoundedFormula.realize_toFormula_snoc θ (g ∘ a) c).mpr hc⟩
    exact ⟨b, (BoundedFormula.realize_toFormula_snoc θ (f ∘ a) b).mp hb⟩

/-- A quantifier-free formula is realized at a tuple in the domain of a partial equivalence iff
it is realized at the image tuple in the codomain. -/
private theorem isQF_realize_partialEquiv
    {α : Type*} {M N : Type*} [L.Structure M] [L.Structure N]
    {φ : L.Formula α} (hφ : φ.IsQF) (p : M ≃ₚ[L] N)
    {v : α → M} (hv : ∀ i, v i ∈ p.dom) :
    φ.Realize (fun i => (p.toEquiv ⟨v i, hv i⟩ : N)) ↔ φ.Realize v := by
  let vdom : α → p.dom := fun i => ⟨v i, hv i⟩
  -- View the tuple inside the domain substructure: both the inclusion `p.dom ↪ M` and the partial
  -- equivalence `p.dom ↪ N` are embeddings, so each preserves quantifier-free realization.
  have hdom : φ.Realize v ↔ φ.Realize vdom := by
    simpa [Formula.Realize, vdom, Function.comp_def,
      Unique.eq_default (fun x : Fin 0 => (((default : Fin 0 → p.dom) x : p.dom) : M))] using
      hφ.realize_embedding (f := (p.dom.subtype : p.dom ↪[L] M)) (v := vdom) (xs := default)
  have hcod : φ.Realize (fun i => (p.toEquiv ⟨v i, hv i⟩ : N)) ↔ φ.Realize vdom := by
    simpa [Formula.Realize, vdom, Function.comp_def, PartialEquiv.toEmbedding,
      Unique.eq_default (fun x : Fin 0 => (p.toEquiv ((default : Fin 0 → p.dom) x) : N))] using
      hφ.realize_embedding (f := p.toEmbedding) (v := vdom) (xs := default)
  exact hcod.trans hdom.symm

/-- Given a partial equivalence `p₀ : M ≃ₚ[L] N` together with an elementary embedding
`e : N ↪ₑ[L] N'` and a partial equivalence `q : M ≃ₚ[L] N'` extending the codomain-mapped
`PartialEquiv.codMap p₀ e`, transport a realization of a quantifier-free formula along `q`. -/
private theorem exists_realize_codMap_of_extends
    {α : Type} [Finite α] {φ : L.Formula (α ⊕ Fin 1)} (hφ : φ.IsQF)
    {M N N' A : Type max u v} [L.Structure M] [L.Structure N] [L.Structure N'] [L.Structure A]
    (p₀ : M ≃ₚ[L] N) (e : N ↪ₑ[L] N')
    (q : M ≃ₚ[L] N') (hpq : PartialEquiv.codMap p₀ e.toEmbedding ≤ q)
    (f : A ↪[L] M) (g : A ↪[L] N) (a : α → A) (b : M)
    (hp_dom : ∀ i, f (a i) ∈ p₀.dom)
    (hp_apply : ∀ i, (p₀.toEquiv ⟨f (a i), hp_dom i⟩ : N) = g (a i))
    (hbq : b ∈ q.dom) (hb : φ.Realize (Sum.elim (f ∘ a) (Fin.snoc default b))) :
    ∃ b' : N', φ.Realize (Sum.elim ((e.toEmbedding ∘ g) ∘ a) (Fin.snoc default b')) := by
  -- As `q` extends `codMap p₀ e`, the generators `f (a i)` lie in `q.dom` and `q` sends them to
  -- `e (g (a i))`. Transporting the witness `b` along `q` then preserves the realization.
  have hqa_dom (i : α) : f (a i) ∈ q.dom := PartialEquiv.dom_le_dom hpq (hp_dom i)
  have hqa_apply (i : α) : (q.toEquiv ⟨f (a i), hqa_dom i⟩ : N') = e (g (a i)) := by
    have hx' := congr_arg (fun y : q.cod => (y : N'))
      (PartialEquiv.toEquiv_inclusion_apply hpq
        (⟨f (a i), hp_dom i⟩ : (PartialEquiv.codMap p₀ e.toEmbedding).dom))
    change (q.toEquiv ⟨f (a i), hqa_dom i⟩ : N') =
      e ((p₀.toEquiv ⟨f (a i), hp_dom i⟩ : N)) at hx'
    rw [hx', hp_apply]
  let vM : α ⊕ Fin 1 → M := Sum.elim (f ∘ a) (Fin.snoc default b)
  have hvM (i : α ⊕ Fin 1) : vM i ∈ q.dom := by
    cases i with
    | inl x => simpa [vM, Function.comp_def] using hqa_dom x
    | inr _ => simpa [vM, Fin.snoc] using hbq
  refine ⟨q.toEquiv ⟨b, hbq⟩, ?_⟩
  have hqreal : φ.Realize (fun i : α ⊕ Fin 1 => (q.toEquiv ⟨vM i, hvM i⟩ : N')) :=
    (isQF_realize_partialEquiv hφ q hvM).mpr (by simpa [vM] using hb)
  convert hqreal using 1
  funext i
  cases i with
  | inl x => simpa [vM, Function.comp_def] using (hqa_apply x).symm
  | inr j => simp [vM, Fin.snoc, Subsingleton.elim j 0]

/-- Pull a realization of a quantifier-free formula back through an elementary embedding to obtain
a witness in the source structure. -/
private theorem exists_realize_descent_through_elementary
    {α : Type} [Finite α] {φ : L.Formula (α ⊕ Fin 1)}
    {N N' : Type max u v} [L.Structure N] [L.Structure N']
    (e : N ↪ₑ[L] N') (ga : α → N) (b' : N')
    (htarget : φ.Realize (Sum.elim (e.toEmbedding ∘ ga) (Fin.snoc default b'))) :
    ∃ c : N, φ.Realize (Sum.elim ga (Fin.snoc default c)) := by
  -- The witness over `α ⊕ Fin 1` is the existential closure `θ.ex`, which the elementary embedding
  -- `e` reflects from `N'` back to `N`.
  let θ : L.BoundedFormula α 1 := BoundedFormula.relabel (id : α ⊕ Fin 1 → α ⊕ Fin 1) φ
  have hθN' : θ.ex.Realize (e.toEmbedding ∘ ga) default :=
    BoundedFormula.realize_ex.mpr
      ⟨b', (BoundedFormula.realize_relabel_id_snoc φ (e.toEmbedding ∘ ga) b').mpr htarget⟩
  have hθN : θ.ex.Realize ga default :=
    (e.map_boundedFormula θ.ex ga default).mp
      (by simpa [Function.comp_def, Unique.eq_default] using hθN')
  obtain ⟨c, hc⟩ := BoundedFormula.realize_ex.mp hθN
  exact ⟨c, (BoundedFormula.realize_relabel_id_snoc φ ga c).mp hc⟩

/-- If, for every pair of nonempty models of `T`, the `< κ`-generated elementary extension-pair
property holds for an infinite `κ`, then `T` has quantifier elimination.

The hypothesis is a `< κ`-generated variant of the extension property appearing as condition (2)
in [Theorem 7.11][vandendries_henson_2016]. -/
theorem hasQuantifierElimination_of_isElementaryExtensionPairCardinalLTGenerated
    {T : L.Theory} {κ : Cardinal} (hκ : Cardinal.aleph0 ≤ κ)
    (h : ∀ ⦃M N : Type (max u v)⦄ [L.Structure M] [L.Structure N]
      [T.Model M] [T.Model N] [Nonempty M] [Nonempty N],
      L.IsElementaryExtensionPairCardinalLTGenerated κ M N) :
    T.HasQuantifierElimination := by
  refine hasQuantifierElimination_of_exists_realize_of_embeddings (T := T) ?_
  intro α _ φ hφ M N A _ _ _ _ _ _ _ f g a hM
  obtain ⟨b, hb⟩ := hM
  obtain ⟨p₀, hp_dom, hp_apply⟩ := exists_cardinalLTEquiv_of_embeddings hκ f g a
  obtain ⟨N', hN', e, q₀, hbq, hpq⟩ := h p₀ b
  letI : L.Structure N' := hN'
  obtain ⟨b', hb'⟩ := exists_realize_codMap_of_extends hφ (p₀ : M ≃ₚ[L] N) e
    (q₀ : M ≃ₚ[L] N') hpq f g a b hp_dom hp_apply hbq hb
  exact exists_realize_descent_through_elementary e (g ∘ a) b' hb'

/-- If every pair of nonempty models of `T` has the finitely generated elementary extension-pair
property, then `T` has quantifier elimination.

The hypothesis is a finitely generated variant of the extension property appearing as condition
(2) in [Theorem 7.11][vandendries_henson_2016]. -/
theorem hasQuantifierElimination_of_isElementaryExtensionPairFG
    {T : L.Theory}
    (h : ∀ ⦃M N : Type (max u v)⦄ [L.Structure M] [L.Structure N]
      [T.Model M] [T.Model N] [Nonempty M] [Nonempty N],
      L.IsElementaryExtensionPairFG M N) :
    T.HasQuantifierElimination :=
  hasQuantifierElimination_of_isElementaryExtensionPairCardinalLTGenerated le_rfl
    fun ⦃M N⦄ _ _ _ _ _ _ => (@h M N _ _ _ _ _ _).toCardinalLTGenerated_aleph0

/-- If every pair of nonempty models of `T` has the elementary extension-pair property, then `T`
has quantifier elimination.

The hypothesis is condition (2) in [Theorem 7.11][vandendries_henson_2016]; this theorem proves
the implication from that extension property to condition (1). -/
theorem hasQuantifierElimination_of_isElementaryExtensionPair
    {T : L.Theory}
    (h : ∀ ⦃M N : Type (max u v)⦄ [L.Structure M] [L.Structure N]
      [T.Model M] [T.Model N] [Nonempty M] [Nonempty N],
      L.IsElementaryExtensionPair M N) :
    T.HasQuantifierElimination :=
  hasQuantifierElimination_of_isElementaryExtensionPairFG
    fun ⦃M N⦄ _ _ _ _ _ _ => (@h M N _ _ _ _ _ _).FG

end Theory

end Language

end FirstOrder
