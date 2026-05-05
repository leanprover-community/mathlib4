/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
module

public import Mathlib.ModelTheory.Complexity
public import Mathlib.ModelTheory.Satisfiability
public import Mathlib.ModelTheory.PartialEquiv

/-!
# Quantifier Elimination

This file defines what it means for a first-order theory to have quantifier elimination.

## Main Definitions

- `FirstOrder.Language.Theory.HasQuantifierElimination` states that every bounded formula in
  finitely many free variables is equivalent, over the theory, to a quantifier-free bounded
  formula.
-/

@[expose] public section

universe u v w

namespace FirstOrder

namespace Language

abbrev Sub (L : Language) (M N : Type*) [L.Structure M] [L.Structure N] :=
  M ≃ₚ[L] N

abbrev Sub₀ (L : Language) (M N : Type*) [L.Structure M] [L.Structure N] :=
  L.FGEquiv M N

namespace PartialEquiv

noncomputable def codMap
    {L : Language} {M N N' : Type*}
    [L.Structure M] [L.Structure N] [L.Structure N']
    (f : L.Sub M N) (e : N ↪[L] N') : M ≃ₚ[L] N' where
  dom := f.dom
  cod := f.cod.map e.toHom
  toEquiv := (e.substructureEquivMap f.cod).comp f.toEquiv

def ExtendsAlong
    {L : Language} {M N N' : Type*}
    [L.Structure M] [L.Structure N] [L.Structure N']
    (e : N ↪ₑ[L] N') (f : M ≃ₚ[L] N) (g : M ≃ₚ[L] N') : Prop :=
  codMap f e.toEmbedding ≤ g

end PartialEquiv

namespace Theory

open Structure

variable {L : Language.{u, v}}
variable {M : Type w} {N A : Type*} [L.Structure M] [L.Structure N] [L.Structure A]

/-- A theory has quantifier elimination if every bounded formula is equivalent, over the theory, to
a quantifier-free bounded formula. -/
def HasQuantifierElimination (T : L.Theory) : Prop :=
  ∀ {m : ℕ} (φ : L.Formula (Fin m)),
    ∃ ψ : L.Formula (Fin m), ψ.IsQF ∧ φ ⇔[T] ψ


-----------------------------------------------------------------------------------------

private theorem exists_substructure_embedding_of_agree_qf
    {m : ℕ} {M N : Type*} [L.Structure M] [L.Structure N]
    (v : Fin m → M) (w : Fin m → N)
    (hQF : ∀ ψ : L.Formula (Fin m), ψ.IsQF → (ψ.Realize v ↔ ψ.Realize w)) :
    ∃ S : L.Substructure M, ∃ g : S ↪[L] N, ∃ a : Fin m → S,
      ((↑) ∘ a = v) ∧ g ∘ a = w := by
  classical
  let S : L.Substructure M := Substructure.closure L (Set.range v)
  let idx : Set.range v → Fin m := fun x => Classical.choose x.2
  have hidx : ∀ x : Set.range v, v (idx x) = x.1 := fun x => Classical.choose_spec x.2
  have hvar : ∀ {i j : Fin m}, v i = v j → w i = w j := by
    intro i j hij
    have hv : (Term.equal (L := L) (Term.var i) (Term.var j) : L.Formula (Fin m)).Realize v := by
      simpa [Formula.realize_equal] using hij
    have hiffFn :
        BoundedFormula.IsQF (Term.equal (L := L) (Term.var i) (Term.var j)) →
          ((Term.equal (L := L) (Term.var i) (Term.var j) : L.Formula (Fin m)).Realize v ↔
            (Term.equal (L := L) (Term.var i) (Term.var j) : L.Formula (Fin m)).Realize w) :=
      hQF (Term.equal (L := L) (Term.var i) (Term.var j))
    have hiff :
        (Term.equal (L := L) (Term.var i) (Term.var j) : L.Formula (Fin m)).Realize v ↔
          (Term.equal (L := L) (Term.var i) (Term.var j) : L.Formula (Fin m)).Realize w :=
      hiffFn
        (by
          simpa [Term.equal] using
            (BoundedFormula.IsAtomic.equal
              ((Term.var i).relabel Sum.inl) ((Term.var j).relabel Sum.inl)).isQF)
    have hw :
        (Term.equal (L := L) (Term.var i) (Term.var j) : L.Formula (Fin m)).Realize w :=
      hiff.1 hv
    simpa using hw
  have hterm_realize :
      ∀ t : L.Term (Set.range v),
        (t.relabel idx).realize v = t.realize ((↑) : Set.range v → M) := by
    intro t
    have hvcomp : v ∘ idx = ((↑) : Set.range v → M) := by
      funext x
      exact hidx x
    calc
      (t.relabel idx).realize v = t.realize (v ∘ idx) := by
        exact Term.realize_relabel (t := t) (g := idx) (v := v)
      _ = t.realize ((↑) : Set.range v → M) := by
        simp [hvcomp]
  have hterm_eq :
      ∀ {t u : L.Term (Set.range v)},
        t.realize ((↑) : Set.range v → M) = u.realize ((↑) : Set.range v → M) →
          (t.relabel idx).realize w = (u.relabel idx).realize w := by
    intro t u htu
    have hv :
        (Term.equal (L := L) (t.relabel idx) (u.relabel idx) : L.Formula (Fin m)).Realize v := by
      simpa [Formula.realize_equal, hterm_realize t, hterm_realize u] using htu
    have hiffFn :
        BoundedFormula.IsQF (Term.equal (L := L) (t.relabel idx) (u.relabel idx)) →
          ((Term.equal (L := L) (t.relabel idx) (u.relabel idx) : L.Formula (Fin m)).Realize v ↔
            (Term.equal (L := L) (t.relabel idx) (u.relabel idx) : L.Formula (Fin m)).Realize w) :=
      hQF (Term.equal (L := L) (t.relabel idx) (u.relabel idx))
    have hiff :
        (Term.equal (L := L) (t.relabel idx) (u.relabel idx) : L.Formula (Fin m)).Realize v ↔
          (Term.equal (L := L) (t.relabel idx) (u.relabel idx) : L.Formula (Fin m)).Realize w :=
      hiffFn
        (by
          simpa [Term.equal] using
            (BoundedFormula.IsAtomic.equal
              ((t.relabel idx).relabel Sum.inl) ((u.relabel idx).relabel Sum.inl)).isQF)
    have hw :
        (Term.equal (L := L) (t.relabel idx) (u.relabel idx) : L.Formula (Fin m)).Realize w :=
      hiff.1 hv
    simpa using hw
  choose repr hrepr using fun x : S =>
    (Substructure.mem_closure_iff_exists_term (L := L) (s := Set.range v) (x := (x : M))).1 x.2
  let g : S ↪[L] N := {
    toFun := fun x => (repr x).relabel idx |>.realize w
    inj' := by
      intro x y hxy
      apply Subtype.ext
      have hw :
          (Term.equal (L := L) ((repr x).relabel idx) ((repr y).relabel idx) :
            L.Formula (Fin m)).Realize w := by
        simpa [Formula.realize_equal] using hxy
      have hiffFn :
          BoundedFormula.IsQF
              (Term.equal (L := L) ((repr x).relabel idx) ((repr y).relabel idx)) →
            ((Term.equal (L := L) ((repr x).relabel idx) ((repr y).relabel idx) :
              L.Formula (Fin m)).Realize v ↔
              (Term.equal (L := L) ((repr x).relabel idx) ((repr y).relabel idx) :
                L.Formula (Fin m)).Realize w) :=
        hQF (Term.equal (L := L) ((repr x).relabel idx) ((repr y).relabel idx))
      have hiff :
          (Term.equal (L := L) ((repr x).relabel idx) ((repr y).relabel idx) :
            L.Formula (Fin m)).Realize v ↔
          (Term.equal (L := L) ((repr x).relabel idx) ((repr y).relabel idx) :
            L.Formula (Fin m)).Realize w :=
        hiffFn
          (by
            simpa [Term.equal] using
              (BoundedFormula.IsAtomic.equal
                (((repr x).relabel idx).relabel Sum.inl)
                (((repr y).relabel idx).relabel Sum.inl)).isQF)
      have hv :
          (Term.equal (L := L) ((repr x).relabel idx) ((repr y).relabel idx) :
            L.Formula (Fin m)).Realize v :=
        hiff.2 hw
      simpa [hterm_realize (repr x), hterm_realize (repr y), hrepr x, hrepr y] using hv
    map_fun' := by
      intro n f x
      have hfunc :
          (repr (Structure.funMap f x)).realize ((↑) : Set.range v → M) =
            (Term.func f fun i => repr (x i)).realize ((↑) : Set.range v → M) := by
        calc
          (repr (Structure.funMap f x)).realize ((↑) : Set.range v → M) =
              (↑(Structure.funMap f x) : M) := hrepr _
          _ = Structure.funMap f fun i => ↑(x i) := rfl
          _ = (Term.func f fun i => repr (x i)).realize ((↑) : Set.range v → M) := by
            simp [Term.realize, hrepr]
      simpa [Term.realize] using
        (hterm_eq (t := repr (Structure.funMap f x)) (u := Term.func f fun i => repr (x i)) hfunc)
    map_rel' := by
      intro n R x
      have hiffFn :
          BoundedFormula.IsQF (R.formula fun i => (repr (x i)).relabel idx) →
            ((R.formula fun i => (repr (x i)).relabel idx : L.Formula (Fin m)).Realize v ↔
              (R.formula fun i => (repr (x i)).relabel idx : L.Formula (Fin m)).Realize w) :=
        hQF (R.formula fun i => (repr (x i)).relabel idx)
      have h :
          (R.formula fun i => (repr (x i)).relabel idx : L.Formula (Fin m)).Realize v ↔
            (R.formula fun i => (repr (x i)).relabel idx : L.Formula (Fin m)).Realize w :=
        hiffFn
          (by
            simpa [Relations.formula] using
              (BoundedFormula.IsAtomic.rel R
                (fun i => ((repr (x i)).relabel idx).relabel Sum.inl)).isQF)
      simpa [hterm_realize, hrepr] using h.symm
  }
  let a : Fin m → S := fun i => ⟨v i, Substructure.subset_closure ⟨i, rfl⟩⟩
  have ha : ((↑) ∘ a : Fin m → M) = v := by
    funext i
    rfl
  have hg : g ∘ a = w := by
    funext i
    let xi : Set.range v := ⟨v i, ⟨i, rfl⟩⟩
    have hxi :
        (repr (a i)).realize ((↑) : Set.range v → M) =
          (Term.var (L := L) xi).realize ((↑) : Set.range v → M) := by
      simp [a, xi, hrepr]
    have hEq := hterm_eq hxi
    have hwx : w (idx xi) = w i := hvar (hidx xi)
    simpa [g, a, xi] using hEq.trans hwx
  exact ⟨S, g, a, ha, hg⟩




theorem marker_314
    {T : L.Theory} {m : ℕ} (φ : L.Formula (Fin m)) :
    (∃ ψ : L.Formula (Fin m), ψ.IsQF ∧ φ ⇔[T] ψ) ↔
      (∀ {M N A : Type (max u v)} [L.Structure M] [L.Structure N] [L.Structure A]
        [T.Model M] [T.Model N] [Nonempty M] [Nonempty N]
        (f : A ↪[L] M) (g : A ↪[L] N)
        (a : Fin m → A), φ.Realize (f ∘ a) ↔ φ.Realize (g ∘ a)) := by
  constructor
  · intro h M N A _ _ _ _ _ _ _ f g a
    rcases h with ⟨ψ, hψ, hiff⟩
    have hM : φ.Realize (f ∘ a) ↔ ψ.Realize (f ∘ a) := hiff.realize_iff (M := M) (v := f ∘ a)
    have hN : ψ.Realize (g ∘ a) ↔ φ.Realize (g ∘ a) :=
      (hiff.realize_iff (M := N) (v := g ∘ a)).symm
    have hf : ψ.Realize (f ∘ a) ↔ ψ.Realize a := by
      simpa [Formula.Realize, Unique.eq_default (f ∘ default)] using
        (hψ.realize_embedding (f := f) (v := a) (xs := default))
    have hg : ψ.Realize a ↔ ψ.Realize (g ∘ a) := by
      simpa [Formula.Realize, Unique.eq_default (g ∘ default)] using
        (hψ.realize_embedding (f := g) (v := a) (xs := default)).symm
    calc
      φ.Realize (f ∘ a) ↔ ψ.Realize (f ∘ a) := hM
      _ ↔ ψ.Realize a := hf
      _ ↔ ψ.Realize (g ∘ a) := hg
      _ ↔ φ.Realize (g ∘ a) := hN
  · intro hcommon
    classical
    by_cases hqe : ∃ ψ : L.Formula (Fin m), ψ.IsQF ∧ φ ⇔[T] ψ
    · exact hqe
    · let Q1 : Type _ := {ψ : L.Formula (Fin m) // ψ.IsQF ∧ φ ⟹[T] ψ}
      let base1 : L[[Fin m]].Theory :=
        (L.lhomWithConstants (Fin m)).onTheory T ∪ {Formula.equivSentence φ.not}
      let U1 : Option Q1 → L[[Fin m]].Theory
        | none => base1
        | some ψ => base1 ∪ {Formula.equivSentence ψ.1}
      have hsat1 : Theory.IsSatisfiable (⋃ i, U1 i) := by
        by_contra hsat1
        rw [Theory.isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset] at hsat1
        push_neg at hsat1
        rcases hsat1 with ⟨s, hs⟩
        let qfs : Finset Q1 :=
          s.filterMap id (by
            intro a a' b ha ha'
            simpa using ha.trans ha'.symm)
        let lqfs : List Q1 := qfs.toList
        let θ : L.Formula (Fin m) := (lqfs.map Subtype.val).foldr (· ⊓ ·) ⊤
        have hθQF : θ.IsQF := by
          unfold θ
          induction lqfs with
          | nil => exact BoundedFormula.IsQF.top
          | cons q l ih =>
              exact q.2.1.inf (by simpa using ih)
        have hφθ : φ ⟹[T] θ := by
          intro M v xs hφ
          simpa [θ] using
            ((BoundedFormula.realize_foldr_inf (l := lqfs.map Subtype.val) (v := v)
              (xs := xs)).2 (by
                intro ψ hψ
                rcases List.mem_map.1 hψ with ⟨q, hq, rfl⟩
                exact q.2.2 M v xs hφ))
        have hθφ : θ ⟹[T] φ := by
          intro M v xs hθ
          by_contra hφ
          letI : (constantsOn (Fin m)).Structure M := constantsOn.structure v
          have hmodel : M ⊨ ⋃ i ∈ s, U1 i := by
            refine ⟨fun σ hσ => ?_⟩
            simp only [Set.mem_iUnion] at hσ
            rcases hσ with ⟨i, hi, hσ⟩
            have hθall :
                ∀ ψ ∈ lqfs.map Subtype.val, BoundedFormula.Realize ψ v xs := by
              simpa [θ] using
                ((BoundedFormula.realize_foldr_inf (l := lqfs.map Subtype.val) (v := v)
                  (xs := xs)).1 hθ)
            cases i with
            | none =>
                rcases hσ with hT | hnot
                · exact ((LHom.onTheory_model _ _).2 inferInstance).realize_of_mem _ hT
                · rw [Set.mem_singleton_iff] at hnot
                  subst hnot
                  exact (Formula.realize_equivSentence (M := M) φ.not).2 (by
                    have : ¬φ.Realize v := by
                      simpa [Formula.boundedFormula_realize_eq_realize (φ := φ) (x := v) (y := xs)]
                        using hφ
                    simpa [Formula.realize_not] using this)
            | some q =>
                rcases hσ with hbase | hq
                · rcases hbase with hT | hnot
                  · exact ((LHom.onTheory_model _ _).2 inferInstance).realize_of_mem _ hT
                  · rw [Set.mem_singleton_iff] at hnot
                    subst hnot
                    exact (Formula.realize_equivSentence (M := M) φ.not).2 (by
                      have : ¬φ.Realize v := by
                        simpa [Formula.boundedFormula_realize_eq_realize (φ := φ) (x := v)
                          (y := xs)] using hφ
                      simpa [Formula.realize_not] using this)
                · rw [Set.mem_singleton_iff] at hq
                  subst hq
                  have hqmem : q ∈ qfs := by
                    simpa [qfs] using hi
                  have hqlist : q.1 ∈ lqfs.map Subtype.val := by
                    exact List.mem_map.2 ⟨q, Finset.mem_toList.2 hqmem, rfl⟩
                  have hqreal : q.1.Realize v :=
                    (Formula.boundedFormula_realize_eq_realize (φ := q.1) (x := v) (y := xs)).1
                      (hθall q.1 hqlist)
                  exact (Formula.realize_equivSentence (M := M) q.1).2 hqreal
          exact hs (Theory.Model.isSatisfiable M)
        exact False.elim (hqe ⟨θ, hθQF, Theory.imp_antisymm hφθ hθφ⟩)
      obtain ⟨M1⟩ := hsat1
      letI : L.Structure M1 := (L.lhomWithConstants (Fin m)).reduct M1
      haveI : T.Model M1 := by
        have hsubset : (L.lhomWithConstants (Fin m)).onTheory T ⊆ ⋃ i, U1 i := by
          intro σ hσ
          refine Set.mem_iUnion.2 ⟨none, ?_⟩
          exact Or.inl hσ
        exact (LHom.onTheory_model _ _).1 (M1.is_model.mono hsubset)
      haveI : (L.lhomWithConstants (Fin m)).IsExpansionOn M1 := LHom.isExpansionOn_reduct _ _
      let v0 : Fin m → M1 := fun i => (L.con i : M1)
      have hnotφv0 : ¬ φ.Realize v0 := by
        have hmem : Formula.equivSentence φ.not ∈ ⋃ i, U1 i := by
          refine Set.mem_iUnion.2 ⟨none, ?_⟩
          simp [U1, base1]
        have hreal : M1 ⊨ Formula.equivSentence φ.not := M1.is_model.realize_of_mem _ hmem
        have hreal' : φ.not.Realize v0 := (Formula.realize_equivSentence (M := M1) φ.not).1 hreal
        simpa [Formula.realize_not] using hreal'
      have hqfConseq : ∀ q : Q1, q.1.Realize v0 := by
        intro q
        have hmem : Formula.equivSentence q.1 ∈ ⋃ i, U1 i := by
          refine Set.mem_iUnion.2 ⟨some q, ?_⟩
          simp [U1, base1]
        have hreal : M1 ⊨ Formula.equivSentence q.1 := M1.is_model.realize_of_mem _ hmem
        exact (Formula.realize_equivSentence (M := M1) q.1).1 hreal
      let P : Type _ := {ψ : L.Formula (Fin m) // ψ.IsQF ∧ ψ.Realize v0}
      let base2 : L[[Fin m]].Theory :=
        (L.lhomWithConstants (Fin m)).onTheory T ∪ {Formula.equivSentence φ}
      let U2 : Option P → L[[Fin m]].Theory
        | none => base2
        | some ψ => base2 ∪ {Formula.equivSentence ψ.1}
      have hsat2 : Theory.IsSatisfiable (⋃ i, U2 i) := by
        by_contra hsat2
        rw [Theory.isSatisfiable_iUnion_iff_isSatisfiable_iUnion_finset] at hsat2
        push_neg at hsat2
        rcases hsat2 with ⟨s, hs⟩
        let qfs : Finset P :=
          s.filterMap id (by
            intro a a' b ha ha'
            simpa using ha.trans ha'.symm)
        let lqfs : List P := qfs.toList
        let θ : L.Formula (Fin m) := (lqfs.map Subtype.val).foldr (· ⊓ ·) ⊤
        have hθQF : θ.IsQF := by
          unfold θ
          induction lqfs with
          | nil => exact BoundedFormula.IsQF.top
          | cons q l ih =>
              exact q.2.1.inf (by simpa using ih)
        have hφnotθ : φ ⟹[T] θ.not := by
          intro M v xs hφ
          by_contra hnotθ
          have hθ : BoundedFormula.Realize θ v xs := by
            simpa [BoundedFormula.realize_not] using hnotθ
          letI : (constantsOn (Fin m)).Structure M := constantsOn.structure v
          have hmodel : M ⊨ ⋃ i ∈ s, U2 i := by
            refine ⟨fun σ hσ => ?_⟩
            simp only [Set.mem_iUnion] at hσ
            rcases hσ with ⟨i, hi, hσ⟩
            have hθall :
                ∀ ψ ∈ lqfs.map Subtype.val, BoundedFormula.Realize ψ v xs := by
              simpa [θ] using
                ((BoundedFormula.realize_foldr_inf (l := lqfs.map Subtype.val) (v := v)
                  (xs := xs)).1 hθ)
            cases i with
            | none =>
                rcases hσ with hT | hφ'
                · exact ((LHom.onTheory_model _ _).2 inferInstance).realize_of_mem _ hT
                · rw [Set.mem_singleton_iff] at hφ'
                  subst hφ'
                  exact (Formula.realize_equivSentence (M := M) φ).2
                    ((Formula.boundedFormula_realize_eq_realize (φ := φ) (x := v) (y := xs)).1 hφ)
            | some q =>
                rcases hσ with hbase | hq
                · rcases hbase with hT | hφ'
                  · exact ((LHom.onTheory_model _ _).2 inferInstance).realize_of_mem _ hT
                  · rw [Set.mem_singleton_iff] at hφ'
                    subst hφ'
                    exact (Formula.realize_equivSentence (M := M) φ).2
                      ((Formula.boundedFormula_realize_eq_realize (φ := φ) (x := v) (y := xs)).1
                        hφ)
                · rw [Set.mem_singleton_iff] at hq
                  subst hq
                  have hqmem : q ∈ qfs := by
                    simpa [qfs] using hi
                  have hqlist : q.1 ∈ lqfs.map Subtype.val := by
                    exact List.mem_map.2 ⟨q, Finset.mem_toList.2 hqmem, rfl⟩
                  have hqreal : q.1.Realize v :=
                    (Formula.boundedFormula_realize_eq_realize (φ := q.1) (x := v) (y := xs)).1
                      (hθall q.1 hqlist)
                  exact (Formula.realize_equivSentence (M := M) q.1).2 hqreal
          exact hs (Theory.Model.isSatisfiable M)
        have hθv0 : θ.Realize v0 := by
          have hθv0' : BoundedFormula.Realize θ v0 default := by
            simpa [θ] using
              ((BoundedFormula.realize_foldr_inf (l := lqfs.map Subtype.val) (v := v0)
                (xs := default)).2 (by
                  intro ψ hψ
                  rcases List.mem_map.1 hψ with ⟨q, hq, rfl⟩
                  exact (Formula.boundedFormula_realize_eq_realize (φ := q.1) (x := v0)
                    (y := default)).2 q.2.2))
          exact (Formula.boundedFormula_realize_eq_realize (φ := θ) (x := v0) (y := default)).1
            hθv0'
        have hnotθv0 : θ.not.Realize v0 := by
          let qnot : Q1 := ⟨θ.not, hθQF.not, hφnotθ⟩
          exact hqfConseq qnot
        exact (hnotθv0 hθv0).elim
      obtain ⟨N1⟩ := hsat2
      letI : L.Structure N1 := (L.lhomWithConstants (Fin m)).reduct N1
      haveI : T.Model N1 := by
        have hsubset : (L.lhomWithConstants (Fin m)).onTheory T ⊆ ⋃ i, U2 i := by
          intro σ hσ
          refine Set.mem_iUnion.2 ⟨none, ?_⟩
          exact Or.inl hσ
        exact (LHom.onTheory_model _ _).1 (N1.is_model.mono hsubset)
      haveI : (L.lhomWithConstants (Fin m)).IsExpansionOn N1 := LHom.isExpansionOn_reduct _ _
      let w : Fin m → N1 := fun i => (L.con i : N1)
      have hφw : φ.Realize w := by
        have hmem : Formula.equivSentence φ ∈ ⋃ i, U2 i := by
          refine Set.mem_iUnion.2 ⟨none, ?_⟩
          simp [U2, base2]
        have hreal : N1 ⊨ Formula.equivSentence φ := N1.is_model.realize_of_mem _ hmem
        exact (Formula.realize_equivSentence (M := N1) φ).1 hreal
      have hqfIncl : ∀ ψ : L.Formula (Fin m), ψ.IsQF → ψ.Realize v0 → ψ.Realize w := by
        intro ψ hψ hψv0
        let q : P := ⟨ψ, hψ, hψv0⟩
        have hmem : Formula.equivSentence ψ ∈ ⋃ i, U2 i := by
          refine Set.mem_iUnion.2 ⟨some q, ?_⟩
          exact Or.inr (Set.mem_singleton _)
        have hreal : N1 ⊨ Formula.equivSentence ψ := N1.is_model.realize_of_mem _ hmem
        exact (Formula.realize_equivSentence (M := N1) ψ).1 hreal
      have hqfEq : ∀ ψ : L.Formula (Fin m), ψ.IsQF → (ψ.Realize v0 ↔ ψ.Realize w) := by
        intro ψ hψ
        constructor
        · exact hqfIncl ψ hψ
        · intro hψw
          by_contra hψv0
          have hnotv0 : ψ.not.Realize v0 := by simpa [Formula.realize_not] using hψv0
          have hnotw : ψ.not.Realize w := hqfIncl ψ.not hψ.not hnotv0
          exact hnotw hψw
      obtain ⟨S, g, a, ha, hg⟩ := exists_substructure_embedding_of_agree_qf v0 w hqfEq
      let M0 : Type _ := M1.Carrier
      let N0 : Type _ := N1.Carrier
      letI : L.Structure M0 := inferInstanceAs (L.Structure M1)
      letI : L.Structure N0 := inferInstanceAs (L.Structure N1)
      letI : T.Model M0 := inferInstanceAs (T.Model M1)
      letI : T.Model N0 := inferInstanceAs (T.Model N1)
      let A0 : Type _ := S
      letI : L.Structure A0 := inferInstanceAs (L.Structure S)
      let f0 : A0 ↪[L] M0 := S.subtype
      let g0 : A0 ↪[L] N0 := g
      let a0 : Fin m → A0 := a
      have hsame :
          φ.Realize (f0 ∘ a0) ↔ φ.Realize (g0 ∘ a0) := by
        exact hcommon (A := A0) f0 g0 a0
      have hφga : φ.Realize (g ∘ a) := by simpa [hg] using hφw
      exact False.elim (hnotφv0 (by simpa [M0, N0, A0, f0, g0, a0, ha] using hsame.mpr hφga))


-----------------------------------------------------------------------------------------

private theorem isQF_toFormula
    {α : Type*} {n : ℕ} {φ : L.BoundedFormula α n} (hφ : φ.IsQF) :
    φ.toFormula.IsQF := by
  induction hφ with
  | falsum => exact BoundedFormula.IsQF.falsum
  | of_isAtomic hφ =>
      cases hφ with
      | equal t₁ t₂ =>
          simpa [BoundedFormula.toFormula, Term.equal] using
            (BoundedFormula.IsAtomic.equal
              ((t₁).relabel Sum.inl) ((t₂).relabel Sum.inl)).isQF
      | rel R ts =>
          simpa [BoundedFormula.toFormula, Relations.formula] using
            (BoundedFormula.IsAtomic.rel R
              (fun i => (ts i).relabel Sum.inl)).isQF
  | imp _ _ ih₁ ih₂ =>
      simpa [BoundedFormula.toFormula] using ih₁.imp ih₂

private theorem exists_qf_equiv_ex_of_qf
    {T : L.Theory}
    (h :
      ∀ {m : ℕ} (θ : L.BoundedFormula (Fin m) 1), θ.IsQF →
        ∃ ψ : L.Formula (Fin m), ψ.IsQF ∧ θ.ex ⇔[T] ψ)
    {m n : ℕ} {θ : L.BoundedFormula (Fin m) (n + 1)} (hθ : θ.IsQF) :
    ∃ ψ : L.BoundedFormula (Fin m) n, ψ.IsQF ∧ θ.ex ⇔[T] ψ := by
  classical
  let toOne : Fin m ⊕ Fin (n + 1) → Fin (m + n) ⊕ Fin 1 :=
    Sum.elim
      (fun i : Fin m => Sum.inl (Fin.castAdd n i))
      (fun j : Fin (n + 1) =>
        Fin.lastCases (Sum.inr 0) (fun i : Fin n => Sum.inl (Fin.natAdd m i)) j)
  let θ' : L.BoundedFormula (Fin (m + n)) 1 :=
    BoundedFormula.relabel (L := L) (β := Fin (m + n)) (n := 1) toOne θ.toFormula
  have hθ' : θ'.IsQF := by
    exact (isQF_toFormula hθ).relabel _
  obtain ⟨ψ', hψ', hθψ'⟩ := h θ' hθ'
  let ψ : L.BoundedFormula (Fin m) n :=
    BoundedFormula.relabel (L := L) (β := Fin m) (n := n)
      (fun i : Fin (m + n) => finSumFinEquiv.symm i) ψ'
  refine ⟨ψ, ?_, ?_⟩
  · exact hψ'.relabel _
  · intro M v xs
    let v' : Fin (m + n) → M := fun i => Sum.elim v xs (finSumFinEquiv.symm i)
    have hmain := hθψ' M v' default
    rw [BoundedFormula.realize_iff] at hmain
    rw [BoundedFormula.realize_iff]
    calc
      θ.ex.Realize v xs ↔ θ'.ex.Realize v' default := by
        rw [BoundedFormula.realize_ex, BoundedFormula.realize_ex]
        refine exists_congr fun a => ?_
        change θ.Realize v (Fin.snoc xs a) ↔
          (BoundedFormula.relabel toOne θ.toFormula).Realize v' (Fin.snoc default a)
        rw [BoundedFormula.realize_relabel]
        have hxs0 :
            (Fin.snoc default a ∘ Fin.natAdd 1 : Fin 0 → M) = default := by
          funext i
          exact i.elim0
        rw [hxs0]
        let val : Fin m ⊕ Fin (n + 1) → M :=
          Sum.elim v' (Fin.snoc default a ∘ Fin.castAdd 0) ∘ toOne
        change θ.Realize v (Fin.snoc xs a) ↔ θ.toFormula.Realize val
        rw [BoundedFormula.realize_toFormula]
        have hfree :
            val ∘ Sum.inl = v := by
          funext i
          simp [val, toOne, v']
        have hbound :
            val ∘ Sum.inr = Fin.snoc xs a := by
          funext j
          refine Fin.lastCases ?_ ?_ j
          · simp [val, toOne, v', Fin.snoc]
          · intro i
            simp [val, toOne, v']
        simp [hfree, hbound]
      _ ↔ ψ'.Realize v' := hmain
      _ ↔ ψ.Realize v xs := by
        have hxs0 : (xs ∘ Fin.natAdd n : Fin 0 → M) = default := by
          funext i
          exact i.elim0
        change ψ'.Realize v' ↔
          (BoundedFormula.relabel (fun i : Fin (m + n) => finSumFinEquiv.symm i) ψ').Realize v xs
        rw [BoundedFormula.realize_relabel]
        change ψ'.Realize v' ↔
          BoundedFormula.Realize ψ' v' (xs ∘ Fin.natAdd n)
        rw [hxs0]
        change ψ'.Realize v' ↔ ψ'.Realize v'
        rfl

theorem marker_315
  {T : L.Theory} :
  ((∀ {m : ℕ} (θ : L.BoundedFormula (Fin m) 1), θ.IsQF →
  ∃ (ψ : L.Formula (Fin m)), ψ.IsQF ∧ θ.ex ⇔[T] ψ))
  → HasQuantifierElimination T := by
  intro h m φ
  let P : ∀ {n : ℕ}, L.BoundedFormula (Fin m) n → Prop :=
    fun {n} φ => ∃ ψ : L.BoundedFormula (Fin m) n, ψ.IsQF ∧ φ ⇔[T] ψ
  have hP : P φ := by
    refine φ.induction_on_exists_not (P := P) ?hqf ?hnot ?hex ?hse
    · intro n ψ hψ
      exact ⟨ψ, hψ, Theory.Iff.refl ψ⟩
    · intro n φ hφ
      rcases hφ with ⟨ψ, hψ, hφψ⟩
      exact ⟨ψ.not, hψ.not, hφψ.not⟩
    · intro n φ hφ
      rcases hφ with ⟨ψ, hψ, hφψ⟩
      rcases exists_qf_equiv_ex_of_qf h hψ with ⟨χ, hχ, hψχ⟩
      exact ⟨χ, hχ, hφψ.ex.trans hψχ⟩
    · intro n φ₁ φ₂ hφ₁φ₂
      have hφ₁φ₂T : φ₁ ⇔[T] φ₂ := by
        intro M v xs
        exact hφ₁φ₂ (Theory.ModelType.of (∅ : L.Theory) M) v xs
      constructor
      · rintro ⟨ψ, hψ, hφ₁ψ⟩
        exact ⟨ψ, hψ, hφ₁φ₂T.symm.trans hφ₁ψ⟩
      · rintro ⟨ψ, hψ, hφ₂ψ⟩
        exact ⟨ψ, hψ, hφ₁φ₂T.trans hφ₂ψ⟩
  exact hP


-----------------------------------------------------------------------------------------

theorem marker_316 {T : L.Theory} :
  (∀ {m : ℕ} (φ : L.Formula (Fin m.succ)) (_ : φ.IsQF)
    {M N A : Type (max u v)} [L.Structure M] [L.Structure N] [L.Structure A]
    [T.Model M] [T.Model N] [Nonempty M] [Nonempty N]
    (f : A ↪[L] M) (g : A ↪[L] N) (a : Fin m → A),
    (∃ (b : M), φ.Realize (Fin.snoc (f ∘ a) b)) →
    (∃ (c : N), φ.Realize (Fin.snoc (g ∘ a) c))) →
  T.HasQuantifierElimination := by
  intro h
  apply marker_315
  intro m θ hθ
  refine (marker_314 (T := T) (φ := θ.ex)).2 ?_
  intro M N A _ _ _ _ _ _ _ f g a
  let φ : L.Formula (Fin m.succ) := θ.toFormula.relabel finSumFinEquiv
  have hφQF : φ.IsQF := by
    exact (isQF_toFormula hθ).relabel _
  have hreal :
      ∀ {X : Type (max u v)} [L.Structure X] (x : Fin m → X) (b : X),
        φ.Realize (Fin.snoc x b) ↔ θ.Realize x (Fin.snoc default b) := by
    intro X _ x b
    rw [Formula.realize_relabel, BoundedFormula.realize_toFormula]
    have hfree : ((Fin.snoc x b ∘ ⇑finSumFinEquiv) ∘ Sum.inl) = x := by
      funext i
      change (Fin.snoc x b : Fin (m + 1) → X) i.castSucc = x i
      rw [Fin.snoc_castSucc]
    have hbound : ((Fin.snoc x b ∘ ⇑finSumFinEquiv) ∘ Sum.inr) = Fin.snoc default b := by
      funext i
      have hi : i = 0 := Subsingleton.elim i 0
      rw [hi]
      change (Fin.snoc x b : Fin (m + 1) → X) (Fin.last m) =
        (Fin.snoc default b : Fin 1 → X) (Fin.last 0)
      rw [Fin.snoc_last, Fin.snoc_last]
    rw [hfree, hbound]
  constructor
  · intro hM
    rw [Formula.Realize, BoundedFormula.realize_ex] at hM
    rw [Formula.Realize, BoundedFormula.realize_ex]
    rcases hM with ⟨b, hb⟩
    obtain ⟨c, hc⟩ :=
      h (m := m) φ hφQF (M := M) (N := N) (A := A) f g a
        ⟨b, (hreal (f ∘ a) b).2 hb⟩
    exact ⟨c, (hreal (g ∘ a) c).1 hc⟩
  · intro hN
    rw [Formula.Realize, BoundedFormula.realize_ex] at hN
    rw [Formula.Realize, BoundedFormula.realize_ex]
    rcases hN with ⟨c, hc⟩
    obtain ⟨b, hb⟩ :=
      h (m := m) φ hφQF (M := N) (N := M) (A := A) g f a
        ⟨c, (hreal (g ∘ a) c).2 hc⟩
    exact ⟨b, (hreal (f ∘ a) b).1 hb⟩

/-- Henson, Theorem 7.11, direction `(2) → (1)`: if every partial isomorphism between
substructures of models of `T` can be extended, after passing to an elementary extension of the
codomain model, to include any prescribed element of the domain model, then `T` has quantifier
elimination. -/
theorem henson_711
    {T : L.Theory}
    (h :
      ∀ {M N : Type (max u v)} [L.Structure M] [L.Structure N]
        [T.Model M] [T.Model N] [Nonempty M] [Nonempty N]
        (f : L.Sub M N) (a : M),
        ∃ (N' : Type (max u v)) (_ : L.Structure N')
          (e : N ↪ₑ[L] N') (g : L.Sub M N'),
          a ∈ g.dom ∧ f.ExtendsAlong e g) :
    T.HasQuantifierElimination := by
  sorry


-----------------------------------------------------------------------------------------


end Theory

end Language

end FirstOrder
