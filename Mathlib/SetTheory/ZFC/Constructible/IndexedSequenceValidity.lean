/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.FiniteSequenceComparison
public import Mathlib.SetTheory.ZFC.Constructible.IndexedSequenceZF

/-!
# Validity and decoding of indexed finite-sequence codes

The indexed representation is useful only if object-language predicates cannot
accept spurious infinite or non-functional graphs as finite programs.  This
file supplies a fixed first-order validity predicate and proves two
representation theorems:

* every genuine `sequenceCode xs` is valid;
* every valid code represents one actual finite Lean list.

The representing graph is allowed to contain irrelevant extra elements.  At
each index below the recorded length, however, it must contain exactly one
value. Every predicate consuming this representation inspects only those
indexed values, so this is the precise invariant required for sound decoding.
-/

@[expose] public section

universe u

namespace Constructible.IndexedSequenceZF

open FiniteSequenceZF

/-! ## Natural members of omega and finite ordinals -/

/-- The members of the standard von Neumann omega are exactly `natCode`s. -/
theorem mem_omega_iff_exists_natCode (x : ZFSet.{u}) :
    x ∈ Ordinal.omega0.toZFSet ↔ ∃ n : Nat, x = natCode n := by
  constructor
  · intro hx
    rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨alpha, halpha, rfl⟩
    rcases Ordinal.lt_omega0.mp halpha with ⟨n, hn⟩
    subst alpha
    exact ⟨n, rfl⟩
  · rintro ⟨n, rfl⟩
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr
      (Ordinal.natCast_lt_omega0 n)

/-- Membership in a finite von Neumann ordinal is bounded natural indexing. -/
theorem mem_natCode_iff_exists_lt (x : ZFSet.{u}) (n : Nat) :
    x ∈ natCode n ↔ ∃ k : Nat, k < n ∧ x = natCode k := by
  constructor
  · intro hx
    rcases Ordinal.mem_toZFSet_iff.mp hx with ⟨alpha, halpha, rfl⟩
    have halphaOmega : alpha < Ordinal.omega0 :=
      halpha.trans (Ordinal.natCast_lt_omega0 n)
    rcases Ordinal.lt_omega0.mp halphaOmega with ⟨k, hk⟩
    subst alpha
    have hkn : k < n := by
      exact_mod_cast halpha
    exact ⟨k, hkn, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact (natCode_mem_natCode_iff k n).mpr hk

/-! ## The fixed first-order predicate -/

/-- With the supplied indices, assert that `<value,index>` belongs to `graph`. -/
def functionGraphValueAt {n : Nat} (graph value index : Fin n) :
    FOFormula n :=
  (Delta0Formula.boundedEx graph
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last n) value.castSucc index.castSucc)).toFO

@[simp]
theorem satisfies_functionGraphValueAt {n : Nat}
    (graph value index : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies Delta0Formula.ZFMem
        (functionGraphValueAt graph value index) s ↔
      ZFSet.pair (s value) (s index) ∈ s graph := by
  simp only [functionGraphValueAt, Delta0Formula.satisfies_toFO,
    Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hq
    exact ⟨ZFSet.pair (s value) (s index), hq, rfl⟩

/-- Formula-level implication, kept local to avoid importing theory packaging. -/
def formulaImp {n : Nat} (phi psi : FOFormula n) : FOFormula n :=
  FOFormula.disj (.neg phi) psi

@[simp]
theorem satisfies_formulaImp {A : Type u} (E : A → A → Prop)
    {n : Nat} (phi psi : FOFormula n) (s : Tuple A n) :
    FOFormula.Satisfies E (formulaImp phi psi) s ↔
      (FOFormula.Satisfies E phi s → FOFormula.Satisfies E psi s) := by
  rw [formulaImp, FOFormula.satisfies_disj]
  change (¬FOFormula.Satisfies E phi s ∨ FOFormula.Satisfies E psi s) ↔ _
  constructor
  · rintro (hphi | hpsi) h
    · exact False.elim (hphi h)
    · exact hpsi
  · intro h
    by_cases hphi : FOFormula.Satisfies E phi s
    · exact Or.inr (h hphi)
    · exact Or.inl hphi

/-
Assignment layout in the innermost context:

`[omega, sequence, length, graph, index, value, other]`.
-/

/-- At the current index, the graph has exactly one value. -/
def uniqueValueAtBody : FOFormula 6 :=
  .conj
    (functionGraphValueAt (3 : Fin 6) (5 : Fin 6) (4 : Fin 6))
    (.all
      (formulaImp
        (functionGraphValueAt (3 : Fin 7) (6 : Fin 7) (4 : Fin 7))
        (.eq (6 : Fin 7) (5 : Fin 7))))

/-- Every index in the recorded length has a unique graph value. -/
def totalFunctionalBody : FOFormula 5 :=
  formulaImp
    (.mem (4 : Fin 5) (2 : Fin 5))
    (.ex uniqueValueAtBody)

/--
`sequenceValidityFormula(omega, sequence)` says that `sequence` records a
natural length and a total, single-valued graph on that finite ordinal.
-/
def sequenceValidityFormula : FOFormula 2 :=
  .ex (.ex
    (.conj
      (Delta0Formula.kuratowskiPairEqAt
        (1 : Fin 4) (2 : Fin 4) (3 : Fin 4)).toFO
      (.conj
        (.mem (2 : Fin 4) (0 : Fin 4))
        (.all totalFunctionalBody))))

@[simp]
theorem satisfies_uniqueValueAtBody
    (omega sequence length graph index value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem uniqueValueAtBody
        ![omega, sequence, length, graph, index, value] ↔
      ZFSet.pair value index ∈ graph ∧
        ∀ other : ZFSet.{u},
          ZFSet.pair other index ∈ graph → other = value := by
  simp [uniqueValueAtBody]

@[simp]
theorem satisfies_totalFunctionalBody
    (omega sequence length graph index : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem totalFunctionalBody
        ![omega, sequence, length, graph, index] ↔
      (index ∈ length →
        ∃ value : ZFSet.{u},
          ZFSet.pair value index ∈ graph ∧
            ∀ other : ZFSet.{u},
              ZFSet.pair other index ∈ graph → other = value) := by
  simp [totalFunctionalBody]

@[simp]
theorem satisfies_sequenceValidityFormula
    (omega sequence : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
        ![omega, sequence] ↔
      ∃ length graph : ZFSet.{u},
        sequence = ZFSet.pair length graph ∧
          length ∈ omega ∧
          ∀ index : ZFSet.{u}, index ∈ length →
            ∃ value : ZFSet.{u},
              ZFSet.pair value index ∈ graph ∧
                ∀ other : ZFSet.{u},
                  ZFSet.pair other index ∈ graph → other = value := by
  simp [sequenceValidityFormula]

/-! ## External representation and decoding -/

/-- A finite list is represented by the uniquely indexed part of a code. -/
def Represents (sequence : ZFSet.{u}) (xs : List ZFSet.{u}) : Prop :=
  ∃ graph : ZFSet.{u},
    sequence = ZFSet.pair (natCode xs.length) graph ∧
      ∀ k : Fin xs.length,
        ZFSet.pair (xs.get k) (natCode k.1) ∈ graph ∧
          ∀ value : ZFSet.{u},
            ZFSet.pair value (natCode k.1) ∈ graph → value = xs.get k

/-- A genuine indexed sequence code represents its source list. -/
theorem represents_sequenceCode (xs : List ZFSet.{u}) :
    Represents (sequenceCode xs) xs := by
  refine ⟨graph xs, rfl, ?_⟩
  intro k
  constructor
  · exact (mem_graph_iff xs _).mpr ⟨k, rfl⟩
  · intro value hvalue
    rcases (mem_graph_iff xs _).mp hvalue with ⟨j, hpair⟩
    have hparts := ZFSet.pair_inj.mp hpair
    have hindex : k.1 = j.1 := natCode_injective hparts.2
    have hkj : k = j := Fin.ext hindex
    subst j
    exact hparts.1

/-- Validity is precisely representability by some finite list. -/
theorem satisfies_sequenceValidityFormula_iff_exists_represents
    (sequence : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
        ![Ordinal.omega0.toZFSet, sequence] ↔
      ∃ xs : List ZFSet.{u}, Represents sequence xs := by
  rw [satisfies_sequenceValidityFormula]
  constructor
  · rintro ⟨length, graph, hsequence, hlength, hfunctional⟩
    rcases (mem_omega_iff_exists_natCode length).mp hlength with
      ⟨n, rfl⟩
    have hvalue : ∀ k : Fin n, ∃ value : ZFSet.{u},
        ZFSet.pair value (natCode k.1) ∈ graph ∧
          ∀ other : ZFSet.{u},
            ZFSet.pair other (natCode k.1) ∈ graph → other = value := by
      intro k
      exact hfunctional (natCode k.1)
        ((mem_natCode_iff_exists_lt _ n).mpr ⟨k.1, k.2, rfl⟩)
    let valueAt : Fin n → ZFSet.{u} := fun k => Classical.choose (hvalue k)
    let xs : List ZFSet.{u} := List.ofFn valueAt
    refine ⟨xs, graph, ?_, ?_⟩
    · simpa only [xs, List.length_ofFn] using hsequence
    · intro k
      let kn : Fin n := ⟨k.1, by simpa only [xs, List.length_ofFn] using k.2⟩
      have hk := Classical.choose_spec (hvalue kn)
      simpa only [xs, List.get_ofFn, kn] using hk
  · rintro ⟨xs, graph, hsequence, hgraph⟩
    refine ⟨natCode xs.length, graph, hsequence, ?_, ?_⟩
    · exact (mem_omega_iff_exists_natCode _).mpr ⟨xs.length, rfl⟩
    · intro index hindex
      rcases (mem_natCode_iff_exists_lt index xs.length).mp hindex with
        ⟨k, hk, rfl⟩
      let i : Fin xs.length := ⟨k, hk⟩
      refine ⟨xs.get i, (hgraph i).1, ?_⟩
      exact (hgraph i).2

/-- In particular, every genuine indexed code satisfies validity. -/
theorem satisfies_sequenceValidityFormula_sequenceCode
    (xs : List ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
      ![Ordinal.omega0.toZFSet, sequenceCode xs] := by
  apply (satisfies_sequenceValidityFormula_iff_exists_represents _).mpr
  exact ⟨xs, represents_sequenceCode xs⟩

end Constructible.IndexedSequenceZF
