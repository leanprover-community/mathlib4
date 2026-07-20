/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.FiniteSequenceZF
public import Mathlib.SetTheory.ZFC.Constructible.InternalWellOrder

/-!
# A bounded formula for von Neumann successor

This file defines an arity-polymorphic bounded formula saying that one
coordinate is the von Neumann successor of another.  The formula is used for
the transition from index `k` to index `k + 1` in internally coded execution
traces.
-/

@[expose] public section

open Set

universe u

namespace Constructible

namespace Delta0Formula

/--
`successorAt succ index` says that `succ = index ∪ {index}`.

The three clauses state that `index ∈ succ`, every member of `succ` is either
a member of `index` or equal to `index`, and every member of `index` belongs
to `succ`.
-/
def successorAt {n : Nat} (succ index : Fin n) : Delta0Formula n :=
  .conj
    (.mem index succ)
    (.conj
      (.boundedAll succ
        (disj
          (.mem (Fin.last n) index.castSucc)
          (.eq (Fin.last n) index.castSucc)))
      (.boundedAll index
        (.mem (Fin.last n) succ.castSucc)))

/-- Ambient semantics of the bounded successor formula. -/
@[simp]
theorem satisfies_successorAt {n : Nat} (succ index : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (successorAt succ index) s ↔
      s succ = insert (s index) (s index) := by
  simp only [successorAt, Satisfies, satisfies_boundedAll,
    satisfies_disj, snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨hindex, hsucc, hsubset⟩
    apply ZFSet.ext
    intro x
    rw [ZFSet.mem_insert_iff]
    constructor
    · intro hx
      rcases hsucc x hx with hxIndex | hxIndex
      · exact Or.inr hxIndex
      · exact Or.inl hxIndex
    · rintro (rfl | hx)
      · exact hindex
      · exact hsubset x hx
  · intro hsuccEq
    rw [hsuccEq]
    refine ⟨ZFSet.mem_insert_iff.mpr (Or.inl rfl), ?_, ?_⟩
    · intro x hx
      rcases ZFSet.mem_insert_iff.mp hx with rfl | hx
      · exact Or.inr rfl
      · exact Or.inl hx
    · intro x hx
      exact ZFSet.mem_insert_iff.mpr (Or.inr hx)

/-- The same successor predicate in unrestricted first-order syntax. -/
def successorFOAt {n : Nat} (succ index : Fin n) : FOFormula n :=
  (successorAt succ index).toFO

/-- Ambient raw-`ZFSet` semantics of the unrestricted formula. -/
@[simp]
theorem satisfies_successorFOAt_ambient {n : Nat}
    (succ index : Fin n) (s : Tuple ZFSet.{u} n) :
    FOFormula.Satisfies ZFMem (successorFOAt succ index) s ↔
      s succ = insert (s index) (s index) := by
  rw [successorFOAt, satisfies_toFO, satisfies_successorAt]

/-- Bounded successor semantics directly on the constructible subtype. -/
@[simp]
theorem satisfies_successorAt_lCarrier {n : Nat}
    (succ index : Fin n) (s : Tuple Model.LCarrier.{u} n) :
    Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        (successorAt succ index) s ↔
      (s succ).1 = insert (s index).1 (s index).1 := by
  rw [satisfies_lCarrier_absolute]
  exact satisfies_successorAt succ index (fun i => (s i).1)

/-- First-order successor semantics directly on `LCarrier`. -/
@[simp]
theorem satisfies_successorFOAt_lCarrier {n : Nat}
    (succ index : Fin n) (s : Tuple Model.LCarrier.{u} n) :
    FOFormula.Satisfies
        (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
        (successorFOAt succ index) s ↔
      (s succ).1 = insert (s index).1 (s index).1 := by
  rw [successorFOAt, satisfies_toFO,
    satisfies_successorAt_lCarrier]

/--
Raw-domain semantics with quantifiers restricted to `L`.  Constructibility of
the whole assignment is the exact hypothesis needed to invoke bounded
absoluteness.
-/
@[simp]
theorem satisfiesIn_L_successorFOAt {n : Nat}
    (succ index : Fin n) (s : Tuple ZFSet.{u} n)
    (hs : ∀ i, s i ∈ L) :
    Model.SatisfiesIn L (successorFOAt succ index) s ↔
      s succ = insert (s index) (s index) := by
  let sL : Tuple Model.LCarrier.{u} n := fun i => ⟨s i, hs i⟩
  have hbridge :=
    Model.satisfies_lCarrier_iff_satisfiesIn_L
      (successorFOAt succ index) sL
  have hbridgeRaw :
      FOFormula.Satisfies
          (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
          (successorFOAt succ index) sL ↔
        Model.SatisfiesIn L (successorFOAt succ index) s := by
    simpa only [sL] using hbridge
  have hsemantic := satisfies_successorFOAt_lCarrier succ index sL
  have hsemanticRaw :
      FOFormula.Satisfies
          (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
          (successorFOAt succ index) sL ↔
        s succ = insert (s index) (s index) := by
    simpa only [sL] using hsemantic
  exact hbridgeRaw.symm.trans hsemanticRaw

end Delta0Formula

namespace FiniteSequenceZF

/-- The von Neumann code of `k + 1` is the successor of the code of `k`. -/
theorem natCode_succ_eq_insert (k : Nat) :
    (natCode (k + 1) : ZFSet.{u}) =
      insert (natCode k) (natCode k) := by
  simp only [natCode, Nat.cast_add, Nat.cast_one,
    Ordinal.toZFSet_add_one]

/-- The bounded successor formula holds on consecutive natural codes. -/
theorem satisfies_successorAt_natCode (k : Nat) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
      (Delta0Formula.successorAt (0 : Fin 2) (1 : Fin 2))
      ![(natCode (k + 1) : ZFSet.{u}), natCode k] := by
  rw [Delta0Formula.satisfies_successorAt]
  exact natCode_succ_eq_insert k

/-- The unrestricted successor formula holds on consecutive natural codes. -/
theorem satisfies_successorFOAt_natCode (k : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem
      (Delta0Formula.successorFOAt (0 : Fin 2) (1 : Fin 2))
      ![(natCode (k + 1) : ZFSet.{u}), natCode k] := by
  rw [Delta0Formula.satisfies_successorFOAt_ambient]
  exact natCode_succ_eq_insert k

/-- Consecutive natural codes, packaged as an assignment in `LCarrier`. -/
noncomputable def successorNatCodeLAssignment (k : Nat) :
    Tuple Model.LCarrier.{u} 2 :=
  ![⟨natCode (k + 1), natCode_mem_L (k + 1)⟩,
    ⟨natCode k, natCode_mem_L k⟩]

/-- The successor formula on consecutive natural codes inside `LCarrier`. -/
theorem satisfies_successorFOAt_natCode_lCarrier (k : Nat) :
    FOFormula.Satisfies
      (fun x y : Model.LCarrier.{u} => x.1 ∈ y.1)
      (Delta0Formula.successorFOAt (0 : Fin 2) (1 : Fin 2))
      (successorNatCodeLAssignment k) := by
  rw [Delta0Formula.satisfies_successorFOAt_lCarrier]
  exact natCode_succ_eq_insert k

/-- The same natural-code fact in raw satisfaction restricted to `L`. -/
theorem satisfiesIn_L_successorFOAt_natCode (k : Nat) :
    Model.SatisfiesIn L
      (Delta0Formula.successorFOAt (0 : Fin 2) (1 : Fin 2))
      ![(natCode (k + 1) : ZFSet.{u}), natCode k] := by
  rw [Delta0Formula.satisfiesIn_L_successorFOAt]
  · exact natCode_succ_eq_insert k
  · intro i
    fin_cases i
    · exact natCode_mem_L (k + 1)
    · exact natCode_mem_L k

end FiniteSequenceZF

end Constructible
