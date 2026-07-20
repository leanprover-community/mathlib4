/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.FiniteSequenceComparison
public import Mathlib.SetTheory.ZFC.Constructible.IndexedSequenceZF
public import Mathlib.SetTheory.ZFC.Constructible.IndexedSequenceValidity

/-!
# First-order comparison of indexed finite-sequence codes

This file gives fixed object-language formulas for reading the indexed graph
stored by `IndexedSequenceZF.sequenceCode`, comparing prefixes, and building
shortlex comparisons. It uses the indexed representation throughout.
-/

@[expose] public section

universe u

namespace Constructible.IndexedSequenceZF

open FiniteSequenceZF

/-! ## Indexed access -/

/-- With assignment `[relation,output,input]`, assert `<output,input> ∈ relation`. -/
def graphPairMemAt {n : Nat} (relation output input : Fin n) :
    Delta0Formula n :=
  .boundedEx relation
    (Delta0Formula.kuratowskiPairEqAt
      (Fin.last n) output.castSucc input.castSucc)

@[simp]
theorem satisfies_graphPairMemAt {n : Nat} (relation output input : Fin n)
    (s : Tuple ZFSet.{u} n) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem
        (graphPairMemAt relation output input) s ↔
      ZFSet.pair (s output) (s input) ∈ s relation := by
  simp only [graphPairMemAt, Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    snoc_last, snoc_castSucc]
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact hq
  · intro hq
    exact ⟨ZFSet.pair (s output) (s input), hq, rfl⟩

/--
Supply bounded candidates for the two components of a Kuratowski pair.

If coordinate `pair` is `{{left},{left,right}}`, the four witnesses are the
left singleton, `left`, the unordered pair, and `right`, respectively.
-/
def withBoundedKuratowskiComponents {n : Nat} (pair : Fin n)
    (body : Delta0Formula (n + 4)) : Delta0Formula n :=
  .boundedEx pair
    (.boundedEx (Fin.last n)
      (.boundedEx pair.castSucc.castSucc
        (.boundedEx (Fin.last (n + 2)) body)))

@[simp]
theorem satisfies_withBoundedKuratowskiComponents {A : Type u}
    (E : A → A → Prop) {n : Nat} (pair : Fin n)
    (body : Delta0Formula (n + 4)) (s : Tuple A n) :
    Delta0Formula.Satisfies E
        (withBoundedKuratowskiComponents pair body) s ↔
      ∃ leftBox : A, E leftBox (s pair) ∧
        ∃ left : A, E left leftBox ∧
          ∃ rightBox : A, E rightBox (s pair) ∧
            ∃ right : A, E right rightBox ∧
              Delta0Formula.Satisfies E body
                (snoc (snoc (snoc (snoc s leftBox) left)
                  rightBox) right) := by
  simp only [withBoundedKuratowskiComponents, Delta0Formula.Satisfies,
    snoc_last, snoc_castSucc]

/--
Read one entry from an indexed sequence code.

The assignment layout is `[sequence,index,value]`.  The formula first decodes
`sequence = <length,graph>` and then checks `<value,index> ∈ graph`.
-/
def valueAtDelta0 : Delta0Formula 3 :=
  withBoundedKuratowskiComponents 0
    (.conj
      (Delta0Formula.kuratowskiPairEqAt 0 4 6)
      (.conj (.mem 1 4) (graphPairMemAt 6 2 1)))

/-- The indexed-access predicate in the unrestricted formula syntax. -/
def valueAtFormula : FOFormula 3 :=
  valueAtDelta0.toFO

@[simp]
theorem satisfies_valueAtDelta0 (sequence index value : ZFSet.{u}) :
    Delta0Formula.Satisfies Delta0Formula.ZFMem valueAtDelta0
        ![sequence, index, value] ↔
      ∃ length graph : ZFSet.{u},
        sequence = ZFSet.pair length graph ∧
          index ∈ length ∧ ZFSet.pair value index ∈ graph := by
  simp only [valueAtDelta0,
    satisfies_withBoundedKuratowskiComponents,
    Delta0Formula.Satisfies,
    Delta0Formula.satisfies_kuratowskiPairEqAt,
    satisfies_graphPairMemAt]
  constructor
  · rintro ⟨leftBox, hleftBox, length, hlength,
      rightBox, hrightBox, graph, hgraph, hsequence, hindex, hvalue⟩
    exact ⟨length, graph, hsequence, hindex, hvalue⟩
  · rintro ⟨length, graph, hsequence, hindex, hvalue⟩
    refine ⟨{length}, ?_, length, ?_, {length, graph}, ?_, graph, ?_,
      ?_, ?_, ?_⟩
    · simp [hsequence, ZFSet.pair]
    · simp
    · simp [hsequence, ZFSet.pair]
    · simp
    · change sequence = ZFSet.pair length graph
      exact hsequence
    · change index ∈ length
      exact hindex
    · change ZFSet.pair value index ∈ graph
      exact hvalue

@[simp]
theorem satisfies_valueAtFormula (sequence index value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![sequence, index, value] ↔
      ∃ length graph : ZFSet.{u},
        sequence = ZFSet.pair length graph ∧
          index ∈ length ∧ ZFSet.pair value index ∈ graph := by
  rw [valueAtFormula, Delta0Formula.satisfies_toFO,
    satisfies_valueAtDelta0]

theorem satisfies_valueAt_sequenceCode_iff (xs : List ZFSet.{u})
    (k : Nat) (value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![sequenceCode xs, natCode k, value] ↔
      ∃ hk : k < xs.length, value = xs.get ⟨k, hk⟩ := by
  rw [satisfies_valueAtFormula]
  constructor
  · rintro ⟨length, relation, hcode, hindex, hmem⟩
    have hparts := ZFSet.pair_inj.mp hcode
    rw [← hparts.2] at hmem
    rcases (mem_graph_iff xs _).mp hmem with ⟨i, hpair⟩
    have hpairParts := ZFSet.pair_inj.mp hpair
    have hk : k < xs.length := by
      have hki : k = i.1 := natCode_injective hpairParts.2
      simpa only [hki] using i.2
    refine ⟨hk, ?_⟩
    have hki : k = i.1 := natCode_injective hpairParts.2
    simpa only [hki] using hpairParts.1
  · rintro ⟨hk, rfl⟩
    refine ⟨natCode xs.length, graph xs, rfl,
      (natCode_mem_natCode_iff k xs.length).mpr hk, ?_⟩
    exact (mem_graph_iff xs _).mpr ⟨⟨k, hk⟩, rfl⟩

/-- Indexed access is sound for every code satisfying the representation invariant. -/
theorem satisfies_valueAt_represents_iff {sequence : ZFSet.{u}}
    {xs : List ZFSet.{u}} (hrep : Represents sequence xs)
    (k : Nat) (value : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![sequence, natCode k, value] ↔
      ∃ hk : k < xs.length, value = xs.get ⟨k, hk⟩ := by
  rcases hrep with ⟨relation, hsequence, hgraph⟩
  rw [satisfies_valueAtFormula]
  constructor
  · rintro ⟨length, graph', hcode, hindex, hvalue⟩
    have hparts := ZFSet.pair_inj.mp (hsequence.symm.trans hcode)
    rw [← hparts.1] at hindex
    rw [← hparts.2] at hvalue
    have hk : k < xs.length :=
      (natCode_mem_natCode_iff k xs.length).mp hindex
    exact ⟨hk, (hgraph ⟨k, hk⟩).2 value hvalue⟩
  · rintro ⟨hk, hvalue⟩
    refine ⟨natCode xs.length, relation, hsequence,
      (natCode_mem_natCode_iff k xs.length).mpr hk, ?_⟩
    simpa only [hvalue] using (hgraph ⟨k, hk⟩).1

/-! ## Equal prefixes -/

/-- The members of a finite von Neumann ordinal are exactly earlier codes. -/
@[simp]
theorem mem_natCode_iff (index : ZFSet.{u}) (k : Nat) :
    index ∈ natCode k ↔
      ∃ j : Nat, j < k ∧ index = natCode j := by
  constructor
  · intro hindex
    change index ∈ (k : Ordinal.{u}).toZFSet at hindex
    rcases Ordinal.mem_toZFSet_iff.mp hindex with ⟨beta, hbeta, rfl⟩
    have hbetaOmega : beta < Ordinal.omega0 :=
      hbeta.trans (Ordinal.natCast_lt_omega0 k)
    rcases Ordinal.lt_omega0.mp hbetaOmega with ⟨j, rfl⟩
    refine ⟨j, ?_, rfl⟩
    exact_mod_cast hbeta
  · rintro ⟨j, hj, rfl⟩
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (by exact_mod_cast hj)

/--
All entries before a coded bound agree.

The assignment layout is `[leftSequence,rightSequence,bound]`.  For every
internal index in `bound`, one common value must be readable from both indexed
graphs.
-/
def samePrefixFormula : FOFormula 3 :=
  FOFormula.boundedAll 2
    (.ex (.conj
      (FOFormula.rename
        ![(0 : Fin 5), (3 : Fin 5), (4 : Fin 5)] valueAtFormula)
      (FOFormula.rename
        ![(1 : Fin 5), (3 : Fin 5), (4 : Fin 5)] valueAtFormula)))

@[simp]
theorem satisfies_samePrefixFormula
    (leftSequence rightSequence bound : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem samePrefixFormula
        ![leftSequence, rightSequence, bound] ↔
      ∀ index : ZFSet.{u}, index ∈ bound →
        ∃ value : ZFSet.{u},
          FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
              ![leftSequence, index, value] ∧
            FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
              ![rightSequence, index, value] := by
  simp only [samePrefixFormula, FOFormula.satisfies_boundedAll,
    FOFormula.Satisfies, FOFormula.satisfies_rename]
  constructor
  · intro h index hindex
    rcases h index hindex with ⟨value, hleft, hright⟩
    refine ⟨value, ?_, ?_⟩
    · change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![leftSequence, index, value] at hleft
      exact hleft
    · change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        ![rightSequence, index, value] at hright
      exact hright
  · intro h index hindex
    rcases h index hindex with ⟨value, hleft, hright⟩
    refine ⟨value, ?_, ?_⟩
    · change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        (fun i => snoc (snoc ![leftSequence, rightSequence, bound] index) value
          (![0, 3, 4] i))
      exact hleft
    · change FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
        (fun i => snoc (snoc ![leftSequence, rightSequence, bound] index) value
          (![1, 3, 4] i))
      exact hright

theorem satisfies_samePrefix_sequenceCode_iff
    (xs ys : List ZFSet.{u}) (k : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem samePrefixFormula
        ![sequenceCode xs, sequenceCode ys, natCode k] ↔
      ∀ j : Nat, j < k →
        ∃ hx : j < xs.length, ∃ hy : j < ys.length,
          xs.get ⟨j, hx⟩ = ys.get ⟨j, hy⟩ := by
  rw [satisfies_samePrefixFormula]
  constructor
  · intro h j hj
    rcases h (natCode j) (mem_natCode_iff _ _ |>.2 ⟨j, hj, rfl⟩) with
      ⟨value, hleft, hright⟩
    rcases (satisfies_valueAt_sequenceCode_iff xs j value).mp hleft with
      ⟨hx, hvalueX⟩
    rcases (satisfies_valueAt_sequenceCode_iff ys j value).mp hright with
      ⟨hy, hvalueY⟩
    exact ⟨hx, hy, hvalueX.symm.trans hvalueY⟩
  · intro h index hindex
    rcases (mem_natCode_iff index k).mp hindex with ⟨j, hj, rfl⟩
    rcases h j hj with ⟨hx, hy, hxy⟩
    refine ⟨xs.get ⟨j, hx⟩, ?_, ?_⟩
    · exact (satisfies_valueAt_sequenceCode_iff xs j _).mpr ⟨hx, rfl⟩
    · exact (satisfies_valueAt_sequenceCode_iff ys j _).mpr
        ⟨hy, hxy⟩

/-- Prefix comparison is sound for arbitrary represented sequence codes. -/
theorem satisfies_samePrefix_represents_iff
    {leftSequence rightSequence : ZFSet.{u}}
    {xs ys : List ZFSet.{u}}
    (hleft : Represents leftSequence xs)
    (hright : Represents rightSequence ys) (k : Nat) :
    FOFormula.Satisfies Delta0Formula.ZFMem samePrefixFormula
        ![leftSequence, rightSequence, natCode k] ↔
      ∀ j : Nat, j < k →
        ∃ hx : j < xs.length, ∃ hy : j < ys.length,
          xs.get ⟨j, hx⟩ = ys.get ⟨j, hy⟩ := by
  rw [satisfies_samePrefixFormula]
  constructor
  · intro h j hj
    rcases h (natCode j) ((mem_natCode_iff _ _).mpr ⟨j, hj, rfl⟩) with
      ⟨value, hvalueLeft, hvalueRight⟩
    rcases (satisfies_valueAt_represents_iff hleft j value).mp
        hvalueLeft with ⟨hx, hvalueX⟩
    rcases (satisfies_valueAt_represents_iff hright j value).mp
        hvalueRight with ⟨hy, hvalueY⟩
    exact ⟨hx, hy, hvalueX.symm.trans hvalueY⟩
  · intro h index hindex
    rcases (mem_natCode_iff index k).mp hindex with ⟨j, hj, rfl⟩
    rcases h j hj with ⟨hx, hy, hxy⟩
    refine ⟨xs.get ⟨j, hx⟩, ?_, ?_⟩
    · exact (satisfies_valueAt_represents_iff hleft j _).mpr ⟨hx, rfl⟩
    · exact (satisfies_valueAt_represents_iff hright j _).mpr ⟨hy, hxy⟩

/-- Pointwise agreement below `k` is equivalent to equality of `take k`. -/
theorem take_eq_take_iff_pointwise (xs ys : List ZFSet.{u}) (k : Nat)
    (hkx : k ≤ xs.length) (hky : k ≤ ys.length) :
    xs.take k = ys.take k ↔
      ∀ j : Nat, j < k →
        ∃ hx : j < xs.length, ∃ hy : j < ys.length,
          xs.get ⟨j, hx⟩ = ys.get ⟨j, hy⟩ := by
  constructor
  · intro htake j hj
    have hx : j < xs.length := hj.trans_le hkx
    have hy : j < ys.length := hj.trans_le hky
    have hjx : j < (xs.take k).length := by
      simpa only [List.length_take, Nat.min_eq_left hkx] using hj
    have hjy : j < (ys.take k).length := by
      simpa only [List.length_take, Nat.min_eq_left hky] using hj
    have hget :
        (xs.take k).get ⟨j, hjx⟩ =
          (ys.take k).get ⟨j, hjy⟩ := by
      have hoption := congrArg (fun zs : List ZFSet.{u} => zs[j]?) htake
      change (xs.take k)[j]? = (ys.take k)[j]? at hoption
      rw [List.getElem?_eq_getElem hjx,
        List.getElem?_eq_getElem hjy] at hoption
      exact Option.some.inj hoption
    refine ⟨hx, hy, ?_⟩
    simpa using hget
  · intro hpoint
    apply List.ext_get
    · simp only [List.length_take, Nat.min_eq_left hkx,
        Nat.min_eq_left hky]
    · intro j hjx hjy
      have hj : j < k := by
        simpa only [List.length_take, Nat.min_eq_left hkx] using hjx
      rcases hpoint j hj with ⟨hx, hy, hget⟩
      simpa using hget

/-- On genuine codes and an in-range bound, `samePrefixFormula` means `take` equality. -/
theorem satisfies_samePrefix_sequenceCode_iff_take
    (xs ys : List ZFSet.{u}) (k : Nat)
    (hkx : k ≤ xs.length) (hky : k ≤ ys.length) :
    FOFormula.Satisfies Delta0Formula.ZFMem samePrefixFormula
        ![sequenceCode xs, sequenceCode ys, natCode k] ↔
      xs.take k = ys.take k := by
  rw [satisfies_samePrefix_sequenceCode_iff,
    take_eq_take_iff_pointwise xs ys k hkx hky]

/-! ## Shortlex -/

/-- With assignment `[sequence,length]`, decode the recorded length. -/
def hasLengthFormula : FOFormula 2 :=
  .ex (Delta0Formula.kuratowskiPairEqAt 0 1 2).toFO

@[simp]
theorem satisfies_hasLengthFormula (sequence length : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
        ![sequence, length] ↔
      ∃ graph : ZFSet.{u}, sequence = ZFSet.pair length graph := by
  simp [hasLengthFormula]

theorem satisfies_hasLength_sequenceCode_iff
    (xs : List ZFSet.{u}) (length : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
        ![sequenceCode xs, length] ↔
      length = natCode xs.length := by
  rw [satisfies_hasLengthFormula]
  constructor
  · rintro ⟨graph', hcode⟩
    exact (ZFSet.pair_inj.mp hcode).1.symm
  · rintro rfl
    exact ⟨graph xs, rfl⟩

theorem satisfies_hasLength_represents_iff {sequence : ZFSet.{u}}
    {xs : List ZFSet.{u}} (hrep : Represents sequence xs)
    (length : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
        ![sequence, length] ↔
      length = natCode xs.length := by
  rcases hrep with ⟨graph, hsequence, _hgraph⟩
  rw [satisfies_hasLengthFormula]
  constructor
  · rintro ⟨graph', hcode⟩
    exact (ZFSet.pair_inj.mp (hsequence.symm.trans hcode)).1.symm
  · rintro rfl
    exact ⟨graph, hsequence⟩

/-
For `tokenLt : FOFormula (parameterCount + 2)`, the two last coordinates are
the compared values.  The resulting shortlex formula has layout

`[token parameters..., omega, leftSequence, rightSequence]`.
-/

/-- Select the omega and left-sequence coordinates for the validity formula. -/
def validityLeftRename (parameterCount : Nat) :
    Fin 2 → Fin (parameterCount + 3) :=
  ![(Fin.last parameterCount).castSucc.castSucc,
    (Fin.last (parameterCount + 1)).castSucc]

/-- Select the omega and right-sequence coordinates for the validity formula. -/
def validityRightRename (parameterCount : Nat) :
    Fin 2 → Fin (parameterCount + 3) :=
  ![(Fin.last parameterCount).castSucc.castSucc,
    Fin.last (parameterCount + 2)]

/-- Select the left sequence and its length coordinate. -/
def leftLengthRename (parameterCount : Nat) :
    Fin 2 → Fin (parameterCount + 5) :=
  ![(Fin.last (parameterCount + 1)).castSucc.castSucc.castSucc,
    (Fin.last (parameterCount + 3)).castSucc]

/-- Select the right sequence and its length coordinate. -/
def rightLengthRename (parameterCount : Nat) :
    Fin 2 → Fin (parameterCount + 5) :=
  ![(Fin.last (parameterCount + 2)).castSucc.castSucc,
    Fin.last (parameterCount + 4)]

/-- Select both sequences and the current prefix index. -/
def prefixRename (parameterCount : Nat) :
    Fin 3 → Fin (parameterCount + 6) :=
  ![(Fin.last (parameterCount + 1)).castSucc.castSucc.castSucc.castSucc,
    (Fin.last (parameterCount + 2)).castSucc.castSucc.castSucc,
    Fin.last (parameterCount + 5)]

/-- Select the left sequence, index, and decoded value. -/
def leftValueRename (parameterCount : Nat) :
    Fin 3 → Fin (parameterCount + 8) :=
  ![(Fin.last (parameterCount + 1)).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc,
    (Fin.last (parameterCount + 5)).castSucc.castSucc,
    (Fin.last (parameterCount + 6)).castSucc]

/-- Select the right sequence, index, and decoded value. -/
def rightValueRename (parameterCount : Nat) :
    Fin 3 → Fin (parameterCount + 8) :=
  ![(Fin.last (parameterCount + 2)).castSucc.castSucc.castSucc.castSucc.castSucc,
    (Fin.last (parameterCount + 5)).castSucc.castSucc,
    Fin.last (parameterCount + 7)]

/-- Select the two decoded token values for comparison. -/
def tokenLtRename (parameterCount : Nat) :
    Fin (parameterCount + 2) → Fin (parameterCount + 8) :=
  Fin.lastCases (Fin.last (parameterCount + 7))
    (fun j => Fin.lastCases (Fin.last (parameterCount + 6)).castSucc
      (fun i =>
        i.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc)
      j)

theorem comp_validityLeftRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount) (omega left right : A) :
    (fun i => snoc (snoc (snoc params omega) left) right
      (validityLeftRename parameterCount i)) = ![omega, left] := by
  funext i
  fin_cases i <;> simp [validityLeftRename]

theorem comp_validityRightRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount) (omega left right : A) :
    (fun i => snoc (snoc (snoc params omega) left) right
      (validityRightRename parameterCount i)) = ![omega, right] := by
  funext i
  fin_cases i <;> simp [validityRightRename]

theorem comp_leftLengthRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount)
    (omega left right leftLength rightLength : A) :
    (fun i =>
      snoc (snoc (snoc (snoc (snoc params omega) left) right)
        leftLength) rightLength (leftLengthRename parameterCount i)) =
      ![left, leftLength] := by
  funext i
  fin_cases i <;> simp [leftLengthRename]

theorem comp_rightLengthRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount)
    (omega left right leftLength rightLength : A) :
    (fun i =>
      snoc (snoc (snoc (snoc (snoc params omega) left) right)
        leftLength) rightLength (rightLengthRename parameterCount i)) =
      ![right, rightLength] := by
  funext i
  fin_cases i <;> simp [rightLengthRename]

theorem comp_prefixRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount)
    (omega left right leftLength rightLength index : A) :
    (fun i =>
      snoc (snoc (snoc (snoc (snoc (snoc params omega) left) right)
        leftLength) rightLength) index (prefixRename parameterCount i)) =
      ![left, right, index] := by
  funext i
  fin_cases i <;> simp [prefixRename]

theorem comp_leftValueRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount)
    (omega left right leftLength rightLength index leftValue rightValue : A) :
    (fun i =>
      snoc (snoc
        (snoc (snoc (snoc (snoc (snoc (snoc params omega) left) right)
          leftLength) rightLength) index) leftValue) rightValue
        (leftValueRename parameterCount i)) =
      ![left, index, leftValue] := by
  funext i
  fin_cases i <;> simp [leftValueRename]

theorem comp_rightValueRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount)
    (omega left right leftLength rightLength index leftValue rightValue : A) :
    (fun i =>
      snoc (snoc
        (snoc (snoc (snoc (snoc (snoc (snoc params omega) left) right)
          leftLength) rightLength) index) leftValue) rightValue
        (rightValueRename parameterCount i)) =
      ![right, index, rightValue] := by
  funext i
  fin_cases i <;> simp [rightValueRename]

theorem comp_tokenLtRename {A : Type u} {parameterCount : Nat}
    (params : Tuple A parameterCount)
    (omega left right leftLength rightLength index leftValue rightValue : A) :
    (fun i =>
      snoc (snoc
        (snoc (snoc (snoc (snoc (snoc (snoc params omega) left) right)
          leftLength) rightLength) index) leftValue) rightValue
        (tokenLtRename parameterCount i)) =
      snoc (snoc params leftValue) rightValue := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [tokenLtRename]
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [tokenLtRename]
    · simp [tokenLtRename]

/-- The body after the two recorded lengths have been decoded. -/
def shortlexCore {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2)) :
    FOFormula (parameterCount + 5) :=
  .conj
    (FOFormula.rename (leftLengthRename parameterCount) hasLengthFormula)
    (.conj
      (FOFormula.rename (rightLengthRename parameterCount) hasLengthFormula)
      (FOFormula.disj
        (.mem (Fin.last (parameterCount + 3)).castSucc
          (Fin.last (parameterCount + 4)))
        (.conj
          (.eq (Fin.last (parameterCount + 3)).castSucc
            (Fin.last (parameterCount + 4)))
          (FOFormula.boundedEx (Fin.last (parameterCount + 3)).castSucc
            (.conj
              (FOFormula.rename (prefixRename parameterCount)
                samePrefixFormula)
              (.ex (.ex
                (.conj
                  (FOFormula.rename (leftValueRename parameterCount)
                    valueAtFormula)
                  (.conj
                    (FOFormula.rename (rightValueRename parameterCount)
                      valueAtFormula)
                    (FOFormula.rename (tokenLtRename parameterCount)
                      tokenLt))))))))))

/--
Validity-guarded shortlex comparison of two indexed sequence codes.

The free assignment is `[token parameters..., omega, leftSequence,
rightSequence]`.  The final two variables of `tokenLt` receive the entries at
the first differing index.
-/
def shortlexFormula {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2)) :
    FOFormula (parameterCount + 3) :=
  .conj
    (FOFormula.rename (validityLeftRename parameterCount)
      sequenceValidityFormula)
    (.conj
      (FOFormula.rename (validityRightRename parameterCount)
        sequenceValidityFormula)
      (.ex (.ex (shortlexCore tokenLt))))

theorem satisfies_shortlexFormula {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2))
    (params : Tuple ZFSet.{u} parameterCount)
    (omega leftSequence rightSequence : ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem (shortlexFormula tokenLt)
        (snoc (snoc (snoc params omega) leftSequence) rightSequence) ↔
      FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
          ![omega, leftSequence] ∧
        FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
          ![omega, rightSequence] ∧
        ∃ leftLength rightLength : ZFSet.{u},
          FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
              ![leftSequence, leftLength] ∧
            FOFormula.Satisfies Delta0Formula.ZFMem hasLengthFormula
              ![rightSequence, rightLength] ∧
            (leftLength ∈ rightLength ∨
              leftLength = rightLength ∧
                ∃ index : ZFSet.{u}, index ∈ leftLength ∧
                  FOFormula.Satisfies Delta0Formula.ZFMem samePrefixFormula
                      ![leftSequence, rightSequence, index] ∧
                    ∃ leftValue rightValue : ZFSet.{u},
                      FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
                          ![leftSequence, index, leftValue] ∧
                        FOFormula.Satisfies Delta0Formula.ZFMem valueAtFormula
                          ![rightSequence, index, rightValue] ∧
                        FOFormula.Satisfies Delta0Formula.ZFMem tokenLt
                          (snoc (snoc params leftValue) rightValue)) := by
  simp only [shortlexFormula, shortlexCore, FOFormula.Satisfies,
    FOFormula.satisfies_rename, FOFormula.satisfies_disj,
    FOFormula.satisfies_boundedEx, comp_validityLeftRename,
    comp_validityRightRename, comp_leftLengthRename,
    comp_rightLengthRename, comp_prefixRename, comp_leftValueRename,
    comp_rightValueRename, comp_tokenLtRename, snoc_last, snoc_castSucc]

/--
Semantic correctness on any two valid representations.  The supplied token
formula may use the preceding parameter tuple; its final two coordinates are
interpreted by `R`.
-/
theorem satisfies_shortlexFormula_represents_iff
    {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2))
    (params : Tuple ZFSet.{u} parameterCount)
    (R : ZFSet.{u} → ZFSet.{u} → Prop)
    {leftSequence rightSequence : ZFSet.{u}}
    {xs ys : List ZFSet.{u}}
    (hleft : Represents leftSequence xs)
    (hright : Represents rightSequence ys)
    (htoken : ∀ leftValue rightValue : ZFSet.{u},
      FOFormula.Satisfies Delta0Formula.ZFMem tokenLt
          (snoc (snoc params leftValue) rightValue) ↔
        R leftValue rightValue) :
    FOFormula.Satisfies Delta0Formula.ZFMem (shortlexFormula tokenLt)
        (snoc (snoc (snoc params Ordinal.omega0.toZFSet)
          leftSequence) rightSequence) ↔
      List.Shortlex R xs ys := by
  rw [satisfies_shortlexFormula]
  have hvalidLeft :
      FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
        ![Ordinal.omega0.toZFSet, leftSequence] :=
    (satisfies_sequenceValidityFormula_iff_exists_represents leftSequence).mpr
      ⟨xs, hleft⟩
  have hvalidRight :
      FOFormula.Satisfies Delta0Formula.ZFMem sequenceValidityFormula
        ![Ordinal.omega0.toZFSet, rightSequence] :=
    (satisfies_sequenceValidityFormula_iff_exists_represents rightSequence).mpr
      ⟨ys, hright⟩
  constructor
  · rintro ⟨_hvalidLeft, _hvalidRight, leftLength, rightLength,
      hleftLength, hrightLength, hshort⟩
    have hleftLengthEq :=
      (satisfies_hasLength_represents_iff hleft leftLength).mp hleftLength
    have hrightLengthEq :=
      (satisfies_hasLength_represents_iff hright rightLength).mp hrightLength
    subst leftLength
    subst rightLength
    rcases hshort with hlength | ⟨hlengthCode, index, hindex,
        hprefix, leftValue, rightValue, hleftValue, hrightValue, hlt⟩
    · exact List.Shortlex.of_length_lt
        ((natCode_mem_natCode_iff xs.length ys.length).mp hlength)
    · have hlength : xs.length = ys.length :=
        natCode_injective hlengthCode
      rcases (mem_natCode_iff index xs.length).mp hindex with
        ⟨k, hk, rfl⟩
      have hpoint :=
        (satisfies_samePrefix_represents_iff hleft hright k).mp hprefix
      have hkRightLe : k ≤ ys.length := by
        rw [← hlength]
        exact hk.le
      have htake : xs.take k = ys.take k :=
        (take_eq_take_iff_pointwise xs ys k hk.le hkRightLe).mpr hpoint
      rcases (satisfies_valueAt_represents_iff hleft k leftValue).mp
          hleftValue with ⟨hkx, hleftValueEq⟩
      rcases (satisfies_valueAt_represents_iff hright k rightValue).mp
          hrightValue with ⟨hky, hrightValueEq⟩
      have hrelation :
          R (xs.get ⟨k, hkx⟩) (ys.get ⟨k, hky⟩) := by
        apply (htoken leftValue rightValue).mp at hlt
        simpa only [hleftValueEq, hrightValueEq] using hlt
      apply List.Shortlex.of_lex hlength
      apply (listLex_iff_exists_index hlength).mpr
      exact ⟨k, hkx, hky, htake, hrelation⟩
  · intro hshortlex
    refine ⟨hvalidLeft, hvalidRight, natCode xs.length,
      natCode ys.length, ?_, ?_, ?_⟩
    · exact (satisfies_hasLength_represents_iff hleft _).mpr rfl
    · exact (satisfies_hasLength_represents_iff hright _).mpr rfl
    · rcases List.shortlex_def.mp hshortlex with hlength | ⟨hlength, hlex⟩
      · exact Or.inl
          ((natCode_mem_natCode_iff xs.length ys.length).mpr hlength)
      · apply Or.inr
        refine ⟨congrArg natCode hlength, ?_⟩
        rcases (listLex_iff_exists_index hlength).mp hlex with
          ⟨k, hkx, hky, htake, hrelation⟩
        refine ⟨natCode k,
          (natCode_mem_natCode_iff k xs.length).mpr hkx, ?_,
          xs.get ⟨k, hkx⟩, ys.get ⟨k, hky⟩, ?_, ?_, ?_⟩
        · apply (satisfies_samePrefix_represents_iff hleft hright k).mpr
          exact (take_eq_take_iff_pointwise xs ys k hkx.le hky.le).mp htake
        · exact (satisfies_valueAt_represents_iff hleft k _).mpr
            ⟨hkx, rfl⟩
        · exact (satisfies_valueAt_represents_iff hright k _).mpr
            ⟨hky, rfl⟩
        · exact (htoken _ _).mpr hrelation

/-- The advertised specialization to the canonical indexed sequence codes. -/
theorem satisfies_shortlexFormula_sequenceCode_iff
    {parameterCount : Nat}
    (tokenLt : FOFormula (parameterCount + 2))
    (params : Tuple ZFSet.{u} parameterCount)
    (R : ZFSet.{u} → ZFSet.{u} → Prop)
    (htoken : ∀ leftValue rightValue : ZFSet.{u},
      FOFormula.Satisfies Delta0Formula.ZFMem tokenLt
          (snoc (snoc params leftValue) rightValue) ↔
        R leftValue rightValue)
    (xs ys : List ZFSet.{u}) :
    FOFormula.Satisfies Delta0Formula.ZFMem (shortlexFormula tokenLt)
        (snoc (snoc (snoc params Ordinal.omega0.toZFSet)
          (sequenceCode xs)) (sequenceCode ys)) ↔
      List.Shortlex R xs ys :=
  satisfies_shortlexFormula_represents_iff tokenLt params R
    (represents_sequenceCode xs) (represents_sequenceCode ys) htoken

end Constructible.IndexedSequenceZF
