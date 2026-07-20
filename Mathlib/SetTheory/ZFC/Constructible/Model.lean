/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Def
public import Mathlib.SetTheory.ZFC.Constructible.Semantics

/-!
# The first-order structure carried by the constructible universe

This file connects the formula syntax used to construct `L` with Mathlib's
general model-theory API.  The language has no function symbols and one binary
relation symbol, interpreted as membership.

The existing `Constructible.FOFormula n` treats all `n` variables uniformly
and appends a bound variable at the end of a tuple.  Mathlib's
`BoundedFormula Empty n` has exactly the same convention, so the translation
below does not need a variable permutation.
-/

@[expose] public section

open Set

universe u

namespace Constructible

namespace Model

/-! ## Raw-domain semantics for external classes -/

/--
Satisfaction with quantifiers restricted to an external class of `ZFSet`s.

Assignments remain raw `ZFSet` tuples.  This is the useful presentation for
comparing two domains such as `LStageZF alpha` and `L`, since the same tuple can
be passed to both sides without transporting subtype values.
-/
@[simp]
def SatisfiesIn (M : Set ZFSet.{u}) :
    {n : Nat} -> FOFormula n -> Tuple ZFSet.{u} n -> Prop
  | _, .mem i j, s => s i ∈ s j
  | _, .eq i j, s => s i = s j
  | _, .neg phi, s => ¬SatisfiesIn M phi s
  | _, .conj phi psi, s => SatisfiesIn M phi s ∧ SatisfiesIn M psi s
  | _, .ex phi, s => ∃ x, x ∈ M ∧ SatisfiesIn M phi (snoc s x)

/-- The subtype whose elements range over an external class `M`. -/
abbrev ClassCarrier (M : Set ZFSet.{u}) := {x : ZFSet.{u} // x ∈ M}

theorem subtypeVal_snoc {M : Set ZFSet.{u}} {n : Nat}
    (s : Tuple (ClassCarrier M) n) (x : ClassCarrier M) :
    (fun i => (snoc s x i).1) = snoc (fun i => (s i).1) x.1 := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

/--
Raw-domain restricted satisfaction is equivalent to ordinary satisfaction on
the subtype carrying exactly the elements of `M`.
-/
theorem satisfies_subtype_iff_satisfiesIn (M : Set ZFSet.{u}) {n : Nat}
    (phi : FOFormula n) (s : Tuple (ClassCarrier M) n) :
    FOFormula.Satisfies
        (fun x y : ClassCarrier M => x.1 ∈ y.1) phi s ↔
      SatisfiesIn M phi (fun i => (s i).1) := by
  induction phi with
  | mem i j => rfl
  | eq i j =>
      constructor
      · exact fun h => congrArg Subtype.val h
      · exact fun h => Subtype.ext h
  | neg phi ih => exact not_congr (ih s)
  | conj phi psi ihPhi ihPsi =>
      exact and_congr (ihPhi s) (ihPsi s)
  | ex phi ih =>
      constructor
      · rintro ⟨x, hx⟩
        refine ⟨x.1, x.2, ?_⟩
        simpa only [subtypeVal_snoc] using (ih (snoc s x)).mp hx
      · rintro ⟨x, hxM, hx⟩
        let xM : ClassCarrier M := ⟨x, hxM⟩
        refine ⟨xM, (ih (snoc s xM)).mpr ?_⟩
        simpa only [subtypeVal_snoc] using hx

/-- The ambient `ZFSet` universe, regarded as a membership structure. -/
instance zfSetMembershipStructure :
    FirstOrder.Language.setTheory.Structure ZFSet.{u} :=
  FirstOrder.Language.setTheoryStructure fun x y => x ∈ y

/-- The type of constructible sets.  Its membership proof is part of the type. -/
abbrev LCarrier := ClassCarrier (L : Set ZFSet.{u})

/-- Membership on the constructible carrier, inherited from `ZFSet`. -/
abbrev lCarrierMem (x y : LCarrier.{u}) : Prop := x.1 ∈ y.1

/-- The type of elements of one constructible stage. -/
abbrev StageCarrier (alpha : Ordinal.{u}) :=
  ClassCarrier (LStageZF alpha : Set ZFSet.{u})

/-- The subtype/raw-domain bridge specialized to the full constructible class. -/
theorem satisfies_lCarrier_iff_satisfiesIn_L {n : Nat} (phi : FOFormula n)
    (s : Tuple LCarrier.{u} n) :
    FOFormula.Satisfies
        (fun x y : LCarrier.{u} => x.1 ∈ y.1) phi s ↔
      SatisfiesIn (L : Set ZFSet.{u}) phi (fun i => (s i).1) :=
  satisfies_subtype_iff_satisfiesIn (L : Set ZFSet.{u}) phi s

/-- The subtype/raw-domain bridge specialized to a constructible stage. -/
theorem satisfies_stageCarrier_iff_satisfiesIn {alpha : Ordinal.{u}}
    {n : Nat} (phi : FOFormula n) (s : Tuple (StageCarrier alpha) n) :
    FOFormula.Satisfies
        (fun x y : StageCarrier alpha => x.1 ∈ y.1) phi s ↔
      SatisfiesIn (LStageZF alpha : Set ZFSet.{u}) phi
        (fun i => (s i).1) :=
  satisfies_subtype_iff_satisfiesIn
    (LStageZF alpha : Set ZFSet.{u}) phi s

/-- Membership on `LCarrier` is ambient membership restricted to `L`. -/
instance lCarrierMembershipStructure :
    FirstOrder.Language.setTheory.Structure LCarrier.{u} :=
  FirstOrder.Language.setTheoryStructure lCarrierMem

/--
Translate the construction syntax to Mathlib's bounded-formula syntax.

All variables of `FOFormula n` become Mathlib bound variables.  This gives a
sentence when `n = 0` and supports the existing last-variable quantifier
convention for arbitrary `n`.
-/
def toBoundedFormula : {n : Nat} -> FOFormula n ->
    FirstOrder.Language.setTheory.BoundedFormula Empty n
  | _, .mem i j =>
      FirstOrder.Language.Term.mem (.var (Sum.inr i)) (.var (Sum.inr j))
  | _, .eq i j =>
      .equal (.var (Sum.inr i)) (.var (Sum.inr j))
  | _, .neg phi => (toBoundedFormula phi).not
  | _, .conj phi psi => toBoundedFormula phi ⊓ toBoundedFormula psi
  | _, .ex phi => (toBoundedFormula phi).ex

/-- Extract the index denoted by a term in the function-free membership language. -/
def fromBoundedTerm {n : Nat} :
    FirstOrder.Language.setTheory.Term (Empty ⊕ Fin n) -> Fin n
  | .var (Sum.inl i) => Empty.elim i
  | .var (Sum.inr i) => i
  | .func f _ => Empty.elim f

/--
Normalize a Mathlib membership-language formula to the small construction
syntax.  The two syntaxes use different primitive Boolean connectives, but
they have the same expressive power.
-/
def fromBoundedFormula : {n : Nat} ->
    FirstOrder.Language.setTheory.BoundedFormula Empty n -> FOFormula n
  | n, .falsum => .ex (.neg (.eq (Fin.last n) (Fin.last n)))
  | _, .equal t u => .eq (fromBoundedTerm t) (fromBoundedTerm u)
  | _, .rel .mem ts =>
      .mem (fromBoundedTerm (ts 0)) (fromBoundedTerm (ts 1))
  | _, .imp phi psi =>
      FOFormula.disj (.neg (fromBoundedFormula phi))
        (fromBoundedFormula psi)
  | _, .all phi => FOFormula.all (fromBoundedFormula phi)

/-- Closed construction formulas translate to Mathlib sentences. -/
abbrev toSentence (phi : FOFormula 0) : FirstOrder.Language.setTheory.Sentence :=
  toBoundedFormula phi

@[simp, nolint simpNF]
theorem snoc_eq_finSnoc {A : Type u} {n : Nat}
    (s : Fin n -> A) (x : A) : snoc s x = Fin.snoc s x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp

section ArbitraryStructure

variable {A : Type u} (E : A -> A -> Prop)

@[simp]
theorem termValue_eq_assignment {n : Nat}
    (t : FirstOrder.Language.setTheory.Term (Empty ⊕ Fin n)) (s : Fin n -> A) :
    termValue E t s = s (fromBoundedTerm t) := by
  cases t with
  | var i =>
      cases i with
      | inl i => exact Empty.elim i
      | inr i => rfl
  | func f _ => exact Empty.elim f

/-- Realization of a translated formula with an explicitly supplied relation. -/
def translatedRealizes {n : Nat} (phi : FOFormula n) (s : Tuple A n) : Prop :=
  realizes E (toBoundedFormula phi) s

/--
The translation preserves Tarskian satisfaction in every binary structure.
In particular, this applies both to ambient `ZFSet` and to `LCarrier`.
-/
@[simp]
theorem realize_toBoundedFormula {n : Nat} (phi : FOFormula n)
    (s : Tuple A n) :
    translatedRealizes E phi s ↔
      FOFormula.Satisfies E phi s := by
  letI : FirstOrder.Language.setTheory.Structure A :=
    FirstOrder.Language.setTheoryStructure E
  induction phi with
  | mem i j =>
      change E (s i) (s j) ↔ E (s i) (s j)
      rfl
  | eq i j =>
      change s i = s j ↔ s i = s j
      rfl
  | neg phi ih =>
      change (¬translatedRealizes E phi s) ↔
        ¬FOFormula.Satisfies E phi s
      exact not_congr (ih s)
  | conj phi psi ihPhi ihPsi =>
      change
        ((toBoundedFormula phi ⊓ toBoundedFormula psi).Realize Empty.elim s) ↔
          FOFormula.Satisfies E phi s ∧ FOFormula.Satisfies E psi s
      rw [FirstOrder.Language.BoundedFormula.realize_inf]
      exact and_congr (ihPhi s) (ihPsi s)
  | ex phi ih =>
      change
        ((toBoundedFormula phi).ex.Realize Empty.elim s) ↔
          ∃ x, FOFormula.Satisfies E phi (snoc s x)
      rw [FirstOrder.Language.BoundedFormula.realize_ex]
      simp only [snoc_eq_finSnoc]
      exact exists_congr fun x => ih (Fin.snoc s x)

/-- The forward translation stated through the canonical `realizes` wrapper. -/
theorem realizes_toBoundedFormula {n : Nat} (phi : FOFormula n)
    (s : Tuple A n) :
    realizes E (toBoundedFormula phi) s <->
      FOFormula.Satisfies E phi s := by
  simpa [translatedRealizes] using realize_toBoundedFormula E phi s

/--
Every Mathlib formula in the function-free membership language has the same
semantics as its normalization to `FOFormula`.
-/
@[simp]
theorem realize_fromBoundedFormula {n : Nat}
    (phi : FirstOrder.Language.setTheory.BoundedFormula Empty n)
    (s : Tuple A n) :
    realizes E phi s <->
      FOFormula.Satisfies E (fromBoundedFormula phi) s := by
  classical
  induction phi with
  | falsum =>
      rw [realizes_falsum]
      simp only [fromBoundedFormula]
      simp [FOFormula.Satisfies]
  | equal t u =>
      change termValue E t s = termValue E u s <->
        s (fromBoundedTerm t) = s (fromBoundedTerm u)
      rw [termValue_eq_assignment, termValue_eq_assignment]
  | rel R ts =>
      cases R with
      | mem =>
          change E (termValue E (ts 0) s) (termValue E (ts 1) s) <->
            E (s (fromBoundedTerm (ts 0)))
              (s (fromBoundedTerm (ts 1)))
          rw [termValue_eq_assignment, termValue_eq_assignment]
  | imp phi psi ihPhi ihPsi =>
      rw [realizes_imp]
      simp only [fromBoundedFormula]
      rw [FOFormula.satisfies_disj]
      change (realizes E phi s -> realizes E psi s) <->
        Not (FOFormula.Satisfies E (fromBoundedFormula phi) s) \/
          FOFormula.Satisfies E (fromBoundedFormula psi) s
      rw [ihPhi, ihPsi]
      tauto
  | all phi ih =>
      rw [realizes_all]
      simp only [fromBoundedFormula]
      rw [FOFormula.satisfies_all]
      simp only [snoc_eq_finSnoc]
      change (forall x : A, realizes E phi (Fin.snoc s x)) <->
        forall x : A,
          FOFormula.Satisfies E (fromBoundedFormula phi) (Fin.snoc s x)
      exact forall_congr' fun x => ih (Fin.snoc s x)

/-- Normalizing to `FOFormula` and translating back preserves realization. -/
theorem realizes_to_fromBoundedFormula {n : Nat}
    (phi : FirstOrder.Language.setTheory.BoundedFormula Empty n)
    (s : Tuple A n) :
    realizes E (toBoundedFormula (fromBoundedFormula phi)) s <->
      realizes E phi s := by
  exact (realizes_toBoundedFormula E (fromBoundedFormula phi) s).trans
    (realize_fromBoundedFormula E phi s).symm

end ArbitraryStructure

/-!
## `DefZF` through Mathlib formulas
-/

/--
The internal definable-powerset operation is characterized by Mathlib's
membership-language formulas and by the intrinsically scoped `FOFormula`
syntax.
-/
theorem mem_DefZF_iff_exists_realizes {a z : ZFSet.{u}} :
    z ∈ DefZF a <->
      z ⊆ a /\
        Exists fun n : Nat =>
          Exists fun s : Tuple (ZFCarrier a) n =>
            Exists fun phi :
              FirstOrder.Language.setTheory.BoundedFormula Empty (n + 1) =>
              forall x : ZFCarrier a,
                x.1 ∈ z <->
                  realizes (zfCarrierMem a) phi (snoc s x) := by
  rw [mem_DefZF_iff_exists_satisfies]
  constructor
  · rintro ⟨hza, n, s, phi, hphi⟩
    refine ⟨hza, n, s, toBoundedFormula phi, ?_⟩
    intro x
    have hsem :=
      realize_toBoundedFormula (zfCarrierMem a) phi (snoc s x)
    exact (hphi x).trans (by
      simpa [translatedRealizes] using hsem.symm)
  · rintro ⟨hza, n, s, phi, hphi⟩
    refine ⟨hza, n, s, fromBoundedFormula phi, ?_⟩
    intro x
    exact (hphi x).trans
      (realize_fromBoundedFormula (zfCarrierMem a) phi (snoc s x))

/-- The specialized satisfaction bridge for the constructible universe. -/
@[simp]
theorem lCarrier_realize_toBoundedFormula {n : Nat} (phi : FOFormula n)
    (s : Tuple LCarrier.{u} n) :
    (toBoundedFormula phi).Realize Empty.elim s ↔
      FOFormula.Satisfies (fun x y : LCarrier.{u} => x.1 ∈ y.1) phi s :=
  realize_toBoundedFormula (fun x y : LCarrier.{u} => x.1 ∈ y.1) phi s

end Model

end Constructible
