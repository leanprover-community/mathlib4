/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Bounding
public import Mathlib.SetTheory.ZFC.Constructible.Model

/-!
# Formula reflection for the constructible hierarchy

For a fixed first-order formula and a starting level, this file constructs an
omega-chain of levels.  At every successor step, witnesses for all existential
subformulas with parameters in the current level are added.  The union level
is then closed under the relevant witnesses, so the Tarski--Vaught induction
shows that the formula has the same truth value there as in the full class
`L`.
-/

@[expose] public section

open Set

universe u

namespace Constructible

section ZFC

open Model

/-- Forget the membership proofs in a tuple over an internal stage. -/
def stageTupleVal {alpha : Ordinal.{u}} {n : Nat}
    (s : Tuple (ZFCarrier (LStageZF alpha)) n) : Tuple ZFSet.{u} n :=
  fun i => (s i).1

@[simp]
theorem stageTupleVal_apply {alpha : Ordinal.{u}} {n : Nat}
    (s : Tuple (ZFCarrier (LStageZF alpha)) n) (i : Fin n) :
    stageTupleVal s i = (s i).1 :=
  rfl

/--
`ClosesFrom phi alpha beta` says that `beta` contains witnesses for every
existential subformula of `phi` whose free assignment lies in level `alpha`.
The recursive clauses ensure that the same holds for every subformula.
-/
def ClosesFrom : {n : Nat} -> FOFormula n ->
    Ordinal.{u} -> Ordinal.{u} -> Prop
  | _, .mem _ _, _, _ => True
  | _, .eq _ _, _, _ => True
  | _, .neg phi, alpha, beta => ClosesFrom phi alpha beta
  | _, .conj phi psi, alpha, beta =>
      ClosesFrom phi alpha beta /\ ClosesFrom psi alpha beta
  | n, .ex phi, alpha, beta =>
      ClosesFrom phi alpha beta /\
        forall s : Tuple ZFSet.{u} n,
          (forall i, s i ∈ LStageZF alpha) ->
          Model.SatisfiesIn L (.ex phi) s ->
          exists x : ZFSet.{u},
            x ∈ LStageZF beta /\ Model.SatisfiesIn L phi (snoc s x)

/-- Enlarging the target level preserves witness closure. -/
theorem ClosesFrom.mono_right {n : Nat} {phi : FOFormula n}
    {alpha beta gamma : Ordinal.{u}} (hbeta : beta <= gamma)
    (h : ClosesFrom phi alpha beta) : ClosesFrom phi alpha gamma := by
  induction phi with
  | mem i j => trivial
  | eq i j => trivial
  | neg phi ih => exact ih h
  | conj phi psi ihPhi ihPsi =>
      exact ⟨ihPhi h.1, ihPsi h.2⟩
  | ex phi ih =>
      refine ⟨ih h.1, ?_⟩
      intro s hs hsat
      rcases h.2 s hs hsat with ⟨x, hx, hphi⟩
      exact ⟨x, LStageZF_mono hbeta hx, hphi⟩

/-- A total chosen witness, using the empty set when the existential is false. -/
noncomputable def chosenWitness {n : Nat} (phi : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) : ZFSet.{u} := by
  classical
  exact if h : Model.SatisfiesIn L (.ex phi) s then Classical.choose h else ∅

theorem chosenWitness_mem_L {n : Nat} (phi : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) (h : Model.SatisfiesIn L (.ex phi) s) :
    chosenWitness phi s ∈ L := by
  rw [chosenWitness, dif_pos h]
  exact (Classical.choose_spec h).1

theorem chosenWitness_satisfies {n : Nat} (phi : FOFormula (n + 1))
    (s : Tuple ZFSet.{u} n) (h : Model.SatisfiesIn L (.ex phi) s) :
    Model.SatisfiesIn L phi (snoc s (chosenWitness phi s)) := by
  rw [chosenWitness, dif_pos h]
  exact (Classical.choose_spec h).2

/-- A proof-independent chosen occurrence level, defaulting to zero off `L`. -/
noncomputable def stageOfConstructible (x : ZFSet.{u}) : Ordinal.{u} := by
  classical
  exact if hx : x ∈ L then stageOf x hx else 0

theorem mem_stageOfConstructible {x : ZFSet.{u}} (hx : x ∈ L) :
    x ∈ LStageZF (stageOfConstructible x) := by
  simp only [stageOfConstructible, dif_pos hx]
  exact mem_LStageZF_stageOf x hx

/-- A common ordinal bound for the chosen witnesses over one stage. -/
noncomputable def existentialWitnessBound {n : Nat}
    (phi : FOFormula (n + 1)) (alpha : Ordinal.{u}) : Ordinal.{u} :=
  iSup fun s : Tuple (ZFCarrier (LStageZF alpha)) n =>
    Order.succ (stageOfConstructible (chosenWitness phi (stageTupleVal s)))

theorem chosenWitness_mem_existentialWitnessBound {n : Nat}
    (phi : FOFormula (n + 1)) (alpha : Ordinal.{u})
    (s : Tuple (ZFCarrier (LStageZF alpha)) n)
    (h : Model.SatisfiesIn L (.ex phi) (stageTupleVal s)) :
    chosenWitness phi (stageTupleVal s) ∈
      LStageZF (existentialWitnessBound phi alpha) := by
  have hwL := chosenWitness_mem_L phi (stageTupleVal s) h
  have hwStage := mem_stageOfConstructible hwL
  apply LStageZF_mono _ hwStage
  exact (Order.le_succ _).trans (Ordinal.le_iSup
    (fun t : Tuple (ZFCarrier (LStageZF alpha)) n =>
      Order.succ (stageOfConstructible (chosenWitness phi (stageTupleVal t)))) s)

/-- Recursively combine all witness bounds required by a formula. -/
noncomputable def closingBound : {n : Nat} -> FOFormula n ->
    Ordinal.{u} -> Ordinal.{u}
  | _, .mem _ _, alpha => alpha
  | _, .eq _ _, alpha => alpha
  | _, .neg phi, alpha => closingBound phi alpha
  | _, .conj phi psi, alpha =>
      max (closingBound phi alpha) (closingBound psi alpha)
  | _, .ex phi, alpha =>
      max (closingBound phi alpha) (existentialWitnessBound phi alpha)

theorem le_closingBound {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : alpha <= closingBound phi alpha := by
  induction phi with
  | mem i j => exact le_rfl
  | eq i j => exact le_rfl
  | neg phi ih => exact ih
  | conj phi psi ihPhi ihPsi => exact ihPhi.trans (le_max_left _ _)
  | ex phi ih => exact ih.trans (le_max_left _ _)

/-- The recursively computed bound really closes all relevant subformulas. -/
theorem closesFrom_closingBound {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) :
    ClosesFrom phi alpha (closingBound phi alpha) := by
  induction phi with
  | mem i j => trivial
  | eq i j => trivial
  | neg phi ih => exact ih
  | conj phi psi ihPhi ihPsi =>
      exact ⟨ihPhi.mono_right (le_max_left _ _),
        ihPsi.mono_right (le_max_right _ _)⟩
  | ex phi ih =>
      refine ⟨ih.mono_right (le_max_left _ _), ?_⟩
      intro s hs hsat
      let sa : Tuple (ZFCarrier (LStageZF alpha)) _ :=
        fun i => ⟨s i, hs i⟩
      have hval : stageTupleVal sa = s := by
        funext i
        rfl
      have hwBound := chosenWitness_mem_existentialWitnessBound phi alpha sa
        (by simpa only [hval] using hsat)
      refine ⟨chosenWitness phi s, ?_, chosenWitness_satisfies phi s hsat⟩
      apply LStageZF_mono (le_max_right _ _)
      simpa only [hval] using hwBound

/-- One closure step is chosen strictly above every bound just constructed. -/
noncomputable def reflectionStep {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : Ordinal.{u} :=
  Order.succ (closingBound phi alpha)

theorem lt_reflectionStep {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : alpha < reflectionStep phi alpha :=
  (le_closingBound phi alpha).trans_lt (Order.lt_succ _)

theorem closesFrom_reflectionStep {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) :
    ClosesFrom phi alpha (reflectionStep phi alpha) :=
  (closesFrom_closingBound phi alpha).mono_right (Order.le_succ _)

/-- The omega-sequence obtained by repeatedly adjoining all required witnesses. -/
noncomputable def reflectionSequence {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : Nat -> Ordinal.{u}
  | 0 => alpha
  | k + 1 => reflectionStep phi (reflectionSequence phi alpha k)

@[simp]
theorem reflectionSequence_zero {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : reflectionSequence phi alpha 0 = alpha :=
  rfl

@[simp]
theorem reflectionSequence_succ {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) (k : Nat) :
    reflectionSequence phi alpha (k + 1) =
      reflectionStep phi (reflectionSequence phi alpha k) :=
  rfl

theorem reflectionSequence_lt_succ {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) (k : Nat) :
    reflectionSequence phi alpha k < reflectionSequence phi alpha (k + 1) := by
  rw [reflectionSequence_succ]
  exact lt_reflectionStep phi _

theorem reflectionSequence_strictMono {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : StrictMono (reflectionSequence phi alpha) :=
  strictMono_nat_of_lt_succ (reflectionSequence_lt_succ phi alpha)

/-- The limit of the witness-closure sequence. -/
noncomputable def reflectionOrdinal {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : Ordinal.{u} :=
  iSup (reflectionSequence phi alpha)

theorem reflectionSequence_le_ordinal {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) (k : Nat) :
    reflectionSequence phi alpha k <= reflectionOrdinal phi alpha :=
  Ordinal.le_iSup (reflectionSequence phi alpha) k

theorem reflectionSequence_lt_ordinal {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) (k : Nat) :
    reflectionSequence phi alpha k < reflectionOrdinal phi alpha :=
  (reflectionSequence_lt_succ phi alpha k).trans_le
    (reflectionSequence_le_ordinal phi alpha (k + 1))

theorem reflectionOrdinal_isSuccLimit {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : Order.IsSuccLimit (reflectionOrdinal phi alpha) := by
  rw [Order.isSuccLimit_iff]
  constructor
  · exact not_isMin_iff.mpr ⟨reflectionSequence phi alpha 0,
      reflectionSequence_lt_ordinal phi alpha 0⟩
  · apply Order.isSuccPrelimit_of_succ_lt
    intro gamma hgamma
    apply Ordinal.succ_lt_iSup_of_ne_iSup
      (f := reflectionSequence phi alpha)
    · intro k hk
      exact (reflectionSequence_lt_ordinal phi alpha k).ne hk
    · exact hgamma

theorem le_reflectionOrdinal {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) : alpha <= reflectionOrdinal phi alpha := by
  simpa only [reflectionSequence_zero] using
    reflectionSequence_le_ordinal phi alpha 0

/-- Every finite tuple in the limit already occurs together at one sequence stage. -/
theorem exists_reflectionSequence_for_tuple {m n : Nat}
    (phi : FOFormula n) (alpha : Ordinal.{u})
    (s : Tuple ZFSet.{u} m)
    (hs : forall i, s i ∈ LStageZF (reflectionOrdinal phi alpha)) :
    exists k : Nat, forall i, s i ∈ LStageZF (reflectionSequence phi alpha k) := by
  induction m with
  | zero =>
      exact ⟨0, fun i => Fin.elim0 i⟩
  | succ m ih =>
      let init : Tuple ZFSet.{u} m := fun i => s i.castSucc
      have hinit : forall i, init i ∈ LStageZF (reflectionOrdinal phi alpha) :=
        fun i => hs i.castSucc
      rcases ih init hinit with ⟨k, hk⟩
      have hlast := hs (Fin.last m)
      rcases (mem_LStageZF_limit_iff
        (reflectionOrdinal_isSuccLimit phi alpha)).mp hlast with
        ⟨gamma, hgamma, hlastGamma⟩
      rcases (Ordinal.lt_iSup_iff.mp hgamma) with ⟨l, hgammaL⟩
      refine ⟨max k l, ?_⟩
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · exact LStageZF_mono
          ((reflectionSequence_strictMono phi alpha).monotone
            (le_max_right k l))
          (LStageZF_mono hgammaL.le hlastGamma)
      · exact LStageZF_mono
          ((reflectionSequence_strictMono phi alpha).monotone
            (le_max_left k l))
          (hk j)

/--
If every step of one cofinal chain closes a formula from that step to the
next, then its limit is closed for that formula.  Crucially, the same chain is
kept while recursing through subformulas.
-/
theorem closesFrom_of_cofinal_sequence {n : Nat} (phi : FOFormula n)
    (sequence : Nat -> Ordinal.{u}) (beta : Ordinal.{u})
    (hcofinal : forall {m : Nat} (s : Tuple ZFSet.{u} m),
      (forall i, s i ∈ LStageZF beta) ->
      exists k : Nat, forall i, s i ∈ LStageZF (sequence k))
    (hstep : forall k, ClosesFrom phi (sequence k) (sequence (k + 1)))
    (hle : forall k, sequence (k + 1) <= beta) :
    ClosesFrom phi beta beta := by
  induction phi with
  | mem i j => trivial
  | eq i j => trivial
  | neg phi ih =>
      exact ih (fun k => hstep k)
  | conj phi psi ihPhi ihPsi =>
      exact ⟨ihPhi (fun k => (hstep k).1),
        ihPsi (fun k => (hstep k).2)⟩
  | ex phi ih =>
      refine ⟨ih (fun k => (hstep k).1), ?_⟩
      intro s hs hsat
      rcases hcofinal s hs with ⟨k, hk⟩
      rcases (hstep k).2 s hk hsat with ⟨x, hx, hphi⟩
      exact ⟨x, LStageZF_mono (hle k) hx, hphi⟩

/-- The limit level is closed under witnesses for the formula and all subformulas. -/
theorem closesFrom_reflectionOrdinal {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) :
    ClosesFrom phi (reflectionOrdinal phi alpha)
      (reflectionOrdinal phi alpha) := by
  apply closesFrom_of_cofinal_sequence phi (reflectionSequence phi alpha)
    (reflectionOrdinal phi alpha)
  · intro m s hs
    exact exists_reflectionSequence_for_tuple phi alpha s hs
  · intro k
    rw [reflectionSequence_succ]
    exact closesFrom_reflectionStep phi _
  · intro k
    exact reflectionSequence_le_ordinal phi alpha (k + 1)

/-- Tarski--Vaught induction from witness closure to formula absoluteness. -/
theorem satisfiesIn_stage_iff_L_of_closes {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u})
    (hclose : ClosesFrom phi alpha alpha)
    (s : Tuple ZFSet.{u} n) (hs : forall i, s i ∈ LStageZF alpha) :
    Model.SatisfiesIn (LStageZF alpha : Set ZFSet.{u}) phi s <->
      Model.SatisfiesIn L phi s := by
  induction phi with
  | mem i j => rfl
  | eq i j => rfl
  | neg phi ih =>
      exact not_congr (ih hclose s hs)
  | conj phi psi ihPhi ihPsi =>
      exact and_congr (ihPhi hclose.1 s hs) (ihPsi hclose.2 s hs)
  | ex phi ih =>
      constructor
      · rintro ⟨x, hxStage, hphi⟩
        have hxL : x ∈ L :=
          LStageZF_subset_constructibleUniverse alpha hxStage
        refine ⟨x, hxL, ?_⟩
        apply (ih hclose.1 (snoc s x) ?_).mp hphi
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hxStage
        · simpa using hs j
      · intro hex
        rcases hclose.2 s hs hex with ⟨x, hxStage, hphi⟩
        refine ⟨x, hxStage, ?_⟩
        apply (ih hclose.1 (snoc s x) ?_).mpr hphi
        intro i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using hxStage
        · simpa using hs j

/--
Every formula reflects between `L` and an arbitrarily high constructible
level.  This is the form used by full Separation and Replacement.
-/
theorem exists_reflecting_LStage {n : Nat} (phi : FOFormula n)
    (alpha : Ordinal.{u}) :
    exists beta : Ordinal.{u}, alpha <= beta /\
      forall s : Tuple ZFSet.{u} n,
        (forall i, s i ∈ LStageZF beta) ->
        (Model.SatisfiesIn (LStageZF beta : Set ZFSet.{u}) phi s <->
          Model.SatisfiesIn L phi s) := by
  refine ⟨reflectionOrdinal phi alpha, le_reflectionOrdinal phi alpha, ?_⟩
  intro s hs
  exact satisfiesIn_stage_iff_L_of_closes phi _
    (closesFrom_reflectionOrdinal phi alpha) s hs

end ZFC

end Constructible
