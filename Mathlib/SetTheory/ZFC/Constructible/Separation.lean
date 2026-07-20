/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Reflection

/-!
# Full Separation in the constructible universe

For a formula with constructible parameters and a constructible set `a`, a
reflecting level turns truth in the proper class `L` into ordinary
first-order truth over one internal stage.  The corresponding definable
subset of that stage lies in its `DefZF`; intersecting it with `a` gives the
required Separation set.
-/

@[expose] public section

open Set

universe u

namespace Constructible

section ZFC

/--
Full first-order Separation for the raw-domain semantics of `L`.

The last variable of `phi` is the element being separated; the preceding
`n` variables are parameters.
-/
theorem exists_separation {n : Nat} (phi : FOFormula (n + 1))
    (params : Tuple ZFSet.{u} n) (hparams : forall i, params i ∈ L)
    {a : ZFSet.{u}} (ha : a ∈ L) :
    exists b : ZFSet.{u}, b ∈ L /\
      forall x : ZFSet.{u},
        x ∈ b <-> x ∈ a /\
          Model.SatisfiesIn L phi (snoc params x) := by
  have hall : forall i, snoc params a i ∈ L := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using ha
    · simpa using hparams j
  rcases exists_LStage_for_tuple (snoc params a) hall with ⟨alpha, halpha⟩
  have hparamsAlpha : forall i, params i ∈ LStageZF alpha := by
    intro i
    simpa using halpha i.castSucc
  have haAlpha : a ∈ LStageZF alpha := by
    simpa using halpha (Fin.last n)
  rcases exists_reflecting_LStage phi alpha with
    ⟨beta, halphaBeta, hreflect⟩
  have hparamsBeta : forall i, params i ∈ LStageZF beta :=
    fun i => LStageZF_mono halphaBeta (hparamsAlpha i)
  have haBeta : a ∈ LStageZF beta :=
    LStageZF_mono halphaBeta haAlpha
  let paramsBeta : Tuple (ZFCarrier (LStageZF beta)) n :=
    fun i => ⟨params i, hparamsBeta i⟩
  let c : ZFSet.{u} :=
    ZFSet.sep
      (fun x => Model.SatisfiesIn (LStageZF beta : Set ZFSet.{u})
        phi (snoc params x))
      (LStageZF beta)
  have hcDef : c ∈ DefZF (LStageZF beta) := by
    rw [mem_DefZF_iff_exists_satisfies]
    refine ⟨ZFSet.sep_subset, n, paramsBeta, phi, ?_⟩
    intro x
    simp only [c, ZFSet.mem_sep, and_iff_right x.2]
    have hbridge :=
      Model.satisfies_stageCarrier_iff_satisfiesIn
        (alpha := beta) phi (snoc paramsBeta x)
    have hassign :
        (fun i => (snoc paramsBeta x i).1) = snoc params x.1 := by
      simp only [Model.subtypeVal_snoc, paramsBeta]
    change
      Model.SatisfiesIn (LStageZF beta : Set ZFSet.{u}) phi
          (snoc params x.1) ↔
        FOFormula.Satisfies
          (fun y z : ZFCarrier (LStageZF beta) => y.1 ∈ z.1) phi
          (snoc paramsBeta x)
    rw [← hassign]
    exact hbridge.symm
  have hcL : c ∈ L := by
    refine ⟨Order.succ beta, ?_⟩
    rw [LStageZF_succ]
    exact hcDef
  refine ⟨a ∩ c, inter_mem_L ha hcL, ?_⟩
  intro x
  rw [ZFSet.mem_inter]
  constructor
  · rintro ⟨hxa, hxc⟩
    have hxBeta : x ∈ LStageZF beta :=
      (LStageZF_isTransitive beta).mem_trans hxa haBeta
    have hstage :
        Model.SatisfiesIn (LStageZF beta : Set ZFSet.{u})
          phi (snoc params x) :=
      (ZFSet.mem_sep.mp hxc).2
    have hassign : forall i, snoc params x i ∈ LStageZF beta := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hxBeta
      · simpa using hparamsBeta j
    exact ⟨hxa, (hreflect (snoc params x) hassign).mp hstage⟩
  · rintro ⟨hxa, hL⟩
    have hxBeta : x ∈ LStageZF beta :=
      (LStageZF_isTransitive beta).mem_trans hxa haBeta
    have hassign : forall i, snoc params x i ∈ LStageZF beta := by
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa using hxBeta
      · simpa using hparamsBeta j
    have hstage := (hreflect (snoc params x) hassign).mpr hL
    refine ⟨hxa, ?_⟩
    exact ZFSet.mem_sep.mpr ⟨hxBeta, hstage⟩

/-- Full Separation packaged on the subtype model `LCarrier`. -/
theorem Model.exists_separationLCarrier {n : Nat}
    (phi : FOFormula (n + 1)) (params : Tuple Model.LCarrier.{u} n)
    (a : Model.LCarrier.{u}) :
    exists b : Model.LCarrier.{u}, forall x : Model.LCarrier.{u},
      x.1 ∈ b.1 <-> x.1 ∈ a.1 /\
        FOFormula.Satisfies
          (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
          phi (snoc params x) := by
  let rawParams : Tuple ZFSet.{u} n := fun i => (params i).1
  have hraw : forall i, rawParams i ∈ L := fun i => (params i).2
  rcases exists_separation phi rawParams hraw a.2 with ⟨b, hbL, hb⟩
  refine ⟨⟨b, hbL⟩, ?_⟩
  intro x
  rw [hb x.1]
  have hbridge := Model.satisfies_lCarrier_iff_satisfiesIn_L
    phi (snoc params x)
  simpa only [Model.subtypeVal_snoc] using
    and_congr_right (fun _ => hbridge.symm)

/--
Full Separation stated directly with Mathlib's membership-language formulas.
This is the Mathlib-facing interface for full Separation.
-/
theorem Model.exists_separationBoundedFormula {n : Nat}
    (phi : FirstOrder.Language.setTheory.BoundedFormula Empty (n + 1))
    (params : Tuple Model.LCarrier.{u} n) (a : Model.LCarrier.{u}) :
    exists b : Model.LCarrier.{u}, forall x : Model.LCarrier.{u},
      x.1 ∈ b.1 <-> x.1 ∈ a.1 /\
        phi.Realize Empty.elim (snoc params x) := by
  rcases Model.exists_separationLCarrier
      (Model.fromBoundedFormula phi) params a with ⟨b, hb⟩
  refine ⟨b, ?_⟩
  intro x
  rw [hb x]
  exact and_congr_right fun _ =>
    (Model.realize_fromBoundedFormula
      (fun z w : Model.LCarrier.{u} => z.1 ∈ w.1)
      phi (snoc params x)).symm

/--
Full Separation stated with Mathlib formulas whose variables are free.

Relabelling the free variables into the bounded-variable context lets us
reuse `exists_separationBoundedFormula`; realization is unchanged by
`Formula.realize_relabel_sumInr`.
-/
theorem Model.exists_separationFormula {n : Nat}
    (phi : FirstOrder.Language.setTheory.Formula (Fin (n + 1)))
    (params : Tuple Model.LCarrier.{u} n) (a : Model.LCarrier.{u}) :
    exists b : Model.LCarrier.{u}, forall x : Model.LCarrier.{u},
      x.1 ∈ b.1 <-> x.1 ∈ a.1 /\
        phi.Realize (Fin.snoc params x) := by
  simpa only [FirstOrder.Language.Formula.realize_relabel_sumInr,
    Model.snoc_eq_finSnoc] using
    (Model.exists_separationBoundedFormula
      (FirstOrder.Language.BoundedFormula.relabel
        (β := Empty) (n := n + 1) (k := 0)
        (fun i : Fin (n + 1) => (Sum.inr i : Empty ⊕ Fin (n + 1)))
        phi) params a)

end ZFC

end Constructible
