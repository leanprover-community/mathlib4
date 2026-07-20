/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.Equivalence
public import Mathlib.SetTheory.ZFC.Constructible.Bounding

/-!
# Constructibility of rudimentary term values

Every primitive Gödel operation preserves constructibility. The proof first
shows that all members of an operation value are constructible, bounds those
members together with the two operands in one constructible stage, and then
uses the existing bounded definition of the operation to place its value in
the next stage.

It follows by structural induction that a rudimentary term whose generators
belong to `L` also evaluates to an element of `L`.
-/

@[expose] public section

open Set

universe u v

namespace Constructible

namespace Godel

/-- The field of a constructible relation is constructible. -/
theorem pairField_mem_L {r : ZFSet.{u}} (hr : r ∈ L) : pairField r ∈ L := by
  simpa only [pairField] using sUnion_mem_L (sUnion_mem_L hr)

/-- A bounded membership definition for a fiber over a fixed pair of parameters. -/
def fiberDelta0Section {U x z : ZFSet.{u}} (hx : x ∈ U) (hz : z ∈ U) :
    Delta0Section U (fiber x z) where
  arity := 2
  params := ![⟨x, hx⟩, ⟨z, hz⟩]
  formula := fiberMemAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)
  correct := by
    intro q
    have hassign :
        snoc (Delta0Formula.val ![⟨x, hx⟩, ⟨z, hz⟩]) q.1 =
          ![x, z, q.1] := by
      funext i
      fin_cases i <;> rfl
    rw [hassign]
    exact satisfies_fiberMemAt (2 : Fin 3) (0 : Fin 3) (1 : Fin 3)
      ![x, z, q.1]

/-- Fibers of constructible relations at constructible parameters belong to `L`. -/
theorem fiber_mem_L {x z : ZFSet.{u}} (hx : x ∈ L) (hz : z ∈ L) :
    fiber x z ∈ L := by
  have hmembers : ∀ q ∈ fiber x z, q ∈ L := by
    intro q hq
    have hpair : ZFSet.pair q z ∈ x := mem_fiber_iff.mp hq
    exact mem_L_of_mem (pair_left_mem_pairField hpair) (pairField_mem_L hx)
  rcases exists_LStage_for_tuple ![x, z] (by
      intro i
      fin_cases i
      · exact hx
      · exact hz) with ⟨alpha, hparams⟩
  rcases exists_LStage_for_members hmembers with ⟨beta, hmembersBeta⟩
  let gamma : Ordinal.{u} := max alpha beta
  have hxGamma : x ∈ LStageZF gamma :=
    LStageZF_mono (le_max_left alpha beta) (hparams 0)
  have hzGamma : z ∈ LStageZF gamma :=
    LStageZF_mono (le_max_left alpha beta) (hparams 1)
  have hfiberGamma : fiber x z ⊆ LStageZF gamma := by
    intro q hq
    exact LStageZF_mono (le_max_right alpha beta) (hmembersBeta q hq)
  refine ⟨Order.succ gamma, ?_⟩
  rw [LStageZF_succ]
  exact (fiberDelta0Section hxGamma hzGamma).mem_DefZF
    (LStageZF_isTransitive gamma) hfiberGamma

/-- Every member of a primitive operation value is constructible. -/
theorem mem_L_of_mem_op {i : Fin 9} {x y q : ZFSet.{u}}
    (hx : x ∈ L) (hy : y ∈ L) (hq : q ∈ op i x y) : q ∈ L := by
  fin_cases i
  · rcases mem_F0_iff.mp hq with rfl | rfl
    · exact hx
    · exact hy
  · exact mem_L_of_mem (mem_F1_iff.mp hq).1 hx
  · rcases mem_F2_iff.mp hq with ⟨a, ha, b, hb, rfl⟩
    exact orderedPair_mem_L (mem_L_of_mem ha hx) (mem_L_of_mem hb hy)
  · rcases mem_F3_iff.mp hq with ⟨a, z, b, hz, hab, rfl⟩
    have haL : a ∈ L :=
      mem_L_of_mem (pair_left_mem_pairField hab) (pairField_mem_L hy)
    have hbL : b ∈ L :=
      mem_L_of_mem (pair_right_mem_pairField hab) (pairField_mem_L hy)
    have hzL : z ∈ L := mem_L_of_mem hz hx
    simpa only [triple] using
      orderedPair_mem_L haL (orderedPair_mem_L hzL hbL)
  · rcases mem_F4_iff.mp hq with ⟨a, b, z, hz, hab, rfl⟩
    have haL : a ∈ L :=
      mem_L_of_mem (pair_left_mem_pairField hab) (pairField_mem_L hy)
    have hbL : b ∈ L :=
      mem_L_of_mem (pair_right_mem_pairField hab) (pairField_mem_L hy)
    have hzL : z ∈ L := mem_L_of_mem hz hx
    simpa only [triple] using
      orderedPair_mem_L haL (orderedPair_mem_L hbL hzL)
  · rcases (mem_F5_iff (x := x) (y := y) (z := q)).mp hq with
      ⟨a, ha, hqa⟩
    exact mem_L_of_mem hqa (mem_L_of_mem ha hx)
  · rcases (mem_F6_iff (x := x) (y := y) (z := q)).mp hq with ⟨a, ha⟩
    exact mem_L_of_mem (pair_right_mem_pairField ha) (pairField_mem_L hx)
  · rcases (mem_F7_iff (x := x) (y := y) (q := q)).mp hq with
      ⟨a, ha, b, hb, rfl, _hab⟩
    exact orderedPair_mem_L (mem_L_of_mem ha hx) (mem_L_of_mem hb hx)
  · rcases mem_F8_iff.mp hq with ⟨z, hz, rfl⟩
    exact fiber_mem_L hx (mem_L_of_mem hz hy)

/-- Every primitive Gödel operation sends constructible inputs to a constructible output. -/
theorem op_mem_L {i : Fin 9} {x y : ZFSet.{u}}
    (hx : x ∈ L) (hy : y ∈ L) : op i x y ∈ L := by
  have hmembers : ∀ q ∈ op i x y, q ∈ L :=
    fun q hq => mem_L_of_mem_op hx hy hq
  rcases exists_LStage_for_tuple ![x, y] (by
      intro j
      fin_cases j
      · exact hx
      · exact hy) with ⟨alpha, hparams⟩
  rcases exists_LStage_for_members hmembers with ⟨beta, hmembersBeta⟩
  let gamma : Ordinal.{u} := max alpha beta
  have hxGamma : x ∈ LStageZF gamma :=
    LStageZF_mono (le_max_left alpha beta) (hparams 0)
  have hyGamma : y ∈ LStageZF gamma :=
    LStageZF_mono (le_max_left alpha beta) (hparams 1)
  have hopGamma : op i x y ⊆ LStageZF gamma := by
    intro q hq
    exact LStageZF_mono (le_max_right alpha beta) (hmembersBeta q hq)
  refine ⟨Order.succ gamma, ?_⟩
  rw [LStageZF_succ]
  exact op_mem_DefZF_of_subset
    (LStageZF_isTransitive gamma) hxGamma hyGamma hopGamma

namespace RudimentaryTerm

/-- A rudimentary term over constructible generators evaluates to a constructible set. -/
theorem eval_mem_L {alpha : Type u} {rho : alpha -> ZFSet.{v}}
    (hrho : ∀ a, rho a ∈ L) (term : RudimentaryTerm alpha) :
    eval rho term ∈ L := by
  induction term with
  | var a => exact hrho a
  | app i left right hleft hright =>
      exact op_mem_L hleft hright

end RudimentaryTerm

/-- Every canonical generator over a constructible set belongs to `L`. -/
theorem rudimentaryGenerator_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (a : Option (Constructible.ZFCarrier U)) : rudimentaryGenerator U a ∈ L := by
  cases a with
  | none => exact hU
  | some x => exact mem_L_of_mem x.2 hU

/-- A term over `U ∪ {U}` is constructible whenever `U` is constructible. -/
theorem RudimentaryClosureTerm.eval_mem_L {U : ZFSet.{u}} (hU : U ∈ L)
    (term : RudimentaryClosureTerm U) : term.eval ∈ L :=
  RudimentaryTerm.eval_mem_L (rudimentaryGenerator_mem_L hU) term

end Godel

end Constructible
