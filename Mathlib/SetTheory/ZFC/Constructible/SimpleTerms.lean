/-
Copyright (c) 2026 Zike Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zike Liu
-/
module
public import Mathlib.SetTheory.ZFC.Constructible.SimpleComposition

/-!
# Simplicity of rudimentary terms

This file lifts simplicity from the basic Gödel operations to arbitrary finite rudimentary terms
and reifies their parameters over an internal carrier.
-/

@[expose] public section

universe u

namespace Constructible.Godel

/-- Each coordinate projection is simple. -/
theorem isSimpleSetFunction_projection {n : Nat} (i : Fin n) :
    IsSimpleSetFunction
      (fun args : Tuple ZFSet.{u} n => args i) := by
  simpa only [IsSimpleSetFunction, IsSimpleTupleMap] using
    (isSimpleTupleMap_projection
      (fun _ : Fin 1 => i))

/-- If all nine basic operations are simple, every finite rudimentary term is
simple.  This is the composition step needed independently of reification. -/
theorem RudimentaryTerm.isSimple_eval
    (hop : ∀ i : Fin 9,
      IsSimpleSetFunction
        (fun s : Tuple ZFSet.{u} 2 => op i (s 0) (s 1)))
    {n : Nat} (t : RudimentaryTerm (Fin n)) :
    IsSimpleSetFunction
      (fun args : Tuple ZFSet.{u} n => RudimentaryTerm.eval args t) := by
  induction t with
  | var i =>
      exact isSimpleSetFunction_projection i
  | app i left right hleft hright =>
      have h := (hop i).compBinary hleft hright
      have hOne : (1 : Fin 2) = Fin.succ 0 := by rfl
      simpa only [RudimentaryTerm.eval, binaryTuple, hOne,
        Fin.cases_zero, Fin.cases_succ] using h

/-- Replace every occurrence of the universe generator by coordinate zero and
every genuine set parameter by its corresponding following coordinate. -/
def reificationIndex {U : ZFSet.{u}} {n : Nat}
    (labels : Tuple (Option (ZFCarrier U)) n) : Fin n → Fin (n + 1) :=
  fun i => match labels i with
    | none => 0
    | some _ => i.succ

/-- Fill the otherwise-unused parameter slots of universe occurrences by a
fixed genuine member of `U`. -/
def reificationParams {U : ZFSet.{u}} {n : Nat}
    (default : ZFCarrier U)
    (labels : Tuple (Option (ZFCarrier U)) n) :
    Tuple (ZFCarrier U) n :=
  fun i => match labels i with
    | none => default
    | some x => x

theorem tupleCons_reificationIndex {U : ZFSet.{u}} {n : Nat}
    (default : ZFCarrier U)
    (labels : Tuple (Option (ZFCarrier U)) n) :
    (fun i =>
      tupleCons U (Delta0Formula.val (reificationParams default labels))
        (reificationIndex labels i)) =
      rudimentaryGenerator U ∘ labels := by
  funext i
  simp only [Function.comp_apply]
  cases hlabel : labels i with
  | none =>
      simp [reificationIndex, hlabel, rudimentaryGenerator]
  | some x =>
      simp [reificationIndex, reificationParams, hlabel,
        rudimentaryGenerator]

/-- A finitely reified term over `U ∪ {U}` can be applied to `U` and genuine
parameters from `U` through the strong simplicity bridge. -/
theorem finiteReification_mem_DefZF
    (hop : ∀ i : Fin 9,
      IsSimpleSetFunction
        (fun s : Tuple ZFSet.{u} 2 => op i (s 0) (s 1)))
    {U z : ZFSet.{u}} (hU : U.IsTransitive)
    (default : ZFCarrier U) (hzU : z ⊆ U)
    (t : RudimentaryClosureTerm U) (ht : t.eval = z) :
    z ∈ Constructible.DefZF U := by
  rcases RudimentaryTerm.exists_finiteReification t with
    ⟨n, labels, body, hbody⟩
  let params : Tuple (ZFCarrier U) n :=
    reificationParams default labels
  let renamed : RudimentaryTerm (Fin (n + 1)) :=
    body.rename (reificationIndex labels)
  let f : Tuple ZFSet.{u} (n + 1) → ZFSet.{u} :=
    fun args => RudimentaryTerm.eval args renamed
  have hf : IsSimpleSetFunction f := by
    exact RudimentaryTerm.isSimple_eval hop renamed
  have heval :
      f (tupleCons U (Delta0Formula.val params)) = z := by
    simp only [f, renamed, RudimentaryTerm.eval_rename]
    have hassign :
        tupleCons U (Delta0Formula.val params) ∘
            reificationIndex labels =
          rudimentaryGenerator U ∘ labels := by
      change
        (fun i => tupleCons U (Delta0Formula.val params)
          (reificationIndex labels i)) = rudimentaryGenerator U ∘ labels
      simpa only [params] using
        (tupleCons_reificationIndex default labels)
    rw [hassign]
    rw [hbody (rudimentaryGenerator U)]
    exact ht
  have hsub : f (tupleCons U (Delta0Formula.val params)) ⊆ U := by
    simpa only [heval] using hzU
  have hmem := hf.mem_DefZF_withUniverse hU params hsub
  simpa only [heval] using hmem

/-- The hard inclusion, conditional only on the nine primitive simplicity
lemmas.  The empty carrier is discharged by the previously proved exact base
case; a nonempty carrier supplies the harmless filler used by reification. -/
theorem godelDef_subset_DefZF_of_simpleOps
    (hop : ∀ i : Fin 9,
      IsSimpleSetFunction
        (fun s : Tuple ZFSet.{u} 2 => op i (s 0) (s 1)))
    {U : ZFSet.{u}} (hU : U.IsTransitive) :
    godelDef U ⊆ Constructible.DefZF U := by
  rcases ZFSet.eq_empty_or_nonempty U with rfl | hnonempty
  · rw [← DefZF_eq_godelDef_empty]
  · rcases hnonempty with ⟨default, hdefault⟩
    intro z hz
    rcases mem_godelDef_iff_exists_rudimentaryTerm.mp hz with
      ⟨hzU, t, ht⟩
    exact finiteReification_mem_DefZF hop hU
      ⟨default, hdefault⟩ hzU t ht

end Constructible.Godel
