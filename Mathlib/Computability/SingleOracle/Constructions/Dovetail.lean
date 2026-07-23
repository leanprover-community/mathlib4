/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Mathlib.Computability.SingleOracle.Constructions.Eval

/-!
# Dovetail.lean

This file defines `dovetail c`, a code which dovetails the code `c`;
`dovetail c` gives the code to the function which, on input `n`,
returns `y` s.t. `[c](n,y)=0`.

This `y` may not be minimal.

If such a `y` exists, `dovetail c` is guaranteed to find it.

## Construction

def dovetail c x :
  find the smallest y s.t. [c]_{y.l}(x, y.right) = 0. -- this can be done with rfind.
  return y.right

Note then that this guarantees: `∃ y,[c](x,y)=0 ↔ [dovetail c](x)↓`

## Main declarations

- `dovetail` : Code → Code : returns a code which dovetails the input code.
- `dovetail_ev_0`: asserts that if the dovetail procedure `dovetail c n` halts,
    the acquired value `y` satisfies `[c](n,y)=0`.
- `dovetail_ev_1`: asserts that the dovetail procedure `dovetail c n`
    diverges iff there is no `y` s.t. `[c](n,y)=0`.
- `dovetail_ev_2`: asserts that the dovetail procedure `dovetail c n`
    halts iff there is a `y` s.t. `[c](n,y)=0`.

-/

open Nat Part

namespace Oracle.Single.Code

/-
We implement
-/
def dovetailn (c : Code) : Code :=
  c_rfind <|
  c_if_eq'.comp₂
  (c_evaln.comp₃ (pair left (left.comp right)) (c_const c) (right.comp right))
  (c_const 1)

set_option linter.unusedVariables false in -- why does hdvt give a warning?
theorem dovetailn_ev_0 {O : ℕ → ℕ} {c : Code} {x : ℕ} (h : (eval O (dovetailn c) x).Dom) :
let (eq := hdvt) dvt := (eval O (dovetailn c) x).get h
evaln O dvt.right c ⟪x, dvt.left⟫=Option.some 0 := by
  extract_lets; expose_names
  unfold dovetailn at h hdvt
  have := Part.get_mem h
  rw [← hdvt] at this
  simp only [c_rfind_ev, mem_rfind, ev_simps] at this
  simp? at this says
    simp only [unpair_pair, coe_some, map_eq_map, map_some, unpair1_to_l, bind_eq_bind, bind_some,
    unpair2_to_r, Part.map_bind, mem_bind_iff, mem_map_iff, decide_eq_true_eq, exists_eq_right,
    decide_eq_false_iff_not] at this
  rcases this with ⟨⟨h2, h3, h4⟩, h5⟩; clear h5
  simp? [Seq.seq]  at h3 says
    simp only [Seq.seq, map_some, bind_some, c_evaln_ev, Nat.n2c, n2c_c2n, coe_some,
      mem_some_iff] at h3
  rw [h3] at h4; clear h3;
  simp only [pair_l, pair_r] at h4
  have := Part.eq_some_iff.mpr h4; clear h4
  simp? [o2n] at this says
    simp only [o2n, ite_eq_left_iff, some_inj, one_ne_zero, imp_false, Decidable.not_not] at this
  exact Encodable.encode_inj.mp this
theorem dovetailn_ev_0' {O : ℕ → ℕ} {c : Code} {x : ℕ} (h : (eval O (dovetailn c) x).Dom) :
let dvt := (eval O (dovetailn c) x).get h
eval O c ⟪x, dvt.left⟫=Part.some 0 := by
  have := dovetailn_ev_0 h
  extract_lets
  expose_names
  extract_lets at this
  exact Part.eq_some_iff.mpr (evaln_sound this)

lemma Part.eq_none_iff_forall_ne_some {α} {o : Part α} : o = Part.none ↔ ∀ a, o ≠ Part.some a := by
  simpa using (@Part.ne_none_iff _ o).not
lemma Part.not_none_iff_dom {α} {o : Part α} : (o ≠ Part.none) ↔ (o.Dom) := by
  apply Iff.intro
  · intro a
    simp only [eq_none_iff_forall_ne_some, ne_eq, not_forall, not_not] at a
    rcases a with ⟨h1,h2⟩
    rw [h2]
    exact trivial
  · intro a
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    exact a
theorem dovetailn_ev_1' {O : ℕ → ℕ} {c : Code} {x : ℕ} :
    eval O (dovetailn c) x=Part.none ↔ ∀ s y, evaln O s c ⟪x, y⟫ ≠ Option.some 0 := by
  constructor
  · contrapose
    simp? says
      simp only [ne_eq, not_forall, Decidable.not_not, forall_exists_index]
    intro s y h
    apply Part.not_none_iff_dom.mpr
    unfold dovetailn
    simp only [c_rfind_ev]
    simp only [comp₂, comp₃] -- without this theres a recursion depth error. why?
    simp? says
      simp only [rfind_dom, map_eq_map, mem_map_iff, decide_eq_true_eq, exists_eq_right, map_Dom]
    use ⟪y, s⟫
    simp [eval, Seq.seq]
    constructor <;> aesop
  · contrapose
    intro h
    simp? says simp only [ne_eq, not_forall, Decidable.not_not]
    have hh := Part.not_none_iff_dom.mp h
    have := dovetailn_ev_0 hh
    aesop? says
      apply Exists.intro
      · apply Exists.intro
        exact this

theorem dovetailn_ev_1_aux {O : ℕ → ℕ} {c : Code} {x : ℕ} :
    (∀ s y, evaln O s c ⟪x, y⟫ ≠ Option.some 0) ↔ ∀ y, eval O c ⟪x, y⟫ ≠ Part.some 0 := by
  constructor
  · contrapose
    simp only [ne_eq, not_forall, not_not, forall_exists_index]
    intro y h
    have := evaln_complete.mp (Part.eq_some_iff.mp h)
    aesop
  · contrapose
    simp only [ne_eq, not_forall, Decidable.not_not, not_not, forall_exists_index]
    intro s y h
    use y
    exact Part.eq_some_iff.mpr (evaln_sound h)

theorem dovetailn_ev_1 {O : ℕ → ℕ} {c : Code} {x : ℕ} :
    eval O (dovetailn c) x=Part.none ↔ ∀ y, eval O c ⟪x, y⟫ ≠ Part.some 0 :=
  Iff.trans dovetailn_ev_1' dovetailn_ev_1_aux
theorem dovetailn_ev_2 {O : ℕ → ℕ} {c : Code} {x : ℕ} :
    (eval O (dovetailn c) x).Dom ↔ ∃ y, eval O c ⟪x, y⟫=Part.some 0 := by
  have := (@dovetailn_ev_1 O c x).not
  simpa using Iff.trans (Iff.symm Part.not_none_iff_dom) this

def dovetail (c : Code) : Code := left.comp (dovetailn c)

theorem dovetail_dom_iff_dovetailn_dom {O : ℕ → ℕ} {c : Code} {x : ℕ} :
    (eval O (dovetail c) x).Dom ↔ (eval O (dovetailn c) x).Dom := by
  simp [dovetail,eval]
theorem dovetail_none_iff_dovetailn_none {O : ℕ → ℕ} {c : Code} {x : ℕ} :
    (eval O (dovetail c) x) = Part.none ↔ (eval O (dovetailn c) x) = Part.none := by
  apply not_iff_not.mp
  simpa [Part.not_none_iff_dom] using dovetail_dom_iff_dovetailn_dom
theorem dovetail_ev_0 {O : ℕ → ℕ} {c : Code} {x : ℕ} (h : (eval O (dovetail c) x).Dom) :
    let dvt := (eval O (dovetail c) x).get h
    eval O c ⟪x, dvt⟫ = Part.some 0 := by
  have : (eval O (dovetailn c) x).Dom := dovetail_dom_iff_dovetailn_dom.mp h
  have main := dovetailn_ev_0' this
  extract_lets
  extract_lets at main
  expose_names
  have : dvt = dvt_1.left := by simp [dvt_1,dvt,dovetail, eval, Part.Dom.bind this]
  rw [this]
  exact main

theorem dovetail_ev_1' {O : ℕ → ℕ} {c : Code} {x : ℕ} :
    eval O (dovetail c) x=Part.none ↔ ∀ s y, evaln O s c ⟪x, y⟫ ≠ Option.some 0 := by
  simpa [dovetail_none_iff_dovetailn_none] using dovetailn_ev_1'
theorem dovetail_ev_1 {O : ℕ → ℕ} {c : Code} {x : ℕ} :
    eval O (dovetail c) x=Part.none ↔ ∀ y, eval O c ⟪x, y⟫ ≠ Part.some 0 :=
  Iff.trans dovetail_ev_1' dovetailn_ev_1_aux
theorem dovetail_ev_2 {O : ℕ → ℕ} {c : Code} {x : ℕ} :
    (eval O (dovetail c) x).Dom ↔ ∃ y, eval O c ⟪x, y⟫=Part.some 0 := by
  have := (@dovetail_ev_1 O c x).not
  simp only [ne_eq, not_forall, not_not] at this
  exact Iff.trans (Iff.symm Part.not_none_iff_dom) this
end Oracle.Single.Code
