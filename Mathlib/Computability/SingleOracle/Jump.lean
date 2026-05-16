/-
Copyright (c) 2026 Edwin Park. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edwin Park
-/
import Mathlib.Computability.SingleOracle.Constructions.Basic
import Mathlib.Computability.SingleOracle.Constructions.Primitive
import Mathlib.Computability.SingleOracle.Constructions.Meta
import Mathlib.Computability.SingleOracle.Order

/-!
# Jump.lean

This file defines the jump operator on total functions, and basic reducibility results
involving the jump.

## Main declarations
- `K0` : the K₀ operator, on total functions
- `K`  : the K operator, on total functions
- `jump`: the jump operator, on total functions

- `K0_eq_K` : asserts that K and K0 are of the same degree
- `not_jump_le` : asserts that the jump of an oracle is strictly above the oracle
-/

open Computability
open Oracle.Single

open Classical in
/--
An analogue of the K₀ operator for total-function oracles, which encodes
computation values on top of whether or not they converge.
-/
@[simp] noncomputable def K0 (O : ℕ → ℕ) : ℕ → ℕ := fun n =>
  let part := eval O n.left n.right
  if h : part.Dom then (part.get h) + 1 else 0
open Classical in
/--
An analogue of the K operator for total-function oracles, which encodes
computation values on top of whether or not they converge.
-/
@[simp] noncomputable def K (O : ℕ → ℕ) : ℕ → ℕ := fun n =>
  let part := eval O n n
  if h : part.Dom then (part.get h) + 1 else 0
noncomputable abbrev jump (O : ℕ → ℕ) : ℕ → ℕ := K0 O

notation : 10000 f"⌜" => jump f

namespace Oracle.Single.Code

section jump_decode
/--
The code `c_jump_decode` is intended for use where the output of a query to `K0`
has to be "decoded".

(Note that `K0` encodes Part.none with 0, and Part.some x with x+1.)
-/
def c_jump_decode (c : Code) := c_ite c c_diverge (c_pred.comp c)
open Classical in
@[simp, ev_simps] theorem c_jump_decode_ev {O : ℕ → ℕ} {c : Code} {x : ℕ} (hc : code_total O c) :
    eval O (c_jump_decode c) x =
    if eval O c x = Part.some 0 then Part.none else (Nat.pred <$> eval O c x) := by
  simp only [c_jump_decode, ev_simps, Part.map_eq_map]
  simp only [c_ite_ev hc, c_diverge_ev]
  congr
  simp only [ev_simps, Part.bind_eq_bind]
  if h : (eval O c x).Dom then
    rewrite [Part.get_eq_iff_eq_some.mp (Part.get_eq_get_of_eq _ h rfl)]
    simp [-Part.some_get]
  else
    simp [Part.eq_none_iff'.mpr h]
open Classical in
@[simp, ev_simps] theorem c_jump_decode_ev' {O c} (hc : code_total O c) :
    eval O (c_jump_decode c) =
    fun x => if eval O c x = Part.some 0 then Part.none else (Nat.pred <$> eval O c x) := by
  funext xs
  exact c_jump_decode_ev hc
end jump_decode

/--
We can retrieve the value of `O x` from `(K0 O) x` by
decoding it with `c_jump_decode`.
-/
theorem le_K0 (O : ℕ → ℕ) :  O ≤ᵀᶠ (K0 O) := by
  apply exists_code.mpr  -- changes goal to: ∃ c, eval (K0 O) c = O
  let q := oracle.comp (pair (c_const oracle) c_id)
  use c_jump_decode q
  have compute_total : code_total (K0 O) q := by apply prim_total; apply_cp
  simpa [compute_total, q, ev_simps, Seq.seq] using by exact rfl
theorem le_jump (O : ℕ → ℕ) : O ≤ᵀᶠ O⌜ := le_K0 O

open Classical in
/--
We use the fact that `K O x = K0 O ⟪x, x⟫`.
-/
theorem K_le_K0 (O : ℕ → ℕ) : (K O) ≤ᵀᶠ (K0 O) := by
  apply exists_code.mpr
  use oracle.comp <| pair c_id c_id
  simpa [ev_simps, Seq.seq] using by exact rfl

open Classical in
/--
We wish to calculate `K0 O x` i.e. `eval O x.left x.r` with access to `K`.
We use `c_ev_const`, which returns the code of the function that
calculates `eval O x.left x.r` for all inputs.
By querying this to `K`, we are done.
-/
theorem K0_le_K (O : ℕ → ℕ) : (K0 O) ≤ᵀᶠ (K O) := by
  apply exists_code.mpr
  let compute := oracle.comp c_ev_const
  use compute
  have compute_total : code_total (K O) compute := by apply prim_total; apply_cp
  funext x
  rw [eval_total_comp compute_total]
  simp [eval, c_ev_const_ev']

theorem K_eq_K0 {O : ℕ → ℕ} : (K O)  ≡ᵀᶠ (K0 O) := ⟨K_le_K0 O,K0_le_K O⟩
theorem K0_eq_K {O : ℕ → ℕ} : (K0 O) ≡ᵀᶠ (K O) := K_eq_K0.symm
theorem le_K (O : ℕ → ℕ) : O ≤ᵀᶠ (K O) := .trans (le_K0 O) (K0_le_K O)

open Classical in
/--
To show that the jump of `O` is not reducible to `O`,
suppose bwoc it is.

Then, we may construct a code `g` that diverges/converges if its
input converges/diverges on itself.

A contradiction arises if we ask whether `g` converges on itself.
-/
theorem not_jump_le (O : ℕ → ℕ) : ¬(O⌜ ≤ᵀᶠ O) := by
  intro h
  rcases exists_code.mp h with ⟨c_jump, hc_jump⟩
  let g := c_ite (c_jump.comp (pair c_id c_id)) zero c_diverge
  have hg :
      eval O g = fun (x : ℕ) =>
      if (O⌜) (Nat.pair x x) = 0 then
        Part.some 0
      else
        Part.none := by
    unfold g
    funext x
    have : code_total O (c_jump.comp (pair c_id c_id)) := by
      intro x; simp [eval, hc_jump, Seq.seq]
    simp [c_ite_ev this, eval, hc_jump, Seq.seq]
  cases Classical.em (eval O g g).Dom with
  | inl h => have h' := h; rw [hg] at h'; simp [h] at h'
  | inr h => have h' := h; rw [hg] at h'; simp [h] at h'

theorem not_K_le (O : ℕ → ℕ) : ¬(K O ≤ᵀᶠ O) :=
  fun h => not_jump_le O (.trans (K0_le_K O) h)

theorem lt_K0 {O : ℕ → ℕ} : O <ᵀᶠ (K0 O) := ⟨le_jump O,not_jump_le O⟩

end Oracle.Single.Code
