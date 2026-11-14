/-
Copyright (c) 2026 Annie Yao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Annie Yao, Justin Mu, Marco David, Zhan Shi
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Homology.AInfinity.Grading
public import Mathlib.Tactic.Module

/-!
# Index triples of the Stasheff identities

The arity-n Stasheff identity is a signed sum over the triples (r, s, t) with
r + s + t = n and 1 ≤ s: the (r, s, t) summand applies an inner operation mₛ to the middle
s inputs, and an outer operation of arity r + 1 + t to the result, placed in the middle of
the remaining inputs:

$$m_{r+1+t}(a_0, \dots, a_{r-1}, m_s(a_r, \dots, a_{r+s-1}), a_{r+s}, \dots, a_{n-1})$$

For example, for n = 4 the triple (1, 2, 1) gives the summand m₃(a₀, m₂(a₁, a₂), a₃).

This file handles bookkeeping and combinatorics attached to such a triple,
as well as the degrees of the operations, and the Koszul signs.

## Main definitions

* `AInfinity.operationTargetDeg`, `AInfinity.stasheffTargetDeg`: the degrees of
  mₙ(a₀, …, aₙ₋₁) and of the arity-n Stasheff identity.
* `AInfinity.StasheffIndex`: the index triples (r, s, t) with r + s + t = n and 1 ≤ s.
* `AInfinity.stasheffSign`: the Koszul sign of the (r, s, t) summand.
* `AInfinity.signedStasheffSum`: the sum of a family of (r, s, t) terms with these signs.

## Main results

* `AInfinity.stasheffDegOut_sum`: the outer operation of the (r, s, t) summand has the
  degree of the arity-n Stasheff identity.
-/

@[expose] public section

namespace AInfinity

universe v w

variable {n : ℕ}

section Degrees

variable {β : Type v} [AddCommGroup β] [Grading β] (deg : Fin n → β)

/-- The degree of mₙ(a₀, …, aₙ₋₁) for inputs aᵢ of degrees `deg i`, where mₙ itself
has degree 2 - n. -/
abbrev operationTargetDeg : β :=
  (∑ i, deg i) + (2 - n : ℤ) • degOne

/-- The degree of the arity-n Stasheff identity on inputs of degrees `deg`. -/
abbrev stasheffTargetDeg : β :=
  (∑ i, deg i) + (3 - n : ℤ) • degOne

end Degrees

/-- An index triple (r, s, t) of the arity-n Stasheff identity: r + s + t = n and
1 ≤ s. -/
@[ext]
structure StasheffIndex (n : ℕ) where
  /-- The number of inputs before the inner operation. -/
  r : ℕ
  /-- The arity of the inner operation. -/
  s : ℕ
  /-- The number of inputs after the inner operation. -/
  t : ℕ
  /-- The three blocks of inputs make up all `n` inputs. -/
  sum_eq : r + s + t = n
  /-- The inner operation has at least one input. -/
  one_le_s : 1 ≤ s
  deriving DecidableEq

namespace StasheffIndex

/-- An index triple (r, s, t) is determined by the endpoints r and r + s of the nonempty
interval of inputs fed to the inner operation. -/
def equivLt : StasheffIndex n ≃ {x : Fin (n + 1) × Fin (n + 1) // x.1 < x.2} where
  toFun p := ⟨(⟨p.r, by have := p.sum_eq; omega⟩, ⟨p.r + p.s, by have := p.sum_eq; omega⟩),
    Fin.mk_lt_mk.2 (Nat.lt_add_of_pos_right p.one_le_s)⟩
  invFun x := ⟨x.1.1, x.1.2 - x.1.1, n - x.1.2, by have := x.1.2.isLt; omega,
    Nat.sub_pos_of_lt x.2⟩
  left_inv p := by have := p.sum_eq; ext <;> dsimp only <;> omega
  right_inv x := Subtype.ext <| Prod.ext rfl <| Fin.ext <| Nat.add_sub_cancel' x.2.le

/-- The index triples of the arity-n Stasheff identity form a finite type, through their
identification with pairs of ordered endpoints. -/
instance : Fintype (StasheffIndex n) :=
  .ofEquiv _ equivLt.symm

variable (p : StasheffIndex n)

/-- The inner operation of a Stasheff term has positive arity. -/
instance : NeZero p.s :=
  ⟨by have := p.one_le_s; omega⟩

/-- The outer operation of a Stasheff term has positive arity. -/
instance : NeZero (p.r + 1 + p.t) :=
  ⟨by omega⟩

@[simp]
lemma r_le : p.r ≤ n :=
  (Nat.le_add_right p.r p.s).trans (Nat.le.intro p.sum_eq)

@[simp]
lemma r_add_s_le : p.r + p.s ≤ n :=
  Nat.le.intro p.sum_eq

/-! ### Positions of the morphisms and objects of the inner and outer operations

The (r, s, t) summand cuts the n input morphisms into the first r inputs, the s inputs of the inner
operation and the last t inputs. As a result, it cuts the n + 1 objects into the objects r, …, r + s
of the inner operation and the objects 0, …, r and r + s, …, n of the outer operation.
The following maps record these positions among all n inputs and n + 1 objects, with the vocabulary
of `Composition`: the positions of objects are *boundaries*, the positions of input morphisms are
*indices*.

Arguments indexing input morphisms within a block are named `j`, and arguments
indexing objects are named `k`; `i` is reserved for positions among all n inputs. -/

/-- The position of the `j`-th of the first r inputs among the n inputs: `j` itself. -/
def leftIndex (j : Fin p.r) : Fin n :=
  j.castLE p.r_le

/-- The position r + j of the `j`-th input of the inner operation among the n inputs. -/
def innerIndex (j : Fin p.s) : Fin n :=
  (j.natAdd p.r).castLE p.r_add_s_le

/-- The position r + s + j of the `j`-th of the last t inputs among the n inputs. -/
def rightIndex (j : Fin p.t) : Fin n :=
  (j.natAdd (p.r + p.s)).castLE p.sum_eq.le

/-- The position r + k of the `k`-th object of the inner operation among the n + 1 objects. -/
def innerBoundary (k : Fin (p.s + 1)) : Fin (n + 1) :=
  (k.natAdd p.r).castLE (Nat.succ_le_succ p.r_add_s_le)

/-- The positions of the objects of the outer operation among the n + 1 objects are
0, …, r, followed by r + s, …, n, skipping the objects strictly between positions r and r + s. -/
def outerBoundary : Fin (p.r + 1 + p.t + 1) → Fin (n + 1) :=
  Fin.append (m := p.r + 1) (Fin.castLE (Nat.succ_le_succ p.r_le))
    fun k : Fin (p.t + 1) ↦ (k.natAdd (p.r + p.s)).castLE (Nat.succ_le_succ p.sum_eq.le)

/-- The position of the inner output among the inputs of the outer operation is r. -/
abbrev middleIndex : Fin (p.r + 1 + p.t) :=
  (Fin.last p.r).castAdd p.t

@[simp]
lemma val_leftIndex (j : Fin p.r) : (p.leftIndex j : ℕ) = j :=
  rfl

@[simp]
lemma val_innerIndex (j : Fin p.s) : (p.innerIndex j : ℕ) = p.r + j :=
  rfl

@[simp]
lemma val_rightIndex (j : Fin p.t) : (p.rightIndex j : ℕ) = p.r + p.s + j :=
  rfl

@[simp]
lemma val_innerBoundary (k : Fin (p.s + 1)) : (p.innerBoundary k : ℕ) = p.r + k :=
  rfl

/-- Up to position r, the outer object string follows the original one. -/
@[simp]
lemma val_outerBoundary_castAdd (k : Fin (p.r + 1)) :
    (p.outerBoundary (k.castAdd (p.t + 1)) : ℕ) = k := by
  simp [outerBoundary]

/-- After position r, the outer object string skips the s - 1 objects strictly inside the
inner block. -/
@[simp]
lemma val_outerBoundary_natAdd (k : Fin (p.t + 1)) :
    (p.outerBoundary (k.natAdd (p.r + 1)) : ℕ) = p.r + p.s + k := by
  simp [outerBoundary]

/-- The source of the `j`-th input of the inner operation is the `j`-th inner object. -/
@[simp]
lemma innerBoundary_castSucc (j : Fin p.s) :
    p.innerBoundary j.castSucc = (p.innerIndex j).castSucc :=
  rfl

/-- The target of the `j`-th input of the inner operation is the `(j + 1)`-st inner object. -/
@[simp]
lemma innerBoundary_succ (j : Fin p.s) : p.innerBoundary j.succ = (p.innerIndex j).succ :=
  rfl

/-- The outer object string starts at the object 0. -/
@[simp]
lemma outerBoundary_zero : p.outerBoundary 0 = 0 :=
  Fin.ext (p.val_outerBoundary_castAdd 0)

/-- The outer object string ends at the object n. -/
@[simp]
lemma outerBoundary_last : p.outerBoundary (Fin.last _) = Fin.last n :=
  Fin.ext ((p.val_outerBoundary_natAdd (Fin.last p.t)).trans p.sum_eq)

/-- Before the inner output, the source of an outer input is the source of the original
input. -/
@[simp]
lemma outerBoundary_left_castSucc (j : Fin p.r) :
    p.outerBoundary (j.castSucc.castAdd p.t).castSucc = (p.leftIndex j).castSucc :=
  Fin.ext (p.val_outerBoundary_castAdd j.castSucc)

/-- Before the inner output, the target of an outer input is the target of the original
input. -/
@[simp]
lemma outerBoundary_left_succ (j : Fin p.r) :
    p.outerBoundary (j.castSucc.castAdd p.t).succ = (p.leftIndex j).succ :=
  Fin.ext (p.val_outerBoundary_castAdd j.succ)

/-- The source of the inner output, as an outer input, is the first inner object. -/
@[simp]
lemma outerBoundary_middle_castSucc : p.outerBoundary p.middleIndex.castSucc = p.innerBoundary 0 :=
  Fin.ext (p.val_outerBoundary_castAdd (Fin.last p.r))

/-- The target of the inner output, as an outer input, is the last inner object. -/
@[simp]
lemma outerBoundary_middle_succ :
    p.outerBoundary p.middleIndex.succ = p.innerBoundary (Fin.last p.s) :=
  Fin.ext (p.val_outerBoundary_natAdd 0)

/-- After the inner output, the source of an outer input is the source of the original
input. -/
lemma outerBoundary_right_castSucc (j : Fin p.t) :
    p.outerBoundary (j.natAdd (p.r + 1)).castSucc = (p.rightIndex j).castSucc :=
  Fin.ext (p.val_outerBoundary_natAdd j.castSucc)

/-- After the inner output, the target of an outer input is the target of the original
input. -/
@[simp]
lemma outerBoundary_right_succ (j : Fin p.t) :
    p.outerBoundary (j.natAdd (p.r + 1)).succ = (p.rightIndex j).succ :=
  Fin.ext (p.val_outerBoundary_natAdd j.succ)

/-- The first r inputs, the s inputs of the inner operation and the last t inputs make up
all n inputs. -/
@[to_additive]
lemma prod_leftIndex_mul_prod_innerIndex_mul_prod_rightIndex {M : Type*} [CommMonoid M]
    (f : Fin n → M) :
    (∏ j, f (p.leftIndex j)) * (∏ j, f (p.innerIndex j)) * ∏ j, f (p.rightIndex j) = ∏ i, f i := by
  rw [← Fin.prod_congr' f p.sum_eq, Fin.prod_univ_add, Fin.prod_univ_add]
  rfl

end StasheffIndex

section ObjectStrings

/- Throughout this section, let `X 0`, …, `X n` be a given string of objects which form the
sources and targets of the morphisms `aᵢ : X i → X (i + 1)` that appear in any Stasheff term. -/
variable {Obj : Type w} (X : Fin (n + 1) → Obj) (p : StasheffIndex n)

/-- The object string of the inner operation is `X r`, …, `X (r + s)`. -/
def stasheffObjIn : Fin (p.s + 1) → Obj :=
  fun k ↦ X (p.innerBoundary k)

/-- The object string of the outer operation of the (r, s, t) summand, obtained from `X` by
deleting the objects strictly between positions r and r + s. -/
def stasheffObjOut : Fin (p.r + 1 + p.t + 1) → Obj :=
  fun k ↦ X (p.outerBoundary k)

/-- The outer object string starts at `X 0`. -/
@[simp]
lemma stasheffObjOut_zero : stasheffObjOut X p 0 = X 0 :=
  congrArg X p.outerBoundary_zero

/-- The outer object string ends at `X (Fin.last n)`. -/
@[simp]
lemma stasheffObjOut_last : stasheffObjOut X p (Fin.last (p.r + 1 + p.t)) = X (Fin.last n) :=
  congrArg X p.outerBoundary_last

/-- Before the inner output, the source of an outer input is the source of the original
input. -/
@[simp]
lemma stasheffObjOut_left_castSucc (j : Fin p.r) :
    stasheffObjOut X p (j.castSucc.castAdd p.t).castSucc = X (p.leftIndex j).castSucc :=
  congrArg X (p.outerBoundary_left_castSucc j)

/-- Before the inner output, the target of an outer input is the target of the original
input. -/
@[simp]
lemma stasheffObjOut_left_succ (j : Fin p.r) :
    stasheffObjOut X p (j.castSucc.castAdd p.t).succ = X (p.leftIndex j).succ :=
  congrArg X (p.outerBoundary_left_succ j)

/-- The source of the inner output, as an outer input, is the first inner object. -/
@[simp]
lemma stasheffObjOut_middle_castSucc :
    stasheffObjOut X p p.middleIndex.castSucc = stasheffObjIn X p 0 :=
  congrArg X p.outerBoundary_middle_castSucc

/-- The target of the inner output, as an outer input, is the last inner object. -/
@[simp]
lemma stasheffObjOut_middle_succ :
    stasheffObjOut X p p.middleIndex.succ = stasheffObjIn X p (Fin.last p.s) :=
  congrArg X p.outerBoundary_middle_succ

/-- After the inner output, the source of an outer input is the source of the original
input. -/
lemma stasheffObjOut_right_castSucc (j : Fin p.t) :
    stasheffObjOut X p (j.natAdd (p.r + 1)).castSucc = X (p.rightIndex j).castSucc :=
  congrArg X (p.outerBoundary_right_castSucc j)

/-- After the inner output, the target of an outer input is the target of the original
input. -/
@[simp]
lemma stasheffObjOut_right_succ (j : Fin p.t) :
    stasheffObjOut X p (j.natAdd (p.r + 1)).succ = X (p.rightIndex j).succ :=
  congrArg X (p.outerBoundary_right_succ j)

end ObjectStrings

section Degrees

/- Throughout this section, let `deg i` denote the degree of the morphism `aᵢ` that appears
in a Stasheff term. -/
variable {β : Type v} [AddCommGroup β] [Grading β] (deg : Fin n → β) (p : StasheffIndex n)

/-- The input degrees for the inner operation mₛ. -/
def stasheffDegIn : Fin p.s → β :=
  fun j ↦ deg (p.innerIndex j)

/-- The degree of the output of the inner operation mₛ. -/
def stasheffInnerDeg : β :=
  operationTargetDeg (stasheffDegIn deg p)

/-- The input degrees for the outer operation $m_{r+1+t}$. -/
def stasheffDegOut : Fin (p.r + 1 + p.t) → β :=
  Fin.append (Fin.snoc (fun j ↦ deg (p.leftIndex j)) (stasheffInnerDeg deg p))
    fun j ↦ deg (p.rightIndex j)

@[simp]
lemma stasheffDegOut_left (j : Fin p.r) :
    stasheffDegOut deg p (j.castSucc.castAdd p.t) = deg (p.leftIndex j) := by
  simp [stasheffDegOut]

@[simp]
lemma stasheffDegOut_middle : stasheffDegOut deg p p.middleIndex = stasheffInnerDeg deg p := by
  simp [stasheffDegOut]

@[simp]
lemma stasheffDegOut_right (j : Fin p.t) :
    stasheffDegOut deg p (j.natAdd (p.r + 1)) = deg (p.rightIndex j) := by
  simp [stasheffDegOut]

/-- The result of the outer operation has the correct Stasheff target degree. -/
lemma stasheffDegOut_sum :
    operationTargetDeg (stasheffDegOut deg p) = stasheffTargetDeg deg := by
  have h : (n : ℤ) = p.r + p.s + p.t := by exact_mod_cast p.sum_eq.symm
  simp only [operationTargetDeg, stasheffTargetDeg, Fin.sum_univ_add, stasheffDegOut_left,
    stasheffDegOut_middle, stasheffDegOut_right, Fin.sum_univ_castSucc, stasheffInnerDeg,
    stasheffDegIn, ← p.sum_leftIndex_add_sum_innerIndex_add_sum_rightIndex deg]
  rw [h]
  module

/-- The Koszul sign of the Stasheff term is (-1) raised to the sum of the reduced degrees
‖a‖ = |a| - 1 of the last t inputs. -/
def stasheffSign : ℤˣ :=
  ∏ j : Fin p.t, (sign (deg (p.rightIndex j) - degOne)).toMul

/-- The signed sum `∑ p, stasheffSign deg p • f p` over the index triples `p : StasheffIndex n`
of the arity-n Stasheff identity. -/
def signedStasheffSum {M : Type*} [AddCommGroup M] (f : StasheffIndex n → M) : M :=
  ∑ q, stasheffSign deg q • f q

end Degrees

end AInfinity
