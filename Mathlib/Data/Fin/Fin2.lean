/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Mathport.Rename
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Function.Basic

#align_import data.fin.fin2 from "leanprover-community/mathlib"@"c4658a649d216f57e99621708b09dcb3dcccbd23"

/-!
# Inductive type variant of `Fin`

`Fin` is defined as a subtype of `ℕ`. This file defines an equivalent type, `Fin2`, which is
defined inductively. This is useful for its induction principle and different definitional
equalities.

## Main declarations

* `Fin2 n`: Inductive type variant of `Fin n`. `fz` corresponds to `0` and `fs n` corresponds to
  `n`.
* `Fin2.toNat`, `Fin2.optOfNat`, `Fin2.ofNat'`: Conversions to and from `ℕ`. `ofNat' m` takes a
  proof that `m < n` through the class `Fin2.IsLT`.
* `Fin2.add k`: Takes `i : Fin2 n` to `i + k : Fin2 (n + k)`.
* `Fin2.left`: Embeds `Fin2 n` into `Fin2 (n + k)`.
* `Fin2.insertPerm a`: Permutation of `Fin2 n` which cycles `0, ..., a - 1` and leaves
  `a, ..., n - 1` unchanged.
* `Fin2.remapLeft f`: Function `Fin2 (m + k) → Fin2 (n + k)` by applying `f : Fin m → Fin n` to
  `0, ..., m - 1` and sending `m + i` to `n + i`.
-/

open Nat

universe u

/-- An alternate definition of `Fin n` defined as an inductive type instead of a subtype of `ℕ`. -/
inductive Fin2 : ℕ → Type
  /-- `0` as a member of `Fin (n + 1)` (`Fin 0` is empty) -/
  | fz {n} : Fin2 (n + 1)
  /-- `n` as a member of `Fin (n + 1)` -/
  | fs {n} : Fin2 n → Fin2 (n + 1)
#align fin2 Fin2

namespace Fin2

/-- Define a dependent function on `Fin2 (succ n)` by giving its value at
zero (`H1`) and by giving a dependent function on the rest (`H2`). -/
@[elab_as_elim]
protected def cases' {n} {C : Fin2 (succ n) → Sort u} (H1 : C fz) (H2 : ∀ n, C (fs n)) :
    ∀ i : Fin2 (succ n), C i
  | fz => H1
  | fs n => H2 n
#align fin2.cases' Fin2.cases'

/-- Ex falso. The dependent eliminator for the empty `Fin2 0` type. -/
def elim0 {C : Fin2 0 → Sort u} : ∀ i : Fin2 0, C i := nofun
#align fin2.elim0 Fin2.elim0

/-- Converts a `Fin2` into a natural. -/
def toNat : ∀ {n}, Fin2 n → ℕ
  | _, @fz _ => 0
  | _, @fs _ i => succ (toNat i)
#align fin2.to_nat Fin2.toNat

/-- Converts a natural into a `Fin2` if it is in range -/
def optOfNat : ∀ {n}, ℕ → Option (Fin2 n)
  | 0, _ => none
  | succ _, 0 => some fz
  | succ m, succ k => fs <$> @optOfNat m k
#align fin2.opt_of_nat Fin2.optOfNat

/-- `i + k : Fin2 (n + k)` when `i : Fin2 n` and `k : ℕ` -/
def add {n} (i : Fin2 n) : ∀ k, Fin2 (n + k)
  | 0 => i
  | succ k => fs (add i k)
#align fin2.add Fin2.add

/-- `left k` is the embedding `Fin2 n → Fin2 (k + n)` -/
def left (k) : ∀ {n}, Fin2 n → Fin2 (k + n)
  | _, @fz _ => fz
  | _, @fs _ i => fs (left k i)
#align fin2.left Fin2.left

/-- `insertPerm a` is a permutation of `Fin2 n` with the following properties:
  * `insertPerm a i = i+1` if `i < a`
  * `insertPerm a a = 0`
  * `insertPerm a i = i` if `i > a` -/
def insertPerm : ∀ {n}, Fin2 n → Fin2 n → Fin2 n
  | _, @fz _, @fz _ => fz
  | _, @fz _, @fs _ j => fs j
  | _, @fs (succ _) _, @fz _ => fs fz
  | _, @fs (succ _) i, @fs _ j =>
    match insertPerm i j with
    | fz => fz
    | fs k => fs (fs k)
#align fin2.insert_perm Fin2.insertPerm

/-- `remapLeft f k : Fin2 (m + k) → Fin2 (n + k)` applies the function
  `f : Fin2 m → Fin2 n` to inputs less than `m`, and leaves the right part
  on the right (that is, `remapLeft f k (m + i) = n + i`). -/
def remapLeft {m n} (f : Fin2 m → Fin2 n) : ∀ k, Fin2 (m + k) → Fin2 (n + k)
  | 0, i => f i
  | _k + 1, @fz _ => fz
  | _k + 1, @fs _ i => fs (remapLeft f _ i)
#align fin2.remap_left Fin2.remapLeft

/-- This is a simple type class inference prover for proof obligations
  of the form `m < n` where `m n : ℕ`. -/
class IsLT (m n : ℕ) : Prop where
  /-- The unique field of `Fin2.IsLT`, a proof that `m < n`. -/
  h : m < n
#align fin2.is_lt Fin2.IsLT

instance IsLT.zero (n) : IsLT 0 (succ n) :=
  ⟨succ_pos _⟩

instance IsLT.succ (m n) [l : IsLT m n] : IsLT (succ m) (succ n) :=
  ⟨succ_lt_succ l.h⟩

/-- Use type class inference to infer the boundedness proof, so that we can directly convert a
`Nat` into a `Fin2 n`. This supports notation like `&1 : Fin 3`. -/
def ofNat' : ∀ {n} (m) [IsLT m n], Fin2 n
  | 0, _, h => absurd h.h (Nat.not_lt_zero _)
  | succ _, 0, _ => fz
  | succ n, succ m, h => fs (@ofNat' n m ⟨lt_of_succ_lt_succ h.h⟩)
#align fin2.of_nat' Fin2.ofNat'

/-- `castSucc i` embeds `i : Fin2 n` in `Fin2 (n+1)`. -/
def castSucc {n} : Fin2 n → Fin2 (n + 1)
  | fz   => fz
  | fs k => fs <| castSucc k

/-- The greatest value of `Fin2 (n+1)`. -/
def last : {n : Nat} → Fin2 (n+1)
  | 0   => fz
  | n+1 => fs (@last n)

/-- Maps `0` to `n-1`, `1` to `n-2`, ..., `n-1` to `0`. -/
def rev {n : Nat} : Fin2 n → Fin2 n
  | .fz   => last
  | .fs i => i.rev.castSucc

@[simp] lemma rev_last {n} : rev (@last n) = fz := by
  induction n <;> simp_all [rev, castSucc, last]

@[simp] lemma rev_castSucc {n} (i : Fin2 n) : rev (castSucc i) = fs (rev i) := by
  induction i <;> simp_all [rev, castSucc, last]

@[simp] lemma rev_rev {n} (i : Fin2 n) : i.rev.rev = i := by
  induction i <;> simp_all [rev]

theorem rev_involutive {n} : Function.Involutive (@rev n) := rev_rev

@[inherit_doc] local prefix:arg "&" => ofNat'

instance : Inhabited (Fin2 1) :=
  ⟨fz⟩

instance instFintype : ∀ n, Fintype (Fin2 n)
  | 0   => ⟨∅, Fin2.elim0⟩
  | n+1 =>
    let ⟨elems, compl⟩ := instFintype n
    { elems    := elems.map ⟨Fin2.fs, @fs.inj _⟩ |>.cons .fz (by simp)
      complete := by rintro (_|i) <;> simp [compl] }

end Fin2
