/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Lemmas for tuples `Fin m → α`

This file contains alternative definitions of common operators on vectors which expand
definitionally to the expected expression when evaluated on `![]` notation.

This allows "proof by reflection", where we prove `f = ![f 0, f 1]` by defining
`FinVec.etaExpand f` to be equal to the RHS definitionally, and then prove that
`f = etaExpand f`.

The definitions in this file should normally not be used directly; the intent is for the
corresponding `*_eq` lemmas to be used in a place where they are definitionally unfolded.

## Main definitions

* `FinVec.seq`
* `FinVec.map`
* `FinVec.sum`
* `FinVec.etaExpand`
-/

assert_not_exists Field

namespace FinVec

variable {m : ℕ} {α β : Type*}

/-- Evaluate `FinVec.seq f v = ![(f 0) (v 0), (f 1) (v 1), ...]` -/
def seq : ∀ {m}, (Fin m → α → β) → (Fin m → α) → Fin m → β
  | 0, _, _ => ![]
  | _ + 1, f, v => Matrix.vecCons (f 0 (v 0)) (seq (Matrix.vecTail f) (Matrix.vecTail v))

@[simp]
theorem seq_eq : ∀ {m} (f : Fin m → α → β) (v : Fin m → α), seq f v = fun i => f i (v i)
  | 0, _, _ => Subsingleton.elim _ _
  | n + 1, f, v =>
    funext fun i => by
      simp_rw [seq, seq_eq]
      refine i.cases ?_ fun i => ?_
      · rfl
      · rw [Matrix.cons_val_succ]
        rfl

example {f₁ f₂ : α → β} (a₁ a₂ : α) : seq ![f₁, f₂] ![a₁, a₂] = ![f₁ a₁, f₂ a₂] := rfl

/-- `FinVec.map f v = ![f (v 0), f (v 1), ...]` -/
def map (f : α → β) {m} : (Fin m → α) → Fin m → β :=
  seq fun _ => f

/-- This can be used to prove
```lean
example {f : α → β} (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] :=
  (map_eq _ _).symm
```
-/
@[simp]
theorem map_eq (f : α → β) {m} (v : Fin m → α) : map f v = f ∘ v :=
  seq_eq _ _

example {f : α → β} (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] :=
  (map_eq _ _).symm

/-- Expand `v` to `![v 0, v 1, ...]` -/
def etaExpand {m} (v : Fin m → α) : Fin m → α :=
  map id v

/-- This can be used to prove
```lean
example (a : Fin 2 → α) : a = ![a 0, a 1] :=
  (etaExpand_eq _).symm
```
-/
@[simp]
theorem etaExpand_eq {m} (v : Fin m → α) : etaExpand v = v :=
  map_eq id v

example (a : Fin 2 → α) : a = ![a 0, a 1] :=
  (etaExpand_eq _).symm

/-- `∀` with better defeq for `∀ x : Fin m → α, P x`. -/
def Forall : ∀ {m} (_ : (Fin m → α) → Prop), Prop
  | 0, P => P ![]
  | _ + 1, P => ∀ x : α, Forall fun v => P (Matrix.vecCons x v)

/-- This can be used to prove
```lean
example (P : (Fin 2 → α) → Prop) : (∀ f, P f) ↔ ∀ a₀ a₁, P ![a₀, a₁] :=
  (forall_iff _).symm
```
-/
@[simp]
theorem forall_iff : ∀ {m} (P : (Fin m → α) → Prop), Forall P ↔ ∀ x, P x
  | 0, P => by
    simp only [Forall, Fin.forall_fin_zero_pi]
    rfl
  | .succ n, P => by simp only [Forall, forall_iff, Fin.forall_fin_succ_pi, Matrix.vecCons]

example (P : (Fin 2 → α) → Prop) : (∀ f, P f) ↔ ∀ a₀ a₁, P ![a₀, a₁] :=
  (forall_iff _).symm

/-- `∃` with better defeq for `∃ x : Fin m → α, P x`. -/
def Exists : ∀ {m} (_ : (Fin m → α) → Prop), Prop
  | 0, P => P ![]
  | _ + 1, P => ∃ x : α, Exists fun v => P (Matrix.vecCons x v)

/-- This can be used to prove
```lean
example (P : (Fin 2 → α) → Prop) : (∃ f, P f) ↔ ∃ a₀ a₁, P ![a₀, a₁] :=
  (exists_iff _).symm
```
-/
theorem exists_iff : ∀ {m} (P : (Fin m → α) → Prop), Exists P ↔ ∃ x, P x
  | 0, P => by
    simp only [Exists, Fin.exists_fin_zero_pi, Matrix.vecEmpty]
    rfl
  | .succ n, P => by simp only [Exists, exists_iff, Fin.exists_fin_succ_pi, Matrix.vecCons]

example (P : (Fin 2 → α) → Prop) : (∃ f, P f) ↔ ∃ a₀ a₁, P ![a₀, a₁] :=
  (exists_iff _).symm

/-- `Finset.univ.sum` with better defeq for `Fin`. -/
def sum [Add α] [Zero α] : ∀ {m} (_ : Fin m → α), α
  | 0, _ => 0
  | 1, v => v 0
  | _ + 2, v => sum (fun i => v (Fin.castSucc i)) + v (Fin.last _)

-- `to_additive` without `existing` fails, see
-- https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/to_additive.20complains.20about.20equation.20lemmas/near/508910537
/-- `Finset.univ.prod` with better defeq for `Fin`. -/
@[to_additive existing]
def prod [Mul α] [One α] : ∀ {m} (_ : Fin m → α), α
  | 0, _ => 1
  | 1, v => v 0
  | _ + 2, v => prod (fun i => v (Fin.castSucc i)) * v (Fin.last _)

/-- This can be used to prove
```lean
example [CommMonoid α] (a : Fin 3 → α) : ∏ i, a i = a 0 * a 1 * a 2 :=
  (prod_eq _).symm
```
-/
@[to_additive (attr := simp)
/-- This can be used to prove
```lean
example [AddCommMonoid α] (a : Fin 3 → α) : ∑ i, a i = a 0 + a 1 + a 2 :=
  (sum_eq _).symm
``` -/]
theorem prod_eq [CommMonoid α] : ∀ {m} (a : Fin m → α), prod a = ∏ i, a i
  | 0, _ => rfl
  | 1, a => (Fintype.prod_unique a).symm
  | n + 2, a => by rw [Fin.prod_univ_castSucc, prod, prod_eq]

example [CommMonoid α] (a : Fin 3 → α) : ∏ i, a i = a 0 * a 1 * a 2 :=
  (prod_eq _).symm

example [AddCommMonoid α] (a : Fin 3 → α) : ∑ i, a i = a 0 + a 1 + a 2 :=
  (sum_eq _).symm

section Meta
open Lean Meta Qq

/-- Produce a term of the form `f 0 * f 1 * ... * f (n - 1)` and an application of `FinVec.prod_eq`
that shows it is equal to `∏ i, f i`. -/
def mkProdEqQ {u : Level} {α : Q(Type u)} (inst : Q(CommMonoid $α)) (n : ℕ) (f : Q(Fin $n → $α)) :
    MetaM <| (val : Q($α)) × Q(∏ i, $f i = $val) := do
  match n with
  | 0 => return ⟨q((1 : $α)), q(Fin.prod_univ_zero $f)⟩
  | m + 1 =>
    let nezero : Q(NeZero ($m + 1)) := q(⟨Nat.succ_ne_zero _⟩)
    let val ← makeRHS (m + 1) f nezero (m + 1)
    let _ : $val =Q FinVec.prod $f := ⟨⟩
    return ⟨q($val), q(FinVec.prod_eq $f |>.symm)⟩
where
  /-- Creates the expression `f 0 * f 1 * ... * f (n - 1)`. -/
  makeRHS (n : ℕ) (f : Q(Fin $n → $α)) (nezero : Q(NeZero $n)) (k : ℕ) : MetaM Q($α) := do
  match k with
  | 0 => failure
  | 1 => pure q($f 0)
  | m + 1 =>
    let pre ← makeRHS n f nezero m
    let mRaw : Q(ℕ) := mkRawNatLit m
    pure q($pre * $f (OfNat.ofNat $mRaw))

/-- Produce a term of the form `f 0 + f 1 + ... + f (n - 1)` and an application of `FinVec.sum_eq`
that shows it is equal to `∑ i, f i`. -/
def mkSumEqQ {u : Level} {α : Q(Type u)} (inst : Q(AddCommMonoid $α)) (n : ℕ) (f : Q(Fin $n → $α)) :
    MetaM <| (val : Q($α)) × Q(∑ i, $f i = $val) := do
  match n with
  | 0 => return ⟨q((0 : $α)), q(Fin.sum_univ_zero $f)⟩
  | m + 1 =>
    let nezero : Q(NeZero ($m + 1)) := q(⟨Nat.succ_ne_zero _⟩)
    let val ← makeRHS (m + 1) f nezero (m + 1)
    let _ : $val =Q FinVec.sum $f := ⟨⟩
    return ⟨q($val), q(FinVec.sum_eq $f |>.symm)⟩
where
  /-- Creates the expression `f 0 + f 1 + ... + f (n - 1)`. -/
  makeRHS (n : ℕ) (f : Q(Fin $n → $α)) (nezero : Q(NeZero $n)) (k : ℕ) : MetaM Q($α) := do
  match k with
  | 0 => failure
  | 1 => pure q($f 0)
  | m + 1 =>
    let pre ← makeRHS n f nezero m
    let mRaw : Q(ℕ) := mkRawNatLit m
    pure q($pre + $f (OfNat.ofNat $mRaw))

end Meta

end FinVec

namespace Fin
open Qq Lean FinVec

/-- Rewrites `∏ i : Fin n, f i` as `f 0 * f 1 * ... * f (n - 1)` when `n` is a numeral. -/
simproc_decl prod_univ_ofNat (∏ _ : Fin _, _) := .ofQ fun u _ e => do
  match u, e with
  | .succ _, ~q(@Finset.prod (Fin $n) _ $inst (@Finset.univ _ $instF) $f) => do
    match (generalizing := false) n.nat? with
    | none =>
      return .continue
    | some nVal =>
      let ⟨res, pf⟩ ← mkProdEqQ inst nVal f
      let ⟨_⟩ ← assertDefEqQ q($instF) q(Fin.fintype _)
      have _ : $n =Q $nVal := ⟨⟩
      return .visit <| .mk q($res) <| some q($pf)
  | _, _ => return .continue

/-- Rewrites `∑ i : Fin n, f i` as `f 0 + f 1 + ... + f (n - 1)` when `n` is a numeral. -/
simproc_decl sum_univ_ofNat (∑ _ : Fin _, _) := .ofQ fun u _ e => do
  match u, e with
  | .succ _, ~q(@Finset.sum (Fin $n) _ $inst (@Finset.univ _ $instF) $f) => do
    match n.nat? with
    | none =>
      return .continue
    | some nVal =>
      let ⟨res, pf⟩ ← mkSumEqQ inst nVal f
      let ⟨_⟩ ← assertDefEqQ q($instF) q(Fin.fintype _)
      have _ : $n =Q $nVal := ⟨⟩
      return .visit <| .mk q($res) <| some q($pf)
  | _, _ => return .continue

end Fin
