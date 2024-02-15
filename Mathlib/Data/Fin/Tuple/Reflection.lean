/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin

#align_import data.fin.tuple.reflection from "leanprover-community/mathlib"@"d95bef0d215ea58c0fd7bbc4b151bf3fe952c095"

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
* `FinVec.const`
* `FinVec.single`
-/


namespace FinVec

variable {m n : ℕ} {α β γ : Type*}

/-- Evaluate `FinVec.seq f v = ![(f 0) (v 0), (f 1) (v 1), ...]` -/
def seq : ∀ {m}, (Fin m → α → β) → (Fin m → α) → Fin m → β
  | 0, _, _ => ![]
  | _ + 1, f, v => Matrix.vecCons (f 0 (v 0)) (seq (Matrix.vecTail f) (Matrix.vecTail v))
#align fin_vec.seq FinVec.seq

@[simp]
theorem seq_eq : ∀ {m} (f : Fin m → α → β) (v : Fin m → α), seq f v = fun i => f i (v i)
  | 0, f, v => Subsingleton.elim _ _
  | n + 1, f, v =>
    funext fun i => by
      simp_rw [seq, seq_eq]
      refine' i.cases _ fun i => _
      · rfl
      · rw [Matrix.cons_val_succ]
        rfl
#align fin_vec.seq_eq FinVec.seq_eq

example {f₁ f₂ : α → β} (a₁ a₂ : α) : seq ![f₁, f₂] ![a₁, a₂] = ![f₁ a₁, f₂ a₂] := rfl

/-- `FinVec.map f v = ![f (v 0), f (v 1), ...]` -/
def map (f : α → β) {m} : (Fin m → α) → Fin m → β :=
  seq fun _ => f
#align fin_vec.map FinVec.map

/-- This can be use to prove
```lean
example {f : α → β} (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] :=
  (map_eq _ _).symm
```
-/
@[simp]
theorem map_eq (f : α → β) {m} (v : Fin m → α) : map f v = f ∘ v :=
  seq_eq _ _
#align fin_vec.map_eq FinVec.map_eq

example {f : α → β} (a₁ a₂ : α) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] :=
  (map_eq _ _).symm

/-- Expand `v` to `![v 0, v 1, ...]` -/
def etaExpand {m} (v : Fin m → α) : Fin m → α :=
  map id v
#align fin_vec.eta_expand FinVec.etaExpand

/-- This can be use to prove
```lean
example (a : Fin 2 → α) : a = ![a 0, a 1] :=
  (etaExpand_eq _).symm
```
-/
@[simp]
theorem etaExpand_eq {m} (v : Fin m → α) : etaExpand v = v :=
  map_eq id v
#align fin_vec.eta_expand_eq FinVec.etaExpand_eq

example (a : Fin 2 → α) : a = ![a 0, a 1] :=
  (etaExpand_eq _).symm

/-- `∀` with better defeq for `∀ x : Fin m → α, P x`. -/
def Forall : ∀ {m} (_ : (Fin m → α) → Prop), Prop
  | 0, P => P ![]
  | _ + 1, P => ∀ x : α, Forall fun v => P (Matrix.vecCons x v)
#align fin_vec.forall FinVec.Forall

/-- This can be use to prove
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
#align fin_vec.forall_iff FinVec.forall_iff

example (P : (Fin 2 → α) → Prop) : (∀ f, P f) ↔ ∀ a₀ a₁, P ![a₀, a₁] :=
  (forall_iff _).symm

/-- `∃` with better defeq for `∃ x : Fin m → α, P x`. -/
def Exists : ∀ {m} (_ : (Fin m → α) → Prop), Prop
  | 0, P => P ![]
  | _ + 1, P => ∃ x : α, Exists fun v => P (Matrix.vecCons x v)
#align fin_vec.exists FinVec.Exists

/-- This can be use to prove
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
#align fin_vec.exists_iff FinVec.exists_iff

example (P : (Fin 2 → α) → Prop) : (∃ f, P f) ↔ ∃ a₀ a₁, P ![a₀, a₁] :=
  (exists_iff _).symm

def const : ∀ {m} (_a : α), Fin m → α
  | 0, _ => ![]
  | _ + 1, a => Matrix.vecCons a (const a)

/-- This can be use to prove
```lean
example (x : α) : Function.const _ x = ![x, x, x] :=
  const_eq _
```
-/
theorem const_eq : ∀ {m} (a : α), (const a : Fin m → α) = Function.const _ a
  | 0, _ => Subsingleton.elim _ _
  | _ + 1, a => funext <| Fin.cases rfl fun i => by rw [const, const_eq]; rfl

/-- `Pi.single` with better defeq for `Fin`. -/
def single [Zero α] : ∀ {m} (_i : Fin m) (_a : α), Fin m → α
  | 0 => fun _ _ => ![]
  | _ + 1 => Fin.cases
    (fun a => Matrix.vecCons a (const 0))
    (fun i a => Matrix.vecCons 0 (single i a))

-- TODO: move
theorem _root_.Function.Injective.single_eq
    {ι ι' α: Type*} [DecidableEq ι] [DecidableEq ι'] [Zero α] (i j : ι) (a : α) (f : ι → ι')
    (hf : Function.Injective f) :
    (Pi.single (f i) a : ι' → α) (f j) = (Pi.single i a : ι → α) j := by
  simp [Pi.single_apply, hf.eq_iff]

/-- This can be use to prove
```lean
example [Zero α] (x : α) : Pi.single 1 x = ![0, x, 0] :=
  (single_eq _ _).symm
```
-/
theorem single_eq [Zero α] : ∀ {m} (i : Fin m) (a : α),
    (single i a : Fin m → α) = Pi.single i a
  | 0, _, _ => Subsingleton.elim _ _
  | _ + 1, i, a => by
    funext j
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j =>
        dsimp [single]
        rw [Pi.single_eq_of_ne (Fin.succ_ne_zero _), const_eq]
        rfl
    | succ i =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j =>
        dsimp [single]
        rw [single_eq]
        rw [Matrix.cons_val_succ, (Fin.succ_injective _).single_eq]

example [Zero α] (x : α) : Pi.single 1 x = ![0, x, 0] :=
  (single_eq _ _).symm

/-- `Finset.univ.sum` with better defeq for `Fin`. -/
def sum [Add α] [Zero α] : ∀ {m} (_ : Fin m → α), α
  | 0, _ => 0
  | 1, v => v 0
  -- porting note: inline `∘` since it is no longer reducible
  | _ + 2, v => sum (fun i => v (Fin.castSucc i)) + v (Fin.last _)
#align fin_vec.sum FinVec.sum

open BigOperators

/-- This can be used to prove
```lean
example [AddCommMonoid α] (a : Fin 3 → α) : ∑ i, a i = a 0 + a 1 + a 2 :=
  (sum_eq _).symm
```
-/
@[simp]
theorem sum_eq [AddCommMonoid α] : ∀ {m} (a : Fin m → α), sum a = ∑ i, a i
  | 0, a => rfl
  | 1, a => (Fintype.sum_unique a).symm
  | n + 2, a => by rw [Fin.sum_univ_castSucc, sum, sum_eq]
#align fin_vec.sum_eq FinVec.sum_eq

example [AddCommMonoid α] (a : Fin 3 → α) : ∑ i, a i = a 0 + a 1 + a 2 :=
  (sum_eq _).symm

end FinVec
