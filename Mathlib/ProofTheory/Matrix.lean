/-
Copyright (c) 2024 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Nat.Pairing

/-!
Temporary file to be moved to VecNotation
-/

universe u u1

namespace Matrix
open Fin
section
variable {n : ℕ} {α β: Type u}

@[simp] lemma vecCons_succ (i : Fin n)  (a : α) (s : Fin n → α) :
    (a :> s) (Fin.succ i) = s i := by simp

@[simp] lemma cons_app_one {n : ℕ} (a : α) (s : Fin n.succ → α) : (a :> s) 1 = s 0 := rfl

@[simp] lemma cons_app_two {n : ℕ} (a : α) (s : Fin n.succ.succ → α) : (a :> s) 2 = s 1 := rfl

@[simp] lemma cons_app_three {n : ℕ} (a : α) (s : Fin n.succ.succ.succ → α) : (a :> s) 3 = s 2 :=
  rfl

section delab
open Lean PrettyPrinter Delaborator SubExpr

/-- `unexpandVecEmpty` -/
@[app_unexpander Matrix.vecEmpty]
def unexpandVecEmpty : Unexpander
  | `($(_)) => `(![])

/-- `unexpandVecCons` -/
@[app_unexpander Matrix.vecCons]
def unexpandVecCons : Unexpander
  | `($(_) $a ![])      => `(![$a])
  | `($(_) $a ![$as,*]) => `(![$a, $as,*])
  | _                   => throw ()

end delab

@[simp] lemma rightConcat_zero (a : α) (s : Fin n.succ → α) :
    (s <: a) 0 = s 0 := rightConcat_castSucc 0

@[simp] lemma zero_succ_eq_id {n} : (0 : Fin (n + 1)) :> succ = id :=
  funext $ Fin.cases (by simp) (by simp)

lemma eq_vecCons {C : Type u} (s : Fin (n + 1) → C) : s = s 0 :> s ∘ Fin.succ :=
   funext $ Fin.cases (by simp) (by simp)

@[simp] lemma vecCons_ext (a₁ a₂ : α) (s₁ s₂ : Fin n → α) :
    a₁ :> s₁ = a₂ :> s₂ ↔ a₁ = a₂ ∧ s₁ = s₂ :=
  ⟨by intros h
      constructor
      · exact congrFun h 0
      · exact funext (fun i => by simpa using congrFun h (Fin.castSucc i + 1)),
   by intros h; simp[h]⟩

lemma vecCons_assoc (a b : α) (s : Fin n → α) :
    a :> (s <: b) = (a :> s) <: b := by
  funext x; cases' x using Fin.cases with x <;> simp; cases x using Fin.lastCases <;>
  simp[Fin.succ_castSucc]

/-- Decidable vector equality -/
def decVec {α : Type _} : {n : ℕ} → (v w : Fin n → α) → (∀ i, Decidable (v i = w i)) →
    Decidable (v = w)
  | 0,     _, _, _ => by simp[Matrix.empty_eq]; exact isTrue trivial
  | n + 1, v, w, d => by
      rw[eq_vecCons v, eq_vecCons w, vecCons_ext]
      haveI : Decidable (v ∘ Fin.succ = w ∘ Fin.succ) := decVec _ _ (by intros i; simp; exact d _)
      refine instDecidableAnd

lemma comp_vecCons (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (a :> s) x) = f a :> f ∘ s :=
funext (fun i => cases (by simp) (by simp) i)

lemma comp_vecCons' (f : α → β) (a : α) (s : Fin n → α) :
    (fun x => f $ (a :> s) x) = f a :> fun i => f (s i) :=
  comp_vecCons f a s

lemma comp_vecCons'' (f : α → β) (a : α) (s : Fin n → α) : f ∘ (a :> s) = f a :> f ∘ s :=
  comp_vecCons f a s

@[simp] lemma comp₀ (f : α → β) : f ∘ (![] : Fin 0 → α) = ![] := by simp[Matrix.empty_eq]

@[simp] lemma comp₁ (a : α) (f : α → β) : f ∘ ![a] = ![f a] := by simp[comp_vecCons'']

@[simp] lemma comp₂ (a₁ a₂ : α) (f : α → β) : f ∘ ![a₁, a₂] = ![f a₁, f a₂] := by
  simp[comp_vecCons'']

@[simp] lemma comp₃ (a₁ a₂ a₃ : α) (f : α → β) : f ∘ ![a₁, a₂, a₃] = ![f a₁, f a₂, f a₃] := by
  simp[comp_vecCons'']

lemma vecConsLast_vecEmpty {s : Fin 0 → α} (a : α) : s <: a = ![a] :=
  funext (fun x => by
    have : 0 = Fin.last 0 := by rfl
    cases' x using Fin.cases with i <;> simp[this]
    have := i.isLt; contradiction )

lemma constant_eq_singleton {a : α} : (fun _ => a) = ![a] := by funext x; simp

lemma constant_eq_singleton' {v : Fin 1 → α} : v = ![v 0] := by funext x; simp[Fin.eq_zero]

lemma constant_eq_vec₂ {a : α} : (fun _ => a) = ![a, a] := by
  funext x; cases x using Fin.cases <;> simp[Fin.eq_zero]

lemma fun_eq_vec₂ {v : Fin 2 → α} : v = ![v 0, v 1] := by
  funext x; cases x using Fin.cases <;> simp[Fin.eq_zero]

lemma injective_vecCons {f : Fin n → α} (h : Function.Injective f) {a} (ha : ∀ i, a ≠ f i) :
    Function.Injective (a :> f) := by
  have : ∀ i, f i ≠ a := fun i => (ha i).symm
  intro i j; cases i using Fin.cases <;> cases j using Fin.cases <;> simp[*]
  intro hf; exact h hf

end

variable {α : Type _} {n : ℕ}

/-- Translate `Vector` to `List` -/
def toList : {n : ℕ} → (Fin n → α) → List α
  | 0,     _ => []
  | _ + 1, v => v 0 :: toList (v ∘ Fin.succ)

@[simp] lemma toList_zero (v : Fin 0 → α) : toList v = [] := rfl

@[simp] lemma toList_succ (v : Fin (n + 1) → α) : toList v = v 0 :: toList (v ∘ Fin.succ) := rfl

@[simp] lemma toList_length (v : Fin n → α) : (toList v).length = n :=
  by induction n <;> simp[*]

@[simp] lemma toList_nth (v : Fin n → α) (i) (hi) :
    (toList v).nthLe i hi = v ⟨i, by simpa using hi⟩ := by
  induction n generalizing i <;> simp[*, List.nthLe_cons]
  case zero => contradiction
  case succ => rcases i <;> simp

@[simp] lemma mem_toList_iff {v : Fin n → α} {a} : a ∈ toList v ↔ ∃ i, v i = a := by
  induction n <;>
  simp[*];
  constructor;
  { rintro (rfl | ⟨i, rfl⟩) <;> simp }; { rintro ⟨i, rfl⟩; cases i using Fin.cases <;> simp }

/-- Convert to option vector -/
def toOptionVec : {n : ℕ} → (Fin n → Option α) → Option (Fin n → α)
  | 0,     _ => some vecEmpty
  | _ + 1, v => (toOptionVec (v ∘ Fin.succ)).bind (fun vs => (v 0).map (fun z => z :> vs))

@[simp] lemma toOptionVec_some (v : Fin n → α) : toOptionVec (fun i => some (v i)) = some v := by
  induction n <;>
  simp[*, Matrix.empty_eq, toOptionVec, Function.comp];
  exact funext (Fin.cases (by simp) (by simp))

@[simp] lemma toOptionVec_zero (v : Fin 0 → Option α) : toOptionVec v = some ![] := rfl

@[simp] lemma toOptionVec_eq_none_iff {v : Fin n → Option α} :
    toOptionVec v = none ↔ ∃ i, v i = none := by
  induction' n with n ih
  · simp
  · simp[toOptionVec]
    rcases hz : v 0 with (_ | a) <;> simp
    { exact ⟨0, hz⟩ }
    { rcases hs : toOptionVec (v ∘ Fin.succ) with (_ | w) <;> simp
      { rcases ih.mp hs with ⟨i, hi⟩
        exact ⟨i.succ, hi⟩ }
      { intro x; cases x using Fin.cases
        · simp[hz]
        · have : toOptionVec (v ∘ Fin.succ) ≠ none ↔ ∀ i : Fin n, v i.succ ≠ none :=
            by simpa using not_iff_not.mpr (@ih (v ∘ Fin.succ))
          exact this.mp (by simp[hs]) _ } }

@[simp] lemma toOptionVec_eq_some_iff {v : Fin n → Option α} {w : Fin n → α} :
    toOptionVec v = some w ↔ ∀ i, v i = some (w i) := by
  induction' n with n ih
  · simp[Matrix.empty_eq]
  · simp[toOptionVec]
    rcases hz : v 0 with (_ | a) <;> simp
    { exact ⟨0, by simp[hz]⟩ }
    { rcases hs : toOptionVec (v ∘ Fin.succ) with (_ | z) <;> simp
      { have : ∃ i : Fin n, v i.succ = none := by simpa using hs
        rcases this with ⟨i, hi⟩
        exact ⟨i.succ, by simp[hi]⟩ }
      { have : ∀ i, v i.succ = some (z i) := ih.mp hs
        have : v = some a :> (fun i => some (z i)) :=
          by funext i; cases i using Fin.cases <;> simp[hz, this]
        simp[this, ← comp_vecCons', Iff.symm Function.funext_iff ] } }

/-- Convert Vector to Nat -/
def vecToNat : {n : ℕ} → (Fin n → ℕ) → ℕ
  | 0,     _ => 0
  | _ + 1, v => Nat.pair (v 0) (vecToNat $ v ∘ Fin.succ)
/-
variable {m : Type u → Type v} [Monad m] {α : Type w} {β : Type u}

def getM : {n : ℕ} → {β : Fin n → Type u} → ((i : Fin n) → m (β i)) → m ((i : Fin n) → β i)
  | 0,     _, _ => pure finZeroElim
  | _ + 1, _, f => Fin.cases <$> f 0 <*> getM (f ·.succ)

lemma getM_pure [LawfulMonad m] {n} {β : Fin n → Type u} (v : (i : Fin n) → β i) :
    getM (fun i => (pure (v i) : m (β i))) = pure v := by
  induction' n with n ih <;> simp[empty_eq, getM]
  · congr; funext x; exact x.elim0
  · simp[vecHead, vecTail, Function.comp, seq_eq_bind, ih]
    exact congr_arg _ (funext $ Fin.cases rfl (fun i => rfl))
-/
end Matrix
