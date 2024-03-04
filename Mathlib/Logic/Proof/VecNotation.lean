import Mathlib.Data.Fin.VecNotation

namespace Matrix
open Fin
section
universe u v
variable {n : ℕ} {α : Type u} {β : Type v}

infixr:70 " :> " => vecCons

@[simp] lemma vecCons_zero {a : α} {s : Fin n → α} :
    (a :> s) 0 = a := by simp

@[simp] lemma vecCons_succ (i : Fin n) {a : α} {s : Fin n → α} :
    (a :> s) (Fin.succ i) = s i := by simp

@[simp] lemma vecCons_last {C : Type v}  (a : C) (s : Fin (n + 1) → C) :
    (a :> s) (Fin.last (n + 1)) = s (Fin.last n) := vecCons_succ (Fin.last n)

def vecConsLast {n : ℕ} (t : Fin n → α) (h : α) : Fin n.succ → α :=
  Fin.lastCases h t

infixl:70 " <: " => vecConsLast

@[simp] lemma rightConcat_last  {a : α} {s : Fin n → α} : (s <: a) (last n) = a := by simp[vecConsLast]

@[simp] lemma rightConcat_castSucc (i : Fin n)  {a : α} {s : Fin n → α} :
    (s <: a) (Fin.castSucc i) = s i := by simp[vecConsLast]

lemma comp_vecConsLast (f : α → β) (a : α) (s : Fin n → α) : (fun x => f $ (s <: a) x) = f ∘ s <: f a :=
funext (fun i => lastCases (by simp) (by simp) i)

@[simp] lemma vecHead_comp (f : α → β) (v : Fin (n + 1) → α) : vecHead (f ∘ v) = f (vecHead v) :=
  by simp[vecHead]

@[simp] lemma vecTail_comp (f : α → β) (v : Fin (n + 1) → α) : vecTail (f ∘ v) = f ∘ (vecTail v) :=
  by simp[vecTail, Function.comp.assoc]

end

end Matrix
