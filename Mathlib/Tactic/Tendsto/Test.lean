import Mathlib.Data.Real.Basic
-- import Mathlib.Data.ENat.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Tactic

import Mathlib.Data.Seq.Computation


-- #eval Fib 30

unsafe def Fib_impl (n : ℕ) : ℕ := Id.run do
  let mut prev := 1
  let mut prev_prev := 1
  for _ in [2:n+1] do
    let new := prev_prev + prev
    prev_prev := prev
    prev := new
  return prev

@[implemented_by Fib_impl]
def Fib : ℕ → ℕ
| 0 => 1
| 1 => 1
| m + 2 => Fib m + Fib (m + 1)

theorem kek (n : ℕ) : Fib n + Fib (n + 1) = Fib (n + 2) := by
  conv => rhs; unfold Fib


def Fib' (n : ℕ) : Thunk ℕ := match n with
| 0 => ⟨fun _ ↦ 1⟩
| 1 => ⟨fun _ ↦ 1⟩
| m + 2 => ⟨fun _ ↦ (Fib' m).get + (Fib' (m + 1)).get⟩

-- #eval (Fib' 50).get


#check Sum
#check Sigma.mk

universe u in
def MyStream (α : Type u) : Type u :=
  (Σ (i : ℕ), (Fin i → α)) ⊕ (ℕ → α)

def MyStream.ofList {α : Type} (li : List α) : MyStream α :=
  Sum.inl ⟨li.length, fun i ↦ li[i]⟩



inductive PreMS where
| const : ℝ → PreMS
| nil : PreMS
| cons (deg : ℝ) (coef : PreMS) (tl : Thunk PreMS) : PreMS

def Stream'' (α : Type) := {x : Stream' (Option α) // ∀ n, (x n).isNone → (x (n + 1)).isNone}

universe u in
def Kek (α : Sort u) := ℕ → α


mutual
  inductive PreMS' where
  | const : ℝ → PreMS'
  | list (li : ℕ → Option (ℝ × PreMS'WF)) : PreMS'

  inductive PreMS'WF : Type where
  | mk (ms : PreMS') (h_wf : PreMS'_wf ms) : PreMS'WF

  inductive PreMS'_wf : PreMS' → Type where
  | const (c : ℝ) : PreMS'_wf (PreMS.const c)
  | list (li : ℕ → Option (ℝ × PreMS'WF)) (h_li : ∀ n, li n = none → li (n + 1) = none) : PreMS'_wf (PreMS.list li)

end

#check PreMS'

universe u

-- axiom MyType : Type 1

-- #check MyType
-- #check (MyType × MyType)

inductive MyType where
| constr : (ℕ → MyType) → MyType


inductive MyType' where
| constr : Kek MyType' → MyType'

#check Stream'
