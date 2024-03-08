/-
Copyright (c) 2024 Shogo Saito. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shogo Saito. Adapted for mathlib by Hunter Monroe
-/
import Mathlib.ProofTheory.System

/-!
# Predicate calculus

This file defines the predicate calculus.

-/

class VMonoidStruct {α : Type*} (M : α → α → Type*) where
  id {a} : M a a
  comp {a₁ a₂ a₃} : M a₂ a₃ → M a₁ a₂ → M a₁ a₃

instance {α : Type*} (M : α → α → Type*) [VMonoidStruct M] (a : α) : One (M a a) :=
  ⟨VMonoidStruct.id⟩

instance {α : Type*} (M : α → α → Type*) [VMonoidStruct M] (a₁ a₂ a₃ : α) :
  HSMul (M a₂ a₃) (M a₁ a₂) (M a₁ a₃) := ⟨VMonoidStruct.comp⟩

/- a.k.a. category -/
class VMonoid {α : Type*} (M : α → α → Type*) extends VMonoidStruct M where
  id_left {a b : α} (m : M a b) : (1 : M b b) • m = m
  id_right {a b : α} (m : M a b) : m • (1 : M a a) = m
  comp_assoc {a₁ a₂ a₃ a₄: α} (m₃ : M a₃ a₄) (m₂ : M a₂ a₃) (m₁ : M a₁ a₂) :
    m₃ • (m₂ • m₁) = (m₃ • m₂) • m₁

namespace ProofTheory

namespace Unsorted

class BoundedVariable (T : ℕ → Type*) where
  bvar {n} : Fin n → T n

scoped prefix:max "#" => BoundedVariable.bvar

section Term

variable (T : ℕ → Type*) [BoundedVariable T] (R : outParam (ℕ → ℕ → Type*)) [VMonoid R]

class RewritingT where
  evalT {n₁ n₂} : R n₁ n₂ → T n₁ → T n₂
  evalT_injective' {n₁ n₂} : Function.Injective (evalT : R n₁ n₂ → T n₁ → T n₂)
  evalT_id {n} : ∀ t : T n, evalT 1 t = t
  evalT_comp {n₁ n₂ n₃} (ω₂ : R n₂ n₃) (ω₁ : R n₁ n₂) :
    ∀ t : T n₁, evalT (ω₂ • ω₁) t = evalT ω₂ (evalT ω₁ t)

open RewritingT

infix:70 " ⋙ " => RewritingT.evalT

class RewritingT.Substs [RewritingT T R] where
  substs {k n} (v : Fin k → T n) : R k n
  evalT_substs {k n} (v : Fin k → T n) (x : Fin k) : substs v ⋙ #x = v x
  comp_substs {k n₁ n₂} (ω : R n₁ n₂) (v : Fin k → T n₁) : ω • (substs v) =
    substs (fun i => ω ⋙ (v i))
  bShift {n} : R n (n + 1)
  evalT_bShift {n} (x : Fin n) : bShift ⋙ (#x : T n) = #x.succ

end Term

open RewritingT RewritingT.Substs

section Formula

variable (F : ℕ → Type*) [(n : ℕ) → LogicalConnective (F n)] [UnivQuantifier F] [ExQuantifier F]
variable (T : outParam (ℕ → Type*)) [BoundedVariable T]
variable (R : outParam (ℕ → ℕ → Type*)) [VMonoid R]

class Rewriting where
  eval {n₁ n₂} : R n₁ n₂ → F n₁ →ˡᶜ F n₂
  q {n₁ n₂} : R n₁ n₂ → R (n₁ + 1) (n₂ + 1)
  q_id {n} : q (1 : R n n) = 1
  q_comp {n₁ n₂ n₃} (ω₂ : R n₂ n₃) (ω₁ : R n₁ n₂) : q (ω₂ • ω₁) = (q ω₂) • (q ω₁)
  eval_id {n} : ∀ f : F n, eval 1 f = f
  eval_comp {n₁ n₂ n₃} (ω₂ : R n₂ n₃) (ω₁ : R n₁ n₂) : ∀ f : F n₁, eval (ω₂ • ω₁) f =
    eval ω₂ (eval ω₁ f)
  eval_all {n₁ n₂} (ω : R n₁ n₂) : ∀ f : F (n₁ + 1), eval ω (∀' f) = ∀' eval (q ω) f
  eval_ex {n₁ n₂} (ω : R n₁ n₂) : ∀ f : F (n₁ + 1), eval ω (∃' f) = ∃' eval (q ω) f

open Rewriting

class Rewriting.Substs [RewritingT T R] [RewritingT.Substs T R] extends Rewriting F R where
  q_substs {k n} (v : Fin k → T n) :
    q (substs v) = substs (#0 :> fun i => RewritingT.evalT (bShift T) (v i))

class SyntacticRewriting [RewritingT T R] [RewritingT.Substs T R]
    extends Rewriting F R where
  shift {n} : R n n
  free {n} : R (n + 1) n
  q_shift {n} : q (shift : R n n) = shift
  q_free {n} : q (free : R (n + 1) n) = free
  q_substs {k n} (v : Fin k → T n) :
    q (substs v) = substs (#0 :> fun i => RewritingT.evalT (bShift T) (v i))

end Formula

variable {T : ℕ → Type*} [BoundedVariable T] {R : ℕ → ℕ → Type*}
variable [VMonoid R] [RewritingT T R] [RewritingT.Substs T R]

def op {k n} (t : T k) (v : Fin k → T n) : T n := evalT (substs v) t

structure Operator (α : ℕ → Type*) (k : ℕ) where
   t : α k

class Operator.Zero (T : ℕ → Type*) where
  zero : T 0

end Unsorted

namespace TwoSorted
/-
variable (F : ℕ → ℕ → Type u) [(m n : ℕ) → LogicalConnective (F m n)] [UnivQuantifier₂ F]
  [ExQuantifier₂ F]

class RewritingT (T₁ T₂ : outParam (ℕ → Type v)) (R : outParam (ℕ → ℕ → ℕ → ℕ → Type w)) where
  id {m n} : R m n m n
  comp {m₁ n₁ m₂ n₂ m₃ n₃} : R m₂ n₂ m₃ n₃ → R m₁ n₁ m₂ n₂ → R m₁ n₁ m₃ n₃
  substs {l m k n} (w : Fin l → T₁ m) (v : Fin k → T₂ n) : R l k m n
  q₁ {m₁ n₁ m₂ n₂} : R m₁ n₁ m₂ n₂ → R (m₁ + 1) n₁ (m₂ + 1) n₂
  q₂ {m₁ n₁ m₂ n₂} : R m₁ n₁ m₂ n₂ → R m₁ (n₁ + 1) m₂ (n₂ + 1)
  eval {m₁ n₁ m₂ n₂} : R m₁ n₁ m₂ n₂ → F m₁ n₁ →L F m₂ n₂
  eval_id {m n} : ∀ f : F m n, eval id f = f
  eval_comp {m₁ n₁ m₂ n₂ m₃ n₃} (ω₂ : R m₂ n₂ m₃ n₃) (ω₁ : R m₁ n₁ m₂ n₂) : ∀ f : F m₁ n₁,
    eval (comp ω₂ ω₁) f = eval ω₂ (eval ω₁ f)
  eval_all₁ {n₁ n₂} : ∀ ω : R m₁ n₁ m₂ n₂, ∀ f : F (m₁ + 1) n₁, eval ω (∀¹ f) = ∀¹ eval (q₁ ω) f
  eval_all₂ {n₁ n₂} : ∀ ω : R m₁ n₁ m₂ n₂, ∀ f : F m₁ (n₁ + 1), eval ω (∀² f) = ∀² eval (q₂ ω) f
  eval_ex₁ {n₁ n₂} : ∀ ω : R m₁ n₁ m₂ n₂, ∀ f : F (m₁ + 1) n₁, eval ω (∃¹ f) = ∃¹ eval (q₁ ω) f
  eval_ex₂ {n₁ n₂} : ∀ ω : R m₁ n₁ m₂ n₂, ∀ f : F m₁ (n₁ + 1), eval ω (∃² f) = ∃² eval (q₂ ω) f

-/
end TwoSorted

end ProofTheory
