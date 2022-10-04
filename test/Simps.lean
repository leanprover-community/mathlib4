import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Simps
import Mathlib.Tactic.RunCmd
import Mathlib.Lean.Exception
import Mathlib.Data.Equiv.Basic

-- set_option trace.simps.debug true
set_option trace.simps.verbose true

open Lean Meta Elab Term Command

structure Foo1 : Type where
  one : Nat
  two : Bool
  three : Nat → Bool
  four : 1 = 1
  five : 2 = 1

initialize_simps_projections Foo1 (one → toNat, two → toBool, three → coe as_prefix, -toBool)

run_cmd liftTermElabM <| do
  let  env ← getEnv
  let state := ((simpsStructure.getState env).find? `Foo1).get!
  -- IO.println <| format state
  guard <| state.1 == []
  guard <| state.2.map (·.1) == [`toNat, `toBool, `coe, `four, `five]
  liftMetaM <| guard (← isDefEq (state.2.head!.2) (← elabTerm (← `(Foo1.one)) none))
  liftMetaM <| guard (← isDefEq (state.2.tail.head!.2) (← elabTerm (← `(Foo1.two)) none))
  guard <| state.2.map (·.3) == (List.range 5).map ([·])
  guard <| state.2.map (·.4) == [true, false, true, false, false]
  guard <| state.2.map (·.5) == [false, false, true, false, false]
  pure ()

structure Foo2 (α : Type _) : Type _ where
  elim : α × α

def Foo2.simps.elim (α : Type _) : Foo2 α → α × α := fun x => (x.elim.1, x.elim.2)

initialize_simps_projections Foo2

-- run_cmd liftTermElabM <| do
--   let  env ← getEnv
--   let state := ((simpsStructure.getState env).find? `Foo2).get!
--   IO.println <| format state

structure Left (α : Type _) extends Foo2 α where
  moreData1 : Nat
  moreData2 : Nat

initialize_simps_projections Left

structure Right (α : Type u) (β : Type v) extends Foo2 α where
  otherData : β

initialize_simps_projections Right (toFoo2_elim → newProjection)

run_cmd liftTermElabM <| do
  let  env ← getEnv
  let state := ((simpsStructure.getState env).find? `Right).get!
  -- IO.println <| format state
  guard <| state.1 == [`u, `v]
  guard <| state.2.map (·.1) == [`toFoo2, `otherData, `newProjection]
  guard <| state.2.map (·.3) == [[0],[1],[0,0]]
  guard <| state.2.map (·.4) == [true, true, true]
  guard <| state.2.map (·.5) == [false, false, false]

structure Top (α β : Type _) extends Left α, Right α β

initialize_simps_projections Top

structure NewTop (α β : Type _) extends Right α β, Left α

def NewTop.simps.newElim {α β : Type _} (x : NewTop α β) : α × α := x.elim

-- initialize_simps_projections? NewTop (toRight_toFoo2_elim → newElim)


run_cmd liftCoreM <| successIfFail <| simpsGetRawProjections `DoesntExist

class Something (α : Type _) where
  op : α → α → α → α

instance {α : Type _} [Something α] : Add α :=
⟨λ x y => Something.op x y y⟩


initialize_simps_projections? Something


-- other tests (to delete)


-- some testing

lemma Prod.eq {α β : Type _} {x y : α × β} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y :=
match x, y, h₁, h₂ with
| _x, (_, _), rfl, rfl => rfl -- using eta for Structures!

instance AddSemigroup.prod {α β : Type _} [AddSemigroup α] [AddSemigroup β] : AddSemigroup (α × β) :=
{ add := λ x y => ⟨x.1 + y.1, x.2 + y.2⟩
  add_assoc := λ _ _ _ => congrArg₂ Prod.mk (add_assoc ..) (add_assoc ..) } -- using eta for Structures!

-- #print AddSemigroup
-- #print AddCommSemigroup
-- #print AddMonoid
-- #print AddCommMonoid
-- #print AddMonoidWithOne

lemma prod_mul {α β : Type _} [AddSemigroup α] [AddSemigroup β] (x y : α × β) :
  x + y = ⟨x.1 + y.1, x.2 + y.2⟩ := rfl

-- attribute [notation_class] Add HAdd
-- #print HAdd

initialize_simps_projections AddSemigroup (toAdd_add → add, -toAdd)

class MyClass (R : Type u) extends AddMonoidWithOne R, Monoid R

#print MyClass

-- #eval 1+1
-- #check Equiv
-- #check Equiv.inv_fun_as_coe
-- #check @Equiv.inv_fun_as_coe
-- #check Equiv

-- #print Lean.Expr
-- #print Prod.snd
-- #print Coe
-- structure Foo : Type _ :=
--   x : Nat
--   p : x = 3

-- example (z : Foo) (h : z.x = 3) : ⟨z.x, h⟩ = z :=
-- by simp

-- instance : Add Foo :=
-- ⟨λ z₁ z₂ => ⟨z₁.x + z₂.x - 3, by simp [Foo.p]⟩⟩

-- def foo : Foo → Type _ :=
-- λ z => { l : List Nat // l.head? = some z.x }

-- instance {z₁ z₂ : Foo} : HAdd (foo z₁) (foo z₂) (foo <| z₁ + z₂) :=
-- ⟨λ w₁ w₂ => ⟨w₁.1 ++ w₂.1, sorry⟩⟩

-- example {W : (Nat × Nat → Nat × Nat) → Type} {w : ∀ f, W f} {f : Nat × Nat → Nat × Nat} :
--  w (λ x : Nat × Nat => ((f (x.1, x.2)).1, (f x).2)) = w f :=
-- _

-- example {α β : Type _} (e : α × β) : (e.1, e.2) = e :=
-- rfl

-- example {α β : Type _} (e : α ≃ β) : Equiv.toFun e = sorry :=
-- _
