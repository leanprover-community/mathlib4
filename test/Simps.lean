import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Simps
import Mathlib.Tactic.RunCmd
import Mathlib.Lean.Exception
import Mathlib.Data.Equiv.Basic
-- import Mathlib.Util.Simp -- temp


-- set_option trace.simps.debug true
-- set_option trace.simps.verbose true

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
  guard <| state.1 == []
  guard <| state.2.map (·.1) == #[`toNat, `toBool, `coe, `four, `five]
  liftMetaM <| guard (← isDefEq (state.2[0]!.2) (← elabTerm (← `(Foo1.one)) none))
  liftMetaM <| guard (← isDefEq (state.2[1]!.2) (← elabTerm (← `(Foo1.two)) none))
  guard <| state.2.map (·.3) == (Array.range 5).map ([·])
  guard <| state.2.map (·.4) == #[true, false, true, false, false]
  guard <| state.2.map (·.5) == #[false, false, true, false, false]
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
  guard <| state.2.map (·.1) == #[`toFoo2, `otherData, `newProjection]
  guard <| state.2.map (·.3) == #[[0],[1],[0,0]]
  guard <| state.2.map (·.4) == #[true, true, true]
  guard <| state.2.map (·.5) == #[false, false, false]

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


initialize_simps_projections Something

/- start Lean 3 test suite -/


universe v u w
-- set_option trace.simps.verbose true
-- set_option trace.simps.debug true
-- set_option trace.app_builder true

structure Equiv' (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)
(left_inv  : invFun.LeftInverse toFun)
(right_inv : invFun.RightInverse toFun)

infix:25 (priority := default+1) " ≃ " => Equiv'

-- macro "simps?" rest:simpsArgsRest : attr => `(attr| simps ? $rest)
-- local infix (name := Equiv') ` ≃ `:25 := Equiv'

/- Since `prod` and `PProd` are a special case for `@[simps]`, we define a new structure to test
  the basic functionality.-/
structure MyProd (α β : Type _) := (fst : α) (snd : β)

def MyProd.map {α α' β β'} (f : α → α') (g : β → β') (x : MyProd α β) : MyProd α' β' :=
⟨f x.1, g x.2⟩

namespace foo
@[simps] protected def rfl {α} : α ≃ α :=
⟨id, λ x => x, λ _ => rfl, λ _ => rfl⟩

/- simps adds declarations -/
run_cmd liftTermElabM <| do
  let env ← getEnv
  guard <| env.find? `foo.rfl_toFun |>.isSome
  guard <| env.find? `foo.rfl_invFun |>.isSome
  guard <| env.find? `foo.rfl_left_inv |>.isNone
  guard <| env.find? `foo.rfl_right_inv |>.isNone

example (n : ℕ) : foo.rfl.toFun n = n := by rw [foo.rfl_toFun, id]
example (n : ℕ) : foo.rfl.invFun n = n := by rw [foo.rfl_invFun]

/- the declarations are `simp` lemmas -/
@[simps] def foo : ℕ × ℤ := (1, 2)

-- note: in Lean 4 the first test succeeds without `@[simps]`, however, the remaining tests don't
example : foo.1 = 1 := by simp
example {a : ℕ} {h : 1 = a} : foo.1 = a := by rw [foo_fst, h]
example {a : ℕ} {h : 1 = a} : foo.1 = a := by simp <;> rw [h]
example {a : ℤ} {h : 2 = a} : foo.2 = a := by simp <;> rw [h]
example {a : ℕ} {h : 1 = a} : foo.1 = a := by dsimp <;> rw [h] -- check that dsimp also unfolds
example {a : ℤ} {h : 2 = a} : foo.2 = a := by dsimp <;> rw [h]
example {α} (x y : α) (h : x = y) : foo.rfl.toFun x = y := by simp <;> rw [h]
example {α} (x y : α) (h : x = y) : foo.rfl.invFun x = y := by simp <;> rw [h]
-- example {α} (x y : α) (h : x = y) : foo.rfl.toFun = @id α := by { successIfFail {simp}, rfl }

/- check some failures -/
def bar1 : ℕ := 1 -- type is not a structure
noncomputable def bar2 {α} : α ≃ α :=
Classical.choice ⟨foo.rfl⟩

run_cmd liftCoreM <| do
  -- _ ← simpsTac `foo.bar1
  -- successIfFailWithMsg (simpsTac `foo.bar1)
  --   "Invalid `simps` attribute. Target Nat is not a structure"
  -- _ ← simpsTac `foo.bar2
  -- successIfFailWithMsg (simpsTac `foo.bar2)
  --   "Invalid `simps` attribute. The body is not a constructor application:
  -- Classical.choice (_ : Nonempty (α ≃ α))"
  pure ()

/- test that if a non-constructor is given as definition, then
  `{rhsMd := semireducible, simpRhs := true}` is applied automatically. -/
@[simps] def rfl2 {α} : α ≃ α := foo.rfl

example {α} (x : α) : rfl2.toFun x = x ∧ rfl2.invFun x = x := by
  dsimp
  guard_target == x = x ∧ x = x
  exact ⟨rfl, rfl⟩

example {α} (x : α) : rfl2.toFun x = x ∧ rfl2.invFun x = x := by
  dsimp only [rfl2_toFun, rfl2_invFun]
  guard_target == x = x ∧ x = x
  exact ⟨rfl, rfl⟩

/- test `fullyApplied` option -/

@[simps (config := {fullyApplied := false})]
def rfl3 {α} : α ≃ α := ⟨id, λ x => x, λ _ => rfl, λ _ => rfl⟩

end foo

/- we reduce the type when applying [simps] -/
def my_equiv := Equiv'
@[simps] def baz : my_equiv ℕ ℕ := ⟨id, λ x => x, λ _ => rfl, λ _ => rfl⟩

/- todo: test that name clashes gives an error -/

/- check projections for nested structures -/

namespace CountNested
@[simps (config := {attrs := [`simp, `norm]})]
def nested1 : MyProd ℕ $ MyProd ℤ ℕ :=
⟨2, -1, 1⟩

@[simps (config := {attrs := []})]
def nested2 : ℕ × MyProd ℕ ℕ :=
⟨2, MyProd.map Nat.succ Nat.pred ⟨1, 2⟩⟩

end CountNested

run_cmd liftTermElabM <| do
  let env ← getEnv
  guard <| env.find? `CountNested.nested1_fst |>.isSome
  guard <| env.find? `CountNested.nested1_snd_fst |>.isSome
  guard <| env.find? `CountNested.nested1_snd_snd |>.isSome
  guard <| env.find? `CountNested.nested2_fst |>.isSome
  guard <| env.find? `CountNested.nested2_snd |>.isSome
  guard <| hasSimpAttribute env `CountNested.nested1_fst -- simp attribute is global
  guard <| not <| hasSimpAttribute env `CountNested.nested2_fst -- lemmas_only doesn't add simp lemma
  -- todo: maybe test that there are no other lemmas generated
  -- guard $ 7 = env.fold 0
  --   (λ d n => n + if d.to_name.components.init.ilast = `CountNested then 1 else 0)

-- testing with arguments
@[simps] def bar {_ : Type _} (n m : ℕ) : ℕ × ℤ :=
⟨n - m, n + m⟩

structure EquivPlusData (α β) extends α ≃ β where
  P : (α → β) → Prop
  data : P toFun

structure ComplicatedEquivPlusData (α) extends α ⊕ α ≃ α ⊕ α where
  P : (α ⊕ α → α ⊕ α) → Prop
  data : P toFun
  extra : Bool → MyProd ℕ ℕ

@[simps]
def rflWithData {α} : EquivPlusData α α :=
{ foo.rfl with
  P := λ f => f = id
  data := rfl }

@[simps]
def rflWithData' {α} : EquivPlusData α α :=
{ P := λ f => f = id
  data := rfl
  toEquiv' := foo.rfl }

/- test whether eta expansions are reduced correctly -/
@[simps]
def test {α} : ComplicatedEquivPlusData α :=
{ foo.rfl with
  P := λ f => f = id
  data := rfl
  extra := λ _ => ⟨(⟨3, 5⟩ : MyProd _ _).1, (⟨3, 5⟩ : MyProd _ _).2⟩ }

/- test whether this is indeed rejected as a valid eta expansion -/
@[simps]
def test_sneaky {α} : ComplicatedEquivPlusData α :=
{ foo.rfl with
  P := λ f => f = id
  data := rfl
  extra := λ _ => ⟨(3,5).1,(3,5).2⟩ }

run_cmd liftTermElabM <| do
  let env ← getEnv
  guard <| env.find? `rflWithData_toEquiv' |>.isSome
  guard <| env.find? `rflWithData'_toEquiv' |>.isSome
  guard <| env.find? `test_extra |>.isSome
  guard <| env.find? `test_sneaky_extra_fst |>.isSome
  guard <| env.find? `rflWithData_to_equiv_toFun |>.isNone
  guard <| env.find? `rflWithData'_to_equiv_toFun |>.isNone
  guard <| env.find? `test_extra_fst |>.isNone
  guard <| env.find? `test_sneaky_extra |>.isNone

structure PartiallyAppliedStr :=
(data : ℕ → MyProd ℕ ℕ)

/- if we have a partially applied constructor, we treat it as if it were eta-expanded -/
@[simps]
def partially_applied_term : PartiallyAppliedStr := ⟨MyProd.mk 3⟩

@[simps]
def another_term : PartiallyAppliedStr := ⟨λ n => ⟨n + 1, n + 2⟩⟩

run_cmd liftTermElabM <| do
  let env ← getEnv
  guard <| env.find? `partially_applied_term_data_fst |>.isSome
  guard <| env.find? `partially_applied_term_data_snd |>.isSome

structure VeryPartiallyAppliedStr :=
(data : ∀β, ℕ → β → MyProd ℕ β)

/- if we have a partially applied constructor, we treat it as if it were eta-expanded.
  (this is not very useful, and we could remove this behavior if convenient) -/
@[simps]
def very_partially_applied_term : VeryPartiallyAppliedStr := ⟨@MyProd.mk ℕ⟩

run_cmd liftTermElabM <| do
  let env ← getEnv
  guard <| env.find? `very_partially_applied_term_data_fst |>.isSome
  guard <| env.find? `very_partially_applied_term_data_snd |>.isSome

@[simps] def let1 : ℕ × ℤ :=
let n := 3; ⟨n + 4, 5⟩

@[simps] def let2 : ℕ × ℤ :=
let n := 3; let m := 4; let k := 5; ⟨n + m, k⟩

@[simps] def let3 : ℕ → ℕ × ℤ :=
λ n => let m := 4; let k := 5; ⟨n + m, k⟩

@[simps] def let4 : ℕ → ℕ × ℤ :=
let m := 4; let k := 5; λ n => ⟨n + m, k⟩

run_cmd liftTermElabM <| do
  let env ← getEnv
  guard <| env.find? `let1_fst |>.isSome
  guard <| env.find? `let2_fst |>.isSome
  guard <| env.find? `let3_fst |>.isSome
  guard <| env.find? `let4_fst |>.isSome
  guard <| env.find? `let1_snd |>.isSome
  guard <| env.find? `let2_snd |>.isSome
  guard <| env.find? `let3_snd |>.isSome
  guard <| env.find? `let4_snd |>.isSome


namespace specify
@[simps fst] def specify1 : ℕ × ℕ × ℕ := (1, 2, 3)
@[simps snd] def specify2 : ℕ × ℕ × ℕ := (1, 2, 3)
@[simps snd_fst] def specify3 : ℕ × ℕ × ℕ := (1, 2, 3)
@[simps snd snd_snd snd_snd] def specify4 : ℕ × ℕ × ℕ := (1, 2, 3) -- last argument is ignored
@[simps] noncomputable def specify5 : ℕ × ℕ × ℕ := (1, Classical.choice ⟨(2, 3)⟩)
end specify

run_cmd liftTermElabM <| do
  let env ← getEnv
  guard <| env.find? `specify.specify1_fst |>.isSome
  guard <| env.find? `specify.specify2_snd |>.isSome
  guard <| env.find? `specify.specify3_snd_fst  |>.isSome
  guard <| env.find? `specify.specify4_snd_snd |>.isSome
  guard <| env.find? `specify.specify4_snd |>.isSome
  guard <| env.find? `specify.specify5_fst |>.isSome
  guard <| env.find? `specify.specify5_snd |>.isSome
  -- todo: there are no other lemmas generated
  -- guard $ 12 = env.fold 0
  --   (λ d n => n + if d.to_name.components.init.ilast = `specify then 1 else 0)
  _ ← successIfFail (simpsTac .missing `specify.specify1 {} ["fst_fst"])
--     "Invalid simp lemma specify.specify1_fst_fst.
-- Projection fst doesn't exist, because target is not a structure."
  _ ← successIfFail (simpsTac .missing `specify.specify1 {} ["foo_fst"])
--     "Invalid simp lemma specify.specify1_foo_fst. Structure prod does not have projection foo.
-- The known projections are:
--   [fst, snd]
-- You can also see this information by running
--   `initialize_simps_projections? prod`.
-- Note: these projection names might not correspond to the projection names of the structure."
  _ ← successIfFail (simpsTac .missing `specify.specify1 {} ["snd_bar"])
--     "Invalid simp lemma specify.specify1_snd_bar. Structure prod does not have projection bar.
-- The known projections are:
--   [fst, snd]
-- You can also see this information by running
--   `initialize_simps_projections? prod`.
-- Note: these projection names might not correspond to the projection names of the structure."
  _ ← successIfFail (simpsTac .missing `specify.specify5 {} ["snd_snd"])
--     "Invalid simp lemma specify.specify5_snd_snd.
-- The given definition is not a constructor application:
--   Classical.choice specify.specify5._proof_1"


/- We also eta-reduce if we explicitly specify the projection. -/
attribute [simps extra] test -- this should raise an error!
run_cmd liftTermElabM <| do
  let env ← getEnv
  let d1 := env.find? `test_extra |>.get!
  let d2 := env.find? `test_extra_2 |>.get!
  guard <| d1.type == d2.type
  pure ()

/- check simpRhs option -/
@[simps (config := {simpRhs := true})] def Equiv'.trans {α β γ} (f : α ≃ β) (g : β ≃ γ) : α ≃ γ :=
⟨ g.toFun ∘ f.toFun,
  f.invFun ∘ g.invFun,
  (by intro x <;> simp [Equiv'.left_inv _ _]),
  (by intro x <;> simp [Equiv'.right_inv _ _])⟩


example {α β γ : Type} (f : α ≃ β) (g : β ≃ γ) (x : α) :
  (f.trans g).toFun x = (f.trans g).toFun x := by
  dsimp only [Equiv'.trans_toFun]
  guard_target == g.toFun (f.toFun x) = g.toFun (f.toFun x)
  rfl

-- local -- attributes cannot be local?
attribute [simp] Nat.zero_add Nat.one_mul Nat.mul_one
@[simps (config := {simpRhs := true})] def myNatEquiv : ℕ ≃ ℕ :=
⟨λ n => 0 + n, λ n => 1 * n * 1, by intro n <;> simp, by intro n <;> simp⟩

example (n : ℕ) : myNatEquiv.toFun (myNatEquiv.toFun $ myNatEquiv.invFun n) = n :=
by { /-successIfFail { rfl },-/ simp only [myNatEquiv_toFun, myNatEquiv_invFun] }

@[simps (config := {simpRhs := true})] def succeed_without_simplification_possible : ℕ ≃ ℕ :=
⟨λ n => n, λ n => n, by intro n <;> rfl, by intro n <;> rfl⟩


/- test that we don't recursively take projections of `prod` and `PProd` -/
@[simps] def pprodEquivProd2 : PProd ℕ ℕ ≃ ℕ × ℕ :=
{ toFun := λ x => ⟨x.1, x.2⟩
  invFun := λ x => ⟨x.1, x.2⟩
  left_inv := λ ⟨_, _⟩ => rfl
  right_inv := λ ⟨_, _⟩ => rfl }

run_cmd liftTermElabM <| do
  let env ← getEnv
  guard <| env.find? `pprodEquivProd2_toFun |>.isSome
  guard <| env.find? `pprodEquivProd2_invFun |>.isSome

attribute [simps toFun_fst invFun_snd] pprodEquivProd2

run_cmd liftTermElabM <| do
  let env ← getEnv
  guard <| env.find? `pprodEquivProd2_toFun_fst |>.isSome
  guard <| env.find? `pprodEquivProd2_invFun_snd |>.isSome

-- we can disable this behavior with the option `notRecursive`.
@[simps (config := {notRecursive := []})] def pprodEquivProd22 : PProd ℕ ℕ ≃ ℕ × ℕ :=
pprodEquivProd2

run_cmd liftTermElabM <| do
  let env ← getEnv
  guard <| env.find? `pprodEquivProd22_toFun_fst |>.isSome
  guard <| env.find? `pprodEquivProd22_toFun_snd |>.isSome
  guard <| env.find? `pprodEquivProd22_invFun_fst |>.isSome
  guard <| env.find? `pprodEquivProd22_invFun_snd |>.isSome

/- Tests with universe levels -/
class has_hom (obj : Type u) : Type (max u (v+1)) :=
(hom : obj → obj → Type v)

infixr:10 " ⟶ " => has_hom.hom -- type as \h

class CategoryStruct (obj : Type u) extends has_hom.{v} obj : Type (max u (v+1)) :=
(id       : ∀ X : obj, hom X X)
(comp     : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z))

notation "𝟙" => CategoryStruct.id -- type as \b1
infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

@[simps] instance types : CategoryStruct (Type u) :=
{ hom     := λ a b => (a → b)
  id      := λ _ => id
  comp    := λ f g => g ∘ f }

example (X : Type u) : (X ⟶ X) = (X → X) := by simp
example (X : Type u) : 𝟙 X = (λ x => x) := by { ext <;> simp }
example (X Y Z : Type u) (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = g ∘ f := by { ext <;> simp }

namespace coercing

structure FooStr :=
 (c : Type)
 (x : c)

instance : CoeSort FooStr Type := ⟨FooStr.c⟩

@[simps] def foo : FooStr := ⟨ℕ, 3⟩
@[simps] def foo2 : FooStr := ⟨ℕ, 34⟩

example : foo = ℕ := by simp only [foo_c]
example : foo.x = (3 : ℕ) := by simp only [foo_x]

structure VooStr (n : ℕ) :=
 (c : Type)
 (x : c)

instance (n : ℕ) : CoeSort (VooStr n) Type := ⟨VooStr.c⟩

@[simps] def voo : VooStr 7 := ⟨ℕ, 3⟩
@[simps] def voo2 : VooStr 4 := ⟨ℕ, 34⟩

example : voo = ℕ := by simp only [voo_c]
example : voo.x = (3 : ℕ) := by simp only [voo_x]

structure Equiv2 (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)
(left_inv  : invFun.LeftInverse toFun)
(right_inv : invFun.RightInverse toFun)

instance {α β} : CoeFun (Equiv2 α β) (λ _ => α → β) := ⟨Equiv2.toFun⟩

@[simps] protected def rfl2 {α} : Equiv2 α α :=
⟨λ x => x, λ x => x, λ _ => rfl, λ _ => rfl⟩

example {α} (x : α) : coercing.rfl2 x = x := by rw [coercing.rfl2_toFun]
example {α} (x : α) : coercing.rfl2 x = x := by simp
example {α} (x : α) : coercing.rfl2.invFun x = x := by simp

@[simps] protected def Equiv2.symm {α β} (f : Equiv2 α β) : Equiv2 β α :=
⟨f.invFun, f, f.right_inv, f.left_inv⟩

@[simps] protected def Equiv2.symm2 {α β} (f : Equiv2 α β) : Equiv2 β α :=
⟨f.invFun, f.toFun, f.right_inv, f.left_inv⟩

@[simps (config := {fullyApplied := false})] protected def Equiv2.symm3 {α β} (f : Equiv2 α β) : Equiv2 β α :=
⟨f.invFun, f, f.right_inv, f.left_inv⟩

example {α β} (f : Equiv2 α β) (y : β) : f.symm y = f.invFun y := by simp
example {α β} (f : Equiv2 α β) (x : α) : f.symm.invFun x = f x := by simp

example {α β} (f : Equiv2 α β) : f.symm.invFun = f := by { /-successIfFail {simp} <;>-/ rfl }
example {α β} (f : Equiv2 α β) : f.symm3.invFun = f := by simp

class SemiGroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

@[simps] instance {α β} [SemiGroup α] [SemiGroup β] : SemiGroup (α × β) :=
{ mul := λ x y => (x.1 * y.1, x.2 * y.2)
  mul_assoc := by { intros <;> simp only [SemiGroup.mul_assoc] <;> rfl } }

example {α β} [SemiGroup α] [SemiGroup β] (x y : α × β) : x * y = (x.1 * y.1, x.2 * y.2) := by simp
example {α β} [SemiGroup α] [SemiGroup β] (x y : α × β) : (x * y).1 = x.1 * y.1 := by simp

structure BSemigroup :=
  (G : Type _)
  (op : G → G → G)
  -- (infix:60 " * " => op) -- this seems to be removed
  (op_assoc : ∀ (x y z : G), op (op x y) z = op x (op y z))

namespace BSemigroup

instance : CoeSort BSemigroup (Type _) := ⟨BSemigroup.G⟩
-- We could try to generate lemmas with this `Mul` instance, but it is unused in mathlib.
-- Therefore, this is ignored.
instance (G : BSemigroup) : Mul G := ⟨G.op⟩

@[simps] def prod_BSemigroup (G H : BSemigroup) : BSemigroup :=
{ G := G × H
  op := λ x y => (x.1 * y.1, x.2 * y.2)
  op_assoc := by intros <;> dsimp [BSemigroup.Mul] <;> simp [BSemigroup.op_assoc]}


end BSemigroup

class ExtendingStuff (G : Type u) extends Mul G, Zero G, Neg G, Subset G :=
(new_axiom : ∀ x : G, x * - 0 ⊆ - x)

@[simps] def bar : ExtendingStuff ℕ :=
{ mul := (·*·)
  zero := 0
  neg := Nat.succ
  subset := λ _ _ => True
  new_axiom := λ _ => trivial }

section
local attribute [instance] bar
example (x : ℕ) : x * - 0 ⊆ - x := by simp
end

class new_ExtendingStuff (G : Type u) extends Mul G, Zero G, Neg G, Subset G :=
(new_axiom : ∀ x : G, x * - 0 ⊆ - x)

@[simps] def new_bar : new_ExtendingStuff ℕ :=
{ mul := (·*·)
  zero := 0
  neg := Nat.succ
  subset := λ _ _ => True
  new_axiom := λ _ => trivial }

section
local attribute [instance] new_bar
example (x : ℕ) : x * - 0 ⊆ - x := by simp
end


end coercing

namespace ManualCoercion

structure Equiv (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)

local infix:25 (priority := high) " ≃ " => ManualCoercion.Equiv

variable {α β γ : Sort _}

instance : CoeFun (α ≃ β) (λ _ => α → β) := ⟨Equiv.toFun⟩

def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
def Equiv.simps.invFun (e : α ≃ β) : β → α := e.symm

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[simps (config := {simpRhs := true})]
protected def Equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : γ) : (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
by simp only [Equiv.trans_invFun]

end ManualCoercion

namespace FaultyManualCoercion

structure Equiv (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)

local infix:25 (priority := high) " ≃ " => FaultyManualCoercion.Equiv

variable {α β γ : Sort _}

/-- See Note [custom simps projection] -/
noncomputable def Equiv.simps.invFun (e : α ≃ β) : β → α := Classical.choice ⟨e.invFun⟩

run_cmd liftTermElabM <| do
  successIfFail (simpsGetRawProjections `FaultyManualCoercion.Equiv)
-- "Invalid custom projection:
--   λ {α : Sort u_1} {β : Sort u_2} (e : α ≃ β), Classical.choice _
-- Expression is not definitionally equal to
--   λ (α : Sort u_1) (β : Sort u_2) (x : α ≃ β), x.invFun"

end FaultyManualCoercion

namespace ManualInitialize
/- defining a manual coercion. -/
variable {α β γ : Sort _}

structure Equiv (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)

local infix:25 (priority := high) " ≃ " => ManualInitialize.Equiv

instance : CoeFun (α ≃ β) (λ _ => α → β) := ⟨Equiv.toFun⟩

def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
-- test: intentionally using different unvierse levels for Equiv.symm than for Equiv
def Equiv.simps.invFun (e : α ≃ β) : β → α := e.symm

initialize_simps_projections Equiv

-- run_cmd has_attribute `_simps_str `ManualInitialize.Equiv

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[simps (config := {simpRhs := true})] protected def Equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

end ManualInitialize

namespace FaultyUniverses

variable {α β γ : Sort _}

structure Equiv (α : Sort u) (β : Sort v) :=
(toFun    : α → β)
(invFun   : β → α)

local infix:25 (priority := high) " ≃ " => FaultyUniverses.Equiv

instance : CoeFun (α ≃ β) (λ _ => α → β) := ⟨Equiv.toFun⟩

def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
-- test: intentionally using different names for the universe variable for Equiv.symm than for
-- Equiv
def Equiv.simps.invFun {α : Type u} {β : Type v} (e : α ≃ β) : β → α := e.symm

run_cmd liftTermElabM <| do
  successIfFail (simpsGetRawProjections `FaultyUniverses.Equiv)
-- "Invalid custom projection:
--   λ {α : Type u} {β : Type v} (e : α ≃ β), ⇑(e.symm)
-- Expression has different type than FaultyUniverses.Equiv.invFun. Given type:
--   ∀ {α : Type u} {β : Type v} (e : α ≃ β), (λ (_x : β ≃ α), β → α) e.symm
-- Expected type:
--   ∀ (α : Sort u) (β : Sort v), α ≃ β → β → α"

end FaultyUniverses

namespace ManualUniverses

variable {α β γ : Sort _}

structure Equiv (α : Sort u) (β : Sort v) :=
(toFun    : α → β)
(invFun   : β → α)

local infix:25 (priority := high) " ≃ " => ManualUniverses.Equiv

instance : CoeFun (α ≃ β) (λ _ => α → β) := ⟨Equiv.toFun⟩

def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
-- test: intentionally using different unvierse levels for Equiv.symm than for Equiv
def Equiv.simps.invFun {α : Sort w} {β : Sort u} (e : α ≃ β) : β → α := e.symm

-- check whether we can generate custom projections even if the universe names don't match
initialize_simps_projections Equiv

end ManualUniverses

namespace ManualProjectionNames

structure Equiv (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)

local infix:25 (priority := high) " ≃ " => ManualProjectionNames.Equiv

variable {α β γ : Sort _}

instance : CoeFun (α ≃ β) (λ _ => α → β) := ⟨Equiv.toFun⟩

def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
def Equiv.simps.symm_apply (e : α ≃ β) : β → α := e.symm

initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)

run_cmd liftTermElabM <| do
  let data ← simpsGetRawProjections `ManualProjectionNames.Equiv
  guard <| data.2.map (·.name) == #[`apply, `symm_apply]

@[simps (config := {simpRhs := true})]
protected def Equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : α) : (e₁.trans e₂) x = e₂ (e₁ x) :=
by simp only [Equiv.trans_apply]

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : γ) : (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
by simp only [Equiv.trans_symm_apply]

-- the new projection names are parsed correctly (the old projection names won't work anymore)
@[simps apply symm_apply] protected def Equiv.trans2 (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩


end ManualProjectionNames

namespace PrefixProjectionNames

structure Equiv (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)

local infix:25 (priority := high) " ≃ " => PrefixProjectionNames.Equiv

variable {α β γ : Sort _}

instance : CoeFun (α ≃ β) (λ _ => α → β) := ⟨Equiv.toFun⟩

def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
def Equiv.simps.symm_apply (e : α ≃ β) : β → α := e.symm
initialize_simps_projections Equiv (toFun → coe as_prefix, invFun → symm_apply)

run_cmd liftTermElabM <| do
  let env ← getEnv
  data ← simpsGetRawProjections e `PrefixProjectionNames.Equiv
  guard $ data.2.map projection_data.name = [`coe, `symm_apply]
  guard $ data.2.map projection_data.is_prefix = [tt, false]

@[simps (config := {simpRhs := true})] protected def Equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : α) : (e₁.trans e₂) x = e₂ (e₁ x) :=
by simp only [Equiv.coe_trans]

-- the new projection names are parsed correctly
@[simps coe symm_apply] protected def Equiv.trans2 (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

-- it interacts somewhat well with multiple projections (though the generated name is not great)
@[simps snd_coe_fst] def foo {α β γ δ : Type _} (x : α) (e₁ : α ≃ β) (e₂ : γ ≃ δ) :
  α × (α × γ ≃ β × δ) :=
⟨x, prod.map e₁ e₂, prod.map e₁.symm e₂.symm⟩

example {α β γ δ : Type _} (x : α) (e₁ : α ≃ β) (e₂ : γ ≃ δ) (z : α × γ) :
  ((foo x e₁ e₂).2 z).1 = e₁ z.1 :=
by simp only [coe_foo_snd_fst]

end PrefixProjectionNames


-- test transparency setting
structure SetPlus (α : Type) :=
(s : Set α)
(x : α)
(h : x ∈ s)

@[simps] def Nat.SetPlus : SetPlus ℕ := ⟨Set.univ, 1, trivial⟩

example : Nat.SetPlus.s = Set.univ := by
  dsimp only [Nat.SetPlus_s]
  guard_target @Set.univ ℕ = Set.univ
  rfl

@[simps (config := {typeMd := semireducible})]
def Nat.SetPlus2 : SetPlus ℕ := ⟨Set.univ, 1, trivial⟩

example : Nat.SetPlus2.s = Set.univ :=
begin
  successIfFail { dsimp only [Nat.SetPlus2_s] }, rfl
end

@[simps (config := {rhsMd := semireducible})]
def Nat.SetPlus3 : SetPlus ℕ := Nat.SetPlus

example : Nat.SetPlus3.s = Set.univ :=
begin
  dsimp only [Nat.SetPlus3_s]
  guard_target @Set.univ ℕ = Set.univ
  rfl
end

namespace NestedNonFullyApplied

structure Equiv (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)

local infix:25 (priority := high) " ≃ " => NestedNonFullyApplied.Equiv

variable {α β γ : Sort _}

@[simps] def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

@[simps (config := {rhsMd := semireducible, fullyApplied := false})] def Equiv.symm2 : (α ≃ β) ≃ (β ≃ α) :=
⟨Equiv.symm, Equiv.symm⟩

example (e : α ≃ β) : (Equiv.symm2.invFun e).toFun = e.invFun :=
begin
  dsimp only [Equiv.symm2_invFun_toFun]
  guard_target e.invFun = e.invFun
  rfl
end

/- do not prematurely unfold `Equiv.symm`, unless necessary -/
@[simps toFun toFun_toFun {rhsMd := semireducible})] def Equiv.symm3 : (α ≃ β) ≃ (β ≃ α) :=
Equiv.symm2

example (e : α ≃ β) (y : β) : (Equiv.symm3.toFun e).toFun y = e.invFun y ∧
  (Equiv.symm3.toFun e).toFun y = e.invFun y :=
begin
  split
  { dsimp only [Equiv.symm3_toFun], guard_target e.symm.toFun y = e.invFun y, rfl }
  { dsimp only [Equiv.symm3_toFun_toFun], guard_target e.invFun y = e.invFun y, rfl }
end

end NestedNonFullyApplied

-- test that type classes which are props work
class PropClass (n : ℕ) : Prop :=
(has_true : True)

instance has_PropClass (n : ℕ) : PropClass n := ⟨trivial⟩

structure NeedsPropClass (n : ℕ) [PropClass n] :=
(t : True)

@[simps] def test_PropClass : NeedsPropClass 1 :=
{ t := trivial }

/- check that when the coercion is given in eta-expanded form, we can also find the coercion. -/
structure AlgHom (R A B : Type _) :=
(toFun : A → B)

instance (R A B : Type _) : CoeFun (AlgHom R A B) (λ _ => A → B) := ⟨λ f => f.toFun⟩

@[simps] def myAlgHom : AlgHom Unit Bool Bool :=
{ toFun := id }

example (x : Bool) : myAlgHom x = id x := by simp only [myAlgHom_toFun]

structure RingHom (A B : Type _) where
  toFun : A → B

instance (A B : Type _) : CoeFun (RingHom A B) (λ _ => A → B) := ⟨λ f => f.toFun⟩

@[simps] def myRingHom : RingHom Bool Bool :=
{ toFun := id }

example (x : Bool) : myRingHom x = id x := by simp only [myRingHom_toFun]

/- check interaction with the `@[to_additive]` attribute -/

@[to_additive, simps]
instance {M N} [Mul M] [Mul N] : Mul (M × N) := ⟨λ p q => ⟨p.1 * q.1, p.2 * q.2⟩⟩

run_cmd liftTermElabM <| do
  let env ← getEnv
  guard <| env.find? `prod.Mul_mul |>.isSome
  guard <| env.find? `prod.Add_add |>.isSome
  -- has_attribute `to_additive `prod.Mul
  -- has_attribute `to_additive `prod.Mul_mul
  guard <| hasSimpAttribute `Prod.Mul_mul
  guard <| hasSimpAttribute `Prod.Add_add

example {M N} [Mul M] [Mul N] (p q : M × N) : p * q = ⟨p.1 * q.1, p.2 * q.2⟩ := by simp
example {M N} [Add M] [Add N] (p q : M × N) : p + q = ⟨p.1 + q.1, p.2 + q.2⟩ := by simp

/- The names of the generated simp lemmas for the additive version are not great if the definition
  had a custom additive name -/
@[to_additive my_add_instance, simps]
instance my_instance {M N} [One M] [One N] : One (M × N) := ⟨(1, 1)⟩

run_cmd liftTermElabM <| do
  get_decl `my_instance_one
  get_decl `my_add_instance_zero
  -- has_attribute `to_additive `my_instance -- todo
  -- has_attribute `to_additive `my_instance_one
  guard <| hasSimpAttribute `my_instance_one
  guard <| hasSimpAttribute `my_add_instance_zero

example {M N} [One M] [One N] : (1 : M × N) = ⟨1, 1⟩ := by simp
example {M N} [Zero M] [Zero N] : (0 : M × N) = ⟨0, 0⟩ := by simp

section
/-! Test `dsimp, simp` with the option `simpRhs` -/

local attribute [simp] nat.add

structure MyType :=
(A : Type)

@[simps (config := {simpRhs := true})] def myTypeDef : MyType :=
⟨{ x : Fin (Nat.add 3 0) // 1 + 1 = 2 }⟩

example (h : false) (x y : { x : Fin (Nat.add 3 0) // 1 + 1 = 2 }) : myTypeDef.A = Unit := by
  simp only [myTypeDef_A]
  guard_target == { x : Fin 3 // true } = Unit
  /- note: calling only one of `simp` or `dsimp` does not produce the current target
  as the following tests show. -/
  -- successIfFail { guard_hyp x : { x : Fin 3 // true } }
  dsimp at x
  -- successIfFail { guard_hyp x : { x : Fin 3 // true } }
  simp at y
  -- successIfFail { guard_hyp y : { x : Fin 3 // true } }
  simp at x
  dsimp at y
  guard_hyp x : { x : Fin 3 // true }
  guard_hyp y : { x : Fin 3 // true }
  contradiction

/- Test that `to_additive` copies the `@[_rfl_lemma]` attribute correctly -/
@[to_additive, simps]
def monoid_hom.my_comp {M N P : Type _} [mul_one_class M] [mul_one_class N] [mul_one_class P]
  (hnp : N →* P) (hmn : M →* N) : M →* P :=
{ toFun := hnp ∘ hmn, map_one' := by simp, map_mul' := by simp }

-- `simps` adds the `_rfl_lemma` attribute to `monoid_hom.my_comp_apply`
example {M N P : Type _} [mul_one_class M] [mul_one_class N] [mul_one_class P]
  (hnp : N →* P) (hmn : M →* N) (m : M) : hnp.my_comp hmn m = hnp (hmn m) := by
  dsimp
  guard_target == hnp (hmn m) = hnp (hmn m)
  rfl

-- `to_additive` adds the `_rfl_lemma` attribute to `add_monoid_hom.my_comp_apply`
example {M N P : Type _} [add_zero_class M] [add_zero_class N] [add_zero_class P]
  (hnp : N →+ P) (hmn : M →+ N) (m : M) : hnp.my_comp hmn m = hnp (hmn m) := by
  dsimp
  guard_target == hnp (hmn m) = hnp (hmn m)
  rfl

-- test that `to_additive` works with a custom name
@[to_additive some_test2, simps]
def some_test1 (M : Type _) [comm_monoid M] : subtype (λ f : M, true) := ⟨1, trivial⟩

run_cmd get_decl `some_test2_coe

end

/- Test custom compositions of projections. -/

section comp_projs

instance {α β} : CoeFun (α ≃ β) (λ _ => α → β) := ⟨Equiv'.toFun⟩

@[simps] protected def Equiv'.symm {α β} (f : α ≃ β) : β ≃ α :=
⟨f.invFun, f, f.right_inv, f.left_inv⟩

structure DecoratedEquiv (α : Sort _) (β : Sort _) extends Equiv' α β :=
(P_toFun    : Function.injective toFun )
(P_invFun   : Function.injective invFun)

instance {α β} : CoeFun (DecoratedEquiv α β) (λ _ => α → β) := ⟨λ f => f.toEquiv'⟩

def DecoratedEquiv.symm {α β : Sort _} (e : DecoratedEquiv α β) : DecoratedEquiv β α :=
{ toEquiv' := e.toEquiv'.symm
  P_toFun := e.P_invFun
  P_invFun := e.P_toFun }

def DecoratedEquiv.simps.apply {α β : Sort _} (e : DecoratedEquiv α β) : α → β := e
def DecoratedEquiv.simps.symm_apply {α β : Sort _} (e : DecoratedEquiv α β) : β → α := e.symm

initialize_simps_projections DecoratedEquiv
  (toEquiv'_toFun → apply, toEquiv'_invFun → symm_apply, -toEquiv')

@[simps] def foo (α : Type) : DecoratedEquiv α α :=
{ toFun    := λ x => x
  invFun   := λ x => x
  left_inv  := λ _ => rfl
  right_inv := λ _ => rfl
  P_toFun  := λ _ _ h => h
  P_invFun := λ _ _ h => h }

example {α : Type} (x : α) : (foo α).symm x = x := by
  dsimp
  guard_target == x = x
  rfl

@[simps toEquiv' apply symm_apply] def foo2 (α : Type) : DecoratedEquiv α α :=
{ P_toFun  := λ _ _ h => h
  P_invFun := λ _ _ h => h, ..foo.rfl }

example {α : Type} (x : α) : (foo2 α).toEquiv' x = x := by
  dsimp
  guard_target == foo.rfl x = x
  rfl

example {α : Type} (x : α) : foo2 α x = x := by
  dsimp
  guard_target == x = x
  rfl

structure FurtherDecoratedEquiv (α : Sort _) (β : Sort _) extends DecoratedEquiv α β :=
(Q_toFun    : Function.surjective toFun )
(Q_invFun   : Function.surjective invFun )

instance {α β} : CoeFun (FurtherDecoratedEquiv α β) (λ _ => α → β) :=
⟨λ f => f.toDecoratedEquiv⟩

def FurtherDecoratedEquiv.symm {α β : Sort _} (e : FurtherDecoratedEquiv α β) :
  FurtherDecoratedEquiv β α :=
{ toDecoratedEquiv := e.toDecoratedEquiv.symm
  Q_toFun := e.Q_invFun
  Q_invFun := e.Q_toFun }

def FurtherDecoratedEquiv.simps.apply {α β : Sort _} (e : FurtherDecoratedEquiv α β) : α → β := e
def FurtherDecoratedEquiv.simps.symm_apply {α β : Sort _} (e : FurtherDecoratedEquiv α β) :
  β → α := e.symm

initialize_simps_projections FurtherDecoratedEquiv
  (toDecoratedEquiv_toEquiv'_toFun → apply, toDecoratedEquiv_toEquiv'_invFun → symm_apply
  -toDecoratedEquiv, toDecoratedEquiv_toEquiv' → toEquiv', -toEquiv')

@[simps] def ffoo (α : Type) : FurtherDecoratedEquiv α α :=
{ toFun    := λ x => x
  invFun   := λ x => x
  left_inv  := λ _ => rfl
  right_inv := λ _ => rfl
  P_toFun  := λ _ _ h => h
  P_invFun := λ _ _ h => h
  Q_toFun  := λ y => ⟨y, rfl⟩
  Q_invFun := λ y => ⟨y, rfl⟩ }

example {α : Type} (x : α) : (ffoo α).symm x = x :=
by dsimp <;> guard_target == x = x <;> rfl }

@[simps] def ffoo3 (α : Type) : FurtherDecoratedEquiv α α :=
{ Q_toFun  := λ y => ⟨y, rfl⟩, Q_invFun  := λ y => ⟨y, rfl⟩, .. foo α }

@[simps apply toEquiv'_toFun toDecoratedEquiv_apply]
def ffoo4 (α : Type) : FurtherDecoratedEquiv α α :=
{ Q_toFun  := λ y => ⟨y, rfl⟩, Q_invFun  := λ y => ⟨y, rfl⟩, toDecoratedEquiv := foo α }

structure OneMore (α : Sort _) (β : Sort _) extends FurtherDecoratedEquiv α β

instance {α β} : CoeFun (OneMore α β) (λ _ => α → β) :=
⟨λ f => f.to_FurtherDecoratedEquiv⟩

def OneMore.symm {α β : Sort _} (e : OneMore α β) :
  OneMore β α :=
{ to_FurtherDecoratedEquiv := e.to_FurtherDecoratedEquiv.symm }

def OneMore.simps.apply {α β : Sort _} (e : OneMore α β) : α → β := e
def OneMore.simps.symm_apply {α β : Sort _} (e : OneMore α β) : β → α := e.symm

initialize_simps_projections OneMore
  (to_FurtherDecoratedEquiv_toDecoratedEquiv_toEquiv'_toFun → apply
   to_FurtherDecoratedEquiv_toDecoratedEquiv_toEquiv'_invFun → symm_apply
  -to_FurtherDecoratedEquiv, to_FurtherDecoratedEquiv_toDecoratedEquiv → to_dequiv
  -to_dequiv)

@[simps] def fffoo (α : Type) : OneMore α α :=
{ toFun    := λ x => x
  invFun   := λ x => x
  left_inv  := λ _ => rfl
  right_inv := λ _ => rfl
  P_toFun  := λ _ _ h => h
  P_invFun := λ _ _ h => h
  Q_toFun  := λ y => ⟨y, rfl⟩
  Q_invFun := λ y => ⟨y, rfl⟩ }

example {α : Type} (x : α) : (fffoo α).symm x = x :=
by dsimp <;> guard_target == x = x <;> rfl

@[simps apply to_dequiv_apply to_FurtherDecoratedEquiv_apply to_dequiv]
def fffoo2 (α : Type) : OneMore α α := fffoo α

/- test the case where a projection takes additional arguments. -/
variable {ι : Type _} [decidable_eq ι] (A : ι → Type _)

class something [Add ι] [∀ i, add_comm_monoid (A i)] :=
(mul {i} : A i →+ A i)

def something.simps.apply [Add ι] [∀ i, add_comm_monoid (A i)] [something A] {i : ι} (x : A i) :
  A i :=
something.mul ι x

initialize_simps_projections something (mul_toFun → apply, -mul)

class something2 [Add ι] :=
(mul {i j} : A i ≃ (A j ≃ A (i + j)))

def something2.simps.mul [Add ι] [something2 A] {i j : ι}
  (x : A i) (y : A j) : A (i + j) :=
something2.mul x y

initialize_simps_projections something2 (mul → mul', mul_toFun_toFun → mul, -mul')

attribute [ext] Equiv'

@[simps]
def thing (h : Bool ≃ (Bool ≃ Bool)) : something2 (λ x : ℕ, Bool) :=
{ mul := λ i j => { toFun := λ b => { toFun := h b
  invFun := (h b).symm
  left_inv := (h b).left_inv
  right_inv := (h b).right_inv }
  invFun := h.symm
  left_inv := by { convert h.left_inv, ext x; rfl }
  right_inv := by { convert h.right_inv, ext x; rfl } } }

example (h : Bool ≃ (Bool ≃ Bool)) (i j : ℕ) (b1 b2 : Bool) :
  @something2.mul _ _ _ _ (thing h) i j b1 b2 = h b1 b2 :=
by simp only [thing_mul]

end comp_projs

section
/-! Check that the tactic also works if the elaborated type of `type` reduces to `Sort _`, but is
  not `Sort _` itself. -/
structure MyFunctor (C D : Type _) :=
(obj : C → D)
local infixr:26 " ⥤ " => MyFunctor

@[simps]
def fooSum {I J : Type _} (C : I → Type _) {D : J → Type _} :
  (∀ i, C i) ⥤ (∀ j, D j) ⥤ (∀ s : I ⊕ J, Sum.rec C D s) :=
{ obj := λ f => { obj := λ g s => Sum.rec f g s }}

end

/- end Lean 3 test suite -/


-- other tests (to delete)


-- some testing

lemma Prod.eq {α β : Type _} {x y : α × β} (h₁ : x.1 = y.1) (h₂ : x.2 = y.2) : x = y :=
match x, y, h₁, h₂ with
| _x, (_, _), rfl, rfl => rfl -- using eta for Structures!

instance AddSemigroup.prod {α β : Type _} [AddSemigroup α] [AddSemigroup β] :
  AddSemigroup (α × β) :=
{ add := λ x y => ⟨x.1 + y.1, x.2 + y.2⟩
  add_assoc := λ _ _ _ => congrArg₂ Prod.mk (add_assoc ..) (add_assoc ..) } -- using eta for Structures!

lemma prod_mul {α β : Type _} [AddSemigroup α] [AddSemigroup β] (x y : α × β) :
  x + y = ⟨x.1 + y.1, x.2 + y.2⟩ := rfl

-- attribute [notation_class] Add HAdd
-- #print HAdd

initialize_simps_projections AddSemigroup (toAdd_add → add, -toAdd)

class MyClass (R : Type u) extends AddMonoidWithOne R, Monoid R
