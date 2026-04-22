import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Simps.Basic
import Mathlib.Lean.Exception
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Prod.Basic
import Mathlib.Tactic.Common

-- set_option trace.simps.debug true
-- set_option trace.simps.verbose true
-- set_option pp.universes true
set_option autoImplicit true

open Lean Meta Elab Term Command Simps

/-- Tests whether `declName` has the `@[simp]` attribute in `env`. -/
def hasSimpAttribute (env : Environment) (declName : Name) : Bool :=
  simpExtension.getState env |>.lemmaNames.contains <| .decl declName


structure Foo1 : Type where
  Projone : Nat
  two : Bool
  three : Nat → Bool
  four : 1 = 1
  five : 2 = 1

initialize_simps_projections Foo1 (Projone → toNat, two → toBool, three → coe, as_prefix coe,
  -toBool)

run_cmd liftTermElabM do
  let env ← getEnv
  let state := (Simps.structureExt.find? env `Foo1).get!
  guard <| state.1 == []
  guard <| state.2.map (·.1) == #[`toNat, `toBool, `coe, `four, `five]
  liftMetaM <| guard (← isDefEq (state.2[0]!.2) (← elabTerm (← `(Foo1.Projone)) none))
  liftMetaM <| guard (← isDefEq (state.2[1]!.2) (← elabTerm (← `(Foo1.two)) none))
  guard <| state.2.map (·.3) == (Array.range 5).map ([·])
  guard <| state.2.map (·.4) == #[true, false, true, false, false]
  guard <| state.2.map (·.5) == #[false, false, true, false, false]
  pure ()

structure Foo2 (α : Type _) : Type _ where
  elim : α × α

def Foo2.Simps.elim (α : Type _) : Foo2 α → α × α := fun x ↦ (x.elim.1, x.elim.2)

initialize_simps_projections Foo2


/--
trace: [simps.verbose] The projections for this structure have already been initialized by a previous invocation of `initialize_simps_projections` or `@[simps]`.
    Generated projections for Foo2:
    Projection elim: fun α x => (x.elim.1, x.elim.2)
-/
#guard_msgs in
initialize_simps_projections Foo2


@[simps]
def Foo2.foo2 : Foo2 Nat := ⟨(0, 0)⟩

-- run_cmd do
--   logInfo m!"{Simps.structureExt.find? (← getEnv) `Foo2 |>.get!}"

structure Left (α : Type _) extends Foo2 α where
  moreData1 : Nat
  moreData2 : Nat

initialize_simps_projections Left

structure Right (α : Type u) (β : Type v) extends Foo2 α where
  otherData : β

initialize_simps_projections Right (elim → newProjection, -otherData, +toFoo2)

run_cmd liftTermElabM do
  let env ← getEnv
  let state := (Simps.structureExt.find? env `Right).get!
  -- logInfo m!"{state}"
  guard <| state.1 == [`u, `v]
  guard <| state.2.map (·.1) == #[`toFoo2, `otherData, `newProjection]
  guard <| state.2.map (·.3) == #[[0], [1], [0,0]]
  guard <| state.2.map (·.4) == #[true, false, true]
  guard <| state.2.map (·.5) == #[false, false, false]

structure Top (α β : Type _) extends Left α, Right α β

initialize_simps_projections Top

structure NewTop (α β : Type _) extends Right α β, Left α

def NewTop.Simps.newElim {α β : Type _} (x : NewTop α β) : α × α := x.elim

initialize_simps_projections NewTop (elim → newElim)

run_cmd liftCoreM <| successIfFail <| getRawProjections .missing `DoesntExist

class Something (α : Type _) where
  op : α → α → α → α

instance {α : Type _} [Something α] : Add α :=
  ⟨fun x y ↦ Something.op x y y⟩


initialize_simps_projections Something

universe v u w

structure Equiv' (α : Sort _) (β : Sort _) where
  (toFun     : α → β)
  (invFun    : β → α)
  (left_inv  : invFun.LeftInverse toFun)
  (right_inv : invFun.RightInverse toFun)

infix:25 (priority := default+1) " ≃ " => Equiv'

/- Since `prod` and `PProd` are a special case for `@[simps]`, we define a new structure to test
  the basic functionality. -/
structure MyProd (α β : Type _) where (fst : α) (snd : β)

def MyProd.map {α α' β β'} (f : α → α') (g : β → β') (x : MyProd α β) : MyProd α' β' :=
  ⟨f x.1, g x.2⟩

namespace foo
@[simps] protected def rfl {α} : α ≃ α :=
  ⟨id, fun x ↦ x, fun _ ↦ rfl, fun _ ↦ rfl⟩

/- simps adds declarations -/
run_cmd liftTermElabM do
  let env ← getEnv
  guard <| env.find? `foo.rfl_toFun |>.isSome
  guard <| env.find? `foo.rfl_invFun |>.isSome
  guard <| env.find? `foo.rfl_left_inv |>.isNone
  guard <| env.find? `foo.rfl_right_inv |>.isNone
  guard <| simpsAttr.getParam? env `foo.rfl == #[`foo.rfl_toFun, `foo.rfl_invFun]

example (n : ℕ) : foo.rfl.toFun n = n := by rw [foo.rfl_toFun, id]
example (n : ℕ) : foo.rfl.invFun n = n := by rw [foo.rfl_invFun]

/- the declarations are `simp` lemmas -/
@[simps] def bar : ℕ × ℤ := (1, 2)

-- note: in Lean 4 the first test succeeds without `@[simps]`, however, the remaining tests don't
example : bar.1 = 1 := by simp
example {a : ℕ} {h : 1 = a} : bar.1 = a := by rw [bar_fst, h]
example {a : ℕ} {h : 1 = a} : bar.1 = a := by simp; rw [h]
example {a : ℤ} {h : 2 = a} : bar.2 = a := by simp; rw [h]
example {a : ℕ} {h : 1 = a} : bar.1 = a := by dsimp; rw [h] -- check that dsimp also unfolds
example {a : ℤ} {h : 2 = a} : bar.2 = a := by dsimp; rw [h]
example {α} (x y : α) (h : x = y) : foo.rfl.toFun x = y := by simp; rw [h]
example {α} (x y : α) (h : x = y) : foo.rfl.invFun x = y := by simp; rw [h]
-- example {α} (x y : α) (h : x = y) : foo.rfl.toFun = @id α := by { successIfFail {simp}, rfl }

/- check some failures -/
def bar1 : ℕ := 1 -- type is not a structure
noncomputable def bar2 {α} : α ≃ α :=
Classical.choice ⟨foo.rfl⟩

run_cmd liftCoreM do
  _ ← successIfFail <| simpsTac .missing `foo.bar1 { rhsMd := .default, simpRhs := true }
  --   "Invalid `simps` attribute. Target Nat is not a structure"
  _ ← successIfFail <| simpsTac .missing `foo.bar2 { rhsMd := .default, simpRhs := true }
  --   "Invalid `simps` attribute. The body is not a constructor application:
  -- Classical.choice (_ : Nonempty (α ≃ α))"
  pure ()

/- test that if a non-constructor is given as definition, then
  `{rhsMd := .default, simpRhs := true}` is applied automatically. -/
@[simps!] def rfl2 {α} : α ≃ α := foo.rfl

example {α} (x : α) : rfl2.toFun x = x ∧ rfl2.invFun x = x := by
  dsimp
  guard_target = x = x ∧ x = x
  exact ⟨rfl, rfl⟩

example {α} (x : α) : rfl2.toFun x = x ∧ rfl2.invFun x = x := by
  dsimp only [rfl2_toFun, rfl2_invFun]
  guard_target = x = x ∧ x = x
  exact ⟨rfl, rfl⟩

/- test `fullyApplied` option -/

@[simps -fullyApplied]
def rfl3 {α} : α ≃ α := ⟨id, fun x ↦ x, fun _ ↦ rfl, fun _ ↦ rfl⟩

end foo

/- we reduce the type when applying [simps] -/
def my_equiv := Equiv'
@[simps] def baz : my_equiv ℕ ℕ := ⟨id, fun x ↦ x, fun _ ↦ rfl, fun _ ↦ rfl⟩

/- todo: test that name clashes gives an error -/

/- check projections for nested structures -/

namespace CountNested
@[simps]
def nested1 : MyProd ℕ <| MyProd ℤ ℕ :=
  ⟨2, -1, 1⟩

@[simps -isSimp]
def nested2 : ℕ × MyProd ℕ ℕ :=
  ⟨2, MyProd.map Nat.succ Nat.pred ⟨1, 2⟩⟩

end CountNested

run_cmd liftTermElabM do
  let env ← getEnv
  guard <| env.find? `CountNested.nested1_fst |>.isSome
  guard <| env.find? `CountNested.nested1_snd_fst |>.isSome
  guard <| env.find? `CountNested.nested1_snd_snd |>.isSome
  guard <| env.find? `CountNested.nested2_fst |>.isSome
  guard <| env.find? `CountNested.nested2_snd |>.isSome
  guard <| simpsAttr.getParam? env `CountNested.nested1 ==
    #[`CountNested.nested1_fst, `CountNested.nested1_snd_fst, `CountNested.nested1_snd_snd]
  guard <| simpsAttr.getParam? env `CountNested.nested2 ==
    #[`CountNested.nested2_fst, `CountNested.nested2_snd]
  -- todo: test that another attribute can be added (not working yet)
  guard <| hasSimpAttribute env `CountNested.nested1_fst -- simp attribute is global
  guard <| not <| hasSimpAttribute env `CountNested.nested2_fst
    -- `- isSimp` doesn't add simp lemma
  -- todo: maybe test that there are no other lemmas generated
  -- guard <| 7 = env.fold 0
  --   (fun d n ↦ n + if d.to_name.components.init.ilast = `CountNested then 1 else 0)

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

/-- Test whether structure-eta-reduction is working correctly. -/
@[simps!]
def rflWithData {α} : EquivPlusData α α :=
  { foo.rfl with
    P := fun f ↦ f = id
    data := rfl }

@[simps!]
def rflWithData' {α} : EquivPlusData α α :=
  { P := fun f ↦ f = id
    data := rfl
    toEquiv' := foo.rfl }

/- test whether eta expansions are reduced correctly -/
@[simps!]
def test {α} : ComplicatedEquivPlusData α :=
  { foo.rfl with
    P := fun f ↦ f = id
    data := rfl
    extra := fun _ ↦ ⟨(⟨3, 5⟩ : MyProd _ _).1, (⟨3, 5⟩ : MyProd _ _).2⟩ }

/- test whether this is indeed rejected as a valid eta expansion -/
@[simps!]
def test_sneaky {α} : ComplicatedEquivPlusData α :=
  { foo.rfl with
    P := fun f ↦ f = id
    data := rfl
    extra := fun _ ↦ ⟨(3,5).1,(3,5).2⟩ }

run_cmd liftTermElabM do
  let env ← getEnv
  guard <| env.find? `rflWithData_toFun |>.isSome
  guard <| env.find? `rflWithData'_toFun |>.isSome
  guard <| env.find? `test_extra_fst |>.isSome
  guard <| simpsAttr.getParam? env `test ==
    #[`test_P, `test_extra_fst, `test_extra_snd, `test_toFun, `test_invFun]
  guard <| env.find? `test_sneaky_extra_fst |>.isSome
  guard <| env.find? `rflWithData_toEquiv_toFun |>.isNone
  guard <| env.find? `rflWithData'_toEquiv_toFun |>.isNone
  guard <| env.find? `test_sneaky_extra |>.isNone

structure PartiallyAppliedStr where
  (data : ℕ → MyProd ℕ ℕ)

/- if we have a partially applied constructor, we treat it as if it were eta-expanded -/
@[simps]
def partially_applied_term : PartiallyAppliedStr := ⟨MyProd.mk 3⟩

@[simps]
def another_term : PartiallyAppliedStr := ⟨fun n ↦ ⟨n + 1, n + 2⟩⟩

run_cmd liftTermElabM do
  let env ← getEnv
  guard <| env.find? `partially_applied_term_data_fst |>.isSome
  guard <| env.find? `partially_applied_term_data_snd |>.isSome
  guard <| simpsAttr.getParam? env `partially_applied_term ==
    #[`partially_applied_term_data_fst, `partially_applied_term_data_snd]

structure VeryPartiallyAppliedStr where
  (data : ∀ β, ℕ → β → MyProd ℕ β)

/- if we have a partially applied constructor, we treat it as if it were eta-expanded.
  (this is not very useful, and we could remove this behavior if convenient) -/
@[simps]
def very_partially_applied_term : VeryPartiallyAppliedStr := ⟨@MyProd.mk ℕ⟩

run_cmd liftTermElabM do
  let env ← getEnv
  guard <| env.find? `very_partially_applied_term_data_fst |>.isSome
  guard <| env.find? `very_partially_applied_term_data_snd |>.isSome

@[simps] def let1 : ℕ × ℤ :=
  let n := 3; ⟨n + 4, 5⟩

@[simps] def let2 : ℕ × ℤ :=
  let n := 3; let m := 4; let k := 5; ⟨n + m, k⟩

@[simps] def let3 : ℕ → ℕ × ℤ :=
  fun n ↦ let m := 4; let k := 5; ⟨n + m, k⟩

@[simps] def let4 : ℕ → ℕ × ℤ :=
  let m := 4; let k := 5; fun n ↦ ⟨n + m, k⟩

run_cmd liftTermElabM do
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
-- todo: error when naming arguments
@[simps fst] def specify1 : ℕ × ℕ × ℕ := (1, 2, 3)
@[simps snd] def specify2 : ℕ × ℕ × ℕ := (1, 2, 3)
@[simps snd_fst] def specify3 : ℕ × ℕ × ℕ := (1, 2, 3)
@[simps snd snd_snd] def specify4 : ℕ × ℕ × ℕ := (1, 2, 3) -- last argument is ignored
@[simps] noncomputable def specify5 : ℕ × ℕ × ℕ := (1, Classical.choice ⟨(2, 3)⟩)
end specify

run_cmd liftTermElabM do
  let env ← getEnv
  guard <| env.find? `specify.specify1_fst |>.isSome
  guard <| env.find? `specify.specify2_snd |>.isSome
  guard <| env.find? `specify.specify3_snd_fst |>.isSome
  guard <| env.find? `specify.specify4_snd_snd |>.isSome
  guard <| env.find? `specify.specify4_snd |>.isSome
  guard <| env.find? `specify.specify5_fst |>.isSome
  guard <| env.find? `specify.specify5_snd |>.isSome
  guard <| simpsAttr.getParam? env `specify.specify1 == #[`specify.specify1_fst]
  guard <| simpsAttr.getParam? env `specify.specify4 ==
    #[`specify.specify4_snd_snd, `specify.specify4_snd]
  guard <| simpsAttr.getParam? env `specify.specify5 ==
    #[`specify.specify5_fst, `specify.specify5_snd]
  _ ← successIfFail <| simpsTac .missing `specify.specify1 {} [("fst_fst", .missing)]
--     "Invalid simp lemma specify.specify1_fst_fst.
-- Projection fst doesn't exist, because target is not a structure."
  _ ← successIfFail <| simpsTac .missing `specify.specify1 {} [("foo_fst", .missing)]
--     "Invalid simp lemma specify.specify1_foo_fst. Structure prod does not have projection foo.
-- The known projections are:
--   [fst, snd]
-- You can also see this information by running
--   `initialize_simps_projections? prod`.
-- Note: these projection names might not correspond to the projection names of the structure."
  _ ← successIfFail <| simpsTac .missing `specify.specify1 {} [("snd_bar", .missing)]
--     "Invalid simp lemma specify.specify1_snd_bar. Structure prod does not have projection bar.
-- The known projections are:
--   [fst, snd]
-- You can also see this information by running
--   `initialize_simps_projections? prod`.
-- Note: these projection names might not correspond to the projection names of the structure."
  _ ← successIfFail <| simpsTac .missing `specify.specify5 { rhsMd := .default, simpRhs := true }
    [("snd_snd", .missing)]
--     "Invalid simp lemma specify.specify5_snd_snd.
-- The given definition is not a constructor application:
--   Classical.choice specify.specify5._proof_1"


/- We also eta-reduce if we explicitly specify the projection. -/
attribute [simps extra] test
example {α} {b : Bool} {x} (h : (⟨3, 5⟩ : MyProd _ _) = x) : (@test α).extra b = x := by
  dsimp
  rw [h]

/- check simpRhs option -/
@[simps +simpRhs] def Equiv'.trans {α β γ} (f : α ≃ β) (g : β ≃ γ) : α ≃ γ :=
⟨ g.toFun ∘ f.toFun,
  f.invFun ∘ g.invFun,
  (by intro x; simp [Equiv'.left_inv _ _]),
  (by intro x; simp [Equiv'.right_inv _ _])⟩


example {α β γ : Type} (f : α ≃ β) (g : β ≃ γ) (x : α) {z : γ} (h : g.toFun (f.toFun x) = z) :
  (f.trans g).toFun x = z := by
  dsimp only [Equiv'.trans_toFun]
  rw [h]

attribute [local simp] Nat.zero_add Nat.one_mul Nat.mul_one
@[simps +simpRhs] def myNatEquiv : ℕ ≃ ℕ :=
  ⟨fun n ↦ 0 + n, fun n ↦ 1 * n * 1, by intro n; simp, by intro n; simp⟩

example (n : ℕ) : myNatEquiv.toFun (myNatEquiv.toFun <| myNatEquiv.invFun n) = n := by
  { /-successIfFail { rfl },-/ simp only [myNatEquiv_toFun, myNatEquiv_invFun] }

@[simps +simpRhs] def succeed_without_simplification_possible : ℕ ≃ ℕ :=
  ⟨fun n ↦ n, fun n ↦ n, by intro n; rfl, by intro n; rfl⟩


/- test that we don't recursively take projections of `prod` and `PProd` -/
@[simps] def pprodEquivProd2 : PProd ℕ ℕ ≃ ℕ × ℕ :=
  { toFun := fun x ↦ ⟨x.1, x.2⟩
    invFun := fun x ↦ ⟨x.1, x.2⟩
    left_inv := fun ⟨_, _⟩ ↦ rfl
    right_inv := fun ⟨_, _⟩ ↦ rfl }

run_cmd liftTermElabM do
  let env ← getEnv
  guard <| env.find? `pprodEquivProd2_toFun |>.isSome
  guard <| env.find? `pprodEquivProd2_invFun |>.isSome

attribute [simps toFun_fst invFun_snd] pprodEquivProd2

run_cmd liftTermElabM do
  let env ← getEnv
  guard <| env.find? `pprodEquivProd2_toFun_fst |>.isSome
  guard <| env.find? `pprodEquivProd2_invFun_snd |>.isSome

-- we can disable this behavior with the option `notRecursive`.
@[simps! (notRecursive := [])] def pprodEquivProd22 : PProd ℕ ℕ ≃ ℕ × ℕ :=
  pprodEquivProd2

run_cmd liftTermElabM do
  let env ← getEnv
  guard <| env.find? `pprodEquivProd22_toFun_fst |>.isSome
  guard <| env.find? `pprodEquivProd22_toFun_snd |>.isSome
  guard <| env.find? `pprodEquivProd22_invFun_fst |>.isSome
  guard <| env.find? `pprodEquivProd22_invFun_snd |>.isSome

/- Tests with universe levels -/
class has_hom (obj : Type u) : Type (max u (v+1)) where
  (hom : obj → obj → Type v)

infixr:10 " ⟶ " => has_hom.hom -- type as \h

class CategoryStruct (obj : Type u) : Type (max u (v+1)) extends has_hom.{v} obj where
  (id   : ∀ X : obj, hom X X)
  (comp : ∀ {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z))

notation "𝟙" => CategoryStruct.id -- type as \b1
infixr:80 " ≫ " => CategoryStruct.comp -- type as \gg

namespace types

@[simps] instance : CategoryStruct (Type u) :=
  { hom  := fun a b ↦ (a → b)
    id   := fun _ ↦ id
    comp := fun f g ↦ g ∘ f }

end types

/--
info: types.comp_def.{u} {X✝ Y✝ Z✝ : Type u} (f : X✝ → Y✝) (g : Y✝ → Z✝) (a✝ : X✝) : (f ≫ g) a✝ = (g ∘ f) a✝
-/
#guard_msgs in
#check types.comp_def

@[ext] theorem types.ext {X Y : Type u} {f g : X ⟶ Y} : (∀ x, f x = g x) → f = g := funext

example (X : Type u) {x : Type u} (h : (X → X) = x) : (X ⟶ X) = x := by simp; rw [h]
example (X : Type u) {f : X → X} (h : ∀ x, f x = x) : 𝟙 X = f := by ext; simp; rw [h]
example (X Y Z : Type u) (f : X ⟶ Y) (g : Y ⟶ Z) {k : X → Z} (h : ∀ x, g (f x) = k x) :
  f ≫ g = k := by ext; simp; rw [h]

-- Ensure that a universe polymorphic projection like `PLift.down`
-- doesn't cause `simp` lemmas about proofs.

instance discreteCategory : CategoryStruct Nat where
  hom X Y := ULift (PLift (X = Y))
  id _ := ULift.up (PLift.up rfl)
  comp f g := ⟨⟨f.1.1.trans g.1.1⟩⟩

structure Prefunctor (C : Type u) [CategoryStruct C] (D : Type v) [CategoryStruct D] where
  /-- The action of a (pre)functor on vertices/objects. -/
  obj : C → D
  /-- The action of a (pre)functor on edges/arrows/morphisms. -/
  map : ∀ {X Y : C}, (X ⟶ Y) → (obj X ⟶ obj Y)

@[simps]
def IdentityPreunctor : Prefunctor (Type u) Nat where
  obj _ := 5
  map _ := ⟨⟨rfl⟩⟩

/-- error: Unknown identifier `IdentityPreunctor_map_down_down` -/
#guard_msgs in
#check IdentityPreunctor_map_down_down

namespace coercing

structure FooStr where
  (c : Type)
  (x : c)

instance : CoeSort FooStr Type := ⟨FooStr.c⟩

@[simps] def foo : FooStr := ⟨ℕ, 3⟩
@[simps] def foo2 : FooStr := ⟨ℕ, 34⟩

example {x : Type} (h : ℕ = x) : foo = x := by simp only [foo_c]; rw [h]
example {x : ℕ} (h : (3 : ℕ) = x) : foo.x = x := by simp only [foo_x]; rw [h]

structure VooStr (n : ℕ) where
  (c : Type)
  (x : c)

instance (n : ℕ) : CoeSort (VooStr n) Type := ⟨VooStr.c⟩

@[simps] def voo : VooStr 7 := ⟨ℕ, 3⟩
@[simps] def voo2 : VooStr 4 := ⟨ℕ, 34⟩

example {x : Type} (h : ℕ = x) : voo = x := by simp only [voo_c]; rw [h]
example {x : ℕ} (h : (3 : ℕ) = x) : voo.x = x := by simp only [voo_x]; rw [h]

structure Equiv2 (α : Sort _) (β : Sort _) where
  (toFun     : α → β)
  (invFun    : β → α)
  (left_inv  : invFun.LeftInverse toFun)
  (right_inv : invFun.RightInverse toFun)

instance {α β} : CoeFun (Equiv2 α β) (fun _ ↦ α → β) := ⟨Equiv2.toFun⟩

@[simps] protected def rfl2 {α} : Equiv2 α α :=
  ⟨fun x ↦ x, fun x ↦ x, fun _ ↦ rfl, fun _ ↦ rfl⟩

example {α} (x x' : α) (h : x = x') : coercing.rfl2 x = x' := by rw [coercing.rfl2_toFun, h]
example {α} (x x' : α) (h : x = x') : coercing.rfl2 x = x' := by simp; rw [h]
example {α} (x x' : α) (h : x = x') : coercing.rfl2.invFun x = x' := by simp; rw [h]

@[simps] protected def Equiv2.symm {α β} (f : Equiv2 α β) : Equiv2 β α :=
  ⟨f.invFun, f, f.right_inv, f.left_inv⟩

@[simps] protected def Equiv2.symm2 {α β} (f : Equiv2 α β) : Equiv2 β α :=
  ⟨f.invFun, f.toFun, f.right_inv, f.left_inv⟩

@[simps -fullyApplied] protected def Equiv2.symm3 {α β} (f : Equiv2 α β) : Equiv2 β α :=
  ⟨f.invFun, f, f.right_inv, f.left_inv⟩

example {α β} (f : Equiv2 α β) (y : β) {x} (h : f.invFun y = x) : f.symm y = x := by simp; rw [h]
example {α β} (f : Equiv2 α β) (x : α) {z} (h : f x = z) : f.symm.invFun x = z := by simp; rw [h]

-- example {α β} (f : Equiv2 α β) {x} (h : f = x) : f.symm.invFun = x :=
-- by { /-successIfFail {simp <;> rw [h]} <;>-/ rfl }
example {α β} (f : Equiv2 α β) {x} (h : f = x) : f.symm3.invFun = x := by simp; rw [h]

class Semigroup (G : Type u) extends Mul G where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)

@[simps] instance {α β} [Semigroup α] [Semigroup β] : Semigroup (α × β) :=
  { mul := fun x y ↦ (x.1 * y.1, x.2 * y.2)
    mul_assoc := fun _ _ _ ↦ Prod.ext (Semigroup.mul_assoc ..) (Semigroup.mul_assoc ..) }

example {α β} [Semigroup α] [Semigroup β] (x y : α × β) : x * y = (x.1 * y.1, x.2 * y.2) := by simp
example {α β} [Semigroup α] [Semigroup β] (x y : α × β) : (x * y).1 = x.1 * y.1 := by simp

structure BSemigroup where
  (G : Type _)
  (op : G → G → G)
  -- (infix:60 " * " => op) -- this seems to be removed
  (op_assoc : ∀ (x y z : G), op (op x y) z = op x (op y z))

namespace BSemigroup

instance : CoeSort BSemigroup (Type _) := ⟨BSemigroup.G⟩
-- We could try to generate lemmas with this `HMul` instance, but it is unused in mathlib3/mathlib4.
-- Therefore, this is ignored.
instance (G : BSemigroup) : Mul G := ⟨G.op⟩

protected def prod (G H : BSemigroup) : BSemigroup :=
  { G := G × H
    op := fun x y ↦ (x.1 * y.1, x.2 * y.2)
    op_assoc := fun _ _ _ ↦ Prod.ext (BSemigroup.op_assoc ..) (BSemigroup.op_assoc ..) }

end BSemigroup

class ExtendingStuff (G : Type u) extends Mul G, Zero G, Neg G, HasSubset G where
  new_axiom : ∀ x : G, x * - 0 ⊆ - x

@[simps!, instance_reducible] def bar : ExtendingStuff ℕ :=
  { neg := Nat.succ
    Subset := fun _ _ ↦ True
    new_axiom := fun _ ↦ trivial }

section
attribute [local instance] bar
example (x : ℕ) : x * - 0 ⊆ - x := by simp
end

class new_ExtendingStuff (G : Type u) extends Mul G, Zero G, Neg G, HasSubset G where
  new_axiom : ∀ x : G, x * - 0 ⊆ - x

@[simps!, instance_reducible] def new_bar : new_ExtendingStuff ℕ :=
  { neg := Nat.succ
    Subset := fun _ _ ↦ True
    new_axiom := fun _ ↦ trivial }

section
attribute [local instance] new_bar
example (x : ℕ) : x * - 0 ⊆ - x := by simp
end


end coercing

namespace ManualCoercion

structure Equiv (α : Sort _) (β : Sort _) where
  (toFun  : α → β)
  (invFun : β → α)

local infix:25 (priority := high) " ≃ " => ManualCoercion.Equiv

variable {α β γ : Sort _}

instance : CoeFun (α ≃ β) (fun _ ↦ α → β) := ⟨Equiv.toFun⟩

def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
def Equiv.Simps.invFun (e : α ≃ β) : β → α := e.symm

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[simps +simpRhs]
protected def Equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ (e₁ : α → β), e₁.symm ∘ (e₂.symm : γ → β)⟩

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : γ) {z} (h : e₁.symm (e₂.symm x) = z) :
    (e₁.trans e₂).symm x = z := by
  simp only [Equiv.trans_invFun]; rw [h]

end ManualCoercion

namespace FaultyManualCoercion

structure Equiv (α : Sort _) (β : Sort _) where
  (toFun  : α → β)
  (invFun : β → α)

local infix:25 (priority := high) " ≃ " => FaultyManualCoercion.Equiv

variable {α β γ : Sort _}

/-- See Note [custom simps projection] -/
noncomputable def Equiv.Simps.invFun (e : α ≃ β) : β → α := Classical.choice ⟨e.invFun⟩

run_cmd liftTermElabM do
  successIfFail (getRawProjections .missing `FaultyManualCoercion.Equiv)
-- "Invalid custom projection:
--   fun {α : Sort u_1} {β : Sort u_2} (e : α ≃ β) ↦ Classical.choice _
-- Expression is not definitionally equal to
--   fun (α : Sort u_1) (β : Sort u_2) (x : α ≃ β) ↦ x.invFun"

end FaultyManualCoercion

namespace ManualInitialize
/- defining a manual coercion. -/
variable {α β γ : Sort _}

structure Equiv (α : Sort _) (β : Sort _) where
  (toFun  : α → β)
  (invFun : β → α)

local infix:25 (priority := high) " ≃ " => ManualInitialize.Equiv

instance : CoeFun (α ≃ β) (fun _ ↦ α → β) := ⟨Equiv.toFun⟩

def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
def Equiv.Simps.invFun (e : α ≃ β) : β → α := e.symm

initialize_simps_projections Equiv

-- run_cmd has_attribute `_simps_str `ManualInitialize.Equiv

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[simps +simpRhs]
protected def Equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ (e₁ : α → β), e₁.symm ∘ (e₂.symm : γ → β)⟩

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : γ) {z} (h : e₁.symm (e₂.symm x) = z) :
    (e₁.trans e₂).symm x = z := by
  simp only [Equiv.trans_invFun]; rw [h]

end ManualInitialize

namespace FaultyUniverses

variable {α β γ : Sort _}

structure Equiv (α : Sort u) (β : Sort v) where
  (toFun  : α → β)
  (invFun : β → α)

local infix:25 (priority := high) " ≃ " => FaultyUniverses.Equiv

instance : CoeFun (α ≃ β) (fun _ ↦ α → β) := ⟨Equiv.toFun⟩

def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
def Equiv.Simps.invFun {α : Type u} {β : Type v} (e : α ≃ β) : β → α := e.symm

run_cmd liftTermElabM do
  successIfFail (getRawProjections .missing `FaultyUniverses.Equiv)
-- "Invalid custom projection:
--   fun {α} {β} e => (Equiv.symm e).toFun
-- Expression has different type than FaultyUniverses.Equiv.invFun. Given type:
--   {α : Type u} → {β : Type v} → α ≃ β → β → α
-- Expected type:
--   (α : Sort u) → (β : Sort v) → α ≃ β → β → α
-- Note: make sure order of implicit arguments is exactly the same."

end FaultyUniverses

namespace ManualUniverses

variable {α β γ : Sort _}

structure Equiv (α : Sort u) (β : Sort v) where
  (toFun  : α → β)
  (invFun : β → α)

local infix:25 (priority := high) " ≃ " => ManualUniverses.Equiv

instance : CoeFun (α ≃ β) (fun _ ↦ α → β) := ⟨Equiv.toFun⟩

def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
-- test: intentionally using different universe levels for Equiv.symm than for Equiv
def Equiv.Simps.invFun {α : Sort w} {β : Sort u} (e : α ≃ β) : β → α := e.symm

-- check whether we can generate custom projections even if the universe names don't match
initialize_simps_projections Equiv

end ManualUniverses

namespace ManualProjectionNames

structure Equiv (α : Sort _) (β : Sort _) where
  (toFun  : α → β)
  (invFun : β → α)

local infix:25 (priority := high) " ≃ " => ManualProjectionNames.Equiv

variable {α β γ : Sort _}

instance : CoeFun (α ≃ β) (fun _ ↦ α → β) := ⟨Equiv.toFun⟩

def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
def Equiv.Simps.symm_apply (e : α ≃ β) : β → α := e.symm

initialize_simps_projections Equiv (toFun → apply, invFun → symm_apply)

run_cmd liftTermElabM do
  let data ← getRawProjections .missing `ManualProjectionNames.Equiv
  guard <| data.2.map (·.name) == #[`apply, `symm_apply]

@[simps +simpRhs]
protected def Equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ (e₁ : α → β), e₁.symm ∘ (e₂.symm : γ → β)⟩

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : α) {z} (h : e₂ (e₁ x) = z) : (e₁.trans e₂) x = z := by
  simp only [Equiv.trans_apply]; rw [h]

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : γ) {z} (h : e₁.symm (e₂.symm x) = z) :
    (e₁.trans e₂).symm x = z := by
  simp only [Equiv.trans_symm_apply]; rw [h]

-- the new projection names are parsed correctly (the old projection names won't work anymore)
@[simps apply symm_apply] protected def Equiv.trans2 (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ (e₁ : α → β), e₁.symm ∘ (e₂.symm : γ → β)⟩

end ManualProjectionNames

namespace PrefixProjectionNames

structure Equiv (α : Sort _) (β : Sort _) where
  (toFun  : α → β)
  (invFun : β → α)

local infix:25 (priority := high) " ≃ " => PrefixProjectionNames.Equiv

variable {α β γ : Sort _}

instance : CoeFun (α ≃ β) (fun _ ↦ α → β) := ⟨Equiv.toFun⟩

def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
def Equiv.Simps.symm_apply (e : α ≃ β) : β → α := e.symm
initialize_simps_projections Equiv (toFun → coe, as_prefix coe, invFun → symm_apply)

run_cmd liftTermElabM do
  let data ← getRawProjections .missing `PrefixProjectionNames.Equiv
  guard <| data.2.map (·.name) = #[`coe, `symm_apply]
  guard <| data.2.map (·.isPrefix) = #[true, false]

@[simps +simpRhs]
protected def Equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ (e₁ : α → β), e₁.symm ∘ (e₂.symm : γ → β)⟩

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : α) {z} (h : e₂ (e₁ x) = z) : (e₁.trans e₂) x = z := by
  simp only [Equiv.coe_trans]
  rw [h]

-- the new projection names are parsed correctly
@[simps coe symm_apply] protected def Equiv.trans2 (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
  ⟨e₂ ∘ (e₁ : α → β), e₁.symm ∘ (e₂.symm : γ → β)⟩

-- it interacts somewhat well with multiple projections (though the generated name is not great)
@[simps! snd_coe_fst] def foo {α β γ δ : Type _} (x : α) (e₁ : α ≃ β) (e₂ : γ ≃ δ) :
    α × (α × γ ≃ β × δ) :=
  ⟨x, Prod.map e₁ e₂, Prod.map e₁.symm e₂.symm⟩

example {α β γ δ : Type _} (x : α) (e₁ : α ≃ β) (e₂ : γ ≃ δ) (z : α × γ) {y} (h : e₁ z.1 = y) :
    ((foo x e₁ e₂).2 z).1 = y := by
  simp only [coe_foo_snd_fst]
  rw [h]

end PrefixProjectionNames

namespace DsimpLhs

structure Functor where
  obj : Type → Type
  map {X Y : Type} (f : X → Y) : obj X → obj Y

structure NatIso (F G : Functor) where
  app (X : Type) : Equiv (F.obj X) (G.obj X)
  naturality {X Y : Type} (f : X → Y) : G.map f ∘ app X = app Y ∘ F.map f

def NatIso.refl (F : Functor) : NatIso F F where
  app X := Equiv.refl _
  naturality := by simp

abbrev Functor.const (X : Type) : Functor where
  obj _ := X
  map _ := id

abbrev Functor.id : Functor where
  obj X := X
  map f := f

abbrev Functor.comp (F G : Functor) : Functor where
  obj X := G.obj (F.obj X)
  map f := G.map (F.map f)

@[simps!]
def iso (X : Type) : NatIso (Functor.id.comp (.const X)) (.const X) := NatIso.refl _

set_option pp.explicit true in
/-- info: DsimpLhs.iso_app_apply (X X✝ : Type) (a : (Functor.id.comp (Functor.const X)).obj X✝) :
  @Eq ((Functor.id.comp (Functor.const X)).obj X✝)
    (@DFunLike.coe (Equiv ((Functor.id.comp (Functor.const X)).obj X✝) ((Functor.id.comp (Functor.const X)).obj X✝))
      ((Functor.id.comp (Functor.const X)).obj X✝) (fun x => (Functor.id.comp (Functor.const X)).obj X✝)
      (@EquivLike.toFunLike
        (Equiv ((Functor.id.comp (Functor.const X)).obj X✝) ((Functor.id.comp (Functor.const X)).obj X✝))
        ((Functor.id.comp (Functor.const X)).obj X✝) ((Functor.id.comp (Functor.const X)).obj X✝)
        (@Equiv.instEquivLike ((Functor.id.comp (Functor.const X)).obj X✝)
          ((Functor.id.comp (Functor.const X)).obj X✝)))
      (@NatIso.app (Functor.id.comp (Functor.const X)) (Functor.const X) (iso X) X✝) a)
    a -/
#guard_msgs in
#check iso_app_apply

@[simps! +dsimpLhs]
def iso' (X : Type) : NatIso (Functor.id.comp (.const X)) (.const X) := NatIso.refl _

set_option pp.explicit true in
/-- info: DsimpLhs.iso'_app_apply (X X✝ : Type) (a : (Functor.id.comp (Functor.const X)).obj X✝) :
  @Eq ((Functor.id.comp (Functor.const X)).obj X✝)
    (@DFunLike.coe (Equiv X X) X (fun x => X)
      (@EquivLike.toFunLike
        (Equiv ((Functor.id.comp (Functor.const X)).obj X✝) ((Functor.id.comp (Functor.const X)).obj X✝))
        ((Functor.id.comp (Functor.const X)).obj X✝) ((Functor.id.comp (Functor.const X)).obj X✝)
        (@Equiv.instEquivLike ((Functor.id.comp (Functor.const X)).obj X✝)
          ((Functor.id.comp (Functor.const X)).obj X✝)))
      (@NatIso.app (Functor.id.comp (Functor.const X)) (Functor.const X) (iso' X) X✝) a)
    a -/
#guard_msgs in
#check iso'_app_apply

example (n : Nat) : (iso Nat).app Nat n = n := by
  dsimp only
  fail_if_success simp
  rfl

example (n : Nat) : (iso' Nat).app Nat n = n := by
  simp

end DsimpLhs

-- test transparency setting
structure SetPlus (α : Type) where
  (s : Set α)
  (x : α)
  (h : x ∈ s)

@[simps] def Nat.SetPlus1 : SetPlus ℕ := ⟨Set.univ, 1, trivial⟩

example {x : Set ℕ} (h : Set.univ = x) : Nat.SetPlus1.s = x := by
  dsimp only [Nat.SetPlus1_s]
  rw [h]

@[simps (typeMd := .default)]
def Nat.SetPlus2 : SetPlus ℕ := ⟨Set.univ, 1, trivial⟩

example {x : Set ℕ} (h : Set.univ = x) : Nat.SetPlus2.s = x := by
  fail_if_success { rw [h] }
  exact h

@[simps (rhsMd := .default)]
def Nat.SetPlus3 : SetPlus ℕ := Nat.SetPlus1

example {x : Set ℕ} (h : Set.univ = x) : Nat.SetPlus3.s = x := by
  dsimp only [Nat.SetPlus3_s]
  rw [h]

namespace NestedNonFullyApplied

structure Equiv (α : Sort _) (β : Sort _) where
  (toFun  : α → β)
  (invFun : β → α)

local infix:25 (priority := high) " ≃ " => NestedNonFullyApplied.Equiv

variable {α β γ : Sort _}

@[simps] def Equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

@[simps (rhsMd := .default) -fullyApplied]
def Equiv.symm2 : (α ≃ β) ≃ (β ≃ α) :=
  ⟨Equiv.symm, Equiv.symm⟩

example (e : α ≃ β) {x : β → α} (h : e.invFun = x) : (Equiv.symm2.invFun e).toFun = x := by
  dsimp only [Equiv.symm2_invFun_toFun]
  rw [h]

/- do not prematurely unfold `Equiv.symm`, unless necessary -/
@[simps (rhsMd := .default) toFun toFun_toFun] def Equiv.symm3 : (α ≃ β) ≃ (β ≃ α) :=
  Equiv.symm2

-- this fails in Lean 4, not sure what is going on
-- example (e : α ≃ β) (y : β) : (Equiv.symm3.toFun e).toFun y = e.invFun y ∧
--   (Equiv.symm3.toFun e).toFun y = e.invFun y := by
--   constructor
--   { dsimp only [Equiv.symm3_toFun]
--     guard_target = e.symm.toFun y = e.invFun y
--     rfl }
--   { dsimp only [Equiv.symm3_toFun_toFun]
--     guard_target = e.invFun y = e.invFun y
--     rfl }

end NestedNonFullyApplied

-- test that type classes which are props work
class PropClass (n : ℕ) : Prop where
  has_true : True

instance has_PropClass (n : ℕ) : PropClass n := ⟨trivial⟩

structure NeedsPropClass (n : ℕ) [PropClass n] where
  (t : True)

@[simps] def test_PropClass : NeedsPropClass 1 :=
  { t := trivial }

/- check that when the coercion is given in eta-expanded form, we can also find the coercion. -/
structure AlgHom (R A B : Type _) where
  (toFun : A → B)

instance (R A B : Type _) : CoeFun (AlgHom R A B) (fun _ ↦ A → B) := ⟨fun f ↦ f.toFun⟩

@[simps] def myAlgHom : AlgHom Unit Bool Bool :=
  { toFun := id }

example (x : Bool) {z} (h : id x = z) : myAlgHom x = z := by
  simp only [myAlgHom_toFun]
  rw [h]

structure RingHom (A B : Type _) where
  toFun : A → B

instance (A B : Type _) : CoeFun (RingHom A B) (fun _ ↦ A → B) := ⟨fun f ↦ f.toFun⟩

@[simps] def myRingHom : RingHom Bool Bool :=
{ toFun := id }

example (x : Bool) {z} (h : id x = z) : myRingHom x = z := by
  simp only [myRingHom_toFun]
  rw [h]

/- check interaction with the `@[to_additive]` attribute -/

-- set_option trace.simps.debug true

@[to_additive (attr := simps)]
instance Prod.instMul {M N} [Mul M] [Mul N] : Mul (M × N) := ⟨fun p q ↦ ⟨p.1 * q.1, p.2 * q.2⟩⟩

run_cmd liftTermElabM do
  let env ← getEnv
  guard <| env.find? `Prod.mul_def |>.isSome
  guard <| env.find? `Prod.add_def |>.isSome
  -- hasAttribute `to_additive `Prod.instMul
  -- hasAttribute `to_additive `Prod.mul_def
  guard <| hasSimpAttribute env `Prod.mul_def
  guard <| hasSimpAttribute env `Prod.add_def

example {M N} [Mul M] [Mul N] (p q : M × N) : p * q = ⟨p.1 * q.1, p.2 * q.2⟩ := by simp
example {M N} [Add M] [Add N] (p q : M × N) : p + q = ⟨p.1 + q.1, p.2 + q.2⟩ := by simp

/- The names of the generated simp lemmas for the additive version are not great if the definition
  had a custom additive name -/
@[to_additive (attr := simps) my_add_instance]
instance my_instance {M N} [One M] [One N] : One (M × N) := ⟨(1, 1)⟩

run_cmd liftTermElabM do
  let env ← getEnv
  guard <| env.find? `my_instance_one |>.isSome
  guard <| env.find? `my_add_instance_zero |>.isSome
  -- hasAttribute `to_additive `my_instance -- todo
  -- hasAttribute `to_additive `my_instance_one
  guard <| hasSimpAttribute env `my_instance_one
  guard <| hasSimpAttribute env `my_add_instance_zero

example {M N} [One M] [One N] : (1 : M × N) = ⟨1, 1⟩ := by simp
example {M N} [Zero M] [Zero N] : (0 : M × N) = ⟨0, 0⟩ := by simp

section
/-! Test `dsimp, simp` with the option `simpRhs` -/

attribute [local simp] Nat.add

structure MyType where
  (A : Type)

@[simps +simpRhs] def myTypeDef : MyType :=
  ⟨{ _x : Fin (Nat.add 3 0) // 1 + 1 = 2 }⟩

-- todo: this fails in Lean 4, not sure what is going on
set_option linter.unusedVariables false in
example (h : false) (x y : { x : Fin (Nat.add 3 0) // 1 + 1 = 2 }) : myTypeDef.A = Unit := by
  simp only [myTypeDef_A]
  guard_target = { _x : Fin 3 // True } = Unit
  /- note: calling only one of `simp` or `dsimp` does not produce the current target
  as the following tests show. -/
  fail_if_success { guard_hyp x : { _x : Fin 3 // true } }
  dsimp at x
  fail_if_success { guard_hyp x : { _x : Fin 3 // true } }
  simp at y
  fail_if_success { guard_hyp y : { _x : Fin 3 // true } }
  simp at x
  guard_hyp x : { _x : Fin 3 // True }
  guard_hyp y : { _x : Fin 3 // True }
  contradiction

-- test that `to_additive` works with a custom name
@[to_additive (attr := simps) some_test2]
def some_test1 (M : Type _) [CommMonoid M] : Subtype (fun _ : M ↦ True) := ⟨1, trivial⟩

run_cmd liftTermElabM do
  let env ← getEnv
  guard <| env.find? `some_test2_coe |>.isSome

end

/- Test custom compositions of projections. -/

section comp_projs

instance {α β} : CoeFun (α ≃ β) (fun _ ↦ α → β) := ⟨Equiv'.toFun⟩

@[simps] protected def Equiv'.symm {α β} (f : α ≃ β) : β ≃ α :=
  ⟨f.invFun, f, f.right_inv, f.left_inv⟩

structure DecoratedEquiv (α : Sort _) (β : Sort _) extends Equiv' α β where
  (P_toFun  : Function.Injective toFun)
  (P_invFun : Function.Injective invFun)

instance {α β} : CoeFun (DecoratedEquiv α β) (fun _ ↦ α → β) := ⟨fun f ↦ f.toEquiv'⟩

def DecoratedEquiv.symm {α β : Sort _} (e : DecoratedEquiv α β) : DecoratedEquiv β α :=
  { toEquiv' := e.toEquiv'.symm
    P_toFun := e.P_invFun
    P_invFun := e.P_toFun }

def DecoratedEquiv.Simps.apply {α β : Sort _} (e : DecoratedEquiv α β) : α → β := e
def DecoratedEquiv.Simps.symm_apply {α β : Sort _} (e : DecoratedEquiv α β) : β → α := e.symm

initialize_simps_projections DecoratedEquiv (toFun → apply, invFun → symm_apply, -toEquiv')

@[simps] def foo (α : Type) : DecoratedEquiv α α :=
  { toFun     := fun x ↦ x
    invFun    := fun x ↦ x
    left_inv  := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    P_toFun   := fun _ _ h ↦ h
    P_invFun  := fun _ _ h ↦ h }

example {α : Type} (x z : α) (h : x = z) : (foo α).symm x = z := by
  dsimp
  guard_target = x = z
  rw [h]

@[simps! toEquiv' apply symm_apply] def foo2 (α : Type) : DecoratedEquiv α α :=
  { foo.rfl with
    P_toFun  := fun _ _ h ↦ h
    P_invFun := fun _ _ h ↦ h }


example {α : Type} (x z : α) (h : foo.rfl x = z) : (foo2 α).toEquiv' x = z := by
  dsimp only [foo2_toEquiv']
  guard_target = foo.rfl x = z
  rw [h]

example {α : Type} (x z : α) (h : x = z) : (foo2 α).toEquiv' x = z := by
  dsimp only [foo2_apply]
  guard_target = x = z
  rw [h]

example {α : Type} (x z : α) (h : x = z) : foo2 α x = z := by
  dsimp
  guard_target = x = z
  rw [h]

structure FurtherDecoratedEquiv (α : Sort _) (β : Sort _) extends DecoratedEquiv α β where
  (Q_toFun  : Function.Surjective toFun)
  (Q_invFun : Function.Surjective invFun)

instance {α β} : CoeFun (FurtherDecoratedEquiv α β) (fun _ ↦ α → β) :=
  ⟨fun f ↦ f.toDecoratedEquiv⟩

def FurtherDecoratedEquiv.symm {α β : Sort _} (e : FurtherDecoratedEquiv α β) :
    FurtherDecoratedEquiv β α :=
  { toDecoratedEquiv := e.toDecoratedEquiv.symm
    Q_toFun := e.Q_invFun
    Q_invFun := e.Q_toFun }

def FurtherDecoratedEquiv.Simps.apply {α β : Sort _} (e : FurtherDecoratedEquiv α β) : α → β := e
def FurtherDecoratedEquiv.Simps.symm_apply {α β : Sort _} (e : FurtherDecoratedEquiv α β) :
    β → α := e.symm

initialize_simps_projections FurtherDecoratedEquiv
  (toFun → apply, invFun → symm_apply, -toDecoratedEquiv, toEquiv' → toEquiv', -toEquiv')

@[simps] def ffoo (α : Type) : FurtherDecoratedEquiv α α :=
  { toFun     := fun x ↦ x
    invFun    := fun x ↦ x
    left_inv  := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    P_toFun   := fun _ _ h ↦ h
    P_invFun  := fun _ _ h ↦ h
    Q_toFun   := fun y ↦ ⟨y, rfl⟩
    Q_invFun  := fun y ↦ ⟨y, rfl⟩ }

example {α : Type} (x z : α) (h : x = z) : (ffoo α).symm x = z := by
  dsimp
  guard_target = x = z
  rw [h]

@[simps!] def ffoo3 (α : Type) : FurtherDecoratedEquiv α α :=
  { foo α with Q_toFun := fun y ↦ ⟨y, rfl⟩, Q_invFun := fun y ↦ ⟨y, rfl⟩ }

@[simps! apply toEquiv' toEquiv'_toFun toDecoratedEquiv_apply]
def ffoo4 (α : Type) : FurtherDecoratedEquiv α α :=
  { Q_toFun := fun y ↦ ⟨y, rfl⟩, Q_invFun := fun y ↦ ⟨y, rfl⟩, toDecoratedEquiv := foo α }

structure OneMore (α : Sort _) (β : Sort _) extends FurtherDecoratedEquiv α β

instance {α β} : CoeFun (OneMore α β) (fun _ ↦ α → β) :=
  ⟨fun f ↦ f.toFurtherDecoratedEquiv⟩

def OneMore.symm {α β : Sort _} (e : OneMore α β) :
    OneMore β α :=
  { toFurtherDecoratedEquiv := e.toFurtherDecoratedEquiv.symm }

def OneMore.Simps.apply {α β : Sort _} (e : OneMore α β) : α → β := e
def OneMore.Simps.symm_apply {α β : Sort _} (e : OneMore α β) : β → α := e.symm

initialize_simps_projections OneMore (toFun → apply, invFun → symm_apply,
  -toFurtherDecoratedEquiv, toDecoratedEquiv → to_dequiv, -to_dequiv)

@[simps] def fffoo (α : Type) : OneMore α α :=
  { toFun     := fun x ↦ x
    invFun    := fun x ↦ x
    left_inv  := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl
    P_toFun   := fun _ _ h ↦ h
    P_invFun  := fun _ _ h ↦ h
    Q_toFun   := fun y ↦ ⟨y, rfl⟩
    Q_invFun  := fun y ↦ ⟨y, rfl⟩ }

example {α : Type} (x : α) : (fffoo α).symm x = x := by dsimp

@[simps! apply to_dequiv_apply toFurtherDecoratedEquiv_apply to_dequiv]
def fffoo2 (α : Type) : OneMore α α := fffoo α

/- test the case where a projection takes additional arguments. -/
variable {ι : Type _} [DecidableEq ι] (A : ι → Type _)

structure ZeroHom (M N : Type _) [Zero M] [Zero N] where
  (toFun : M → N)
  (map_zero' : toFun 0 = 0)

structure AddHom (M N : Type _) [Add M] [Add N] where
  (toFun : M → N)
  (map_add' : ∀ x y, toFun (x + y) = toFun x + toFun y)

structure AddMonoidHom (M N : Type _) [AddMonoid M] [AddMonoid N]
  extends ZeroHom M N, AddHom M N

infixr:25 " →+ " => AddMonoidHom

instance (M N : Type _) [AddMonoid M] [AddMonoid N] : CoeFun (M →+ N) (fun _ ↦ M → N) := ⟨(·.toFun)⟩

class AddHomPlus [Add ι] [∀ i, AddCommMonoid (A i)] where
  (myMul {i} : A i →+ A i)

def AddHomPlus.Simps.apply [Add ι] [∀ i, AddCommMonoid (A i)] [AddHomPlus A] {i : ι} (x : A i) :
    A i :=
  AddHomPlus.myMul x

initialize_simps_projections AddHomPlus (myMul_toFun → apply, -myMul)

class AddHomPlus2 [Add ι] where
  (myMul {i j} : A i ≃ (A j ≃ A (i + j)))

def AddHomPlus2.Simps.mul [Add ι] [AddHomPlus2 A] {i j : ι} (x : A i) (y : A j) : A (i + j) :=
  AddHomPlus2.myMul x y

initialize_simps_projections AddHomPlus2 (-myMul, myMul_toFun_toFun → mul)

attribute [ext] Equiv'

set_option warn.classDefReducibility false in
@[simps]
def thing (h : Bool ≃ (Bool ≃ Bool)) : AddHomPlus2 (fun _ : ℕ ↦ Bool) :=
  { myMul :=
    { toFun := fun b ↦
      { toFun := h b
        invFun := (h b).symm
        left_inv := (h b).left_inv
        right_inv := (h b).right_inv }
      invFun := h.symm
      left_inv := h.left_inv -- definitional eta
      right_inv := h.right_inv } } -- definitional eta

example (h : Bool ≃ (Bool ≃ Bool)) (i j : ℕ) (b1 b2 : Bool) {x} (h2 : h b1 b2 = x) :
  @AddHomPlus2.myMul _ _ _ (thing h) i j b1 b2 = x := by
  simp only [thing_mul]
  rw [h2]

end comp_projs

section
/-! Check that the tactic also works if the elaborated type of `type` reduces to `Sort _`, but is
  not `Sort _` itself. -/
structure MyFunctor (C D : Type _) where
  (obj : C → D)
local infixr:26 " ⥤ " => MyFunctor

@[simps]
noncomputable def fooSum {I J : Type _} (C : I → Type _) {D : J → Type _} :
    (∀ i, C i) ⥤ (∀ j, D j) ⥤ (∀ s : I ⊕ J, Sum.rec C D s) :=
  { obj := fun f ↦ { obj := fun g s ↦ Sum.rec f g s }}

end

/-! Test that we deal with classes whose names are prefixes of other classes -/

class MyDiv (α : Type _) extends Div α
class MyDivInv (α : Type _) extends MyDiv α
class MyGroup (α : Type _) extends MyDivInv α
initialize_simps_projections MyGroup

/-! Test that the automatic projection module doesn't throw an error if we have a projection name
unrelated to one of the classes. -/

class MyGOne {ι} [Zero ι] (A : ι → Type _) where
  /-- The term `one` of grade 0 -/
  one : A 0

initialize_simps_projections MyGOne

class Artificial (n : Nat) where
  /-- The term `one` of grade 0 -/
  one : Nat

initialize_simps_projections Artificial


namespace UnderScoreDigit

/-!
We do not consider `field` to be a prefix of `field_1`, as the latter is often
a different field with an auto-generated name.
-/

structure Foo where
  field : Nat
  field_9 : Nat × Nat
  field_2 : Nat

@[simps field field_2 field_9_fst]
def myFoo : Foo := ⟨1, ⟨1, 1⟩, 1⟩

structure Prod (X Y : Type _) extends _root_.Prod X Y

structure Prod2 (X Y : Type _) extends toProd_1 : Prod X Y

initialize_simps_projections Prod2 (toProd → myName, toProd_1 → myOtherName)

structure Prod3 (X Y : Type _) extends toProd_1 : Prod X Y

@[simps] def foo : Prod3 Nat Nat := { fst := 1, snd := 3 }
@[simps toProd_1] def foo' : Prod3 Nat Nat := { fst := 1, snd := 3 }

end UnderScoreDigit

namespace Grind

@[simps (attr := grind =) -isSimp]
def foo := (2, 3)

example : foo.1 = 2 := by grind
example : foo.1 = 2 := by
  fail_if_success simp
  rfl

end Grind

def MyNat := Nat

def MyNat.zero : MyNat := Nat.zero

structure MyNatStruct where
  n : MyNat

@[simps]
def zero : MyNatStruct where
  n := MyNat.zero

-- Verify that the equality type is not reduced from `MyNat` to `Nat`:
set_option pp.explicit true in
/-- info: zero_n : @Eq MyNat zero.n MyNat.zero -/
#guard_msgs in
#check zero_n
