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


initialize_simps_projections? Something

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

infix:25 (priority := high) " ≃ " => Equiv'

-- macro "simps?" rest:simpsArgsRest : attr => `(attr| simps ? $rest)
-- local infix (name := equiv') ` ≃ `:25 := equiv'

/- Since `prod` and `pprod` are a special case for `@[simps]`, we define a new structure to test
  the basic functionality.-/
structure my_prod (α β : Type _) := (fst : α) (snd : β)

def myprod.map {α α' β β'} (f : α → α') (g : β → β') (x : my_prod α β) : my_prod α' β' :=
⟨f x.1, g x.2⟩

namespace foo
@[simps] protected def rfl {α} : α ≃ α :=
⟨id, λ x => x, λ _ => rfl, λ _ => rfl⟩

/- simps adds declarations -/
run_cmd liftTermElabM <| do
  let e ← getEnv
  guard <| (e.find? `foo.rfl_toFun).isSome
  guard <| (e.find? `foo.rfl_invFun).isSome
  guard <| (e.find? `foo.rfl_left_inv).isNone
  guard <| (e.find? `foo.rfl_right_inv).isNone

example (n : ℕ) : foo.rfl.toFun n = n := by rw [foo.rfl_toFun, id]
example (n : ℕ) : foo.rfl.invFun n = n := by rw [foo.rfl_invFun]

/- the declarations are `simp` lemmas -/
@[simps] def foo : ℕ × ℤ := (1, 2)

example : foo.1 = 1 := by simp -- note: in Lean 4 this succeeds without `@[simps]`
example : foo.2 = 2 := by simp
example : foo.1 = 1 := by dsimp <;> rfl -- check that dsimp also unfolds
example : foo.2 = 2 := by dsimp <;> rfl
example {α} (x : α) : foo.rfl.toFun x = x := by simp
example {α} (x : α) : foo.rfl.invFun x = x := by simp
example {α} (x : α) : foo.rfl.toFun = @id α := by { successIfFail {simp}, refl }

/- check some failures -/
def bar1 : ℕ := 1 -- type is not a structure
noncomputable def bar2 {α} : α ≃ α :=
Classical.choice ⟨foo.rfl⟩

run_cmd liftCoreM <| do
  -- _ ← simpsTac `foo.bar1
  -- successIfFailWithMsg (simpsTac `foo.bar1)
  --   "Invalid `simps` attribute. Target nat is not a structure"
  -- _ ← simpsTac `foo.bar2
  -- successIfFailWithMsg (simpsTac `foo.bar2)
  --   "Invalid `simps` attribute. The body is not a constructor application:
  -- Classical.choice bar2._proof_1"
  let e ← getEnv
  let nm := `foo.bar1
  let d := (e.find? nm).get!
  let lhs : Expr := mkConst d.name (d.levelParams.map Level.param)
  MetaM.run' <| simpsAddProjections e nm d.type lhs d.value! #[] d.levelParams false {} [] []

#exit
/- test that if a non-constructor is given as definition, then
  `{rhs_md := semireducible, simp_rhs := true}` is applied automatically. -/
@[simps] def rfl2 {α} : α ≃ α := foo.rfl

example {α} (x : α) : rfl2.toFun x = x ∧ rfl2.invFun x = x :=
begin
  dsimp only [rfl2_toFun, rfl2_invFun]
  guard_target (x = x ∧ x = x)
  exact ⟨rfl, rfl⟩
end

/- test `fully_applied` option -/

@[simps {fully_applied := false}] def rfl3 {α} : α ≃ α := ⟨id, λ x => x, λ x => rfl, λ x => rfl⟩

end foo

/- we reduce the type when applying [simps] -/
def my_equiv := equiv'
@[simps] def baz : my_equiv ℕ ℕ := ⟨id, λ x => x, λ x => rfl, λ x => rfl⟩

/- test name clashes -/
def name_clash_fst := 1
def name_clash_snd := 1
def name_clash_snd_2 := 1
@[simps] def name_clash := (2, 3)

run_cmd liftTermElabM <| do
  let e ← getEnv
  e.find? `name_clash_fst_2
  e.find? `name_clash_snd_3

/- check projections for nested structures -/

namespace count_nested
@[simps {attrs := [`simp, `norm]}] def nested1 : my_prod ℕ $ my_prod ℤ ℕ :=
⟨2, -1, 1⟩

@[simps {attrs := []}] def nested2 : ℕ × my_prod ℕ ℕ :=
⟨2, myprod.map nat.succ nat.pred ⟨1, 2⟩⟩

end count_nested

run_cmd liftTermElabM <| do
  let e ← getEnv
  e.find? `count_nested.nested1_fst
  e.find? `count_nested.nested1_snd_fst
  e.find? `count_nested.nested1_snd_snd
  e.find? `count_nested.nested2_fst
  e.find? `count_nested.nested2_snd
  is_simp_lemma `count_nested.nested1_fst >>= λ b => guard b, -- simp attribute is global
  is_simp_lemma `count_nested.nested2_fst >>= λ b => guard $ ¬b, --lemmas_only doesn't add simp lemma
  guard $ 7 = e.fold 0 -- there are no other lemmas generated
    (λ d n, n + if d.to_name.components.init.ilast = `count_nested then 1 else 0)

-- testing with arguments
@[simps] def bar {α : Type _} (n m : ℕ) : ℕ × ℤ :=
⟨n - m, n + m⟩

structure equiv_plus_data (α β) extends α ≃ β :=
(P : (α → β) → Prop)
(data : P toFun)

structure automorphism_plus_data α extends α ⊕ α ≃ α ⊕ α :=
(P : (α ⊕ α → α ⊕ α) → Prop)
(data : P toFun)
(extra : bool → my_prod ℕ ℕ)

@[simps]
def refl_with_data {α} : equiv_plus_data α α :=
{ P := λ f => f = id
  data := rfl
  ..foo.rfl }

@[simps]
def refl_with_data' {α} : equiv_plus_data α α :=
{ P := λ f => f = id
  data := rfl
  to_equiv' := foo.rfl }

/- test whether eta expansions are reduced correctly -/
@[simps]
def test {α} : automorphism_plus_data α :=
{ P := λ f => f = id
  data := rfl
  extra := λ b => ⟨(⟨3, 5⟩ : my_prod _ _).1, (⟨3, 5⟩ : my_prod _ _).2⟩
  ..foo.rfl }

/- test whether this is indeed rejected as a valid eta expansion -/
@[simps]
def test_sneaky {α} : automorphism_plus_data α :=
{ P := λ f => f = id
  data := rfl
  extra := λ b => ⟨(3,5).1,(3,5).2⟩
  ..foo.rfl }

run_cmd liftTermElabM <| do
  let e ← getEnv
  e.find? `refl_with_data_to_equiv'
  e.find? `refl_with_data'_to_equiv'
  e.find? `test_extra
  e.find? `test_sneaky_extra_fst
  successIfFail (e.find? `refl_with_data_to_equiv_toFun)
  successIfFail (e.find? `refl_with_data'_to_equiv_toFun)
  successIfFail (e.find? `test_extra_fst)
  successIfFail (e.find? `test_sneaky_extra)

structure partially_applied_str :=
(data : ℕ → my_prod ℕ ℕ)

/- if we have a partially applied constructor, we treat it as if it were eta-expanded -/
@[simps]
def partially_applied_term : partially_applied_str := ⟨my_prod.mk 3⟩

@[simps]
def another_term : partially_applied_str := ⟨λ n => ⟨n + 1, n + 2⟩⟩

run_cmd liftTermElabM <| do
  let e ← getEnv
  e.find? `partially_applied_term_data_fst
  e.find? `partially_applied_term_data_snd

structure very_partially_applied_str :=
(data : ∀β, ℕ → β → my_prod ℕ β)

/- if we have a partially applied constructor, we treat it as if it were eta-expanded.
  (this is not very useful, and we could remove this behavior if convenient) -/
@[simps]
def very_partially_applied_term : very_partially_applied_str := ⟨@my_prod.mk ℕ⟩

run_cmd liftTermElabM <| do
  let e ← getEnv
  e.find? `very_partially_applied_term_data_fst
  e.find? `very_partially_applied_term_data_snd

@[simps] def let1 : ℕ × ℤ :=
let n := 3 in ⟨n + 4, 5⟩

@[simps] def let2 : ℕ × ℤ :=
let n := 3, m := 4 in let k := 5 in ⟨n + m, k⟩

@[simps] def let3 : ℕ → ℕ × ℤ :=
λ n => let m := 4, k := 5 in ⟨n + m, k⟩

@[simps] def let4 : ℕ → ℕ × ℤ :=
let m := 4, k := 5 in λ n => ⟨n + m, k⟩

run_cmd liftTermElabM <| do
  let e ← getEnv
  e.find? `let1_fst, e.find? `let2_fst, e.find? `let3_fst, e.find? `let4_fst
  e.find? `let1_snd, e.find? `let2_snd, e.find? `let3_snd, e.find? `let4_snd


namespace specify
@[simps fst] def specify1 : ℕ × ℕ × ℕ := (1, 2, 3)
@[simps snd] def specify2 : ℕ × ℕ × ℕ := (1, 2, 3)
@[simps snd_fst] def specify3 : ℕ × ℕ × ℕ := (1, 2, 3)
@[simps snd snd_snd snd_snd] def specify4 : ℕ × ℕ × ℕ := (1, 2, 3) -- last argument is ignored
@[simps] noncomputable def specify5 : ℕ × ℕ × ℕ := (1, Classical.choice ⟨(2, 3)⟩)
end specify

run_cmd liftTermElabM <| do
  let e ← getEnv
  e.find? `specify.specify1_fst, e.find? `specify.specify2_snd
  e.find? `specify.specify3_snd_fst, e.find? `specify.specify4_snd_snd, e.find? `specify.specify4_snd
  e.find? `specify.specify5_fst, e.find? `specify.specify5_snd
  guard $ 12 = e.fold 0 -- there are no other lemmas generated
    (λ d n, n + if d.to_name.components.init.ilast = `specify then 1 else 0)
  successIfFailWithMsg (simpsTac `specify.specify1 {} ["fst_fst"])
    "Invalid simp lemma specify.specify1_fst_fst.
Projection fst doesn't exist, because target is not a structure."
  successIfFailWithMsg (simpsTac `specify.specify1 {} ["foo_fst"])
    "Invalid simp lemma specify.specify1_foo_fst. Structure prod does not have projection foo.
The known projections are:
  [fst, snd]
You can also see this information by running
  `initialize_simps_projections? prod`.
Note: these projection names might not correspond to the projection names of the structure."
  successIfFailWithMsg (simpsTac `specify.specify1 {} ["snd_bar"])
    "Invalid simp lemma specify.specify1_snd_bar. Structure prod does not have projection bar.
The known projections are:
  [fst, snd]
You can also see this information by running
  `initialize_simps_projections? prod`.
Note: these projection names might not correspond to the projection names of the structure."
  successIfFailWithMsg (simpsTac `specify.specify5 {} ["snd_snd"])
    "Invalid simp lemma specify.specify5_snd_snd.
The given definition is not a constructor application:
  Classical.choice specify.specify5._proof_1"


/- We also eta-reduce if we explicitly specify the projection. -/
attribute [simps extra] test
run_cmd liftTermElabM <| do
  let e ← getEnv
  d1 ← e.find? `test_extra
  d2 ← e.find? `test_extra_2
  guard $ d1.type =ₐ d2.type
  skip

/- check simp_rhs option -/
@[simps {simp_rhs := true}] def equiv'.trans {α β γ} (f : α ≃ β) (g : β ≃ γ) : α ≃ γ :=
⟨g.toFun ∘ f.toFun, f.invFun ∘ g.invFun
  by { intro x, simp [equiv'.left_inv _ _] }, by { intro x, simp [equiv'.right_inv _ _] }⟩


example {α β γ : Type} (f : α ≃ β) (g : β ≃ γ) (x : α) :
  (f.trans g).toFun x = (f.trans g).toFun x :=
begin
  dsimp only [equiv'.trans_toFun]
  guard_target g.toFun (f.toFun x) = g.toFun (f.toFun x)
  refl
end

local attribute [simp] nat.zero_add nat.one_mul nat.mul_one
@[simps {simp_rhs := true}] def my_nat_equiv : ℕ ≃ ℕ :=
⟨λ n => 0 + n, λ n => 1 * n * 1, by { intro n, simp }, by { intro n, simp }⟩

run_cmd successIfFail (has_attribute `_refl_lemma `my_nat_equiv'_toFun) >>
  has_attribute `_refl_lemma `equiv'.trans_toFun

example (n : ℕ) : my_nat_equiv.toFun (my_nat_equiv.toFun $ my_nat_equiv.invFun n) = n :=
by { successIfFail { refl }, simp only [my_nat_equiv_toFun, my_nat_equiv_invFun] }

@[simps {simp_rhs := true}] def succeed_without_simplification_possible : ℕ ≃ ℕ :=
⟨λ n => n, λ n => n, by { intro n, refl }, by { intro n, refl }⟩


/- test that we don't recursively take projections of `prod` and `pprod` -/
@[simps] def pprod_equiv_prod : pprod ℕ ℕ ≃ ℕ × ℕ :=
{ toFun := λ x => ⟨x.1, x.2⟩
  invFun := λ x => ⟨x.1, x.2⟩
  left_inv := λ ⟨x, y⟩, rfl
  right_inv := λ ⟨x, y⟩, rfl }

run_cmd liftTermElabM <| do
  let e ← getEnv
  e.find? `pprod_equiv_prod_toFun
  e.find? `pprod_equiv_prod_invFun

attribute [simps toFun_fst invFun_snd] pprod_equiv_prod

run_cmd liftTermElabM <| do
  let e ← getEnv
  e.find? `pprod_equiv_prod_toFun_fst
  e.find? `pprod_equiv_prod_invFun_snd

-- we can disable this behavior with the option `not_recursive`.
@[simps {not_recursive := []}] def pprod_equiv_prod2 : pprod ℕ ℕ ≃ ℕ × ℕ :=
pprod_equiv_prod

run_cmd liftTermElabM <| do
  let e ← getEnv
  e.find? `pprod_equiv_prod2_toFun_fst
  e.find? `pprod_equiv_prod2_toFun_snd
  e.find? `pprod_equiv_prod2_invFun_fst
  e.find? `pprod_equiv_prod2_invFun_snd

/- Tests with universe levels -/
class has_hom (obj : Type u) : Type (max u (v+1)) :=
(hom : obj → obj → Type v)

infixr ` ⟶ `:10 := has_hom.hom -- type as \h

class category_struct (obj : Type u) extends has_hom.{v} obj : Type (max u (v+1)) :=
(id       : Π X : obj, hom X X)
(comp     : Π {X Y Z : obj}, (X ⟶ Y) → (Y ⟶ Z) → (X ⟶ Z))

notation `𝟙` := category_struct.id -- type as \b1
infixr ` ≫ `:80 := category_struct.comp -- type as \gg

@[simps] instance types : category_struct (Type u) :=
{ hom     := λ a b, (a → b)
  id      := λ a => id
  comp    := λ _ _ _ f g, g ∘ f }

example (X : Type u) : (X ⟶ X) = (X → X) := by simp
example (X : Type u) : 𝟙 X = (λ x => x) := by { funext, simp }
example (X Y Z : Type u) (f : X ⟶ Y) (g : Y ⟶ Z) : f ≫ g = g ∘ f := by { funext, simp }

namespace coercing

structure foo_str :=
 (c : Type)
 (x : c)

instance : has_coe_to_sort foo_str Type := ⟨foo_str.c⟩

@[simps] def foo : foo_str := ⟨ℕ, 3⟩
@[simps] def foo2 : foo_str := ⟨ℕ, 34⟩

example : ↥foo = ℕ := by simp only [foo_c]
example : foo.x = (3 : ℕ) := by simp only [foo_x]

structure voo_str (n : ℕ) :=
 (c : Type)
 (x : c)

instance has_coe_voo_str (n : ℕ) : has_coe_to_sort (voo_str n) Type := ⟨voo_str.c⟩

@[simps] def voo : voo_str 7 := ⟨ℕ, 3⟩
@[simps] def voo2 : voo_str 4 := ⟨ℕ, 34⟩

example : ↥voo = ℕ := by simp only [voo_c]
example : voo.x = (3 : ℕ) := by simp only [voo_x]

structure equiv2 (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)
(left_inv  : invFun.LeftInverse toFun)
(right_inv : invFun.RightInverse toFun)

instance {α β} : has_coe_toFun (equiv2 α β) (λ _ => α → β) := ⟨equiv2.toFun⟩

@[simps] protected def rfl2 {α} : equiv2 α α :=
⟨λ x => x, λ x => x, λ x => rfl, λ x => rfl⟩

example {α} (x : α) : coercing.rfl2 x = x := by rw [coercing.rfl2_toFun]
example {α} (x : α) : coercing.rfl2 x = x := by simp
example {α} (x : α) : coercing.rfl2.invFun x = x := by simp

@[simps] protected def equiv2.symm {α β} (f : equiv2 α β) : equiv2 β α :=
⟨f.invFun, f, f.right_inv, f.left_inv⟩

@[simps] protected def equiv2.symm2 {α β} (f : equiv2 α β) : equiv2 β α :=
⟨f.invFun, f.toFun, f.right_inv, f.left_inv⟩

@[simps {fully_applied := false}] protected def equiv2.symm3 {α β} (f : equiv2 α β) : equiv2 β α :=
⟨f.invFun, f, f.right_inv, f.left_inv⟩

example {α β} (f : equiv2 α β) (y : β) : f.symm y = f.invFun y := by simp
example {α β} (f : equiv2 α β) (x : α) : f.symm.invFun x = f x := by simp

example {α β} (f : equiv2 α β) : f.symm.invFun = f := by { successIfFail {simp}, refl }
example {α β} (f : equiv2 α β) : f.symm3.invFun = f := by simp

section
set_option old_structure_cmd true
class semigroup (G : Type u) extends has_mul G :=
(mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
end

@[simps] instance {α β} [semigroup α] [semigroup β] : semigroup (α × β) :=
{ mul := λ x y, (x.1 * y.1, x.2 * y.2)
  mul_assoc := by { intros, simp only [semigroup.mul_assoc], refl } }

example {α β} [semigroup α] [semigroup β] (x y : α × β) : x * y = (x.1 * y.1, x.2 * y.2) :=
by simp
example {α β} [semigroup α] [semigroup β] (x y : α × β) : (x * y).1 = x.1 * y.1 := by simp

structure Semigroup :=
  (G : Type _)
  (op : G → G → G)
  (infix (name := op) ` * ` := op)
  (op_assoc : ∀ (x y z : G), (x * y) * z = x * (y * z))

namespace Group

instance : has_coe_to_sort Semigroup Type _ := ⟨Semigroup.G⟩
-- We could try to generate lemmas with this `has_mul` instance, but it is unused in mathlib.
-- Therefore, this is ignored.
instance (G : Semigroup) : has_mul G := ⟨G.op⟩

@[simps] def prod_Semigroup (G H : Semigroup) : Semigroup :=
{ G := G × H
  op := λ x y, (x.1 * y.1, x.2 * y.2)
  op_assoc := by { intros, dsimp [Group.has_mul], simp [Semigroup.op_assoc] }}


end Group

section
set_option old_structure_cmd true
class extending_stuff (G : Type u) extends has_mul G, has_zero G, has_neg G, has_subset G :=
(new_axiom : ∀ x : G, x * - 0 ⊆ - x)
end

@[simps] def bar : extending_stuff ℕ :=
{ mul := (*)
  zero := 0
  neg := nat.succ
  subset := λ x y, true
  new_axiom := λ x => trivial }

section
local attribute [instance] bar
example (x : ℕ) : x * - 0 ⊆ - x := by simp
end

class new_extending_stuff (G : Type u) extends has_mul G, has_zero G, has_neg G, has_subset G :=
(new_axiom : ∀ x : G, x * - 0 ⊆ - x)

@[simps] def new_bar : new_extending_stuff ℕ :=
{ mul := (*)
  zero := 0
  neg := nat.succ
  subset := λ x y, true
  new_axiom := λ x => trivial }

section
local attribute [instance] new_bar
example (x : ℕ) : x * - 0 ⊆ - x := by simp
end


end coercing

namespace manual_coercion

structure equiv (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)

local infix (name := equiv) ` ≃ `:25 := manual_coercion.equiv

variables {α β γ : Sort _}

instance : has_coe_toFun (α ≃ β) (λ _ => α → β) := ⟨equiv.toFun⟩

def equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
def equiv.simps.invFun (e : α ≃ β) : β → α := e.symm

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[simps {simp_rhs := true}] protected def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : γ) : (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
by simp only [equiv.trans_invFun]

end manual_coercion

namespace faulty_manual_coercion

structure equiv (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)

local infix (name := equiv) ` ≃ `:25 := faulty_manual_coercion.equiv

variables {α β γ : Sort _}

/-- See Note [custom simps projection] -/
noncomputable def equiv.simps.invFun (e : α ≃ β) : β → α := Classical.choice ⟨e.invFun⟩

run_cmd liftTermElabM <| do let e ← getEnv, successIfFailWithMsg (simps_get_raw_projections e `faulty_manual_coercion.equiv)
"Invalid custom projection:
  λ {α : Sort u_1} {β : Sort u_2} (e : α ≃ β), Classical.choice _
Expression is not definitionally equal to
  λ (α : Sort u_1) (β : Sort u_2) (x : α ≃ β), x.invFun"

end faulty_manual_coercion

namespace manual_initialize
/- defining a manual coercion. -/
variables {α β γ : Sort _}

structure equiv (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)

local infix (name := equiv) ` ≃ `:25 := manual_initialize.equiv

instance : has_coe_toFun (α ≃ β) (λ _ => α → β) := ⟨equiv.toFun⟩

def equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
-- test: intentionally using different unvierse levels for equiv.symm than for equiv
def equiv.simps.invFun (e : α ≃ β) : β → α := e.symm

initialize_simps_projections equiv

run_cmd has_attribute `_simps_str `manual_initialize.equiv

/-- Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`. -/
@[simps {simp_rhs := true}] protected def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

end manual_initialize

namespace faulty_universes

variables {α β γ : Sort _}

structure equiv (α : Sort u) (β : Sort v) :=
(toFun    : α → β)
(invFun   : β → α)

local infix (name := equiv) ` ≃ `:25 := faulty_universes.equiv

instance : has_coe_toFun (α ≃ β) (λ _ => α → β) := ⟨equiv.toFun⟩

def equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
-- test: intentionally using different names for the universe variables for equiv.symm than for
-- equiv
def equiv.simps.invFun {α : Type u} {β : Type v} (e : α ≃ β) : β → α := e.symm

run_cmd liftTermElabM <| do let e ← getEnv
  successIfFailWithMsg (simps_get_raw_projections e `faulty_universes.equiv)
"Invalid custom projection:
  λ {α : Type u} {β : Type v} (e : α ≃ β), ⇑(e.symm)
Expression has different type than faulty_universes.equiv.invFun. Given type:
  Π {α : Type u} {β : Type v} (e : α ≃ β), (λ (_x : β ≃ α), β → α) e.symm
Expected type:
  Π (α : Sort u) (β : Sort v), α ≃ β → β → α"

end faulty_universes

namespace manual_universes

variables {α β γ : Sort _}

structure equiv (α : Sort u) (β : Sort v) :=
(toFun    : α → β)
(invFun   : β → α)

local infix (name := equiv) ` ≃ `:25 := manual_universes.equiv

instance : has_coe_toFun (α ≃ β) (λ _ => α → β) := ⟨equiv.toFun⟩

def equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
-- test: intentionally using different unvierse levels for equiv.symm than for equiv
def equiv.simps.invFun {α : Sort w} {β : Sort u} (e : α ≃ β) : β → α := e.symm

-- check whether we can generate custom projections even if the universe names don't match
initialize_simps_projections equiv

end manual_universes

namespace manual_projection_names

structure equiv (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)

local infix (name := equiv) ` ≃ `:25 := manual_projection_names.equiv

variables {α β γ : Sort _}

instance : has_coe_toFun (α ≃ β) (λ _ => α → β) := ⟨equiv.toFun⟩

def equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
def equiv.simps.symm_apply (e : α ≃ β) : β → α := e.symm

initialize_simps_projections equiv (toFun → apply, invFun → symm_apply)

run_cmd liftTermElabM <| do
  let e ← getEnv
  data ← simps_get_raw_projections e `manual_projection_names.equiv
  guard $ data.2.map projection_data.name = [`apply, `symm_apply]

@[simps {simp_rhs := true}] protected def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : α) : (e₁.trans e₂) x = e₂ (e₁ x) :=
by simp only [equiv.trans_apply]

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : γ) : (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
by simp only [equiv.trans_symm_apply]

-- the new projection names are parsed correctly (the old projection names won't work anymore)
@[simps apply symm_apply] protected def equiv.trans2 (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩


end manual_projection_names

namespace prefix_projection_names

structure equiv (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)

local infix (name := equiv) ` ≃ `:25 := prefix_projection_names.equiv

variables {α β γ : Sort _}

instance : has_coe_toFun (α ≃ β) (λ _ => α → β) := ⟨equiv.toFun⟩

def equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

/-- See Note [custom simps projection] -/
def equiv.simps.symm_apply (e : α ≃ β) : β → α := e.symm
initialize_simps_projections equiv (toFun → coe as_prefix, invFun → symm_apply)

run_cmd liftTermElabM <| do
  let e ← getEnv
  data ← simps_get_raw_projections e `prefix_projection_names.equiv
  guard $ data.2.map projection_data.name = [`coe, `symm_apply]
  guard $ data.2.map projection_data.is_prefix = [tt, false]

@[simps {simp_rhs := true}] protected def equiv.trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

example (e₁ : α ≃ β) (e₂ : β ≃ γ) (x : α) : (e₁.trans e₂) x = e₂ (e₁ x) :=
by simp only [equiv.coe_trans]

-- the new projection names are parsed correctly
@[simps coe symm_apply] protected def equiv.trans2 (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=
⟨e₂ ∘ e₁, e₁.symm ∘ e₂.symm⟩

-- it interacts somewhat well with multiple projections (though the generated name is not great)
@[simps snd_coe_fst] def foo {α β γ δ : Type _} (x : α) (e₁ : α ≃ β) (e₂ : γ ≃ δ) :
  α × (α × γ ≃ β × δ) :=
⟨x, prod.map e₁ e₂, prod.map e₁.symm e₂.symm⟩

example {α β γ δ : Type _} (x : α) (e₁ : α ≃ β) (e₂ : γ ≃ δ) (z : α × γ) :
  ((foo x e₁ e₂).2 z).1 = e₁ z.1 :=
by simp only [coe_foo_snd_fst]

end prefix_projection_names


-- test transparency setting
structure set_plus (α : Type) :=
(s : set α)
(x : α)
(h : x ∈ s)

@[simps] def nat_set_plus : set_plus ℕ := ⟨set.univ, 1, trivial⟩

example : nat_set_plus.s = set.univ :=
begin
  dsimp only [nat_set_plus_s]
  guard_target @set.univ ℕ = set.univ
  refl
end

@[simps {type_md := semireducible}] def nat_set_plus2 : set_plus ℕ := ⟨set.univ, 1, trivial⟩

example : nat_set_plus2.s = set.univ :=
begin
  successIfFail { dsimp only [nat_set_plus2_s] }, refl
end

@[simps {rhs_md := semireducible}] def nat_set_plus3 : set_plus ℕ := nat_set_plus

example : nat_set_plus3.s = set.univ :=
begin
  dsimp only [nat_set_plus3_s]
  guard_target @set.univ ℕ = set.univ
  refl
end

namespace nested_non_fully_applied

structure equiv (α : Sort _) (β : Sort _) :=
(toFun    : α → β)
(invFun   : β → α)

local infix (name := equiv) ` ≃ `:25 := nested_non_fully_applied.equiv

variables {α β γ : Sort _}

@[simps] def equiv.symm (e : α ≃ β) : β ≃ α := ⟨e.invFun, e.toFun⟩

@[simps {rhs_md := semireducible, fully_applied := false}] def equiv.symm2 : (α ≃ β) ≃ (β ≃ α) :=
⟨equiv.symm, equiv.symm⟩

example (e : α ≃ β) : (equiv.symm2.invFun e).toFun = e.invFun :=
begin
  dsimp only [equiv.symm2_invFun_toFun]
  guard_target e.invFun = e.invFun
  refl
end

/- do not prematurely unfold `equiv.symm`, unless necessary -/
@[simps toFun toFun_toFun {rhs_md := semireducible}] def equiv.symm3 : (α ≃ β) ≃ (β ≃ α) :=
equiv.symm2

example (e : α ≃ β) (y : β) : (equiv.symm3.toFun e).toFun y = e.invFun y ∧
  (equiv.symm3.toFun e).toFun y = e.invFun y :=
begin
  split
  { dsimp only [equiv.symm3_toFun], guard_target e.symm.toFun y = e.invFun y, refl }
  { dsimp only [equiv.symm3_toFun_toFun], guard_target e.invFun y = e.invFun y, refl }
end

end nested_non_fully_applied

-- test that type classes which are props work
class prop_class (n : ℕ) : Prop :=
(has_true : true)

instance has_prop_class (n : ℕ) : prop_class n := ⟨trivial⟩

structure needs_prop_class (n : ℕ) [prop_class n] :=
(t : true)

@[simps] def test_prop_class : needs_prop_class 1 :=
{ t := trivial }

/- check that when the coercion is given in eta-expanded form, we can also find the coercion. -/
structure alg_hom (R A B : Type _) :=
(toFun : A → B)

instance (R A B : Type _) : has_coe_toFun (alg_hom R A B) (λ _ => A → B) := ⟨λ f => f.toFun⟩

@[simps] def my_alg_hom : alg_hom unit bool bool :=
{ toFun := id }

example (x : bool) : my_alg_hom x = id x := by simp only [my_alg_hom_toFun]

structure ring_hom (A B : Type _) :=
(toFun : A → B)

instance (A B : Type _) : has_coe_toFun (ring_hom A B) (λ _ => A → B) := ⟨λ f => f.toFun⟩

@[simps] def my_ring_hom : ring_hom bool bool :=
{ toFun := id }

example (x : bool) : my_ring_hom x = id x := by simp only [my_ring_hom_toFun]

/- check interaction with the `@[to_additive]` attribute -/

@[to_additive, simps]
instance {M N} [has_mul M] [has_mul N] : has_mul (M × N) := ⟨λ p q, ⟨p.1 * q.1, p.2 * q.2⟩⟩

run_cmd liftTermElabM <| do
  get_decl `prod.has_mul_mul
  get_decl `prod.has_add_add
  has_attribute `to_additive `prod.has_mul
  has_attribute `to_additive `prod.has_mul_mul
  has_attribute `simp `prod.has_mul_mul
  has_attribute `simp `prod.has_add_add

example {M N} [has_mul M] [has_mul N] (p q : M × N) : p * q = ⟨p.1 * q.1, p.2 * q.2⟩ := by simp
example {M N} [has_add M] [has_add N] (p q : M × N) : p + q = ⟨p.1 + q.1, p.2 + q.2⟩ := by simp

/- The names of the generated simp lemmas for the additive version are not great if the definition
  had a custom additive name -/
@[to_additive my_add_instance, simps]
instance my_instance {M N} [has_one M] [has_one N] : has_one (M × N) := ⟨(1, 1)⟩

run_cmd liftTermElabM <| do
  get_decl `my_instance_one
  get_decl `my_add_instance_zero
  has_attribute `to_additive `my_instance
  has_attribute `to_additive `my_instance_one
  has_attribute `simp `my_instance_one
  has_attribute `simp `my_add_instance_zero

example {M N} [has_one M] [has_one N] : (1 : M × N) = ⟨1, 1⟩ := by simp
example {M N} [has_zero M] [has_zero N] : (0 : M × N) = ⟨0, 0⟩ := by simp

section
/-! Test `dsimp, simp` with the option `simp_rhs` -/

local attribute [simp] nat.add

structure my_type :=
(A : Type)

@[simps {simp_rhs := true}] def my_type_def : my_type := ⟨{ x : fin (nat.add 3 0) // 1 + 1 = 2 }⟩

example (h : false) (x y : { x : fin (nat.add 3 0) // 1 + 1 = 2 }) : my_type_def.A = unit :=
begin
  simp only [my_type_def_A]
  guard_target ({ x : fin 3 // true } = unit)
  /- note: calling only one of `simp` or `dsimp` does not produce the current target
  as the following tests show. -/
  successIfFail { guard_hyp x : { x : fin 3 // true } }
  dsimp at x
  successIfFail { guard_hyp x : { x : fin 3 // true } }
  simp at y
  successIfFail { guard_hyp y : { x : fin 3 // true } }
  simp at x, dsimp at y
  guard_hyp x : { x : fin 3 // true }
  guard_hyp y : { x : fin 3 // true }
  contradiction
end

/- Test that `to_additive` copies the `@[_refl_lemma]` attribute correctly -/
@[to_additive, simps]
def monoid_hom.my_comp {M N P : Type _} [mul_one_class M] [mul_one_class N] [mul_one_class P]
  (hnp : N →* P) (hmn : M →* N) : M →* P :=
{ toFun := hnp ∘ hmn, map_one' := by simp, map_mul' := by simp, }

-- `simps` adds the `_refl_lemma` attribute to `monoid_hom.my_comp_apply`
example {M N P : Type _} [mul_one_class M] [mul_one_class N] [mul_one_class P]
  (hnp : N →* P) (hmn : M →* N) (m : M) : hnp.my_comp hmn m = hnp (hmn m) :=
by { dsimp, guard_target (hnp (hmn m) = hnp (hmn m)), refl }

-- `to_additive` adds the `_refl_lemma` attribute to `add_monoid_hom.my_comp_apply`
example {M N P : Type _} [add_zero_class M] [add_zero_class N] [add_zero_class P]
  (hnp : N →+ P) (hmn : M →+ N) (m : M) : hnp.my_comp hmn m = hnp (hmn m) :=
by { dsimp, guard_target (hnp (hmn m) = hnp (hmn m)), refl }

-- test that `to_additive` works with a custom name
@[to_additive some_test2, simps]
def some_test1 (M : Type _) [comm_monoid M] : subtype (λ f : M, true) := ⟨1, trivial⟩

run_cmd get_decl `some_test2_coe

end

/- Test custom compositions of projections. -/

section comp_projs

instance {α β} : has_coe_toFun (α ≃ β) (λ _ => α → β) := ⟨equiv'.toFun⟩

@[simps] protected def equiv'.symm {α β} (f : α ≃ β) : β ≃ α :=
⟨f.invFun, f, f.right_inv, f.left_inv⟩

structure decorated_equiv (α : Sort _) (β : Sort _) extends equiv' α β :=
(P_toFun    : function.injective toFun )
(P_invFun   : function.injective invFun)

instance {α β} : has_coe_toFun (decorated_equiv α β) (λ _ => α → β) := ⟨λ f => f.to_equiv'⟩

def decorated_equiv.symm {α β : Sort _} (e : decorated_equiv α β) : decorated_equiv β α :=
{ to_equiv' := e.to_equiv'.symm
  P_toFun := e.P_invFun
  P_invFun := e.P_toFun }

def decorated_equiv.simps.apply {α β : Sort _} (e : decorated_equiv α β) : α → β := e
def decorated_equiv.simps.symm_apply {α β : Sort _} (e : decorated_equiv α β) : β → α := e.symm

initialize_simps_projections decorated_equiv
  (to_equiv'_toFun → apply, to_equiv'_invFun → symm_apply, -to_equiv')

@[simps] def foo (α : Type) : decorated_equiv α α :=
{ toFun    := λ x => x
  invFun   := λ x => x
  left_inv  := λ x => rfl
  right_inv := λ x => rfl
  P_toFun  := λ x y h, h
  P_invFun := λ x y h, h }

example {α : Type} (x : α) : (foo α).symm x = x :=
by { dsimp, guard_target (x = x), refl }

@[simps to_equiv' apply symm_apply] def foo2 (α : Type) : decorated_equiv α α :=
{ P_toFun  := λ x y h, h
  P_invFun := λ x y h, h, ..foo.rfl }

example {α : Type} (x : α) : (foo2 α).to_equiv' x = x :=
by { dsimp, guard_target (foo.rfl x = x), refl }

example {α : Type} (x : α) : foo2 α x = x :=
by { dsimp, guard_target (x = x), refl }

structure further_decorated_equiv (α : Sort _) (β : Sort _) extends decorated_equiv α β :=
(Q_toFun    : function.surjective toFun )
(Q_invFun   : function.surjective invFun )

instance {α β} : has_coe_toFun (further_decorated_equiv α β) (λ _ => α → β) :=
⟨λ f => f.to_decorated_equiv⟩

def further_decorated_equiv.symm {α β : Sort _} (e : further_decorated_equiv α β) :
  further_decorated_equiv β α :=
{ to_decorated_equiv := e.to_decorated_equiv.symm
  Q_toFun := e.Q_invFun
  Q_invFun := e.Q_toFun }

def further_decorated_equiv.simps.apply {α β : Sort _} (e : further_decorated_equiv α β) : α → β := e
def further_decorated_equiv.simps.symm_apply {α β : Sort _} (e : further_decorated_equiv α β) :
  β → α := e.symm

initialize_simps_projections further_decorated_equiv
  (to_decorated_equiv_to_equiv'_toFun → apply, to_decorated_equiv_to_equiv'_invFun → symm_apply
  -to_decorated_equiv, to_decorated_equiv_to_equiv' → to_equiv', -to_equiv')

@[simps] def ffoo (α : Type) : further_decorated_equiv α α :=
{ toFun    := λ x => x
  invFun   := λ x => x
  left_inv  := λ x => rfl
  right_inv := λ x => rfl
  P_toFun  := λ x y h, h
  P_invFun := λ x y h, h
  Q_toFun  := λ y => ⟨y, rfl⟩
  Q_invFun := λ y => ⟨y, rfl⟩ }

example {α : Type} (x : α) : (ffoo α).symm x = x :=
by { dsimp, guard_target (x = x), refl }

@[simps] def ffoo3 (α : Type) : further_decorated_equiv α α :=
{ Q_toFun  := λ y => ⟨y, rfl⟩, Q_invFun  := λ y => ⟨y, rfl⟩, .. foo α }

@[simps apply to_equiv'_toFun to_decorated_equiv_apply]
def ffoo4 (α : Type) : further_decorated_equiv α α :=
{ Q_toFun  := λ y => ⟨y, rfl⟩, Q_invFun  := λ y => ⟨y, rfl⟩, to_decorated_equiv := foo α }

structure one_more (α : Sort _) (β : Sort _) extends further_decorated_equiv α β

instance {α β} : has_coe_toFun (one_more α β) (λ _ => α → β) :=
⟨λ f => f.to_further_decorated_equiv⟩

def one_more.symm {α β : Sort _} (e : one_more α β) :
  one_more β α :=
{ to_further_decorated_equiv := e.to_further_decorated_equiv.symm }

def one_more.simps.apply {α β : Sort _} (e : one_more α β) : α → β := e
def one_more.simps.symm_apply {α β : Sort _} (e : one_more α β) : β → α := e.symm

initialize_simps_projections one_more
  (to_further_decorated_equiv_to_decorated_equiv_to_equiv'_toFun → apply
   to_further_decorated_equiv_to_decorated_equiv_to_equiv'_invFun → symm_apply
  -to_further_decorated_equiv, to_further_decorated_equiv_to_decorated_equiv → to_dequiv
  -to_dequiv)

@[simps] def fffoo (α : Type) : one_more α α :=
{ toFun    := λ x => x
  invFun   := λ x => x
  left_inv  := λ x => rfl
  right_inv := λ x => rfl
  P_toFun  := λ x y h, h
  P_invFun := λ x y h, h
  Q_toFun  := λ y => ⟨y, rfl⟩
  Q_invFun := λ y => ⟨y, rfl⟩ }

example {α : Type} (x : α) : (fffoo α).symm x = x :=
by { dsimp, guard_target (x = x), refl }

@[simps apply to_dequiv_apply to_further_decorated_equiv_apply to_dequiv]
def fffoo2 (α : Type) : one_more α α := fffoo α

/- test the case where a projection takes additional arguments. -/
variables {ι : Type _} [decidable_eq ι] (A : ι → Type _)

class something [has_add ι] [Π i, add_comm_monoid (A i)] :=
(mul {i} : A i →+ A i)

def something.simps.apply [has_add ι] [Π i, add_comm_monoid (A i)] [something A] {i : ι} (x : A i) :
  A i :=
something.mul ι x

initialize_simps_projections something (mul_toFun → apply, -mul)

class something2 [has_add ι] :=
(mul {i j} : A i ≃ (A j ≃ A (i + j)))

def something2.simps.mul [has_add ι] [something2 A] {i j : ι}
  (x : A i) (y : A j) : A (i + j) :=
something2.mul x y

initialize_simps_projections something2 (mul → mul', mul_toFun_toFun → mul, -mul')

attribute [ext] equiv'

@[simps]
def thing (h : bool ≃ (bool ≃ bool)) : something2 (λ x : ℕ, bool) :=
{ mul := λ i j, { toFun := λ b => { toFun := h b
  invFun := (h b).symm
  left_inv := (h b).left_inv
  right_inv := (h b).right_inv }
  invFun := h.symm
  left_inv := by { convert h.left_inv, ext x; refl }
  right_inv := by { convert h.right_inv, ext x; refl } } }

example (h : bool ≃ (bool ≃ bool)) (i j : ℕ) (b1 b2 : bool) :
  @something2.mul _ _ _ _ (thing h) i j b1 b2 = h b1 b2 :=
by simp only [thing_mul]

end comp_projs

section
/-! Check that the tactic also works if the elaborated type of `type` reduces to `Sort _`, but is
  not `Sort _` itself. -/
structure my_functor (C D : Type _) :=
(obj []    : C → D)
local infixr ` ⥤ `:26 := my_functor

@[simps]
def foo_sum {I J : Type _} (C : I → Type _) {D : J → Type _} :
  (Π i, C i) ⥤ (Π j, D j) ⥤ (Π s : I ⊕ J, sum.elim C D s) :=
{ obj := λ f => { obj := λ g s, sum.rec f g s }}

end

/- end Lean 3 test suite -/


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
-- #check Equiv.invFun_as_coe
-- #check @Equiv.invFun_as_coe
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
