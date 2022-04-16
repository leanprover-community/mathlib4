import Mathlib.Algebra.Group.ToAdditiveInstances
open Lean

-- work in a namespace so that it doesn't matter if names clash
set_option trace.to_additive true
set_option trace.to_additive.replace true
@[to_additive bar0]
def foo0 {α} [Mul α] [One α] (x y : α) : α := x * y * 1

theorem foo0_works : bar0 3 4 = 7 := by decide

class my_has_pow (α : Type u) (β : Type v) :=
(pow : α → β → α)

class my_has_scalar (M : Type u) (α : Type v) := (smul : M → α → α)

attribute [to_additive_reorder 1] my_has_pow
attribute [to_additive_reorder 1 4] my_has_pow.pow
attribute [to_additive test.my_has_scalar] my_has_pow
attribute [to_additive test.my_has_scalar.smul] my_has_pow.pow

-- set_option pp.universes true
-- set_option pp.implicit true
-- set_option pp.notation false

infix " ^ ":80 => my_has_pow.pow

@[to_additive bar1]
def foo1 {α} [my_has_pow α ℕ] (x : α) (n : ℕ) : α := @my_has_pow.pow α ℕ _ x n

instance dummy : my_has_pow ℕ $ plift ℤ := ⟨fun _ _ => 0⟩

set_option pp.universes true
@[to_additive bar2]
def foo2 {α} [my_has_pow α ℕ] (x : α) (n : ℕ) (m : plift ℤ) : α := x ^ (n ^ m)

@[to_additive bar3]
def foo3 {α} [my_has_pow α ℕ] (x : α) : ℕ → α := @my_has_pow.pow α ℕ _ x

@[to_additive bar4]
def {a b} foo4 {α : Type a} : Type b → Type (max a b) := @my_has_pow α

@[to_additive bar4_test]
lemma foo4_test {α β : Type*} : @foo4 α β = @my_has_pow α β := rfl

@[to_additive bar5]
def foo5 {α} [my_has_pow α ℕ] [my_has_pow ℕ ℤ] : true := trivial

@[to_additive bar6]
def foo6 {α} [my_has_pow α ℕ] : α → ℕ → α := @my_has_pow.pow α ℕ _

@[to_additive bar7]
def foo7 := @my_has_pow.pow

open tactic
/- test the eta-expansion applied on `foo6`. -/
run_cmd do
env ← get_env,
reorder ← to_additive.reorder_attr.get_cache,
d ← get_decl `test.foo6,
let e := d.value.eta_expand env reorder,
let t := d.type.eta_expand env reorder,
let decl := declaration.defn `test.barr6 d.univ_params t e d.reducibility_hints d.is_trusted,
add_decl decl,
skip

/-! Test the namespace bug (#8733). This code should *not* generate a lemma
  `add_some_def.in_namespace`. -/
def some_def.in_namespace : bool := ff

def some_def {α : Type*} [has_mul α] (x : α) : α :=
if some_def.in_namespace then x * x else x

-- cannot apply `@[to_additive]` to `some_def` if `some_def.in_namespace` doesn't have the attribute
run_cmd do
  dict ← to_additive.aux_attr.get_cache,
  success_if_fail
    (transform_decl_with_prefix_dict dict ff tt mk_name_map mk_name_map mk_name_map
      `some_def `add_some_def []),
  skip

attribute [to_additive some_other_name] some_def.in_namespace
attribute [to_additive add_some_def] some_def

run_cmd success_if_fail (get_decl `add_some_def.in_namespace)

example : (add_units.mk_of_add_eq_zero 0 0 (by simp) : ℕ)
        = (add_units.mk_of_add_eq_zero 0 0 (by simp) : ℕ) :=
by norm_cast

-- TODO test alias

-- test @[to_additive_relevant_args] and to_additive.first_multiplicative_arg

-- first multiplicative argument: f
def foo_mul {I J K : Type*} (n : ℕ) {f : I → Type*} (L : Type*) [∀ i (n : ℕ), bool → has_one (f i)]
  [has_add I] [has_mul L] : true :=
trivial

@[to_additive]
instance pi.has_one {I : Type*} {f : I → Type*} [∀ i, has_one $ f i] : has_one (Π i : I, f i) :=
⟨λ _, 1⟩

run_cmd do
  n ← to_additive.first_multiplicative_arg `test.pi.has_one,
  guard $ n = 2,
  n ← to_additive.first_multiplicative_arg `test.foo_mul,
  guard $ n = 5

@[to_additive]
def nat_pi_has_one {α : Type*} [has_one α] : has_one (Π x : ℕ, α) := by apply_instance

@[to_additive]
def pi_nat_has_one {I : Type*} : has_one (Π x : I, ℕ) := by apply_instance

end test
