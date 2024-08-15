/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Logic.Unique
import Mathlib.Tactic.Spread
import Batteries.Tactic.Classical

/-!
# Instances and theorems on pi types

This file provides instances for the typeclass defined in `Algebra.Group.Defs`. More sophisticated
instances are defined in `Algebra.Group.Pi.Lemmas` files elsewhere.

## Porting note

This file relied on the `pi_instance` tactic, which was not available at the time of porting. The
comment `--pi_instance` is inserted before all fields which were previously derived by
`pi_instance`. See this Zulip discussion:
[https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/not.20porting.20pi_instance]
-/

-- We enforce to only import `Algebra.Group.Defs` and basic logic
assert_not_exists Set.range
assert_not_exists MonoidHom
assert_not_exists MonoidWithZero
assert_not_exists DenselyOrdered

open Function

universe u v₁ v₂ v₃

variable {I : Type u}

-- The indexing type
variable {α β γ : Type*}

-- The families of types already equipped with instances
variable {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}
variable (x y : ∀ i, f i) (i : I)

namespace Pi

/-! `1`, `0`, `+`, `*`, `+ᵥ`, `•`, `^`, `-`, `⁻¹`, and `/` are defined pointwise. -/

@[to_additive]
instance instOne [∀ i, One <| f i] : One (∀ i : I, f i) :=
  ⟨fun _ => 1⟩

#adaptation_note
/--
After https://github.com/leanprover/lean4/pull/4481
the `simpNF` linter incorrectly claims this lemma can't be applied by `simp`.
-/
@[to_additive (attr := simp, nolint simpNF)]
theorem one_apply [∀ i, One <| f i] : (1 : ∀ i, f i) i = 1 :=
  rfl

@[to_additive]
theorem one_def [∀ i, One <| f i] : (1 : ∀ i, f i) = fun _ => 1 :=
  rfl

@[to_additive (attr := simp)] lemma _root_.Function.const_one [One β] : const α (1 : β) = 1 := rfl

@[to_additive (attr := simp)]
theorem one_comp [One γ] (x : α → β) : (1 : β → γ) ∘ x = 1 :=
  rfl

@[to_additive (attr := simp)]
theorem comp_one [One β] (x : β → γ) : x ∘ (1 : α → β) = const α (x 1) :=
  rfl

@[to_additive]
instance instMul [∀ i, Mul <| f i] : Mul (∀ i : I, f i) :=
  ⟨fun f g i => f i * g i⟩

@[to_additive (attr := simp)]
theorem mul_apply [∀ i, Mul <| f i] : (x * y) i = x i * y i :=
  rfl

@[to_additive]
theorem mul_def [∀ i, Mul <| f i] : x * y = fun i => x i * y i :=
  rfl

@[to_additive (attr := simp)]
lemma _root_.Function.const_mul [Mul β] (a b : β) : const α a * const α b = const α (a * b) := rfl

@[to_additive]
theorem mul_comp [Mul γ] (x y : β → γ) (z : α → β) : (x * y) ∘ z = x ∘ z * y ∘ z :=
  rfl

@[to_additive]
instance instSMul [∀ i, SMul α <| f i] : SMul α (∀ i : I, f i) :=
  ⟨fun s x => fun i => s • x i⟩

@[to_additive existing instSMul]
instance instPow [∀ i, Pow (f i) β] : Pow (∀ i, f i) β :=
  ⟨fun x b i => x i ^ b⟩

@[to_additive (attr := simp, to_additive) (reorder := 5 6) smul_apply]
theorem pow_apply [∀ i, Pow (f i) β] (x : ∀ i, f i) (b : β) (i : I) : (x ^ b) i = x i ^ b :=
  rfl

@[to_additive (attr := to_additive) (reorder := 5 6) smul_def]
theorem pow_def [∀ i, Pow (f i) β] (x : ∀ i, f i) (b : β) : x ^ b = fun i => x i ^ b :=
  rfl

@[to_additive (attr := simp, to_additive) (reorder := 2 3, 5 6) smul_const]
lemma _root_.Function.const_pow [Pow α β] (a : α) (b : β) : const I a ^ b = const I (a ^ b) := rfl

@[to_additive (attr := to_additive) (reorder := 6 7) smul_comp]
theorem pow_comp [Pow γ α] (x : β → γ) (a : α) (y : I → β) : (x ^ a) ∘ y = x ∘ y ^ a :=
  rfl

-- Use `Pi.ofNat_apply` instead

@[to_additive]
instance instInv [∀ i, Inv <| f i] : Inv (∀ i : I, f i) :=
  ⟨fun f i => (f i)⁻¹⟩

@[to_additive (attr := simp)]
theorem inv_apply [∀ i, Inv <| f i] : x⁻¹ i = (x i)⁻¹ :=
  rfl

@[to_additive]
theorem inv_def [∀ i, Inv <| f i] : x⁻¹ = fun i => (x i)⁻¹ :=
  rfl

@[to_additive]
lemma _root_.Function.const_inv [Inv β] (a : β) : (const α a)⁻¹ = const α a⁻¹ := rfl

@[to_additive]
theorem inv_comp [Inv γ] (x : β → γ) (y : α → β) : x⁻¹ ∘ y = (x ∘ y)⁻¹ :=
  rfl

@[to_additive]
instance instDiv [∀ i, Div <| f i] : Div (∀ i : I, f i) :=
  ⟨fun f g i => f i / g i⟩

@[to_additive (attr := simp)]
theorem div_apply [∀ i, Div <| f i] : (x / y) i = x i / y i :=
  rfl

@[to_additive]
theorem div_def [∀ i, Div <| f i] : x / y = fun i => x i / y i :=
  rfl

@[to_additive]
theorem div_comp [Div γ] (x y : β → γ) (z : α → β) : (x / y) ∘ z = x ∘ z / y ∘ z :=
  rfl

@[to_additive (attr := simp)]
lemma _root_.Function.const_div [Div β] (a b : β) : const α a / const α b = const α (a / b) := rfl

@[to_additive]
instance semigroup [∀ i, Semigroup (f i)] : Semigroup (∀ i, f i) where
  mul_assoc := by intros; ext; exact mul_assoc _ _ _

@[to_additive]
instance commSemigroup [∀ i, CommSemigroup (f i)] : CommSemigroup (∀ i, f i) where
  mul_comm := by intros; ext; exact mul_comm _ _

@[to_additive]
instance mulOneClass [∀ i, MulOneClass (f i)] : MulOneClass (∀ i, f i) where
  one_mul := by intros; ext; exact one_mul _
  mul_one := by intros; ext; exact mul_one _

@[to_additive]
instance invOneClass [∀ i, InvOneClass (f i)] : InvOneClass (∀ i, f i) where
  inv_one := by ext; exact inv_one

@[to_additive]
instance monoid [∀ i, Monoid (f i)] : Monoid (∀ i, f i) where
  __ := semigroup
  __ := mulOneClass
  npow := fun n x i => x i ^ n
  npow_zero := by intros; ext; exact Monoid.npow_zero _
  npow_succ := by intros; ext; exact Monoid.npow_succ _ _

@[to_additive]
instance commMonoid [∀ i, CommMonoid (f i)] : CommMonoid (∀ i, f i) :=
  { monoid, commSemigroup with }

@[to_additive Pi.subNegMonoid]
instance divInvMonoid [∀ i, DivInvMonoid (f i)] : DivInvMonoid (∀ i, f i) where
  zpow := fun z x i => x i ^ z
  div_eq_mul_inv := by intros; ext; exact div_eq_mul_inv _ _
  zpow_zero' := by intros; ext; exact DivInvMonoid.zpow_zero' _
  zpow_succ' := by intros; ext; exact DivInvMonoid.zpow_succ' _ _
  zpow_neg' := by intros; ext; exact DivInvMonoid.zpow_neg' _ _

@[to_additive Pi.subNegZeroMonoid]
instance divInvOneMonoid [∀ i, DivInvOneMonoid (f i)] : DivInvOneMonoid (∀ i, f i) where
  inv_one := by ext; exact inv_one

@[to_additive]
instance involutiveInv [∀ i, InvolutiveInv (f i)] : InvolutiveInv (∀ i, f i) where
  inv_inv := by intros; ext; exact inv_inv _

@[to_additive Pi.subtractionMonoid]
instance divisionMonoid [∀ i, DivisionMonoid (f i)] : DivisionMonoid (∀ i, f i) where
  __ := divInvMonoid
  __ := involutiveInv
  mul_inv_rev := by intros; ext; exact mul_inv_rev _ _
  inv_eq_of_mul := by intros _ _ h; ext; exact DivisionMonoid.inv_eq_of_mul _ _ (congrFun h _)

@[to_additive instSubtractionCommMonoid]
instance divisionCommMonoid [∀ i, DivisionCommMonoid (f i)] : DivisionCommMonoid (∀ i, f i) :=
  { divisionMonoid, commSemigroup with }

@[to_additive]
instance group [∀ i, Group (f i)] : Group (∀ i, f i) where
  mul_left_inv := by intros; ext; exact mul_left_inv _

@[to_additive]
instance commGroup [∀ i, CommGroup (f i)] : CommGroup (∀ i, f i) := { group, commMonoid with }

@[to_additive] instance instIsLeftCancelMul [∀ i, Mul (f i)] [∀ i, IsLeftCancelMul (f i)] :
    IsLeftCancelMul (∀ i, f i) where
  mul_left_cancel  _ _ _ h := funext fun _ ↦ mul_left_cancel (congr_fun h _)

@[to_additive] instance instIsRightCancelMul [∀ i, Mul (f i)] [∀ i, IsRightCancelMul (f i)] :
    IsRightCancelMul (∀ i, f i) where
  mul_right_cancel  _ _ _ h := funext fun _ ↦ mul_right_cancel (congr_fun h _)

@[to_additive] instance instIsCancelMul [∀ i, Mul (f i)] [∀ i, IsCancelMul (f i)] :
    IsCancelMul (∀ i, f i) where

@[to_additive]
instance leftCancelSemigroup [∀ i, LeftCancelSemigroup (f i)] : LeftCancelSemigroup (∀ i, f i) :=
  { semigroup with mul_left_cancel := fun _ _ _ => mul_left_cancel }

@[to_additive]
instance rightCancelSemigroup [∀ i, RightCancelSemigroup (f i)] : RightCancelSemigroup (∀ i, f i) :=
  { semigroup with mul_right_cancel := fun _ _ _ => mul_right_cancel }

@[to_additive]
instance leftCancelMonoid [∀ i, LeftCancelMonoid (f i)] : LeftCancelMonoid (∀ i, f i) :=
  { leftCancelSemigroup, monoid with }

@[to_additive]
instance rightCancelMonoid [∀ i, RightCancelMonoid (f i)] : RightCancelMonoid (∀ i, f i) :=
  { rightCancelSemigroup, monoid with }

@[to_additive]
instance cancelMonoid [∀ i, CancelMonoid (f i)] : CancelMonoid (∀ i, f i) :=
  { leftCancelMonoid, rightCancelMonoid with }

@[to_additive]
instance cancelCommMonoid [∀ i, CancelCommMonoid (f i)] : CancelCommMonoid (∀ i, f i) :=
  { leftCancelMonoid, commMonoid with }

section

variable [DecidableEq I]
variable [∀ i, One (f i)] [∀ i, One (g i)] [∀ i, One (h i)]

/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/
@[to_additive "The function supported at `i`, with value `x` there, and `0` elsewhere."]
def mulSingle (i : I) (x : f i) : ∀ (j : I), f j :=
  Function.update 1 i x

@[to_additive (attr := simp)]
theorem mulSingle_eq_same (i : I) (x : f i) : mulSingle i x i = x :=
  Function.update_same i x _

@[to_additive (attr := simp)]
theorem mulSingle_eq_of_ne {i i' : I} (h : i' ≠ i) (x : f i) : mulSingle i x i' = 1 :=
  Function.update_noteq h x _

/-- Abbreviation for `mulSingle_eq_of_ne h.symm`, for ease of use by `simp`. -/
@[to_additive (attr := simp)
  "Abbreviation for `single_eq_of_ne h.symm`, for ease of use by `simp`."]
theorem mulSingle_eq_of_ne' {i i' : I} (h : i ≠ i') (x : f i) : mulSingle i x i' = 1 :=
  mulSingle_eq_of_ne h.symm x

@[to_additive (attr := simp)]
theorem mulSingle_one (i : I) : mulSingle i (1 : f i) = 1 :=
  Function.update_eq_self _ _

-- Porting note:
-- 1) Why do I have to specify the type of `mulSingle i x` explicitly?
-- 2) Why do I have to specify the type of `(1 : I → β)`?
-- 3) Removed `{β : Sort*}` as `[One β]` converts it to a type anyways.
/-- On non-dependent functions, `Pi.mulSingle` can be expressed as an `ite` -/
@[to_additive "On non-dependent functions, `Pi.single` can be expressed as an `ite`"]
theorem mulSingle_apply [One β] (i : I) (x : β) (i' : I) :
    (mulSingle i x : I → β) i' = if i' = i then x else 1 :=
  Function.update_apply (1 : I → β) i x i'

-- Porting note: Same as above.
/-- On non-dependent functions, `Pi.mulSingle` is symmetric in the two indices. -/
@[to_additive "On non-dependent functions, `Pi.single` is symmetric in the two indices."]
theorem mulSingle_comm [One β] (i : I) (x : β) (i' : I) :
    (mulSingle i x : I → β) i' = (mulSingle i' x : I → β) i := by
  simp [mulSingle_apply, eq_comm]

@[to_additive]
theorem apply_mulSingle (f' : ∀ i, f i → g i) (hf' : ∀ i, f' i 1 = 1) (i : I) (x : f i) (j : I) :
    f' j (mulSingle i x j) = mulSingle i (f' i x) j := by
  simpa only [Pi.one_apply, hf', mulSingle] using Function.apply_update f' 1 i x j

@[to_additive apply_single₂]
theorem apply_mulSingle₂ (f' : ∀ i, f i → g i → h i) (hf' : ∀ i, f' i 1 1 = 1) (i : I)
    (x : f i) (y : g i) (j : I) :
    f' j (mulSingle i x j) (mulSingle i y j) = mulSingle i (f' i x y) j := by
  by_cases h : j = i
  · subst h
    simp only [mulSingle_eq_same]
  · simp only [mulSingle_eq_of_ne h, hf']

@[to_additive]
theorem mulSingle_op {g : I → Type*} [∀ i, One (g i)] (op : ∀ i, f i → g i)
    (h : ∀ i, op i 1 = 1) (i : I) (x : f i) :
    mulSingle i (op i x) = fun j => op j (mulSingle i x j) :=
  Eq.symm <| funext <| apply_mulSingle op h i x

@[to_additive]
theorem mulSingle_op₂ {g₁ g₂ : I → Type*} [∀ i, One (g₁ i)] [∀ i, One (g₂ i)]
    (op : ∀ i, g₁ i → g₂ i → f i) (h : ∀ i, op i 1 1 = 1) (i : I) (x₁ : g₁ i) (x₂ : g₂ i) :
    mulSingle i (op i x₁ x₂) = fun j => op j (mulSingle i x₁ j) (mulSingle i x₂ j) :=
  Eq.symm <| funext <| apply_mulSingle₂ op h i x₁ x₂

variable (f)

@[to_additive]
theorem mulSingle_injective (i : I) : Function.Injective (mulSingle i : f i → ∀ i, f i) :=
  Function.update_injective _ i

@[to_additive (attr := simp)]
theorem mulSingle_inj (i : I) {x y : f i} : mulSingle i x = mulSingle i y ↔ x = y :=
  (Pi.mulSingle_injective _ _).eq_iff

end

/-- The mapping into a product type built from maps into each component. -/
@[simp]
protected def prod (f' : ∀ i, f i) (g' : ∀ i, g i) (i : I) : f i × g i :=
  (f' i, g' i)

-- Porting note: simp now unfolds the lhs, so we are not marking these as simp.
-- @[simp]
theorem prod_fst_snd : Pi.prod (Prod.fst : α × β → α) (Prod.snd : α × β → β) = id :=
  rfl

-- Porting note: simp now unfolds the lhs, so we are not marking these as simp.
-- @[simp]
theorem prod_snd_fst : Pi.prod (Prod.snd : α × β → β) (Prod.fst : α × β → α) = Prod.swap :=
  rfl

end Pi

namespace Function

section Extend

@[to_additive]
theorem extend_one [One γ] (f : α → β) : Function.extend f (1 : α → γ) (1 : β → γ) = 1 :=
  funext fun _ => by apply ite_self

@[to_additive]
theorem extend_mul [Mul γ] (f : α → β) (g₁ g₂ : α → γ) (e₁ e₂ : β → γ) :
    Function.extend f (g₁ * g₂) (e₁ * e₂) = Function.extend f g₁ e₁ * Function.extend f g₂ e₂ := by
  classical
  funext x
  simp only [not_exists, extend_def, Pi.mul_apply, apply_dite₂, dite_eq_ite, ite_self]
-- Porting note: The Lean3 statement was
-- `funext <| λ _, by convert (apply_dite2 (*) _ _ _ _ _).symm`
-- which converts to
-- `funext fun _ => by convert (apply_dite₂ (· * ·) _ _ _ _ _).symm`
-- However this does not work, and we're not sure why.

@[to_additive]
theorem extend_inv [Inv γ] (f : α → β) (g : α → γ) (e : β → γ) :
    Function.extend f g⁻¹ e⁻¹ = (Function.extend f g e)⁻¹ := by
  classical
  funext x
  simp only [not_exists, extend_def, Pi.inv_apply, apply_dite Inv.inv]
-- Porting note: The Lean3 statement was
-- `funext <| λ _, by convert (apply_dite has_inv.inv _ _ _).symm`
-- which converts to
-- `funext fun _ => by convert (apply_dite Inv.inv _ _ _).symm`
-- However this does not work, and we're not sure why.

@[to_additive]
theorem extend_div [Div γ] (f : α → β) (g₁ g₂ : α → γ) (e₁ e₂ : β → γ) :
    Function.extend f (g₁ / g₂) (e₁ / e₂) = Function.extend f g₁ e₁ / Function.extend f g₂ e₂ := by
  classical
  funext x
  simp [Function.extend_def, apply_dite₂]
-- Porting note: The Lean3 statement was
-- `funext <| λ _, by convert (apply_dite2 (/) _ _ _ _ _).symm`
-- which converts to
-- `funext fun _ => by convert (apply_dite₂ (· / ·) _ _ _ _ _).symm`
-- However this does not work, and we're not sure why.

end Extend

theorem surjective_pi_map {F : ∀ i, f i → g i} (hF : ∀ i, Surjective (F i)) :
    Surjective fun x : ∀ i, f i => fun i => F i (x i) := fun y =>
  ⟨fun i => (hF i (y i)).choose, funext fun i => (hF i (y i)).choose_spec⟩

theorem injective_pi_map {F : ∀ i, f i → g i} (hF : ∀ i, Injective (F i)) :
    Injective fun x : ∀ i, f i => fun i => F i (x i) :=
  fun _ _ h => funext fun i => hF i <| (congr_fun h i : _)

theorem bijective_pi_map {F : ∀ i, f i → g i} (hF : ∀ i, Bijective (F i)) :
    Bijective fun x : ∀ i, f i => fun i => F i (x i) :=
  ⟨injective_pi_map fun i => (hF i).injective, surjective_pi_map fun i => (hF i).surjective⟩

lemma comp_eq_const_iff (b : β) (f : α → β) {g : β → γ} (hg : Injective g) :
    g ∘ f = Function.const _ (g b) ↔ f = Function.const _ b :=
  hg.comp_left.eq_iff' rfl

@[to_additive]
lemma comp_eq_one_iff [One β] [One γ] (f : α → β) {g : β → γ} (hg : Injective g) (hg0 : g 1 = 1) :
    g ∘ f = 1 ↔ f = 1 := by
  simpa [hg0, const_one] using comp_eq_const_iff 1 f hg

@[to_additive]
lemma comp_ne_one_iff [One β] [One γ] (f : α → β) {g : β → γ} (hg : Injective g) (hg0 : g 1 = 1) :
    g ∘ f ≠ 1 ↔ f ≠ 1 :=
  (comp_eq_one_iff f hg hg0).ne

end Function

/-- If the one function is surjective, the codomain is trivial. -/
@[to_additive "If the zero function is surjective, the codomain is trivial."]
def uniqueOfSurjectiveOne (α : Type*) {β : Type*} [One β] (h : Function.Surjective (1 : α → β)) :
    Unique β :=
  h.uniqueOfSurjectiveConst α (1 : β)

@[to_additive]
theorem Subsingleton.pi_mulSingle_eq {α : Type*} [DecidableEq I] [Subsingleton I] [One α]
    (i : I) (x : α) : Pi.mulSingle i x = fun _ => x :=
  funext fun j => by rw [Subsingleton.elim j i, Pi.mulSingle_eq_same]

namespace Sum

variable (a a' : α → γ) (b b' : β → γ)

@[to_additive (attr := simp)]
theorem elim_one_one [One γ] : Sum.elim (1 : α → γ) (1 : β → γ) = 1 :=
  Sum.elim_const_const 1

@[to_additive (attr := simp)]
theorem elim_mulSingle_one [DecidableEq α] [DecidableEq β] [One γ] (i : α) (c : γ) :
    Sum.elim (Pi.mulSingle i c) (1 : β → γ) = Pi.mulSingle (Sum.inl i) c := by
  simp only [Pi.mulSingle, Sum.elim_update_left, elim_one_one]

@[to_additive (attr := simp)]
theorem elim_one_mulSingle [DecidableEq α] [DecidableEq β] [One γ] (i : β) (c : γ) :
    Sum.elim (1 : α → γ) (Pi.mulSingle i c) = Pi.mulSingle (Sum.inr i) c := by
  simp only [Pi.mulSingle, Sum.elim_update_right, elim_one_one]

@[to_additive]
theorem elim_inv_inv [Inv γ] : Sum.elim a⁻¹ b⁻¹ = (Sum.elim a b)⁻¹ :=
  (Sum.comp_elim Inv.inv a b).symm

@[to_additive]
theorem elim_mul_mul [Mul γ] : Sum.elim (a * a') (b * b') = Sum.elim a b * Sum.elim a' b' := by
  ext x
  cases x <;> rfl

@[to_additive]
theorem elim_div_div [Div γ] : Sum.elim (a / a') (b / b') = Sum.elim a b / Sum.elim a' b' := by
  ext x
  cases x <;> rfl

end Sum
