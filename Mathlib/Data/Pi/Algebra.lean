/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Prod.Basic
import Mathlib.Logic.Unique
import Mathlib.Data.Sum.Basic

#align_import data.pi.algebra from "leanprover-community/mathlib"@"70d50ecfd4900dd6d328da39ab7ebd516abe4025"

/-!
# Instances and theorems on pi types

This file provides basic definitions and notation instances for Pi types.

Instances of more sophisticated classes are defined in `Pi.lean` files elsewhere.
-/

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
#align pi.has_one Pi.instOne
#align pi.has_zero Pi.instZero

@[to_additive (attr := simp)]
theorem one_apply [∀ i, One <| f i] : (1 : ∀ i, f i) i = 1 :=
  rfl
#align pi.one_apply Pi.one_apply
#align pi.zero_apply Pi.zero_apply

@[to_additive]
theorem one_def [∀ i, One <| f i] : (1 : ∀ i, f i) = fun _ => 1 :=
  rfl
#align pi.one_def Pi.one_def
#align pi.zero_def Pi.zero_def

@[to_additive (attr := simp)]
theorem const_one [One β] : const α (1 : β) = 1 :=
  rfl
#align pi.const_one Pi.const_one
#align pi.const_zero Pi.const_zero

@[to_additive (attr := simp)]
theorem one_comp [One γ] (x : α → β) : (1 : β → γ) ∘ x = 1 :=
  rfl
#align pi.one_comp Pi.one_comp
#align pi.zero_comp Pi.zero_comp

@[to_additive (attr := simp)]
theorem comp_one [One β] (x : β → γ) : x ∘ (1 : α → β) = const α (x 1) :=
  rfl
#align pi.comp_one Pi.comp_one
#align pi.comp_zero Pi.comp_zero

@[to_additive]
instance instMul [∀ i, Mul <| f i] : Mul (∀ i : I, f i) :=
  ⟨fun f g i => f i * g i⟩
#align pi.has_mul Pi.instMul
#align pi.has_add Pi.instAdd

@[to_additive (attr := simp)]
theorem mul_apply [∀ i, Mul <| f i] : (x * y) i = x i * y i :=
  rfl
#align pi.mul_apply Pi.mul_apply
#align pi.add_apply Pi.add_apply

@[to_additive]
theorem mul_def [∀ i, Mul <| f i] : x * y = fun i => x i * y i :=
  rfl
#align pi.mul_def Pi.mul_def
#align pi.add_def Pi.add_def

@[to_additive (attr := simp)]
theorem const_mul [Mul β] (a b : β) : const α a * const α b = const α (a * b) :=
  rfl
#align pi.const_mul Pi.const_mul
#align pi.const_add Pi.const_add

@[to_additive]
theorem mul_comp [Mul γ] (x y : β → γ) (z : α → β) : (x * y) ∘ z = x ∘ z * y ∘ z :=
  rfl
#align pi.mul_comp Pi.mul_comp
#align pi.add_comp Pi.add_comp

@[to_additive]
instance instSMul [∀ i, SMul α <| f i] : SMul α (∀ i : I, f i) :=
  ⟨fun s x => fun i => s • x i⟩
#align pi.has_smul Pi.instSMul
#align pi.has_vadd Pi.instVAdd

@[to_additive existing instSMul]
instance instPow [∀ i, Pow (f i) β] : Pow (∀ i, f i) β :=
  ⟨fun x b i => x i ^ b⟩

@[to_additive (attr := simp, to_additive) (reorder := 5 6) smul_apply]
theorem pow_apply [∀ i, Pow (f i) β] (x : ∀ i, f i) (b : β) (i : I) : (x ^ b) i = x i ^ b :=
  rfl
#align pi.pow_apply Pi.pow_apply
#align pi.smul_apply Pi.smul_apply
#align pi.vadd_apply Pi.vadd_apply

@[to_additive (attr := to_additive) (reorder := 5 6) smul_def]
theorem pow_def [∀ i, Pow (f i) β] (x : ∀ i, f i) (b : β) : x ^ b = fun i => x i ^ b :=
  rfl
#align pi.pow_def Pi.pow_def
#align pi.smul_def Pi.smul_def
#align pi.vadd_def Pi.vadd_def

@[to_additive (attr := simp, to_additive) (reorder := 2 3, 5 6) smul_const]
theorem const_pow [Pow α β] (a : α) (b : β) : const I a ^ b = const I (a ^ b) :=
  rfl
#align pi.const_pow Pi.const_pow
#align pi.smul_const Pi.smul_const
#align pi.vadd_const Pi.vadd_const

@[to_additive (attr := to_additive) (reorder := 6 7) smul_comp]
theorem pow_comp [Pow γ α] (x : β → γ) (a : α) (y : I → β) : (x ^ a) ∘ y = x ∘ y ^ a :=
  rfl
#align pi.pow_comp Pi.pow_comp
#align pi.smul_comp Pi.smul_comp
#align pi.vadd_comp Pi.vadd_comp

/-!
Porting note: `bit0` and `bit1` are deprecated. This section can be removed entirely
(without replacement?).
-/
section deprecated

set_option linter.deprecated false

@[simp, deprecated]
theorem bit0_apply [∀ i, Add <| f i] : (bit0 x) i = bit0 (x i) :=
  rfl
#align pi.bit0_apply Pi.bit0_apply

@[simp, deprecated]
theorem bit1_apply [∀ i, Add <| f i] [∀ i, One <| f i] : (bit1 x) i = bit1 (x i) :=
  rfl
#align pi.bit1_apply Pi.bit1_apply

end deprecated

@[to_additive]
instance instInv [∀ i, Inv <| f i] : Inv (∀ i : I, f i) :=
  ⟨fun f i => (f i)⁻¹⟩
#align pi.has_inv Pi.instInv
#align pi.has_neg Pi.instNeg

@[to_additive (attr := simp)]
theorem inv_apply [∀ i, Inv <| f i] : x⁻¹ i = (x i)⁻¹ :=
  rfl
#align pi.inv_apply Pi.inv_apply
#align pi.neg_apply Pi.neg_apply

@[to_additive]
theorem inv_def [∀ i, Inv <| f i] : x⁻¹ = fun i => (x i)⁻¹ :=
  rfl
#align pi.inv_def Pi.inv_def
#align pi.neg_def Pi.neg_def

@[to_additive]
theorem const_inv [Inv β] (a : β) : (const α a)⁻¹ = const α a⁻¹ :=
  rfl
#align pi.const_inv Pi.const_inv
#align pi.const_neg Pi.const_neg

@[to_additive]
theorem inv_comp [Inv γ] (x : β → γ) (y : α → β) : x⁻¹ ∘ y = (x ∘ y)⁻¹ :=
  rfl
#align pi.inv_comp Pi.inv_comp
#align pi.neg_comp Pi.neg_comp

@[to_additive]
instance instDiv [∀ i, Div <| f i] : Div (∀ i : I, f i) :=
  ⟨fun f g i => f i / g i⟩
#align pi.has_div Pi.instDiv
#align pi.has_sub Pi.instSub

@[to_additive (attr := simp)]
theorem div_apply [∀ i, Div <| f i] : (x / y) i = x i / y i :=
  rfl
#align pi.div_apply Pi.div_apply
#align pi.sub_apply Pi.sub_apply

@[to_additive]
theorem div_def [∀ i, Div <| f i] : x / y = fun i => x i / y i :=
  rfl
#align pi.div_def Pi.div_def
#align pi.sub_def Pi.sub_def

@[to_additive]
theorem div_comp [Div γ] (x y : β → γ) (z : α → β) : (x / y) ∘ z = x ∘ z / y ∘ z :=
  rfl
#align pi.div_comp Pi.div_comp
#align pi.sub_comp Pi.sub_comp

@[to_additive (attr := simp)]
theorem const_div [Div β] (a b : β) : const α a / const α b = const α (a / b) :=
  rfl
#align pi.const_div Pi.const_div
#align pi.const_sub Pi.const_sub

section

variable [DecidableEq I]

variable [∀ i, One (f i)] [∀ i, One (g i)] [∀ i, One (h i)]

/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/
@[to_additive "The function supported at `i`, with value `x` there, and `0` elsewhere."]
def mulSingle (i : I) (x : f i) : ∀ (j : I), f j :=
  Function.update 1 i x
#align pi.mul_single Pi.mulSingle
#align pi.single Pi.single

@[to_additive (attr := simp)]
theorem mulSingle_eq_same (i : I) (x : f i) : mulSingle i x i = x :=
  Function.update_same i x _
#align pi.mul_single_eq_same Pi.mulSingle_eq_same
#align pi.single_eq_same Pi.single_eq_same

@[to_additive (attr := simp)]
theorem mulSingle_eq_of_ne {i i' : I} (h : i' ≠ i) (x : f i) : mulSingle i x i' = 1 :=
  Function.update_noteq h x _
#align pi.mul_single_eq_of_ne Pi.mulSingle_eq_of_ne
#align pi.single_eq_of_ne Pi.single_eq_of_ne

/-- Abbreviation for `mulSingle_eq_of_ne h.symm`, for ease of use by `simp`. -/
@[to_additive (attr := simp)
  "Abbreviation for `single_eq_of_ne h.symm`, for ease of use by `simp`."]
theorem mulSingle_eq_of_ne' {i i' : I} (h : i ≠ i') (x : f i) : mulSingle i x i' = 1 :=
  mulSingle_eq_of_ne h.symm x
#align pi.mul_single_eq_of_ne' Pi.mulSingle_eq_of_ne'
#align pi.single_eq_of_ne' Pi.single_eq_of_ne'

@[to_additive (attr := simp)]
theorem mulSingle_one (i : I) : mulSingle i (1 : f i) = 1 :=
  Function.update_eq_self _ _
#align pi.mul_single_one Pi.mulSingle_one
#align pi.single_zero Pi.single_zero

-- Porting notes:
-- 1) Why do I have to specify the type of `mulSingle i x` explicitly?
-- 2) Why do I have to specify the type of `(1 : I → β)`?
-- 3) Removed `{β : Sort*}` as `[One β]` converts it to a type anyways.
/-- On non-dependent functions, `Pi.mulSingle` can be expressed as an `ite` -/
@[to_additive "On non-dependent functions, `Pi.single` can be expressed as an `ite`"]
theorem mulSingle_apply [One β] (i : I) (x : β) (i' : I) :
    (mulSingle i x : I → β) i' = if i' = i then x else 1 :=
  Function.update_apply (1 : I → β) i x i'
#align pi.mul_single_apply Pi.mulSingle_apply
#align pi.single_apply Pi.single_apply

-- Porting notes : Same as above.
/-- On non-dependent functions, `Pi.mulSingle` is symmetric in the two indices. -/
@[to_additive "On non-dependent functions, `Pi.single` is symmetric in the two indices."]
theorem mulSingle_comm [One β] (i : I) (x : β) (i' : I) :
    (mulSingle i x : I → β) i' = (mulSingle i' x : I → β) i := by
  simp [mulSingle_apply, eq_comm]
  -- 🎉 no goals
#align pi.mul_single_comm Pi.mulSingle_comm
#align pi.single_comm Pi.single_comm

@[to_additive]
theorem apply_mulSingle (f' : ∀ i, f i → g i) (hf' : ∀ i, f' i 1 = 1) (i : I) (x : f i) (j : I) :
    f' j (mulSingle i x j) = mulSingle i (f' i x) j := by
  simpa only [Pi.one_apply, hf', mulSingle] using Function.apply_update f' 1 i x j
  -- 🎉 no goals
#align pi.apply_mul_single Pi.apply_mulSingle
#align pi.apply_single Pi.apply_single

@[to_additive apply_single₂]
theorem apply_mulSingle₂ (f' : ∀ i, f i → g i → h i) (hf' : ∀ i, f' i 1 1 = 1) (i : I)
    (x : f i) (y : g i) (j : I) :
    f' j (mulSingle i x j) (mulSingle i y j) = mulSingle i (f' i x y) j := by
  by_cases h : j = i
  -- ⊢ f' j (mulSingle i x j) (mulSingle i y j) = mulSingle i (f' i x y) j
  · subst h
    -- ⊢ f' j (mulSingle j x j) (mulSingle j y j) = mulSingle j (f' j x y) j
    simp only [mulSingle_eq_same]
    -- 🎉 no goals
  · simp only [mulSingle_eq_of_ne h, hf']
    -- 🎉 no goals
#align pi.apply_mul_single₂ Pi.apply_mulSingle₂
#align pi.apply_single₂ Pi.apply_single₂

@[to_additive]
theorem mulSingle_op {g : I → Type*} [∀ i, One (g i)] (op : ∀ i, f i → g i)
    (h : ∀ i, op i 1 = 1) (i : I) (x : f i) :
    mulSingle i (op i x) = fun j => op j (mulSingle i x j) :=
  Eq.symm <| funext <| apply_mulSingle op h i x
#align pi.mul_single_op Pi.mulSingle_op
#align pi.single_op Pi.single_op

@[to_additive]
theorem mulSingle_op₂ {g₁ g₂ : I → Type*} [∀ i, One (g₁ i)] [∀ i, One (g₂ i)]
    (op : ∀ i, g₁ i → g₂ i → f i) (h : ∀ i, op i 1 1 = 1) (i : I) (x₁ : g₁ i) (x₂ : g₂ i) :
    mulSingle i (op i x₁ x₂) = fun j => op j (mulSingle i x₁ j) (mulSingle i x₂ j) :=
  Eq.symm <| funext <| apply_mulSingle₂ op h i x₁ x₂
#align pi.mul_single_op₂ Pi.mulSingle_op₂
#align pi.single_op₂ Pi.single_op₂

variable (f)

@[to_additive]
theorem mulSingle_injective (i : I) : Function.Injective (mulSingle i : f i → ∀ i, f i) :=
  Function.update_injective _ i
#align pi.mul_single_injective Pi.mulSingle_injective
#align pi.single_injective Pi.single_injective

@[to_additive (attr := simp)]
theorem mulSingle_inj (i : I) {x y : f i} : mulSingle i x = mulSingle i y ↔ x = y :=
  (Pi.mulSingle_injective _ _).eq_iff
#align pi.mul_single_inj Pi.mulSingle_inj
#align pi.single_inj Pi.single_inj

end

/-- The mapping into a product type built from maps into each component. -/
@[simp]
protected def prod (f' : ∀ i, f i) (g' : ∀ i, g i) (i : I) : f i × g i :=
  (f' i, g' i)
#align pi.prod Pi.prod

-- Porting note : simp now unfolds the lhs, so we are not marking these as simp.
-- @[simp]
theorem prod_fst_snd : Pi.prod (Prod.fst : α × β → α) (Prod.snd : α × β → β) = id :=
  funext fun _ => Prod.mk.eta
#align pi.prod_fst_snd Pi.prod_fst_snd

-- Porting note : simp now unfolds the lhs, so we are not marking these as simp.
-- @[simp]
theorem prod_snd_fst : Pi.prod (Prod.snd : α × β → β) (Prod.fst : α × β → α) = Prod.swap :=
  rfl
#align pi.prod_snd_fst Pi.prod_snd_fst

end Pi

namespace Function

section Extend

@[to_additive]
theorem extend_one [One γ] (f : α → β) : Function.extend f (1 : α → γ) (1 : β → γ) = 1 :=
  funext fun _ => by apply ite_self
                     -- 🎉 no goals
#align function.extend_one Function.extend_one
#align function.extend_zero Function.extend_zero

@[to_additive]
theorem extend_mul [Mul γ] (f : α → β) (g₁ g₂ : α → γ) (e₁ e₂ : β → γ) :
    Function.extend f (g₁ * g₂) (e₁ * e₂) = Function.extend f g₁ e₁ * Function.extend f g₂ e₂ := by
  classical
  funext x
  simp only [not_exists, extend_def, Pi.mul_apply, apply_dite₂, dite_eq_ite, ite_self]
-- Porting note: The Lean3 statement was
-- `funext $ λ _, by convert (apply_dite2 (*) _ _ _ _ _).symm`
-- which converts to
-- `funext fun _ => by convert (apply_dite₂ (· * ·) _ _ _ _ _).symm`
-- However this does not work, and we're not sure why.
#align function.extend_mul Function.extend_mul
#align function.extend_add Function.extend_add

@[to_additive]
theorem extend_inv [Inv γ] (f : α → β) (g : α → γ) (e : β → γ) :
    Function.extend f g⁻¹ e⁻¹ = (Function.extend f g e)⁻¹ := by
  classical
  funext x
  simp only [not_exists, extend_def, Pi.inv_apply, apply_dite Inv.inv]
-- Porting note: The Lean3 statement was
-- `funext $ λ _, by convert (apply_dite has_inv.inv _ _ _).symm`
-- which converts to
-- `funext fun _ => by convert (apply_dite Inv.inv _ _ _).symm`
-- However this does not work, and we're not sure why.
#align function.extend_inv Function.extend_inv
#align function.extend_neg Function.extend_neg

@[to_additive]
theorem extend_div [Div γ] (f : α → β) (g₁ g₂ : α → γ) (e₁ e₂ : β → γ) :
    Function.extend f (g₁ / g₂) (e₁ / e₂) = Function.extend f g₁ e₁ / Function.extend f g₂ e₂ := by
  classical
  funext x
  simp [Function.extend_def, apply_dite₂]
-- Porting note: The Lean3 statement was
-- `funext $ λ _, by convert (apply_dite2 (/) _ _ _ _ _).symm`
-- which converts to
-- `funext fun _ => by convert (apply_dite₂ (· / ·) _ _ _ _ _).symm`
-- However this does not work, and we're not sure why.
#align function.extend_div Function.extend_div
#align function.extend_sub Function.extend_sub

end Extend

theorem surjective_pi_map {F : ∀ i, f i → g i} (hF : ∀ i, Surjective (F i)) :
    Surjective fun x : ∀ i, f i => fun i => F i (x i) := fun y =>
  ⟨fun i => (hF i (y i)).choose, funext fun i => (hF i (y i)).choose_spec⟩
#align function.surjective_pi_map Function.surjective_pi_map

theorem injective_pi_map {F : ∀ i, f i → g i} (hF : ∀ i, Injective (F i)) :
    Injective fun x : ∀ i, f i => fun i => F i (x i) :=
  fun _ _ h => funext fun i => hF i <| (congr_fun h i : _)
#align function.injective_pi_map Function.injective_pi_map

theorem bijective_pi_map {F : ∀ i, f i → g i} (hF : ∀ i, Bijective (F i)) :
    Bijective fun x : ∀ i, f i => fun i => F i (x i) :=
  ⟨injective_pi_map fun i => (hF i).injective, surjective_pi_map fun i => (hF i).surjective⟩
#align function.bijective_pi_map Function.bijective_pi_map

end Function

/-- If the one function is surjective, the codomain is trivial. -/
@[to_additive "If the zero function is surjective, the codomain is trivial."]
def uniqueOfSurjectiveOne (α : Type*) {β : Type*} [One β] (h : Function.Surjective (1 : α → β)) :
    Unique β :=
  h.uniqueOfSurjectiveConst α (1 : β)
#align unique_of_surjective_one uniqueOfSurjectiveOne
#align unique_of_surjective_zero uniqueOfSurjectiveZero

@[to_additive]
theorem Subsingleton.pi_mulSingle_eq {α : Type*} [DecidableEq I] [Subsingleton I] [One α]
    (i : I) (x : α) : Pi.mulSingle i x = fun _ => x :=
  funext fun j => by rw [Subsingleton.elim j i, Pi.mulSingle_eq_same]
                     -- 🎉 no goals
#align subsingleton.pi_mul_single_eq Subsingleton.pi_mulSingle_eq
#align subsingleton.pi_single_eq Subsingleton.pi_single_eq

namespace Sum

variable (a a' : α → γ) (b b' : β → γ)

@[to_additive (attr := simp)]
theorem elim_one_one [One γ] : Sum.elim (1 : α → γ) (1 : β → γ) = 1 :=
  Sum.elim_const_const 1
#align sum.elim_one_one Sum.elim_one_one
#align sum.elim_zero_zero Sum.elim_zero_zero

@[to_additive (attr := simp)]
theorem elim_mulSingle_one [DecidableEq α] [DecidableEq β] [One γ] (i : α) (c : γ) :
    Sum.elim (Pi.mulSingle i c) (1 : β → γ) = Pi.mulSingle (Sum.inl i) c := by
  simp only [Pi.mulSingle, Sum.elim_update_left, elim_one_one]
  -- 🎉 no goals

@[to_additive (attr := simp)]
theorem elim_one_mulSingle [DecidableEq α] [DecidableEq β] [One γ] (i : β) (c : γ) :
    Sum.elim (1 : α → γ) (Pi.mulSingle i c) = Pi.mulSingle (Sum.inr i) c := by
  simp only [Pi.mulSingle, Sum.elim_update_right, elim_one_one]
  -- 🎉 no goals
#align sum.elim_mul_single_one Sum.elim_mulSingle_one
#align sum.elim_one_mul_single Sum.elim_one_mulSingle
#align sum.elim_single_zero Sum.elim_single_zero
#align sum.elim_zero_single Sum.elim_zero_single

@[to_additive]
theorem elim_inv_inv [Inv γ] : Sum.elim a⁻¹ b⁻¹ = (Sum.elim a b)⁻¹ :=
  (Sum.comp_elim Inv.inv a b).symm
#align sum.elim_inv_inv Sum.elim_inv_inv
#align sum.elim_neg_neg Sum.elim_neg_neg

@[to_additive]
theorem elim_mul_mul [Mul γ] : Sum.elim (a * a') (b * b') = Sum.elim a b * Sum.elim a' b' := by
  ext x
  -- ⊢ Sum.elim (a * a') (b * b') x = (Sum.elim a b * Sum.elim a' b') x
  cases x <;> rfl
  -- ⊢ Sum.elim (a * a') (b * b') (inl val✝) = (Sum.elim a b * Sum.elim a' b') (inl …
              -- 🎉 no goals
              -- 🎉 no goals
#align sum.elim_mul_mul Sum.elim_mul_mul
#align sum.elim_add_add Sum.elim_add_add

@[to_additive]
theorem elim_div_div [Div γ] : Sum.elim (a / a') (b / b') = Sum.elim a b / Sum.elim a' b' := by
  ext x
  -- ⊢ Sum.elim (a / a') (b / b') x = (Sum.elim a b / Sum.elim a' b') x
  cases x <;> rfl
  -- ⊢ Sum.elim (a / a') (b / b') (inl val✝) = (Sum.elim a b / Sum.elim a' b') (inl …
              -- 🎉 no goals
              -- 🎉 no goals
#align sum.elim_div_div Sum.elim_div_div
#align sum.elim_sub_sub Sum.elim_sub_sub

end Sum
