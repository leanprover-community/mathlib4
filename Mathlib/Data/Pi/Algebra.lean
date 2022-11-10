/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Prod.Basic
import Mathlib.Logic.Unique
import Mathlib.Data.Sum.Basic

/-!
# Instances and theorems on pi types

This file provides basic definitions and notation instances for Pi types.

Instances of more sophisticated classes are defined in `Pi.lean` files elsewhere.
-/

open Function

universe u v₁ v₂ v₃

variable {I : Type u}

-- The indexing type
variable {α β γ : Type _}

-- The families of types already equipped with instances
variable {f : I → Type v₁} {g : I → Type v₂} {h : I → Type v₃}

variable (x y : ∀ i, f i) (i : I)

namespace Pi

/-! `1`, `0`, `+`, `*`, `+ᵥ`, `•`, `^`, `-`, `⁻¹`, and `/` are defined pointwise. -/

@[to_additive instZero] -- TODO: improve `to_additive`
instance instOne [∀ i, One <| f i] : One (∀ i : I, f i) :=
  ⟨fun _ => 1⟩

@[simp, to_additive]
theorem one_apply [∀ i, One <| f i] : (1 : ∀ i, f i) i = 1 :=
  rfl

@[to_additive]
theorem one_def [∀ i, One <| f i] : (1 : ∀ i, f i) = fun _ => 1 :=
  rfl

@[simp, to_additive]
theorem const_one [One β] : const α (1 : β) = 1 :=
  rfl

@[simp, to_additive]
theorem one_comp [One γ] (x : α → β) : (1 : β → γ) ∘ x = 1 :=
  rfl

@[simp, to_additive]
theorem comp_one [One β] (x : β → γ) : x ∘ (1 : α → β) = const α (x 1) :=
  rfl

@[to_additive instAdd] -- TODO: improve `to_additive`
instance instMul [∀ i, Mul <| f i] : Mul (∀ i : I, f i) :=
  ⟨fun f g i => f i * g i⟩

@[simp, to_additive]
theorem mul_apply [∀ i, Mul <| f i] : (x * y) i = x i * y i :=
  rfl

@[to_additive]
theorem mul_def [∀ i, Mul <| f i] : x * y = fun i => x i * y i :=
  rfl

@[simp, to_additive]
theorem const_mul [Mul β] (a b : β) : const α a * const α b = const α (a * b) :=
  rfl

@[to_additive]
theorem mul_comp [Mul γ] (x y : β → γ) (z : α → β) : (x * y) ∘ z = x ∘ z * y ∘ z :=
  rfl

-- @[to_additive instHasVadd] -- TODO
instance instHasSmul [∀ i, HasSmul α <| f i] : HasSmul α (∀ i : I, f i) :=
  ⟨fun s x => fun i => s • x i⟩

-- TODO: Didn't manage to use `to_additive` above. Delete this once the above works:
instance instHasVadd [∀ i, HasVadd α <| f i] : HasVadd α (∀ i : I, f i) :=
  ⟨fun s x => fun i => s +ᵥ x i⟩

@[simp, to_additive]
theorem smul_apply [∀ i, HasSmul α <| f i] (s : α) (x : ∀ i, f i) (i : I) : (s • x) i = s • x i :=
  rfl

@[to_additive]
theorem smul_def [∀ i, HasSmul α <| f i] (s : α) (x : ∀ i, f i) : s • x = fun i => s • x i :=
  rfl

@[simp, to_additive]
theorem smul_const [HasSmul α β] (a : α) (b : β) : a • const I b = const I (a • b) :=
  rfl

@[to_additive ]
theorem smul_comp [HasSmul α γ] (a : α) (x : β → γ) (y : I → β) : (a • x) ∘ y = a • x ∘ y :=
  rfl

-- @[to_additive] TODO
instance instPow [∀ i, Pow (f i) β] : Pow (∀ i, f i) β :=
  ⟨fun x b i => x i ^ b⟩

-- TODO: `to_additive` didn't work because `a ^ b` changes to `b • a`.
-- Delete this once the above works:
instance instHasSmul' [∀ i, HasSmul β (f i)] : HasSmul β (∀ i, f i) :=
  ⟨fun b x i => b • (x i)⟩

@[simp, to_additive Pi.smul_apply, to_additive_reorder 5]
theorem pow_apply [∀ i, Pow (f i) β] (x : ∀ i, f i) (b : β) (i : I) : (x ^ b) i = x i ^ b :=
  rfl

@[to_additive Pi.smul_def, to_additive_reorder 5]
theorem pow_def [∀ i, Pow (f i) β] (x : ∀ i, f i) (b : β) : x ^ b = fun i => x i ^ b :=
  rfl

-- `to_additive` generates bad output if we take `has_pow α β`.
@[simp, to_additive smul_const, to_additive_reorder 5]
theorem const_pow [Pow β α] (b : β) (a : α) : const I b ^ a = const I (b ^ a) :=
  rfl

@[to_additive smul_comp, to_additive_reorder 6]
theorem pow_comp [Pow γ α] (x : β → γ) (a : α) (y : I → β) : (x ^ a) ∘ y = x ∘ y ^ a :=
  rfl

-- TODO: deprecated. Remove?
-- @[simp]
-- theorem bit0_apply [∀ i, Add <| f i] : (bit0 x) i = bit0 (x i) :=
--   rfl

-- @[simp]
-- theorem bit1_apply [∀ i, Add <| f i] [∀ i, One <| f i] : (bit1 x) i = bit1 (x i) :=
--   rfl

@[to_additive instNegForAll] -- TODO: improve `to_additive`
instance instInvForAll [∀ i, Inv <| f i] : Inv (∀ i : I, f i) :=
  ⟨fun f i => (f i)⁻¹⟩

@[simp, to_additive]
theorem inv_apply [∀ i, Inv <| f i] : x⁻¹ i = (x i)⁻¹ :=
  rfl

@[to_additive]
theorem inv_def [∀ i, Inv <| f i] : x⁻¹ = fun i => (x i)⁻¹ :=
  rfl

@[to_additive]
theorem const_inv [Inv β] (a : β) : (const α a)⁻¹ = const α a⁻¹ :=
  rfl

@[to_additive]
theorem inv_comp [Inv γ] (x : β → γ) (y : α → β) : x⁻¹ ∘ y = (x ∘ y)⁻¹ :=
  rfl

@[to_additive instSubForAll] -- TODO: improve `to_additive`
instance instDivForAll [∀ i, Div <| f i] : Div (∀ i : I, f i) :=
  ⟨fun f g i => f i / g i⟩

@[simp, to_additive]
theorem div_apply [∀ i, Div <| f i] : (x / y) i = x i / y i :=
  rfl

@[to_additive]
theorem div_def [∀ i, Div <| f i] : x / y = fun i => x i / y i :=
  rfl

@[to_additive]
theorem div_comp [Div γ] (x y : β → γ) (z : α → β) : (x / y) ∘ z = x ∘ z / y ∘ z :=
  rfl

@[simp, to_additive]
theorem const_div [Div β] (a b : β) : const α a / const α b = const α (a / b) :=
  rfl

section

variable [DecidableEq I]

variable [∀ i, One (f i)] [∀ i, One (g i)] [∀ i, One (h i)]

/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/
@[to_additive Pi.single "The function supported at `i`, with value `x` there, and `0` elsewhere."]
def mulSingle (i : I) (x : f i) : ∀ i, f i :=
  Function.update 1 i x

@[simp, to_additive]
theorem mul_single_eq_same (i : I) (x : f i) : mulSingle i x i = x :=
  Function.update_same i x _

@[simp, to_additive]
theorem mul_single_eq_of_ne {i i' : I} (h : i' ≠ i) (x : f i) : mulSingle i x i' = 1 :=
  Function.update_noteq h x _

/-- Abbreviation for `mul_single_eq_of_ne h.symm`, for ease of use by `simp`. -/
@[simp, to_additive "Abbreviation for `single_eq_of_ne h.symm`, for ease of\nuse by `simp`."]
theorem mul_single_eq_of_ne' {i i' : I} (h : i ≠ i') (x : f i) : mulSingle i x i' = 1 :=
  mul_single_eq_of_ne h.symm x

@[simp, to_additive]
theorem mul_single_one (i : I) : mulSingle i (1 : f i) = 1 :=
  Function.update_eq_self _ _

-- TODO: Seems to be a coersion problem: RHS has Type `β`, LHS not.
/-- On non-dependent functions, `Pi.mulSingle` can be expressed as an `ite` -/
@[to_additive "On non-dependent functions, `Pi.single` can be expressed as an `ite`"]
theorem mul_single_apply {β : Sort _} [One β] (i : I) (x : β) (i' : I) :
    mulSingle i x i' = if i' = i then x else 1 :=
  Function.update_apply 1 i x i'

/-- On non-dependent functions, `Pi.mulSingle` is symmetric in the two indices. -/
@[to_additive "On non-dependent functions, `Pi.single` is symmetric in the two\nindices."]
theorem mul_single_comm {β : Sort _} [One β] (i : I) (x : β) (i' : I) :
    mulSingle i x i' = mulSingle i' x i := by
  simp [mul_single_apply, eq_comm]

@[to_additive]
theorem apply_mul_single (f' : ∀ i, f i → g i) (hf' : ∀ i, f' i 1 = 1) (i : I) (x : f i) (j : I) :
    f' j (mulSingle i x j) = mulSingle i (f' i x) j := by
  simpa only [Pi.one_apply, hf', mulSingle] using Function.apply_update f' 1 i x j

@[to_additive apply_single₂]
theorem apply_mul_single₂ (f' : ∀ i, f i → g i → h i) (hf' : ∀ i, f' i 1 1 = 1) (i : I)
    (x : f i) (y : g i) (j : I) :
    f' j (mulSingle i x j) (mulSingle i y j) = mulSingle i (f' i x y) j := by
  by_cases h:j = i
  · subst h
    simp only [mul_single_eq_same]

  · simp only [mul_single_eq_of_ne h, hf']

@[to_additive]
theorem mul_single_op {g : I → Type _} [∀ i, One (g i)] (op : ∀ i, f i → g i)
    (h : ∀ i, op i 1 = 1) (i : I) (x : f i) :
    mulSingle i (op i x) = fun j => op j (mulSingle i x j) :=
  Eq.symm <| funext <| apply_mul_single op h i x

@[to_additive]
theorem mul_single_op₂ {g₁ g₂ : I → Type _} [∀ i, One (g₁ i)] [∀ i, One (g₂ i)]
    (op : ∀ i, g₁ i → g₂ i → f i) (h : ∀ i, op i 1 1 = 1) (i : I) (x₁ : g₁ i) (x₂ : g₂ i) :
    mulSingle i (op i x₁ x₂) = fun j => op j (mulSingle i x₁ j) (mulSingle i x₂ j) :=
  Eq.symm <| funext <| apply_mul_single₂ op h i x₁ x₂

variable (f)

@[to_additive]
theorem mul_single_injective (i : I) : Function.Injective (mulSingle i : f i → ∀ i, f i) :=
  Function.update_injective _ i

@[simp, to_additive]
theorem mul_single_inj (i : I) {x y : f i} : mulSingle i x = mulSingle i y ↔ x = y :=
  (Pi.mul_single_injective _ _).eq_iff

end

/-- The mapping into a product type built from maps into each component. -/
@[simp]
protected def prod (f' : ∀ i, f i) (g' : ∀ i, g i) (i : I) : f i × g i :=
  (f' i, g' i)

@[simp]
theorem prod_fst_snd : Pi.prod (Prod.fst : α × β → α) (Prod.snd : α × β → β) = id :=
  funext fun _ => Prod.mk.eta

@[simp]
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
    Function.extend f (g₁ * g₂) (e₁ * e₂) = Function.extend f g₁ e₁ * Function.extend f g₂ e₂ :=
  funext fun _ => by convert (apply_dite₂ (· * ·)).symm

@[to_additive]
theorem extend_inv [Inv γ] (f : α → β) (g : α → γ) (e : β → γ) :
    Function.extend f g⁻¹ e⁻¹ = (Function.extend f g e)⁻¹ :=
  funext fun _ => by convert (apply_dite Inv.inv _ _ _).symm

@[to_additive]
theorem extend_div [Div γ] (f : α → β) (g₁ g₂ : α → γ) (e₁ e₂ : β → γ) :
    Function.extend f (g₁ / g₂) (e₁ / e₂) = Function.extend f g₁ e₁ / Function.extend f g₂ e₂ :=
  funext fun _ => by convert (apply_dite₂ (· / ·) _ _ _ _ _).symm

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


#align bijective.injective Bijective.injective
#align bijective.surjective Bijective.surjective

end Function

/-- If the one function is surjective, the codomain is trivial. -/
@[to_additive "If the zero function is surjective, the codomain is trivial."]
def uniqueOfSurjectiveOne (α : Type _) {β : Type _} [One β] (h : Function.Surjective (1 : α → β)) :
    Unique β :=
  h.uniqueOfSurjectiveConst α (1 : β)

@[to_additive Subsingleton.pi_single_eq]
theorem Subsingleton.pi_mul_single_eq {α : Type _} [DecidableEq I] [Subsingleton I] [One α]
    (i : I) (x : α) : Pi.mulSingle i x = fun _ => x :=
  funext fun j => by rw [Subsingleton.elim j i, Pi.mul_single_eq_same]

namespace Sum

variable (a a' : α → γ) (b b' : β → γ)

@[simp, to_additive]
theorem elim_one_one [One γ] : Sum.elim (1 : α → γ) (1 : β → γ) = 1 :=
  Sum.elim_const_const 1

@[simp, to_additive]
theorem elim_mul_single_one [DecidableEq α] [DecidableEq β] [One γ] (i : α) (c : γ) :
    Sum.elim (Pi.mulSingle i c) (1 : β → γ) = Pi.mulSingle (Sum.inl i) c := by
  simp only [Pi.mulSingle, Sum.elim_update_left, elim_one_one]

@[simp, to_additive]
theorem elim_one_mul_single [DecidableEq α] [DecidableEq β] [One γ] (i : β) (c : γ) :
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
