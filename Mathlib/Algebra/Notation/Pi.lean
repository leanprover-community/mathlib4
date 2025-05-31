/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot, Eric Wieser
-/
import Mathlib.Algebra.Notation.Defs
import Mathlib.Data.Set.Operations
import Mathlib.Util.AssertExists

/-!
# Notation for algebraic operators on pi types

This file provides only the notation for (pointwise) `0`, `1`, `+`, `*`, `•`, `^`, `⁻¹` on pi types.
See `Mathlib/Algebra/Group/Pi/Basic.lean` for the `Monoid` and `Group` instances.
-/

assert_not_exists Monoid Preorder

open Function

variable {ι α β : Type*} {G M N O : ι → Type*}

namespace Pi

-- TODO: Do we really need this definition? If so, where to put it?
/-- The mapping into a product type built from maps into each component. -/
@[simp]
protected def prod {α β : ι → Type*} (f : ∀ i, α i) (g : ∀ i, β i) (i : ι) : α i × β i := (f i, g i)

lemma prod_fst_snd : Pi.prod (Prod.fst : α × β → α) (Prod.snd : α × β → β) = id := rfl
lemma prod_snd_fst : Pi.prod (Prod.snd : α × β → β) (Prod.fst : α × β → α) = .swap := rfl

/-! `1`, `0`, `+`, `*`, `+ᵥ`, `•`, `^`, `-`, `⁻¹`, and `/` are defined pointwise. -/

section One
variable [∀ i, One (M i)] [∀ i, One (N i)] [∀ i, One (O i)]

@[to_additive]
instance instOne : One (∀ i, M i) where one _ := 1

@[to_additive (attr := simp high)]
lemma one_apply (i : ι) : (1 : ∀ i, M i) i = 1 := rfl

@[to_additive]
lemma one_def : (1 : ∀ i, M i) = fun _ ↦ 1 := rfl

variable [DecidableEq ι] {i : ι} {x : M i}

/-- The function supported at `i`, with value `x` there, and `1` elsewhere. -/
@[to_additive "The function supported at `i`, with value `x` there, and `0` elsewhere."]
def mulSingle (i : ι) (x : M i) : ∀ j, M j := Function.update 1 i x

@[to_additive (attr := simp)]
lemma mulSingle_eq_same (i : ι) (x : M i) : mulSingle i x i = x := Function.update_self i x _

@[to_additive (attr := simp)]
lemma mulSingle_eq_of_ne {i i' : ι} (h : i' ≠ i) (x : M i) : mulSingle i x i' = 1 :=
  Function.update_of_ne h x _

/-- Abbreviation for `mulSingle_eq_of_ne h.symm`, for ease of use by `simp`. -/
@[to_additive (attr := simp)
  "Abbreviation for `single_eq_of_ne h.symm`, for ease of use by `simp`."]
lemma mulSingle_eq_of_ne' {i i' : ι} (h : i ≠ i') (x : M i) : mulSingle i x i' = 1 :=
  mulSingle_eq_of_ne h.symm x

@[to_additive (attr := simp)]
lemma mulSingle_one (i : ι) : mulSingle i (1 : M i) = 1 := Function.update_eq_self _ _

@[to_additive (attr := simp)]
lemma mulSingle_eq_one_iff : mulSingle i x = 1 ↔ x = 1 := by
  refine ⟨fun h => ?_, fun h => h.symm ▸ mulSingle_one i⟩
  rw [← mulSingle_eq_same i x, h, one_apply]

@[to_additive]
lemma mulSingle_ne_one_iff : mulSingle i x ≠ 1 ↔ x ≠ 1 :=
  mulSingle_eq_one_iff.ne

@[to_additive]
lemma apply_mulSingle (f' : ∀ i, M i → N i) (hf' : ∀ i, f' i 1 = 1) (i : ι) (x : M i) (j : ι) :
    f' j (mulSingle i x j) = mulSingle i (f' i x) j := by
  simpa only [Pi.one_apply, hf', mulSingle] using Function.apply_update f' 1 i x j

@[to_additive apply_single₂]
lemma apply_mulSingle₂ (f' : ∀ i, M i → N i → O i) (hf' : ∀ i, f' i 1 1 = 1) (i : ι)
    (x : M i) (y : N i) (j : ι) :
    f' j (mulSingle i x j) (mulSingle i y j) = mulSingle i (f' i x y) j := by
  by_cases h : j = i
  · subst h
    simp only [mulSingle_eq_same]
  · simp only [mulSingle_eq_of_ne h, hf']

@[to_additive]
lemma mulSingle_op (op : ∀ i, M i → N i) (h : ∀ i, op i 1 = 1) (i : ι) (x : M i) :
    mulSingle i (op i x) = fun j => op j (mulSingle i x j) :=
  .symm <| funext <| apply_mulSingle op h i x

@[to_additive]
lemma mulSingle_op₂ (op : ∀ i, M i → N i → O i) (h : ∀ i, op i 1 1 = 1) (i : ι) (x : M i)
    (y : N i) : mulSingle i (op i x y) = fun j ↦ op j (mulSingle i x j) (mulSingle i y j) :=
  .symm <| funext <| apply_mulSingle₂ op h i x y

@[to_additive]
lemma mulSingle_injective (i : ι) : Function.Injective (mulSingle i : M i → ∀ i, M i) :=
  Function.update_injective _ i

@[to_additive (attr := simp)]
lemma mulSingle_inj (i : ι) {x y : M i} : mulSingle i x = mulSingle i y ↔ x = y :=
  (mulSingle_injective _).eq_iff

variable {M : Type*} [One M]

/-- On non-dependent functions, `Pi.mulSingle` can be expressed as an `ite` -/
@[to_additive "On non-dependent functions, `Pi.single` can be expressed as an `ite`"]
lemma mulSingle_apply (i : ι) (x : M) (i' : ι) :
    (mulSingle i x : ι → M) i' = if i' = i then x else 1 :=
  Function.update_apply (1 : ι → M) i x i'

-- Porting note: Same as above.
/-- On non-dependent functions, `Pi.mulSingle` is symmetric in the two indices. -/
@[to_additive "On non-dependent functions, `Pi.single` is symmetric in the two indices."]
lemma mulSingle_comm (i : ι) (x : M) (j : ι) :
    (mulSingle i x : ι → M) j = (mulSingle j x : ι → M) i := by simp [mulSingle_apply, eq_comm]

@[to_additive (attr := simp)] lemma _root_.Function.const_one : const α (1 : M) = 1 := rfl

@[to_additive (attr := simp)] lemma one_comp (f : α → β) : (1 : β → M) ∘ f = 1 := rfl
@[to_additive (attr := simp)] lemma comp_one (f : M → β) : f ∘ (1 : α → M) = const α (f 1) := rfl

end One

section Mul
variable [∀ i, Mul (M i)]

@[to_additive]
instance instMul : Mul (∀ i, M i) where mul f g i := f i * g i

@[to_additive (attr := simp)]
lemma mul_apply (f g : ∀ i, M i) (i : ι) : (f * g) i = f i * g i := rfl

@[to_additive]
lemma mul_def (f g : ∀ i, M i) : f * g = fun i ↦ f i * g i := rfl

variable {M : Type*} [Mul M]

@[to_additive (attr := simp)]
lemma _root_.Function.const_mul (a b : M) : const ι a * const ι b = const ι (a * b) := rfl

@[to_additive]
lemma mul_comp (f g : β → M) (z : α → β) : (f * g) ∘ z = f ∘ z * g ∘ z := rfl

end Mul

section Inv
variable [∀ i, Inv (G i)]

@[to_additive]
instance instInv : Inv (∀ i, G i) where inv f i := (f i)⁻¹

@[to_additive (attr := simp)]
lemma inv_apply (f : ∀ i, G i) (i : ι) : f⁻¹ i = (f i)⁻¹ := rfl

@[to_additive]
lemma inv_def (f : ∀ i, G i) : f⁻¹ = fun i ↦ (f i)⁻¹ := rfl

variable {G : Type*} [Inv G]

@[to_additive]
lemma _root_.Function.const_inv (a : G) : (const ι a)⁻¹ = const ι a⁻¹ := rfl

@[to_additive]
lemma inv_comp (f : β → G) (g : α → β) : f⁻¹ ∘ g = (f ∘ g)⁻¹ := rfl
end Inv

section Div
variable [∀ i, Div (G i)]

@[to_additive]
instance instDiv : Div (∀ i, G i) where div f g i := f i / g i

@[to_additive (attr := simp)]
lemma div_apply (f g : ∀ i, G i) (i : ι) : (f / g) i = f i / g i :=rfl

@[to_additive]
lemma div_def (f g : ∀ i, G i) : f / g = fun i ↦ f i / g i := rfl

variable {G : Type*} [Div G]

@[to_additive]
lemma div_comp (f g : β → G) (z : α → β) : (f / g) ∘ z = f ∘ z / g ∘ z := rfl

@[to_additive (attr := simp)]
lemma _root_.Function.const_div (a b : G) : const ι a / const ι b = const ι (a / b) := rfl

end Div

section Pow

@[to_additive]
instance instSMul [∀ i, SMul α (M i)] : SMul α (∀ i, M i) where smul a f i := a • f i

variable [∀ i, Pow (M i) α]

@[to_additive existing instSMul]
instance instPow : Pow (∀ i, M i) α where pow f a i := f i ^ a

@[to_additive (attr := simp, to_additive) (reorder := 5 6) smul_apply]
lemma pow_apply (f : ∀ i, M i) (a : α) (i : ι) : (f ^ a) i = f i ^ a := rfl

@[to_additive (attr := to_additive) (reorder := 5 6) smul_def]
lemma pow_def (f : ∀ i, M i) (a : α) : f ^ a = fun i ↦ f i ^ a := rfl

variable {M : Type*} [Pow M α]

@[to_additive (attr := simp, to_additive) (reorder := 2 3, 5 6) smul_const]
lemma _root_.Function.const_pow (a : M) (b : α) : const ι a ^ b = const ι (a ^ b) := rfl

@[to_additive (attr := to_additive) (reorder := 6 7) smul_comp]
lemma pow_comp (f : β → M) (a : α) (g : ι → β) : (f ^ a) ∘ g = f ∘ g ^ a := rfl

end Pow
end Pi

variable {ι M : Type*} [One M]

@[to_additive (attr := simp)]
lemma Set.range_one [Nonempty ι] : Set.range (1 : ι → M) = {1} := by simp [Set.range, eq_comm]; rfl

@[to_additive]
lemma Set.preimage_one (s : Set M) [Decidable ((1 : M) ∈ s)] :
    (1 : ι → M) ⁻¹' s = if (1 : M) ∈ s then Set.univ else ∅ := by
  split_ifs <;> ext <;> simp [*]; rintro ⟨⟩
