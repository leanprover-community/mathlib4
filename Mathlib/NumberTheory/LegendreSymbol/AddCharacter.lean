/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Algebra.Group.AddChar

#align_import number_theory.legendre_symbol.add_character from "leanprover-community/mathlib"@"0723536a0522d24fc2f159a096fb3304bef77472"

/-!
# Additive characters of finite rings and fields

This file collects some results on additive characters whose domain is (the additive group of)
a finite ring or field.

## Main definitions and results

We define an additive character `ψ` to be *primitive* if `mulShift ψ a` is trivial only when
`a = 0`.

We show that when `ψ` is primitive, then the map `a ↦ mulShift ψ a` is injective
(`AddChar.to_mulShift_inj_of_isPrimitive`) and that `ψ` is primitive when `R` is a field
and `ψ` is nontrivial (`AddChar.IsNontrivial.isPrimitive`).

We also show that there are primitive additive characters on `R` (with suitable
target `R'`) when `R` is a field or `R = ZMod n` (`AddChar.primitiveCharFiniteField`
and `AddChar.primitiveZModChar`).

Finally, we show that the sum of all character values is zero when the character
is nontrivial (and the target is a domain); see `AddChar.sum_eq_zero_of_isNontrivial`.

## Tags

additive character
-/


universe u v

namespace AddChar

section Additive

-- The domain and target of our additive characters. Now we restrict to a ring in the domain.
variable {R : Type u} [CommRing R] {R' : Type v} [CommMonoid R']

/-- An additive character is *primitive* iff all its multiplicative shifts by nonzero
elements are nontrivial. -/
def IsPrimitive (ψ : AddChar R R') : Prop :=
  ∀ a : R, a ≠ 0 → IsNontrivial (mulShift ψ a)
#align add_char.is_primitive AddChar.IsPrimitive

/-- The map associating to `a : R` the multiplicative shift of `ψ` by `a`
is injective when `ψ` is primitive. -/
theorem to_mulShift_inj_of_isPrimitive {ψ : AddChar R R'} (hψ : IsPrimitive ψ) :
    Function.Injective ψ.mulShift := by
  intro a b h
  apply_fun fun x => x * mulShift ψ (-b) at h
  simp only [mulShift_mul, mulShift_zero, add_right_neg] at h
  have h₂ := hψ (a + -b)
  rw [h, isNontrivial_iff_ne_trivial, ← sub_eq_add_neg, sub_ne_zero] at h₂
  exact not_not.mp fun h => h₂ h rfl
#align add_char.to_mul_shift_inj_of_is_primitive AddChar.to_mulShift_inj_of_isPrimitive

-- `AddCommGroup.equiv_direct_sum_zmod_of_fintype`
-- gives the structure theorem for finite abelian groups.
-- This could be used to show that the map above is a bijection.
-- We leave this for a later occasion.
/-- When `R` is a field `F`, then a nontrivial additive character is primitive -/
theorem IsNontrivial.isPrimitive {F : Type u} [Field F] {ψ : AddChar F R'} (hψ : IsNontrivial ψ) :
    IsPrimitive ψ := by
  intro a ha
  cases' hψ with x h
  use a⁻¹ * x
  rwa [mulShift_apply, mul_inv_cancel_left₀ ha]
#align add_char.is_nontrivial.is_primitive AddChar.IsNontrivial.isPrimitive

-- Porting note: Using `structure` gives a timeout, see
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/mysterious.20finsupp.20related.20timeout/near/365719262 and
-- https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/mysterious.20finsupp.20related.20timeout
-- In Lean4, `set_option genInjectivity false in` may solve this issue.
-- can't prove that they always exist (referring to providing an `Inhabited` instance)
/-- Definition for a primitive additive character on a finite ring `R` into a cyclotomic extension
of a field `R'`. It records which cyclotomic extension it is, the character, and the
fact that the character is primitive. -/
-- @[nolint has_nonempty_instance] -- Porting note: removed
def PrimitiveAddChar (R : Type u) [CommRing R] (R' : Type v) [Field R'] :=
  Σ n : ℕ+, Σ' char : AddChar R (CyclotomicField n R'), IsPrimitive char
#align add_char.primitive_add_char AddChar.PrimitiveAddChar

/-- The first projection from `PrimitiveAddChar`, giving the cyclotomic field. -/
noncomputable def PrimitiveAddChar.n {R : Type u} [CommRing R] {R' : Type v} [Field R'] :
    PrimitiveAddChar R R' → ℕ+ := fun χ => χ.1
#align add_char.primitive_add_char.n AddChar.PrimitiveAddChar.n

/-- The second projection from `PrimitiveAddChar`, giving the character. -/
noncomputable def PrimitiveAddChar.char {R : Type u} [CommRing R] {R' : Type v} [Field R'] :
    ∀ χ : PrimitiveAddChar R R', AddChar R (CyclotomicField χ.n R') := fun χ => χ.2.1
#align add_char.primitive_add_char.char AddChar.PrimitiveAddChar.char

/-- The third projection from `PrimitiveAddChar`, showing that `χ.char` is primitive. -/
theorem PrimitiveAddChar.prim {R : Type u} [CommRing R] {R' : Type v} [Field R'] :
    ∀ χ : PrimitiveAddChar R R', IsPrimitive χ.char := fun χ => χ.2.2
#align add_char.primitive_add_char.prim AddChar.PrimitiveAddChar.prim

/-!
### Additive characters on `ZMod n`
-/

section ZModChar

variable {C : Type v} [CommMonoid C]

section ZModCharDef


/-- We can define an additive character on `ZMod n` when we have an `n`th root of unity `ζ : C`. -/
def zmodChar (n : ℕ+) {ζ : C} (hζ : ζ ^ (n : ℕ) = 1) : AddChar (ZMod n) C where
  toFun a := ζ ^ a.val
  map_zero_one' := by simp only [ZMod.val_zero, pow_zero]
  map_add_mul' x y := by simp only [ZMod.val_add, ← pow_eq_pow_mod _ hζ, ← pow_add]
#align add_char.zmod_char AddChar.zmodChar

/-- The additive character on `ZMod n` defined using `ζ` sends `a` to `ζ^a`. -/
theorem zmodChar_apply {n : ℕ+} {ζ : C} (hζ : ζ ^ (n : ℕ) = 1) (a : ZMod n) :
    zmodChar n hζ a = ζ ^ a.val :=
  rfl
#align add_char.zmod_char_apply AddChar.zmodChar_apply

theorem zmodChar_apply' {n : ℕ+} {ζ : C} (hζ : ζ ^ (n : ℕ) = 1) (a : ℕ) :
    zmodChar n hζ a = ζ ^ a := by
  rw [pow_eq_pow_mod a hζ, zmodChar_apply, ZMod.val_nat_cast a]
#align add_char.zmod_char_apply' AddChar.zmodChar_apply'

end ZModCharDef

/-- An additive character on `ZMod n` is nontrivial iff it takes a value `≠ 1` on `1`. -/
theorem zmod_char_isNontrivial_iff (n : ℕ+) (ψ : AddChar (ZMod n) C) :
    IsNontrivial ψ ↔ ψ 1 ≠ 1 := by
  refine' ⟨_, fun h => ⟨1, h⟩⟩
  contrapose!
  rintro h₁ ⟨a, ha⟩
  have ha₁ : a = a.val • (1 : ZMod ↑n) := by
    rw [nsmul_eq_mul, mul_one]; exact (ZMod.nat_cast_zmod_val a).symm
  rw [ha₁, map_nsmul_pow, h₁, one_pow] at ha
  exact ha rfl
#align add_char.zmod_char_is_nontrivial_iff AddChar.zmod_char_isNontrivial_iff

/-- A primitive additive character on `ZMod n` takes the value `1` only at `0`. -/
theorem IsPrimitive.zmod_char_eq_one_iff (n : ℕ+) {ψ : AddChar (ZMod n) C} (hψ : IsPrimitive ψ)
    (a : ZMod n) : ψ a = 1 ↔ a = 0 := by
  refine' ⟨fun h => not_imp_comm.mp (hψ a) _, fun ha => by rw [ha, map_zero_one]⟩
  rw [zmod_char_isNontrivial_iff n (mulShift ψ a), mulShift_apply, mul_one, h, Classical.not_not]
#align add_char.is_primitive.zmod_char_eq_one_iff AddChar.IsPrimitive.zmod_char_eq_one_iff

/-- The converse: if the additive character takes the value `1` only at `0`,
then it is primitive. -/
theorem zmod_char_primitive_of_eq_one_only_at_zero (n : ℕ) (ψ : AddChar (ZMod n) C)
    (hψ : ∀ a, ψ a = 1 → a = 0) : IsPrimitive ψ := by
  refine' fun a ha => (isNontrivial_iff_ne_trivial _).mpr fun hf => _
  have h : mulShift ψ a 1 = (1 : AddChar (ZMod n) C) (1 : ZMod n) :=
    congr_fun (congr_arg (↑) hf) 1
  rw [mulShift_apply, mul_one] at h; norm_cast at h
  exact ha (hψ a h)
#align add_char.zmod_char_primitive_of_eq_one_only_at_zero AddChar.zmod_char_primitive_of_eq_one_only_at_zero

/-- The additive character on `ZMod n` associated to a primitive `n`th root of unity
is primitive -/
theorem zmodChar_primitive_of_primitive_root (n : ℕ+) {ζ : C} (h : IsPrimitiveRoot ζ n) :
    IsPrimitive (zmodChar n ((IsPrimitiveRoot.iff_def ζ n).mp h).left) := by
  apply zmod_char_primitive_of_eq_one_only_at_zero
  intro a ha
  rw [zmodChar_apply, ← pow_zero ζ] at ha
  exact (ZMod.val_eq_zero a).mp (IsPrimitiveRoot.pow_inj h (ZMod.val_lt a) n.pos ha)
#align add_char.zmod_char_primitive_of_primitive_root AddChar.zmodChar_primitive_of_primitive_root

/-- There is a primitive additive character on `ZMod n` if the characteristic of the target
does not divide `n` -/
noncomputable def primitiveZModChar (n : ℕ+) (F' : Type v) [Field F'] (h : (n : F') ≠ 0) :
    PrimitiveAddChar (ZMod n) F' :=
  haveI : NeZero ((n : ℕ) : F') := ⟨h⟩
  ⟨n, zmodChar n (IsCyclotomicExtension.zeta_pow n F' _),
    zmodChar_primitive_of_primitive_root n (IsCyclotomicExtension.zeta_spec n F' _)⟩
#align add_char.primitive_zmod_char AddChar.primitiveZModChar

end ZModChar

end Additive

/-!
### Existence of a primitive additive character on a finite field
-/

/-- There is a primitive additive character on the finite field `F` if the characteristic
of the target is different from that of `F`.
We obtain it as the composition of the trace from `F` to `ZMod p` with a primitive
additive character on `ZMod p`, where `p` is the characteristic of `F`. -/
noncomputable def primitiveCharFiniteField (F F' : Type*) [Field F] [Finite F] [Field F']
    (h : ringChar F' ≠ ringChar F) : PrimitiveAddChar F F' := by
  let p := ringChar F
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime F _⟩
  let pp := p.toPNat hp.1.pos
  have hp₂ : ¬ringChar F' ∣ p := by
    cases' CharP.char_is_prime_or_zero F' (ringChar F') with hq hq
    · exact mt (Nat.Prime.dvd_iff_eq hp.1 (Nat.Prime.ne_one hq)).mp h.symm
    · rw [hq]
      exact fun hf => Nat.Prime.ne_zero hp.1 (zero_dvd_iff.mp hf)
  let ψ := primitiveZModChar pp F' (neZero_iff.mp (NeZero.of_not_dvd F' hp₂))
  letI : Algebra (ZMod p) F := ZMod.algebra _ _
  let ψ' := ψ.char.compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom
  have hψ' : IsNontrivial ψ' := by
    obtain ⟨a, ha⟩ := FiniteField.trace_to_zmod_nondegenerate F one_ne_zero
    rw [one_mul] at ha
    exact ⟨a, fun hf => ha <| (ψ.prim.zmod_char_eq_one_iff pp <| Algebra.trace (ZMod p) F a).mp hf⟩
  exact ⟨ψ.n, ψ', hψ'.isPrimitive⟩
#align add_char.primitive_char_finite_field AddChar.primitiveCharFiniteField

/-!
### The sum of all character values
-/


section sum

open scoped BigOperators

variable {R : Type*} [AddGroup R] [Fintype R] {R' : Type*} [CommRing R']

/-- The sum over the values of a nontrivial additive character vanishes if the target ring
is a domain. -/
theorem sum_eq_zero_of_isNontrivial [IsDomain R'] {ψ : AddChar R R'} (hψ : IsNontrivial ψ) :
    ∑ a, ψ a = 0 := by
  rcases hψ with ⟨b, hb⟩
  have h₁ : ∑ a : R, ψ (b + a) = ∑ a : R, ψ a :=
    Fintype.sum_bijective _ (AddGroup.addLeft_bijective b) _ _ fun x => rfl
  simp_rw [map_add_mul] at h₁
  have h₂ : ∑ a : R, ψ a = Finset.univ.sum ↑ψ := rfl
  rw [← Finset.mul_sum, h₂] at h₁
  exact eq_zero_of_mul_eq_self_left hb h₁
#align add_char.sum_eq_zero_of_is_nontrivial AddChar.sum_eq_zero_of_isNontrivial

/-- The sum over the values of the trivial additive character is the cardinality of the source. -/
theorem sum_eq_card_of_is_trivial {ψ : AddChar R R'} (hψ : ¬IsNontrivial ψ) :
    ∑ a, ψ a = Fintype.card R := by
  simp only [IsNontrivial] at hψ
  push_neg at hψ
  simp only [hψ, Finset.sum_const, Nat.smul_one_eq_coe]
  rfl
#align add_char.sum_eq_card_of_is_trivial AddChar.sum_eq_card_of_is_trivial

end sum

open scoped BigOperators in
/-- The sum over the values of `mulShift ψ b` for `ψ` primitive is zero when `b ≠ 0`
and `#R` otherwise. -/
theorem sum_mulShift {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar R R'} (b : R)
    (hψ : IsPrimitive ψ) : ∑ x : R, ψ (x * b) = if b = 0 then Fintype.card R else 0 := by
  split_ifs with h
  · -- case `b = 0`
    simp only [h, mul_zero, map_zero_one, Finset.sum_const, Nat.smul_one_eq_coe]
    rfl
  · -- case `b ≠ 0`
    simp_rw [mul_comm]
    exact mod_cast sum_eq_zero_of_isNontrivial (hψ b h)
#align add_char.sum_mul_shift AddChar.sum_mulShift

end AddChar
