/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.ZMod.Units
import Mathlib.Analysis.Complex.Polynomial

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

/-- The values of an additive character on a ring of positive characteristic are roots of unity. -/
lemma val_mem_rootsOfUnity (φ : AddChar R R') (a : R) (h : 0 < ringChar R) :
    (φ.val_isUnit a).unit ∈ rootsOfUnity (ringChar R).toPNat' R' := by
  simp only [mem_rootsOfUnity', IsUnit.unit_spec, Nat.toPNat'_coe, h, ↓reduceIte,
    ← map_nsmul_eq_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, map_zero_eq_one]

/-- An additive character is *primitive* iff all its multiplicative shifts by nonzero
elements are nontrivial. -/
def IsPrimitive (ψ : AddChar R R') : Prop := ∀ ⦃a : R⦄, a ≠ 0 → mulShift ψ a ≠ 1
#align add_char.is_primitive AddChar.IsPrimitive

/-- The composition of a primitive additive character with an injective mooid homomorphism
is also primitive. -/
lemma IsPrimitive.compMulHom_of_isPrimitive {R'' : Type*} [CommMonoid R''] {φ : AddChar R R'}
    {f : R' →* R''} (hφ : φ.IsPrimitive) (hf : Function.Injective f) :
    (f.compAddChar φ).IsPrimitive := fun a ha ↦ by
  simpa [DFunLike.ext_iff] using (MonoidHom.compAddChar_injective_right f hf).ne (hφ ha)

/-- The map associating to `a : R` the multiplicative shift of `ψ` by `a`
is injective when `ψ` is primitive. -/
theorem to_mulShift_inj_of_isPrimitive {ψ : AddChar R R'} (hψ : IsPrimitive ψ) :
    Function.Injective ψ.mulShift := by
  intro a b h
  apply_fun fun x => x * mulShift ψ (-b) at h
  simp only [mulShift_mul, mulShift_zero, add_right_neg, mulShift_apply] at h
  simpa [← sub_eq_add_neg, sub_eq_zero] using (hψ . h)
#align add_char.to_mul_shift_inj_of_is_primitive AddChar.to_mulShift_inj_of_isPrimitive

-- `AddCommGroup.equiv_direct_sum_zmod_of_fintype`
-- gives the structure theorem for finite abelian groups.
-- This could be used to show that the map above is a bijection.
-- We leave this for a later occasion.
/-- When `R` is a field `F`, then a nontrivial additive character is primitive -/
theorem IsPrimitive.of_ne_one {F : Type u} [Field F] {ψ : AddChar F R'} (hψ : ψ ≠ 1) :
    IsPrimitive ψ :=
  fun a ha h ↦ hψ <| by simpa [mulShift_mulShift, ha] using congr_arg (mulShift · a⁻¹) h
#align add_char.is_nontrivial.is_primitive AddChar.IsPrimitive.of_ne_one

/-- If `r` is not a unit, then `e.mulShift r` is not primitive. -/
lemma not_isPrimitive_mulShift [Finite R] (e : AddChar R R') {r : R}
    (hr : ¬ IsUnit r) : ¬ IsPrimitive (e.mulShift r) := by
  simp only [IsPrimitive, not_forall]
  simp only [isUnit_iff_mem_nonZeroDivisors_of_finite, mem_nonZeroDivisors_iff, not_forall] at hr
  rcases hr with ⟨x, h, h'⟩
  exact ⟨x, h', by simp only [mulShift_mulShift, mul_comm r, h, mulShift_zero, not_ne_iff]⟩

/-- Definition for a primitive additive character on a finite ring `R` into a cyclotomic extension
of a field `R'`. It records which cyclotomic extension it is, the character, and the
fact that the character is primitive. -/
-- Porting note(#5171): this linter isn't ported yet.
-- can't prove that they always exist (referring to providing an `Inhabited` instance)
-- @[nolint has_nonempty_instance]
structure PrimitiveAddChar (R : Type u) [CommRing R] (R' : Type v) [Field R'] where
  /-- The first projection from `PrimitiveAddChar`, giving the cyclotomic field. -/
  n : ℕ+
  /-- The second projection from `PrimitiveAddChar`, giving the character. -/
  char : AddChar R (CyclotomicField n R')
  /-- The third projection from `PrimitiveAddChar`, showing that `χ.char` is primitive. -/
  prim : IsPrimitive char
#align add_char.primitive_add_char AddChar.PrimitiveAddChar
#align add_char.primitive_add_char.n AddChar.PrimitiveAddChar.n
#align add_char.primitive_add_char.char AddChar.PrimitiveAddChar.char
#align add_char.primitive_add_char.prim AddChar.PrimitiveAddChar.prim

/-!
### Additive characters on `ZMod n`
-/

section ZMod

variable {N : ℕ+} {R : Type*} [CommRing R] (e : AddChar (ZMod N) R)

/-- If `e` is not primitive, then `e.mulShift d = 1` for some proper divisor `d` of `N`. -/
lemma exists_divisor_of_not_isPrimitive (he : ¬e.IsPrimitive) :
    ∃ d : ℕ, d ∣ N ∧ d < N ∧ e.mulShift d = 1 := by
  simp_rw [IsPrimitive, not_forall, not_ne_iff] at he
  rcases he with ⟨b, hb_ne, hb⟩
  -- We have `AddChar.mulShift e b = 1`, but `b ≠ 0`.
  obtain ⟨d, hd, u, hu, rfl⟩ := b.eq_unit_mul_divisor
  refine ⟨d, hd, lt_of_le_of_ne (Nat.le_of_dvd N.pos hd) ?_, ?_⟩
  · exact fun h ↦ by simp only [h, ZMod.natCast_self, mul_zero, ne_eq, not_true_eq_false] at hb_ne
  · rw [← mulShift_unit_eq_one_iff _ hu, ← hb, mul_comm]
    ext1 y
    rw [mulShift_apply, mulShift_apply, mulShift_apply, mul_assoc]

end ZMod

section ZModChar

variable {C : Type v} [CommMonoid C]

section ZModCharDef


/-- We can define an additive character on `ZMod n` when we have an `n`th root of unity `ζ : C`. -/
def zmodChar (n : ℕ+) {ζ : C} (hζ : ζ ^ (n : ℕ) = 1) : AddChar (ZMod n) C where
  toFun a := ζ ^ a.val
  map_zero_eq_one' := by simp only [ZMod.val_zero, pow_zero]
  map_add_eq_mul' x y := by simp only [ZMod.val_add, ← pow_eq_pow_mod _ hζ, ← pow_add]
#align add_char.zmod_char AddChar.zmodChar

/-- The additive character on `ZMod n` defined using `ζ` sends `a` to `ζ^a`. -/
theorem zmodChar_apply {n : ℕ+} {ζ : C} (hζ : ζ ^ (n : ℕ) = 1) (a : ZMod n) :
    zmodChar n hζ a = ζ ^ a.val :=
  rfl
#align add_char.zmod_char_apply AddChar.zmodChar_apply

theorem zmodChar_apply' {n : ℕ+} {ζ : C} (hζ : ζ ^ (n : ℕ) = 1) (a : ℕ) :
    zmodChar n hζ a = ζ ^ a := by
  rw [pow_eq_pow_mod a hζ, zmodChar_apply, ZMod.val_natCast a]
#align add_char.zmod_char_apply' AddChar.zmodChar_apply'

end ZModCharDef

/-- An additive character on `ZMod n` is nontrivial iff it takes a value `≠ 1` on `1`. -/
theorem zmod_char_ne_one_iff (n : ℕ+) (ψ : AddChar (ZMod n) C) : ψ ≠ 1 ↔ ψ 1 ≠ 1 := by
  rw [ne_one_iff]
  refine ⟨?_, fun h => ⟨_, h⟩⟩
  contrapose!
  rintro h₁ a
  have ha₁ : a = a.val • (1 : ZMod ↑n) := by
    rw [nsmul_eq_mul, mul_one]; exact (ZMod.natCast_zmod_val a).symm
  rw [ha₁, map_nsmul_eq_pow, h₁, one_pow]
#align add_char.zmod_char_is_nontrivial_iff AddChar.zmod_char_ne_one_iff

/-- A primitive additive character on `ZMod n` takes the value `1` only at `0`. -/
theorem IsPrimitive.zmod_char_eq_one_iff (n : ℕ+) {ψ : AddChar (ZMod n) C} (hψ : IsPrimitive ψ)
    (a : ZMod n) : ψ a = 1 ↔ a = 0 := by
  refine ⟨fun h => not_imp_comm.mp (@hψ a) ?_, fun ha => by rw [ha, map_zero_eq_one]⟩
  rw [zmod_char_ne_one_iff n (mulShift ψ a), mulShift_apply, mul_one, h, Classical.not_not]
#align add_char.is_primitive.zmod_char_eq_one_iff AddChar.IsPrimitive.zmod_char_eq_one_iff

/-- The converse: if the additive character takes the value `1` only at `0`,
then it is primitive. -/
theorem zmod_char_primitive_of_eq_one_only_at_zero (n : ℕ) (ψ : AddChar (ZMod n) C)
    (hψ : ∀ a, ψ a = 1 → a = 0) : IsPrimitive ψ := by
  refine fun a ha hf => ?_
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
noncomputable def FiniteField.primitiveChar (F F' : Type*) [Field F] [Finite F] [Field F']
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
  have hψ' : ψ' ≠ 1 := by
    obtain ⟨a, ha⟩ := FiniteField.trace_to_zmod_nondegenerate F one_ne_zero
    rw [one_mul] at ha
    exact ne_one_iff.2
      ⟨a, fun hf => ha <| (ψ.prim.zmod_char_eq_one_iff pp <| Algebra.trace (ZMod p) F a).mp hf⟩
  exact ⟨ψ.n, ψ', IsPrimitive.of_ne_one hψ'⟩
#align add_char.primitive_char_finite_field AddChar.FiniteField.primitiveChar
@[deprecated (since := "2024-05-30")] alias primitiveCharFiniteField := FiniteField.primitiveChar

/-!
### The sum of all character values
-/

section sum

variable {R : Type*} [AddGroup R] [Fintype R] {R' : Type*} [CommRing R']

/-- The sum over the values of a nontrivial additive character vanishes if the target ring
is a domain. -/
theorem sum_eq_zero_of_ne_one [IsDomain R'] {ψ : AddChar R R'} (hψ : ψ ≠ 1) : ∑ a, ψ a = 0 := by
  rcases ne_one_iff.1 hψ with ⟨b, hb⟩
  have h₁ : ∑ a : R, ψ (b + a) = ∑ a : R, ψ a :=
    Fintype.sum_bijective _ (AddGroup.addLeft_bijective b) _ _ fun x => rfl
  simp_rw [map_add_eq_mul] at h₁
  have h₂ : ∑ a : R, ψ a = Finset.univ.sum ↑ψ := rfl
  rw [← Finset.mul_sum, h₂] at h₁
  exact eq_zero_of_mul_eq_self_left hb h₁
#align add_char.sum_eq_zero_of_is_nontrivial AddChar.sum_eq_zero_of_ne_one

/-- The sum over the values of the trivial additive character is the cardinality of the source. -/
theorem sum_eq_card_of_eq_one {ψ : AddChar R R'} (hψ : ψ = 1) :
    ∑ a, ψ a = Fintype.card R := by simp [hψ]
#align add_char.sum_eq_card_of_is_trivial AddChar.sum_eq_card_of_eq_one

end sum

/-- The sum over the values of `mulShift ψ b` for `ψ` primitive is zero when `b ≠ 0`
and `#R` otherwise. -/
theorem sum_mulShift {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar R R'} (b : R)
    (hψ : IsPrimitive ψ) : ∑ x : R, ψ (x * b) = if b = 0 then Fintype.card R else 0 := by
  split_ifs with h
  · -- case `b = 0`
    simp only [h, mul_zero, map_zero_eq_one, Finset.sum_const, Nat.smul_one_eq_cast]
    rfl
  · -- case `b ≠ 0`
    simp_rw [mul_comm]
    exact mod_cast sum_eq_zero_of_ne_one (hψ h)
#align add_char.sum_mul_shift AddChar.sum_mulShift

/-!
### Complex-valued additive characters
-/

section Ring

variable {R : Type*} [CommRing R]

/-- Post-composing an additive character to `ℂ` with complex conjugation gives the inverse
character. -/
lemma starComp_eq_inv (hR : 0 < ringChar R) {φ : AddChar R ℂ} :
    (starRingEnd ℂ).compAddChar φ = φ⁻¹ := by
  ext1 a
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_compAddChar, MonoidHom.coe_coe,
    Function.comp_apply, inv_apply']
  have H := Complex.norm_eq_one_of_mem_rootsOfUnity <| φ.val_mem_rootsOfUnity a hR
  exact (Complex.inv_eq_conj H).symm

lemma starComp_apply (hR : 0 < ringChar R) {φ : AddChar R ℂ} (a : R) :
    (starRingEnd ℂ) (φ a) = φ⁻¹ a := by
  rw [← starComp_eq_inv hR]
  rfl

end Ring

section Field

variable (F : Type*) [Field F] [Finite F] [DecidableEq F]

private lemma ringChar_ne : ringChar ℂ ≠ ringChar F := by
  simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite F).symm

/--  A primitive additive character on the finite field `F` with values in `ℂ`. -/
noncomputable def FiniteField.primitiveChar_to_Complex : AddChar F ℂ := by
  refine MonoidHom.compAddChar ?_ (primitiveChar F ℂ <| ringChar_ne F).char
  exact (IsCyclotomicExtension.algEquiv ?n ℂ (CyclotomicField ?n ℂ) ℂ : CyclotomicField ?n ℂ →* ℂ)

lemma FiniteField.primitiveChar_to_Complex_isPrimitive :
    (primitiveChar_to_Complex F).IsPrimitive := by
  refine IsPrimitive.compMulHom_of_isPrimitive (PrimitiveAddChar.prim _) ?_
  let nn := (primitiveChar F ℂ <| ringChar_ne F).n
  exact (IsCyclotomicExtension.algEquiv nn ℂ (CyclotomicField nn ℂ) ℂ).injective

end Field

end AddChar
