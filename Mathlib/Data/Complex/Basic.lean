/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.GroupWithZero.Bitwise

#align_import data.complex.basic from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# The complex numbers

The complex numbers are modelled as ℝ^2 in the obvious way and it is shown that they form a field
of characteristic zero. The result that the complex numbers are algebraically closed, see
`FieldTheory.AlgebraicClosure`.
-/


open BigOperators

open Set Function

/-! ### Definition and basic arithmetic -/


/-- Complex numbers consist of two `Real`s: a real part `re` and an imaginary part `im`. -/
structure Complex : Type where
  re : ℝ
  im : ℝ


notation "ℂ" => Complex

namespace Complex

open ComplexConjugate

noncomputable instance : DecidableEq ℂ :=
  Classical.decEq _

/-- The equivalence between the complex numbers and `ℝ × ℝ`. -/
@[simps apply]
def equivRealProd : ℂ ≃ ℝ × ℝ where
  toFun z := ⟨z.re, z.im⟩
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

@[simp]
theorem eta : ∀ z : ℂ, Complex.mk z.re z.im = z
  | ⟨_, _⟩ => rfl

@[ext]
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

theorem ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
  ⟨fun H => by simp [H], fun h => ext h.1 h.2⟩

theorem re_surjective : Surjective re := fun x => ⟨⟨x, 0⟩, rfl⟩

theorem im_surjective : Surjective im := fun y => ⟨⟨0, y⟩, rfl⟩

@[simp]
theorem range_re : range re = univ :=
  re_surjective.range_eq

@[simp]
theorem range_im : range im = univ :=
  im_surjective.range_eq

-- Porting note: refactored instance to allow `norm_cast` to work
/-- The natural inclusion of the real numbers into the complex numbers.
The name `Complex.ofReal` is reserved for the bundled homomorphism. -/
@[coe]
def ofReal' (r : ℝ) : ℂ :=
  ⟨r, 0⟩
instance : Coe ℝ ℂ :=
  ⟨ofReal'⟩

@[simp, norm_cast]
theorem ofReal_re (r : ℝ) : Complex.re (r : ℂ) = r :=
  rfl

@[simp, norm_cast]
theorem ofReal_im (r : ℝ) : (r : ℂ).im = 0 :=
  rfl

theorem ofReal_def (r : ℝ) : (r : ℂ) = ⟨r, 0⟩ :=
  rfl

@[simp, norm_cast]
theorem ofReal_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w :=
  ⟨congrArg re, by apply congrArg⟩

-- Porting note: made coercion explicit
theorem ofReal_injective : Function.Injective ((↑) : ℝ → ℂ) := fun _ _ => congrArg re

-- Porting note: made coercion explicit
instance canLift : CanLift ℂ ℝ (↑) fun z => z.im = 0 where
  prf z hz := ⟨z.re, ext rfl hz.symm⟩

/-- The product of a set on the real axis and a set on the imaginary axis of the complex plane,
denoted by `s ×ℂ t`. -/
def Set.reProdIm (s t : Set ℝ) : Set ℂ :=
  re ⁻¹' s ∩ im ⁻¹' t

infixl:72 " ×ℂ " => Set.reProdIm

theorem mem_reProdIm {z : ℂ} {s t : Set ℝ} : z ∈ s ×ℂ t ↔ z.re ∈ s ∧ z.im ∈ t :=
  Iff.rfl

instance : Zero ℂ :=
  ⟨(0 : ℝ)⟩

instance : Inhabited ℂ :=
  ⟨0⟩

@[simp]
theorem zero_re : (0 : ℂ).re = 0 :=
  rfl

@[simp]
theorem zero_im : (0 : ℂ).im = 0 :=
  rfl

@[simp, norm_cast]
theorem ofReal_zero : ((0 : ℝ) : ℂ) = 0 :=
  rfl

@[simp]
theorem ofReal_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 :=
  ofReal_inj

theorem ofReal_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 :=
  not_congr ofReal_eq_zero

instance : One ℂ :=
  ⟨(1 : ℝ)⟩

@[simp]
theorem one_re : (1 : ℂ).re = 1 :=
  rfl

@[simp]
theorem one_im : (1 : ℂ).im = 0 :=
  rfl

@[simp, norm_cast]
theorem ofReal_one : ((1 : ℝ) : ℂ) = 1 :=
  rfl

@[simp]
theorem ofReal_eq_one {z : ℝ} : (z : ℂ) = 1 ↔ z = 1 :=
  ofReal_inj

theorem ofReal_ne_one {z : ℝ} : (z : ℂ) ≠ 1 ↔ z ≠ 1 :=
  not_congr ofReal_eq_one

instance : Add ℂ :=
  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp]
theorem add_re (z w : ℂ) : (z + w).re = z.re + w.re :=
  rfl

@[simp]
theorem add_im (z w : ℂ) : (z + w).im = z.im + w.im :=
  rfl

section
set_option linter.deprecated false
@[simp]
theorem bit0_re (z : ℂ) : (bit0 z).re = bit0 z.re :=
  rfl

@[simp]
theorem bit1_re (z : ℂ) : (bit1 z).re = bit1 z.re :=
  rfl

@[simp]
theorem bit0_im (z : ℂ) : (bit0 z).im = bit0 z.im :=
  Eq.refl _

@[simp]
theorem bit1_im (z : ℂ) : (bit1 z).im = bit0 z.im :=
  add_zero _

@[simp, norm_cast]
theorem ofReal_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
  ext_iff.2 <| by simp [ofReal']

@[simp, norm_cast]
theorem ofReal_bit0 (r : ℝ) : ((bit0 r : ℝ) : ℂ) = bit0 (r : ℂ) :=
  ext_iff.2 <| by simp [bit0]

@[simp, norm_cast]
theorem ofReal_bit1 (r : ℝ) : ((bit1 r : ℝ) : ℂ) = bit1 (r : ℂ) :=
  ext_iff.2 <| by simp [bit1]

end

instance : Neg ℂ :=
  ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp]
theorem neg_re (z : ℂ) : (-z).re = -z.re :=
  rfl

@[simp]
theorem neg_im (z : ℂ) : (-z).im = -z.im :=
  rfl

@[simp, norm_cast]
theorem ofReal_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r :=
  ext_iff.2 <| by simp [ofReal']

instance : Sub ℂ :=
  ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

instance : Mul ℂ :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp]
theorem mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im :=
  rfl

@[simp]
theorem mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re :=
  rfl

@[simp, norm_cast]
theorem ofReal_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s :=
  ext_iff.2 <| by simp [ofReal']

theorem ofReal_mul_re (r : ℝ) (z : ℂ) : (↑r * z).re = r * z.re := by simp [ofReal']

theorem ofReal_mul_im (r : ℝ) (z : ℂ) : (↑r * z).im = r * z.im := by simp [ofReal']

theorem ofReal_mul' (r : ℝ) (z : ℂ) : ↑r * z = ⟨r * z.re, r * z.im⟩ :=
  ext (ofReal_mul_re _ _) (ofReal_mul_im _ _)

/-! ### The imaginary unit, `I` -/


/-- The imaginary unit. -/
def I : ℂ :=
  ⟨0, 1⟩

@[simp]
theorem I_re : I.re = 0 :=
  rfl

@[simp]
theorem I_im : I.im = 1 :=
  rfl

@[simp]
theorem I_mul_I : I * I = -1 :=
  ext_iff.2 <| by simp

theorem I_mul (z : ℂ) : I * z = ⟨-z.im, z.re⟩ :=
  ext_iff.2 <| by simp

theorem I_ne_zero : (I : ℂ) ≠ 0 :=
  mt (congr_arg im) zero_ne_one.symm

theorem mk_eq_add_mul_I (a b : ℝ) : Complex.mk a b = a + b * I :=
  ext_iff.2 <| by simp [ofReal']

@[simp]
theorem re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z :=
  ext_iff.2 <| by simp [ofReal']

theorem mul_I_re (z : ℂ) : (z * I).re = -z.im := by simp

theorem mul_I_im (z : ℂ) : (z * I).im = z.re := by simp

theorem I_mul_re (z : ℂ) : (I * z).re = -z.im := by simp

theorem I_mul_im (z : ℂ) : (I * z).im = z.re := by simp

@[simp]
theorem equivRealProd_symm_apply (p : ℝ × ℝ) : equivRealProd.symm p = p.1 + p.2 * I := by
  ext <;> simp [Complex.equivRealProd, ofReal']

/-! ### Commutative ring instance and lemmas -/


/- We use a nonstandard formula for the `ℕ` and `ℤ` actions to make sure there is no
diamond from the other actions they inherit through the `ℝ`-action on `ℂ` and action transitivity
defined in `Data.Complex.Module`. -/
instance : Nontrivial ℂ :=
  pullback_nonzero re rfl rfl

-- porting note: moved from `Module/Data/Complex/Basic.lean`
section SMul

variable {R : Type*} [SMul R ℝ]

/- The useless `0` multiplication in `smul` is to make sure that
`RestrictScalars.module ℝ ℂ ℂ = Complex.module` definitionally. -/
instance instSMulRealComplex : SMul R ℂ where
  smul r x := ⟨r • x.re - 0 * x.im, r • x.im + 0 * x.re⟩

theorem smul_re (r : R) (z : ℂ) : (r • z).re = r • z.re := by simp [(· • ·), SMul.smul]

theorem smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im := by simp [(· • ·), SMul.smul]

@[simp]
theorem real_smul {x : ℝ} {z : ℂ} : x • z = x * z :=
  rfl

end SMul

-- Porting note: proof needed modifications and rewritten fields
instance addCommGroup : AddCommGroup ℂ :=
  { zero := (0 : ℂ)
    add := (· + ·)
    neg := Neg.neg
    sub := Sub.sub
    nsmul := fun n z => n • z
    zsmul := fun n z => n • z
    zsmul_zero' := by intros; ext <;> simp [smul_re, smul_im]
    nsmul_zero := by intros; ext <;> simp [smul_re, smul_im]
    nsmul_succ := by
      intros; ext <;> simp [AddMonoid.nsmul_succ, add_mul, add_comm,
        smul_re, smul_im]
    zsmul_succ' := by
      intros; ext <;> simp [SubNegMonoid.zsmul_succ', add_mul, add_comm,
        smul_re, smul_im]
    zsmul_neg' := by
      intros; ext <;> simp [zsmul_neg', add_mul, smul_re, smul_im]
    add_assoc := by intros; ext <;> simp [add_assoc]
    zero_add := by intros; ext <;> simp
    add_zero := by intros; ext <;> simp
    add_comm := by intros; ext <;> simp [add_comm]
    add_left_neg := by intros; ext <;> simp }


instance Complex.addGroupWithOne : AddGroupWithOne ℂ :=
  { Complex.addCommGroup with
    natCast := fun n => ⟨n, 0⟩
    natCast_zero := by
      ext <;> simp [Nat.cast, AddMonoidWithOne.natCast_zero]
    natCast_succ := fun _ => by ext <;> simp [Nat.cast, AddMonoidWithOne.natCast_succ]
    intCast := fun n => ⟨n, 0⟩
    intCast_ofNat := fun _ => by ext <;> rfl
    intCast_negSucc := fun n => by
      ext
      · simp [AddGroupWithOne.intCast_negSucc]
        show -(1: ℝ) + (-n) = -(↑(n + 1))
        simp [Nat.cast_add, add_comm]
      · simp [AddGroupWithOne.intCast_negSucc]
        show im ⟨n, 0⟩ = 0
        rfl
    one := 1 }

-- Porting note: proof needed modifications and rewritten fields
instance commRing : CommRing ℂ :=
  { Complex.addGroupWithOne with
    mul := (· * ·)
    npow := @npowRec _ ⟨(1 : ℂ)⟩ ⟨(· * ·)⟩
    add_comm := by intros; ext <;> simp [add_comm]
    left_distrib := by
      intros; ext <;> simp [mul_re, mul_im] <;> ring
    right_distrib := by
      intros; ext <;> simp [mul_re, mul_im] <;> ring
    zero_mul := by intros; ext <;> simp [zero_mul]
    mul_zero := by intros; ext <;> simp [mul_zero]
    mul_assoc := by intros; ext <;> simp [mul_assoc] <;> ring
    one_mul := by intros; ext <;> simp [one_mul]
    mul_one := by intros; ext <;> simp [mul_one]
    mul_comm := by intros; ext <;> simp [mul_comm]; ring }

/-- This shortcut instance ensures we do not find `Ring` via the noncomputable `Complex.field`
instance. -/
instance : Ring ℂ := by infer_instance

/-- This shortcut instance ensures we do not find `CommSemiring` via the noncomputable
`Complex.field` instance. -/
instance : CommSemiring ℂ :=
  inferInstance

-- porting note: added due to changes in typeclass search order
/-- This shortcut instance ensures we do not find `Semiring` via the noncomputable
`Complex.field` instance. -/
instance : Semiring ℂ :=
  inferInstance

/-- The "real part" map, considered as an additive group homomorphism. -/
def reAddGroupHom : ℂ →+ ℝ where
  toFun := re
  map_zero' := zero_re
  map_add' := add_re

@[simp]
theorem coe_reAddGroupHom : (reAddGroupHom : ℂ → ℝ) = re :=
  rfl

/-- The "imaginary part" map, considered as an additive group homomorphism. -/
def imAddGroupHom : ℂ →+ ℝ where
  toFun := im
  map_zero' := zero_im
  map_add' := add_im

@[simp]
theorem coe_imAddGroupHom : (imAddGroupHom : ℂ → ℝ) = im :=
  rfl

section
set_option linter.deprecated false
@[simp]
theorem I_pow_bit0 (n : ℕ) : I ^ bit0 n = (-1) ^ n := by rw [pow_bit0', Complex.I_mul_I]

@[simp]
theorem I_pow_bit1 (n : ℕ) : I ^ bit1 n = (-1) ^ n * I := by rw [pow_bit1', Complex.I_mul_I]

--Porting note: new theorem
@[simp, norm_cast]
theorem ofReal_ofNat (n : ℕ) [n.AtLeastTwo] :
    ((no_index (OfNat.ofNat n) : ℝ) : ℂ) = OfNat.ofNat n :=
  rfl

@[simp]
theorem re_ofNat (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : ℂ).re = OfNat.ofNat n :=
  rfl

@[simp]
theorem im_ofNat (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : ℂ).im = 0 :=
  rfl

end
/-! ### Complex conjugation -/


/-- This defines the complex conjugate as the `star` operation of the `StarRing ℂ`. It
is recommended to use the ring endomorphism version `starRingEnd`, available under the
notation `conj` in the locale `ComplexConjugate`. -/
instance : StarRing ℂ where
  star z := ⟨z.re, -z.im⟩
  star_involutive x := by simp only [eta, neg_neg]
  star_mul a b := by ext <;> simp [add_comm] <;> ring
  star_add a b := by ext <;> simp [add_comm]

@[simp]
theorem conj_re (z : ℂ) : (conj z).re = z.re :=
  rfl

@[simp]
theorem conj_im (z : ℂ) : (conj z).im = -z.im :=
  rfl

theorem conj_ofReal (r : ℝ) : conj (r : ℂ) = r :=
  ext_iff.2 <| by simp [star]

@[simp]
theorem conj_I : conj I = -I :=
  ext_iff.2 <| by simp
  set_option linter.uppercaseLean3 false in


section
set_option linter.deprecated false
theorem conj_bit0 (z : ℂ) : conj (bit0 z) = bit0 (conj z) :=
  ext_iff.2 <| by simp [bit0]

theorem conj_bit1 (z : ℂ) : conj (bit1 z) = bit1 (conj z) :=
  ext_iff.2 <| by simp [bit0]
end
-- @[simp]
/- Porting note: `simp` attribute removed as the result could be proved
by `simp only [@map_neg, Complex.conj_i, @neg_neg]`
-/
theorem conj_neg_I : conj (-I) = I :=
  ext_iff.2 <| by simp

theorem conj_eq_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
  ⟨fun h => ⟨z.re, ext rfl <| eq_zero_of_neg_eq (congr_arg im h)⟩, fun ⟨h, e⟩ => by
    rw [e, conj_ofReal]⟩

theorem conj_eq_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
  conj_eq_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp [ofReal'], fun h => ⟨_, h.symm⟩⟩

theorem conj_eq_iff_im {z : ℂ} : conj z = z ↔ z.im = 0 :=
  ⟨fun h => add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp (congr_arg im h)), fun h =>
    ext rfl (neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero.mpr h))⟩

-- `simpNF` complains about this being provable by `IsROrC.star_def` even
-- though it's not imported by this file.
-- Porting note: linter `simpNF` not found
@[simp]
theorem star_def : (Star.star : ℂ → ℂ) = conj :=
  rfl

/-! ### Norm squared -/


/-- The norm squared function. -/
-- Porting note: `@[pp_nodot]` not found
-- @[pp_nodot]
def normSq : ℂ →*₀ ℝ where
  toFun z := z.re * z.re + z.im * z.im
  map_zero' := by simp
  map_one' := by simp
  map_mul' z w := by
    dsimp
    ring

theorem normSq_apply (z : ℂ) : normSq z = z.re * z.re + z.im * z.im :=
  rfl

@[simp]
theorem normSq_ofReal (r : ℝ) : normSq r = r * r := by
  simp [normSq, ofReal']

@[simp]
theorem normSq_mk (x y : ℝ) : normSq ⟨x, y⟩ = x * x + y * y :=
  rfl

theorem normSq_add_mul_I (x y : ℝ) : normSq (x + y * I) = x ^ 2 + y ^ 2 := by
  rw [← mk_eq_add_mul_I, normSq_mk, sq, sq]

theorem normSq_eq_conj_mul_self {z : ℂ} : (normSq z : ℂ) = conj z * z := by
  ext <;> simp [normSq, mul_comm, ofReal']

-- @[simp]
/- Porting note: `simp` attribute removed as linter reports this can be proved
by `simp only [@map_zero]` -/
theorem normSq_zero : normSq 0 = 0 :=
  normSq.map_zero

-- @[simp]
/- Porting note: `simp` attribute removed as linter reports this can be proved
by `simp only [@map_one]` -/
theorem normSq_one : normSq 1 = 1 :=
  normSq.map_one

@[simp]
theorem normSq_ofNat (n : ℕ) [n.AtLeastTwo] :
    normSq (no_index (OfNat.ofNat n : ℂ)) = OfNat.ofNat n * OfNat.ofNat n := by
  simp [normSq]

@[simp]
theorem normSq_I : normSq I = 1 := by simp [normSq]

theorem normSq_nonneg (z : ℂ) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

@[simp]
theorem range_normSq : range normSq = Ici 0 :=
  Subset.antisymm (range_subset_iff.2 normSq_nonneg) fun x hx =>
    ⟨Real.sqrt x, by rw [normSq_ofReal, Real.mul_self_sqrt hx]⟩

theorem normSq_eq_zero {z : ℂ} : normSq z = 0 ↔ z = 0 :=
  ⟨fun h =>
    ext (eq_zero_of_mul_self_add_mul_self_eq_zero h)
      (eq_zero_of_mul_self_add_mul_self_eq_zero <| (add_comm _ _).trans h),
    fun h => h.symm ▸ normSq_zero⟩

@[simp]
theorem normSq_pos {z : ℂ} : 0 < normSq z ↔ z ≠ 0 :=
  (normSq_nonneg z).lt_iff_ne.trans <| not_congr (eq_comm.trans normSq_eq_zero)

@[simp]
theorem normSq_neg (z : ℂ) : normSq (-z) = normSq z := by simp [normSq]

@[simp]
theorem normSq_conj (z : ℂ) : normSq (conj z) = normSq z := by simp [normSq]

theorem normSq_mul (z w : ℂ) : normSq (z * w) = normSq z * normSq w :=
  normSq.map_mul z w

theorem normSq_add (z w : ℂ) : normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re := by
  dsimp [normSq]; ring

theorem re_sq_le_normSq (z : ℂ) : z.re * z.re ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)

theorem im_sq_le_normSq (z : ℂ) : z.im * z.im ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)

theorem mul_conj (z : ℂ) : z * conj z = normSq z :=
  ext_iff.2 <| by simp [normSq, mul_comm, sub_eq_neg_add, add_comm, ofReal']

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
  ext_iff.2 <| by simp [two_mul, ofReal']

/-- The coercion `ℝ → ℂ` as a `RingHom`. -/
def ofReal : ℝ →+* ℂ where
  toFun x := (x : ℂ)
  map_one' := ofReal_one
  map_zero' := ofReal_zero
  map_mul' := ofReal_mul
  map_add' := ofReal_add

@[simp]
theorem ofReal_eq_coe (r : ℝ) : ofReal r = r :=
  rfl

@[simp]
theorem I_sq : I ^ 2 = -1 := by rw [sq, I_mul_I]

@[simp]
theorem sub_re (z w : ℂ) : (z - w).re = z.re - w.re :=
  rfl

@[simp]
theorem sub_im (z w : ℂ) : (z - w).im = z.im - w.im :=
  rfl

@[simp, norm_cast]
theorem ofReal_sub (r s : ℝ) : ((r - s : ℝ) : ℂ) = r - s :=
  ext_iff.2 <| by simp [ofReal']

@[simp, norm_cast]
theorem ofReal_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n := by
  induction n <;> simp [*, ofReal_mul, pow_succ]

theorem sub_conj (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I :=
  ext_iff.2 <| by simp [two_mul, sub_eq_add_neg, ofReal']

theorem normSq_sub (z w : ℂ) : normSq (z - w) = normSq z + normSq w - 2 * (z * conj w).re := by
  rw [sub_eq_add_neg, normSq_add]
  simp only [RingHom.map_neg, mul_neg, neg_re, normSq_neg]
  ring

/-! ### Inversion -/


noncomputable instance : Inv ℂ :=
  ⟨fun z => conj z * ((normSq z)⁻¹ : ℝ)⟩

theorem inv_def (z : ℂ) : z⁻¹ = conj z * ((normSq z)⁻¹ : ℝ) :=
  rfl

@[simp]
theorem inv_re (z : ℂ) : z⁻¹.re = z.re / normSq z := by simp [inv_def, division_def, ofReal']

@[simp]
theorem inv_im (z : ℂ) : z⁻¹.im = -z.im / normSq z := by simp [inv_def, division_def, ofReal']

@[simp, norm_cast]
theorem ofReal_inv (r : ℝ) : ((r⁻¹ : ℝ) : ℂ) = (r : ℂ)⁻¹ :=
  ext_iff.2 <| by simp [ofReal']

protected theorem inv_zero : (0⁻¹ : ℂ) = 0 := by
  rw [← ofReal_zero, ← ofReal_inv, inv_zero]

protected theorem mul_inv_cancel {z : ℂ} (h : z ≠ 0) : z * z⁻¹ = 1 := by
  rw [inv_def, ← mul_assoc, mul_conj, ← ofReal_mul, mul_inv_cancel (mt normSq_eq_zero.1 h),
    ofReal_one]

noncomputable instance : RatCast ℂ where
  ratCast := Rat.castRec

/-! ### Cast lemmas -/

@[simp, norm_cast]
theorem ofReal_nat_cast (n : ℕ) : ((n : ℝ) : ℂ) = n :=
  map_natCast ofReal n

@[simp, norm_cast]
theorem nat_cast_re (n : ℕ) : (n : ℂ).re = n := by rw [← ofReal_nat_cast, ofReal_re]

@[simp, norm_cast]
theorem nat_cast_im (n : ℕ) : (n : ℂ).im = 0 := by rw [← ofReal_nat_cast, ofReal_im]

@[simp, norm_cast]
theorem ofReal_int_cast (n : ℤ) : ((n : ℝ) : ℂ) = n :=
  map_intCast ofReal n

@[simp, norm_cast]
theorem int_cast_re (n : ℤ) : (n : ℂ).re = n := by rw [← ofReal_int_cast, ofReal_re]

@[simp, norm_cast]
theorem int_cast_im (n : ℤ) : (n : ℂ).im = 0 := by rw [← ofReal_int_cast, ofReal_im]

@[simp, norm_cast]
theorem rat_cast_im (q : ℚ) : (q : ℂ).im = 0 := by
  show (Rat.castRec q : ℂ).im = 0
  cases q
  simp [Rat.castRec]

@[simp, norm_cast]
theorem rat_cast_re (q : ℚ) : (q : ℂ).re = (q : ℝ) := by
  show (Rat.castRec q : ℂ).re = _
  cases q
  simp [Rat.castRec, normSq, Rat.mk_eq_divInt, Rat.mkRat_eq_div, div_eq_mul_inv, *]

/-! ### Field instance and lemmas -/

noncomputable instance instField : Field ℂ :=
{ qsmul := fun n z => n • z
  qsmul_eq_mul' := fun n z => ext_iff.2 <| by simp [Rat.smul_def, smul_re, smul_im]
  inv := Inv.inv
  mul_inv_cancel := @Complex.mul_inv_cancel
  inv_zero := Complex.inv_zero }

section
set_option linter.deprecated false
@[simp]
theorem I_zpow_bit0 (n : ℤ) : I ^ bit0 n = (-1) ^ n := by rw [zpow_bit0', I_mul_I]

@[simp]
theorem I_zpow_bit1 (n : ℤ) : I ^ bit1 n = (-1) ^ n * I := by rw [zpow_bit1', I_mul_I]

end

theorem div_re (z w : ℂ) : (z / w).re = z.re * w.re / normSq w + z.im * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]

theorem div_im (z w : ℂ) : (z / w).im = z.im * w.re / normSq w - z.re * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]

theorem conj_inv (x : ℂ) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv' _

@[simp, norm_cast]
theorem ofReal_div (r s : ℝ) : ((r / s : ℝ) : ℂ) = r / s :=
  map_div₀ ofReal r s

@[simp, norm_cast]
theorem ofReal_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n :=
  map_zpow₀ ofReal r n

@[simp]
theorem div_I (z : ℂ) : z / I = -(z * I) :=
  (div_eq_iff_mul_eq I_ne_zero).2 <| by simp [mul_assoc]

@[simp]
theorem inv_I : I⁻¹ = -I := by
  rw [inv_eq_one_div, div_I, one_mul]

-- @[simp]
/- Porting note: `simp` attribute removed as linter reports this can be proved
by `simp only [@map_inv₀]` -/
theorem normSq_inv (z : ℂ) : normSq z⁻¹ = (normSq z)⁻¹ :=
  map_inv₀ normSq z

-- @[simp]
/- Porting note: `simp` attribute removed as linter reports this can be proved
by `simp only [@map_div₀]` -/
theorem normSq_div (z w : ℂ) : normSq (z / w) = normSq z / normSq w :=
  map_div₀ normSq z w

@[simp, norm_cast]
theorem ofReal_rat_cast (n : ℚ) : ((n : ℝ) : ℂ) = (n : ℂ) :=
  map_ratCast ofReal n

lemma div_ofReal (z : ℂ) (x : ℝ) : z / x = ⟨z.re / x, z.im / x⟩ := by
  simp_rw [div_eq_inv_mul, ← ofReal_inv, ofReal_mul']

lemma div_nat_cast (z : ℂ) (n : ℕ) : z / n = ⟨z.re / n, z.im / n⟩ := by
  exact_mod_cast div_ofReal z n

lemma div_int_cast (z : ℂ) (n : ℤ) : z / n = ⟨z.re / n, z.im / n⟩ := by
  exact_mod_cast div_ofReal z n

lemma div_rat_cast (z : ℂ) (x : ℚ) : z / x = ⟨z.re / x, z.im / x⟩ := by
  exact_mod_cast div_ofReal z x

lemma div_ofNat (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    z / OfNat.ofNat n = ⟨z.re / OfNat.ofNat n, z.im / OfNat.ofNat n⟩ :=
  div_nat_cast z n

@[simp] lemma div_ofReal_re (z : ℂ) (x : ℝ) : (z / x).re = z.re / x := by rw [div_ofReal]
@[simp] lemma div_ofReal_im (z : ℂ) (x : ℝ) : (z / x).im = z.im / x := by rw [div_ofReal]
@[simp] lemma div_nat_cast_re (z : ℂ) (n : ℕ) : (z / n).re = z.re / n := by rw [div_nat_cast]
@[simp] lemma div_nat_cast_im (z : ℂ) (n : ℕ) : (z / n).im = z.im / n := by rw [div_nat_cast]
@[simp] lemma div_int_cast_re (z : ℂ) (n : ℤ) : (z / n).re = z.re / n := by rw [div_int_cast]
@[simp] lemma div_int_cast_im (z : ℂ) (n : ℤ) : (z / n).im = z.im / n := by rw [div_int_cast]
@[simp] lemma div_rat_cast_re (z : ℂ) (x : ℚ) : (z / x).re = z.re / x := by rw [div_rat_cast]
@[simp] lemma div_rat_cast_im (z : ℂ) (x : ℚ) : (z / x).im = z.im / x := by rw [div_rat_cast]

@[simp]
lemma div_ofNat_re (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (z / no_index (OfNat.ofNat n)).re = z.re / OfNat.ofNat n := div_nat_cast_re z n

@[simp]
lemma div_ofNat_im (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (z / no_index (OfNat.ofNat n)).im = z.im / OfNat.ofNat n := div_nat_cast_im z n

/-! ### Characteristic zero -/


instance charZero : CharZero ℂ :=
  charZero_of_inj_zero fun n h => by
    rwa [← ofReal_nat_cast, ofReal_eq_zero, Nat.cast_eq_zero] at h

-- Test if the `ℚ` smul instance is correct.
example : (Complex.instSMulRealComplex : SMul ℚ ℂ) = (Algebra.toSMul : SMul ℚ ℂ) := rfl

/-- A complex number `z` plus its conjugate `conj z` is `2` times its real part. -/
theorem re_eq_add_conj (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
  have : (↑(↑2 : ℝ) : ℂ) = (2 : ℂ) := rfl
  simp only [add_conj, ofReal_mul, ofReal_one, ofReal_bit0, this,
    mul_div_cancel_left (z.re : ℂ) two_ne_zero]

/-- A complex number `z` minus its conjugate `conj z` is `2i` times its imaginary part. -/
theorem im_eq_sub_conj (z : ℂ) : (z.im : ℂ) = (z - conj z) / (2 * I) := by
  have : (↑2 : ℝ ) * I = 2 * I := rfl
  simp only [sub_conj, ofReal_mul, ofReal_one, ofReal_bit0, mul_right_comm, this,
    mul_div_cancel_left _ (mul_ne_zero two_ne_zero I_ne_zero : 2 * I ≠ 0)]

/-! ### Absolute value -/


namespace AbsTheory

-- We develop enough theory to bundle `abs` into an `AbsoluteValue` before making things public;
-- this is so there's not two versions of it hanging around.
local notation "abs" z => Real.sqrt (normSq z)

private theorem mul_self_abs (z : ℂ) : ((abs z) * abs z) = normSq z :=
  Real.mul_self_sqrt (normSq_nonneg _)

private theorem abs_nonneg' (z : ℂ) : 0 ≤ abs z :=
  Real.sqrt_nonneg _

theorem abs_conj (z : ℂ) : (abs conj z) = abs z := by simp

private theorem abs_re_le_abs (z : ℂ) : |z.re| ≤ abs z := by
  rw [mul_self_le_mul_self_iff (abs_nonneg z.re) (abs_nonneg' _), abs_mul_abs_self, mul_self_abs]
  apply re_sq_le_normSq

private theorem re_le_abs (z : ℂ) : z.re ≤ abs z :=
  (abs_le.1 (abs_re_le_abs _)).2

private theorem abs_mul (z w : ℂ) : (abs z * w) = (abs z) * abs w := by
  rw [normSq_mul, Real.sqrt_mul (normSq_nonneg _)]

private theorem abs_add (z w : ℂ) : (abs z + w) ≤ (abs z) + abs w :=
  (mul_self_le_mul_self_iff (abs_nonneg' (z + w))
      (add_nonneg (abs_nonneg' z) (abs_nonneg' w))).2 <| by
    rw [mul_self_abs, add_mul_self_eq, mul_self_abs, mul_self_abs, add_right_comm, normSq_add,
      add_le_add_iff_left, mul_assoc, mul_le_mul_left (zero_lt_two' ℝ), ←
      Real.sqrt_mul <| normSq_nonneg z, ← normSq_conj w, ← map_mul]
    exact re_le_abs (z * conj w)

/-- The complex absolute value function, defined as the square root of the norm squared. -/
noncomputable def _root_.Complex.abs : AbsoluteValue ℂ ℝ where
  toFun x := abs x
  map_mul' := abs_mul
  nonneg' := abs_nonneg'
  eq_zero' _ := (Real.sqrt_eq_zero <| normSq_nonneg _).trans normSq_eq_zero
  add_le' := abs_add

end AbsTheory

theorem abs_def : (Complex.abs : ℂ → ℝ) = fun z => (normSq z).sqrt :=
  rfl

theorem abs_apply {z : ℂ} : Complex.abs z = (normSq z).sqrt :=
  rfl

@[simp, norm_cast]
theorem abs_ofReal (r : ℝ) : Complex.abs r = |r| := by
  simp [Complex.abs, normSq_ofReal, Real.sqrt_mul_self_eq_abs]

nonrec theorem abs_of_nonneg {r : ℝ} (h : 0 ≤ r) : Complex.abs r = r :=
  (Complex.abs_ofReal _).trans (abs_of_nonneg h)

theorem abs_natCast (n : ℕ) : Complex.abs n = n := Complex.abs_of_nonneg (Nat.cast_nonneg n)

@[simp]
theorem abs_ofNat (n : ℕ) [n.AtLeastTwo] :
    Complex.abs (no_index (OfNat.ofNat n : ℂ)) = OfNat.ofNat n :=
  abs_natCast n

theorem mul_self_abs (z : ℂ) : Complex.abs z * Complex.abs z = normSq z :=
  Real.mul_self_sqrt (normSq_nonneg _)

theorem sq_abs (z : ℂ) : Complex.abs z ^ 2 = normSq z :=
  Real.sq_sqrt (normSq_nonneg _)

@[simp]
theorem sq_abs_sub_sq_re (z : ℂ) : Complex.abs z ^ 2 - z.re ^ 2 = z.im ^ 2 := by
  rw [sq_abs, normSq_apply, ← sq, ← sq, add_sub_cancel']

@[simp]
theorem sq_abs_sub_sq_im (z : ℂ) : Complex.abs z ^ 2 - z.im ^ 2 = z.re ^ 2 := by
  rw [← sq_abs_sub_sq_re, sub_sub_cancel]

@[simp]
theorem abs_I : Complex.abs I = 1 := by simp [Complex.abs]

theorem abs_two : Complex.abs 2 = 2 := abs_ofNat 2

@[simp]
theorem range_abs : range Complex.abs = Ici 0 :=
  Subset.antisymm
    (by simp only [range_subset_iff, Ici, mem_setOf_eq, map_nonneg, forall_const])
    (fun x hx => ⟨x, Complex.abs_of_nonneg hx⟩)

@[simp]
theorem abs_conj (z : ℂ) : Complex.abs (conj z) = Complex.abs z :=
  AbsTheory.abs_conj z

-- Porting note: @[simp] can prove it now
theorem abs_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.abs (s.prod f) = s.prod fun I => Complex.abs (f I) :=
  map_prod Complex.abs _ _

-- @[simp]
/- Porting note: `simp` attribute removed as linter reports this can be proved
by `simp only [@map_pow]` -/
theorem abs_pow (z : ℂ) (n : ℕ) : Complex.abs (z ^ n) = Complex.abs z ^ n :=
  map_pow Complex.abs z n

-- @[simp]
/- Porting note: `simp` attribute removed as linter reports this can be proved
by `simp only [@map_zpow₀]` -/
theorem abs_zpow (z : ℂ) (n : ℤ) : Complex.abs (z ^ n) = Complex.abs z ^ n :=
  map_zpow₀ Complex.abs z n

theorem abs_re_le_abs (z : ℂ) : |z.re| ≤ Complex.abs z :=
  Real.abs_le_sqrt <| by
    rw [normSq_apply, ← sq]
    exact le_add_of_nonneg_right (mul_self_nonneg _)

theorem abs_im_le_abs (z : ℂ) : |z.im| ≤ Complex.abs z :=
  Real.abs_le_sqrt <| by
    rw [normSq_apply, ← sq, ← sq]
    exact le_add_of_nonneg_left (sq_nonneg _)

theorem re_le_abs (z : ℂ) : z.re ≤ Complex.abs z :=
  (abs_le.1 (abs_re_le_abs _)).2

theorem im_le_abs (z : ℂ) : z.im ≤ Complex.abs z :=
  (abs_le.1 (abs_im_le_abs _)).2

@[simp]
theorem abs_re_lt_abs {z : ℂ} : |z.re| < Complex.abs z ↔ z.im ≠ 0 := by
  rw [Complex.abs, AbsoluteValue.coe_mk, MulHom.coe_mk, Real.lt_sqrt (abs_nonneg _), normSq_apply,
    _root_.sq_abs, ← sq, lt_add_iff_pos_right, mul_self_pos]

@[simp]
theorem abs_im_lt_abs {z : ℂ} : |z.im| < Complex.abs z ↔ z.re ≠ 0 := by
  simpa using @abs_re_lt_abs (z * I)

@[simp]
lemma abs_re_eq_abs {z : ℂ} : |z.re| = abs z ↔ z.im = 0 :=
  not_iff_not.1 <| (abs_re_le_abs z).lt_iff_ne.symm.trans abs_re_lt_abs

@[simp]
lemma abs_im_eq_abs {z : ℂ} : |z.im| = abs z ↔ z.re = 0 :=
  not_iff_not.1 <| (abs_im_le_abs z).lt_iff_ne.symm.trans abs_im_lt_abs

@[simp]
theorem abs_abs (z : ℂ) : |Complex.abs z| = Complex.abs z :=
  _root_.abs_of_nonneg (AbsoluteValue.nonneg _ z)

-- Porting note: probably should be golfed
theorem abs_le_abs_re_add_abs_im (z : ℂ) : Complex.abs z ≤ |z.re| + |z.im| := by
  simpa [re_add_im] using Complex.abs.add_le z.re (z.im * I)

-- Porting note: added so `two_pos` in the next proof works
-- TODO: move somewhere else
instance : NeZero (1 : ℝ) :=
 ⟨by apply one_ne_zero⟩

theorem abs_le_sqrt_two_mul_max (z : ℂ) : Complex.abs z ≤ Real.sqrt 2 * max |z.re| |z.im| := by
  cases' z with x y
  simp only [abs_apply, normSq_mk, ← sq]
  by_cases hle : |x| ≤ |y|
  · calc
      Real.sqrt (x ^ 2 + y ^ 2) ≤ Real.sqrt (y ^ 2 + y ^ 2) :=
        Real.sqrt_le_sqrt (add_le_add_right (sq_le_sq.2 hle) _)
      _ = Real.sqrt 2 * max |x| |y| := by
        rw [max_eq_right hle, ← two_mul, Real.sqrt_mul two_pos.le, Real.sqrt_sq_eq_abs]
  · have hle' := le_of_not_le hle
    rw [add_comm]
    calc
      Real.sqrt (y ^ 2 + x ^ 2) ≤ Real.sqrt (x ^ 2 + x ^ 2) :=
        Real.sqrt_le_sqrt (add_le_add_right (sq_le_sq.2 hle') _)
      _ = Real.sqrt 2 * max |x| |y| := by
        rw [max_eq_left hle', ← two_mul, Real.sqrt_mul two_pos.le, Real.sqrt_sq_eq_abs]

theorem abs_re_div_abs_le_one (z : ℂ) : |z.re / Complex.abs z| ≤ 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
  else by simp_rw [_root_.abs_div, abs_abs,
    div_le_iff (AbsoluteValue.pos Complex.abs hz), one_mul, abs_re_le_abs]

theorem abs_im_div_abs_le_one (z : ℂ) : |z.im / Complex.abs z| ≤ 1 :=
  if hz : z = 0 then by simp [hz, zero_le_one]
  else by simp_rw [_root_.abs_div, abs_abs,
    div_le_iff (AbsoluteValue.pos Complex.abs hz), one_mul, abs_im_le_abs]

-- Porting note: removed `norm_cast` attribute because the RHS can't start with `↑`
@[simp]
theorem abs_cast_nat (n : ℕ) : Complex.abs (n : ℂ) = n := by
  rw [← ofReal_nat_cast, abs_of_nonneg (Nat.cast_nonneg n)]

@[simp, norm_cast]
theorem int_cast_abs (n : ℤ) : |↑n| = Complex.abs n := by
  rw [← ofReal_int_cast, abs_ofReal]

theorem normSq_eq_abs (x : ℂ) : normSq x = (Complex.abs x) ^ 2 := by
  simp [abs, sq, abs_def, Real.mul_self_sqrt (normSq_nonneg _)]

/-! ### Cauchy sequences -/

local notation "abs'" => Abs.abs

theorem isCauSeq_re (f : CauSeq ℂ Complex.abs) : IsCauSeq abs' fun n => (f n).re := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa using abs_re_le_abs (f j - f i)) (H _ ij)

theorem isCauSeq_im (f : CauSeq ℂ Complex.abs) : IsCauSeq abs' fun n => (f n).im := fun ε ε0 =>
  (f.cauchy ε0).imp fun i H j ij =>
    lt_of_le_of_lt (by simpa using abs_im_le_abs (f j - f i)) (H _ ij)

/-- The real part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqRe (f : CauSeq ℂ Complex.abs) : CauSeq ℝ abs' :=
  ⟨_, isCauSeq_re f⟩

/-- The imaginary part of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqIm (f : CauSeq ℂ Complex.abs) : CauSeq ℝ abs' :=
  ⟨_, isCauSeq_im f⟩

theorem isCauSeq_abs {f : ℕ → ℂ} (hf : IsCauSeq Complex.abs f) :
    IsCauSeq abs' (Complex.abs ∘ f) := fun ε ε0 =>
  let ⟨i, hi⟩ := hf ε ε0
  ⟨i, fun j hj => lt_of_le_of_lt
    (Complex.abs.abs_abv_sub_le_abv_sub _ _) (hi j hj)⟩

/-- The limit of a Cauchy sequence of complex numbers. -/
noncomputable def limAux (f : CauSeq ℂ Complex.abs) : ℂ :=
  ⟨CauSeq.lim (cauSeqRe f), CauSeq.lim (cauSeqIm f)⟩

theorem equiv_limAux (f : CauSeq ℂ Complex.abs) :
    f ≈ CauSeq.const Complex.abs (limAux f) := fun ε ε0 =>
  (exists_forall_ge_and
  (CauSeq.equiv_lim ⟨_, isCauSeq_re f⟩ _ (half_pos ε0))
        (CauSeq.equiv_lim ⟨_, isCauSeq_im f⟩ _ (half_pos ε0))).imp
    fun i H j ij => by
    cases' H _ ij with H₁ H₂
    apply lt_of_le_of_lt (abs_le_abs_re_add_abs_im _)
    dsimp [limAux] at *
    have := add_lt_add H₁ H₂
    rwa [add_halves] at this

instance instIsComplete : CauSeq.IsComplete ℂ Complex.abs :=
  ⟨fun f => ⟨limAux f, equiv_limAux f⟩⟩

open CauSeq

theorem lim_eq_lim_im_add_lim_re (f : CauSeq ℂ Complex.abs) :
    lim f = ↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I :=
  lim_eq_of_equiv_const <|
    calc
      f ≈ _ := equiv_limAux f
      _ = CauSeq.const Complex.abs (↑(lim (cauSeqRe f)) + ↑(lim (cauSeqIm f)) * I) :=
        CauSeq.ext fun _ =>
          Complex.ext (by simp [limAux, cauSeqRe, ofReal']) (by simp [limAux, cauSeqIm, ofReal'])

theorem lim_re (f : CauSeq ℂ Complex.abs) : lim (cauSeqRe f) = (lim f).re := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal']

theorem lim_im (f : CauSeq ℂ Complex.abs) : lim (cauSeqIm f) = (lim f).im := by
  rw [lim_eq_lim_im_add_lim_re]; simp [ofReal']

theorem isCauSeq_conj (f : CauSeq ℂ Complex.abs) :
    IsCauSeq Complex.abs fun n => conj (f n) := fun ε ε0 =>
  let ⟨i, hi⟩ := f.2 ε ε0
  ⟨i, fun j hj => by
    rw [← RingHom.map_sub, abs_conj]; exact hi j hj⟩

/-- The complex conjugate of a complex Cauchy sequence, as a complex Cauchy sequence. -/
noncomputable def cauSeqConj (f : CauSeq ℂ Complex.abs) : CauSeq ℂ Complex.abs :=
  ⟨_, isCauSeq_conj f⟩

theorem lim_conj (f : CauSeq ℂ Complex.abs) : lim (cauSeqConj f) = conj (lim f) :=
  Complex.ext (by simp [cauSeqConj, (lim_re _).symm, cauSeqRe])
    (by simp [cauSeqConj, (lim_im _).symm, cauSeqIm, (lim_neg _).symm]; rfl)

/-- The absolute value of a complex Cauchy sequence, as a real Cauchy sequence. -/
noncomputable def cauSeqAbs (f : CauSeq ℂ Complex.abs) : CauSeq ℝ abs' :=
  ⟨_, isCauSeq_abs f.2⟩

theorem lim_abs (f : CauSeq ℂ Complex.abs) : lim (cauSeqAbs f) = Complex.abs (lim f) :=
  lim_eq_of_equiv_const fun ε ε0 =>
    let ⟨i, hi⟩ := equiv_lim f ε ε0
    ⟨i, fun j hj => lt_of_le_of_lt (Complex.abs.abs_abv_sub_le_abv_sub _ _) (hi j hj)⟩

variable {α : Type*} (s : Finset α)

@[simp, norm_cast]
theorem ofReal_prod (f : α → ℝ) : ((∏ i in s, f i : ℝ) : ℂ) = ∏ i in s, (f i : ℂ) :=
  map_prod ofReal _ _

@[simp, norm_cast]
theorem ofReal_sum (f : α → ℝ) : ((∑ i in s, f i : ℝ) : ℂ) = ∑ i in s, (f i : ℂ) :=
  map_sum ofReal _ _

@[simp]
theorem re_sum (f : α → ℂ) : (∑ i in s, f i).re = ∑ i in s, (f i).re :=
  reAddGroupHom.map_sum f s

@[simp]
theorem im_sum (f : α → ℂ) : (∑ i in s, f i).im = ∑ i in s, (f i).im :=
  imAddGroupHom.map_sum f s

end Complex
