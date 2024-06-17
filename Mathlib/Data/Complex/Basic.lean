/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Image

#align_import data.complex.basic from "leanprover-community/mathlib"@"31c24aa72e7b3e5ed97a8412470e904f82b81004"

/-!
# The complex numbers

The complex numbers are modelled as ℝ^2 in the obvious way and it is shown that they form a field
of characteristic zero. The result that the complex numbers are algebraically closed, see
`FieldTheory.AlgebraicClosure`.
-/

open Set Function

/-! ### Definition and basic arithmetic -/


/-- Complex numbers consist of two `Real`s: a real part `re` and an imaginary part `im`. -/
structure Complex : Type where
  /-- The real part of a complex number. -/
  re : ℝ
  /-- The imaginary part of a complex number. -/
  im : ℝ
#align complex Complex

@[inherit_doc] notation "ℂ" => Complex

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
#align complex.equiv_real_prod Complex.equivRealProd

@[simp]
theorem eta : ∀ z : ℂ, Complex.mk z.re z.im = z
  | ⟨_, _⟩ => rfl
#align complex.eta Complex.eta

-- We only mark this lemma with `ext` *locally* to avoid it applying whenever terms of `ℂ` appear.
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl
#align complex.ext Complex.ext

attribute [local ext] Complex.ext

theorem ext_iff {z w : ℂ} : z = w ↔ z.re = w.re ∧ z.im = w.im :=
  ⟨fun H => by simp [H], fun h => ext h.1 h.2⟩
#align complex.ext_iff Complex.ext_iff

theorem re_surjective : Surjective re := fun x => ⟨⟨x, 0⟩, rfl⟩
#align complex.re_surjective Complex.re_surjective

theorem im_surjective : Surjective im := fun y => ⟨⟨0, y⟩, rfl⟩
#align complex.im_surjective Complex.im_surjective

@[simp]
theorem range_re : range re = univ :=
  re_surjective.range_eq
#align complex.range_re Complex.range_re

@[simp]
theorem range_im : range im = univ :=
  im_surjective.range_eq
#align complex.range_im Complex.range_im

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
#align complex.of_real_re Complex.ofReal_re

@[simp, norm_cast]
theorem ofReal_im (r : ℝ) : (r : ℂ).im = 0 :=
  rfl
#align complex.of_real_im Complex.ofReal_im

theorem ofReal_def (r : ℝ) : (r : ℂ) = ⟨r, 0⟩ :=
  rfl
#align complex.of_real_def Complex.ofReal_def

@[simp, norm_cast]
theorem ofReal_inj {z w : ℝ} : (z : ℂ) = w ↔ z = w :=
  ⟨congrArg re, by apply congrArg⟩
#align complex.of_real_inj Complex.ofReal_inj

-- Porting note: made coercion explicit
theorem ofReal_injective : Function.Injective ((↑) : ℝ → ℂ) := fun _ _ => congrArg re
#align complex.of_real_injective Complex.ofReal_injective

-- Porting note: made coercion explicit
instance canLift : CanLift ℂ ℝ (↑) fun z => z.im = 0 where
  prf z hz := ⟨z.re, ext rfl hz.symm⟩
#align complex.can_lift Complex.canLift

/-- The product of a set on the real axis and a set on the imaginary axis of the complex plane,
denoted by `s ×ℂ t`. -/
def Set.reProdIm (s t : Set ℝ) : Set ℂ :=
  re ⁻¹' s ∩ im ⁻¹' t
#align set.re_prod_im Complex.Set.reProdIm

@[inherit_doc]
infixl:72 " ×ℂ " => Set.reProdIm

theorem mem_reProdIm {z : ℂ} {s t : Set ℝ} : z ∈ s ×ℂ t ↔ z.re ∈ s ∧ z.im ∈ t :=
  Iff.rfl
#align complex.mem_re_prod_im Complex.mem_reProdIm

instance : Zero ℂ :=
  ⟨(0 : ℝ)⟩

instance : Inhabited ℂ :=
  ⟨0⟩

@[simp]
theorem zero_re : (0 : ℂ).re = 0 :=
  rfl
#align complex.zero_re Complex.zero_re

@[simp]
theorem zero_im : (0 : ℂ).im = 0 :=
  rfl
#align complex.zero_im Complex.zero_im

@[simp, norm_cast]
theorem ofReal_zero : ((0 : ℝ) : ℂ) = 0 :=
  rfl
#align complex.of_real_zero Complex.ofReal_zero

@[simp]
theorem ofReal_eq_zero {z : ℝ} : (z : ℂ) = 0 ↔ z = 0 :=
  ofReal_inj
#align complex.of_real_eq_zero Complex.ofReal_eq_zero

theorem ofReal_ne_zero {z : ℝ} : (z : ℂ) ≠ 0 ↔ z ≠ 0 :=
  not_congr ofReal_eq_zero
#align complex.of_real_ne_zero Complex.ofReal_ne_zero

instance : One ℂ :=
  ⟨(1 : ℝ)⟩

@[simp]
theorem one_re : (1 : ℂ).re = 1 :=
  rfl
#align complex.one_re Complex.one_re

@[simp]
theorem one_im : (1 : ℂ).im = 0 :=
  rfl
#align complex.one_im Complex.one_im

@[simp, norm_cast]
theorem ofReal_one : ((1 : ℝ) : ℂ) = 1 :=
  rfl
#align complex.of_real_one Complex.ofReal_one

@[simp]
theorem ofReal_eq_one {z : ℝ} : (z : ℂ) = 1 ↔ z = 1 :=
  ofReal_inj
#align complex.of_real_eq_one Complex.ofReal_eq_one

theorem ofReal_ne_one {z : ℝ} : (z : ℂ) ≠ 1 ↔ z ≠ 1 :=
  not_congr ofReal_eq_one
#align complex.of_real_ne_one Complex.ofReal_ne_one

instance : Add ℂ :=
  ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

@[simp]
theorem add_re (z w : ℂ) : (z + w).re = z.re + w.re :=
  rfl
#align complex.add_re Complex.add_re

@[simp]
theorem add_im (z w : ℂ) : (z + w).im = z.im + w.im :=
  rfl
#align complex.add_im Complex.add_im

-- replaced by `re_ofNat`
#noalign complex.bit0_re
#noalign complex.bit1_re
-- replaced by `im_ofNat`
#noalign complex.bit0_im
#noalign complex.bit1_im

@[simp, norm_cast]
theorem ofReal_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
  ext_iff.2 <| by simp [ofReal']
#align complex.of_real_add Complex.ofReal_add

-- replaced by `Complex.ofReal_ofNat`
#noalign complex.of_real_bit0
#noalign complex.of_real_bit1

instance : Neg ℂ :=
  ⟨fun z => ⟨-z.re, -z.im⟩⟩

@[simp]
theorem neg_re (z : ℂ) : (-z).re = -z.re :=
  rfl
#align complex.neg_re Complex.neg_re

@[simp]
theorem neg_im (z : ℂ) : (-z).im = -z.im :=
  rfl
#align complex.neg_im Complex.neg_im

@[simp, norm_cast]
theorem ofReal_neg (r : ℝ) : ((-r : ℝ) : ℂ) = -r :=
  ext_iff.2 <| by simp [ofReal']
#align complex.of_real_neg Complex.ofReal_neg

instance : Sub ℂ :=
  ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩

instance : Mul ℂ :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩⟩

@[simp]
theorem mul_re (z w : ℂ) : (z * w).re = z.re * w.re - z.im * w.im :=
  rfl
#align complex.mul_re Complex.mul_re

@[simp]
theorem mul_im (z w : ℂ) : (z * w).im = z.re * w.im + z.im * w.re :=
  rfl
#align complex.mul_im Complex.mul_im

@[simp, norm_cast]
theorem ofReal_mul (r s : ℝ) : ((r * s : ℝ) : ℂ) = r * s :=
  ext_iff.2 <| by simp [ofReal']
#align complex.of_real_mul Complex.ofReal_mul

theorem re_ofReal_mul (r : ℝ) (z : ℂ) : (r * z).re = r * z.re := by simp [ofReal']
#align complex.of_real_mul_re Complex.re_ofReal_mul

theorem im_ofReal_mul (r : ℝ) (z : ℂ) : (r * z).im = r * z.im := by simp [ofReal']
#align complex.of_real_mul_im Complex.im_ofReal_mul

lemma re_mul_ofReal (z : ℂ) (r : ℝ) : (z * r).re = z.re *  r := by simp [ofReal']
lemma im_mul_ofReal (z : ℂ) (r : ℝ) : (z * r).im = z.im *  r := by simp [ofReal']

theorem ofReal_mul' (r : ℝ) (z : ℂ) : ↑r * z = ⟨r * z.re, r * z.im⟩ :=
  ext (re_ofReal_mul _ _) (im_ofReal_mul _ _)
#align complex.of_real_mul' Complex.ofReal_mul'

/-! ### The imaginary unit, `I` -/


/-- The imaginary unit. -/
def I : ℂ :=
  ⟨0, 1⟩
set_option linter.uppercaseLean3 false in
#align complex.I Complex.I

@[simp]
theorem I_re : I.re = 0 :=
  rfl
set_option linter.uppercaseLean3 false in
#align complex.I_re Complex.I_re

@[simp]
theorem I_im : I.im = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align complex.I_im Complex.I_im

@[simp]
theorem I_mul_I : I * I = -1 :=
  ext_iff.2 <| by simp
set_option linter.uppercaseLean3 false in
#align complex.I_mul_I Complex.I_mul_I

theorem I_mul (z : ℂ) : I * z = ⟨-z.im, z.re⟩ :=
  ext_iff.2 <| by simp
set_option linter.uppercaseLean3 false in
#align complex.I_mul Complex.I_mul

@[simp] lemma I_ne_zero : (I : ℂ) ≠ 0 := mt (congr_arg im) zero_ne_one.symm
set_option linter.uppercaseLean3 false in
#align complex.I_ne_zero Complex.I_ne_zero

theorem mk_eq_add_mul_I (a b : ℝ) : Complex.mk a b = a + b * I :=
  ext_iff.2 <| by simp [ofReal']
set_option linter.uppercaseLean3 false in
#align complex.mk_eq_add_mul_I Complex.mk_eq_add_mul_I

@[simp]
theorem re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z :=
  ext_iff.2 <| by simp [ofReal']
#align complex.re_add_im Complex.re_add_im

theorem mul_I_re (z : ℂ) : (z * I).re = -z.im := by simp
set_option linter.uppercaseLean3 false in
#align complex.mul_I_re Complex.mul_I_re

theorem mul_I_im (z : ℂ) : (z * I).im = z.re := by simp
set_option linter.uppercaseLean3 false in
#align complex.mul_I_im Complex.mul_I_im

theorem I_mul_re (z : ℂ) : (I * z).re = -z.im := by simp
set_option linter.uppercaseLean3 false in
#align complex.I_mul_re Complex.I_mul_re

theorem I_mul_im (z : ℂ) : (I * z).im = z.re := by simp
set_option linter.uppercaseLean3 false in
#align complex.I_mul_im Complex.I_mul_im

@[simp]
theorem equivRealProd_symm_apply (p : ℝ × ℝ) : equivRealProd.symm p = p.1 + p.2 * I := by
  ext <;> simp [Complex.equivRealProd, ofReal']
#align complex.equiv_real_prod_symm_apply Complex.equivRealProd_symm_apply

/-- The natural `AddEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! (config := { simpRhs := true }) apply symm_apply_re symm_apply_im]
def equivRealProdAddHom : ℂ ≃+ ℝ × ℝ :=
  { equivRealProd with map_add' := by simp }
#align complex.equiv_real_prod_add_hom Complex.equivRealProdAddHom

theorem equivRealProdAddHom_symm_apply (p : ℝ × ℝ) :
    equivRealProdAddHom.symm p = p.1 + p.2 * I := equivRealProd_symm_apply p

/-! ### Commutative ring instance and lemmas -/


/- We use a nonstandard formula for the `ℕ` and `ℤ` actions to make sure there is no
diamond from the other actions they inherit through the `ℝ`-action on `ℂ` and action transitivity
defined in `Data.Complex.Module`. -/
instance : Nontrivial ℂ :=
  pullback_nonzero re rfl rfl

-- Porting note: moved from `Module/Data/Complex/Basic.lean`
namespace SMul

-- The useless `0` multiplication in `smul` is to make sure that
-- `RestrictScalars.module ℝ ℂ ℂ = Complex.module` definitionally.
-- instance made scoped to avoid situations like instance synthesis
-- of `SMul ℂ ℂ` trying to proceed via `SMul ℂ ℝ`.
/-- Scalar multiplication by `R` on `ℝ` extends to `ℂ`. This is used here and in
`Matlib.Data.Complex.Module` to transfer instances from `ℝ` to `ℂ`, but is not
needed outside, so we make it scoped. -/
scoped instance instSMulRealComplex {R : Type*} [SMul R ℝ] : SMul R ℂ where
  smul r x := ⟨r • x.re - 0 * x.im, r • x.im + 0 * x.re⟩

end SMul

open scoped SMul

section SMul

variable {R : Type*} [SMul R ℝ]

theorem smul_re (r : R) (z : ℂ) : (r • z).re = r • z.re := by simp [(· • ·), SMul.smul]
#align complex.smul_re Complex.smul_re

theorem smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im := by simp [(· • ·), SMul.smul]
#align complex.smul_im Complex.smul_im

@[simp]
theorem real_smul {x : ℝ} {z : ℂ} : x • z = x * z :=
  rfl
#align complex.real_smul Complex.real_smul

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


instance addGroupWithOne : AddGroupWithOne ℂ :=
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
  { addGroupWithOne with
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

-- Porting note: added due to changes in typeclass search order
/-- This shortcut instance ensures we do not find `Semiring` via the noncomputable
`Complex.field` instance. -/
instance : Semiring ℂ :=
  inferInstance

/-- The "real part" map, considered as an additive group homomorphism. -/
def reAddGroupHom : ℂ →+ ℝ where
  toFun := re
  map_zero' := zero_re
  map_add' := add_re
#align complex.re_add_group_hom Complex.reAddGroupHom

@[simp]
theorem coe_reAddGroupHom : (reAddGroupHom : ℂ → ℝ) = re :=
  rfl
#align complex.coe_re_add_group_hom Complex.coe_reAddGroupHom

/-- The "imaginary part" map, considered as an additive group homomorphism. -/
def imAddGroupHom : ℂ →+ ℝ where
  toFun := im
  map_zero' := zero_im
  map_add' := add_im
#align complex.im_add_group_hom Complex.imAddGroupHom

@[simp]
theorem coe_imAddGroupHom : (imAddGroupHom : ℂ → ℝ) = im :=
  rfl
#align complex.coe_im_add_group_hom Complex.coe_imAddGroupHom

section
set_option linter.deprecated false
@[simp]
theorem I_pow_bit0 (n : ℕ) : I ^ bit0 n = (-1 : ℂ) ^ n := by rw [pow_bit0', Complex.I_mul_I]
set_option linter.uppercaseLean3 false in
#align complex.I_pow_bit0 Complex.I_pow_bit0

@[simp]
theorem I_pow_bit1 (n : ℕ) : I ^ bit1 n = (-1 : ℂ) ^ n * I := by rw [pow_bit1', Complex.I_mul_I]
set_option linter.uppercaseLean3 false in
#align complex.I_pow_bit1 Complex.I_pow_bit1

end

/-! ### Cast lemmas -/

noncomputable instance instNNRatCast : NNRatCast ℂ where nnratCast q := ofReal' q
noncomputable instance instRatCast : RatCast ℂ where ratCast q := ofReal' q

-- See note [no_index around OfNat.ofNat]
@[simp, norm_cast] lemma ofReal_ofNat (n : ℕ) [n.AtLeastTwo] :
    ofReal' (no_index (OfNat.ofNat n)) = OfNat.ofNat n := rfl
@[simp, norm_cast] lemma ofReal_natCast (n : ℕ) : ofReal' n = n := rfl
@[simp, norm_cast] lemma ofReal_intCast (n : ℤ) : ofReal' n = n := rfl
@[simp, norm_cast] lemma ofReal_nnratCast (q : ℚ≥0) : ofReal' q = q := rfl
@[simp, norm_cast] lemma ofReal_ratCast (q : ℚ) : ofReal' q = q := rfl
#align complex.of_real_nat_cast Complex.ofReal_natCast
#align complex.of_real_int_cast Complex.ofReal_intCast
#align complex.of_real_rat_cast Complex.ofReal_ratCast

@[deprecated (since := "2024-04-17")]
alias ofReal_rat_cast := ofReal_ratCast

-- See note [no_index around OfNat.ofNat]
@[simp]
lemma re_ofNat (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : ℂ).re = OfNat.ofNat n := rfl
@[simp] lemma im_ofNat (n : ℕ) [n.AtLeastTwo] : (no_index (OfNat.ofNat n) : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma natCast_re (n : ℕ) : (n : ℂ).re = n := rfl
@[simp, norm_cast] lemma natCast_im (n : ℕ) : (n : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma intCast_re (n : ℤ) : (n : ℂ).re = n := rfl
@[simp, norm_cast] lemma intCast_im (n : ℤ) : (n : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma re_nnratCast (q : ℚ≥0) : (q : ℂ).re = q := rfl
@[simp, norm_cast] lemma im_nnratCast (q : ℚ≥0) : (q : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma ratCast_re (q : ℚ) : (q : ℂ).re = q := rfl
@[simp, norm_cast] lemma ratCast_im (q : ℚ) : (q : ℂ).im = 0 := rfl
#align complex.nat_cast_re Complex.natCast_re
#align complex.nat_cast_im Complex.natCast_im
#align complex.int_cast_re Complex.intCast_re
#align complex.int_cast_im Complex.intCast_im
#align complex.rat_cast_re Complex.ratCast_re
#align complex.rat_cast_im Complex.ratCast_im

@[deprecated (since := "2024-04-17")]
alias rat_cast_im := ratCast_im

@[norm_cast] lemma ofReal_nsmul (n : ℕ) (r : ℝ) : ↑(n • r) = n • (r : ℂ) := by simp
@[norm_cast] lemma ofReal_zsmul (n : ℤ) (r : ℝ) : ↑(n • r) = n • (r : ℂ) := by simp

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
#align complex.conj_re Complex.conj_re

@[simp]
theorem conj_im (z : ℂ) : (conj z).im = -z.im :=
  rfl
#align complex.conj_im Complex.conj_im

theorem conj_ofReal (r : ℝ) : conj (r : ℂ) = r :=
  ext_iff.2 <| by simp [star]
#align complex.conj_of_real Complex.conj_ofReal

@[simp]
theorem conj_I : conj I = -I :=
  ext_iff.2 <| by simp
  set_option linter.uppercaseLean3 false in
#align complex.conj_I Complex.conj_I

#noalign complex.conj_bit0
#noalign complex.conj_bit1

theorem conj_natCast (n : ℕ) : conj (n : ℂ) = n := map_natCast _ _

@[deprecated (since := "2024-04-17")]
alias conj_nat_cast := conj_natCast

-- See note [no_index around OfNat.ofNat]
theorem conj_ofNat (n : ℕ) [n.AtLeastTwo] : conj (no_index (OfNat.ofNat n : ℂ)) = OfNat.ofNat n :=
  map_ofNat _ _

-- @[simp]
/- Porting note (#11119): `simp` attribute removed as the result could be proved
by `simp only [@map_neg, Complex.conj_i, @neg_neg]`
-/
theorem conj_neg_I : conj (-I) = I :=
  ext_iff.2 <| by simp
set_option linter.uppercaseLean3 false in
#align complex.conj_neg_I Complex.conj_neg_I

theorem conj_eq_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
  ⟨fun h => ⟨z.re, ext rfl <| eq_zero_of_neg_eq (congr_arg im h)⟩, fun ⟨h, e⟩ => by
    rw [e, conj_ofReal]⟩
#align complex.conj_eq_iff_real Complex.conj_eq_iff_real

theorem conj_eq_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
  conj_eq_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp [ofReal'], fun h => ⟨_, h.symm⟩⟩
#align complex.conj_eq_iff_re Complex.conj_eq_iff_re

theorem conj_eq_iff_im {z : ℂ} : conj z = z ↔ z.im = 0 :=
  ⟨fun h => add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp (congr_arg im h)), fun h =>
    ext rfl (neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero.mpr h))⟩
#align complex.conj_eq_iff_im Complex.conj_eq_iff_im

-- `simpNF` complains about this being provable by `RCLike.star_def` even
-- though it's not imported by this file.
-- Porting note: linter `simpNF` not found
@[simp]
theorem star_def : (Star.star : ℂ → ℂ) = conj :=
  rfl
#align complex.star_def Complex.star_def

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
#align complex.norm_sq Complex.normSq

theorem normSq_apply (z : ℂ) : normSq z = z.re * z.re + z.im * z.im :=
  rfl
#align complex.norm_sq_apply Complex.normSq_apply

@[simp]
theorem normSq_ofReal (r : ℝ) : normSq r = r * r := by
  simp [normSq, ofReal']
#align complex.norm_sq_of_real Complex.normSq_ofReal

@[simp]
theorem normSq_natCast (n : ℕ) : normSq n = n * n := normSq_ofReal _

@[deprecated (since := "2024-04-17")]
alias normSq_nat_cast := normSq_natCast

@[simp]
theorem normSq_intCast (z : ℤ) : normSq z = z * z := normSq_ofReal _

@[deprecated (since := "2024-04-17")]
alias normSq_int_cast := normSq_intCast

@[simp]
theorem normSq_ratCast (q : ℚ) : normSq q = q * q := normSq_ofReal _

@[deprecated (since := "2024-04-17")]
alias normSq_rat_cast := normSq_ratCast

-- See note [no_index around OfNat.ofNat]
@[simp]
theorem normSq_ofNat (n : ℕ) [n.AtLeastTwo] :
    normSq (no_index (OfNat.ofNat n : ℂ)) = OfNat.ofNat n * OfNat.ofNat n :=
  normSq_natCast _

@[simp]
theorem normSq_mk (x y : ℝ) : normSq ⟨x, y⟩ = x * x + y * y :=
  rfl
#align complex.norm_sq_mk Complex.normSq_mk

theorem normSq_add_mul_I (x y : ℝ) : normSq (x + y * I) = x ^ 2 + y ^ 2 := by
  rw [← mk_eq_add_mul_I, normSq_mk, sq, sq]
set_option linter.uppercaseLean3 false in
#align complex.norm_sq_add_mul_I Complex.normSq_add_mul_I

theorem normSq_eq_conj_mul_self {z : ℂ} : (normSq z : ℂ) = conj z * z := by
  ext <;> simp [normSq, mul_comm, ofReal']
#align complex.norm_sq_eq_conj_mul_self Complex.normSq_eq_conj_mul_self

-- @[simp]
/- Porting note (#11119): `simp` attribute removed as linter reports this can be proved
by `simp only [@map_zero]` -/
theorem normSq_zero : normSq 0 = 0 :=
  normSq.map_zero
#align complex.norm_sq_zero Complex.normSq_zero

-- @[simp]
/- Porting note (#11119): `simp` attribute removed as linter reports this can be proved
by `simp only [@map_one]` -/
theorem normSq_one : normSq 1 = 1 :=
  normSq.map_one
#align complex.norm_sq_one Complex.normSq_one

@[simp]
theorem normSq_I : normSq I = 1 := by simp [normSq]
set_option linter.uppercaseLean3 false in
#align complex.norm_sq_I Complex.normSq_I

theorem normSq_nonneg (z : ℂ) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
#align complex.norm_sq_nonneg Complex.normSq_nonneg

theorem normSq_eq_zero {z : ℂ} : normSq z = 0 ↔ z = 0 :=
  ⟨fun h =>
    ext (eq_zero_of_mul_self_add_mul_self_eq_zero h)
      (eq_zero_of_mul_self_add_mul_self_eq_zero <| (add_comm _ _).trans h),
    fun h => h.symm ▸ normSq_zero⟩
#align complex.norm_sq_eq_zero Complex.normSq_eq_zero

@[simp]
theorem normSq_pos {z : ℂ} : 0 < normSq z ↔ z ≠ 0 :=
  (normSq_nonneg z).lt_iff_ne.trans <| not_congr (eq_comm.trans normSq_eq_zero)
#align complex.norm_sq_pos Complex.normSq_pos

#adaptation_note /-- nightly-2024-04-01
The simpNF linter now times out on this lemma.
See https://github.com/leanprover-community/mathlib4/issues/12228 -/
@[simp, nolint simpNF]
theorem normSq_neg (z : ℂ) : normSq (-z) = normSq z := by simp [normSq]
#align complex.norm_sq_neg Complex.normSq_neg

@[simp]
theorem normSq_conj (z : ℂ) : normSq (conj z) = normSq z := by simp [normSq]
#align complex.norm_sq_conj Complex.normSq_conj

theorem normSq_mul (z w : ℂ) : normSq (z * w) = normSq z * normSq w :=
  normSq.map_mul z w
#align complex.norm_sq_mul Complex.normSq_mul

theorem normSq_add (z w : ℂ) : normSq (z + w) = normSq z + normSq w + 2 * (z * conj w).re := by
  dsimp [normSq]; ring
#align complex.norm_sq_add Complex.normSq_add

theorem re_sq_le_normSq (z : ℂ) : z.re * z.re ≤ normSq z :=
  le_add_of_nonneg_right (mul_self_nonneg _)
#align complex.re_sq_le_norm_sq Complex.re_sq_le_normSq

theorem im_sq_le_normSq (z : ℂ) : z.im * z.im ≤ normSq z :=
  le_add_of_nonneg_left (mul_self_nonneg _)
#align complex.im_sq_le_norm_sq Complex.im_sq_le_normSq

theorem mul_conj (z : ℂ) : z * conj z = normSq z :=
  ext_iff.2 <| by simp [normSq, mul_comm, sub_eq_neg_add, add_comm, ofReal']
#align complex.mul_conj Complex.mul_conj

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
  ext_iff.2 <| by simp [two_mul, ofReal']
#align complex.add_conj Complex.add_conj

/-- The coercion `ℝ → ℂ` as a `RingHom`. -/
def ofReal : ℝ →+* ℂ where
  toFun x := (x : ℂ)
  map_one' := ofReal_one
  map_zero' := ofReal_zero
  map_mul' := ofReal_mul
  map_add' := ofReal_add
#align complex.of_real Complex.ofReal

@[simp]
theorem ofReal_eq_coe (r : ℝ) : ofReal r = r :=
  rfl
#align complex.of_real_eq_coe Complex.ofReal_eq_coe

@[simp]
theorem I_sq : I ^ 2 = -1 := by rw [sq, I_mul_I]
set_option linter.uppercaseLean3 false in
#align complex.I_sq Complex.I_sq

@[simp]
theorem I_pow_four : I ^ 4 = 1 := by rw [(by norm_num : 4 = 2 * 2), pow_mul, I_sq, neg_one_sq]

@[simp]
theorem sub_re (z w : ℂ) : (z - w).re = z.re - w.re :=
  rfl
#align complex.sub_re Complex.sub_re

@[simp]
theorem sub_im (z w : ℂ) : (z - w).im = z.im - w.im :=
  rfl
#align complex.sub_im Complex.sub_im

@[simp, norm_cast]
theorem ofReal_sub (r s : ℝ) : ((r - s : ℝ) : ℂ) = r - s :=
  ext_iff.2 <| by simp [ofReal']
#align complex.of_real_sub Complex.ofReal_sub

@[simp, norm_cast]
theorem ofReal_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n := by
  induction n <;> simp [*, ofReal_mul, pow_succ]
#align complex.of_real_pow Complex.ofReal_pow

theorem sub_conj (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I :=
  ext_iff.2 <| by simp [two_mul, sub_eq_add_neg, ofReal']
#align complex.sub_conj Complex.sub_conj

theorem normSq_sub (z w : ℂ) : normSq (z - w) = normSq z + normSq w - 2 * (z * conj w).re := by
  rw [sub_eq_add_neg, normSq_add]
  simp only [RingHom.map_neg, mul_neg, neg_re, normSq_neg]
  ring
#align complex.norm_sq_sub Complex.normSq_sub

/-! ### Inversion -/


noncomputable instance : Inv ℂ :=
  ⟨fun z => conj z * ((normSq z)⁻¹ : ℝ)⟩

theorem inv_def (z : ℂ) : z⁻¹ = conj z * ((normSq z)⁻¹ : ℝ) :=
  rfl
#align complex.inv_def Complex.inv_def

@[simp]
theorem inv_re (z : ℂ) : z⁻¹.re = z.re / normSq z := by simp [inv_def, division_def, ofReal']
#align complex.inv_re Complex.inv_re

@[simp]
theorem inv_im (z : ℂ) : z⁻¹.im = -z.im / normSq z := by simp [inv_def, division_def, ofReal']
#align complex.inv_im Complex.inv_im

@[simp, norm_cast]
theorem ofReal_inv (r : ℝ) : ((r⁻¹ : ℝ) : ℂ) = (r : ℂ)⁻¹ :=
  ext_iff.2 <| by simp [ofReal']
#align complex.of_real_inv Complex.ofReal_inv

protected theorem inv_zero : (0⁻¹ : ℂ) = 0 := by
  rw [← ofReal_zero, ← ofReal_inv, inv_zero]
#align complex.inv_zero Complex.inv_zero

protected theorem mul_inv_cancel {z : ℂ} (h : z ≠ 0) : z * z⁻¹ = 1 := by
  rw [inv_def, ← mul_assoc, mul_conj, ← ofReal_mul, mul_inv_cancel (mt normSq_eq_zero.1 h),
    ofReal_one]
#align complex.mul_inv_cancel Complex.mul_inv_cancel

noncomputable instance instDivInvMonoid : DivInvMonoid ℂ where

lemma div_re (z w : ℂ) : (z / w).re = z.re * w.re / normSq w + z.im * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]
#align complex.div_re Complex.div_re

lemma div_im (z w : ℂ) : (z / w).im = z.im * w.re / normSq w - z.re * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]
#align complex.div_im Complex.div_im

/-! ### Field instance and lemmas -/

noncomputable instance instField : Field ℂ where
  mul_inv_cancel := @Complex.mul_inv_cancel
  inv_zero := Complex.inv_zero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by ext <;> simp [NNRat.cast_def, div_re, div_im, mul_div_mul_comm]
  ratCast_def q := by ext <;> simp [Rat.cast_def, div_re, div_im, mul_div_mul_comm]
  nnqsmul_def n z := ext_iff.2 <| by simp [NNRat.smul_def, smul_re, smul_im]
  qsmul_def n z := ext_iff.2 <| by simp [Rat.smul_def, smul_re, smul_im]
#align complex.field Complex.instField

@[simp, norm_cast]
lemma ofReal_nnqsmul (q : ℚ≥0) (r : ℝ) : ofReal' (q • r) = q • r := by simp [NNRat.smul_def]

@[simp, norm_cast]
lemma ofReal_qsmul (q : ℚ) (r : ℝ) : ofReal' (q • r) = q • r := by simp [Rat.smul_def]

theorem conj_inv (x : ℂ) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv' _
#align complex.conj_inv Complex.conj_inv

@[simp, norm_cast]
theorem ofReal_div (r s : ℝ) : ((r / s : ℝ) : ℂ) = r / s :=
  map_div₀ ofReal r s
#align complex.of_real_div Complex.ofReal_div

@[simp, norm_cast]
theorem ofReal_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n :=
  map_zpow₀ ofReal r n
#align complex.of_real_zpow Complex.ofReal_zpow

@[simp]
theorem div_I (z : ℂ) : z / I = -(z * I) :=
  (div_eq_iff_mul_eq I_ne_zero).2 <| by simp [mul_assoc]
set_option linter.uppercaseLean3 false in
#align complex.div_I Complex.div_I

@[simp]
theorem inv_I : I⁻¹ = -I := by
  rw [inv_eq_one_div, div_I, one_mul]
set_option linter.uppercaseLean3 false in
#align complex.inv_I Complex.inv_I

-- @[simp]
/- Porting note (#11119): `simp` attribute removed as linter reports this can be proved
by `simp only [@map_inv₀]` -/
theorem normSq_inv (z : ℂ) : normSq z⁻¹ = (normSq z)⁻¹ :=
  map_inv₀ normSq z
#align complex.norm_sq_inv Complex.normSq_inv

-- @[simp]
/- Porting note (#11119): `simp` attribute removed as linter reports this can be proved
by `simp only [@map_div₀]` -/
theorem normSq_div (z w : ℂ) : normSq (z / w) = normSq z / normSq w :=
  map_div₀ normSq z w
#align complex.norm_sq_div Complex.normSq_div

lemma div_ofReal (z : ℂ) (x : ℝ) : z / x = ⟨z.re / x, z.im / x⟩ := by
  simp_rw [div_eq_inv_mul, ← ofReal_inv, ofReal_mul']

lemma div_natCast (z : ℂ) (n : ℕ) : z / n = ⟨z.re / n, z.im / n⟩ :=
  mod_cast div_ofReal z n

@[deprecated (since := "2024-04-17")]
alias div_nat_cast := div_natCast

lemma div_intCast (z : ℂ) (n : ℤ) : z / n = ⟨z.re / n, z.im / n⟩ :=
  mod_cast div_ofReal z n

@[deprecated (since := "2024-04-17")]
alias div_int_cast := div_intCast

lemma div_ratCast (z : ℂ) (x : ℚ) : z / x = ⟨z.re / x, z.im / x⟩ :=
  mod_cast div_ofReal z x

@[deprecated (since := "2024-04-17")]
alias div_rat_cast := div_ratCast

lemma div_ofNat (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    z / OfNat.ofNat n = ⟨z.re / OfNat.ofNat n, z.im / OfNat.ofNat n⟩ :=
  div_natCast z n

@[simp] lemma div_ofReal_re (z : ℂ) (x : ℝ) : (z / x).re = z.re / x := by rw [div_ofReal]
@[simp] lemma div_ofReal_im (z : ℂ) (x : ℝ) : (z / x).im = z.im / x := by rw [div_ofReal]
@[simp] lemma div_natCast_re (z : ℂ) (n : ℕ) : (z / n).re = z.re / n := by rw [div_natCast]
@[simp] lemma div_natCast_im (z : ℂ) (n : ℕ) : (z / n).im = z.im / n := by rw [div_natCast]
@[simp] lemma div_intCast_re (z : ℂ) (n : ℤ) : (z / n).re = z.re / n := by rw [div_intCast]
@[simp] lemma div_intCast_im (z : ℂ) (n : ℤ) : (z / n).im = z.im / n := by rw [div_intCast]
@[simp] lemma div_ratCast_re (z : ℂ) (x : ℚ) : (z / x).re = z.re / x := by rw [div_ratCast]
@[simp] lemma div_ratCast_im (z : ℂ) (x : ℚ) : (z / x).im = z.im / x := by rw [div_ratCast]

@[deprecated (since := "2024-04-17")]
alias div_rat_cast_im := div_ratCast_im

@[simp]
lemma div_ofNat_re (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (z / no_index (OfNat.ofNat n)).re = z.re / OfNat.ofNat n := div_natCast_re z n

@[simp]
lemma div_ofNat_im (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (z / no_index (OfNat.ofNat n)).im = z.im / OfNat.ofNat n := div_natCast_im z n

/-! ### Characteristic zero -/


instance instCharZero : CharZero ℂ :=
  charZero_of_inj_zero fun n h => by rwa [← ofReal_natCast, ofReal_eq_zero, Nat.cast_eq_zero] at h
#align complex.char_zero_complex Complex.instCharZero

/-- A complex number `z` plus its conjugate `conj z` is `2` times its real part. -/
theorem re_eq_add_conj (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
  simp only [add_conj, ofReal_mul, ofReal_ofNat, mul_div_cancel_left₀ (z.re : ℂ) two_ne_zero]
#align complex.re_eq_add_conj Complex.re_eq_add_conj

/-- A complex number `z` minus its conjugate `conj z` is `2i` times its imaginary part. -/
theorem im_eq_sub_conj (z : ℂ) : (z.im : ℂ) = (z - conj z) / (2 * I) := by
  simp only [sub_conj, ofReal_mul, ofReal_ofNat, mul_right_comm,
    mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero I_ne_zero : 2 * I ≠ 0)]
#align complex.im_eq_sub_conj Complex.im_eq_sub_conj

/-- Show the imaginary number ⟨x, y⟩ as an "x + y*I" string

Note that the Real numbers used for x and y will show as cauchy sequences due to the way Real
numbers are represented.
-/
unsafe instance instRepr : Repr ℂ where
  reprPrec f p :=
    (if p > 65 then (Std.Format.bracket "(" · ")") else (·)) <|
      reprPrec f.re 65 ++ " + " ++ reprPrec f.im 70 ++ "*I"

end Complex

assert_not_exists Multiset
assert_not_exists Algebra
