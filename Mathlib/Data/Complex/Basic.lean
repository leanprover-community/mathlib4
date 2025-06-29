/-
Copyright (c) 2017 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Mario Carneiro
-/
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Algebra.Star.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Tactic.Ring

/-!
# The complex numbers

The complex numbers are modelled as ℝ^2 in the obvious way and it is shown that they form a field
of characteristic zero. The result that the complex numbers are algebraically closed, see
`FieldTheory.AlgebraicClosure`.
-/

assert_not_exists Multiset Algebra

open Set Function

/-! ### Definition and basic arithmetic -/


/-- Complex numbers consist of two `Real`s: a real part `re` and an imaginary part `im`. -/
structure Complex : Type where
  /-- The real part of a complex number. -/
  re : ℝ
  /-- The imaginary part of a complex number. -/
  im : ℝ

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

@[simp]
theorem eta : ∀ z : ℂ, Complex.mk z.re z.im = z
  | ⟨_, _⟩ => rfl

-- We only mark this lemma with `ext` *locally* to avoid it applying whenever terms of `ℂ` appear.
theorem ext : ∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
  | ⟨_, _⟩, ⟨_, _⟩, rfl, rfl => rfl

attribute [local ext] Complex.ext

lemma «forall» {p : ℂ → Prop} : (∀ x, p x) ↔ ∀ a b, p ⟨a, b⟩ := by aesop
lemma «exists» {p : ℂ → Prop} : (∃ x, p x) ↔ ∃ a b, p ⟨a, b⟩ := by aesop

theorem re_surjective : Surjective re := fun x => ⟨⟨x, 0⟩, rfl⟩

theorem im_surjective : Surjective im := fun y => ⟨⟨0, y⟩, rfl⟩

@[simp]
theorem range_re : range re = univ :=
  re_surjective.range_eq

@[simp]
theorem range_im : range im = univ :=
  im_surjective.range_eq

/-- The natural inclusion of the real numbers into the complex numbers. -/
@[coe]
def ofReal (r : ℝ) : ℂ :=
  ⟨r, 0⟩
instance : Coe ℝ ℂ :=
  ⟨ofReal⟩

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

theorem ofReal_injective : Function.Injective ((↑) : ℝ → ℂ) := fun _ _ => congrArg re

instance canLift : CanLift ℂ ℝ (↑) fun z => z.im = 0 where
  prf z hz := ⟨z.re, ext rfl hz.symm⟩

/-- The product of a set on the real axis and a set on the imaginary axis of the complex plane,
denoted by `s ×ℂ t`. -/
def reProdIm (s t : Set ℝ) : Set ℂ :=
  re ⁻¹' s ∩ im ⁻¹' t

@[deprecated (since := "2024-12-03")] protected alias Set.reProdIm := reProdIm

@[inherit_doc]
infixl:72 " ×ℂ " => reProdIm

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

-- replaced by `re_ofNat`
-- replaced by `im_ofNat`

@[simp, norm_cast]
theorem ofReal_add (r s : ℝ) : ((r + s : ℝ) : ℂ) = r + s :=
  Complex.ext_iff.2 <| by simp [ofReal]

-- replaced by `Complex.ofReal_ofNat`

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
  Complex.ext_iff.2 <| by simp [ofReal]

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
  Complex.ext_iff.2 <| by simp [ofReal]

theorem re_ofReal_mul (r : ℝ) (z : ℂ) : (r * z).re = r * z.re := by simp [ofReal]

theorem im_ofReal_mul (r : ℝ) (z : ℂ) : (r * z).im = r * z.im := by simp [ofReal]

lemma re_mul_ofReal (z : ℂ) (r : ℝ) : (z * r).re = z.re *  r := by simp [ofReal]
lemma im_mul_ofReal (z : ℂ) (r : ℝ) : (z * r).im = z.im *  r := by simp [ofReal]

theorem ofReal_mul' (r : ℝ) (z : ℂ) : ↑r * z = ⟨r * z.re, r * z.im⟩ :=
  ext (re_ofReal_mul _ _) (im_ofReal_mul _ _)

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
  Complex.ext_iff.2 <| by simp

theorem I_mul (z : ℂ) : I * z = ⟨-z.im, z.re⟩ :=
  Complex.ext_iff.2 <| by simp

@[simp] lemma I_ne_zero : (I : ℂ) ≠ 0 := mt (congr_arg im) zero_ne_one.symm

theorem mk_eq_add_mul_I (a b : ℝ) : Complex.mk a b = a + b * I :=
  Complex.ext_iff.2 <| by simp [ofReal]

@[simp]
theorem re_add_im (z : ℂ) : (z.re : ℂ) + z.im * I = z :=
  Complex.ext_iff.2 <| by simp [ofReal]

theorem mul_I_re (z : ℂ) : (z * I).re = -z.im := by simp

theorem mul_I_im (z : ℂ) : (z * I).im = z.re := by simp

theorem I_mul_re (z : ℂ) : (I * z).re = -z.im := by simp

theorem I_mul_im (z : ℂ) : (I * z).im = z.re := by simp

@[simp]
theorem equivRealProd_symm_apply (p : ℝ × ℝ) : equivRealProd.symm p = p.1 + p.2 * I := by
  ext <;> simp [Complex.equivRealProd, ofReal]

/-- The natural `AddEquiv` from `ℂ` to `ℝ × ℝ`. -/
@[simps! +simpRhs apply symm_apply_re symm_apply_im]
def equivRealProdAddHom : ℂ ≃+ ℝ × ℝ :=
  { equivRealProd with map_add' := by simp }

theorem equivRealProdAddHom_symm_apply (p : ℝ × ℝ) :
    equivRealProdAddHom.symm p = p.1 + p.2 * I := equivRealProd_symm_apply p

/-! ### Commutative ring instance and lemmas -/


/- We use a nonstandard formula for the `ℕ` and `ℤ` actions to make sure there is no
diamond from the other actions they inherit through the `ℝ`-action on `ℂ` and action transitivity
defined in `Data.Complex.Module`. -/
instance : Nontrivial ℂ :=
  domain_nontrivial re rfl rfl

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

theorem smul_im (r : R) (z : ℂ) : (r • z).im = r • z.im := by simp [(· • ·), SMul.smul]

@[simp]
theorem real_smul {x : ℝ} {z : ℂ} : x • z = x * z :=
  rfl

end SMul

instance addCommGroup : AddCommGroup ℂ :=
  { zero := (0 : ℂ)
    add := (· + ·)
    neg := Neg.neg
    sub := Sub.sub
    nsmul := fun n z => n • z
    zsmul := fun n z => n • z
    zsmul_zero' := by intros; ext <;> simp [smul_re, smul_im]
    nsmul_zero := by intros; ext <;> simp [smul_re, smul_im]
    nsmul_succ := by intros; ext <;> simp [smul_re, smul_im] <;> ring
    zsmul_succ' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
    zsmul_neg' := by intros; ext <;> simp [smul_re, smul_im] <;> ring
    add_assoc := by intros; ext <;> simp <;> ring
    zero_add := by intros; ext <;> simp
    add_zero := by intros; ext <;> simp
    add_comm := by intros; ext <;> simp <;> ring
    neg_add_cancel := by intros; ext <;> simp }


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
        show -(1 : ℝ) + (-n) = -(↑(n + 1))
        simp [Nat.cast_add, add_comm]
      · simp [AddGroupWithOne.intCast_negSucc]
        show im ⟨n, 0⟩ = 0
        rfl
    one := 1 }

instance commRing : CommRing ℂ :=
  { addGroupWithOne with
    mul := (· * ·)
    npow := @npowRec _ ⟨(1 : ℂ)⟩ ⟨(· * ·)⟩
    add_comm := by intros; ext <;> simp <;> ring
    left_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    right_distrib := by intros; ext <;> simp [mul_re, mul_im] <;> ring
    zero_mul := by intros; ext <;> simp
    mul_zero := by intros; ext <;> simp
    mul_assoc := by intros; ext <;> simp <;> ring
    one_mul := by intros; ext <;> simp
    mul_one := by intros; ext <;> simp
    mul_comm := by intros; ext <;> simp <;> ring }

/-- This shortcut instance ensures we do not find `Ring` via the noncomputable `Complex.field`
instance. -/
instance : Ring ℂ := by infer_instance

/-- This shortcut instance ensures we do not find `CommSemiring` via the noncomputable
`Complex.field` instance. -/
instance : CommSemiring ℂ :=
  inferInstance

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

/-! ### Cast lemmas -/

instance instNNRatCast : NNRatCast ℂ where nnratCast q := ofReal q
instance instRatCast : RatCast ℂ where ratCast q := ofReal q

@[simp, norm_cast] lemma ofReal_ofNat (n : ℕ) [n.AtLeastTwo] : ofReal ofNat(n) = ofNat(n) := rfl
@[simp, norm_cast] lemma ofReal_natCast (n : ℕ) : ofReal n = n := rfl
@[simp, norm_cast] lemma ofReal_intCast (n : ℤ) : ofReal n = n := rfl
@[simp, norm_cast] lemma ofReal_nnratCast (q : ℚ≥0) : ofReal q = q := rfl
@[simp, norm_cast] lemma ofReal_ratCast (q : ℚ) : ofReal q = q := rfl

@[simp]
lemma re_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℂ).re = ofNat(n) := rfl
@[simp] lemma im_ofNat (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma natCast_re (n : ℕ) : (n : ℂ).re = n := rfl
@[simp, norm_cast] lemma natCast_im (n : ℕ) : (n : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma intCast_re (n : ℤ) : (n : ℂ).re = n := rfl
@[simp, norm_cast] lemma intCast_im (n : ℤ) : (n : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma re_nnratCast (q : ℚ≥0) : (q : ℂ).re = q := rfl
@[simp, norm_cast] lemma im_nnratCast (q : ℚ≥0) : (q : ℂ).im = 0 := rfl
@[simp, norm_cast] lemma ratCast_re (q : ℚ) : (q : ℂ).re = q := rfl
@[simp, norm_cast] lemma ratCast_im (q : ℚ) : (q : ℂ).im = 0 := rfl

lemma re_nsmul (n : ℕ) (z : ℂ) : (n • z).re = n • z.re := smul_re ..
lemma im_nsmul (n : ℕ) (z : ℂ) : (n • z).im = n • z.im := smul_im ..
lemma re_zsmul (n : ℤ) (z : ℂ) : (n • z).re = n • z.re := smul_re ..
lemma im_zsmul (n : ℤ) (z : ℂ) : (n • z).im = n • z.im := smul_im ..
@[simp] lemma re_nnqsmul (q : ℚ≥0) (z : ℂ) : (q • z).re = q • z.re := smul_re ..
@[simp] lemma im_nnqsmul (q : ℚ≥0) (z : ℂ) : (q • z).im = q • z.im := smul_im ..
@[simp] lemma re_qsmul (q : ℚ) (z : ℂ) : (q • z).re = q • z.re := smul_re ..
@[simp] lemma im_qsmul (q : ℚ) (z : ℂ) : (q • z).im = q • z.im := smul_im ..

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

@[simp]
theorem conj_im (z : ℂ) : (conj z).im = -z.im :=
  rfl

@[simp]
theorem conj_ofReal (r : ℝ) : conj (r : ℂ) = r :=
  Complex.ext_iff.2 <| by simp [star]

@[simp]
theorem conj_I : conj I = -I :=
  Complex.ext_iff.2 <| by simp

theorem conj_natCast (n : ℕ) : conj (n : ℂ) = n := map_natCast _ _

theorem conj_ofNat (n : ℕ) [n.AtLeastTwo] : conj (ofNat(n) : ℂ) = ofNat(n) :=
  map_ofNat _ _

theorem conj_neg_I : conj (-I) = I := by simp

theorem conj_eq_iff_real {z : ℂ} : conj z = z ↔ ∃ r : ℝ, z = r :=
  ⟨fun h => ⟨z.re, ext rfl <| eq_zero_of_neg_eq (congr_arg im h)⟩, fun ⟨h, e⟩ => by
    rw [e, conj_ofReal]⟩

theorem conj_eq_iff_re {z : ℂ} : conj z = z ↔ (z.re : ℂ) = z :=
  conj_eq_iff_real.trans ⟨by rintro ⟨r, rfl⟩; simp [ofReal], fun h => ⟨_, h.symm⟩⟩

theorem conj_eq_iff_im {z : ℂ} : conj z = z ↔ z.im = 0 :=
  ⟨fun h => add_self_eq_zero.mp (neg_eq_iff_add_eq_zero.mp (congr_arg im h)), fun h =>
    ext rfl (neg_eq_iff_add_eq_zero.mpr (add_self_eq_zero.mpr h))⟩

@[simp]
theorem star_def : (Star.star : ℂ → ℂ) = conj :=
  rfl

/-! ### Norm squared -/


/-- The norm squared function. -/
@[pp_nodot]
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
  simp [normSq, ofReal]

@[simp]
theorem normSq_natCast (n : ℕ) : normSq n = n * n := normSq_ofReal _

@[simp]
theorem normSq_intCast (z : ℤ) : normSq z = z * z := normSq_ofReal _

@[simp]
theorem normSq_ratCast (q : ℚ) : normSq q = q * q := normSq_ofReal _

@[simp]
theorem normSq_ofNat (n : ℕ) [n.AtLeastTwo] :
    normSq (ofNat(n) : ℂ) = ofNat(n) * ofNat(n) :=
  normSq_natCast _

@[simp]
theorem normSq_mk (x y : ℝ) : normSq ⟨x, y⟩ = x * x + y * y :=
  rfl

theorem normSq_add_mul_I (x y : ℝ) : normSq (x + y * I) = x ^ 2 + y ^ 2 := by
  rw [← mk_eq_add_mul_I, normSq_mk, sq, sq]

theorem normSq_eq_conj_mul_self {z : ℂ} : (normSq z : ℂ) = conj z * z := by
  ext <;> simp [normSq, mul_comm, ofReal]

theorem normSq_zero : normSq 0 = 0 := by simp

theorem normSq_one : normSq 1 = 1 := by simp

@[simp]
theorem normSq_I : normSq I = 1 := by simp [normSq]

theorem normSq_nonneg (z : ℂ) : 0 ≤ normSq z :=
  add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)

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
  Complex.ext_iff.2 <| by simp [normSq, mul_comm, sub_eq_neg_add, add_comm, ofReal]

theorem add_conj (z : ℂ) : z + conj z = (2 * z.re : ℝ) :=
  Complex.ext_iff.2 <| by simp [two_mul, ofReal]

/-- The coercion `ℝ → ℂ` as a `RingHom`. -/
def ofRealHom : ℝ →+* ℂ where
  toFun x := (x : ℂ)
  map_one' := ofReal_one
  map_zero' := ofReal_zero
  map_mul' := ofReal_mul
  map_add' := ofReal_add

@[simp] lemma ofRealHom_eq_coe (r : ℝ) : ofRealHom r = r := rfl

variable {α : Type*}

@[simp] lemma ofReal_comp_add (f g : α → ℝ) : ofReal ∘ (f + g) = ofReal ∘ f + ofReal ∘ g :=
  map_comp_add ofRealHom ..

@[simp] lemma ofReal_comp_sub (f g : α → ℝ) : ofReal ∘ (f - g) = ofReal ∘ f - ofReal ∘ g :=
  map_comp_sub ofRealHom ..

@[simp] lemma ofReal_comp_neg (f : α → ℝ) : ofReal ∘ (-f) = -(ofReal ∘ f) :=
  map_comp_neg ofRealHom _

lemma ofReal_comp_nsmul (n : ℕ) (f : α → ℝ) : ofReal ∘ (n • f) = n • (ofReal ∘ f) :=
  map_comp_nsmul ofRealHom ..

lemma ofReal_comp_zsmul (n : ℤ) (f : α → ℝ) : ofReal ∘ (n • f) = n • (ofReal ∘ f) :=
  map_comp_zsmul ofRealHom ..

@[simp] lemma ofReal_comp_mul (f g : α → ℝ) : ofReal ∘ (f * g) = ofReal ∘ f * ofReal ∘ g :=
  map_comp_mul ofRealHom ..

@[simp] lemma ofReal_comp_pow (f : α → ℝ) (n : ℕ) : ofReal ∘ (f ^ n) = (ofReal ∘ f) ^ n :=
  map_comp_pow ofRealHom ..

@[simp]
theorem I_sq : I ^ 2 = -1 := by rw [sq, I_mul_I]

@[simp]
lemma I_pow_three : I ^ 3 = -I := by rw [pow_succ, I_sq, neg_one_mul]

@[simp]
theorem I_pow_four : I ^ 4 = 1 := by rw [(by norm_num : 4 = 2 * 2), pow_mul, I_sq, neg_one_sq]

lemma I_pow_eq_pow_mod (n : ℕ) : I ^ n = I ^ (n % 4) := by
  conv_lhs => rw [← Nat.div_add_mod n 4]
  simp [pow_add, pow_mul, I_pow_four]

@[simp]
theorem sub_re (z w : ℂ) : (z - w).re = z.re - w.re :=
  rfl

@[simp]
theorem sub_im (z w : ℂ) : (z - w).im = z.im - w.im :=
  rfl

@[simp, norm_cast]
theorem ofReal_sub (r s : ℝ) : ((r - s : ℝ) : ℂ) = r - s :=
  Complex.ext_iff.2 <| by simp [ofReal]

@[simp, norm_cast]
theorem ofReal_pow (r : ℝ) (n : ℕ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n := by
  induction n <;> simp [*, ofReal_mul, pow_succ]

theorem sub_conj (z : ℂ) : z - conj z = (2 * z.im : ℝ) * I :=
  Complex.ext_iff.2 <| by simp [two_mul, sub_eq_add_neg, ofReal]

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
theorem inv_re (z : ℂ) : z⁻¹.re = z.re / normSq z := by simp [inv_def, division_def, ofReal]

@[simp]
theorem inv_im (z : ℂ) : z⁻¹.im = -z.im / normSq z := by simp [inv_def, division_def, ofReal]

@[simp, norm_cast]
theorem ofReal_inv (r : ℝ) : ((r⁻¹ : ℝ) : ℂ) = (r : ℂ)⁻¹ :=
  Complex.ext_iff.2 <| by simp [ofReal]

protected theorem inv_zero : (0⁻¹ : ℂ) = 0 := by
  rw [← ofReal_zero, ← ofReal_inv, inv_zero]

protected theorem mul_inv_cancel {z : ℂ} (h : z ≠ 0) : z * z⁻¹ = 1 := by
  rw [inv_def, ← mul_assoc, mul_conj, ← ofReal_mul, mul_inv_cancel₀ (mt normSq_eq_zero.1 h),
    ofReal_one]

noncomputable instance instDivInvMonoid : DivInvMonoid ℂ where

lemma div_re (z w : ℂ) : (z / w).re = z.re * w.re / normSq w + z.im * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg]

lemma div_im (z w : ℂ) : (z / w).im = z.im * w.re / normSq w - z.re * w.im / normSq w := by
  simp [div_eq_mul_inv, mul_assoc, sub_eq_add_neg, add_comm]

/-! ### Field instance and lemmas -/

noncomputable instance instField : Field ℂ where
  mul_inv_cancel := @Complex.mul_inv_cancel
  inv_zero := Complex.inv_zero
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by ext <;> simp [NNRat.cast_def, div_re, div_im, mul_div_mul_comm]
  ratCast_def q := by ext <;> simp [Rat.cast_def, div_re, div_im, mul_div_mul_comm]
  nnqsmul_def n z := Complex.ext_iff.2 <| by simp [NNRat.smul_def, smul_re, smul_im]
  qsmul_def n z := Complex.ext_iff.2 <| by simp [Rat.smul_def, smul_re, smul_im]

@[simp, norm_cast]
lemma ofReal_nnqsmul (q : ℚ≥0) (r : ℝ) : ofReal (q • r) = q • r := by simp [NNRat.smul_def]

@[simp, norm_cast]
lemma ofReal_qsmul (q : ℚ) (r : ℝ) : ofReal (q • r) = q • r := by simp [Rat.smul_def]

theorem conj_inv (x : ℂ) : conj x⁻¹ = (conj x)⁻¹ :=
  star_inv₀ _

@[simp, norm_cast]
theorem ofReal_div (r s : ℝ) : ((r / s : ℝ) : ℂ) = r / s := map_div₀ ofRealHom r s

@[simp, norm_cast]
theorem ofReal_zpow (r : ℝ) (n : ℤ) : ((r ^ n : ℝ) : ℂ) = (r : ℂ) ^ n := map_zpow₀ ofRealHom r n

@[simp]
theorem div_I (z : ℂ) : z / I = -(z * I) :=
  (div_eq_iff_mul_eq I_ne_zero).2 <| by simp [mul_assoc]

@[simp]
theorem inv_I : I⁻¹ = -I := by
  rw [inv_eq_one_div, div_I, one_mul]

theorem normSq_inv (z : ℂ) : normSq z⁻¹ = (normSq z)⁻¹ := by simp

theorem normSq_div (z w : ℂ) : normSq (z / w) = normSq z / normSq w := by simp

lemma div_ofReal (z : ℂ) (x : ℝ) : z / x = ⟨z.re / x, z.im / x⟩ := by
  simp_rw [div_eq_inv_mul, ← ofReal_inv, ofReal_mul']

lemma div_natCast (z : ℂ) (n : ℕ) : z / n = ⟨z.re / n, z.im / n⟩ :=
  mod_cast div_ofReal z n

lemma div_intCast (z : ℂ) (n : ℤ) : z / n = ⟨z.re / n, z.im / n⟩ :=
  mod_cast div_ofReal z n

lemma div_ratCast (z : ℂ) (x : ℚ) : z / x = ⟨z.re / x, z.im / x⟩ :=
  mod_cast div_ofReal z x

lemma div_ofNat (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    z / ofNat(n) = ⟨z.re / ofNat(n), z.im / ofNat(n)⟩ :=
  div_natCast z n

@[simp] lemma div_ofReal_re (z : ℂ) (x : ℝ) : (z / x).re = z.re / x := by rw [div_ofReal]
@[simp] lemma div_ofReal_im (z : ℂ) (x : ℝ) : (z / x).im = z.im / x := by rw [div_ofReal]
@[simp] lemma div_natCast_re (z : ℂ) (n : ℕ) : (z / n).re = z.re / n := by rw [div_natCast]
@[simp] lemma div_natCast_im (z : ℂ) (n : ℕ) : (z / n).im = z.im / n := by rw [div_natCast]
@[simp] lemma div_intCast_re (z : ℂ) (n : ℤ) : (z / n).re = z.re / n := by rw [div_intCast]
@[simp] lemma div_intCast_im (z : ℂ) (n : ℤ) : (z / n).im = z.im / n := by rw [div_intCast]
@[simp] lemma div_ratCast_re (z : ℂ) (x : ℚ) : (z / x).re = z.re / x := by rw [div_ratCast]
@[simp] lemma div_ratCast_im (z : ℂ) (x : ℚ) : (z / x).im = z.im / x := by rw [div_ratCast]

@[simp]
lemma div_ofNat_re (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (z / ofNat(n)).re = z.re / ofNat(n) := div_natCast_re z n

@[simp]
lemma div_ofNat_im (z : ℂ) (n : ℕ) [n.AtLeastTwo] :
    (z / ofNat(n)).im = z.im / ofNat(n) := div_natCast_im z n

/-! ### Characteristic zero -/


instance instCharZero : CharZero ℂ :=
  charZero_of_inj_zero fun n h => by rwa [← ofReal_natCast, ofReal_eq_zero, Nat.cast_eq_zero] at h

/-- A complex number `z` plus its conjugate `conj z` is `2` times its real part. -/
theorem re_eq_add_conj (z : ℂ) : (z.re : ℂ) = (z + conj z) / 2 := by
  simp only [add_conj, ofReal_mul, ofReal_ofNat, mul_div_cancel_left₀ (z.re : ℂ) two_ne_zero]

/-- A complex number `z` minus its conjugate `conj z` is `2i` times its imaginary part. -/
theorem im_eq_sub_conj (z : ℂ) : (z.im : ℂ) = (z - conj z) / (2 * I) := by
  simp only [sub_conj, ofReal_mul, ofReal_ofNat, mul_right_comm,
    mul_div_cancel_left₀ _ (mul_ne_zero two_ne_zero I_ne_zero : 2 * I ≠ 0)]

/-- Show the imaginary number ⟨x, y⟩ as an "x + y*I" string

Note that the Real numbers used for x and y will show as cauchy sequences due to the way Real
numbers are represented.
-/
unsafe instance instRepr : Repr ℂ where
  reprPrec f p :=
    (if p > 65 then (Std.Format.bracket "(" · ")") else (·)) <|
      reprPrec f.re 65 ++ " + " ++ reprPrec f.im 70 ++ "*I"

section reProdIm

/-- The preimage under `equivRealProd` of `s ×ˢ t` is `s ×ℂ t`. -/
lemma preimage_equivRealProd_prod (s t : Set ℝ) : equivRealProd ⁻¹' (s ×ˢ t) = s ×ℂ t := rfl

/-- The inequality `s × t ⊆ s₁ × t₁` holds in `ℂ` iff it holds in `ℝ × ℝ`. -/
lemma reProdIm_subset_iff {s s₁ t t₁ : Set ℝ} : s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ×ˢ t ⊆ s₁ ×ˢ t₁ := by
  rw [← @preimage_equivRealProd_prod s t, ← @preimage_equivRealProd_prod s₁ t₁]
  exact Equiv.preimage_subset equivRealProd _ _

/-- If `s ⊆ s₁ ⊆ ℝ` and `t ⊆ t₁ ⊆ ℝ`, then `s × t ⊆ s₁ × t₁` in `ℂ`. -/
lemma reProdIm_subset_iff' {s s₁ t t₁ : Set ℝ} :
    s ×ℂ t ⊆ s₁ ×ℂ t₁ ↔ s ⊆ s₁ ∧ t ⊆ t₁ ∨ s = ∅ ∨ t = ∅ := by
  convert prod_subset_prod_iff
  exact reProdIm_subset_iff

variable {s t : Set ℝ}

@[simp] lemma reProdIm_nonempty : (s ×ℂ t).Nonempty ↔ s.Nonempty ∧ t.Nonempty := by
  simp [Set.Nonempty, reProdIm, Complex.exists]

@[simp] lemma reProdIm_eq_empty : s ×ℂ t = ∅ ↔ s = ∅ ∨ t = ∅ := by
  simp [← not_nonempty_iff_eq_empty, reProdIm_nonempty, -not_and, not_and_or]

end reProdIm

open scoped Interval

section Rectangle

/-- A `Rectangle` is an axis-parallel rectangle with corners `z` and `w`. -/
def Rectangle (z w : ℂ) : Set ℂ := [[z.re, w.re]] ×ℂ [[z.im, w.im]]

end Rectangle

section Segments

/-- A real segment `[a₁, a₂]` translated by `b * I` is the complex line segment. -/
lemma horizontalSegment_eq (a₁ a₂ b : ℝ) :
    (fun (x : ℝ) ↦ x + b * I) '' [[a₁, a₂]] = [[a₁, a₂]] ×ℂ {b} := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.re, x₁, by simp⟩

/-- A vertical segment `[b₁, b₂]` translated by `a` is the complex line segment. -/
lemma verticalSegment_eq (a b₁ b₂ : ℝ) :
    (fun (y : ℝ) ↦ a + y * I) '' [[b₁, b₂]] = {a} ×ℂ [[b₁, b₂]] := by
  rw [← preimage_equivRealProd_prod]
  ext x
  constructor
  · intro hx
    obtain ⟨x₁, hx₁, hx₁'⟩ := hx
    simp [← hx₁', mem_preimage, mem_prod, hx₁]
  · intro hx
    simp only [equivRealProd_apply, singleton_prod, mem_image, Prod.mk.injEq,
      exists_eq_right_right, mem_preimage] at hx
    obtain ⟨x₁, hx₁, hx₁', hx₁''⟩ := hx
    refine ⟨x.im, x₁, by simp⟩

end Segments

end Complex
