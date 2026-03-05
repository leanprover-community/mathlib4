/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
module

public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.RingTheory.GradedAlgebra.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Homogeneous Localization

## Notation
- `ι` is a commutative monoid;
- `A` is a commutative ring;
- `σ` is a class of additive subgroups of `A`;
- `𝒜 : ι → σ` is the grading of `A`;
- `x : Submonoid A` is a submonoid

## Main definitions and results

This file constructs the subring of `Aₓ` where the numerator and denominator have the same grading,
i.e. `{a/b ∈ Aₓ | ∃ (i : ι), a ∈ 𝒜ᵢ ∧ b ∈ 𝒜ᵢ}`.

* `HomogeneousLocalization.NumDenSameDeg`: a structure with a numerator and denominator field
  where they are required to have the same grading.

However `NumDenSameDeg 𝒜 x` cannot have a ring structure for many reasons, for example if `c`
is a `NumDenSameDeg`, then generally, `c + (-c)` is not necessarily `0` for degree reasons ---
`0` is considered to have grade zero (see `deg_zero`) but `c + (-c)` has the same degree as `c`. To
circumvent this, we quotient `NumDenSameDeg 𝒜 x` by the kernel of `c ↦ c.num / c.den`.

* `HomogeneousLocalization.NumDenSameDeg.embedding`: for `x : Submonoid A` and any
  `c : NumDenSameDeg 𝒜 x`, or equivalent a numerator and a denominator of the same degree,
  we get an element `c.num / c.den` of `Aₓ`.
* `HomogeneousLocalization`: `NumDenSameDeg 𝒜 x` quotiented by kernel of `embedding 𝒜 x`.
* `HomogeneousLocalization.val`: if `f : HomogeneousLocalization 𝒜 x`, then `f.val` is an element
  of `Aₓ`. In another word, one can view `HomogeneousLocalization 𝒜 x` as a subring of `Aₓ`
  through `HomogeneousLocalization.val`.
* `HomogeneousLocalization.num`: if `f : HomogeneousLocalization 𝒜 x`, then `f.num : A` is the
  numerator of `f`.
* `HomogeneousLocalization.den`: if `f : HomogeneousLocalization 𝒜 x`, then `f.den : A` is the
  denominator of `f`.
* `HomogeneousLocalization.deg`: if `f : HomogeneousLocalization 𝒜 x`, then `f.deg : ι` is the
  degree of `f` such that `f.num ∈ 𝒜 f.deg` and `f.den ∈ 𝒜 f.deg`
  (see `HomogeneousLocalization.num_mem_deg` and `HomogeneousLocalization.den_mem_deg`).
* `HomogeneousLocalization.num_mem_deg`: if `f : HomogeneousLocalization 𝒜 x`, then
  `f.num_mem_deg` is a proof that `f.num ∈ 𝒜 f.deg`.
* `HomogeneousLocalization.den_mem_deg`: if `f : HomogeneousLocalization 𝒜 x`, then
  `f.den_mem_deg` is a proof that `f.den ∈ 𝒜 f.deg`.
* `HomogeneousLocalization.eq_num_div_den`: if `f : HomogeneousLocalization 𝒜 x`, then
  `f.val : Aₓ` is equal to `f.num / f.den`.

* `HomogeneousLocalization.isLocalRing`: `HomogeneousLocalization 𝒜 x` is a local ring when `x` is
  the complement of some prime ideals.

* `HomogeneousLocalization.map`: Let `A` and `B` be two graded rings and `g : A → B` a
  grading-preserving ring map. If `P ≤ A` and `Q ≤ B` are submonoids such that `P ≤ g⁻¹(Q)`, then
  `g` induces a ring map between the homogeneous localization of `A` at `P` and the homogeneous
  localization of `B` at `Q`.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/

@[expose] public section


noncomputable section

open DirectSum Pointwise

open DirectSum SetLike

variable {ι A σ : Type*}
variable [CommRing A] [SetLike σ A]

local notation "at " x => Localization x

namespace HomogeneousLocalization

section

/-- Let `x` be a submonoid of `A`, then `NumDenSameDeg 𝒜 x` is a structure with a numerator and a
denominator with same grading such that the denominator is contained in `x`.
-/
structure NumDenSameDeg (𝒜 : ι → σ) (x : Submonoid A) where
  deg : ι
  (num den : 𝒜 deg)
  den_mem : (den : A) ∈ x

end

namespace NumDenSameDeg

open SetLike.GradedMonoid Submodule

@[ext]
theorem ext {𝒜 : ι → σ} (x : Submonoid A)
    {c1 c2 : NumDenSameDeg 𝒜 x} (hdeg : c1.deg = c2.deg) (hnum : (c1.num : A) = c2.num)
    (hden : (c1.den : A) = c2.den) : c1 = c2 := by
  rcases c1 with ⟨i1, ⟨n1, hn1⟩, ⟨d1, hd1⟩, h1⟩
  rcases c2 with ⟨i2, ⟨n2, hn2⟩, ⟨d2, hd2⟩, h2⟩
  dsimp only [Subtype.coe_mk] at *
  subst hdeg hnum hden
  congr

section Neg
variable [NegMemClass σ A] {𝒜 : ι → σ} (x : Submonoid A)

instance : Neg (NumDenSameDeg 𝒜 x) where
  neg c := ⟨c.deg, ⟨-c.num, neg_mem c.num.2⟩, c.den, c.den_mem⟩

@[simp]
theorem deg_neg (c : NumDenSameDeg 𝒜 x) : (-c).deg = c.deg :=
  rfl

@[simp]
theorem num_neg (c : NumDenSameDeg 𝒜 x) : ((-c).num : A) = -c.num :=
  rfl

@[simp]
theorem den_neg (c : NumDenSameDeg 𝒜 x) : ((-c).den : A) = c.den :=
  rfl

end Neg

section SMul

variable {𝒜 : ι → σ} (x : Submonoid A) {α : Type*} [SMul α A] [SMulMemClass σ α A]

instance : SMul α (NumDenSameDeg 𝒜 x) where
  smul m c := ⟨c.deg, m • c.num, c.den, c.den_mem⟩

@[simp]
theorem deg_smul (c : NumDenSameDeg 𝒜 x) (m : α) : (m • c).deg = c.deg :=
  rfl

@[simp]
theorem num_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).num : A) = m • c.num :=
  rfl

@[simp]
theorem den_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).den : A) = c.den :=
  rfl

end SMul

variable [AddSubmonoidClass σ A] {𝒜 : ι → σ} (x : Submonoid A)
variable [AddCommMonoid ι] [DecidableEq ι] [GradedRing 𝒜]

open GradedOne in
instance : One (NumDenSameDeg 𝒜 x) where
  one :=
    { deg := 0
      num := ⟨1, one_mem⟩
      den := ⟨1, one_mem⟩
      den_mem := one_mem _ }

@[simp]
theorem deg_one : (1 : NumDenSameDeg 𝒜 x).deg = 0 :=
  rfl

@[simp]
theorem num_one : ((1 : NumDenSameDeg 𝒜 x).num : A) = 1 :=
  rfl

@[simp]
theorem den_one : ((1 : NumDenSameDeg 𝒜 x).den : A) = 1 :=
  rfl

open GradedOne in
instance : Zero (NumDenSameDeg 𝒜 x) where
  zero := ⟨0, 0, ⟨1, one_mem⟩, one_mem _⟩

@[simp]
theorem deg_zero : (0 : NumDenSameDeg 𝒜 x).deg = 0 :=
  rfl

@[simp]
theorem num_zero : (0 : NumDenSameDeg 𝒜 x).num = 0 :=
  rfl

@[simp]
theorem den_zero : ((0 : NumDenSameDeg 𝒜 x).den : A) = 1 :=
  rfl

open GradedMul in
instance : Mul (NumDenSameDeg 𝒜 x) where
  mul p q :=
    { deg := p.deg + q.deg
      num := ⟨p.num * q.num, mul_mem p.num.prop q.num.prop⟩
      den := ⟨p.den * q.den, mul_mem p.den.prop q.den.prop⟩
      den_mem := Submonoid.mul_mem _ p.den_mem q.den_mem }

@[simp]
theorem deg_mul (c1 c2 : NumDenSameDeg 𝒜 x) : (c1 * c2).deg = c1.deg + c2.deg :=
  rfl

@[simp]
theorem num_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).num : A) = c1.num * c2.num :=
  rfl

@[simp]
theorem den_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).den : A) = c1.den * c2.den :=
  rfl

instance : Add (NumDenSameDeg 𝒜 x) where
  add c1 c2 :=
    { deg := c1.deg + c2.deg
      num := ⟨c1.den * c2.num + c2.den * c1.num,
        add_mem (GradedMul.mul_mem c1.den.2 c2.num.2)
          (add_comm c2.deg c1.deg ▸ GradedMul.mul_mem c2.den.2 c1.num.2)⟩
      den := ⟨c1.den * c2.den, GradedMul.mul_mem c1.den.2 c2.den.2⟩
      den_mem := Submonoid.mul_mem _ c1.den_mem c2.den_mem }

@[simp]
theorem deg_add (c1 c2 : NumDenSameDeg 𝒜 x) : (c1 + c2).deg = c1.deg + c2.deg :=
  rfl

@[simp]
theorem num_add (c1 c2 : NumDenSameDeg 𝒜 x) :
    ((c1 + c2).num : A) = c1.den * c2.num + c2.den * c1.num :=
  rfl

@[simp]
theorem den_add (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 + c2).den : A) = c1.den * c2.den :=
  rfl

instance : CommMonoid (NumDenSameDeg 𝒜 x) where
  mul_assoc _ _ _ := ext _ (add_assoc _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul _ := ext _ (zero_add _) (one_mul _) (one_mul _)
  mul_one _ := ext _ (add_zero _) (mul_one _) (mul_one _)
  mul_comm _ _ := ext _ (add_comm _ _) (mul_comm _ _) (mul_comm _ _)

instance : Pow (NumDenSameDeg 𝒜 x) ℕ where
  pow c n :=
    ⟨n • c.deg, @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.num,
      @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.den, by
        induction n with
        | zero => simp only [coe_gnpow, pow_zero, one_mem]
        | succ n ih => simpa only [pow_succ, coe_gnpow] using x.mul_mem ih c.den_mem⟩

@[simp]
theorem deg_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : (c ^ n).deg = n • c.deg :=
  rfl

@[simp]
theorem num_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : ((c ^ n).num : A) = (c.num : A) ^ n :=
  rfl

@[simp]
theorem den_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : ((c ^ n).den : A) = (c.den : A) ^ n :=
  rfl

variable (𝒜)

/-- For `x : prime ideal of A` and any `p : NumDenSameDeg 𝒜 x`, or equivalent a numerator and a
denominator of the same degree, we get an element `p.num / p.den` of `Aₓ`.
-/
def embedding (p : NumDenSameDeg 𝒜 x) : at x :=
  Localization.mk p.num ⟨p.den, p.den_mem⟩

end NumDenSameDeg

end HomogeneousLocalization

/-- For `x : prime ideal of A`, `HomogeneousLocalization 𝒜 x` is `NumDenSameDeg 𝒜 x` modulo the
kernel of `embedding 𝒜 x`. This is essentially the subring of `Aₓ` where the numerator and
denominator share the same grading.
-/
def HomogeneousLocalization (𝒜 : ι → σ) (x : Submonoid A) : Type _ :=
  Quotient (Setoid.ker <| HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 x)

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

section
variable {𝒜 : ι → σ} {x : Submonoid A}

/-- Construct an element of `HomogeneousLocalization 𝒜 x` from a homogeneous fraction. -/
abbrev mk (y : HomogeneousLocalization.NumDenSameDeg 𝒜 x) : HomogeneousLocalization 𝒜 x :=
  Quotient.mk'' y

lemma mk_surjective : Function.Surjective (mk (𝒜 := 𝒜) (x := x)) :=
  Quotient.mk''_surjective

/-- View an element of `HomogeneousLocalization 𝒜 x` as an element of `Aₓ` by forgetting that the
numerator and denominator are of the same grading.
-/
def val (y : HomogeneousLocalization 𝒜 x) : at x :=
  Quotient.liftOn' y (NumDenSameDeg.embedding 𝒜 x) fun _ _ => id

@[simp]
theorem val_mk (i : NumDenSameDeg 𝒜 x) :
    val (mk i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩ :=
  rfl

variable (x)

@[ext]
theorem val_injective : Function.Injective (HomogeneousLocalization.val (𝒜 := 𝒜) (x := x)) :=
  fun a b => Quotient.recOnSubsingleton₂' a b fun _ _ h => Quotient.sound' h

variable (𝒜) {x} in
lemma subsingleton (hx : 0 ∈ x) : Subsingleton (HomogeneousLocalization 𝒜 x) :=
  have := IsLocalization.subsingleton (S := at x) hx
  (HomogeneousLocalization.val_injective (𝒜 := 𝒜) (x := x)).subsingleton

end

section SMul
variable {𝒜 : ι → σ} (x : Submonoid A)
variable {α : Type*} [SMul α A] [IsScalarTower α A A] [SMulMemClass σ α A]

instance : SMul α (HomogeneousLocalization 𝒜 x) where
  smul m := Quotient.map' (m • ·) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    simp only [num_smul, den_smul]
    convert congr_arg (fun z : at x => m • z) h <;> rw [Localization.smul_mk]

@[simp] lemma mk_smul (i : NumDenSameDeg 𝒜 x) (m : α) : mk (m • i) = m • mk i := rfl

@[simp]
theorem val_smul (n : α) : ∀ y : HomogeneousLocalization 𝒜 x, (n • y).val = n • y.val :=
  Quotient.ind' fun _ ↦ by rw [← mk_smul, val_mk, val_mk, Localization.smul_mk, num_smul]; rfl

end SMul

section nsmul
variable [AddSubmonoidClass σ A] {𝒜 : ι → σ} (x : Submonoid A)

instance : SMul ℕ (HomogeneousLocalization 𝒜 x) :=
  haveI := AddSubmonoidClass.nsmulMemClass (S := σ) (M := A)
  HomogeneousLocalization.instSMul x

theorem val_nsmul (n : ℕ) (y : HomogeneousLocalization 𝒜 x) : (n • y).val = n • y.val := by
  rw [val_smul, OreLocalization.nsmul_eq_nsmul]

end nsmul

section zsmul
variable [AddSubgroupClass σ A] {𝒜 : ι → σ} (x : Submonoid A)

instance : SMul ℤ (HomogeneousLocalization 𝒜 x) :=
  haveI := AddSubgroupClass.zsmulMemClass (S := σ) (M := A)
  HomogeneousLocalization.instSMul x

theorem val_zsmul (n : ℤ) (y : HomogeneousLocalization 𝒜 x) : (n • y).val = n • y.val := by
  rw [val_smul, OreLocalization.zsmul_eq_zsmul]

end zsmul

section Neg
variable [NegMemClass σ A] {𝒜 : ι → σ} (x : Submonoid A)

instance : Neg (HomogeneousLocalization 𝒜 x) where
  neg := Quotient.map' Neg.neg fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    simp only [num_neg, den_neg, ← Localization.neg_mk]
    exact congr_arg Neg.neg h

@[simp] lemma mk_neg (i : NumDenSameDeg 𝒜 x) : mk (-i) = -mk i := rfl

@[simp]
theorem val_neg {x} : ∀ y : HomogeneousLocalization 𝒜 x, (-y).val = -y.val :=
  Quotient.ind' fun y ↦ by rw [← mk_neg, val_mk, val_mk, Localization.neg_mk]; rfl

end Neg

variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
variable {𝒜 : ι → σ} [GradedRing 𝒜] (x : Submonoid A)

instance hasPow : Pow (HomogeneousLocalization 𝒜 x) ℕ where
  pow z n :=
    (Quotient.map' (· ^ n) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
          change Localization.mk _ _ = Localization.mk _ _
          simp only [num_pow, den_pow]
          convert congr_arg (fun z : at x => z ^ n) h <;> rw [Localization.mk_pow] <;> rfl :
        HomogeneousLocalization 𝒜 x → HomogeneousLocalization 𝒜 x)
      z

@[simp] lemma mk_pow (i : NumDenSameDeg 𝒜 x) (n : ℕ) : mk (i ^ n) = mk i ^ n := rfl

instance : Add (HomogeneousLocalization 𝒜 x) where
  add :=
    Quotient.map₂ (· + ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_add, den_add]
      convert congr_arg₂ (· + ·) h h' <;> rw [Localization.add_mk] <;> rfl

@[simp] lemma mk_add (i j : NumDenSameDeg 𝒜 x) : mk (i + j) = mk i + mk j := rfl

instance : Sub (HomogeneousLocalization 𝒜 x) where sub z1 z2 := z1 + -z2

instance : Mul (HomogeneousLocalization 𝒜 x) where
  mul :=
    Quotient.map₂ (· * ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_mul, den_mul]
      convert congr_arg₂ (· * ·) h h' <;> rw [Localization.mk_mul] <;> rfl

@[simp] lemma mk_mul (i j : NumDenSameDeg 𝒜 x) : mk (i * j) = mk i * mk j := rfl

instance : One (HomogeneousLocalization 𝒜 x) where one := Quotient.mk'' 1

@[simp] lemma mk_one : mk (1 : NumDenSameDeg 𝒜 x) = 1 := rfl

instance : Zero (HomogeneousLocalization 𝒜 x) where zero := Quotient.mk'' 0

@[simp] lemma mk_zero : mk (0 : NumDenSameDeg 𝒜 x) = 0 := rfl

theorem zero_eq : (0 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 0 :=
  rfl

theorem one_eq : (1 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 1 :=
  rfl

variable {x}

@[simp]
theorem val_zero : (0 : HomogeneousLocalization 𝒜 x).val = 0 :=
  Localization.mk_zero _

@[simp]
theorem val_one : (1 : HomogeneousLocalization 𝒜 x).val = 1 :=
  Localization.mk_one

@[simp]
theorem val_add : ∀ y1 y2 : HomogeneousLocalization 𝒜 x, (y1 + y2).val = y1.val + y2.val :=
  Quotient.ind₂' fun y1 y2 ↦ by rw [← mk_add, val_mk, val_mk, val_mk, Localization.add_mk]; rfl

@[simp]
theorem val_mul : ∀ y1 y2 : HomogeneousLocalization 𝒜 x, (y1 * y2).val = y1.val * y2.val :=
  Quotient.ind₂' fun y1 y2 ↦ by rw [← mk_mul, val_mk, val_mk, val_mk, Localization.mk_mul]; rfl

@[simp]
theorem val_sub (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 - y2).val = y1.val - y2.val := by
  rw [sub_eq_add_neg, ← val_neg, ← val_add]; rfl

@[simp]
theorem val_pow : ∀ (y : HomogeneousLocalization 𝒜 x) (n : ℕ), (y ^ n).val = y.val ^ n :=
  Quotient.ind' fun y n ↦ by rw [← mk_pow, val_mk, val_mk, Localization.mk_pow]; rfl

instance : NatCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Nat.unaryCast⟩

instance : IntCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Int.castDef⟩

@[simp]
theorem val_natCast (n : ℕ) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Nat.unaryCast n) = _ by induction n <;> simp [Nat.unaryCast, *]

@[simp]
theorem val_intCast (n : ℤ) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Int.castDef n) = _ by cases n <;> simp [Int.castDef, *]

instance homogeneousLocalizationCommRing : CommRing (HomogeneousLocalization 𝒜 x) :=
  (HomogeneousLocalization.val_injective x).commRing _ val_zero val_one val_add val_mul val_neg
    val_sub (val_nsmul x · ·) (val_zsmul x · ·) val_pow val_natCast val_intCast

instance homogeneousLocalizationAlgebra :
    Algebra (HomogeneousLocalization 𝒜 x) (Localization x) where
  smul p q := p.val * q
  algebraMap :=
  { toFun := val
    map_one' := val_one
    map_mul' := val_mul
    map_zero' := val_zero
    map_add' := val_add }
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl

@[simp] lemma algebraMap_apply (y) :
    algebraMap (HomogeneousLocalization 𝒜 x) (Localization x) y = y.val := rfl

lemma mk_eq_zero_of_num (f : NumDenSameDeg 𝒜 x) (h : f.num = 0) : mk f = 0 := by
  apply val_injective
  simp only [val_mk, val_zero, h, ZeroMemClass.coe_zero, Localization.mk_zero]

lemma mk_eq_zero_of_den (f : NumDenSameDeg 𝒜 x) (h : f.den = 0) : mk f = 0 := by
  have := subsingleton 𝒜 (h ▸ f.den_mem)
  exact Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
variable (𝒜 x) in
/-- The map from `𝒜 0` to the degree `0` part of `𝒜ₓ` sending `f ↦ f/1`. -/
def fromZeroRingHom : 𝒜 0 →+* HomogeneousLocalization 𝒜 x where
  toFun f := .mk ⟨0, f, 1, one_mem _⟩
  map_one' := rfl
  map_mul' f g := by ext; simp [Localization.mk_mul]
  map_zero' := rfl
  map_add' f g := by ext; simp [Localization.add_mk, add_comm f.1 g.1]

instance : Algebra (𝒜 0) (HomogeneousLocalization 𝒜 x) :=
  (fromZeroRingHom 𝒜 x).toAlgebra

lemma algebraMap_eq : algebraMap (𝒜 0) (HomogeneousLocalization 𝒜 x) = fromZeroRingHom 𝒜 x := rfl

instance : IsScalarTower (𝒜 0) (HomogeneousLocalization 𝒜 x) (Localization x) :=
  .of_algebraMap_eq' rfl

end HomogeneousLocalization

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

section
variable {𝒜 : ι → σ} {x : Submonoid A}

/-- Numerator of an element in `HomogeneousLocalization x`. -/
def num (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out f).num

/-- Denominator of an element in `HomogeneousLocalization x`. -/
def den (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out f).den

/-- For an element in `HomogeneousLocalization x`, degree is the natural number `i` such that
  `𝒜 i` contains both numerator and denominator. -/
def deg (f : HomogeneousLocalization 𝒜 x) : ι :=
  (Quotient.out f).deg

theorem den_mem (f : HomogeneousLocalization 𝒜 x) : f.den ∈ x :=
  (Quotient.out f).den_mem

theorem num_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.num ∈ 𝒜 f.deg :=
  (Quotient.out f).num.2

theorem den_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.den ∈ 𝒜 f.deg :=
  (Quotient.out f).den.2

theorem eq_num_div_den (f : HomogeneousLocalization 𝒜 x) :
    f.val = Localization.mk f.num ⟨f.den, f.den_mem⟩ :=
  congr_arg HomogeneousLocalization.val (Quotient.out_eq' f).symm

theorem den_smul_val (f : HomogeneousLocalization 𝒜 x) :
    f.den • f.val = algebraMap _ _ f.num := by
  rw [eq_num_div_den, Localization.mk_eq_mk', IsLocalization.smul_mk']
  exact IsLocalization.mk'_mul_cancel_left _ ⟨_, _⟩

theorem ext_iff_val (f g : HomogeneousLocalization 𝒜 x) : f = g ↔ f.val = g.val :=
  ⟨congr_arg val, fun e ↦ val_injective x e⟩

end

section

variable [AddSubgroupClass σ A] {𝒜 : ι → σ} {x : Submonoid A}
variable [AddCommMonoid ι] [DecidableEq ι] [GradedRing 𝒜]
variable (𝒜) (𝔭 : Ideal A) [Ideal.IsPrime 𝔭]

/-- Localizing a ring homogeneously at a prime ideal. -/
abbrev AtPrime :=
  HomogeneousLocalization 𝒜 𝔭.primeCompl

theorem isUnit_iff_isUnit_val (f : HomogeneousLocalization.AtPrime 𝒜 𝔭) :
    IsUnit f.val ↔ IsUnit f := by
  refine ⟨fun h1 ↦ ?_, IsUnit.map (algebraMap _ _)⟩
  rcases h1 with ⟨⟨a, b, eq0, eq1⟩, rfl : a = f.val⟩
  obtain ⟨f, rfl⟩ := mk_surjective f
  obtain ⟨b, s, rfl⟩ := IsLocalization.exists_mk'_eq 𝔭.primeCompl b
  rw [val_mk, Localization.mk_eq_mk', ← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq_mul,
    one_mul, IsLocalization.eq_iff_exists (M := 𝔭.primeCompl)] at eq0
  obtain ⟨c, hc : _ = c.1 * (f.den.1 * s.1)⟩ := eq0
  have : f.num.1 ∉ 𝔭 := by
    exact fun h ↦ mul_mem c.2 (mul_mem f.den_mem s.2)
      (hc ▸ Ideal.mul_mem_left _ c.1 (Ideal.mul_mem_right b _ h))
  refine .of_mul_eq_one (Quotient.mk'' ⟨f.1, f.3, f.2, this⟩) ?_
  rw [← mk_mul, ext_iff_val, val_mk]
  simp [mul_comm f.den.1]

instance : Nontrivial (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  ⟨⟨0, 1, fun r => by simp [ext_iff_val, val_zero, val_one, zero_ne_one] at r⟩⟩

instance isLocalRing : IsLocalRing (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simpa only [← isUnit_iff_isUnit_val, val_sub, val_one]
      using IsLocalRing.isUnit_or_isUnit_one_sub_self _

end

section

/-- Localizing away from powers of `f` homogeneously. -/
abbrev Away (𝒜 : ι → σ) (f : A) :=
  HomogeneousLocalization 𝒜 (Submonoid.powers f)

variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
variable (𝒜 : ι → σ) [GradedRing 𝒜] {f : A}

/-- This is a convenient constructor for `Away 𝒜 f` when `f` is homogeneous.
`Away.mk 𝒜 hf n x hx` is the fraction `x / f ^ n`. -/
protected def Away.mk {d : ι} (hf : f ∈ 𝒜 d) (n : ℕ) (x : A) (hx : x ∈ 𝒜 (n • d)) : Away 𝒜 f :=
  HomogeneousLocalization.mk ⟨n • d, ⟨x, hx⟩, ⟨f ^ n, SetLike.pow_mem_graded n hf⟩, ⟨n, rfl⟩⟩

@[simp]
lemma Away.val_mk {d : ι} (n : ℕ) (hf : f ∈ 𝒜 d) (x : A) (hx : x ∈ 𝒜 (n • d)) :
    (Away.mk 𝒜 hf n x hx).val = Localization.mk x ⟨f ^ n, by use n⟩ :=
  rfl

protected
lemma Away.mk_surjective {d : ι} (hf : f ∈ 𝒜 d) (x : Away 𝒜 f) :
    ∃ n a ha, Away.mk 𝒜 hf n a ha = x := by
  obtain ⟨⟨N, ⟨s, hs⟩, ⟨b, hn⟩, ⟨n, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective x
  by_cases hfn : f ^ n = 0
  · have := HomogeneousLocalization.subsingleton 𝒜 (x := .powers f) ⟨n, hfn⟩
    exact ⟨0, 0, zero_mem _, Subsingleton.elim _ _⟩
  obtain rfl := DirectSum.degree_eq_of_mem_mem 𝒜 hn (SetLike.pow_mem_graded n hf) hfn
  exact ⟨n, s, hs, by ext; simp⟩

variable {𝒜 : ι → σ} [GradedRing 𝒜] {f : A}

theorem Away.eventually_smul_mem {m} (hf : f ∈ 𝒜 m) (z : Away 𝒜 f) :
    ∀ᶠ n in Filter.atTop, f ^ n • z.val ∈ algebraMap _ _ '' (𝒜 (n • m) : Set A) := by
  obtain ⟨k, hk : f ^ k = _⟩ := z.den_mem
  apply Filter.mem_of_superset (Filter.Ici_mem_atTop k)
  rintro k' (hk' : k ≤ k')
  simp only [Set.mem_image, SetLike.mem_coe, Set.mem_setOf_eq]
  by_cases hfk : f ^ k = 0
  · refine ⟨0, zero_mem _, ?_⟩
    rw [← tsub_add_cancel_of_le hk', map_zero, pow_add, hfk, mul_zero, zero_smul]
  rw [← tsub_add_cancel_of_le hk', pow_add, mul_smul, hk, den_smul_val,
    Algebra.smul_def, ← map_mul]
  rw [← smul_eq_mul, add_smul,
    DirectSum.degree_eq_of_mem_mem 𝒜 (SetLike.pow_mem_graded _ hf) (hk.symm ▸ z.den_mem_deg) hfk]
  exact ⟨_, SetLike.mul_mem_graded (SetLike.pow_mem_graded _ hf) z.num_mem_deg, rfl⟩

end

section

variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
variable (𝒜 : ι → σ) [GradedRing 𝒜]
variable {B τ : Type*} [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
variable (ℬ : ι → τ) [GradedRing ℬ]
variable {P : Submonoid A} {Q : Submonoid B}

open Graded

/--
Let `A, B` be two graded rings with the same indexing set and `g : 𝒜 →+*ᵍ ℬ` be a graded ring
homomorphism. Let `P ≤ A` be a submonoid and `Q ≤ B` be a submonoid such that `P ≤ g⁻¹ Q`, then `g`
induces a map from the homogeneous localization `A⁰_P` to the homogeneous localization `B⁰_Q`.
-/
def map (g : 𝒜 →+*ᵍ ℬ) (comap_le : P ≤ Q.comap g) :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q where
  toFun := Quotient.map'
    (fun x ↦ ⟨x.1, ⟨_, map_mem g x.2.2⟩, ⟨_, map_mem g x.3.2⟩, comap_le x.4⟩)
    fun x y (e : x.embedding = y.embedding) ↦ by
      apply_fun IsLocalization.map (Localization Q) g.toRingHom comap_le at e
      simp_rw [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
        IsLocalization.map_mk', ← Localization.mk_eq_mk'] at e
      exact e
  map_add' := Quotient.ind₂' fun x y ↦ by
    simp only [← mk_add, Quotient.map'_mk'', num_add, map_add, map_mul, den_add]; rfl
  map_mul' := Quotient.ind₂' fun x y ↦ by
    simp only [← mk_mul, Quotient.map'_mk'', num_mul, map_mul, den_mul]; rfl
  map_zero' := by simp only [← mk_zero (𝒜 := 𝒜), Quotient.map'_mk'', deg_zero,
    num_zero, ZeroMemClass.coe_zero, map_zero, den_zero, map_one]; rfl
  map_one' := by simp only [← mk_one (𝒜 := 𝒜), Quotient.map'_mk'',
    num_one, den_one, map_one]; rfl

/--
Let `A` be a graded ring and `P ≤ Q` be two submonoids, then the homogeneous localization of `A`
at `P` embeds into the homogeneous localization of `A` at `Q`.
-/
abbrev mapId {P Q : Submonoid A} (h : P ≤ Q) :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization 𝒜 Q :=
  map 𝒜 𝒜 (GradedRingHom.id _) h

lemma map_mk (g : 𝒜 →+*ᵍ ℬ) (comap_le : P ≤ Q.comap g) (x) :
    map 𝒜 ℬ g comap_le (mk x) =
    mk ⟨x.1, ⟨_, map_mem g x.2.2⟩, ⟨_, map_mem g x.3.2⟩, comap_le x.4⟩ :=
  rfl

/-- If `g : 𝒜 →+*ᵍ ℬ` is a graded ring homomorphism and `f : A` then we have a map
`Away 𝒜 f →+* Away ℬ (g f)`. -/
protected def Away.map (g : 𝒜 →+*ᵍ ℬ) (f : A) : Away 𝒜 f →+* Away ℬ (g f) :=
  map _ _ g <| by rintro _ ⟨n, rfl⟩; exact ⟨n, by simp⟩

@[simp] lemma Away.map_mk {d : ι} (g : 𝒜 →+*ᵍ ℬ) (f : A) (hf : f ∈ 𝒜 d) (n : ℕ) (x : A)
    (hx : x ∈ 𝒜 (n • d)) :
    Away.map 𝒜 ℬ g f (.mk 𝒜 hf n x hx) = .mk ℬ (map_mem g hf) n (g x) (map_mem g hx) := by
  simp [Away.map, Away.mk, HomogeneousLocalization.map_mk]

end

section mapAway

variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι]
variable (𝒜 : ι → σ) [GradedRing 𝒜]
variable {e : ι} {f : A} {g : A} (hg : g ∈ 𝒜 e) {x : A} (hx : x = f * g)

set_option backward.privateInPublic true in
/-- Given `f ∣ x`, this is the map `A_{(f)} → A_f → A_x`. We will lift this to a map
`A_{(f)} → A_{(x)}` in `awayMap`. -/
private def awayMapAux (hx : f ∣ x) : Away 𝒜 f →+* Localization.Away x :=
  (Localization.awayLift (algebraMap A _) _
    (isUnit_of_dvd_unit (map_dvd _ hx) (IsLocalization.Away.algebraMap_isUnit x))).comp
      (algebraMap (Away 𝒜 f) (Localization.Away f))

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
lemma awayMapAux_mk (n a i hi) :
    awayMapAux 𝒜 ⟨_, hx⟩ (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩) =
      Localization.mk (a * g ^ i) ⟨x ^ i, (Submonoid.mem_powers_iff _ _).mpr ⟨i, rfl⟩⟩ := by
  have : algebraMap A (Localization.Away x) f *
    (Localization.mk g ⟨f * g, (Submonoid.mem_powers_iff _ _).mpr ⟨1, by simp [hx]⟩⟩) = 1 := by
    rw [← Algebra.smul_def, Localization.smul_mk]
    exact Localization.mk_self ⟨f*g, _⟩
  simp only [awayMapAux, RingHom.coe_comp, Function.comp_apply, algebraMap_apply, val_mk]
  rw [Localization.awayLift_mk (hv := this), ← Algebra.smul_def,
    Localization.mk_pow, Localization.smul_mk]
  subst hx
  rfl

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
include hg in
lemma range_awayMapAux_subset :
    Set.range (awayMapAux 𝒜 (f := f) ⟨_, hx⟩) ⊆ Set.range (val (𝒜 := 𝒜)) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb'⟩, j, rfl : _ = b⟩, rfl⟩ := mk_surjective z
  use mk ⟨n+j•e,⟨a*g^j, ?_⟩, ⟨x^j, ?_⟩, j, rfl⟩
  · simp [awayMapAux_mk 𝒜 (hx := hx)]
  · apply SetLike.mul_mem_graded ha
    exact SetLike.pow_mem_graded _ hg
  · rw [hx, mul_pow]
    apply SetLike.mul_mem_graded hb'
    exact SetLike.pow_mem_graded _ hg

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Given `x = f * g` with `g` homogeneous of positive degree,
this is the map `A_{(f)} → A_{(x)}` taking `a/f^i` to `ag^i/(fg)^i`. -/
def awayMap : Away 𝒜 f →+* Away 𝒜 x := by
  let e := RingEquiv.ofLeftInverse (f := algebraMap (Away 𝒜 x) (Localization.Away x))
    (h := (val_injective _).hasLeftInverse.choose_spec)
  refine RingHom.comp (e.symm.toRingHom.comp (Subring.inclusion ?_))
    (awayMapAux 𝒜 (f := f) ⟨_, hx⟩).rangeRestrict
  exact range_awayMapAux_subset 𝒜 hg hx

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
lemma val_awayMap_eq_aux (a) : (awayMap 𝒜 hg hx a).val = awayMapAux 𝒜 ⟨_, hx⟩ a := by
  let e := RingEquiv.ofLeftInverse (f := algebraMap (Away 𝒜 x) (Localization.Away x))
    (h := (val_injective _).hasLeftInverse.choose_spec)
  dsimp [awayMap]
  convert_to (e (e.symm ⟨awayMapAux 𝒜 (f := f) ⟨_, hx⟩ a,
    range_awayMapAux_subset 𝒜 hg hx ⟨_, rfl⟩⟩)).1 = _
  rw [e.apply_symm_apply]

lemma val_awayMap (a) : (awayMap 𝒜 hg hx a).val = Localization.awayLift (algebraMap A _) _
    (isUnit_of_dvd_unit (map_dvd _ ⟨_, hx⟩) (IsLocalization.Away.algebraMap_isUnit x)) a.val := by
  rw [val_awayMap_eq_aux]
  rfl

lemma awayMap_fromZeroRingHom (a) :
    awayMap 𝒜 hg hx (fromZeroRingHom 𝒜 _ a) = fromZeroRingHom 𝒜 _ a := by
  ext
  simp only [fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    val_awayMap, val_mk]
  convert IsLocalization.lift_eq _ _

lemma val_awayMap_mk (n a i hi) : (awayMap 𝒜 hg hx (mk ⟨n, a, ⟨f ^ i, hi⟩, ⟨i, rfl⟩⟩)).val =
    Localization.mk (a * g ^ i) ⟨x ^ i, (Submonoid.mem_powers_iff _ _).mpr ⟨i, rfl⟩⟩ := by
  rw [val_awayMap_eq_aux, awayMapAux_mk 𝒜 (hx := hx)]

/-- Given `x = f * g` with `g` homogeneous of positive degree,
this is the map `A_{(f)} → A_{(x)}` taking `a/f^i` to `ag^i/(fg)^i`. -/
def awayMapₐ : Away 𝒜 f →ₐ[𝒜 0] Away 𝒜 x where
  __ := awayMap 𝒜 hg hx
  commutes' _ := awayMap_fromZeroRingHom ..

@[simp] lemma awayMapₐ_apply (a) : awayMapₐ 𝒜 hg hx a = awayMap 𝒜 hg hx a := rfl

open SetLike in
@[simp]
lemma awayMap_mk {d : ι} (n : ℕ) (hf : f ∈ 𝒜 d) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayMap 𝒜 hg hx (Away.mk 𝒜 hf n a ha) = Away.mk 𝒜 (hx ▸ mul_mem_graded hf hg) n
      (a * g ^ n) (by rw [smul_add]; exact mul_mem_graded ha (pow_mem_graded n hg)) := by
  ext
  exact val_awayMap_mk ..

end mapAway

section isLocalization

variable [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜]
variable {e d : ℕ} {f : A} (hf : f ∈ 𝒜 d) {g : A} (hg : g ∈ 𝒜 e)

/-- The element `t := g ^ d / f ^ e` such that `A_{(fg)} = A_{(f)}[1/t]`. -/
abbrev Away.isLocalizationElem : Away 𝒜 f :=
  Away.mk 𝒜 hf e (g ^ d) (by convert SetLike.pow_mem_graded d hg using 2; exact mul_comm _ _)

variable {x : A} (hx : x = f * g)

/-- Let `t := g ^ d / f ^ e`, then `A_{(fg)} = A_{(f)}[1/t]`. -/
theorem Away.isLocalization_mul (hd : d ≠ 0) :
    letI := (awayMap 𝒜 hg hx).toAlgebra
    IsLocalization.Away (isLocalizationElem hf hg) (Away 𝒜 x) := by
  letI := (awayMap 𝒜 hg hx).toAlgebra
  constructor; constructor
  · rintro ⟨r, n, rfl⟩
    rw [map_pow, RingHom.algebraMap_toAlgebra]
    let z : Away 𝒜 x := Away.mk 𝒜 (hx ▸ SetLike.mul_mem_graded hf hg) (d + e)
        (g ^ e * f ^ (2 * e + d)) <| by
      convert SetLike.mul_mem_graded (SetLike.pow_mem_graded e hg)
        (SetLike.pow_mem_graded (2 * e + d) hf) using 2
      ring
    refine (isUnit_iff_exists_inv.mpr ⟨z, ?_⟩).pow _
    ext
    simp only [val_mul, val_one, awayMap_mk, Away.val_mk, z, Localization.mk_mul]
    rw [← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    use 1
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, mul_one, hx]
    ring
  · intro z
    obtain ⟨n, s, hs, rfl⟩ := Away.mk_surjective 𝒜 (hx ▸ SetLike.mul_mem_graded hf hg) z
    rcases d with - | d
    · contradiction
    let t : Away 𝒜 f := Away.mk 𝒜 hf (n * (e + 1)) (s * g ^ (n * d)) <| by
      convert SetLike.mul_mem_graded hs (SetLike.pow_mem_graded _ hg) using 2; simp; ring
    refine ⟨⟨t, ⟨_, ⟨n, rfl⟩⟩⟩, ?_⟩
    ext
    simp only [RingHom.algebraMap_toAlgebra, map_pow, awayMap_mk, val_mul, val_mk, val_pow,
      Localization.mk_pow, Localization.mk_mul, t]
    rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp; ring⟩
  · intro a b e
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hf a
    obtain ⟨m, b, hb, rfl⟩ := Away.mk_surjective 𝒜 hf b
    replace e := congr_arg val e
    simp only [RingHom.algebraMap_toAlgebra, awayMap_mk, val_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists] at e
    obtain ⟨⟨_, k, rfl⟩, hc⟩ := e
    refine ⟨⟨_, k + m + n, rfl⟩, ?_⟩
    ext
    simp only [val_mul, val_pow, val_mk, Localization.mk_pow,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists, Submonoid.coe_mul, Localization.mk_mul,
      SubmonoidClass.coe_pow, Subtype.exists, exists_prop]
    refine ⟨_, ⟨k, rfl⟩, ?_⟩
    rcases d with - | d
    · contradiction
    subst hx
    convert congr(f ^ (e * (k + m + n)) * g ^ (d * (k + m + n)) * $hc) using 1 <;> ring

end isLocalization

section span

set_option backward.isDefEq.respectTransparency false in
variable [AddSubgroupClass σ A] [AddCommMonoid ι] [DecidableEq ι] {𝒜 : ι → σ} [GradedRing 𝒜] in
/--
Let `𝒜` be a graded ring, finitely generated (as an algebra) over `𝒜₀` by `{ vᵢ }`,
where `vᵢ` has degree `dvᵢ`.
If `f : A` has degree `d`, then `𝒜_(f)` is generated (as a module) over `𝒜₀` by
elements of the form `(∏ i, vᵢ ^ aᵢ) / fᵃ` such that `∑ aᵢ • dvᵢ = a • d`.
-/
theorem Away.span_mk_prod_pow_eq_top {f : A} {d : ι} (hf : f ∈ 𝒜 d)
    {ι' : Type*} [Fintype ι'] (v : ι' → A)
    (hx : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) (dv : ι' → ι) (hxd : ∀ i, v i ∈ 𝒜 (dv i)) :
    Submodule.span (𝒜 0) { (Away.mk 𝒜 hf a (∏ i, v i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) : Away 𝒜 f) |
        (a : ℕ) (ai : ι' → ℕ) (hai : ∑ i, ai i • dv i = a • d) } = ⊤ := by
  by_cases HH : Subsingleton (HomogeneousLocalization.Away 𝒜 f)
  · exact Subsingleton.elim _ _
  rw [← top_le_iff]
  rintro x -
  obtain ⟨⟨n, ⟨a, ha⟩, ⟨b, hb'⟩, ⟨j, (rfl : _ = b)⟩⟩, rfl⟩ := mk_surjective x
  by_cases hfj : f ^ j = 0
  · exact (HH (HomogeneousLocalization.subsingleton _ ⟨_, hfj⟩)).elim
  have : DirectSum.decompose 𝒜 a n = ⟨a, ha⟩ := Subtype.ext (DirectSum.decompose_of_mem_same 𝒜 ha)
  simp_rw [← this]
  clear this ha
  have : a ∈ Submodule.span (𝒜 0) (Submonoid.closure (Set.range v)) := by
    rw [← Algebra.adjoin_eq_span, hx]
    trivial
  induction this using Submodule.span_induction with
  | mem a ha' =>
    obtain ⟨ai, rfl⟩ := Submonoid.exists_of_mem_closure_range _ _ ha'
    clear ha'
    by_cases H : ∑ i, ai i • dv i = n
    · apply Submodule.subset_span
      refine ⟨j, ai, H.trans ?_, ?_⟩
      · exact DirectSum.degree_eq_of_mem_mem 𝒜 hb'
          (SetLike.pow_mem_graded j hf) hfj
      · ext
        simp only [val_mk, Away.val_mk]
        congr
        refine (DirectSum.decompose_of_mem_same _ ?_).symm
        exact H ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i
    · convert zero_mem (Submodule.span (𝒜 0) _)
      ext
      have : (DirectSum.decompose 𝒜 (∏ i : ι', v i ^ ai i) n).1 = 0 := by
        refine DirectSum.decompose_of_mem_ne _ ?_ H
        exact SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i
      simp [this, Localization.mk_zero]
  | zero =>
    convert zero_mem (Submodule.span (𝒜 0) _)
    ext; simp [Localization.mk_zero]
  | add s t hs ht hs' ht' =>
    convert add_mem hs' ht'
    ext; simp [← Localization.add_mk_self]
  | smul r x hx hx' =>
    convert Submodule.smul_mem _ r hx'
    ext
    simp [Algebra.smul_def, algebraMap_eq, fromZeroRingHom, Localization.mk_mul,
      -decompose_mul, coe_decompose_mul_of_left_mem_zero 𝒜 r.2]

variable [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] in
/-- This is strictly weaker than `Away.adjoin_mk_prod_pow_eq_top`. -/
private
theorem Away.adjoin_mk_prod_pow_eq_top_of_pos {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)
    {ι' : Type*} [Fintype ι'] (v : ι' → A)
    (hx : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) (dv : ι' → ℕ)
    (hxd : ∀ i, v i ∈ 𝒜 (dv i)) (hxd' : ∀ i, 0 < dv i) :
    Algebra.adjoin (𝒜 0) { Away.mk 𝒜 hf a (∏ i, v i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) |
        (a : ℕ) (ai : ι' → ℕ) (hai : ∑ i, ai i • dv i = a • d) (_ : ∀ i, ai i ≤ d) } = ⊤ := by
  rw [← top_le_iff]
  change ⊤ ≤ (Algebra.adjoin (𝒜 0) _).toSubmodule
  rw [← HomogeneousLocalization.Away.span_mk_prod_pow_eq_top hf v hx dv hxd, Submodule.span_le]
  rintro _ ⟨a, ai, hai, rfl⟩
  have H₀ : (a - ∑ i : ι', dv i * (ai i / d)) • d = ∑ k : ι', (ai k % d) • dv k := by
    rw [smul_eq_mul, tsub_mul, ← smul_eq_mul, ← hai]
    conv => enter [1, 1, 2, i]; rw [← Nat.mod_add_div (ai i) d]
    simp_rw [smul_eq_mul, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum, mul_comm d, mul_comm (_ / _)]
    simp only [add_tsub_cancel_right]
  have H : Away.mk 𝒜 hf a (∏ i, v i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) =
      Away.mk 𝒜 hf (a - ∑ i : ι', dv i * (ai i / d)) (∏ i, v i ^ (ai i % d))
      (H₀ ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) *
      ∏ i, Away.isLocalizationElem hf (hxd i) ^ (ai i / d) := by
    apply (show Function.Injective (algebraMap (Away 𝒜 f) (Localization.Away f))
      from val_injective _)
    simp only [map_pow, map_prod, map_mul]
    simp only [HomogeneousLocalization.algebraMap_apply, val_mk,
      Localization.mk_pow, Localization.mk_prod, Localization.mk_mul,
      ← Finset.prod_mul_distrib, ← pow_add, ← pow_mul]
    congr
    · ext i
      congr
      exact Eq.symm (Nat.mod_add_div (ai i) d)
    · simp only [SubmonoidClass.coe_finset_prod, ← pow_add, ← pow_mul,
        Finset.prod_pow_eq_pow_sum, SubmonoidClass.coe_pow]
      rw [tsub_add_cancel_of_le]
      rcases d.eq_zero_or_pos with hd | hd
      · simp [hd]
      rw [← mul_le_mul_iff_of_pos_right hd, ← smul_eq_mul (a := a), ← hai, Finset.sum_mul]
      simp_rw [smul_eq_mul, mul_comm (ai _), mul_assoc]
      gcongr
      exact Nat.div_mul_le_self (ai _) d
  rw [H, SetLike.mem_coe]
  apply (Algebra.adjoin (𝒜 0) _).mul_mem
  · apply Algebra.subset_adjoin
    refine ⟨a - ∑ i : ι', dv i * (ai i / d), (ai · % d), H₀.symm, ?_, rfl⟩
    rcases d.eq_zero_or_pos with hd | hd
    · have : ∀ (x : ι'), ai x = 0 := by simpa [hd, fun i ↦ (hxd' i).ne'] using hai
      simp [this]
    exact fun i ↦ (Nat.mod_lt _ hd).le
  apply prod_mem
  · classical
    rintro j -
    apply pow_mem
    apply Algebra.subset_adjoin
    refine ⟨dv j, Pi.single j d, ?_, ?_, ?_⟩
    · simp [Pi.single_apply, mul_comm]
    · aesop (add simp Pi.single_apply)
    ext
    simp [Pi.single_apply]

variable [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] in
/--
Let `𝒜` be a graded ring, finitely generated (as an algebra) over `𝒜₀` by `{ vᵢ }`,
where `vᵢ` has degree `dvᵢ`.
If `f : A` has degree `d`, then `𝒜_(f)` is generated (as an algebra) over `𝒜₀` by
elements of the form `(∏ i, vᵢ ^ aᵢ) / fᵃ` such that `∑ aᵢ • dvᵢ = a • d` and `∀ i, aᵢ ≤ d`.
-/
theorem Away.adjoin_mk_prod_pow_eq_top {f : A} {d : ℕ} (hf : f ∈ 𝒜 d)
    (ι' : Type*) [Fintype ι'] (v : ι' → A)
    (hx : Algebra.adjoin (𝒜 0) (Set.range v) = ⊤) (dv : ι' → ℕ) (hxd : ∀ i, v i ∈ 𝒜 (dv i)) :
    Algebra.adjoin (𝒜 0) { Away.mk 𝒜 hf a (∏ i, v i ^ ai i)
      (hai ▸ SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i) |
        (a : ℕ) (ai : ι' → ℕ) (hai : ∑ i, ai i • dv i = a • d) (_ : ∀ i, ai i ≤ d) } = ⊤ := by
  classical
  let s := Finset.univ.filter (0 < dv ·)
  have := Away.adjoin_mk_prod_pow_eq_top_of_pos hf (ι' := s) (v ∘ Subtype.val) ?_
    (dv ∘ Subtype.val) (fun _ ↦ hxd _) (by simp [s])
  swap
  · rw [← top_le_iff, ← hx, Algebra.adjoin_le_iff, Set.range_subset_iff]
    intro i
    rcases (dv i).eq_zero_or_pos with hi | hi
    · exact algebraMap_mem (R := 𝒜 0) _ ⟨v i, hi ▸ hxd i⟩
    exact Algebra.subset_adjoin ⟨⟨i, by simpa [s] using hi⟩, rfl⟩
  rw [← top_le_iff, ← this]
  apply Algebra.adjoin_mono
  rintro _ ⟨a, ai, hai : ∑ x ∈ s.attach, _ = _, h, rfl⟩
  refine ⟨a, fun i ↦ if hi : i ∈ s then ai ⟨i, hi⟩ else 0, ?_, ?_, ?_⟩
  · simpa [Finset.sum_attach_eq_sum_dite] using hai
  · simp [apply_dite, dite_apply, h]
  · congr 1
    change _ = ∏ x ∈ s.attach, _
    simp [Finset.prod_attach_eq_prod_dite]

variable [AddSubgroupClass σ A] {𝒜 : ℕ → σ} [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A] in
lemma Away.finiteType (f : A) (d : ℕ) (hf : f ∈ 𝒜 d) :
    Algebra.FiniteType (𝒜 0) (Away 𝒜 f) := by
  constructor
  obtain ⟨s, hs, hs'⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  choose dx hdx hxd using Subtype.forall'.mp hs'
  simp_rw [Subalgebra.fg_def, ← top_le_iff,
    ← Away.adjoin_mk_prod_pow_eq_top hf (ι' := s) Subtype.val (by simpa) dx hxd]
  rcases d.eq_zero_or_pos with hd | hd
  · let f' := Away.mk 𝒜 hf 1 1 (by simp [hd, GradedOne.one_mem])
    refine ⟨{f'}, Set.finite_singleton f', ?_⟩
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨a, ai, hai, hai', rfl⟩
    obtain rfl : ai = 0 := funext <| by simpa [hd, hdx] using hai
    simp only [Finset.univ_eq_attach, Pi.zero_apply, pow_zero, Finset.prod_const_one, mem_coe]
    convert pow_mem (Algebra.self_mem_adjoin_singleton (𝒜 0) f') a using 1
    ext
    simp [f', Localization.mk_pow]
  refine ⟨_, ?_, le_rfl⟩
  let b := ∑ i, dx i
  let s' : Set ((Fin (b + 1)) × (s → Fin (d + 1))) := { ai | ∑ i, (ai.2 i).1 * dx i = ai.1 * d }
  let F : s' → Away 𝒜 f := fun ai ↦ Away.mk 𝒜 hf ai.1.1.1 (∏ i, i ^ (ai.1.2 i).1)
    (by convert SetLike.prod_pow_mem_graded _ _ _ _ fun i _ ↦ hxd i; exact ai.2.symm)
  apply (Set.finite_range F).subset
  rintro _ ⟨a, ai, hai, hai', rfl⟩
  refine ⟨⟨⟨⟨a, ?_⟩, fun i ↦ ⟨ai i, (hai' i).trans_lt d.lt_succ_self⟩⟩, hai⟩, rfl⟩
  rw [Nat.lt_succ_iff, ← mul_le_mul_iff_of_pos_right hd, ← smul_eq_mul, ← hai, Finset.sum_mul]
  simp_rw [smul_eq_mul, mul_comm _ d]
  gcongr
  exact hai' _

end span

end HomogeneousLocalization
