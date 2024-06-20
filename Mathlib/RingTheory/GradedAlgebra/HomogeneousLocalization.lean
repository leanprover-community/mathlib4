/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import Mathlib.RingTheory.Localization.AtPrime
import Mathlib.RingTheory.GradedAlgebra.Basic

#align_import ring_theory.graded_algebra.homogeneous_localization from "leanprover-community/mathlib"@"831c494092374cfe9f50591ed0ac81a25efc5b86"

/-!
# Homogeneous Localization

## Notation
- `ι` is a commutative monoid;
- `R` is a commutative semiring;
- `A` is a commutative ring and an `R`-algebra;
- `𝒜 : ι → Submodule R A` is the grading of `A`;
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

* `HomogeneousLocalization.localRing`: `HomogeneousLocalization 𝒜 x` is a local ring when `x` is
  the complement of some prime ideals.

* `HomogeneousLocalization.map`: Let `A` and `B` be two graded rings and `g : A → B` a grading
  preserving ring map. If `P ≤ A` and `Q ≤ B` are submonoids such that `P ≤ g⁻¹(Q)`, then `g`
  induces a ring map between the homogeneous localization of `A` at `P` and the homogeneous
  localization of `B` at `Q`.

## References

* [Robin Hartshorne, *Algebraic Geometry*][Har77]


-/


noncomputable section

open DirectSum Pointwise

open DirectSum SetLike

variable {ι R A : Type*}
variable [AddCommMonoid ι] [DecidableEq ι]
variable [CommRing R] [CommRing A] [Algebra R A]
variable (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
variable (x : Submonoid A)

local notation "at " x => Localization x

namespace HomogeneousLocalization

section

/-- Let `x` be a submonoid of `A`, then `NumDenSameDeg 𝒜 x` is a structure with a numerator and a
denominator with same grading such that the denominator is contained in `x`.
-/
-- Porting note(#5171): this linter isn't ported yet.
-- @[nolint has_nonempty_instance]
structure NumDenSameDeg where
  deg : ι
  (num den : 𝒜 deg)
  den_mem : (den : A) ∈ x
#align homogeneous_localization.num_denom_same_deg HomogeneousLocalization.NumDenSameDeg

end

namespace NumDenSameDeg

open SetLike.GradedMonoid Submodule

variable {𝒜}

@[ext]
theorem ext {c1 c2 : NumDenSameDeg 𝒜 x} (hdeg : c1.deg = c2.deg) (hnum : (c1.num : A) = c2.num)
    (hden : (c1.den : A) = c2.den) : c1 = c2 := by
  rcases c1 with ⟨i1, ⟨n1, hn1⟩, ⟨d1, hd1⟩, h1⟩
  rcases c2 with ⟨i2, ⟨n2, hn2⟩, ⟨d2, hd2⟩, h2⟩
  dsimp only [Subtype.coe_mk] at *
  subst hdeg hnum hden
  congr
#align homogeneous_localization.num_denom_same_deg.ext HomogeneousLocalization.NumDenSameDeg.ext

instance : One (NumDenSameDeg 𝒜 x) where
  one :=
    { deg := 0
      -- Porting note: Changed `one_mem` to `GradedOne.one_mem`
      num := ⟨1, GradedOne.one_mem⟩
      den := ⟨1, GradedOne.one_mem⟩
      den_mem := Submonoid.one_mem _ }

@[simp]
theorem deg_one : (1 : NumDenSameDeg 𝒜 x).deg = 0 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_one HomogeneousLocalization.NumDenSameDeg.deg_one

@[simp]
theorem num_one : ((1 : NumDenSameDeg 𝒜 x).num : A) = 1 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_one HomogeneousLocalization.NumDenSameDeg.num_one

@[simp]
theorem den_one : ((1 : NumDenSameDeg 𝒜 x).den : A) = 1 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_one HomogeneousLocalization.NumDenSameDeg.den_one

instance : Zero (NumDenSameDeg 𝒜 x) where
  zero := ⟨0, 0, ⟨1, GradedOne.one_mem⟩, Submonoid.one_mem _⟩

@[simp]
theorem deg_zero : (0 : NumDenSameDeg 𝒜 x).deg = 0 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_zero HomogeneousLocalization.NumDenSameDeg.deg_zero

@[simp]
theorem num_zero : (0 : NumDenSameDeg 𝒜 x).num = 0 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_zero HomogeneousLocalization.NumDenSameDeg.num_zero

@[simp]
theorem den_zero : ((0 : NumDenSameDeg 𝒜 x).den : A) = 1 :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_zero HomogeneousLocalization.NumDenSameDeg.den_zero

instance : Mul (NumDenSameDeg 𝒜 x) where
  mul p q :=
    { deg := p.deg + q.deg
      -- Porting note: Changed `mul_mem` to `GradedMul.mul_mem`
      num := ⟨p.num * q.num, GradedMul.mul_mem p.num.prop q.num.prop⟩
      den := ⟨p.den * q.den, GradedMul.mul_mem p.den.prop q.den.prop⟩
      den_mem := Submonoid.mul_mem _ p.den_mem q.den_mem }

@[simp]
theorem deg_mul (c1 c2 : NumDenSameDeg 𝒜 x) : (c1 * c2).deg = c1.deg + c2.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_mul HomogeneousLocalization.NumDenSameDeg.deg_mul

@[simp]
theorem num_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).num : A) = c1.num * c2.num :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_mul HomogeneousLocalization.NumDenSameDeg.num_mul

@[simp]
theorem den_mul (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 * c2).den : A) = c1.den * c2.den :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_mul HomogeneousLocalization.NumDenSameDeg.den_mul

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
#align homogeneous_localization.num_denom_same_deg.deg_add HomogeneousLocalization.NumDenSameDeg.deg_add

@[simp]
theorem num_add (c1 c2 : NumDenSameDeg 𝒜 x) :
    ((c1 + c2).num : A) = c1.den * c2.num + c2.den * c1.num :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_add HomogeneousLocalization.NumDenSameDeg.num_add

@[simp]
theorem den_add (c1 c2 : NumDenSameDeg 𝒜 x) : ((c1 + c2).den : A) = c1.den * c2.den :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_add HomogeneousLocalization.NumDenSameDeg.den_add

instance : Neg (NumDenSameDeg 𝒜 x) where
  neg c := ⟨c.deg, ⟨-c.num, neg_mem c.num.2⟩, c.den, c.den_mem⟩

@[simp]
theorem deg_neg (c : NumDenSameDeg 𝒜 x) : (-c).deg = c.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_neg HomogeneousLocalization.NumDenSameDeg.deg_neg

@[simp]
theorem num_neg (c : NumDenSameDeg 𝒜 x) : ((-c).num : A) = -c.num :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_neg HomogeneousLocalization.NumDenSameDeg.num_neg

@[simp]
theorem den_neg (c : NumDenSameDeg 𝒜 x) : ((-c).den : A) = c.den :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_neg HomogeneousLocalization.NumDenSameDeg.den_neg

instance : CommMonoid (NumDenSameDeg 𝒜 x) where
  one := 1
  mul := (· * ·)
  mul_assoc c1 c2 c3 := ext _ (add_assoc _ _ _) (mul_assoc _ _ _) (mul_assoc _ _ _)
  one_mul c := ext _ (zero_add _) (one_mul _) (one_mul _)
  mul_one c := ext _ (add_zero _) (mul_one _) (mul_one _)
  mul_comm c1 c2 := ext _ (add_comm _ _) (mul_comm _ _) (mul_comm _ _)

instance : Pow (NumDenSameDeg 𝒜 x) ℕ where
  pow c n :=
    ⟨n • c.deg, @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.num,
      @GradedMonoid.GMonoid.gnpow _ (fun i => ↥(𝒜 i)) _ _ n _ c.den, by
        induction' n with n ih
        · simpa only [Nat.zero_eq, coe_gnpow, pow_zero] using Submonoid.one_mem _
        · simpa only [pow_succ, coe_gnpow] using x.mul_mem ih c.den_mem⟩

@[simp]
theorem deg_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : (c ^ n).deg = n • c.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_pow HomogeneousLocalization.NumDenSameDeg.deg_pow

@[simp]
theorem num_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : ((c ^ n).num : A) = (c.num : A) ^ n :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_pow HomogeneousLocalization.NumDenSameDeg.num_pow

@[simp]
theorem den_pow (c : NumDenSameDeg 𝒜 x) (n : ℕ) : ((c ^ n).den : A) = (c.den : A) ^ n :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_pow HomogeneousLocalization.NumDenSameDeg.den_pow

section SMul

variable {α : Type*} [SMul α R] [SMul α A] [IsScalarTower α R A]

instance : SMul α (NumDenSameDeg 𝒜 x) where
  smul m c := ⟨c.deg, m • c.num, c.den, c.den_mem⟩

@[simp]
theorem deg_smul (c : NumDenSameDeg 𝒜 x) (m : α) : (m • c).deg = c.deg :=
  rfl
#align homogeneous_localization.num_denom_same_deg.deg_smul HomogeneousLocalization.NumDenSameDeg.deg_smul

@[simp]
theorem num_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).num : A) = m • c.num :=
  rfl
#align homogeneous_localization.num_denom_same_deg.num_smul HomogeneousLocalization.NumDenSameDeg.num_smul

@[simp]
theorem den_smul (c : NumDenSameDeg 𝒜 x) (m : α) : ((m • c).den : A) = c.den :=
  rfl
#align homogeneous_localization.num_denom_same_deg.denom_smul HomogeneousLocalization.NumDenSameDeg.den_smul

end SMul

variable (𝒜)

/-- For `x : prime ideal of A` and any `p : NumDenSameDeg 𝒜 x`, or equivalent a numerator and a
denominator of the same degree, we get an element `p.num / p.den` of `Aₓ`.
-/
def embedding (p : NumDenSameDeg 𝒜 x) : at x :=
  Localization.mk p.num ⟨p.den, p.den_mem⟩
#align homogeneous_localization.num_denom_same_deg.embedding HomogeneousLocalization.NumDenSameDeg.embedding

end NumDenSameDeg

end HomogeneousLocalization

/-- For `x : prime ideal of A`, `HomogeneousLocalization 𝒜 x` is `NumDenSameDeg 𝒜 x` modulo the
kernel of `embedding 𝒜 x`. This is essentially the subring of `Aₓ` where the numerator and
denominator share the same grading.
-/
-- Porting note(#5171): this linter isn't ported yet.
-- @[nolint has_nonempty_instance]
def HomogeneousLocalization : Type _ :=
  Quotient (Setoid.ker <| HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 x)
#align homogeneous_localization HomogeneousLocalization

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

variable {𝒜} {x}

/-- Construct an element of `HomogeneousLocalization 𝒜 x` from a homogeneous fraction. -/
abbrev mk (y : HomogeneousLocalization.NumDenSameDeg 𝒜 x) : HomogeneousLocalization 𝒜 x :=
  Quotient.mk'' y

lemma mk_surjective : Function.Surjective (mk (𝒜 := 𝒜) (x := x)) :=
  Quotient.surjective_Quotient_mk''

/-- View an element of `HomogeneousLocalization 𝒜 x` as an element of `Aₓ` by forgetting that the
numerator and denominator are of the same grading.
-/
def val (y : HomogeneousLocalization 𝒜 x) : at x :=
  Quotient.liftOn' y (NumDenSameDeg.embedding 𝒜 x) fun _ _ => id
#align homogeneous_localization.val HomogeneousLocalization.val

@[simp]
theorem val_mk (i : NumDenSameDeg 𝒜 x) :
    val (mk i) = Localization.mk (i.num : A) ⟨i.den, i.den_mem⟩ :=
  rfl
#align homogeneous_localization.val_mk' HomogeneousLocalization.val_mk

variable (x)

@[ext]
theorem val_injective : Function.Injective (HomogeneousLocalization.val (𝒜 := 𝒜) (x := x)) :=
  fun a b => Quotient.recOnSubsingleton₂' a b fun _ _ h => Quotient.sound' h
#align homogeneous_localization.val_injective HomogeneousLocalization.val_injective

variable (𝒜) {x} in
lemma subsingleton (hx : 0 ∈ x) : Subsingleton (HomogeneousLocalization 𝒜 x) :=
  have := IsLocalization.subsingleton (S := at x) hx
  (HomogeneousLocalization.val_injective (𝒜 := 𝒜) (x := x)).subsingleton

instance hasPow : Pow (HomogeneousLocalization 𝒜 x) ℕ where
  pow z n :=
    (Quotient.map' (· ^ n) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
          change Localization.mk _ _ = Localization.mk _ _
          simp only [num_pow, den_pow]
          convert congr_arg (fun z : at x => z ^ n) h <;> erw [Localization.mk_pow] <;> rfl :
        HomogeneousLocalization 𝒜 x → HomogeneousLocalization 𝒜 x)
      z
#align homogeneous_localization.has_pow HomogeneousLocalization.hasPow

@[simp] lemma mk_pow (i : NumDenSameDeg 𝒜 x) (n : ℕ) : mk (i ^ n) = mk i ^ n := rfl

section SMul

variable {α : Type*} [SMul α R] [SMul α A] [IsScalarTower α R A]
variable [IsScalarTower α A A]

instance : SMul α (HomogeneousLocalization 𝒜 x) where
  smul m := Quotient.map' (m • ·) fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    simp only [num_smul, den_smul]
    convert congr_arg (fun z : at x => m • z) h <;> rw [Localization.smul_mk]

@[simp] lemma mk_smul (i : NumDenSameDeg 𝒜 x) (m : α) : mk (m • i) = m • mk i := rfl

@[simp]
theorem val_smul (n : α) : ∀ y : HomogeneousLocalization 𝒜 x, (n • y).val = n • y.val :=
  Quotient.ind' fun _ ↦ by rw [← mk_smul, val_mk, val_mk, Localization.smul_mk]; rfl
#align homogeneous_localization.smul_val HomogeneousLocalization.val_smul

end SMul

instance : Neg (HomogeneousLocalization 𝒜 x) where
  neg := Quotient.map' Neg.neg fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) => by
    change Localization.mk _ _ = Localization.mk _ _
    simp only [num_neg, den_neg, ← Localization.neg_mk]
    exact congr_arg Neg.neg h

@[simp] lemma mk_neg (i : NumDenSameDeg 𝒜 x) : mk (-i) = -mk i := rfl

instance : Add (HomogeneousLocalization 𝒜 x) where
  add :=
    Quotient.map₂' (· + ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_add, den_add, ← Localization.add_mk]
      convert congr_arg₂ (· + ·) h h' <;> erw [Localization.add_mk] <;> rfl

@[simp] lemma mk_add (i j : NumDenSameDeg 𝒜 x) : mk (i + j) = mk i + mk j := rfl

instance : Sub (HomogeneousLocalization 𝒜 x) where sub z1 z2 := z1 + -z2

instance : Mul (HomogeneousLocalization 𝒜 x) where
  mul :=
    Quotient.map₂' (· * ·)
      fun c1 c2 (h : Localization.mk _ _ = Localization.mk _ _) c3 c4
        (h' : Localization.mk _ _ = Localization.mk _ _) => by
      change Localization.mk _ _ = Localization.mk _ _
      simp only [num_mul, den_mul]
      convert congr_arg₂ (· * ·) h h' <;> erw [Localization.mk_mul] <;> rfl

@[simp] lemma mk_mul (i j : NumDenSameDeg 𝒜 x) : mk (i * j) = mk i * mk j := rfl

instance : One (HomogeneousLocalization 𝒜 x) where one := Quotient.mk'' 1

@[simp] lemma mk_one : mk (1 : NumDenSameDeg 𝒜 x) = 1 := rfl

instance : Zero (HomogeneousLocalization 𝒜 x) where zero := Quotient.mk'' 0

@[simp] lemma mk_zero : mk (0 : NumDenSameDeg 𝒜 x) = 0 := rfl

theorem zero_eq : (0 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 0 :=
  rfl
#align homogeneous_localization.zero_eq HomogeneousLocalization.zero_eq

theorem one_eq : (1 : HomogeneousLocalization 𝒜 x) = Quotient.mk'' 1 :=
  rfl
#align homogeneous_localization.one_eq HomogeneousLocalization.one_eq

variable {x}

@[simp]
theorem val_zero : (0 : HomogeneousLocalization 𝒜 x).val = 0 :=
  Localization.mk_zero _
#align homogeneous_localization.zero_val HomogeneousLocalization.val_zero

@[simp]
theorem val_one : (1 : HomogeneousLocalization 𝒜 x).val = 1 :=
  Localization.mk_one
#align homogeneous_localization.one_val HomogeneousLocalization.val_one

@[simp]
theorem val_add : ∀ y1 y2 : HomogeneousLocalization 𝒜 x, (y1 + y2).val = y1.val + y2.val :=
  Quotient.ind₂' fun y1 y2 ↦ by rw [← mk_add, val_mk, val_mk, val_mk, Localization.add_mk]; rfl
#align homogeneous_localization.add_val HomogeneousLocalization.val_add

@[simp]
theorem val_mul : ∀ y1 y2 : HomogeneousLocalization 𝒜 x, (y1 * y2).val = y1.val * y2.val :=
  Quotient.ind₂' fun y1 y2 ↦ by rw [← mk_mul, val_mk, val_mk, val_mk, Localization.mk_mul]; rfl
#align homogeneous_localization.mul_val HomogeneousLocalization.val_mul

@[simp]
theorem val_neg : ∀ y : HomogeneousLocalization 𝒜 x, (-y).val = -y.val :=
  Quotient.ind' fun y ↦ by rw [← mk_neg, val_mk, val_mk, Localization.neg_mk]; rfl
#align homogeneous_localization.neg_val HomogeneousLocalization.val_neg

@[simp]
theorem val_sub (y1 y2 : HomogeneousLocalization 𝒜 x) : (y1 - y2).val = y1.val - y2.val := by
  rw [sub_eq_add_neg, ← val_neg, ← val_add]; rfl
#align homogeneous_localization.sub_val HomogeneousLocalization.val_sub

@[simp]
theorem val_pow : ∀ (y : HomogeneousLocalization 𝒜 x) (n : ℕ), (y ^ n).val = y.val ^ n :=
  Quotient.ind' fun y n ↦ by rw [← mk_pow, val_mk, val_mk, Localization.mk_pow]; rfl
#align homogeneous_localization.pow_val HomogeneousLocalization.val_pow

instance : NatCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Nat.unaryCast⟩

instance : IntCast (HomogeneousLocalization 𝒜 x) :=
  ⟨Int.castDef⟩

@[simp]
theorem val_natCast (n : ℕ) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Nat.unaryCast n) = _ by induction n <;> simp [Nat.unaryCast, *]
#align homogeneous_localization.nat_cast_val HomogeneousLocalization.val_natCast

@[simp]
theorem val_intCast (n : ℤ) : (n : HomogeneousLocalization 𝒜 x).val = n :=
  show val (Int.castDef n) = _ by cases n <;> simp [Int.castDef, *]
#align homogeneous_localization.int_cast_val HomogeneousLocalization.val_intCast

instance homogenousLocalizationCommRing : CommRing (HomogeneousLocalization 𝒜 x) :=
  (HomogeneousLocalization.val_injective x).commRing _ val_zero val_one val_add val_mul val_neg
    val_sub (val_smul x · ·) (val_smul x · ·) val_pow val_natCast val_intCast
#align homogeneous_localization.homogenous_localization_comm_ring HomogeneousLocalization.homogenousLocalizationCommRing

instance homogeneousLocalizationAlgebra :
    Algebra (HomogeneousLocalization 𝒜 x) (Localization x) where
  smul p q := p.val * q
  toFun := val
  map_one' := val_one
  map_mul' := val_mul
  map_zero' := val_zero
  map_add' := val_add
  commutes' _ _ := mul_comm _ _
  smul_def' _ _ := rfl
#align homogeneous_localization.homogeneous_localization_algebra HomogeneousLocalization.homogeneousLocalizationAlgebra

@[simp] lemma algebraMap_apply (y) :
    algebraMap (HomogeneousLocalization 𝒜 x) (Localization x) y = y.val := rfl

lemma mk_eq_zero_of_num (f : NumDenSameDeg 𝒜 x) (h : f.num = 0) : mk f = 0 := by
  apply val_injective
  simp only [val_mk, val_zero, h, ZeroMemClass.coe_zero, Localization.mk_zero]

lemma mk_eq_zero_of_den (f : NumDenSameDeg 𝒜 x) (h : f.den = 0) : mk f = 0 := by
  have := subsingleton 𝒜 (h ▸ f.den_mem)
  exact Subsingleton.elim _ _

end HomogeneousLocalization

namespace HomogeneousLocalization

open HomogeneousLocalization HomogeneousLocalization.NumDenSameDeg

variable {𝒜} {x}

/-- Numerator of an element in `HomogeneousLocalization x`. -/
def num (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out' f).num
#align homogeneous_localization.num HomogeneousLocalization.num

/-- Denominator of an element in `HomogeneousLocalization x`. -/
def den (f : HomogeneousLocalization 𝒜 x) : A :=
  (Quotient.out' f).den
#align homogeneous_localization.denom HomogeneousLocalization.den

/-- For an element in `HomogeneousLocalization x`, degree is the natural number `i` such that
  `𝒜 i` contains both numerator and denominator. -/
def deg (f : HomogeneousLocalization 𝒜 x) : ι :=
  (Quotient.out' f).deg
#align homogeneous_localization.deg HomogeneousLocalization.deg

theorem den_mem (f : HomogeneousLocalization 𝒜 x) : f.den ∈ x :=
  (Quotient.out' f).den_mem
#align homogeneous_localization.denom_mem HomogeneousLocalization.den_mem

theorem num_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.num ∈ 𝒜 f.deg :=
  (Quotient.out' f).num.2
#align homogeneous_localization.num_mem_deg HomogeneousLocalization.num_mem_deg

theorem den_mem_deg (f : HomogeneousLocalization 𝒜 x) : f.den ∈ 𝒜 f.deg :=
  (Quotient.out' f).den.2
#align homogeneous_localization.denom_mem_deg HomogeneousLocalization.den_mem_deg

theorem eq_num_div_den (f : HomogeneousLocalization 𝒜 x) :
    f.val = Localization.mk f.num ⟨f.den, f.den_mem⟩ :=
  congr_arg HomogeneousLocalization.val (Quotient.out_eq' f).symm
#align homogeneous_localization.eq_num_div_denom HomogeneousLocalization.eq_num_div_den

theorem den_smul_val (f : HomogeneousLocalization 𝒜 x) :
    f.den • f.val = algebraMap _ _ f.num := by
  rw [eq_num_div_den, Localization.mk_eq_mk', IsLocalization.smul_mk']
  exact IsLocalization.mk'_mul_cancel_left _ ⟨_, _⟩

theorem ext_iff_val (f g : HomogeneousLocalization 𝒜 x) : f = g ↔ f.val = g.val :=
  ⟨congr_arg val, fun e ↦ val_injective x e⟩
#align homogeneous_localization.ext_iff_val HomogeneousLocalization.ext_iff_val

section

variable (𝒜) (𝔭 : Ideal A) [Ideal.IsPrime 𝔭]

/-- Localizing a ring homogeneously at a prime ideal. -/
abbrev AtPrime :=
  HomogeneousLocalization 𝒜 𝔭.primeCompl
#align homogeneous_localization.at_prime HomogeneousLocalization.AtPrime

theorem isUnit_iff_isUnit_val (f : HomogeneousLocalization.AtPrime 𝒜 𝔭) :
    IsUnit f.val ↔ IsUnit f := by
  refine ⟨fun h1 ↦ ?_, IsUnit.map (algebraMap _ _)⟩
  rcases h1 with ⟨⟨a, b, eq0, eq1⟩, rfl : a = f.val⟩
  obtain ⟨f, rfl⟩ := mk_surjective f
  obtain ⟨b, s, rfl⟩ := IsLocalization.mk'_surjective 𝔭.primeCompl b
  rw [val_mk, Localization.mk_eq_mk', ← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq_mul,
    one_mul, IsLocalization.eq_iff_exists (M := 𝔭.primeCompl)] at eq0
  obtain ⟨c, hc : _ = c.1 * (f.den.1 * s.1)⟩ := eq0
  have : f.num.1 ∉ 𝔭 := by
    exact fun h ↦ mul_mem c.2 (mul_mem f.den_mem s.2)
      (hc ▸ Ideal.mul_mem_left _ c.1 (Ideal.mul_mem_right b _ h))
  refine isUnit_of_mul_eq_one _ (Quotient.mk'' ⟨f.1, f.3, f.2, this⟩) ?_
  rw [← mk_mul, ext_iff_val, val_mk]
  simp [mul_comm f.den.1]
#align homogeneous_localization.is_unit_iff_is_unit_val HomogeneousLocalization.isUnit_iff_isUnit_val

instance : Nontrivial (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  ⟨⟨0, 1, fun r => by simp [ext_iff_val, val_zero, val_one, zero_ne_one] at r⟩⟩

instance localRing : LocalRing (HomogeneousLocalization.AtPrime 𝒜 𝔭) :=
  LocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
    simpa only [← isUnit_iff_isUnit_val, val_sub, val_one]
      using LocalRing.isUnit_or_isUnit_one_sub_self _

end

section

variable (𝒜) (f : A)

/-- Localizing away from powers of `f` homogeneously. -/
abbrev Away :=
  HomogeneousLocalization 𝒜 (Submonoid.powers f)
#align homogeneous_localization.away HomogeneousLocalization.Away

variable {𝒜} {f}

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
    Algebra.smul_def, ← _root_.map_mul]
  rw [← smul_eq_mul, add_smul,
    DirectSum.degree_eq_of_mem_mem 𝒜 (SetLike.pow_mem_graded _ hf) (hk.symm ▸ z.den_mem_deg) hfk]
  exact ⟨_, SetLike.mul_mem_graded (SetLike.pow_mem_graded _ hf) z.num_mem_deg, rfl⟩

end

section

variable (𝒜)
variable {B : Type*} [CommRing B] [Algebra R B]
variable (ℬ : ι → Submodule R B) [GradedAlgebra ℬ]
variable {P : Submonoid A} {Q : Submonoid B}

/--
Let `A, B` be two graded algebras with the same indexing set and `g : A → B` be a graded algebra
homomorphism (i.e. `g(Aₘ) ⊆ Bₘ`). Let `P ≤ A` be a submonoid and `Q ≤ B` be a submonoid such that
`P ≤ g⁻¹ Q`, then `g` induce a map from the homogeneous localizations `A⁰_P` to the homogeneous
localizations `B⁰_Q`.
-/
def map (g : A →+* B)
    (comap_le : P ≤ Q.comap g) (hg : ∀ i, ∀ a ∈ 𝒜 i, g a ∈ ℬ i) :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization ℬ Q where
  toFun := Quotient.map'
    (fun x ↦ ⟨x.1, ⟨_, hg _ _ x.2.2⟩, ⟨_, hg _ _ x.3.2⟩, comap_le x.4⟩)
    fun x y (e : x.embedding = y.embedding) ↦ by
      apply_fun IsLocalization.map (Localization Q) g comap_le at e
      simp_rw [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
        IsLocalization.map_mk', ← Localization.mk_eq_mk'] at e
      exact e
  map_add' := Quotient.ind₂' fun x y ↦ by
    simp only [← mk_add, Quotient.map'_mk'', num_add, map_add, map_mul, den_add]; rfl
  map_mul' := Quotient.ind₂' fun x y ↦ by
    simp only [← mk_mul, Quotient.map'_mk'', num_mul, map_mul, den_mul]; rfl
  map_zero' := by simp only [← mk_zero (𝒜 := 𝒜), Quotient.map'_mk'', deg_zero,
    num_zero, ZeroMemClass.coe_zero, map_zero, den_zero, map_one]; rfl
  map_one' := by simp only [← mk_one (𝒜 := 𝒜), Quotient.map'_mk'', deg_zero,
    num_one, ZeroMemClass.coe_zero, map_zero, den_one, map_one]; rfl

/--
Let `A` be a graded algebra and `P ≤ Q` be two submonoids, then the homogeneous localization of `A`
at `P` embedds into the homogeneous localization of `A` at `Q`.
-/
abbrev mapId {P Q : Submonoid A} (h : P ≤ Q) :
    HomogeneousLocalization 𝒜 P →+* HomogeneousLocalization 𝒜 Q :=
  map 𝒜 𝒜 (RingHom.id _) h (fun _ _ ↦ id)

lemma map_mk (g : A →+* B)
    (comap_le : P ≤ Q.comap g) (hg : ∀ i, ∀ a ∈ 𝒜 i, g a ∈ ℬ i) (x) :
    map 𝒜 ℬ g comap_le hg (mk x) =
    mk ⟨x.1, ⟨_, hg _ _ x.2.2⟩, ⟨_, hg _ _ x.3.2⟩, comap_le x.4⟩ :=
  rfl

end

end HomogeneousLocalization
