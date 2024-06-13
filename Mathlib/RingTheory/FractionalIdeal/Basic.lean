/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.Localization.Integer
import Mathlib.RingTheory.Localization.Submodule

#align_import ring_theory.fractional_ideal from "leanprover-community/mathlib"@"ed90a7d327c3a5caf65a6faf7e8a0d63c4605df7"

/-!
# Fractional ideals

This file defines fractional ideals of an integral domain and proves basic facts about them.

## Main definitions
Let `S` be a submonoid of an integral domain `R` and `P` the localization of `R` at `S`.
 * `IsFractional` defines which `R`-submodules of `P` are fractional ideals
 * `FractionalIdeal S P` is the type of fractional ideals in `P`
 * a coercion `coeIdeal : Ideal R → FractionalIdeal S P`
 * `CommSemiring (FractionalIdeal S P)` instance:
   the typical ideal operations generalized to fractional ideals
 * `Lattice (FractionalIdeal S P)` instance

## Main statements

  * `mul_left_mono` and `mul_right_mono` state that ideal multiplication is monotone
  * `mul_div_self_cancel_iff` states that `1 / I` is the inverse of `I` if one exists

## Implementation notes

Fractional ideals are considered equal when they contain the same elements,
independent of the denominator `a : R` such that `a I ⊆ R`.
Thus, we define `FractionalIdeal` to be the subtype of the predicate `IsFractional`,
instead of having `FractionalIdeal` be a structure of which `a` is a field.

Most definitions in this file specialize operations from submodules to fractional ideals,
proving that the result of this operation is fractional if the input is fractional.
Exceptions to this rule are defining `(+) := (⊔)` and `⊥ := 0`,
in order to re-use their respective proof terms.
We can still use `simp` to show `↑I + ↑J = ↑(I + J)` and `↑⊥ = ↑0`.

Many results in fact do not need that `P` is a localization, only that `P` is an
`R`-algebra. We omit the `IsLocalization` parameter whenever this is practical.
Similarly, we don't assume that the localization is a field until we need it to
define ideal quotients. When this assumption is needed, we replace `S` with `R⁰`,
making the localization a field.

## References

  * https://en.wikipedia.org/wiki/Fractional_ideal

## Tags

fractional ideal, fractional ideals, invertible ideal
-/


open IsLocalization Pointwise nonZeroDivisors

section Defs

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]
variable [Algebra R P]
variable (S)

/-- A submodule `I` is a fractional ideal if `a I ⊆ R` for some `a ≠ 0`. -/
def IsFractional (I : Submodule R P) :=
  ∃ a ∈ S, ∀ b ∈ I, IsInteger R (a • b)
#align is_fractional IsFractional

variable (P)

/-- The fractional ideals of a domain `R` are ideals of `R` divided by some `a ∈ R`.

More precisely, let `P` be a localization of `R` at some submonoid `S`,
then a fractional ideal `I ⊆ P` is an `R`-submodule of `P`,
such that there is a nonzero `a : R` with `a I ⊆ R`.
-/
def FractionalIdeal :=
  { I : Submodule R P // IsFractional S I }
#align fractional_ideal FractionalIdeal

end Defs

namespace FractionalIdeal

open Set Submodule

variable {R : Type*} [CommRing R] {S : Submonoid R} {P : Type*} [CommRing P]
variable [Algebra R P] [loc : IsLocalization S P]

/-- Map a fractional ideal `I` to a submodule by forgetting that `∃ a, a I ⊆ R`.

This implements the coercion `FractionalIdeal S P → Submodule R P`.
-/
@[coe]
def coeToSubmodule (I : FractionalIdeal S P) : Submodule R P :=
  I.val

/-- Map a fractional ideal `I` to a submodule by forgetting that `∃ a, a I ⊆ R`.

This coercion is typically called `coeToSubmodule` in lemma names
(or `coe` when the coercion is clear from the context),
not to be confused with `IsLocalization.coeSubmodule : Ideal R → Submodule R P`
(which we use to define `coe : Ideal R → FractionalIdeal S P`).
-/
instance : CoeOut (FractionalIdeal S P) (Submodule R P) :=
  ⟨coeToSubmodule⟩

protected theorem isFractional (I : FractionalIdeal S P) : IsFractional S (I : Submodule R P) :=
  I.prop
#align fractional_ideal.is_fractional FractionalIdeal.isFractional

/-- An element of `S` such that `I.den • I = I.num`, see `FractionalIdeal.num` and
`FractionalIdeal.den_mul_self_eq_num`. -/
noncomputable def den (I : FractionalIdeal S P) : S :=
  ⟨I.2.choose, I.2.choose_spec.1⟩

/-- An ideal of `R` such that `I.den • I = I.num`, see `FractionalIdeal.den` and
`FractionalIdeal.den_mul_self_eq_num`. -/
noncomputable def num (I : FractionalIdeal S P) : Ideal R :=
  (I.den • (I : Submodule R P)).comap (Algebra.linearMap R P)

theorem den_mul_self_eq_num (I : FractionalIdeal S P) :
    I.den • (I : Submodule R P) = Submodule.map (Algebra.linearMap R P) I.num := by
  rw [den, num, Submodule.map_comap_eq]
  refine (inf_of_le_right ?_).symm
  rintro _ ⟨a, ha, rfl⟩
  exact I.2.choose_spec.2 a ha

/-- The linear equivalence between the fractional ideal `I` and the integral ideal `I.num`
defined by mapping `x` to `den I • x`. -/
noncomputable def equivNum [Nontrivial P] [NoZeroSMulDivisors R P]
    {I : FractionalIdeal S P} (h_nz : (I.den : R) ≠ 0) : I ≃ₗ[R] I.num := by
  refine LinearEquiv.trans
    (LinearEquiv.ofBijective ((DistribMulAction.toLinearMap R P I.den).restrict fun _ hx ↦ ?_)
      ⟨fun _ _ hxy ↦ ?_, fun ⟨y, hy⟩ ↦ ?_⟩)
    (Submodule.equivMapOfInjective (Algebra.linearMap R P)
      (NoZeroSMulDivisors.algebraMap_injective R P) (num I)).symm
  · rw [← den_mul_self_eq_num]
    exact Submodule.smul_mem_pointwise_smul _ _ _ hx
  · simp_rw [LinearMap.restrict_apply, DistribMulAction.toLinearMap_apply, Subtype.mk.injEq] at hxy
    rwa [Submonoid.smul_def, Submonoid.smul_def, smul_right_inj h_nz, SetCoe.ext_iff] at hxy
  · rw [← den_mul_self_eq_num] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    exact ⟨⟨x, hx⟩, by simp_rw [LinearMap.restrict_apply, Subtype.ext_iff, ← hxy]; rfl⟩

section SetLike

instance : SetLike (FractionalIdeal S P) P where
  coe I := ↑(I : Submodule R P)
  coe_injective' := SetLike.coe_injective.comp Subtype.coe_injective

@[simp]
theorem mem_coe {I : FractionalIdeal S P} {x : P} : x ∈ (I : Submodule R P) ↔ x ∈ I :=
  Iff.rfl
#align fractional_ideal.mem_coe FractionalIdeal.mem_coe

@[ext]
theorem ext {I J : FractionalIdeal S P} : (∀ x, x ∈ I ↔ x ∈ J) → I = J :=
  SetLike.ext
#align fractional_ideal.ext FractionalIdeal.ext

@[simp]
 theorem equivNum_apply [Nontrivial P] [NoZeroSMulDivisors R P] {I : FractionalIdeal S P}
    (h_nz : (I.den : R) ≠ 0) (x : I) :
    algebraMap R P (equivNum h_nz x) = I.den • x := by
  change Algebra.linearMap R P _ = _
  rw [equivNum, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply, LinearMap.restrict_apply,
    Submodule.map_equivMapOfInjective_symm_apply, Subtype.coe_mk,
    DistribMulAction.toLinearMap_apply]

/-- Copy of a `FractionalIdeal` with a new underlying set equal to the old one.
Useful to fix definitional equalities. -/
protected def copy (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : FractionalIdeal S P :=
  ⟨Submodule.copy p s hs, by
    convert p.isFractional
    ext
    simp only [hs]
    rfl⟩
#align fractional_ideal.copy FractionalIdeal.copy

@[simp]
theorem coe_copy (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : ↑(p.copy s hs) = s :=
  rfl
#align fractional_ideal.coe_copy FractionalIdeal.coe_copy

theorem coe_eq (p : FractionalIdeal S P) (s : Set P) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs
#align fractional_ideal.coe_eq FractionalIdeal.coe_eq

end SetLike

-- Porting note: this seems to be needed a lot more than in Lean 3
@[simp]
theorem val_eq_coe (I : FractionalIdeal S P) : I.val = I :=
  rfl
#align fractional_ideal.val_eq_coe FractionalIdeal.val_eq_coe

-- Porting note: had to rephrase this to make it clear to `simp` what was going on.
@[simp, norm_cast]
theorem coe_mk (I : Submodule R P) (hI : IsFractional S I) :
    coeToSubmodule ⟨I, hI⟩ = I :=
  rfl
#align fractional_ideal.coe_mk FractionalIdeal.coe_mk

theorem coeToSet_coeToSubmodule (I : FractionalIdeal S P) :
    ((I : Submodule R P) : Set P) = I :=
  rfl

/-! Transfer instances from `Submodule R P` to `FractionalIdeal S P`. -/

instance (I : FractionalIdeal S P) : Module R I :=
  Submodule.module (I : Submodule R P)

theorem coeToSubmodule_injective :
    Function.Injective (fun (I : FractionalIdeal S P) ↦ (I : Submodule R P)) :=
  Subtype.coe_injective
#align fractional_ideal.coe_to_submodule_injective FractionalIdeal.coeToSubmodule_injective

theorem coeToSubmodule_inj {I J : FractionalIdeal S P} : (I : Submodule R P) = J ↔ I = J :=
  coeToSubmodule_injective.eq_iff
#align fractional_ideal.coe_to_submodule_inj FractionalIdeal.coeToSubmodule_inj

theorem isFractional_of_le_one (I : Submodule R P) (h : I ≤ 1) : IsFractional S I := by
  use 1, S.one_mem
  intro b hb
  rw [one_smul]
  obtain ⟨b', b'_mem, rfl⟩ := h hb
  exact Set.mem_range_self b'
#align fractional_ideal.is_fractional_of_le_one FractionalIdeal.isFractional_of_le_one

theorem isFractional_of_le {I : Submodule R P} {J : FractionalIdeal S P} (hIJ : I ≤ J) :
    IsFractional S I := by
  obtain ⟨a, a_mem, ha⟩ := J.isFractional
  use a, a_mem
  intro b b_mem
  exact ha b (hIJ b_mem)
#align fractional_ideal.is_fractional_of_le FractionalIdeal.isFractional_of_le

/-- Map an ideal `I` to a fractional ideal by forgetting `I` is integral.

This is the function that implements the coercion `Ideal R → FractionalIdeal S P`. -/
@[coe]
def coeIdeal (I : Ideal R) : FractionalIdeal S P :=
  ⟨coeSubmodule P I,
   isFractional_of_le_one _ <| by simpa using coeSubmodule_mono P (le_top : I ≤ ⊤)⟩

-- Is a `CoeTC` rather than `Coe` to speed up failing inference, see library note [use has_coe_t]
/-- Map an ideal `I` to a fractional ideal by forgetting `I` is integral.

This is a bundled version of `IsLocalization.coeSubmodule : Ideal R → Submodule R P`,
which is not to be confused with the `coe : FractionalIdeal S P → Submodule R P`,
also called `coeToSubmodule` in theorem names.

This map is available as a ring hom, called `FractionalIdeal.coeIdealHom`.
-/
instance : CoeTC (Ideal R) (FractionalIdeal S P) :=
  ⟨fun I => coeIdeal I⟩

@[simp, norm_cast]
theorem coe_coeIdeal (I : Ideal R) :
    ((I : FractionalIdeal S P) : Submodule R P) = coeSubmodule P I :=
  rfl
#align fractional_ideal.coe_coe_ideal FractionalIdeal.coe_coeIdeal

variable (S)

@[simp]
theorem mem_coeIdeal {x : P} {I : Ideal R} :
    x ∈ (I : FractionalIdeal S P) ↔ ∃ x', x' ∈ I ∧ algebraMap R P x' = x :=
  mem_coeSubmodule _ _
#align fractional_ideal.mem_coe_ideal FractionalIdeal.mem_coeIdeal

theorem mem_coeIdeal_of_mem {x : R} {I : Ideal R} (hx : x ∈ I) :
    algebraMap R P x ∈ (I : FractionalIdeal S P) :=
  (mem_coeIdeal S).mpr ⟨x, hx, rfl⟩
#align fractional_ideal.mem_coe_ideal_of_mem FractionalIdeal.mem_coeIdeal_of_mem

theorem coeIdeal_le_coeIdeal' [IsLocalization S P] (h : S ≤ nonZeroDivisors R) {I J : Ideal R} :
    (I : FractionalIdeal S P) ≤ J ↔ I ≤ J :=
  coeSubmodule_le_coeSubmodule h
#align fractional_ideal.coe_ideal_le_coe_ideal' FractionalIdeal.coeIdeal_le_coeIdeal'

@[simp]
theorem coeIdeal_le_coeIdeal (K : Type*) [CommRing K] [Algebra R K] [IsFractionRing R K]
    {I J : Ideal R} : (I : FractionalIdeal R⁰ K) ≤ J ↔ I ≤ J :=
  IsFractionRing.coeSubmodule_le_coeSubmodule
#align fractional_ideal.coe_ideal_le_coe_ideal FractionalIdeal.coeIdeal_le_coeIdeal

instance : Zero (FractionalIdeal S P) :=
  ⟨(0 : Ideal R)⟩

@[simp]
theorem mem_zero_iff {x : P} : x ∈ (0 : FractionalIdeal S P) ↔ x = 0 :=
  ⟨fun ⟨x', x'_mem_zero, x'_eq_x⟩ => by
    have x'_eq_zero : x' = 0 := x'_mem_zero
    simp [x'_eq_x.symm, x'_eq_zero], fun hx => ⟨0, rfl, by simp [hx]⟩⟩
#align fractional_ideal.mem_zero_iff FractionalIdeal.mem_zero_iff

variable {S}

@[simp, norm_cast]
theorem coe_zero : ↑(0 : FractionalIdeal S P) = (⊥ : Submodule R P) :=
  Submodule.ext fun _ => mem_zero_iff S
#align fractional_ideal.coe_zero FractionalIdeal.coe_zero

@[simp, norm_cast]
theorem coeIdeal_bot : ((⊥ : Ideal R) : FractionalIdeal S P) = 0 :=
  rfl
#align fractional_ideal.coe_ideal_bot FractionalIdeal.coeIdeal_bot

variable (P)

@[simp]
theorem exists_mem_algebraMap_eq {x : R} {I : Ideal R} (h : S ≤ nonZeroDivisors R) :
    (∃ x', x' ∈ I ∧ algebraMap R P x' = algebraMap R P x) ↔ x ∈ I :=
  ⟨fun ⟨_, hx', Eq⟩ => IsLocalization.injective _ h Eq ▸ hx', fun h => ⟨x, h, rfl⟩⟩
#align fractional_ideal.exists_mem_to_map_eq FractionalIdeal.exists_mem_algebraMap_eq

variable {P}

theorem coeIdeal_injective' (h : S ≤ nonZeroDivisors R) :
    Function.Injective (fun (I : Ideal R) ↦ (I : FractionalIdeal S P)) := fun _ _ h' =>
  ((coeIdeal_le_coeIdeal' S h).mp h'.le).antisymm ((coeIdeal_le_coeIdeal' S h).mp
    h'.ge)
#align fractional_ideal.coe_ideal_injective' FractionalIdeal.coeIdeal_injective'

theorem coeIdeal_inj' (h : S ≤ nonZeroDivisors R) {I J : Ideal R} :
    (I : FractionalIdeal S P) = J ↔ I = J :=
  (coeIdeal_injective' h).eq_iff
#align fractional_ideal.coe_ideal_inj' FractionalIdeal.coeIdeal_inj'

-- Porting note: doesn't need to be @[simp] because it can be proved by coeIdeal_eq_zero
theorem coeIdeal_eq_zero' {I : Ideal R} (h : S ≤ nonZeroDivisors R) :
    (I : FractionalIdeal S P) = 0 ↔ I = (⊥ : Ideal R) :=
  coeIdeal_inj' h
#align fractional_ideal.coe_ideal_eq_zero' FractionalIdeal.coeIdeal_eq_zero'

theorem coeIdeal_ne_zero' {I : Ideal R} (h : S ≤ nonZeroDivisors R) :
    (I : FractionalIdeal S P) ≠ 0 ↔ I ≠ (⊥ : Ideal R) :=
  not_iff_not.mpr <| coeIdeal_eq_zero' h
#align fractional_ideal.coe_ideal_ne_zero' FractionalIdeal.coeIdeal_ne_zero'

theorem coeToSubmodule_eq_bot {I : FractionalIdeal S P} : (I : Submodule R P) = ⊥ ↔ I = 0 :=
  ⟨fun h => coeToSubmodule_injective (by simp [h]), fun h => by simp [h]⟩
#align fractional_ideal.coe_to_submodule_eq_bot FractionalIdeal.coeToSubmodule_eq_bot

theorem coeToSubmodule_ne_bot {I : FractionalIdeal S P} : ↑I ≠ (⊥ : Submodule R P) ↔ I ≠ 0 :=
  not_iff_not.mpr coeToSubmodule_eq_bot
#align fractional_ideal.coe_to_submodule_ne_bot FractionalIdeal.coeToSubmodule_ne_bot

instance : Inhabited (FractionalIdeal S P) :=
  ⟨0⟩

instance : One (FractionalIdeal S P) :=
  ⟨(⊤ : Ideal R)⟩

theorem zero_of_num_eq_bot [NoZeroSMulDivisors R P] (hS : 0 ∉ S) {I : FractionalIdeal S P}
    (hI : I.num = ⊥) : I = 0 := by
  rw [← coeToSubmodule_eq_bot, eq_bot_iff]
  intro x hx
  suffices (den I : R) • x = 0 from
    (smul_eq_zero.mp this).resolve_left (ne_of_mem_of_not_mem (SetLike.coe_mem _) hS)
  have h_eq : I.den • (I : Submodule R P) = ⊥ := by rw [den_mul_self_eq_num, hI, Submodule.map_bot]
  exact (Submodule.eq_bot_iff _).mp h_eq (den I • x) ⟨x, hx, rfl⟩

theorem num_zero_eq (h_inj : Function.Injective (algebraMap R P)) :
    num (0 : FractionalIdeal S P) = 0 := by
  simpa [num, LinearMap.ker_eq_bot] using h_inj

variable (S)

@[simp, norm_cast]
theorem coeIdeal_top : ((⊤ : Ideal R) : FractionalIdeal S P) = 1 :=
  rfl
#align fractional_ideal.coe_ideal_top FractionalIdeal.coeIdeal_top

theorem mem_one_iff {x : P} : x ∈ (1 : FractionalIdeal S P) ↔ ∃ x' : R, algebraMap R P x' = x :=
  Iff.intro (fun ⟨x', _, h⟩ => ⟨x', h⟩) fun ⟨x', h⟩ => ⟨x', ⟨⟩, h⟩
#align fractional_ideal.mem_one_iff FractionalIdeal.mem_one_iff

theorem coe_mem_one (x : R) : algebraMap R P x ∈ (1 : FractionalIdeal S P) :=
  (mem_one_iff S).mpr ⟨x, rfl⟩
#align fractional_ideal.coe_mem_one FractionalIdeal.coe_mem_one

theorem one_mem_one : (1 : P) ∈ (1 : FractionalIdeal S P) :=
  (mem_one_iff S).mpr ⟨1, RingHom.map_one _⟩
#align fractional_ideal.one_mem_one FractionalIdeal.one_mem_one

variable {S}

/-- `(1 : FractionalIdeal S P)` is defined as the R-submodule `f(R) ≤ P`.

However, this is not definitionally equal to `1 : Submodule R P`,
which is proved in the actual `simp` lemma `coe_one`. -/
theorem coe_one_eq_coeSubmodule_top : ↑(1 : FractionalIdeal S P) = coeSubmodule P (⊤ : Ideal R) :=
  rfl
#align fractional_ideal.coe_one_eq_coe_submodule_top FractionalIdeal.coe_one_eq_coeSubmodule_top

@[simp, norm_cast]
theorem coe_one : (↑(1 : FractionalIdeal S P) : Submodule R P) = 1 := by
  rw [coe_one_eq_coeSubmodule_top, coeSubmodule_top]
#align fractional_ideal.coe_one FractionalIdeal.coe_one

section Lattice

/-!
### `Lattice` section

Defines the order on fractional ideals as inclusion of their underlying sets,
and ports the lattice structure on submodules to fractional ideals.
-/


@[simp]
theorem coe_le_coe {I J : FractionalIdeal S P} :
    (I : Submodule R P) ≤ (J : Submodule R P) ↔ I ≤ J :=
  Iff.rfl
#align fractional_ideal.coe_le_coe FractionalIdeal.coe_le_coe

theorem zero_le (I : FractionalIdeal S P) : 0 ≤ I := by
  intro x hx
  -- Porting note: changed the proof from convert; simp into rw; exact
  rw [(mem_zero_iff _).mp hx]
  exact zero_mem (I : Submodule R P)
#align fractional_ideal.zero_le FractionalIdeal.zero_le

instance orderBot : OrderBot (FractionalIdeal S P) where
  bot := 0
  bot_le := zero_le
#align fractional_ideal.order_bot FractionalIdeal.orderBot

@[simp]
theorem bot_eq_zero : (⊥ : FractionalIdeal S P) = 0 :=
  rfl
#align fractional_ideal.bot_eq_zero FractionalIdeal.bot_eq_zero

@[simp]
theorem le_zero_iff {I : FractionalIdeal S P} : I ≤ 0 ↔ I = 0 :=
  le_bot_iff
#align fractional_ideal.le_zero_iff FractionalIdeal.le_zero_iff

theorem eq_zero_iff {I : FractionalIdeal S P} : I = 0 ↔ ∀ x ∈ I, x = (0 : P) :=
  ⟨fun h x hx => by simpa [h, mem_zero_iff] using hx, fun h =>
    le_bot_iff.mp fun x hx => (mem_zero_iff S).mpr (h x hx)⟩
#align fractional_ideal.eq_zero_iff FractionalIdeal.eq_zero_iff

theorem _root_.IsFractional.sup {I J : Submodule R P} :
    IsFractional S I → IsFractional S J → IsFractional S (I ⊔ J)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩ =>
    ⟨aI * aJ, S.mul_mem haI haJ, fun b hb => by
      rcases mem_sup.mp hb with ⟨bI, hbI, bJ, hbJ, rfl⟩
      rw [smul_add]
      apply isInteger_add
      · rw [mul_smul, smul_comm]
        exact isInteger_smul (hI bI hbI)
      · rw [mul_smul]
        exact isInteger_smul (hJ bJ hbJ)⟩
#align is_fractional.sup IsFractional.sup

theorem _root_.IsFractional.inf_right {I : Submodule R P} :
    IsFractional S I → ∀ J, IsFractional S (I ⊓ J)
  | ⟨aI, haI, hI⟩, J =>
    ⟨aI, haI, fun b hb => by
      rcases mem_inf.mp hb with ⟨hbI, _⟩
      exact hI b hbI⟩
#align is_fractional.inf_right IsFractional.inf_right

instance : Inf (FractionalIdeal S P) :=
  ⟨fun I J => ⟨I ⊓ J, I.isFractional.inf_right J⟩⟩

@[simp, norm_cast]
theorem coe_inf (I J : FractionalIdeal S P) : ↑(I ⊓ J) = (I ⊓ J : Submodule R P) :=
  rfl
#align fractional_ideal.coe_inf FractionalIdeal.coe_inf

instance : Sup (FractionalIdeal S P) :=
  ⟨fun I J => ⟨I ⊔ J, I.isFractional.sup J.isFractional⟩⟩

@[norm_cast]
theorem coe_sup (I J : FractionalIdeal S P) : ↑(I ⊔ J) = (I ⊔ J : Submodule R P) :=
  rfl
#align fractional_ideal.coe_sup FractionalIdeal.coe_sup

instance lattice : Lattice (FractionalIdeal S P) :=
  Function.Injective.lattice _ Subtype.coe_injective coe_sup coe_inf
#align fractional_ideal.lattice FractionalIdeal.lattice

instance : SemilatticeSup (FractionalIdeal S P) :=
  { FractionalIdeal.lattice with }

end Lattice

section Semiring

instance : Add (FractionalIdeal S P) :=
  ⟨(· ⊔ ·)⟩

@[simp]
theorem sup_eq_add (I J : FractionalIdeal S P) : I ⊔ J = I + J :=
  rfl
#align fractional_ideal.sup_eq_add FractionalIdeal.sup_eq_add

@[simp, norm_cast]
theorem coe_add (I J : FractionalIdeal S P) : (↑(I + J) : Submodule R P) = I + J :=
  rfl
#align fractional_ideal.coe_add FractionalIdeal.coe_add

@[simp, norm_cast]
theorem coeIdeal_sup (I J : Ideal R) : ↑(I ⊔ J) = (I + J : FractionalIdeal S P) :=
  coeToSubmodule_injective <| coeSubmodule_sup _ _ _
#align fractional_ideal.coe_ideal_sup FractionalIdeal.coeIdeal_sup

theorem _root_.IsFractional.nsmul {I : Submodule R P} :
    ∀ n : ℕ, IsFractional S I → IsFractional S (n • I : Submodule R P)
  | 0, _ => by
    rw [zero_smul]
    convert ((0 : Ideal R) : FractionalIdeal S P).isFractional
    simp
  | n + 1, h => by
    rw [succ_nsmul]
    exact (IsFractional.nsmul n h).sup h
#align is_fractional.nsmul IsFractional.nsmul

instance : SMul ℕ (FractionalIdeal S P) where smul n I := ⟨n • ↑I, I.isFractional.nsmul n⟩

@[norm_cast]
theorem coe_nsmul (n : ℕ) (I : FractionalIdeal S P) :
    (↑(n • I) : Submodule R P) = n • (I : Submodule R P) :=
  rfl
#align fractional_ideal.coe_nsmul FractionalIdeal.coe_nsmul

theorem _root_.IsFractional.mul {I J : Submodule R P} :
    IsFractional S I → IsFractional S J → IsFractional S (I * J : Submodule R P)
  | ⟨aI, haI, hI⟩, ⟨aJ, haJ, hJ⟩ =>
    ⟨aI * aJ, S.mul_mem haI haJ, fun b hb => by
      refine Submodule.mul_induction_on hb ?_ ?_
      · intro m hm n hn
        obtain ⟨n', hn'⟩ := hJ n hn
        rw [mul_smul, mul_comm m, ← smul_mul_assoc, ← hn', ← Algebra.smul_def]
        apply hI
        exact Submodule.smul_mem _ _ hm
      · intro x y hx hy
        rw [smul_add]
        apply isInteger_add hx hy⟩
#align is_fractional.mul IsFractional.mul

theorem _root_.IsFractional.pow {I : Submodule R P} (h : IsFractional S I) :
    ∀ n : ℕ, IsFractional S (I ^ n : Submodule R P)
  | 0 => isFractional_of_le_one _ (pow_zero _).le
  | n + 1 => (pow_succ I n).symm ▸ (IsFractional.pow h n).mul h
#align is_fractional.pow IsFractional.pow

/-- `FractionalIdeal.mul` is the product of two fractional ideals,
used to define the `Mul` instance.

This is only an auxiliary definition: the preferred way of writing `I.mul J` is `I * J`.

Elaborated terms involving `FractionalIdeal` tend to grow quite large,
so by making definitions irreducible, we hope to avoid deep unfolds.
-/
irreducible_def mul (lemma := mul_def') (I J : FractionalIdeal S P) : FractionalIdeal S P :=
  ⟨I * J, I.isFractional.mul J.isFractional⟩
#align fractional_ideal.mul FractionalIdeal.mul

-- local attribute [semireducible] mul
instance : Mul (FractionalIdeal S P) :=
  ⟨fun I J => mul I J⟩

@[simp]
theorem mul_eq_mul (I J : FractionalIdeal S P) : mul I J = I * J :=
  rfl
#align fractional_ideal.mul_eq_mul FractionalIdeal.mul_eq_mul

theorem mul_def (I J : FractionalIdeal S P) :
    I * J = ⟨I * J, I.isFractional.mul J.isFractional⟩ := by simp only [← mul_eq_mul, mul]
#align fractional_ideal.mul_def FractionalIdeal.mul_def

@[simp, norm_cast]
theorem coe_mul (I J : FractionalIdeal S P) : (↑(I * J) : Submodule R P) = I * J := by
  simp only [mul_def, coe_mk]
#align fractional_ideal.coe_mul FractionalIdeal.coe_mul

@[simp, norm_cast]
theorem coeIdeal_mul (I J : Ideal R) : (↑(I * J) : FractionalIdeal S P) = I * J := by
  simp only [mul_def]
  exact coeToSubmodule_injective (coeSubmodule_mul _ _ _)
#align fractional_ideal.coe_ideal_mul FractionalIdeal.coeIdeal_mul

theorem mul_left_mono (I : FractionalIdeal S P) : Monotone (I * ·) := by
  intro J J' h
  simp only [mul_def]
  exact mul_le.mpr fun x hx y hy => mul_mem_mul hx (h hy)
#align fractional_ideal.mul_left_mono FractionalIdeal.mul_left_mono

theorem mul_right_mono (I : FractionalIdeal S P) : Monotone fun J => J * I := by
  intro J J' h
  simp only [mul_def]
  exact mul_le.mpr fun x hx y hy => mul_mem_mul (h hx) hy
#align fractional_ideal.mul_right_mono FractionalIdeal.mul_right_mono

theorem mul_mem_mul {I J : FractionalIdeal S P} {i j : P} (hi : i ∈ I) (hj : j ∈ J) :
    i * j ∈ I * J := by
  simp only [mul_def]
  exact Submodule.mul_mem_mul hi hj
#align fractional_ideal.mul_mem_mul FractionalIdeal.mul_mem_mul

theorem mul_le {I J K : FractionalIdeal S P} : I * J ≤ K ↔ ∀ i ∈ I, ∀ j ∈ J, i * j ∈ K := by
  simp only [mul_def]
  exact Submodule.mul_le
#align fractional_ideal.mul_le FractionalIdeal.mul_le

instance : Pow (FractionalIdeal S P) ℕ :=
  ⟨fun I n => ⟨(I : Submodule R P) ^ n, I.isFractional.pow n⟩⟩

@[simp, norm_cast]
theorem coe_pow (I : FractionalIdeal S P) (n : ℕ) : ↑(I ^ n) = (I : Submodule R P) ^ n :=
  rfl
#align fractional_ideal.coe_pow FractionalIdeal.coe_pow

@[elab_as_elim]
protected theorem mul_induction_on {I J : FractionalIdeal S P} {C : P → Prop} {r : P}
    (hr : r ∈ I * J) (hm : ∀ i ∈ I, ∀ j ∈ J, C (i * j)) (ha : ∀ x y, C x → C y → C (x + y)) :
    C r := by
  simp only [mul_def] at hr
  exact Submodule.mul_induction_on hr hm ha
#align fractional_ideal.mul_induction_on FractionalIdeal.mul_induction_on

instance : NatCast (FractionalIdeal S P) :=
  ⟨Nat.unaryCast⟩

theorem coe_natCast (n : ℕ) : ((n : FractionalIdeal S P) : Submodule R P) = n :=
  show ((n.unaryCast : FractionalIdeal S P) : Submodule R P) = n
  by induction n <;> simp [*, Nat.unaryCast]
#align fractional_ideal.coe_nat_cast FractionalIdeal.coe_natCast

@[deprecated (since := "2024-04-17")]
alias coe_nat_cast := coe_natCast

instance commSemiring : CommSemiring (FractionalIdeal S P) :=
  Function.Injective.commSemiring _ Subtype.coe_injective coe_zero coe_one coe_add coe_mul
    (fun _ _ => coe_nsmul _ _) coe_pow coe_natCast

end Semiring

variable (S P)

/-- `FractionalIdeal.coeToSubmodule` as a bundled `RingHom`. -/
@[simps]
def coeSubmoduleHom : FractionalIdeal S P →+* Submodule R P where
  toFun := coeToSubmodule
  map_one' := coe_one
  map_mul' := coe_mul
  map_zero' := coe_zero (S := S)
  map_add' := coe_add
#align fractional_ideal.coe_submodule_hom FractionalIdeal.coeSubmoduleHom

variable {S P}

section Order

theorem add_le_add_left {I J : FractionalIdeal S P} (hIJ : I ≤ J) (J' : FractionalIdeal S P) :
    J' + I ≤ J' + J :=
  sup_le_sup_left hIJ J'
#align fractional_ideal.add_le_add_left FractionalIdeal.add_le_add_left

theorem mul_le_mul_left {I J : FractionalIdeal S P} (hIJ : I ≤ J) (J' : FractionalIdeal S P) :
    J' * I ≤ J' * J :=
  mul_le.mpr fun _ hk _ hj => mul_mem_mul hk (hIJ hj)
#align fractional_ideal.mul_le_mul_left FractionalIdeal.mul_le_mul_left

theorem le_self_mul_self {I : FractionalIdeal S P} (hI : 1 ≤ I) : I ≤ I * I := by
  convert mul_left_mono I hI
  exact (mul_one I).symm
#align fractional_ideal.le_self_mul_self FractionalIdeal.le_self_mul_self

theorem mul_self_le_self {I : FractionalIdeal S P} (hI : I ≤ 1) : I * I ≤ I := by
  convert mul_left_mono I hI
  exact (mul_one I).symm
#align fractional_ideal.mul_self_le_self FractionalIdeal.mul_self_le_self

theorem coeIdeal_le_one {I : Ideal R} : (I : FractionalIdeal S P) ≤ 1 := fun _ hx =>
  let ⟨y, _, hy⟩ := (mem_coeIdeal S).mp hx
  (mem_one_iff S).mpr ⟨y, hy⟩
#align fractional_ideal.coe_ideal_le_one FractionalIdeal.coeIdeal_le_one

theorem le_one_iff_exists_coeIdeal {J : FractionalIdeal S P} :
    J ≤ (1 : FractionalIdeal S P) ↔ ∃ I : Ideal R, ↑I = J := by
  constructor
  · intro hJ
    refine ⟨⟨⟨⟨{ x : R | algebraMap R P x ∈ J }, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro a b ha hb
      rw [mem_setOf, RingHom.map_add]
      exact J.val.add_mem ha hb
    · rw [mem_setOf, RingHom.map_zero]
      exact J.val.zero_mem
    · intro c x hx
      rw [smul_eq_mul, mem_setOf, RingHom.map_mul, ← Algebra.smul_def]
      exact J.val.smul_mem c hx
    · ext x
      constructor
      · rintro ⟨y, hy, eq_y⟩
        rwa [← eq_y]
      · intro hx
        obtain ⟨y, rfl⟩ := (mem_one_iff S).mp (hJ hx)
        exact mem_setOf.mpr ⟨y, hx, rfl⟩
  · rintro ⟨I, hI⟩
    rw [← hI]
    apply coeIdeal_le_one
#align fractional_ideal.le_one_iff_exists_coe_ideal FractionalIdeal.le_one_iff_exists_coeIdeal

@[simp]
theorem one_le {I : FractionalIdeal S P} : 1 ≤ I ↔ (1 : P) ∈ I := by
  rw [← coe_le_coe, coe_one, Submodule.one_le, mem_coe]
#align fractional_ideal.one_le FractionalIdeal.one_le

variable (S P)

/-- `coeIdealHom (S : Submonoid R) P` is `(↑) : Ideal R → FractionalIdeal S P` as a ring hom -/
@[simps]
def coeIdealHom : Ideal R →+* FractionalIdeal S P where
  toFun := coeIdeal
  map_add' := coeIdeal_sup
  map_mul' := coeIdeal_mul
  map_one' := by rw [Ideal.one_eq_top, coeIdeal_top]
  map_zero' := coeIdeal_bot
#align fractional_ideal.coe_ideal_hom FractionalIdeal.coeIdealHom

theorem coeIdeal_pow (I : Ideal R) (n : ℕ) : ↑(I ^ n) = (I : FractionalIdeal S P) ^ n :=
  (coeIdealHom S P).map_pow _ n
#align fractional_ideal.coe_ideal_pow FractionalIdeal.coeIdeal_pow

theorem coeIdeal_finprod [IsLocalization S P] {α : Sort*} {f : α → Ideal R}
    (hS : S ≤ nonZeroDivisors R) :
    ((∏ᶠ a : α, f a : Ideal R) : FractionalIdeal S P) = ∏ᶠ a : α, (f a : FractionalIdeal S P) :=
  MonoidHom.map_finprod_of_injective (coeIdealHom S P).toMonoidHom (coeIdeal_injective' hS) f
#align fractional_ideal.coe_ideal_finprod FractionalIdeal.coeIdeal_finprod

end Order

end FractionalIdeal
