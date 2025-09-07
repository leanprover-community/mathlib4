/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang, Bichang Lei, María Inés de Frutos-Fernández, Filippo A. E. Nuccio
-/
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Extension of Valuations

In this file, we define the typeclass for valuation extensions and prove basic facts about the
extension of valuations. Let `A` be an `R` algebra, equipped with valuations `vA` and `vR`
respectively. Here, the extension of a valuation means that the pullback of valuation `vA` to `R`
is equivalent to the valuation `vR` on `R`. We only require equivalence, not equality, of
valuations here.

Note that we do not require the ring map from `R` to `A` to be injective. This holds automatically
when `R` is a division ring and `A` is nontrivial.

A motivation for choosing the more flexible `Valuation.Equiv` rather than strict equality here is
to allow for possible normalization. As an example, consider a finite extension `K` of `ℚ_[p]`,
which is a discretely valued field. We may choose the valuation on `K` to be either:

1. the valuation where the uniformizer is mapped to one (more precisely, `-1` in `ℤᵐ⁰`) or

2. the valuation where `p` is mapped to one.

For the algebraic closure of `ℚ_[p]`, if we choose the valuation of `p` to be one, then the
restriction of this valuation to `K` equals the second valuation, but is only equivalent to the
first valuation. The flexibility of equivalence here allows us to develop theory for both cases
without first determining the normalizations once and for all.

## Main Definition

* `Valuation.HasExtension vR vA` : The valuation `vA` on `A` is an extension of the valuation
  `vR` on `R`.

## References

* [Bourbaki, Nicolas. *Commutative algebra*] Chapter VI §3, Valuations.
* <https://en.wikipedia.org/wiki/Valuation_(algebra)#Extension_of_valuations>

## Tags
Valuation, Extension of Valuations

-/
namespace Valuation

variable {R A ΓR ΓA : Type*} [CommRing R] [Ring A]
    [LinearOrderedCommMonoidWithZero ΓR] [LinearOrderedCommMonoidWithZero ΓA] [Algebra R A]
    (vR : Valuation R ΓR) (vA : Valuation A ΓA)

/--
The class `Valuation.HasExtension vR vA` states that the valuation `vA` on `A` is an extension of
the valuation `vR` on `R`. More precisely, `vR` is equivalent to the comap of the valuation `vA`.
-/
class HasExtension : Prop where
  /-- The valuation `vR` on `R` is equivalent to the comap of the valuation `vA` on `A` -/
  val_isEquiv_comap : vR.IsEquiv <| vA.comap (algebraMap R A)

@[deprecated (since := "2025-04-02")] alias _root_.IsValExtension := HasExtension

namespace HasExtension

section algebraMap

variable [vR.HasExtension vA]

-- @[simp] does not work because `vR` cannot be inferred from `R`.
theorem val_map_le_iff (x y : R) : vA (algebraMap R A x) ≤ vA (algebraMap R A y) ↔ vR x ≤ vR y :=
  val_isEquiv_comap.symm x y

theorem val_map_lt_iff (x y : R) : vA (algebraMap R A x) < vA (algebraMap R A y) ↔ vR x < vR y := by
  simpa only [not_le] using ((val_map_le_iff vR vA _ _).not)

theorem val_map_eq_iff (x y : R) : vA (algebraMap R A x) = vA (algebraMap R A y) ↔ vR x = vR y :=
  (IsEquiv.val_eq val_isEquiv_comap).symm

theorem val_map_le_one_iff (x : R) : vA (algebraMap R A x) ≤ 1 ↔ vR x ≤ 1 := by
  simpa only [map_one] using val_map_le_iff vR vA x 1

theorem val_map_lt_one_iff (x : R) : vA (algebraMap R A x) < 1 ↔ vR x < 1 := by
  simpa only [map_one, not_le] using (val_map_le_iff vR vA 1 x).not

theorem val_map_eq_one_iff (x : R) : vA (algebraMap R A x) = 1 ↔ vR x = 1 := by
  simpa only [le_antisymm_iff, map_one] using
    and_congr (val_map_le_iff vR vA x 1) (val_map_le_iff vR vA 1 x)

end algebraMap

instance id : vR.HasExtension vR where
  val_isEquiv_comap := by
    simp only [Algebra.algebraMap_self, comap_id, IsEquiv.refl]

section integer

variable {K : Type*} [Field K] [Algebra K A] {ΓR ΓA ΓK : Type*}
    [LinearOrderedCommGroupWithZero ΓR] [LinearOrderedCommGroupWithZero ΓK]
    [LinearOrderedCommGroupWithZero ΓA] {vR : Valuation R ΓR} {vK : Valuation K ΓK}
    {vA : Valuation A ΓA} [vR.HasExtension vA]

/--
When `K` is a field, if the preimage of the valuation integers of `A` equals to the valuation
integers of `K`, then the valuation on `A` is an extension of the valuation on `K`.
-/
theorem ofComapInteger (h : vA.integer.comap (algebraMap K A) = vK.integer) :
    vK.HasExtension vA where
  val_isEquiv_comap := by
    rw [isEquiv_iff_val_le_one]
    intro x
    simp_rw [← Valuation.mem_integer_iff, ← h, Subring.mem_comap, mem_integer_iff, comap_apply]

instance instAlgebraInteger : Algebra vR.integer vA.integer where
  smul r a := ⟨r • a,
    Algebra.smul_def r (a : A) ▸ mul_mem ((val_map_le_one_iff vR vA _).mpr r.2) a.2⟩
  algebraMap := (algebraMap R A).restrict vR.integer vA.integer
    (by simp [Valuation.mem_integer_iff, val_map_le_one_iff vR vA])
  commutes' _ _ := Subtype.ext (Algebra.commutes _ _)
  smul_def' _ _ := Subtype.ext (Algebra.smul_def _ _)

@[simp, norm_cast]
theorem val_smul (r : vR.integer) (a : vA.integer) : ↑(r • a : vA.integer) = (r : R) • (a : A) := by
  rfl

@[simp, norm_cast]
theorem val_algebraMap (r : vR.integer) :
    ((algebraMap vR.integer vA.integer) r : A) = (algebraMap R A) (r : R) := by
  rfl

instance instIsScalarTowerInteger : IsScalarTower vR.integer vA.integer A where
  smul_assoc x y z := by
    simp only [Algebra.smul_def]
    exact mul_assoc _ _ _

instance instNoZeroSMulDivisorsInteger [NoZeroSMulDivisors R A] :
    NoZeroSMulDivisors vR.integer vA.integer := by
  refine ⟨fun {x y} e ↦ ?_⟩
  have : (x : R) • (y : A) = 0 := by simpa [Subtype.ext_iff, Algebra.smul_def] using e
  simpa only [Subtype.ext_iff, smul_eq_zero] using this

theorem algebraMap_injective [vK.HasExtension vA] [Nontrivial A] :
    Function.Injective (algebraMap vK.integer vA.integer) := by
  intro x y h
  simp only [Subtype.ext_iff, val_algebraMap] at h
  ext
  apply RingHom.injective (algebraMap K A) h

@[instance]
theorem instIsLocalHomValuationInteger {S ΓS : Type*} [CommRing S]
    [LinearOrderedCommGroupWithZero ΓS]
    [Algebra R S] [IsLocalHom (algebraMap R S)] {vS : Valuation S ΓS}
    [vR.HasExtension vS] : IsLocalHom (algebraMap vR.integer vS.integer) where
  map_nonunit r hr := by
    apply (Valuation.integer.integers (v := vR)).isUnit_of_one
    · exact (isUnit_map_iff (algebraMap R S) _).mp (hr.map (algebraMap _ S))
    · apply (Valuation.integer.integers (v := vS)).one_of_isUnit at hr
      exact (val_map_eq_one_iff vR vS _).mp hr

end integer

section AlgebraInstances

open IsLocalRing Valuation ValuationSubring

variable {K L Γ₀ Γ₁ : outParam Type*} [Field K] [Field L] [Algebra K L]
  [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₁] (vK : Valuation K Γ₀)
  (vL : Valuation L Γ₁) [vK.HasExtension vL]

local notation "K₀" => Valuation.valuationSubring vK
local notation "L₀" => Valuation.valuationSubring vL

lemma algebraMap_mem_valuationSubring (x : K₀) : algebraMap K L x ∈ L₀ := by
  rw [mem_valuationSubring_iff, ← _root_.map_one vL, ← _root_.map_one (algebraMap K L),
    val_map_le_iff (vR := vK), _root_.map_one]
  exact x.2

instance instAlgebra_valuationSubring : Algebra K₀ L₀ :=
  inferInstanceAs (Algebra vK.integer vL.integer)

@[simp]
lemma coe_algebraMap_valuationSubring_eq (x : K₀) :
    (algebraMap K₀ L₀ x : L) = algebraMap K L (x : K) := rfl

instance instIsScalarTower_valuationSubring : IsScalarTower K₀ K L :=
  inferInstanceAs (IsScalarTower vK.integer K L)

instance instIsScalarTower_valuationSubring' : IsScalarTower K₀ L₀ L :=
  instIsScalarTowerInteger

instance : IsLocalHom (algebraMap K₀ L₀) := instIsLocalHomValuationInteger

lemma algebraMap_mem_maximalIdeal_iff {x : K₀} :
    algebraMap K₀ L₀ x ∈ (maximalIdeal L₀) ↔ x ∈ maximalIdeal K₀ := by
  simp [mem_maximalIdeal, map_mem_nonunits_iff, _root_.mem_nonunits_iff]

lemma maximalIdeal_comap_algebraMap_eq_maximalIdeal :
    (maximalIdeal L₀).comap (algebraMap K₀ L₀) = maximalIdeal K₀ :=
  Ideal.ext fun _ ↦ by rw [Ideal.mem_comap, algebraMap_mem_maximalIdeal_iff]

instance : Ideal.LiesOver (maximalIdeal L₀) (maximalIdeal K₀) :=
  ⟨(maximalIdeal_comap_algebraMap_eq_maximalIdeal _ _).symm⟩

lemma algebraMap_residue_eq_residue_algebraMap (x : K₀) :
    (algebraMap (ResidueField K₀) (ResidueField L₀)) (IsLocalRing.residue K₀ x) =
      IsLocalRing.residue L₀ (algebraMap K₀ L₀ x) :=
  rfl

end AlgebraInstances

end HasExtension

end Valuation
