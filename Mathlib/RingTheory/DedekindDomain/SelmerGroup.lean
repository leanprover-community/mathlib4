/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/
import Mathlib.Algebra.Group.Equiv.TypeTags
import Mathlib.Data.ZMod.Quotient
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Selmer groups of fraction fields of Dedekind domains

Let $K$ be the field of fractions of a Dedekind domain $R$. For any set $S$ of prime ideals in the
height one spectrum of $R$, and for any natural number $n$, the Selmer group $K(S, n)$ is defined to
be the subgroup of the unit group $K^\times$ modulo $n$-th powers where each element has $v$-adic
valuation divisible by $n$ for all prime ideals $v$ away from $S$. In other words, this is precisely
$$ K(S, n) := \{x(K^\times)^n \in K^\times / (K^\times)^n \ \mid \
                \forall v \notin S, \ \mathrm{ord}_v(x) \equiv 0 \pmod n\}. $$

There is a fundamental short exact sequence
$$ 1 \to R_S^\times / (R_S^\times)^n \to K(S, n) \to \mathrm{Cl}_S(R)[n] \to 0, $$
where $R_S^\times$ is the $S$-unit group of $R$ and $\mathrm{Cl}_S(R)$ is the $S$-class group of
$R$. If the flanking groups are both finite, then $K(S, n)$ is finite by the first isomorphism
theorem. Such is the case when $R$ is the ring of integers of a number field $K$, $S$ is finite, and
$n$ is positive, in which case $R_S^\times$ is finitely generated by Dirichlet's unit theorem and
$\mathrm{Cl}_S(R)$ is finite by the class number theorem.

This file defines the Selmer group $K(S, n)$ and some basic facts.

## Main definitions

 * `IsDedekindDomain.selmerGroup`: the Selmer group.
 * TODO: maps in the sequence.

## Main statements

 * TODO: proofs of exactness of the sequence.
 * TODO: proofs of finiteness for global fields.

## Notations

 * `K⟮S, n⟯`: the Selmer group with parameters `K`, `S`, and `n`.

## Implementation notes

The Selmer group is typically defined as a subgroup of the Galois cohomology group $H^1(K, \mu_n)$
with certain local conditions defined by $v$-adic valuations, where $\mu_n$ is the group of $n$-th
roots of unity over a separable closure of $K$. Here $H^1(K, \mu_n)$ is identified with
$K^\times / (K^\times)^n$ by the long exact sequence from Kummer theory and Hilbert's theorem 90,
and the fundamental short exact sequence becomes an easy consequence of the snake lemma. This file
will define all the maps explicitly for computational purposes, but isomorphisms to the Galois
cohomological definition will be provided when possible.

## References

https://doc.sagemath.org/html/en/reference/number_fields/sage/rings/number_field/selmer_group.html

## Tags

class group, selmer group, unit group
-/

set_option quotPrecheck false
local notation K "/" n => Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range

namespace IsDedekindDomain

noncomputable section

open scoped Classical DiscreteValuation nonZeroDivisors

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R] {K : Type v} [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-! ### Valuations of non-zero elements -/


namespace HeightOneSpectrum

/-- The multiplicative `v`-adic valuation on `Kˣ`. -/
def valuationOfNeZeroToFun (x : Kˣ) : Multiplicative ℤ :=
  let hx := IsLocalization.sec R⁰ (x : K)
  Multiplicative.ofAdd <|
    (-(Associates.mk v.asIdeal).count (Associates.mk <| Ideal.span {hx.fst}).factors : ℤ) -
      (-(Associates.mk v.asIdeal).count (Associates.mk <| Ideal.span {(hx.snd : R)}).factors : ℤ)

@[simp]
theorem valuationOfNeZeroToFun_eq (x : Kˣ) :
    (v.valuationOfNeZeroToFun x : ℤₘ₀) = v.valuation (x : K) := by
  rw [show v.valuation (x : K) = _ * _ by rfl]
  rw [Units.val_inv_eq_inv_val]
  change _ = ite _ _ _ * (ite _ _ _)⁻¹
  simp_rw [IsLocalization.toLocalizationMap_sec, SubmonoidClass.coe_subtype,
    if_neg <| IsLocalization.sec_fst_ne_zero le_rfl x.ne_zero,
    if_neg (nonZeroDivisors.coe_ne_zero _),
    valuationOfNeZeroToFun, ofAdd_sub, ofAdd_neg, div_inv_eq_mul, WithZero.coe_mul,
    WithZero.coe_inv, inv_inv]

/-- The multiplicative `v`-adic valuation on `Kˣ`. -/
def valuationOfNeZero : Kˣ →* Multiplicative ℤ where
  toFun := v.valuationOfNeZeroToFun
  map_one' := by rw [← WithZero.coe_inj, valuationOfNeZeroToFun_eq]; exact map_one _
  map_mul' _ _ := by
    rw [← WithZero.coe_inj, WithZero.coe_mul]
    simp only [valuationOfNeZeroToFun_eq]; exact map_mul _ _ _

@[simp]
theorem valuationOfNeZero_eq (x : Kˣ) : (v.valuationOfNeZero x : ℤₘ₀) = v.valuation (x : K) :=
  valuationOfNeZeroToFun_eq v x

@[simp]
theorem valuation_of_unit_eq (x : Rˣ) :
    v.valuationOfNeZero (Units.map (algebraMap R K : R →* K) x) = 1 := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq, Units.coe_map, eq_iff_le_not_lt]
  constructor
  · exact v.valuation_le_one x
  · cases' x with x _ hx _
    change ¬v.valuation (algebraMap R K x) < 1
    apply_fun v.intValuation at hx
    rw [map_one, map_mul] at hx
    rw [not_lt, ← hx, ← mul_one <| v.valuation _, valuation_of_algebraMap,
      mul_le_mul_left₀ <| left_ne_zero_of_mul_eq_one hx]
    exact v.intValuation_le_one _

-- Porting note: invalid attribute 'semireducible', declaration is in an imported module
-- attribute [local semireducible] MulOpposite

/-- The multiplicative `v`-adic valuation on `Kˣ` modulo `n`-th powers. -/
def valuationOfNeZeroMod (n : ℕ) : (K/n) →* Multiplicative (ZMod n) :=
  (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative.toMonoidHom.comp <|
    QuotientGroup.map (powMonoidHom n : Kˣ →* Kˣ).range
      (AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)))
      v.valuationOfNeZero
      (by
        rintro _ ⟨x, rfl⟩
        exact
          ⟨v.valuationOfNeZero x, by simp only [powMonoidHom_apply, map_pow, Int.toAdd_pow]; rfl⟩)

@[simp]
theorem valuation_of_unit_mod_eq (n : ℕ) (x : Rˣ) :
    v.valuationOfNeZeroMod n (Units.map (algebraMap R K : R →* K) x : K/n) = 1 := by
  -- This used to be `rw`, but we need `erw` after leanprover/lean4#2644
  erw [valuationOfNeZeroMod, MonoidHom.comp_apply, ← QuotientGroup.coe_mk',
    QuotientGroup.map_mk' (G := Kˣ) (N := MonoidHom.range (powMonoidHom n)),
    valuation_of_unit_eq, QuotientGroup.mk_one, map_one]

end HeightOneSpectrum

/-! ### Selmer groups -/


variable {S S' : Set <| HeightOneSpectrum R} {n : ℕ}

/-- The Selmer group `K⟮S, n⟯`. -/
def selmerGroup : Subgroup <| K/n where
  carrier := {x : K/n | ∀ (v) (_ : v ∉ S), (v : HeightOneSpectrum R).valuationOfNeZeroMod n x = 1}
  one_mem' _ _ := by rw [map_one]
  mul_mem' hx hy v hv := by rw [map_mul, hx v hv, hy v hv, one_mul]
  inv_mem' hx v hv := by rw [map_inv, hx v hv, inv_one]

-- Porting note: was `scoped[SelmerGroup]` but that does not work even using `open SelmerGroup`
local notation K "⟮" S "," n "⟯" => @selmerGroup _ _ _ K _ _ _ S n

namespace selmerGroup

theorem monotone (hS : S ≤ S') : K⟮S,n⟯ ≤ K⟮S',n⟯ := fun _ hx v => hx v ∘ mt (@hS v)

/-- The multiplicative `v`-adic valuations on `K⟮S, n⟯` for all `v ∈ S`. -/
def valuation : K⟮S,n⟯ →* S → Multiplicative (ZMod n) where
  toFun x v := (v : HeightOneSpectrum R).valuationOfNeZeroMod n (x : K/n)
  map_one' := funext fun v => map_one _
  map_mul' x y := by simp only [Submonoid.coe_mul, Subgroup.coe_toSubmonoid, map_mul]; rfl

theorem valuation_ker_eq :
    valuation.ker = K⟮(∅ : Set <| HeightOneSpectrum R),n⟯.subgroupOf (K⟮S,n⟯) := by
  ext ⟨_, hx⟩
  constructor
  · intro hx' v _
    by_cases hv : v ∈ S
    · exact congr_fun hx' ⟨v, hv⟩
    · exact hx v hv
  · exact fun hx' => funext fun v => hx' v <| Set.not_mem_empty v

/-- The natural homomorphism from `Rˣ` to `K⟮∅, n⟯`. -/
def fromUnit {n : ℕ} : Rˣ →* K⟮(∅ : Set <| HeightOneSpectrum R),n⟯ where
  toFun x :=
    ⟨QuotientGroup.mk <| Units.map (algebraMap R K).toMonoidHom x, fun v _ =>
      v.valuation_of_unit_mod_eq n x⟩
  map_one' := by simp only [map_one, QuotientGroup.mk_one, Subgroup.mk_eq_one]
  map_mul' _ _ := by simp only [RingHom.toMonoidHom_eq_coe, map_mul, MonoidHom.mem_range,
    powMonoidHom_apply, QuotientGroup.mk_mul, Submonoid.mk_mul_mk]

theorem fromUnit_ker [hn : Fact <| 0 < n] :
    (@fromUnit R _ _ K _ _ _ n).ker = (powMonoidHom n : Rˣ →* Rˣ).range := by
  ext ⟨_, _, _, _⟩
  constructor
  · intro hx
    rcases (QuotientGroup.eq_one_iff _).mp (Subtype.mk.inj hx) with ⟨⟨v, i, vi, iv⟩, hx⟩
    have hv : ↑(_ ^ n : Kˣ) = algebraMap R K _ := congr_arg Units.val hx
    have hi : ↑(_ ^ n : Kˣ)⁻¹ = algebraMap R K _ := congr_arg Units.inv hx
    rw [Units.val_pow_eq_pow_val] at hv
    rw [← inv_pow, Units.inv_mk, Units.val_pow_eq_pow_val] at hi
    rcases IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (x := v) hn.out
        (hv.symm ▸ isIntegral_algebraMap) with
      ⟨v', rfl⟩
    rcases IsIntegrallyClosed.exists_algebraMap_eq_of_isIntegral_pow (R := R) (x := i) hn.out
        (hi.symm ▸ isIntegral_algebraMap) with
      ⟨i', rfl⟩
    rw [← map_mul, map_eq_one_iff _ <| NoZeroSMulDivisors.algebraMap_injective R K] at vi
    rw [← map_mul, map_eq_one_iff _ <| NoZeroSMulDivisors.algebraMap_injective R K] at iv
    rw [Units.val_mk, ← map_pow] at hv
    exact ⟨⟨v', i', vi, iv⟩, by
      simpa only [Units.ext_iff, powMonoidHom_apply, Units.val_pow_eq_pow_val] using
         NoZeroSMulDivisors.algebraMap_injective R K hv⟩
  · rintro ⟨x, hx⟩
    rw [← hx]
    exact Subtype.mk_eq_mk.mpr <| (QuotientGroup.eq_one_iff _).mpr ⟨Units.map (algebraMap R K) x,
      by simp only [powMonoidHom_apply, RingHom.toMonoidHom_eq_coe, map_pow]⟩

/-- The injection induced by the natural homomorphism from `Rˣ` to `K⟮∅, n⟯`. -/
def fromUnitLift [Fact <| 0 < n] : (R/n) →* K⟮(∅ : Set <| HeightOneSpectrum R),n⟯ :=
  (QuotientGroup.kerLift _).comp
    (QuotientGroup.quotientMulEquivOfEq (fromUnit_ker (R := R))).symm.toMonoidHom

theorem fromUnitLift_injective [Fact <| 0 < n] :
    Function.Injective <| @fromUnitLift R _ _ K _ _ _ n _ := by
  dsimp only [fromUnitLift, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact Function.Injective.comp (QuotientGroup.kerLift_injective _) (MulEquiv.injective _)

end selmerGroup

end

end IsDedekindDomain
