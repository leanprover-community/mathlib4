/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/

module

public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.Basic


/-!
# Order of vanishing properties

In this file we define various properties of the order of vanishing, including some API for
computing the order of vanishing in a discrete valuation ring.
-/

@[expose] public section

variable {R : Type*} [CommRing R]

open Ring

section NoetherianDimLEOne

variable {R : Type*} [CommRing R]
variable [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/--
In a Noetherian ring of krull dimension less than or equal to `1`, the order of vanishing
of a non zero divisor `a` is not `⊤`.
-/
lemma ord_ne_top (a : R) (ha : a ∈ nonZeroDivisors R) : ord R a ≠ ⊤ := by
  simp [isFiniteLength_quotient_span_singleton R ha, Ring.ord, Module.length_ne_top_iff]

open scoped nonZeroDivisors
/--
Order of vanishing function as a monoid homomorphism
-/
noncomputable
def ordMonoidHom : R⁰ →* Multiplicative ℕ where
  toFun x := .ofAdd <| (Ring.ord R x).untop (ord_ne_top _ x.2)
  map_one' := by simp
  map_mul' x y := by
    rw [← ofAdd_add]
    congr 1
    apply WithTop.coe_injective
    simp [ord_mul]

lemma ord_eq_ordMonoidHom (x : R⁰) : Ring.ord R x = (ordMonoidHom x).toAdd := by
  change _ = WithTop.some ((Ring.ord R x).untop (ord_ne_top _ x.2))
  simp

lemma ordMonoidWithZeroHom_eq_ordMonoidHom [Nontrivial R] (x : R⁰) :
    ordMonoidWithZeroHom R x = .coe (.ofAdd ((ordMonoidHom x).toAdd : ℤ)) := by
  simp only [SetLike.coe_mem, ordMonoidWithZeroHom_eq_ord, ordMonoidHom, MonoidHom.coe_mk,
    OneHom.coe_mk, toAdd_ofAdd]
  generalize_proofs ha
  generalize ord R x.1 = a at *
  induction a
  · simp at ha
  · rfl

/--
Analogue of `ord_ne_top` for `ordMonoidWithZeroHom`.
-/
lemma ordMonoidWithZeroHom_ne_zero [Nontrivial R] (a : R) (ha : a ∈ nonZeroDivisors R) :
    ordMonoidWithZeroHom R a ≠ 0 := by
  lift a to R⁰ using ha
  simp [ordMonoidWithZeroHom_eq_ordMonoidHom, -ordMonoidWithZeroHom_eq_ord]

variable [Nontrivial R]
/--
Helper lemma to pass between the orders on `ℕ∞` and `ℤᵐ⁰` (which notably have different behaviour at
`∞`). Note that here we're using the fact that the order of any non zero divisor is finite, hence
the assumptions on the ring.
-/
lemma ord_le_iff (a b : R) (ha : a ∈ nonZeroDivisors R) (hb : b ∈ nonZeroDivisors R) :
    ord R a ≤ ord R b ↔ ordMonoidWithZeroHom R a ≤ ordMonoidWithZeroHom R b := by
  lift a to R⁰ using ha
  lift b to R⁰ using hb
  simp [ordMonoidWithZeroHom_eq_ordMonoidHom, ord_eq_ordMonoidHom, -ordMonoidWithZeroHom_eq_ord]

end NoetherianDimLEOne

section IsDiscreteValuationRing

variable [IsDomain R] [IsDiscreteValuationRing R]

/--
In a discrete valuation ring, `ord R x` is the same as `addVal R x`. We prefer the second spelling
here for most purposes.
-/
@[simp]
lemma ord_eq_addVal (x : R) : ord R x = IsDiscreteValuationRing.addVal R x := by
  by_cases hx : x = 0
  · simp only [ord, hx, AddValuation.map_zero]
    subst hx
    by_contra!
    rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at this
    have art := this.2
    rw [Ideal.span_singleton_zero] at art
    have : IsArtinianRing R :=
      (LinearEquiv.isArtinian_iff (Submodule.quotEquivOfEqBot ⊥ rfl).symm).mpr art
    exact (IsDiscreteValuationRing.not_krullDimLE_zero R) (PrimeSpectrum.instKrullDimLEOfNatNat R)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, α, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [ord_mul, ord_pow, ord_of_irreducible ϖ hϖ]
  · simp [IsDiscreteValuationRing.addVal_uniformizer hϖ]
  all_goals simp_all [Irreducible.ne_zero hϖ]

open IsDiscreteValuationRing
/--
In a discrete valuation ring `R`, if the order of vansihing of `x` and `y` is
the same then `x` and `y` must be associated.
-/
lemma ord_eq_iff_associated (x y : R) :
    ord R x = ord R y ↔ Associated x y := by simp [addVal_eq_iff_associated]

/--
For `x y : R` where `R` is a discrete valuation ring, we have that
`min (ord R x) (ord R y) ≤ ord R (x + y)`. It should be noted that the order
we're using here is the order on `ℕ∞`, where `⊤` is greater than everhing else.
This is relevant since when we're working with `ordFrac` we work with `ℤᵐ⁰`, where the
order instance has the `0` element less than everything else.
-/
theorem ord_add (x y : R) : min (Ring.ord R x) (Ring.ord R y) ≤ Ring.ord R (x + y) := by
  rw [ord_eq_addVal x, ord_eq_addVal y, ord_eq_addVal (x + y)]
  exact IsDiscreteValuationRing.addVal_add

end IsDiscreteValuationRing

section ordFrac

variable [IsDomain R] [IsNoetherianRing R] [KrullDimLE 1 R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/--
For any nonzero `x : R`, `ordFrac R (algebraMap R K x) ≥ 1`. Note here that this last
expression is in `ℤᵐ⁰`, so the syntax may be slightly different than expected. Namely,
the `1` here is `WithZero.exp 0`, and so would usually be written as `0` in the additive
context. Further, the order here is different to similar lemmas involving `Ring.ord`, since
here the order is on `ℤᵐ⁰` has the `∞` element less than everything else, whereas in `Ring.ord`
we work with the order on `ℕ∞` where the `∞` element is interpreted as a `⊤` element.
-/
lemma ordFrac_ge_one_of_ne_zero (x : R) (hx : x ≠ 0) :
    ordFrac R (algebraMap R K x) ≥ 1 := by
  simp only [ordFrac_eq_ord R x hx, ordMonoidWithZeroHom_eq_ord x (by simp [hx]), ge_iff_le]
  suffices ord R x ≠ ⊤ by
    rw [ENat.ne_top_iff_exists] at this
    obtain ⟨m, hm⟩ := this
    rw [← hm]
    have := WithZero.map'_coe (AddMonoidHom.toMultiplicative (Nat.castAddMonoidHom ℤ)) m
    have : AddMonoidHom.toMultiplicative (Nat.castAddMonoidHom ℤ) m ≥ 1 := by
      simp [← ofAdd_zero, Multiplicative.ofAdd_le]
    suffices WithZero.map' (AddMonoidHom.toMultiplicative (Nat.castAddMonoidHom ℤ)) 0 ≤
            (WithZero.map' (AddMonoidHom.toMultiplicative (Nat.castAddMonoidHom ℤ))) (m : ℕ∞) by
      exact left_eq_inf.mp rfl
    apply WithZero.map'_mono
    · rw [AddMonoidHom.coe_toMultiplicative]
      apply Monotone.comp
      · exact fun _ _ a ↦ a
      · apply Monotone.comp
        · simp_all only [ne_eq, WithZero.map'_coe, AddMonoidHom.toMultiplicative_apply_apply,
          Nat.coe_castAddMonoidHom, ge_iff_le, Nat.mono_cast]
        · exact fun _ _ a ↦ a
    · aesop
  simp only [ord, ne_eq]
  have := isFiniteLength_quotient_span_singleton R (x := x) (by simp[hx])
  exact Module.length_ne_top_iff.mpr this

/--
For `R` an `S` algebra (with a corresponding compatible action on `K`, the field of fractions
of `R`), for `f : K` and `a : S`, we have that `ordFrac R f ≤ ordFrac R (a • f)` as long as
`algebraMap S R a ≠ 0`.
-/
lemma ordFrac_le_smul {S : Type*} [CommRing S] [Algebra S R] [Algebra S K]
    [IsScalarTower S R K] (a : S) (ha : algebraMap S R a ≠ 0) (f : K) :
    Ring.ordFrac R f ≤ Ring.ordFrac R (a • f) := by
  by_cases j : f = 0
  · simp[j]
  suffices ordFrac R f ≤ ordFrac R (algebraMap S K a • f) by simp_all only [ne_eq,
    algebraMap_smul]
  simp only [smul_eq_mul, map_mul]
  suffices (ordFrac R) ((algebraMap S K) a) ≥ 1 by exact le_mul_of_one_le_left' this
  suffices (ordFrac R) ((algebraMap R K) (algebraMap S R a)) ≥ 1 by
    simpa [IsScalarTower.algebraMap_eq S R K]
  apply ordFrac_ge_one_of_ne_zero
  exact ha

/--
The analogue of `ord_of_isUnit` for `ordFrac`, saying `ordFrac R (algebraMap R K x) = 1` for some
unit `x`.
-/
@[simp]
lemma ordFrac_of_isUnit (x : R) (hx : IsUnit x) : ordFrac R (algebraMap R K x) = 1 := by
  have : x ≠ 0 := IsUnit.ne_zero hx
  have thing : x ∈ nonZeroDivisors R := IsUnit.mem_nonZeroDivisors hx
  simp only [ordFrac_eq_ord R x this, thing, ordMonoidWithZeroHom_eq_ord]
  rw [ord_of_isUnit x hx]
  aesop

/--
In a discrete valuation ring, `ordFrac (algebraMap R K ϖ) = WithZero.exp 1`
for an irreducible element `ϖ`. This is the analogue of `ord_irreducible` for `ordFrac`.
-/
lemma ordFrac_irreducible [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) : ordFrac R (algebraMap R K ϖ) = WithZero.exp 1 := by
  have : ϖ ≠ 0 := Irreducible.ne_zero hϖ
  simp only [ordFrac_eq_ord R ϖ this, mem_nonZeroDivisors_of_ne_zero this,
      ordMonoidWithZeroHom_eq_ord, ord_of_irreducible ϖ hϖ]
  rfl

/--
For a discrete valuation ring `R` with fraction ring `K`,
multiplicative kernel of `ordFrac R` is precisely the elements of `K`
which are in the image of a unit of `R` under the algebra map.
-/
lemma mker_ordFrac_eq_units [IsDiscreteValuationRing R] :
    MonoidHom.mker (ordFrac R) = (IsUnit.submonoid R).map (algebraMap R K) := by
  ext a
  simp only [MonoidHom.mem_mker, Submonoid.mem_map]
  constructor
  · intro h
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
    by_cases ha0 : a = 0
    · simp_all
    obtain ⟨m, α, hx⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ _ ha0
    rw [hx] at h
    have : m = 0 := by
      rw [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀,
        ordFrac_of_isUnit α.1 (Units.isUnit α), ordFrac_irreducible ϖ hϖ] at h
      simpa using h
    rw [this, Units.smul_def, Algebra.smul_def] at hx
    simp only [zpow_zero, mul_one] at hx
    rw [hx]
    use α.1
    exact ⟨Units.isUnit α, rfl⟩
  · intro h
    obtain ⟨x, h1, rfl⟩ := h
    exact ordFrac_of_isUnit x h1

/--
The analogue of `ord_of_isUnit` for `ordFrac`, saying `ordFrac R (algebraMap R K x) = 1` for some
unit `x`.
-/
lemma isUnit_iff_ordFrac_one_of_isDiscreteValuationRing [IsDiscreteValuationRing R] (x : R) :
    IsUnit x ↔ ordFrac R (algebraMap R K x) = 1 := by
  change IsUnit x ↔ algebraMap R K x ∈ MonoidHom.mker (ordFrac R)
  simp [mker_ordFrac_eq_units, IsUnit.mem_submonoid_iff]

/--
`ordFrac R` is precisely the inverse of the valuation
`IsDedekindDomain.HeightOneSpectrum.valuation K (IsDiscreteValuationRing.maximalIdeal R)`.
-/
theorem ordFrac_eq_inverse_comp_valuation [IsDiscreteValuationRing R] :
    ordFrac R =
    MonoidWithZeroHom.comp MonoidWithZero.inverse (IsDedekindDomain.HeightOneSpectrum.valuation K
    (IsDiscreteValuationRing.maximalIdeal R)).toMonoidWithZeroHom := by
  ext a
  by_cases ha : a = 0
  · simp_all
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) a
  simp_all [ordFrac_eq_ord, ord_eq_addVal,
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    IsDiscreteValuationRing.intValuation_maximalIdeal, WithZero.map'_apply]
  rfl

theorem ordFrac_eq_valuation_inv [IsDiscreteValuationRing R] (x : K) :
    ordFrac R x = ((IsDiscreteValuationRing.maximalIdeal R).valuation K x)⁻¹ := by
  simp [ordFrac_eq_inverse_comp_valuation]

/--
TODO: MOVE THIS SOMEWHERE THAT MAKES SENSE

NOTE THAT MATHLIB.ORDER.LATTICE MIGHT BE GOOD, BUT NOT NECESSARILY
-/
lemma min_inv_inv_le {G₀ : Type*} [Inv G₀] [LinearOrder G₀] {x y : G₀} :
    min x⁻¹ y⁻¹ ≤ (max x y)⁻¹ := by
  cases le_total x y <;> simp_all
#check mul_inv_lt_inv_mul_iff

/--
For `x y : R`, if `x + y ≠ 0` then `min (ordFrac R x) (ordFrac R y) ≤ ordFrac R (x + y)`. The
condition that `x + y ≠ 0` is used to guarantee that all the elements we're taking `ordFrac` of
are nonzero, meaning none of them will be `0` in `ℤᵐ⁰`. This allows us to use `ord_add` (which
uses the ordering on `ℕ∞`), since these orders correspond on non `⊤` elements.
-/
theorem ordFrac_add [IsDiscreteValuationRing R] (x y : K) (h1 : x + y ≠ 0) :
    min (Ring.ordFrac R x) (Ring.ordFrac R y) ≤ Ring.ordFrac R (x + y) := by
  simp only [ordFrac_eq_valuation_inv]
  grw [Valuation.map_add, min_inv_inv_le]
  simpa [WithZero.pos_iff_ne_zero]

/--
In a discrete valuation ring `R` with fraction ring `K`, if `x y : K` and
`ordFrac R x = ordFrac R y`, then `x` must only differ from `y` by a unit of `R`.
-/
theorem associated_of_ordFrac_eq [IsDiscreteValuationRing R] (x y : K)
    (h : ordFrac R x = ordFrac R y) : ∃ u : Rˣ, u • x = y := by
  by_cases hx : x = 0
  · simp_all only [map_zero, smul_zero, exists_const]
    by_contra!
    have : ordFrac R y ≠ 0 := by simp [this.symm]
    exact this h.symm
  by_cases hy : y = 0
  · simp_all
  have : (y / x) ∈ MonoidHom.mker (ordFrac R) := by simp_all
  rw [mker_ordFrac_eq_units] at this
  obtain ⟨u, h⟩ := this
  use IsUnit.unit h.1
  simp only [Units.smul_def, Algebra.smul_def, IsUnit.unit_spec, h.2]
  field_simp


end ordFrac
