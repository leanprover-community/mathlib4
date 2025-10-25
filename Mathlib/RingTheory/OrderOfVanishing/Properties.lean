/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles
-/
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Order of vanishing properties

In this file we define various properties of the order of vanishing, including some API for
computing the order of vanishing in a discrete valuation ring.
-/

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

/--
For `x : R` a non zero divisor, `ord R (x^n) = n • ord R x`.
-/
@[simp]
theorem ord_pow (x : R) (hx : x ∈ nonZeroDivisors R) (n : ℕ) : ord R (x ^ n) = n • ord R x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ord_mul, ih, succ_nsmul]
    exact hx

/--
For `x : R` a non zero divisor, `ord R (-x) = ord R x`.
-/
@[simp]
lemma ord_neg (x : R) : ord R (-x) = ord R x:= by
  simp only [ord]
  congr 2
  all_goals exact Ideal.span_singleton_neg x

@[simp]
lemma ord_mul_of_isUnit (a : R) (h : IsUnit a) (x : R) : ord R (a * x) = ord R x := by
  rw [ord, ord, Ideal.span_singleton_mul_left_unit h x]
/--
In an `S` algebra `R`, the order of vanishing of `x : R` is equal to the order of vanishing
of `a • x` for `a` a unit in `S`.
-/
@[simp]
lemma ord_smul_of_isUnit {S : Type*} [CommRing S] [Algebra S R]
    (a : S) (h : IsUnit a) (x : R) : ord R (a • x) = ord R x := by
  rw [Algebra.smul_def a x]
  exact ord_mul_of_isUnit ((algebraMap S R) a) (RingHom.isUnit_map (algebraMap S R) h) x

/-
Simple lemma saying `ord (x) ≤ ord (a * x)`. One should note that the order here
is the order on `ℕ∞` where `∞` is a top element.
-/
lemma ord_le_mul (a : R) (x : R) : ord R x ≤ ord R (a * x) := by
  simp only [ord]
  suffices Ideal.span {a * x} ≤ Ideal.span {x} by
    let g : (R ⧸ Ideal.span {a * x}) →ₗ[R] (R ⧸ Ideal.span {x}) := Submodule.factor this
    refine Module.length_le_of_surjective (Submodule.factor this) (Submodule.factor_surjective this)
  rw [@Ideal.span_singleton_le_span_singleton]
  exact Dvd.intro_left (Algebra.algebraMap a) rfl

/--
In an `S` algebra `R`, the order of vanishing of `x : R` is less than or equal
to the order of vanishing of `a • x` for any `a : S`. One should note that the order here
is the order on `ℕ∞` where `∞` is a top element.
-/
lemma ord_le_smul {S : Type*} [CommRing S] [Algebra S R] (a : S) (x : R) :
    ord R x ≤ ord R (a • x) := by simp [Algebra.smul_def, ord_le_mul]

/--
The order of vanishing of a unit is `0`.
-/
@[simp]
lemma ord_of_isUnit (x : R) (hx : IsUnit x) : ord R x = 0 := by
  simpa using ord_smul_of_isUnit x hx (1 : R)

section IsDiscreteValuationRing


def Submodule.orderIsoOfAlgebraMapSurjective
    {R S M : Type*} [CommRing R] [Ring S] [AddCommGroup M]
    [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]
    (h : Function.Surjective (algebraMap R S)) : Submodule S M ≃o Submodule R M where
  toFun N := N.restrictScalars R
  invFun N := ⟨N.toAddSubmonoid, by simpa [h.forall] using N.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := .rfl

lemma isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective
    {R S M : Type*} [CommRing R] [Ring S] [AddCommGroup M]
    [Algebra R S] [Module R M] [Module S M] [IsScalarTower R S M]
    (h : Function.Surjective (algebraMap R S)) : IsSimpleModule R M ↔ IsSimpleModule S M := by
  rw [isSimpleModule_iff, isSimpleModule_iff,
    (Submodule.orderIsoOfAlgebraMapSurjective h).isSimpleOrder_iff]

variable [IsDomain R] [IsDiscreteValuationRing R]
/--
In a discrete valuation ring, the order of vanishing of an irreducible element is `1`.
-/
theorem ord_irreducible (ϖ : R) (hϖ : Irreducible ϖ) : ord R ϖ = 1 := by
  rw [Ring.ord, Module.length_eq_one_iff]
  have : (Ideal.span {ϖ}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hϖ
  rw [isSimpleModule_iff_isSimpleModule_of_algebraMap_surjective (S := R ⧸ Ideal.span {ϖ})
    Ideal.Quotient.mk_surjective]
  letI := Ideal.Quotient.field (Ideal.span {ϖ})
  infer_instance

variable (R) in
lemma IsDiscreteValutationRing.krullDim_eq_one : ¬ KrullDimLE 0 R := by
  intro a
  have : IsLocalRing R := by exact IsLocalRing.of_singleton_maximalSpectrum
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have c := Ring.KrullDimLE.isNilpotent_iff_mem_maximalIdeal (x := ϖ)
  have : ϖ ∈ IsLocalRing.maximalIdeal R := by
    rw [Irreducible.maximalIdeal_eq hϖ]
    exact Ideal.mem_span_singleton_self ϖ
  have := c.mpr this
  aesop

lemma ord_eq_addVal (x : R) : ord R x = IsDiscreteValuationRing.addVal R x := by
  by_cases hx : x = 0
  · simp [hx, Ring.ord]
    subst hx
    by_contra!
    rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at this
    have art := this.2
    rw [Ideal.span_singleton_zero] at art
    have : IsArtinianRing R :=
      (LinearEquiv.isArtinian_iff (Submodule.quotEquivOfEqBot ⊥ rfl).symm).mpr art
    exact (IsDiscreteValutationRing.krullDim_eq_one R) (PrimeSpectrum.instKrullDimLEOfNatNat R)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, α, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  rw [ord_mul, ord_pow, ord_irreducible ϖ hϖ]
  · simp [IsDiscreteValuationRing.addVal_uniformizer hϖ]
  all_goals simp_all [Irreducible.ne_zero hϖ]

/--
In a discrete valuation ring `R`, if the order of vansihing of `x` and `y` is
the same then `x` and `y` must be associated.
-/
lemma associated_of_ord_eq (x y : R) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ord R x = ord R y) : Associated x y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, α, hx'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  obtain ⟨n, β, hy'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rw [ord_eq_addVal x, ord_eq_addVal y, IsDiscreteValuationRing.addVal_def x α hϖ m hx',
      IsDiscreteValuationRing.addVal_def y β hϖ n hy'] at h
  simp [ENat.coe_inj.mp h, hx', hy', Associates.mk_eq_mk_iff_associated.mp rfl]

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

  simp [ordFrac_eq_ord R x hx, ordMonoidWithZeroHom_eq_ord x (by simp [hx])]
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
    [l : IsScalarTower S R K] (a : S) (ha : algebraMap S R a ≠ 0) (f : K) :
    Ring.ordFrac R f ≤ Ring.ordFrac R (a • f) := by
  by_cases j : f = 0
  · simp[j]
  suffices (ordFrac R) f ≤ (ordFrac R) ((algebraMap S K) a • f) by simp_all only [ne_eq,
    algebraMap_smul]
  simp only [smul_eq_mul, map_mul]
  suffices (ordFrac R) ((algebraMap S K) a) ≥ 1 by exact le_mul_of_one_le_left' this
  suffices (ordFrac R) ((algebraMap R K) (algebraMap S R a)) ≥ 1 by
    simpa [l.algebraMap_eq]
  apply ordFrac_ge_one_of_ne_zero
  exact ha

/--
The analogue of `ord_of_isUnit` for `ordFrac`, saying `ordFrac R (algebraMap R K x) = 1` for some
unit `x`.
-/
lemma ordFrac_of_isUnit (x : R) (hx : IsUnit x) :
    ordFrac R (algebraMap R K x) = 1 := by
  have : x ≠ 0 := by exact IsUnit.ne_zero hx
  have thing : x ∈ nonZeroDivisors R := by exact IsUnit.mem_nonZeroDivisors hx
  simp [ordFrac_eq_ord R x this, thing]
  rw [ord_of_isUnit x hx]
  aesop

/--
In a discrete valuation ring, `ordFrac (algebraMap R K ϖ) = WithZero.exp 1`
for an irreducible element `ϖ`. This is the analogue of `ord_irreducible` for `ordFrac`.
-/
lemma ordFrac_irreducible [IsDiscreteValuationRing R]
    (ϖ : R) (hϖ : Irreducible ϖ) : ordFrac R (algebraMap R K ϖ) = WithZero.exp 1 := by
  have : ϖ ≠ 0 := by exact Irreducible.ne_zero hϖ
  have thing : ϖ ∈ nonZeroDivisors R := by exact mem_nonZeroDivisors_of_ne_zero this
  simp [ordFrac_eq_ord R ϖ this, thing]
  rw [ord_irreducible ϖ hϖ]
  aesop

/--
For `x y : R`, if `x + y ≠ 0` then `min (ordFrac R x) (ordFrac R y) ≤ ordFrac R (x + y)`. The
condition that `x + y ≠ 0` is used to guarantee that all the elements we're taking `ordFrac` of
are nonzero, meaning none of them will be `0` in `ℤᵐ⁰`. This allows us to use `ord_add` (which
uses the ordering on `ℕ∞`), since these orders correspond on non `⊤` elements.
-/
theorem ordFrac_add [IsDiscreteValuationRing R] (x y : K) (h : x + y ≠ 0) :
    min (Ring.ordFrac R x) (Ring.ordFrac R y) ≤ Ring.ordFrac R (x + y) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  by_cases hx0 : x = 0
  · simp[hx0]
  by_cases hy0 : y = 0
  · simp[hy0]
  obtain ⟨m, α, hx⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ _ hx0
  obtain ⟨n, β, hy⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ _ hy0

  rw [Units.smul_def, Algebra.smul_def] at hx hy
  wlog hmn : m ≤ n
  · rw[min_comm, add_comm]
    have sm : y + x ≠ 0 := by  rwa [add_comm]
    apply this y x sm ϖ hϖ hy0 hx0 n β hy m α hx
    omega
  obtain ⟨k, rfl⟩ := Int.exists_add_of_le hmn
  have xy : x + y = (algebraMap R K α + (algebraMap R K β) * (algebraMap R K ϖ)^k) *
      (algebraMap R K ϖ)^m := by
    rw [hx, hy, ← zpow_natCast, zpow_add₀]
    · ring
    · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors <|
        mem_nonZeroDivisors_of_ne_zero <| Irreducible.ne_zero hϖ

  rw [xy, hx, hy, map_mul, map_mul, map_mul, map_zpow₀, map_zpow₀,
     ordFrac_of_isUnit (α : R), ordFrac_of_isUnit (β : R), ordFrac_irreducible _ hϖ]

  · simp only [← WithZero.exp_zsmul, Int.zsmul_eq_mul, mul_one, one_mul, WithZero.exp_add,
      inf_le_iff, WithZero.exp_pos, le_mul_iff_one_le_left]
    have : (algebraMap R K) ↑α + (algebraMap R K) ↑β *
         (algebraMap R K) ϖ ^ k = algebraMap R K (α + β *ϖ^k) := by simp_all
    rw [this]
    have : α + β *ϖ^k ≠ 0 := by
      rw [xy, this] at h
      have m : (algebraMap R K) (↑α + ↑β * ϖ ^ k) ≠ 0 := by
        rw [mul_ne_zero_iff] at h
        exact h.1
      rw [← (algebraMap.coe_zero : algebraMap R K 0 = 0)] at m
      exact fun a ↦ m (congrArg (⇑(algebraMap R K)) a)

    exact Or.inl <| ordFrac_ge_one_of_ne_zero _ this
  all_goals simp

/--
In a discrete valuation ring `R` with fraction ring `K`, if `x y : K` and
`ordFrac R x = ordFrac R y`, then `x` must only differ from `y` by a unit of `R`.
-/
theorem associated_of_ordFrac_eq [IsDiscreteValuationRing R] (x y : K) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : ordFrac R x = ordFrac R y) : ∃ u : Rˣ, u • x = y := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, α, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ _ hx
  obtain ⟨n, β, rfl⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ _ hy

  rw [Units.smul_def, Algebra.smul_def, Units.smul_def, Algebra.smul_def] at ⊢ h
  nth_rewrite 2 [mul_comm] at h
  rw [mul_comm, map_mul, map_mul, map_zpow₀, map_zpow₀] at h
  simp [ordFrac_irreducible ϖ hϖ, ordFrac_of_isUnit] at h
  use β * α⁻¹
  rw[Units.smul_def, Algebra.smul_def]
  simp only [Units.val_mul, map_mul, map_units_inv, h]
  field_simp

end ordFrac
