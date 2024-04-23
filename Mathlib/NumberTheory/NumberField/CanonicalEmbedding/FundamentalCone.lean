/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.Units

/-!
# Fundamental Cone

Let `K` be a number field of signature `(r₁, r₂)`. We define an action of the units `(𝓞 K)ˣ` on
the space `ℝ^r₁ × ℂ^r₂`. The fundamental cone is a cone in `ℝ^r₁ × ℂ^r₂` that is a fundamental
domain for the action of `(𝓞 K)ˣ` up to roots of unity.

## Main definitions and results

* `NumberField.mixedEmbedding.unitSMul`: the action of `(𝓞 K)ˣ` on `ℝ^r₁ × ℂ^r₂` defined, for
`u : (𝓞 K)ˣ`, by multiplication component by component with `mixedEmbedding K u`.

* `NumberField.mixedEmbedding.fundamentalCone`: a cone in `ℝ^r₁ × ℂ^r₂` --that is a subset fixed
by multiplication by a scalar, see `smul_mem_of_mem`--, that is also a fundamental domain for the
action of `(𝓞 K)ˣ` up to roots of unity, see `exists_unitSMul_me` and
`torsion_unitSMul_mem_of_mem`.

* `NumberField.mixedEmbedding.fundamentalCone.integralPoint`: the subset of elements of the
fundamental cone that are images by `mixedEmbedding` of algebraic integers of `K`.

* `NumberField.mixedEmbedding.fundamentalCone.integralPointQuotEquivIsPrincipal`: the equivalence
between `fundamentalCone.integralPoint K / torsion K` and the principal ideals of `𝓞 K`.

* `NumberField.mixedEmbedding.fundamentalCone.card_isPrincipal_norm_mul`: for `n` positive, the
number of principal ideals in `𝓞 K` of norm `n` multiplied by the number of roots of unity is
equal to the number of `fundamentalCone.integralPoint K` of norm `n`.

## Tags

number field, canonical embedding, principal ideals
-/

variable (K : Type*) [Field K]

namespace NumberField.mixedEmbedding

open NumberField NumberField.InfinitePlace

/-- The space `ℝ^r₁ × ℂ^r₂` with `(r₁, r₂)` the signature of `K`. -/
local notation "E" K =>
  ({w : InfinitePlace K // IsReal w} → ℝ) × ({w : InfinitePlace K // IsComplex w} → ℂ)

noncomputable section UnitSMul

/-- The action of `(𝓞 K)ˣ` on `ℝ^r₁ × ℂ^r₂` defined, for `u : (𝓞 K)ˣ`, by multiplication components
by components with `mixedEmbedding K u`. -/
@[simps]
instance unitSMul : SMul (𝓞 K)ˣ (E K) where
  smul := fun u x ↦ (mixedEmbedding K u) * x

instance : MulAction (𝓞 K)ˣ (E K) where
  one_smul := fun _ ↦ by simp_rw [HSMul.hSMul, SMul.smul, Units.coe_one, map_one, one_mul]
  mul_smul := fun _ _ _ ↦ by simp_rw [HSMul.hSMul, SMul.smul, Units.coe_mul, map_mul, mul_assoc]

instance : SMulZeroClass (𝓞 K)ˣ (E K) where
  smul_zero := fun _ ↦ by simp_rw [HSMul.hSMul, SMul.smul, mul_zero]

variable [NumberField K]

theorem unitSMul_eq_iff_mul_eq {x y : (𝓞 K)} {u : (𝓞 K)ˣ} :
    u • mixedEmbedding K x = mixedEmbedding K y ↔ u * x = y := by
  rw [unitSMul_smul, ← map_mul, Function.Injective.eq_iff, ← Submonoid.coe_mul, Subtype.mk_eq_mk]
  exact mixedEmbedding_injective K

theorem norm_unit (u : (𝓞 K)ˣ) :
    mixedEmbedding.norm (mixedEmbedding K u) = 1 := by
  rw [norm_eq_norm, show |(Algebra.norm ℚ) (u : K)| = 1
      by exact NumberField.isUnit_iff_norm.mp (Units.isUnit u), Rat.cast_one]

theorem norm_unitSMul (u : (𝓞 K)ˣ) (x : E K) :
    mixedEmbedding.norm (u • x) = mixedEmbedding.norm x := by
  rw [unitSMul_smul, map_mul, norm_unit, one_mul]

end UnitSMul

noncomputable section logMap

open NumberField.Units NumberField.Units.dirichletUnitTheorem FiniteDimensional

variable [NumberField K] {K}

/-- The map from `ℝ^r₁ × ℂ^r₂` to `{w : InfinitePlace K // w ≠ w₀} → ℝ` (with `w₀` a fixed place)
define in such way that: 1) it factors the map `logEmbedding`, see `logMap_eq_logEmbedding`;
2) it is constant on the lines `{c • x | c ∈ ℝ}`, see `logMap_smul`. -/
def logMap (x : E K) : {w : InfinitePlace K // w ≠ w₀} → ℝ := by
  classical
  exact fun w ↦
    if hw : IsReal w.val then
      Real.log ‖x.1 ⟨w.val, hw⟩‖ - Real.log (mixedEmbedding.norm x) * (finrank ℚ K : ℝ)⁻¹
    else
      2 * (Real.log ‖x.2 ⟨w.val, not_isReal_iff_isComplex.mp hw⟩‖ -
        Real.log (mixedEmbedding.norm x) * (finrank ℚ K : ℝ)⁻¹)

theorem logMap_zero : logMap (0 : E K) = 0 := by
  ext
  simp_rw [logMap, Prod.fst_zero, Prod.snd_zero, map_zero, Pi.zero_apply, norm_zero, Real.log_zero,
    zero_mul, sub_zero, mul_zero, dite_eq_ite, ite_self]

theorem logMap_mul {x y : E K} (hx : mixedEmbedding.norm x ≠ 0) (hy : mixedEmbedding.norm y ≠ 0) :
    logMap (x * y) = logMap x + logMap y := by
  ext w
  simp_rw [Pi.add_apply, logMap]
  split_ifs with hw
  · rw [Prod.fst_mul, Pi.mul_apply, norm_mul, map_mul, Real.log_mul, Real.log_mul hx hy, add_mul]
    · ring
    · exact norm_ne_zero_iff.mpr <| (mixedEmbedding.norm_ne_zero_iff.mp hx).1 ⟨_, hw⟩
    · exact norm_ne_zero_iff.mpr <| (mixedEmbedding.norm_ne_zero_iff.mp hy).1 ⟨_, hw⟩
  · replace hw := not_isReal_iff_isComplex.mp hw
    rw [Prod.snd_mul, Pi.mul_apply, norm_mul, map_mul, Real.log_mul, Real.log_mul hx hy, add_mul]
    · ring
    · exact norm_ne_zero_iff.mpr <| (mixedEmbedding.norm_ne_zero_iff.mp hx).2 ⟨_, hw⟩
    · exact norm_ne_zero_iff.mpr <| (mixedEmbedding.norm_ne_zero_iff.mp hy).2 ⟨_, hw⟩

theorem logMap_eq_logEmbedding (u : (𝓞 K)ˣ) :
    logMap (mixedEmbedding K u) = logEmbedding K u := by
  ext
  simp_rw [logMap, mixedEmbedding.norm_unit, Real.log_one, zero_mul, sub_zero, logEmbedding,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, mult, Nat.cast_ite, ite_mul, Nat.cast_one, one_mul,
    Nat.cast_ofNat, mixedEmbedding, RingHom.prod_apply, Pi.ringHom_apply, norm_embedding_eq,
    norm_embedding_of_isReal]
  rfl

theorem logMap_unitSMul (u : (𝓞 K)ˣ) {x : E K} (hx : mixedEmbedding.norm x ≠ 0) :
    logMap (u • x) = logEmbedding K u + logMap x := by
  rw [unitSMul_smul, logMap_mul (by rw [norm_unit]; norm_num) hx, logMap_eq_logEmbedding]

theorem logMap_torsion_unitSMul (x : E K) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    logMap (ζ • x) = logMap x := by
  ext
  simp_rw [logMap, unitSMul_smul, Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, norm_mul, map_mul,
    norm_eq_norm, mixedEmbedding, RingHom.prod_apply, Pi.ringHom_apply,
    show |(Algebra.norm ℚ) (ζ : K)| = 1 by exact NumberField.isUnit_iff_norm.mp (Units.isUnit ζ),
    Rat.cast_one, one_mul, norm_embedding_eq, norm_embedding_of_isReal, (mem_torsion K).mp hζ,
    one_mul]

theorem logMap_smul {x : E K} {c : ℝ} (hx : mixedEmbedding.norm x ≠ 0) (hc : c ≠ 0) :
    logMap (c • x) = logMap x := by
  rw [show c • x = ((fun _ ↦ c, fun _ ↦ c) : (E K)) * x by rfl, logMap_mul _ hx, add_left_eq_self]
  ext
  have hr : (finrank ℚ K : ℝ) ≠ 0 :=  Nat.cast_ne_zero.mpr (ne_of_gt finrank_pos)
  simp_rw [logMap, Pi.zero_apply, norm_real, Real.log_pow, mul_comm, inv_mul_cancel_left₀ hr,
    Real.norm_eq_abs, Complex.norm_eq_abs,  Complex.abs_ofReal, sub_self, mul_zero, dite_eq_ite,
    ite_self]
  rw [norm_real]
  exact pow_ne_zero _ (abs_ne_zero.mpr hc)

end logMap

noncomputable section

open NumberField.Units NumberField.Units.dirichletUnitTheorem

variable [NumberField K]

/-- The fundamental cone is a cone in `ℝ^r₁ × ℂ^r₂` --that is a subset fixed by multiplication by
a scalar, see `smul_mem_of_mem`--, that is also a fundamental domain for the action of `(𝓞 K)ˣ` up
to roots of unity, see `exists_unitSMul_mem` and `torsion_unitSMul_mem_of_mem`. -/
def fundamentalCone : Set (E K) := by
  classical
  let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ _
  exact logMap⁻¹' (Zspan.fundamentalDomain B)

namespace fundamentalCone

protected theorem zero_mem : 0 ∈ fundamentalCone K := by
  simp_rw [fundamentalCone, Set.mem_preimage, Zspan.mem_fundamentalDomain, logMap_zero, map_zero,
    Finsupp.coe_zero, Pi.zero_apply, Set.left_mem_Ico, zero_lt_one, implies_true]

variable {K}

theorem smul_mem_of_mem {x : E K} (hx : mixedEmbedding.norm x ≠ 0) (hx' : x ∈ fundamentalCone K)
    (c : ℝ) : c • x ∈ fundamentalCone K := by
  by_cases hc : c = 0
  · rw [hc, zero_smul]
    exact fundamentalCone.zero_mem K
  · rwa [fundamentalCone, Set.mem_preimage, logMap_smul hx hc]

theorem exists_unitSMul_mem {x : E K} (hx : mixedEmbedding.norm x ≠ 0) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ fundamentalCone K := by
  classical
  let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ
  rsuffices ⟨⟨_, ⟨u, _, rfl⟩⟩, hu⟩ : ∃ e : unitLattice K, e + logMap x ∈ Zspan.fundamentalDomain B
  · exact ⟨u, by rwa [fundamentalCone, Set.mem_preimage, logMap_unitSMul u hx]⟩
  · obtain ⟨⟨e, h₁⟩, h₂, -⟩ := Zspan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)
    exact ⟨⟨e, by rwa [← Basis.ofZlatticeBasis_span ℝ (unitLattice K)]⟩, h₂⟩

theorem torsion_unitSMul_mem_of_mem {x : E K}
    (hx' : x ∈ fundamentalCone K) {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K) :
    ζ • x ∈ fundamentalCone K := by
  rwa [fundamentalCone, Set.mem_preimage, logMap_torsion_unitSMul _ hζ]

theorem unitSMul_mem_iff_mem_torsion {x : E K} (hx : mixedEmbedding.norm x ≠ 0)
    (hx' : x ∈ fundamentalCone K) (u : (𝓞 K)ˣ) :
    u • x ∈ fundamentalCone K ↔ u ∈ torsion K := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← logEmbedding_eq_zero_iff]
    let B := (Module.Free.chooseBasis ℤ (unitLattice K)).ofZlatticeBasis ℝ
    refine (Subtype.mk_eq_mk (h := ?_) (h' := ?_)).mp <|
      ExistsUnique.unique (Zspan.exist_unique_vadd_mem_fundamentalDomain B (logMap x)) ?_ ?_
    · change logEmbedding K u ∈ (Submodule.span ℤ (Set.range B)).toAddSubgroup
      rw [Basis.ofZlatticeBasis_span ℝ (unitLattice K)]
      exact ⟨u, trivial, rfl⟩
    · exact Submodule.zero_mem _
    · rwa [fundamentalCone, Set.mem_preimage, logMap_unitSMul _ hx] at h
    · rw [AddSubmonoid.mk_vadd, vadd_eq_add, zero_add]
      rwa [fundamentalCone, Set.mem_preimage] at hx'
  · exact torsion_unitSMul_mem_of_mem hx' h

variable (K) in
/-- The set of images by `mixedEmbedding` of algebraic integers of `K` contained in the
fundamental cone. -/
def integralPoint : Set (E K) := (fundamentalCone K) ∩ (mixedEmbedding K '' (𝓞 K))

theorem exists_unique_preimage_of_integralPoint {x : E K} (hx : x ∈ integralPoint K) :
    ∃! a : (𝓞 K), mixedEmbedding K a = x := by
  refine ⟨⟨hx.2.choose, hx.2.choose_spec.1⟩, hx.2.choose_spec.2, fun x h ↦ ?_⟩
  rw [Subtype.ext_iff, ← (mixedEmbedding_injective K).eq_iff, h, hx.2.choose_spec.2]

/-- For `a : fundamentalCone K`, the unique algebraic integer which image by `mixedEmbedding` is
equal to `a`. -/
def preimageOfIntegralPoint (a : integralPoint K) : (𝓞 K) :=
  ⟨a.prop.2.choose, a.prop.2.choose_spec.1⟩

@[simp]
theorem image_preimageOfIntegralPoint (a : integralPoint K) :
    mixedEmbedding K (preimageOfIntegralPoint a) = a := a.prop.2.choose_spec.2

theorem preimageOfIntegralPoint_mixedEmbedding {x : 𝓞 K}
    (hx : mixedEmbedding K x ∈ integralPoint K) :
    preimageOfIntegralPoint (⟨mixedEmbedding K x, hx⟩) = x := by
  rw [Subtype.ext_iff, ← (mixedEmbedding_injective K).eq_iff, image_preimageOfIntegralPoint]

theorem exists_unitSMul_mem_integralPoint {x : E K} (hx : x ∈ mixedEmbedding K '' (𝓞 K)) :
    ∃ u : (𝓞 K)ˣ, u • x ∈ integralPoint K := by
  by_cases hx' : x = 0
  · simp_rw [hx', smul_zero]
    exact ⟨1, fundamentalCone.zero_mem _, ⟨0, zero_mem _, map_zero _⟩⟩
  · replace hx' : mixedEmbedding.norm x ≠ 0 :=
      (norm_eq_zero_iff' (Set.mem_range_of_mem_image (mixedEmbedding K) _ hx)).not.mpr hx'
    obtain ⟨u, hu⟩ := exists_unitSMul_mem hx'
    obtain ⟨x, ⟨hx₁, ⟨_, rfl⟩⟩⟩ := hx
    refine ⟨u, hu, ?_⟩
    rw [unitSMul_smul, ← map_mul]
    exact ⟨u * x,  mul_mem (SetLike.coe_mem (u : 𝓞 K)) hx₁, rfl⟩

theorem torsion_unitSMul_mem_integralPoint {x : E K} {ζ : (𝓞 K)ˣ} (hζ : ζ ∈ torsion K)
    (hx : x ∈ integralPoint K) :
    ζ • x ∈ integralPoint K := by
  obtain ⟨a, ha, rfl⟩ := hx.2
  refine ⟨torsion_unitSMul_mem_of_mem hx.1 hζ, ⟨ζ * a, ?_, ?_⟩⟩
  · exact mul_mem (SetLike.coe_mem (ζ : (𝓞 K))) ha
  · rw [unitSMul_smul, map_mul]

variable (K) in
/-- The map that sends an element of `a : fundamentalCone K` to the associates class
of its preimage in `(𝓞 K)`. By quotienting by the kernel of the map, which is equal to the group of
roots of unity, we get the equivalence `integralPointQuotEquivAssociates`. -/
def integralPointToAssociates (a : integralPoint K) : Associates (𝓞 K) :=
  ⟦preimageOfIntegralPoint a⟧

@[simp]
theorem integralPointToAssociates_apply (a : integralPoint K) :
    integralPointToAssociates K a = ⟦preimageOfIntegralPoint a⟧ := rfl

variable (K) in
theorem integralPointToAssociates_surjective :
    Function.Surjective (integralPointToAssociates K) := by
  rintro ⟨x⟩
  obtain ⟨u, hu⟩ : ∃ u : (𝓞 K)ˣ, u • (mixedEmbedding K x) ∈ integralPoint K :=
      exists_unitSMul_mem_integralPoint ⟨x, SetLike.coe_mem x, rfl⟩
  refine ⟨⟨u • (mixedEmbedding K x), hu⟩, ?_⟩
  refine Quotient.sound ⟨u⁻¹, ?_⟩
  simp_rw [unitSMul_smul, ← map_mul, ← Submonoid.coe_mul]
  rw [preimageOfIntegralPoint_mixedEmbedding, mul_comm, Units.inv_mul_cancel_left]

@[simps]
instance integralPoint_torsionSMul: SMul (torsion K) (integralPoint K) where
  smul := fun ⟨ζ, hζ⟩ ⟨x, hx⟩ ↦ ⟨ζ • x, torsion_unitSMul_mem_integralPoint hζ hx⟩

instance : MulAction (torsion K) (integralPoint K) where
  one_smul := fun _ ↦ by
    rw [Subtype.mk_eq_mk, integralPoint_torsionSMul_smul_coe, OneMemClass.coe_one, one_smul]
  mul_smul := fun _ _ _ ↦ by
    rw [Subtype.mk_eq_mk]
    simp_rw [integralPoint_torsionSMul_smul_coe, Submonoid.coe_mul, mul_smul]

theorem integralPoint_torsionSMul_stabilizer {a : integralPoint K} (ha : (a : E K) ≠ 0) :
    MulAction.stabilizer (torsion K) a = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun ζ hζ ↦ ?_
  rwa [MulAction.mem_stabilizer_iff, Subtype.ext_iff, integralPoint_torsionSMul_smul_coe,
    unitSMul_smul, ← image_preimageOfIntegralPoint, ← map_mul, (mixedEmbedding_injective K).eq_iff,
    mul_eq_right₀, OneMemClass.coe_eq_one, Units.val_eq_one, OneMemClass.coe_eq_one] at hζ
  contrapose! ha
  rw [← image_preimageOfIntegralPoint, ha, map_zero]

theorem integralPointToAssociates_eq_iff (a b : integralPoint K) :
    integralPointToAssociates K a = integralPointToAssociates K b ↔
      ∃ ζ : torsion K, ζ • a = b := by
  rw [integralPointToAssociates_apply, integralPointToAssociates_apply]
  rw [show ⟦preimageOfIntegralPoint a⟧ = ⟦preimageOfIntegralPoint b⟧ ↔
    ∃ u : (𝓞 K)ˣ, preimageOfIntegralPoint a * u = preimageOfIntegralPoint b by
    rw [Associates.mk_eq_mk_iff_associated, Associated]]
  simp_rw [mul_comm, ← unitSMul_eq_iff_mul_eq, image_preimageOfIntegralPoint, Subtype.ext_iff,
    integralPoint_torsionSMul_smul_coe]
  refine ⟨fun ⟨u, h⟩ ↦ ?_, fun ⟨⟨ζ, _⟩, h⟩ ↦ ⟨ζ, h⟩⟩
  by_cases ha : (a : E K) = 0
  · simp_rw [ha, smul_zero] at h ⊢
    exact ⟨1, h⟩
  · have hnz : mixedEmbedding.norm (a : E K) ≠ 0 :=
      (norm_eq_zero_iff' ⟨a.prop.2.choose, a.prop.2.choose_spec.2⟩).not.mpr ha
    refine ⟨⟨u, (unitSMul_mem_iff_mem_torsion hnz a.prop.1 u).mp ?_⟩, h⟩
    rw [h]
    exact b.prop.1

variable (K) in
/-- The equivalence between `fundamentalCone.integralPoint K / torsion K` and `Associates K`. By
composing with the equivalence between `Associates K` and the principal ideals of `𝓞 K`, we get the
equivalence `integralPointQuotEquivIsPrincipal`. -/
def integralPointQuotEquivAssociates :
    Quotient (MulAction.orbitRel (torsion K) (integralPoint K)) ≃ Associates (𝓞 K) := by
  refine Equiv.ofBijective (Quotient.lift (integralPointToAssociates K)
    fun _ _ h ↦ ((integralPointToAssociates_eq_iff _ _).mpr h).symm)
    ⟨?_, (Quot.surjective_lift _).mpr (integralPointToAssociates_surjective K)⟩
  convert Setoid.ker_lift_injective (integralPointToAssociates K)
  all_goals
  · ext a b
    rw [Setoid.ker_def, eq_comm, integralPointToAssociates_eq_iff b a,
      MulAction.orbitRel_apply, MulAction.mem_orbit_iff]

@[simp]
theorem integralPointQuotEquivAssociates_apply (a : integralPoint K) :
    integralPointQuotEquivAssociates K ⟦a⟧ = ⟦preimageOfIntegralPoint a⟧ := rfl

variable (K) in
/-- The equivalence between `fundamentalCone.integralPoint K / torsion K` and the principal
ideals of `𝓞 K`. -/
def integralPointQuotEquivIsPrincipal :
    Quotient (MulAction.orbitRel (torsion K) (integralPoint K)) ≃
      {I : Ideal (𝓞 K) // Submodule.IsPrincipal I} :=
  (integralPointQuotEquivAssociates K).trans (Ideal.associatesEquivIsPrincipal (𝓞 K))

theorem integralPointQuotEquivIsPrincipal_apply (a : integralPoint K) :
    integralPointQuotEquivIsPrincipal K ⟦a⟧ = Ideal.span {preimageOfIntegralPoint a} := by
  rw [integralPointQuotEquivIsPrincipal, Equiv.trans_apply,
    integralPointQuotEquivAssociates_apply, Ideal.associatesEquivIsPrincipal_apply]

variable (K) in
/-- The norm `mixedEmbedding.norm` defined on `fundamentalCone.integralPoint K` lifts to a function
on the classes of `fundamentalCone.integralPoint K` modulo `torsion K`. -/
def integralPointQuotNorm :
    Quotient (MulAction.orbitRel (torsion K) (integralPoint K)) → ℝ := by
  refine Quotient.lift (fun x ↦ mixedEmbedding.norm (x : E K)) fun a b ⟨u, hu⟩ ↦ ?_
  simp_rw [← hu, integralPoint_torsionSMul_smul_coe, norm_unitSMul]

theorem integralPointQuotNorm_apply (a : integralPoint K) :
    integralPointQuotNorm K ⟦a⟧ = mixedEmbedding.norm (a : E K) := rfl

theorem integralPointQuotNorm_eq_norm (a : integralPoint K) :
    integralPointQuotNorm K ⟦a⟧ = |Algebra.norm ℤ (preimageOfIntegralPoint a)| := by
  rw [integralPointQuotNorm_apply, ← image_preimageOfIntegralPoint, norm_eq_norm,
    ← Algebra.coe_norm_int, Rat.cast_abs, Rat.cast_intCast, Int.cast_abs]

theorem integralPointQuotNorm_eq_zero_iff
    (q : Quotient (MulAction.orbitRel (torsion K) (integralPoint K))) :
    integralPointQuotNorm K q = 0 ↔ Quotient.out' q = (0 : E K) := by
  convert_to integralPointQuotNorm K ⟦Quotient.out' q⟧ = 0 ↔ Quotient.out' q = (0 : E K)
  · rw [← @Quotient.mk''_eq_mk, Quotient.out_eq']
  · rw [integralPointQuotNorm_apply, norm_eq_zero_iff' (by
      rw [← image_preimageOfIntegralPoint]
      exact Set.mem_range_self _)]

variable (K) in
/-- The equivalence between classes in `fundamentalCone.integralPoint K / torsion K` of norm `n`
and the principal ideals of `𝓞 K` of norm `n`. -/
def integralPointQuotNormEquivIsPrincipal (n : ℕ) :
    { x // integralPointQuotNorm K x = n } ≃
        { I : Ideal (𝓞 K) // Submodule.IsPrincipal I ∧ Ideal.absNorm I = n } := by
  refine Equiv.trans ?_ (Equiv.subtypeSubtypeEquivSubtypeInter _ _)
  refine Equiv.subtypeEquiv (integralPointQuotEquivIsPrincipal K) ?_
  rintro ⟨a⟩
  rw [show Quot.mk _ a = ⟦a⟧ by rfl, integralPointQuotEquivIsPrincipal_apply,
    integralPointQuotNorm_eq_norm, Ideal.absNorm_span_singleton, Int.abs_eq_natAbs,
    Int.cast_natCast, Nat.cast_inj]

/-- For `n` positive, the number of principal ideals in `𝓞 K` of norm `n` multiplied by the number
of roots of unity in `K` is equal to the number of `fundamentalCone.integralPoint K` of
norm `n`. -/
theorem card_isPrincipal_norm_mul {n : ℕ} (hn : 1 ≤ n) :
    Nat.card {I : Ideal (𝓞 K) // Submodule.IsPrincipal I ∧ Ideal.absNorm I = n} *
      Fintype.card (torsion K) =
        Nat.card ({a : integralPoint K // mixedEmbedding.norm (a : E K) = n}) := by
  rw [← Nat.card_congr (integralPointQuotNormEquivIsPrincipal K n), ← Nat.card_eq_fintype_card,
    ← Nat.card_prod]
  refine Nat.card_congr (Equiv.symm ?_)
  refine (Equiv.subtypeEquiv (q := fun s ↦ integralPointQuotNorm K s.fst = n)
    (MulAction.selfEquivSigmaOrbitsQuotientStabilizer (torsion K) (integralPoint K))
      fun _ ↦ ?_).trans  ?_
  · simp only [MulAction.selfEquivSigmaOrbitsQuotientStabilizer,
      MulAction.selfEquivSigmaOrbitsQuotientStabilizer', MulAction.selfEquivSigmaOrbits',
      Quotient.mk'_eq_mk, Equiv.instTransSortSortSortEquivEquivEquiv_trans, Equiv.trans_apply,
      Equiv.sigmaCongrRight_apply, Equiv.sigmaFiberEquiv_symm_apply_fst, Equiv.Set.ofEq_apply,
      integralPointQuotNorm_apply]
  · refine (@Equiv.subtypeSigmaEquiv _ _ (fun q ↦ integralPointQuotNorm K q = n)).trans
      (Equiv.sigmaEquivProdOfEquiv fun ⟨_, h⟩ ↦ ?_)
    rw [integralPoint_torsionSMul_stabilizer]
    exact QuotientGroup.quotientBot.toEquiv
    rw [ne_eq, ← integralPointQuotNorm_eq_zero_iff, h, Nat.cast_eq_zero, ← ne_eq]
    linarith

end fundamentalCone

end
