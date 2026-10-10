/-
Copyright (c) 2022 María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.Topology.Algebra.Valued.WithVal

/-!
# Completions of Dedekind domains with respect to adic valuations

Given a Dedekind domain `R` with field of fractions `K` and a maximal ideal `v` of `R`, we define
the completion of `K` with respect to its `v`-adic valuation, denoted `v.adicCompletion`, and its
ring of integers, denoted `v.adicCompletionIntegers`.

## Main definitions
- `IsDedekindDomain.HeightOneSpectrum.adicCompletion v` is the completion of `K` with respect
  to its `v`-adic valuation.
- `IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers v` is the ring of integers of
  `v.adicCompletion`.

## Tags
dedekind domain, dedekind ring, adic valuation, completion
-/

@[expose] public section

noncomputable section

open WithZero Multiplicative IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K S : Type*} [Field K] [CommSemiring S]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

namespace IsDedekindDomain.HeightOneSpectrum

/-- `K` as a valued field with the `v`-adic valuation. -/
@[instance_reducible]
def adicValued : Valued K ℤᵐ⁰ :=
  Valued.mk' (v.valuation K)

theorem adicValued_apply {x : K} : v.adicValued.v x = v.valuation K x :=
  rfl

variable (K)

/-- The completion of `K` with respect to its `v`-adic valuation, defined as a one-field structure
wrapping the uniform-space completion `(v.valuation K).Completion`. -/
structure adicCompletion where
  /-- Wrap an element of the underlying completion `(v.valuation K).Completion` into
  `adicCompletion`. -/
  ofCompletion ::
  /-- The underlying element of the completion `(v.valuation K).Completion`. -/
  toCompletion : (v.valuation K).Completion

section Notation

open Lean.PrettyPrinter.Delaborator

/-- Prevents `ofCompletion v x` being printed as `{ toCompletion := x }`
by `delabStructureInstance`. -/
@[app_delab adicCompletion.ofCompletion]
meta def adicCompletion.delabOfCompletion : Delab := delabApp

end Notation

namespace adicCompletion

open UniformSpace MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Filter Topology Valuation

/-- `adicCompletion.toCompletion` and `adicCompletion.ofCompletion` as an equivalence. -/
@[simps]
def equivCompletion : adicCompletion K v ≃ (v.valuation K).Completion where
  toFun := toCompletion
  invFun := ofCompletion
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Field (adicCompletion K v) := fast_instance% (equivCompletion K v).field

/-- `adicCompletion.toCompletion` as a ring isomorphism onto the underlying completion. -/
@[simps! apply]
def equiv : adicCompletion K v ≃+* (v.valuation K).Completion where
  toEquiv := equivCompletion K v
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp] lemma toCompletion_ofCompletion (x : (v.valuation K).Completion) :
    toCompletion (ofCompletion x : adicCompletion K v) = x := rfl
@[simp] lemma ofCompletion_toCompletion (x : adicCompletion K v) :
    ofCompletion x.toCompletion = x := rfl

@[simp] lemma toCompletion_zero : (0 : adicCompletion K v).toCompletion = 0 := rfl
@[simp] lemma toCompletion_one : (1 : adicCompletion K v).toCompletion = 1 := rfl
@[simp] lemma toCompletion_add (x y : adicCompletion K v) :
    (x + y).toCompletion = x.toCompletion + y.toCompletion := rfl
@[simp] lemma toCompletion_mul (x y : adicCompletion K v) :
    (x * y).toCompletion = x.toCompletion * y.toCompletion := rfl

theorem toCompletion_surjective : Function.Surjective (toCompletion (K := K) (v := v)) :=
  (equivCompletion K v).surjective

theorem ofCompletion_surjective : Function.Surjective (ofCompletion (K := K) (v := v)) :=
  (equivCompletion K v).symm.surjective

noncomputable instance : UniformSpace (adicCompletion K v) := .comap toCompletion inferInstance

theorem isUniformInducing_toCompletion :
    IsUniformInducing (toCompletion (K := K) (v := v)) := ⟨rfl⟩

instance : IsUniformAddGroup (adicCompletion K v) :=
  IsUniformInducing.isUniformAddGroup (equiv K v).toRingHom (isUniformInducing_toCompletion K v)

/-- The `v`-adic valuation on `adicCompletion K v`, transported from the completion along `equiv`.
-/
noncomputable def valuation : Valuation (adicCompletion K v) ℤᵐ⁰ :=
  (Valuation.extension (WithVal.valuation (v.valuation K))).comap (equiv K v).toRingHom

@[simp] theorem valuationExtension_toCompletion (x : adicCompletion K v) :
    Valuation.extension (WithVal.valuation (v.valuation K)) x.toCompletion =
      valuation K v x := rfl

@[simp] theorem valuation_ofCompletion (y : (v.valuation K).Completion) :
    valuation K v (ofCompletion y) = Valuation.extension (WithVal.valuation (v.valuation K)) y :=
  rfl

theorem valueGroup_eq :
    (valuation K v).valueGroup =
      (Valuation.extension (WithVal.valuation (v.valuation K))).valueGroup := by
  simp [valuation, valueGroup_def, valueMonoid_eq_closure,
    ← (toCompletion_surjective K v).range_comp, Valuation.comap]

/-- The value group `(valuation K v).valueGroup` of the canonical valuation on `v.adicCompletion K`
is equivalent multiplicatively to the value group of the valuation of `K` extended to
`v.adicCompletion K`. -/
def valueGroupMulEquiv :
    (valuation K v).valueGroup ≃*
      (Valuation.extension (WithVal.valuation (v.valuation K))).valueGroup where
  __ := Set.equivOfEq (by rw [valueGroup_eq K v])
  map_mul' _ _ := rfl

@[simp] theorem coe_valueGroupMulEquiv (a : (valuation K v).valueGroup) :
    (valueGroupMulEquiv K v a : ℤᵐ⁰ˣ) = a := rfl

/-- The value group with zero `(valuation K v).ValueGrou₀` of the canonical valuation on
`v.adicCompletion K` is multiplicatively order isomorphic to the value group with zero of the
valuation of `K` extended to `v.adicCompletion K`. -/
noncomputable def valueGroupOrderMonoidIso :
    (valuation K v).ValueGroup₀ ≃*o
      (Valuation.extension (WithVal.valuation (v.valuation K))).ValueGroup₀ where
  toFun := WithZero.map' (valueGroupMulEquiv K v)
  invFun := WithZero.map' (valueGroupMulEquiv K v).symm
  left_inv x := by match x with | 0 => simp | .coe a => simp
  right_inv y := by match y with | 0 => simp | .coe b => simp
  map_mul' := by simp
  map_le_map_iff' {a b} := by
    match a, b with
    | 0, 0 => simp
    | 0, .coe _ => simp
    | .coe _, 0 => simp
    | .coe a, .coe b => simp [← Subtype.coe_le_coe]

@[simp] theorem valueGroupOrderMonoidIso_coe (a : (valuation K v).valueGroup) :
    valueGroupOrderMonoidIso K v a = (valueGroupMulEquiv K v a : ValueGroup₀ _) := by
  simp [valueGroupOrderMonoidIso]

theorem embedding_valueGroupOrderMonoidIso (g : (valuation K v).ValueGroup₀) :
    embedding (valueGroupOrderMonoidIso K v g) = embedding g := by
  match g with
  | 0 => simp [valueGroupOrderMonoidIso]
  | .coe a => simp [valueGroupOrderMonoidIso_coe, embedding_apply, coe_valueGroupMulEquiv]

theorem valueGroupOrderMonoidIso_restrict (x : v.adicCompletion K) :
    valueGroupOrderMonoidIso K v ((valuation K v).restrict x) =
      (Valuation.extension (WithVal.valuation (v.valuation K))).restrict (toCompletion x) :=
  embedding_strictMono.injective (by simp [embedding_valueGroupOrderMonoidIso])

@[deprecated (since := "2026-09-28")] alias valueGroupEquiv := valueGroupMulEquiv
@[deprecated (since := "2026-09-28")] alias coe_valueGroupEquiv := coe_valueGroupMulEquiv
@[deprecated (since := "2026-09-28")] alias valueGroupOrderIso := valueGroupOrderMonoidIso
@[deprecated (since := "2026-09-28")]
  alias coe_valueGroupOrderIso_coe := valueGroupOrderMonoidIso_coe
@[deprecated (since := "2026-09-28")]
  alias embedding_valueGroupOrderIso := embedding_valueGroupOrderMonoidIso
@[deprecated (since := "2026-09-28")]
  alias valueGroupOrderIso_restrict := valueGroupOrderMonoidIso_restrict

instance : ValuativeRel (v.adicCompletion K) := .ofValuation (valuation K v)
instance : (valuation K v).Compatible := .ofValuation (valuation K v)

instance : IsValuativeTopology (v.adicCompletion K) := by
  refine .of_isInducing (equiv K v).surjective (isUniformInducing_toCompletion K v).isInducing
    fun a b ↦ ?_
  rw [vle_iff_le (valuation K v)]
  exact vle_iff_le _

noncomputable instance : Valued (adicCompletion K v) ℤᵐ⁰ where
  v := valuation K v
  is_topological_valuation s := (valuation K v).is_topological_valuation s

noncomputable instance : CompleteSpace (adicCompletion K v) :=
  ((isUniformInducing_toCompletion K v).completeSpace_congr (toCompletion_surjective K v)).mpr
    inferInstance

/-- Coercion of an element of `WithVal (v.valuation K)` into the adic completion. -/
instance : Coe (WithVal (v.valuation K)) (adicCompletion K v) where
  coe x := ofCompletion (x : (v.valuation K).Completion)

/-- Coercion of an element of `K` into the adic completion. -/
instance (priority := 99) : Coe K (adicCompletion K v) where
  coe k := ofCompletion (k : (v.valuation K).Completion)

@[simp] lemma coe_toCompletion (k : K) :
    (↑k : adicCompletion K v).toCompletion = (k : (v.valuation K).Completion) := rfl

theorem extension_apply_eq_valued (y : (v.valuation K).Completion) :
    (WithVal.valuation (v.valuation K)).extension y = Valued.v y := by
  rcases eq_or_ne y 0 with rfl | h
  · simp
  · obtain ⟨r, hr, hr'⟩ := (WithVal.valuation (v.valuation K)).exists_coe_mem_extension_eq
      (Valued.locally_const ((Valuation.ne_zero_iff _).2 h))
    rw [hr', ← hr, Valued.valuedCompletion_apply]
    rfl

theorem valuedAdicCompletion_apply {x : adicCompletion K v} :
    Valued.v x = Valued.extensionValuation x.toCompletion :=
  extension_apply_eq_valued K v x.toCompletion

@[simp] theorem valued_toCompletion_apply (x : adicCompletion K v) :
    Valued.v x.toCompletion = Valued.v x := (extension_apply_eq_valued K v x.toCompletion).symm

@[simp] theorem valued_ofCompletion_apply (y : (v.valuation K).Completion) :
    Valued.v (ofCompletion y : adicCompletion K v) = Valued.v y := extension_apply_eq_valued K v y

@[deprecated (since := "2026-09-28")] alias valuedAdicCompletion_def := valuedAdicCompletion_apply
@[deprecated (since := "2026-09-28")] alias valued_toCompletion := valued_toCompletion_apply
@[deprecated (since := "2026-09-28")] alias valued_ofCompletion := valued_ofCompletion_apply

theorem valued_coe (k : K) :
    Valued.v (↑k : adicCompletion K v) = v.valuation K k := by
  simp

@[ext] theorem ext {x y : adicCompletion K v} (h : x.toCompletion = y.toCompletion) : x = y := by
  cases x; cases y; exact congrArg ofCompletion h

@[norm_cast] lemma coe_zero : ((0 : K) : adicCompletion K v) = 0 := by
  apply adicCompletion.ext; simp
@[norm_cast] lemma coe_one : ((1 : K) : adicCompletion K v) = 1 := by
  apply adicCompletion.ext; simp
@[norm_cast] lemma coe_add (x y : K) :
    ((x + y : K) : adicCompletion K v) = ↑x + ↑y := by
  apply adicCompletion.ext; simp [UniformSpace.Completion.coe_add]
@[norm_cast] lemma coe_mul (x y : K) :
    ((x * y : K) : adicCompletion K v) = ↑x * ↑y := by
  apply adicCompletion.ext; simp [UniformSpace.Completion.coe_mul]

/-- `toCompletion` as a uniform-space isomorphism onto the underlying completion. -/
def uniformEquiv : adicCompletion K v ≃ᵤ (v.valuation K).Completion where
  toEquiv := equivCompletion K v
  uniformContinuous_toFun := uniformContinuous_comap
  uniformContinuous_invFun :=
    (isUniformInducing_toCompletion K v).uniformContinuous_iff.mpr uniformContinuous_id

theorem continuous_toCompletion : Continuous (toCompletion (K := K) (v := v)) :=
  (uniformEquiv K v).continuous

theorem continuous_ofCompletion : Continuous (ofCompletion (K := K) (v := v)) :=
  (uniformEquiv K v).symm.continuous

instance : T0Space (adicCompletion K v) :=
  (uniformEquiv K v).toHomeomorph.isEmbedding.t0Space

end adicCompletion

lemma valuedAdicCompletion_surjective :
    Function.Surjective (Valued.v : (v.adicCompletion K) → ℤᵐ⁰) := by
  have h : Function.Surjective (Valued.v : (v.valuation K).Completion → ℤᵐ⁰) :=
    Valued.valuedCompletion_surjective_iff.mpr <| .of_comp (v.valuation_surjective K)
  simpa [Function.comp_def] using h.comp (adicCompletion.toCompletion_surjective K v)

lemma adicCompletion_valueGroup_eq : (Valued.v (R := adicCompletion K v)).valueGroup  =
    (valuation K v).valueGroup := by
  ext n
  simp only [MonoidWithZeroHom.mem_valueGroup_iff_of_comm, Valuation.coe_toMonoidWithZeroHom, ne_eq]
  refine ⟨fun ⟨a, ha0, x, hx⟩ ↦ ?_, fun ⟨a, ha0, x, hx⟩ ↦
    ⟨a, by simpa using ha0, ↑x, by simpa using hx⟩⟩
  obtain ⟨b, hb⟩ := valuation_surjective K v (Valued.v a)
  obtain ⟨y, hy⟩ := valuation_surjective K v (Valued.v x)
  exact ⟨b, by rw [hb]; exact ha0, y, by rw [hb, hy]; exact hx⟩

/-- The ring of integers of `adicCompletion`. -/
def adicCompletionIntegers : ValuationSubring (v.adicCompletion K) :=
  Valued.v.valuationSubring

instance : Inhabited (adicCompletionIntegers K v) :=
  ⟨0⟩

variable (R)

theorem mem_adicCompletionIntegers {x : v.adicCompletion K} :
    x ∈ v.adicCompletionIntegers K ↔ Valued.v x ≤ 1 :=
  Iff.rfl

theorem notMem_adicCompletionIntegers {x : v.adicCompletion K} :
    x ∉ v.adicCompletionIntegers K ↔ 1 < Valued.v x := by
  rw [not_congr <| mem_adicCompletionIntegers R K v]
  exact not_le

section AlgebraInstances

instance (priority := 100) adicValued.has_uniform_continuous_const_smul' :
    UniformContinuousConstSMul R (WithVal <| v.valuation K) :=
  uniformContinuousConstSMul_of_continuousConstSMul R (WithVal <| v.valuation K)

section Algebra
variable [Algebra S K]

instance adicValued.uniformContinuousConstSMul :
    UniformContinuousConstSMul S (WithVal <| v.valuation K) := by
  refine ⟨fun l ↦ ?_⟩
  simp_rw [WithVal.smul_right_def, Algebra.smul_def]
  exact (Ring.uniformContinuousConstSMul (WithVal <| v.valuation K)).uniformContinuous_const_smul _

open UniformSpace in
/-- The `S`-algebra structure on the underlying completion. -/
noncomputable instance instAlgebraCompletion : Algebra S ((v.valuation K).Completion) where
  toSMul := Completion.instSMul _ _
  algebraMap := Completion.coeRingHom.comp (algebraMap S (WithVal (v.valuation K)))
  commutes' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_const_mul _) (continuous_mul_const _)
    | ih x => rw [mul_comm]
  smul_def' r x := by
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_eq (continuous_const_smul _) (continuous_const_mul _)
    | ih x =>
      simp [Algebra.smul_def, Completion.algebraMap_def, WithVal.algebraMap_right_apply,
        Completion.coeRingHom]

noncomputable instance : Algebra S (v.adicCompletion K) :=
  fast_instance% (adicCompletion.equivCompletion K v).algebra S

theorem algebraMap_adicCompletion_toCompletion (r : S) :
    (algebraMap S (v.adicCompletion K) r).toCompletion =
      algebraMap S ((v.valuation K).Completion) r := rfl

instance {S₀ : Type*} [CommSemiring S₀] [Algebra S₀ S] [Algebra S₀ K] [IsScalarTower S₀ S K] :
    IsScalarTower S₀ S ((v.valuation K).Completion) :=
  .of_algebraMap_eq fun x ↦ by
    exact congrArg (UniformSpace.Completion.coeRingHom (α := WithVal (v.valuation K)))
      (IsScalarTower.algebraMap_apply S₀ S (WithVal (v.valuation K)) x)

instance {S₀ : Type*} [CommSemiring S₀] [Algebra S₀ S] [Algebra S₀ K] [IsScalarTower S₀ S K] :
    IsScalarTower S₀ S (v.adicCompletion K) :=
  .of_algebraMap_eq fun x ↦ by
    apply adicCompletion.ext
    rw [algebraMap_adicCompletion_toCompletion, algebraMap_adicCompletion_toCompletion,
      IsScalarTower.algebraMap_apply S₀ S ((v.valuation K).Completion)]

theorem coe_smul_adicCompletion (r : S) (x : WithVal (v.valuation K)) :
    (↑(r • x) : v.adicCompletion K) = r • (↑x : v.adicCompletion K) := by
  apply adicCompletion.ext
  exact UniformSpace.Completion.coe_smul r x

theorem algebraMap_adicCompletion : ⇑(algebraMap S <| v.adicCompletion K) = (↑) ∘ algebraMap S K :=
  rfl

variable {R} in
theorem denseRange_algebraMap : DenseRange (algebraMap K (v.adicCompletion K)) := by
  rw [algebraMap_adicCompletion]
  exact (adicCompletion.ofCompletion_surjective K v).denseRange.comp
    (UniformSpace.Completion.denseRange_coe.comp (WithVal.equiv _).symm.surjective.denseRange
      (UniformSpace.Completion.continuous_coe _))
    (adicCompletion.continuous_ofCompletion K v)

end Algebra

theorem coe_algebraMap_mem (r : R) : ↑((algebraMap R K) r) ∈ adicCompletionIntegers K v := by
  rw [mem_adicCompletionIntegers, ← adicCompletion.valued_toCompletion_apply,
    adicCompletion.coe_toCompletion, Valued.valuedCompletion_apply]
  simpa using v.valuation_le_one _

instance : Algebra R (v.adicCompletionIntegers K) where
  smul r x :=
    ⟨r • (x : v.adicCompletion K), by
      rw [Algebra.smul_def]
      refine ValuationSubring.mul_mem _ _ _ ?_ x.2
      rw [algebraMap_adicCompletion]
      exact coe_algebraMap_mem _ _ v r⟩
  algebraMap :=
  { toFun r :=
      ⟨(algebraMap R K r : adicCompletion K v), coe_algebraMap_mem _ _ v r⟩
    map_one' := by ext; simp
    map_mul' x y := by
      ext
      simp [map_mul, UniformSpace.Completion.coe_mul]
    map_zero' := by ext; simp
    map_add' x y := by
      ext
      simp [map_add, UniformSpace.Completion.coe_add] }
  commutes' r x := by
    rw [mul_comm]
  smul_def' r x := by
    ext
    simp +instances only [Algebra.smul_def]
    rfl

@[simp]
lemma algebraMap_adicCompletionIntegers_apply (r : R) :
    algebraMap R (v.adicCompletionIntegers K) r = (algebraMap R K r : v.adicCompletion K) := by
  rfl

instance [FaithfulSMul R K] : FaithfulSMul R (v.adicCompletionIntegers K) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y
  rw [Subtype.ext_iff]
  simp

variable {R K} in
open scoped algebraMap in -- to make the coercions from `R` fire
/-- The valuation on the completion agrees with the global valuation on elements of the
integer ring. -/
theorem valuedAdicCompletion_eq_valuation (r : R) :
    Valued.v (r : v.adicCompletion K) = v.valuation K r := by
  rw [← adicCompletion.valued_toCompletion_apply]
  exact Valued.valuedCompletion_apply _

variable {R K} in
/-- The valuation on the completion agrees with the global valuation on elements of the field. -/
theorem valuedAdicCompletion_eq_valuation' (k : K) :
    Valued.v (k : v.adicCompletion K) = v.valuation K k := by
  rw [← adicCompletion.valued_toCompletion_apply]
  exact Valued.valuedCompletion_apply _

variable {R K} in
open scoped algebraMap in -- to make the coercion from `R` fire
/-- A global integer is in the local integers. -/
lemma coe_mem_adicCompletionIntegers (r : R) :
    (r : adicCompletion K v) ∈ adicCompletionIntegers K v := by
  rw [mem_adicCompletionIntegers, valuedAdicCompletion_eq_valuation]
  exact valuation_le_one v r

@[simp]
theorem coe_smul_adicCompletionIntegers (r : R) (x : v.adicCompletionIntegers K) :
    (↑(r • x) : v.adicCompletion K) = r • (x : v.adicCompletion K) :=
  rfl

instance : Module.IsTorsionFree R (v.adicCompletionIntegers K) := .of_smul_eq_zero <| by simp

instance adicCompletion.instIsScalarTower' :
    IsScalarTower R (v.adicCompletionIntegers K) (v.adicCompletion K) where
  smul_assoc x y z := by simp only [Algebra.smul_def]; apply mul_assoc

end AlgebraInstances

variable {R}

open nonZeroDivisors algebraMap in
variable {K} in
lemma adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers (v : HeightOneSpectrum R)
    (a : v.adicCompletion K) : ∃ b ∈ R⁰, a * b ∈ v.adicCompletionIntegers K := by
  by_cases ha : a ∈ v.adicCompletionIntegers K
  · use 1
    simp [ha]
  · rw [notMem_adicCompletionIntegers] at ha
    -- let ϖ be a uniformiser
    obtain ⟨ϖ, hϖ⟩ := intValuation_exists_uniformizer v
    have : Valued.v (algebraMap R (v.adicCompletion K) ϖ) = (exp (1 : ℤ))⁻¹ := by
      simp [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap, hϖ, exp]
    have hϖ0 : ϖ ≠ 0 := by rintro rfl; simp [exp_ne_zero.symm] at hϖ
    refine ⟨ϖ^(log (Valued.v a)).natAbs, pow_mem (mem_nonZeroDivisors_of_ne_zero hϖ0) _, ?_⟩
    -- now manually translate the goal (an inequality in ℤᵐ⁰) to an inequality of "log" of ℤ
    simp only [map_pow, mem_adicCompletionIntegers, map_mul, this, inv_pow, ← exp_nsmul, nsmul_one,
      Int.natCast_natAbs]
    exact mul_inv_le_one_of_le₀ (le_exp_log.trans (by simp [le_abs_self])) zero_le

instance : FaithfulSMul (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  Subsemiring.faithfulSMul _

theorem adicCompletionIntegers.integers :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Integers ↥(adicCompletionIntegers K v) where
  hom_inj := FaithfulSMul.algebraMap_injective _ _
  map_le_one := by simp [mem_adicCompletionIntegers]
  exists_of_le_one := by simp [mem_adicCompletionIntegers]

variable {K v}

theorem adicCompletionIntegers.isUnit_iff_valued_eq_one {a : v.adicCompletionIntegers K} :
    IsUnit a ↔ Valued.v a.1 = 1 := by
  simp [Valuation.Integers.isUnit_iff_valuation_eq_one (integers K v)]

theorem adicCompletionIntegers.mem_units_iff_valued_eq_one {a : (v.adicCompletion K)ˣ} :
    a ∈ (v.adicCompletionIntegers K).units ↔ Valued.v a.1 = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦
     ⟨h.le, by simp [mem_adicCompletionIntegers, inv_le_one_iff₀, h.symm.le]⟩⟩
  convert! isUnit_iff_valued_eq_one.1 (Submonoid.unitsEquivIsUnitSubmonoid _ ⟨_, h⟩).2

end IsDedekindDomain.HeightOneSpectrum
