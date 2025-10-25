/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.Lie.InvariantForm
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.Algebra.Lie.Weights.Linear
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.PID

/-!
# The trace and Killing forms of a Lie algebra.

Let `L` be a Lie algebra with coefficients in a commutative ring `R`. Suppose `M` is a finite, free
`R`-module and we have a representation `φ : L → End M`. This data induces a natural bilinear form
`B` on `L`, called the trace form associated to `M`; it is defined as `B(x, y) = Tr (φ x) (φ y)`.

In the special case that `M` is `L` itself and `φ` is the adjoint representation, the trace form
is known as the Killing form.

We define the trace / Killing form in this file and prove some basic properties.

## Main definitions

* `LieModule.traceForm`: a finite, free representation of a Lie algebra `L` induces a bilinear form
  on `L` called the trace form.
* `LieModule.traceForm_eq_zero_of_isNilpotent`: the trace form induced by a nilpotent
  representation of a Lie algebra vanishes.
* `killingForm`: the adjoint representation of a (finite, free) Lie algebra `L` induces a bilinear
  form on `L` via the trace form construction.
-/

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "φ" => LieModule.toEnd R L M

open LinearMap (trace)
open Set Module

namespace LieModule

/-- A finite, free representation of a Lie algebra `L` induces a bilinear form on `L` called
the trace form. See also `killingForm`. -/
noncomputable def traceForm : LinearMap.BilinForm R L :=
  ((LinearMap.mul _ _).compl₁₂ (φ).toLinearMap (φ).toLinearMap).compr₂ (trace R M)

lemma traceForm_apply_apply (x y : L) :
    traceForm R L M x y = trace R _ (φ x ∘ₗ φ y) :=
  rfl

lemma traceForm_comm (x y : L) : traceForm R L M x y = traceForm R L M y x :=
  LinearMap.trace_mul_comm R (φ x) (φ y)

lemma traceForm_isSymm : LinearMap.IsSymm (traceForm R L M) := ⟨LieModule.traceForm_comm R L M⟩

@[simp] lemma traceForm_flip : LinearMap.flip (traceForm R L M) = traceForm R L M :=
  Eq.symm <| LinearMap.ext₂ <| traceForm_comm R L M

/-- The trace form of a Lie module is compatible with the action of the Lie algebra.

See also `LieModule.traceForm_apply_lie_apply'`. -/
lemma traceForm_apply_lie_apply (x y z : L) :
    traceForm R L M ⁅x, y⁆ z = traceForm R L M x ⁅y, z⁆ := by
  calc traceForm R L M ⁅x, y⁆ z
      = trace R _ (φ ⁅x, y⁆ ∘ₗ φ z) := by simp only [traceForm_apply_apply]
    _ = trace R _ ((φ x * φ y - φ y * φ x) * φ z) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ y * (φ x * φ z)) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ x * (φ z * φ y)) := ?_
    _ = traceForm R L M x ⁅y, z⁆ := ?_
  · simp only [LieHom.map_lie, Ring.lie_def, ← Module.End.mul_eq_comp]
  · simp only [sub_mul, map_sub, mul_assoc]
  · simp only [LinearMap.trace_mul_cycle' R (φ x) (φ z) (φ y)]
  · simp only [traceForm_apply_apply, LieHom.map_lie, Ring.lie_def, mul_sub, map_sub,
      ← Module.End.mul_eq_comp]

/-- Given a representation `M` of a Lie algebra `L`, the action of any `x : L` is skew-adjoint
w.r.t. the trace form. -/
lemma traceForm_apply_lie_apply' (x y z : L) :
    traceForm R L M ⁅x, y⁆ z = - traceForm R L M y ⁅x, z⁆ :=
  calc traceForm R L M ⁅x, y⁆ z
      = - traceForm R L M ⁅y, x⁆ z := by rw [← lie_skew x y, map_neg, LinearMap.neg_apply]
    _ = - traceForm R L M y ⁅x, z⁆ := by rw [traceForm_apply_lie_apply]

lemma traceForm_lieInvariant : (traceForm R L M).lieInvariant L := by
  intro x y z
  rw [← lie_skew, map_neg, LinearMap.neg_apply, LieModule.traceForm_apply_lie_apply R L M]

/-- This lemma justifies the terminology "invariant" for trace forms. -/
@[simp] lemma lie_traceForm_eq_zero (x : L) : ⁅x, traceForm R L M⁆ = 0 := by
  ext y z
  rw [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply, LinearMap.zero_apply,
    LinearMap.zero_apply, traceForm_apply_lie_apply', sub_self]

@[simp] lemma traceForm_eq_zero_of_isNilpotent [IsReduced R] [IsNilpotent L M] :
    traceForm R L M = 0 := by
  ext x y
  simp only [traceForm_apply_apply, LinearMap.zero_apply, ← isNilpotent_iff_eq_zero]
  apply LinearMap.isNilpotent_trace_of_isNilpotent
  exact isNilpotent_toEnd_of_isNilpotent₂ R L M x y

@[simp]
lemma traceForm_genWeightSpace_eq [Module.Free R M]
    [IsDomain R] [IsPrincipalIdealRing R]
    [LieRing.IsNilpotent L] [IsNoetherian R M] [LinearWeights R L M] (χ : L → R) (x y : L) :
    traceForm R L (genWeightSpace M χ) x y = finrank R (genWeightSpace M χ) • (χ x * χ y) := by
  set d := finrank R (genWeightSpace M χ)
  have h₁ : χ y • d • χ x - χ y • χ x • (d : R) = 0 := by simp [mul_comm (χ x)]
  have h₂ : χ x • d • χ y = d • (χ x * χ y) := by
    simpa [nsmul_eq_mul, smul_eq_mul] using mul_left_comm (χ x) d (χ y)
  have := traceForm_eq_zero_of_isNilpotent R L (shiftedGenWeightSpace R L M χ)
  replace this := LinearMap.congr_fun (LinearMap.congr_fun this x) y
  rwa [LinearMap.zero_apply, LinearMap.zero_apply, traceForm_apply_apply,
    shiftedGenWeightSpace.toEnd_eq, shiftedGenWeightSpace.toEnd_eq,
    ← LinearEquiv.conj_comp, LinearMap.trace_conj', LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.sub_comp, map_sub, map_sub, map_sub, LinearMap.comp_smul, LinearMap.smul_comp,
    LinearMap.comp_id, LinearMap.id_comp, LinearMap.map_smul, LinearMap.map_smul,
    trace_toEnd_genWeightSpace, trace_toEnd_genWeightSpace,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.id_comp, map_smul, map_smul,
    LinearMap.trace_id, ← traceForm_apply_apply, h₁, h₂, sub_zero, sub_eq_zero] at this

/-- The upper and lower central series of `L` are orthogonal w.r.t. the trace form of any Lie module
`M`. -/
lemma traceForm_eq_zero_if_mem_lcs_of_mem_ucs {x y : L} (k : ℕ)
    (hx : x ∈ (⊤ : LieIdeal R L).lcs L k) (hy : y ∈ (⊥ : LieIdeal R L).ucs k) :
    traceForm R L M x y = 0 := by
  induction k generalizing x y with
  | zero =>
    replace hy : y = 0 := by simpa using hy
    simp [hy]
  | succ k ih =>
    rw [LieSubmodule.ucs_succ, LieSubmodule.mem_normalizer] at hy
    simp_rw [LieIdeal.lcs_succ, ← LieSubmodule.mem_toSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span', LieSubmodule.mem_top, true_and] at hx
    refine Submodule.span_induction ?_ ?_ (fun z w _ _ hz hw ↦ ?_) (fun t z _ hz ↦ ?_) hx
    · rintro - ⟨z, w, hw, rfl⟩
      rw [← lie_skew, map_neg, LinearMap.neg_apply, neg_eq_zero, traceForm_apply_lie_apply]
      exact ih hw (hy _)
    · simp
    · simp [hz, hw]
    · simp [hz]

lemma traceForm_apply_eq_zero_of_mem_lcs_of_mem_center {x y : L}
    (hx : x ∈ lowerCentralSeries R L L 1) (hy : y ∈ LieAlgebra.center R L) :
    traceForm R L M x y = 0 := by
  apply traceForm_eq_zero_if_mem_lcs_of_mem_ucs R L M 1
  · simpa using hx
  · simpa using hy

-- This is barely worth having: it usually follows from `LieModule.traceForm_eq_zero_of_isNilpotent`
@[simp] lemma traceForm_eq_zero_of_isTrivial [IsTrivial L M] :
    traceForm R L M = 0 := by
  ext x y
  suffices φ x ∘ₗ φ y = 0 by simp [traceForm_apply_apply, this]
  ext m
  simp

/-- Given a bilinear form `B` on a representation `M` of a nilpotent Lie algebra `L`, if `B` is
invariant (in the sense that the action of `L` is skew-adjoint w.r.t. `B`) then components of the
Fitting decomposition of `M` are orthogonal w.r.t. `B`. -/
lemma eq_zero_of_mem_genWeightSpace_mem_posFitting [LieRing.IsNilpotent L]
    {B : LinearMap.BilinForm R M} (hB : ∀ (x : L) (m n : M), B ⁅x, m⁆ n = -B m ⁅x, n⁆)
    {m₀ m₁ : M} (hm₀ : m₀ ∈ genWeightSpace M (0 : L → R)) (hm₁ : m₁ ∈ posFittingComp R L M) :
    B m₀ m₁ = 0 := by
  replace hB : ∀ x (k : ℕ) m n, B m ((φ x ^ k) n) = (- 1 : R) ^ k • B ((φ x ^ k) m) n := by
    intro x k
    induction k with
    | zero => simp
    | succ k ih =>
    intro m n
    replace hB : ∀ m, B m (φ x n) = (- 1 : R) • B (φ x m) n := by simp [hB]
    have : (-1 : R) ^ k • (-1 : R) = (-1 : R) ^ (k + 1) := by rw [pow_succ (-1 : R), smul_eq_mul]
    conv_lhs => rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply, ih, hB,
      ← (φ x).comp_apply, ← Module.End.mul_eq_comp, ← pow_succ', ← smul_assoc, this]
  suffices ∀ (x : L) m, m ∈ posFittingCompOf R M x → B m₀ m = 0 by
    refine LieSubmodule.iSup_induction (motive := fun m ↦ (B m₀) m = 0) _ hm₁ this (map_zero _) ?_
    simp_all
  clear hm₁ m₁; intro x m₁ hm₁
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm₀
  obtain ⟨k, hk⟩ := hm₀ x
  obtain ⟨m, rfl⟩ := (mem_posFittingCompOf R x m₁).mp hm₁ k
  simp [hB, hk]

lemma trace_toEnd_eq_zero_of_mem_lcs
    {k : ℕ} {x : L} (hk : 1 ≤ k) (hx : x ∈ lowerCentralSeries R L L k) :
    trace R _ (toEnd R L M x) = 0 := by
  replace hx : x ∈ lowerCentralSeries R L L 1 := antitone_lowerCentralSeries _ _ _ hk hx
  replace hx : x ∈ Submodule.span R {m | ∃ u v : L, ⁅u, v⁆ = m} := by
    rw [lowerCentralSeries_succ, ← LieSubmodule.mem_toSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
    simpa using hx
  refine Submodule.span_induction (p := fun x _ ↦ trace R _ (toEnd R L M x) = 0)
    ?_ ?_ (fun u v _ _ hu hv ↦ ?_) (fun t u _ hu ↦ ?_) hx
  · intro y ⟨u, v, huv⟩
    simp [← huv]
  · simp
  · simp [hu, hv]
  · simp [hu]

@[simp]
lemma traceForm_lieSubalgebra_mk_left (L' : LieSubalgebra R L) {x : L} (hx : x ∈ L') (y : L') :
    traceForm R L' M ⟨x, hx⟩ y = traceForm R L M x y :=
  rfl

@[simp]
lemma traceForm_lieSubalgebra_mk_right (L' : LieSubalgebra R L) {x : L'} {y : L} (hy : y ∈ L') :
    traceForm R L' M x ⟨y, hy⟩ = traceForm R L M x y :=
  rfl

open TensorProduct

variable [LieRing.IsNilpotent L] [IsDomain R] [IsPrincipalIdealRing R]

lemma traceForm_eq_sum_genWeightSpaceOf
    [NoZeroSMulDivisors R M] [IsNoetherian R M] [IsTriangularizable R L M] (z : L) :
    traceForm R L M =
    ∑ χ ∈ (finite_genWeightSpaceOf_ne_bot R L M z).toFinset,
      traceForm R L (genWeightSpaceOf M χ z) := by
  ext x y
  have hxy : ∀ χ : R, MapsTo ((toEnd R L M x).comp (toEnd R L M y))
      (genWeightSpaceOf M χ z) (genWeightSpaceOf M χ z) :=
    fun χ m hm ↦ LieSubmodule.lie_mem _ <| LieSubmodule.lie_mem _ hm
  have hfin : {χ : R | (genWeightSpaceOf M χ z : Submodule R M) ≠ ⊥}.Finite := by
    convert finite_genWeightSpaceOf_ne_bot R L M z
    exact LieSubmodule.toSubmodule_eq_bot (genWeightSpaceOf M _ _)
  classical
  have h := LieSubmodule.iSupIndep_toSubmodule.mpr <| iSupIndep_genWeightSpaceOf R L M z
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h <| by
    simp [← LieSubmodule.iSup_toSubmodule]
  simp only [LinearMap.coeFn_sum, Finset.sum_apply, traceForm_apply_apply,
    LinearMap.trace_eq_sum_trace_restrict' hds hfin hxy]
  exact Finset.sum_congr (by simp) (fun χ _ ↦ rfl)

-- In characteristic zero (or even just `LinearWeights R L M`) a stronger result holds (no
-- `⊓ LieAlgebra.center R L`) TODO prove this using `LieModule.traceForm_eq_sum_finrank_nsmul_mul`.
lemma lowerCentralSeries_one_inf_center_le_ker_traceForm [Module.Free R M] [Module.Finite R M] :
    lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L ≤ LinearMap.ker (traceForm R L M) := by
  /- Sketch of proof (due to Zassenhaus):

  Let `z ∈ lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L` and `x : L`. We must show that
  `trace (φ x ∘ φ z) = 0` where `φ z : End R M` indicates the action of `z` on `M` (and likewise
  for `φ x`).

  Because `z` belongs to the indicated intersection, it has two key properties:
  (a) the trace of the action of `z` vanishes on any Lie module of `L`
      (see `LieModule.trace_toEnd_eq_zero_of_mem_lcs`),
  (b) `z` commutes with all elements of `L`.

  If `φ x` were triangularizable, we could write `M` as a direct sum of generalized eigenspaces of
  `φ x`. Because `L` is nilpotent these are all Lie submodules, thus Lie modules in their own right,
  and thus by (a) above we learn that `trace (φ z) = 0` restricted to each generalized eigenspace.
  Because `z` commutes with `x`, this forces `trace (φ x ∘ φ z) = 0` on each generalized eigenspace,
  and so by summing the traces on each generalized eigenspace we learn the total trace is zero, as
  required (see `LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero`).

  To cater for the fact that `φ x` may not be triangularizable, we first extend the scalars from `R`
  to `AlgebraicClosure (FractionRing R)` and argue using the action of `A ⊗ L` on `A ⊗ M`. -/
  rintro z ⟨hz : z ∈ lowerCentralSeries R L L 1, hzc : z ∈ LieAlgebra.center R L⟩
  ext x
  rw [traceForm_apply_apply, LinearMap.zero_apply]
  let A := AlgebraicClosure (FractionRing R)
  suffices algebraMap R A (trace R _ ((φ z).comp (φ x))) = 0 by
    have _i : NoZeroSMulDivisors R A := NoZeroSMulDivisors.trans_faithfulSMul R (FractionRing R) A
    rw [← map_zero (algebraMap R A)] at this
    exact FaithfulSMul.algebraMap_injective R A this
  rw [← LinearMap.trace_baseChange, LinearMap.baseChange_comp, ← toEnd_baseChange,
    ← toEnd_baseChange]
  replace hz : 1 ⊗ₜ z ∈ lowerCentralSeries A (A ⊗[R] L) (A ⊗[R] L) 1 := by
    simp only [lowerCentralSeries_succ, lowerCentralSeries_zero] at hz ⊢
    rw [← LieSubmodule.baseChange_top, ← LieSubmodule.lie_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hz
  replace hzc : 1 ⊗ₜ[R] z ∈ LieAlgebra.center A (A ⊗[R] L) := by
    simp only [mem_maxTrivSubmodule] at hzc ⊢
    intro y
    exact y.induction_on rfl (fun a u ↦ by simp [hzc u])
      (fun u v hu hv ↦ by simp [A, hu, hv])
  apply LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero
  · exact IsTriangularizable.maxGenEigenspace_eq_top (1 ⊗ₜ[R] x)
  · exact fun μ ↦ trace_toEnd_eq_zero_of_mem_lcs A (A ⊗[R] L)
      (genWeightSpaceOf (A ⊗[R] M) μ ((1:A) ⊗ₜ[R] x)) (le_refl 1) hz
  · exact commute_toEnd_of_mem_center_right (A ⊗[R] M) hzc (1 ⊗ₜ x)

/-- A nilpotent Lie algebra with a representation whose trace form is non-singular is Abelian. -/
lemma isLieAbelian_of_ker_traceForm_eq_bot [Module.Free R M] [Module.Finite R M]
    (h : LinearMap.ker (traceForm R L M) = ⊥) : IsLieAbelian L := by
  simpa only [← disjoint_lowerCentralSeries_maxTrivSubmodule_iff R L L, disjoint_iff_inf_le,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.toSubmodule_eq_bot, h]
    using lowerCentralSeries_one_inf_center_le_ker_traceForm R L M

end LieModule

namespace LieSubmodule

open LieModule (traceForm)

variable {R L M}
variable [Module.Free R M] [Module.Finite R M]
variable [IsDomain R] [IsPrincipalIdealRing R]
  (N : LieSubmodule R L M) (I : LieIdeal R L) (h : I ≤ N.idealizer) (x : L) {y : L} (hy : y ∈ I)

lemma trace_eq_trace_restrict_of_le_idealizer
    (hy' : ∀ m ∈ N, (φ x ∘ₗ φ y) m ∈ N := fun m _ ↦ N.lie_mem (N.mem_idealizer.mp (h hy) m)) :
    trace R M (φ x ∘ₗ φ y) = trace R N ((φ x ∘ₗ φ y).restrict hy') := by
  suffices ∀ m, ⁅x, ⁅y, m⁆⁆ ∈ N by
    have : (trace R { x // x ∈ N }) ((φ x ∘ₗ φ y).restrict _) = (trace R M) (φ x ∘ₗ φ y) :=
      (φ x ∘ₗ φ y).trace_restrict_eq_of_forall_mem _ this
    simp [this]
  exact fun m ↦ N.lie_mem (h hy m)

include h in
lemma traceForm_eq_of_le_idealizer :
    traceForm R I N = (traceForm R L M).restrict I := by
  ext ⟨x, hx⟩ ⟨y, hy⟩
  change _ = trace R M (φ x ∘ₗ φ y)
  rw [N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  rfl

include h hy in
/-- Note that this result is slightly stronger than it might look at first glance: we only assume
that `N` is trivial over `I` rather than all of `L`. This means that it applies in the important
case of an Abelian ideal (which has `M = L` and `N = I`). -/
lemma traceForm_eq_zero_of_isTrivial [LieModule.IsTrivial I N] :
    trace R M (φ x ∘ₗ φ y) = 0 := by
  let hy' : ∀ m ∈ N, (φ x ∘ₗ φ y) m ∈ N := fun m _ ↦ N.lie_mem (N.mem_idealizer.mp (h hy) m)
  suffices (φ x ∘ₗ φ y).restrict hy' = 0 by
    simp [this, N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  ext (n : N)
  suffices ⁅y, (n : M)⁆ = 0 by simp [this]
  exact Submodule.coe_eq_zero.mpr (LieModule.IsTrivial.trivial (⟨y, hy⟩ : I) n)

end LieSubmodule

section LieAlgebra

/-- A finite, free (as an `R`-module) Lie algebra `L` carries a bilinear form on `L`.

This is a specialisation of `LieModule.traceForm` to the adjoint representation of `L`. -/
noncomputable abbrev killingForm : LinearMap.BilinForm R L := LieModule.traceForm R L L

open LieAlgebra in
lemma killingForm_apply_apply (x y : L) : killingForm R L x y = trace R L (ad R L x ∘ₗ ad R L y) :=
  LieModule.traceForm_apply_apply R L L x y

lemma killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting
    (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
    {x₀ x₁ : L}
    (hx₀ : x₀ ∈ LieAlgebra.zeroRootSubalgebra R L H)
    (hx₁ : x₁ ∈ LieModule.posFittingComp R H L) :
    killingForm R L x₀ x₁ = 0 :=
  LieModule.eq_zero_of_mem_genWeightSpace_mem_posFitting R H L
    (fun x y z ↦ LieModule.traceForm_apply_lie_apply' R L L x y z) hx₀ hx₁

namespace LieIdeal

variable (I : LieIdeal R L)

/-- The orthogonal complement of an ideal with respect to the killing form is an ideal. -/
noncomputable def killingCompl : LieIdeal R L :=
  LieAlgebra.InvariantForm.orthogonal (killingForm R L) (LieModule.traceForm_lieInvariant R L L) I

@[simp] lemma toSubmodule_killingCompl :
    LieSubmodule.toSubmodule I.killingCompl = (killingForm R L).orthogonal I.toSubmodule :=
  rfl

@[simp] lemma mem_killingCompl {x : L} :
    x ∈ I.killingCompl ↔ ∀ y ∈ I, killingForm R L y x = 0 := by
  rfl

lemma coe_killingCompl_top :
    killingCompl R L ⊤ = LinearMap.ker (killingForm R L) := by
  ext x
  simp [LinearMap.ext_iff, LinearMap.BilinForm.IsOrtho, LieModule.traceForm_comm R L L x]

lemma restrict_killingForm :
    (killingForm R L).restrict I = LieModule.traceForm R I L :=
  rfl

variable [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R]

lemma killingForm_eq :
    killingForm R I = (killingForm R L).restrict I :=
  LieSubmodule.traceForm_eq_of_le_idealizer I I <| by simp

@[simp] lemma le_killingCompl_top_of_isLieAbelian [IsLieAbelian I] :
    I ≤ LieIdeal.killingCompl R L ⊤ := by
  intro x (hx : x ∈ I)
  simp only [mem_killingCompl, LieSubmodule.mem_top, forall_true_left]
  intro y
  rw [LieModule.traceForm_apply_apply]
  exact LieSubmodule.traceForm_eq_zero_of_isTrivial I I (by simp) _ hx

end LieIdeal

open LieModule Module
open Submodule (span subset_span)

namespace LieModule

variable [Field K] [LieAlgebra K L] [Module K M] [LieModule K L M] [FiniteDimensional K M]
variable [LieRing.IsNilpotent L] [LinearWeights K L M] [IsTriangularizable K L M]

lemma traceForm_eq_sum_finrank_nsmul_mul (x y : L) :
    traceForm K L M x y = ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) • (χ x * χ y) := by
  have hxy : ∀ χ : Weight K L M, MapsTo (toEnd K L M x ∘ₗ toEnd K L M y)
      (genWeightSpace M χ) (genWeightSpace M χ) :=
    fun χ m hm ↦ LieSubmodule.lie_mem _ <| LieSubmodule.lie_mem _ hm
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr <| iSupIndep_genWeightSpace' K L M)
    (LieSubmodule.iSup_toSubmodule_eq_top.mpr <| iSup_genWeightSpace_eq_top' K L M)
  simp_rw [traceForm_apply_apply, LinearMap.trace_eq_sum_trace_restrict hds hxy,
    ← traceForm_genWeightSpace_eq K L M _ x y]
  rfl

/-- See also `LieModule.traceForm_eq_sum_finrank_nsmul'` for an expression omitting the zero
weights. -/
lemma traceForm_eq_sum_finrank_nsmul :
    traceForm K L M = ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) •
      (χ : L →ₗ[K] K).smulRight (χ : L →ₗ[K] K) := by
  ext
  rw [traceForm_eq_sum_finrank_nsmul_mul, ← Finset.sum_attach]
  simp

/-- A variant of `LieModule.traceForm_eq_sum_finrank_nsmul` in which the sum is taken only over the
non-zero weights. -/
lemma traceForm_eq_sum_finrank_nsmul' :
    traceForm K L M = ∑ χ ∈ {χ : Weight K L M | χ.IsNonZero}, finrank K (genWeightSpace M χ) •
      (χ : L →ₗ[K] K).smulRight (χ : L →ₗ[K] K) := by
  classical
  suffices ∑ χ ∈ {χ : Weight K L M | χ.IsZero}, finrank K (genWeightSpace M χ) •
      (χ : L →ₗ[K] K).smulRight (χ : L →ₗ[K] K) = 0 by
    rw [traceForm_eq_sum_finrank_nsmul,
      ← Finset.sum_filter_add_sum_filter_not (p := fun χ : Weight K L M ↦ χ.IsNonZero)]
    simp [this]
  refine Finset.sum_eq_zero fun χ hχ ↦ ?_
  replace hχ : (χ : L →ₗ[K] K) = 0 := by simpa [← Weight.coe_toLinear_eq_zero_iff] using hχ
  simp [hχ]

-- The reverse inclusion should also hold: TODO prove this!
lemma range_traceForm_le_span_weight :
    LinearMap.range (traceForm K L M) ≤ span K (range (Weight.toLinear K L M)) := by
  rintro - ⟨x, rfl⟩
  rw [LieModule.traceForm_eq_sum_finrank_nsmul, LinearMap.coeFn_sum, Finset.sum_apply]
  refine Submodule.sum_mem _ fun χ _ ↦ ?_
  simp_rw [LinearMap.smul_apply, LinearMap.coe_smulRight, Weight.toLinear_apply,
    ← Nat.cast_smul_eq_nsmul K]
  exact Submodule.smul_mem _ _ <| Submodule.smul_mem _ _ <| subset_span <| mem_range_self χ

end LieModule

end LieAlgebra
