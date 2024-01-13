/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Semisimple
import Mathlib.Algebra.Lie.Weights.Cartan
import Mathlib.LinearAlgebra.PID
import Mathlib.LinearAlgebra.Trace

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
   on `L` called the trace Form.
 * `LieModule.traceForm_eq_zero_of_isNilpotent`: the trace form induced by a nilpotent
   representation of a Lie algebra vanishes.
 * `killingForm`: the adjoint representation of a (finite, free) Lie algebra `L` induces a bilinear
   form on `L` via the trace form construction.
 * `LieAlgebra.IsKilling`: a typeclass encoding the fact that a Lie algebra has a non-singular
   Killing form.
 * `LieAlgebra.IsKilling.ker_restrictBilinear_of_isCartanSubalgebra_eq_bot`: if the Killing form of
   a Lie algebra is non-singular, it remains non-singular when restricted to a Cartan subalgebra.
 * `LieAlgebra.IsKilling.isSemisimple`: if a Lie algebra has non-singular Killing form then it is
   semisimple.
 * `LieAlgebra.IsKilling.isLieAbelian_of_isCartanSubalgebra`: if the Killing form of a Lie algebra
   is non-singular, then its Cartan subalgebras are Abelian.

## TODO

 * Prove that in characteristic zero, a semisimple Lie algebra has non-singular Killing form.
-/

variable (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [Module.Free R M] [Module.Finite R M]

attribute [local instance] isNoetherian_of_isNoetherianRing_of_finite
attribute [local instance] Module.free_of_finite_type_torsion_free'

local notation "φ" => LieModule.toEndomorphism R L M

open LinearMap (trace)
open Set BigOperators

namespace LieModule

/-- A finite, free representation of a Lie algebra `L` induces a bilinear form on `L` called
the trace Form. See also `killingForm`. -/
noncomputable def traceForm : L →ₗ[R] L →ₗ[R] R :=
  ((LinearMap.mul _ _).compl₁₂ (φ).toLinearMap (φ).toLinearMap).compr₂ (trace R M)

lemma traceForm_apply_apply (x y : L) :
    traceForm R L M x y = trace R _ (φ x ∘ₗ φ y) :=
  rfl

lemma traceForm_comm (x y : L) : traceForm R L M x y = traceForm R L M y x :=
  LinearMap.trace_mul_comm R (φ x) (φ y)

@[simp] lemma traceForm_flip : (traceForm R L M).flip = traceForm R L M :=
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
  · simp only [LieHom.map_lie, Ring.lie_def, ← LinearMap.mul_eq_comp]
  · simp only [sub_mul, mul_sub, map_sub, mul_assoc]
  · simp only [LinearMap.trace_mul_cycle' R (φ x) (φ z) (φ y)]
  · simp only [traceForm_apply_apply, LieHom.map_lie, Ring.lie_def, mul_sub, map_sub,
      ← LinearMap.mul_eq_comp]

/-- Given a representation `M` of a Lie algebra `L`, the action of any `x : L` is skew-adjoint wrt
the trace form. -/
lemma traceForm_apply_lie_apply' (x y z : L) :
    traceForm R L M ⁅x, y⁆ z = - traceForm R L M y ⁅x, z⁆ :=
  calc traceForm R L M ⁅x, y⁆ z
      = - traceForm R L M ⁅y, x⁆ z := by rw [← lie_skew x y, map_neg, LinearMap.neg_apply]
    _ = - traceForm R L M y ⁅x, z⁆ := by rw [traceForm_apply_lie_apply]

/-- This lemma justifies the terminology "invariant" for trace forms. -/
@[simp] lemma lie_traceForm_eq_zero (x : L) : ⁅x, traceForm R L M⁆ = 0 := by
  ext y z
  rw [LieHom.lie_apply, LinearMap.sub_apply, Module.Dual.lie_apply, LinearMap.zero_apply,
    LinearMap.zero_apply, traceForm_apply_lie_apply', sub_self]

@[simp] lemma traceForm_eq_zero_of_isNilpotent [IsReduced R] [IsNilpotent R L M] :
    traceForm R L M = 0 := by
  ext x y
  simp only [traceForm_apply_apply, LinearMap.zero_apply, ← isNilpotent_iff_eq_zero]
  apply LinearMap.isNilpotent_trace_of_isNilpotent
  exact isNilpotent_toEndomorphism_of_isNilpotent₂ R L M x y

/-- The upper and lower central series of `L` are orthogonal wrt the trace form of any Lie module
`M`. -/
lemma traceForm_eq_zero_if_mem_lcs_of_mem_ucs {x y : L} (k : ℕ)
    (hx : x ∈ (⊤ : LieIdeal R L).lcs L k) (hy : y ∈ (⊥ : LieIdeal R L).ucs k) :
    traceForm R L M x y = 0 := by
  induction' k with k ih generalizing x y
  · replace hy : y = 0 := by simpa using hy
    simp [hy]
  · rw [LieSubmodule.ucs_succ, LieSubmodule.mem_normalizer] at hy
    simp_rw [LieIdeal.lcs_succ, ← LieSubmodule.mem_coeSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span', LieSubmodule.mem_top, true_and] at hx
    refine Submodule.span_induction hx ?_ ?_ (fun z w hz hw ↦ ?_) (fun t z hz ↦ ?_)
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
invariant (in the sense that the action of `L` is skew-adjoint wrt `B`) then components of the
Fitting decomposition of `M` are orthogonal wrt `B`. -/
lemma eq_zero_of_mem_weightSpace_mem_posFitting [LieAlgebra.IsNilpotent R L]
    {B : M →ₗ[R] M →ₗ[R] R} (hB : ∀ (x : L) (m n : M), B ⁅x, m⁆ n = - B m ⁅x, n⁆)
    {m₀ m₁ : M} (hm₀ : m₀ ∈ weightSpace M (0 : L → R)) (hm₁ : m₁ ∈ posFittingComp R L M) :
    B m₀ m₁ = 0 := by
  replace hB : ∀ x (k : ℕ) m n, B m ((φ x ^ k) n) = (- 1 : R) ^ k • B ((φ x ^ k) m) n := by
    intro x k
    induction' k with k ih; simp
    intro m n
    replace hB : ∀ m, B m (φ x n) = (- 1 : R) • B (φ x m) n := by simp [hB]
    have : (-1 : R) ^ k • (-1 : R) = (-1 : R) ^ (k + 1) := by rw [pow_succ' (-1 : R), smul_eq_mul]
    conv_lhs => rw [pow_succ', LinearMap.mul_eq_comp, LinearMap.comp_apply, ih, hB,
      ← (φ x).comp_apply, ← LinearMap.mul_eq_comp, ← pow_succ, ← smul_assoc, this]
  suffices : ∀ (x : L) m, m ∈ posFittingCompOf R M x → B m₀ m = 0
  · apply LieSubmodule.iSup_induction _ hm₁ this (map_zero _)
    aesop
  clear hm₁ m₁; intro x m₁ hm₁
  simp only [mem_weightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm₀
  obtain ⟨k, hk⟩ := hm₀ x
  obtain ⟨m, rfl⟩ := (mem_posFittingCompOf R x m₁).mp hm₁ k
  simp [hB, hk]

lemma trace_toEndomorphism_eq_zero_of_mem_lcs
    {k : ℕ} {x : L} (hk : 1 ≤ k) (hx : x ∈ lowerCentralSeries R L L k) :
    trace R _ (toEndomorphism R L M x) = 0 := by
  replace hx : x ∈ lowerCentralSeries R L L 1 := antitone_lowerCentralSeries _ _ _ hk hx
  replace hx : x ∈ Submodule.span R {m | ∃ u v : L, ⁅u, v⁆ = m} := by
    rw [lowerCentralSeries_succ, ← LieSubmodule.mem_coeSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
    simpa using hx
  refine Submodule.span_induction (p := fun x ↦ trace R _ (toEndomorphism R L M x) = 0) hx
    (fun y ⟨u, v, huv⟩ ↦ ?_) ?_ (fun u v hu hv ↦ ?_) (fun t u hu ↦ ?_)
  · simp_rw [← huv, LieHom.map_lie, Ring.lie_def, map_sub, LinearMap.trace_mul_comm, sub_self]
  · simp
  · simp [hu, hv]
  · simp [hu]

variable [LieAlgebra.IsNilpotent R L] [IsTriangularizable R L M]
  [IsDomain R] [IsPrincipalIdealRing R]

lemma traceForm_eq_sum_weightSpaceOf (z : L) :
    traceForm R L M =
    ∑ χ in (finite_weightSpaceOf_ne_bot R L M z).toFinset, traceForm R L (weightSpaceOf M χ z) := by
  ext x y
  have hxy : ∀ χ : R, MapsTo ((toEndomorphism R L M x).comp (toEndomorphism R L M y))
      (weightSpaceOf M χ z) (weightSpaceOf M χ z) :=
    fun χ m hm ↦ LieSubmodule.lie_mem _ <| LieSubmodule.lie_mem _ hm
  have hfin : {χ : R | (weightSpaceOf M χ z : Submodule R M) ≠ ⊥}.Finite := by
    convert finite_weightSpaceOf_ne_bot R L M z
    exact LieSubmodule.coeSubmodule_eq_bot_iff (weightSpaceOf M _ _)
  classical
  have hds := DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top
    (LieSubmodule.independent_iff_coe_toSubmodule.mp <| independent_weightSpaceOf R L M z)
    (IsTriangularizable.iSup_eq_top z)
  simp only [LinearMap.coeFn_sum, Finset.sum_apply, traceForm_apply_apply,
    LinearMap.trace_eq_sum_trace_restrict' hds hfin hxy]
  exact Finset.sum_congr (by simp) (fun χ _ ↦ rfl)

-- In characteristic zero a stronger result holds (no `⊓ LieAlgebra.center K L`) TODO prove this!
lemma lowerCentralSeries_one_inf_center_le_ker_traceForm :
    lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L ≤ LinearMap.ker (traceForm R L M) := by
  rintro z ⟨hz : z ∈ lowerCentralSeries R L L 1, hzc : z ∈ LieAlgebra.center R L⟩
  ext x
  suffices ∀ χ : R, traceForm R L (weightSpaceOf M χ x) z x = 0 by
    simp [traceForm_eq_sum_weightSpaceOf R L M x, this]
  intro χ
  replace hz : LinearMap.trace R _ (toEndomorphism R L (weightSpaceOf M χ x) z) = 0 :=
    trace_toEndomorphism_eq_zero_of_mem_lcs R L _ (le_refl _) hz
  let f := toEndomorphism R L (weightSpaceOf M χ x) z
  let g := toEndomorphism R L (weightSpaceOf M χ x) x
  have h_comm : Commute f g := commute_toEndomorphism_of_mem_center_left _ hzc x
  have hg : _root_.IsNilpotent (g - algebraMap R _ χ) :=
    (toEndomorphism R L M x).isNilpotent_restrict_iSup_sub_algebraMap χ
  rw [traceForm_apply_apply, LinearMap.trace_comp_eq_mul_of_commute_of_isNilpotent χ h_comm hg, hz,
    mul_zero]

/-- A nilpotent Lie algebra with a representation whose trace form is non-singular is Abelian. -/
lemma isLieAbelian_of_ker_traceForm_eq_bot (h : LinearMap.ker (traceForm R L M) = ⊥) :
    IsLieAbelian L := by
  simpa only [← disjoint_lowerCentralSeries_maxTrivSubmodule_iff R L L, disjoint_iff_inf_le,
    LieIdeal.coe_to_lieSubalgebra_to_submodule, LieSubmodule.coeSubmodule_eq_bot_iff, h]
    using lowerCentralSeries_one_inf_center_le_ker_traceForm R L M

end LieModule

namespace LieSubmodule

open LieModule (traceForm)

variable {R L M}
variable [IsDomain R] [IsPrincipalIdealRing R]
  (N : LieSubmodule R L M) (I : LieIdeal R L) (h : I ≤ N.idealizer) (x : L) {y : L} (hy : y ∈ I)

lemma trace_eq_trace_restrict_of_le_idealizer
    (hy' : ∀ m ∈ N, (φ x ∘ₗ φ y) m ∈ N := fun m _ ↦ N.lie_mem (N.mem_idealizer.mp (h hy) m)) :
    trace R M (φ x ∘ₗ φ y) = trace R N ((φ x ∘ₗ φ y).restrict hy') := by
  suffices ∀ m, ⁅x, ⁅y, m⁆⁆ ∈ N by simp [(φ x ∘ₗ φ y).trace_restrict_eq_of_forall_mem _ this]
  exact fun m ↦ N.lie_mem (h hy m)

lemma traceForm_eq_of_le_idealizer :
    traceForm R I N = I.restrictBilinear (traceForm R L M) := by
  ext ⟨x, hx⟩ ⟨y, hy⟩
  change _ = trace R M (φ x ∘ₗ φ y)
  rw [N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  rfl

/-- Note that this result is slightly stronger than it might look at first glance: we only assume
that `N` is trivial over `I` rather than all of `L`. This means that it applies in the important
case of an Abelian ideal (which has `M = L` and `N = I`). -/
lemma traceForm_eq_zero_of_isTrivial [LieModule.IsTrivial I N] :
    trace R M (φ x ∘ₗ φ y) = 0 := by
  let hy' : ∀ m ∈ N, (φ x ∘ₗ φ y) m ∈ N := fun m _ ↦ N.lie_mem (N.mem_idealizer.mp (h hy) m)
  suffices : (φ x ∘ₗ φ y).restrict hy' = 0
  · simp [this, N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  ext n
  suffices ⁅y, (n : M)⁆ = 0 by simp [this]
  exact Submodule.coe_eq_zero.mpr (LieModule.IsTrivial.trivial (⟨y, hy⟩ : I) n)

end LieSubmodule

section LieAlgebra

variable [Module.Free R L] [Module.Finite R L]

/-- A finite, free (as an `R`-module) Lie algebra `L` carries a bilinear form on `L`.

This is a specialisation of `LieModule.traceForm` to the adjoint representation of `L`. -/
noncomputable abbrev killingForm : L →ₗ[R] L →ₗ[R] R := LieModule.traceForm R L L

lemma killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting
    (H : LieSubalgebra R L) [LieAlgebra.IsNilpotent R H]
    {x₀ x₁ : L}
    (hx₀ : x₀ ∈ LieAlgebra.zeroRootSubalgebra R L H)
    (hx₁ : x₁ ∈ LieModule.posFittingComp R H L) :
    killingForm R L x₀ x₁ = 0 :=
  LieModule.eq_zero_of_mem_weightSpace_mem_posFitting R H L
    (fun x y z ↦ LieModule.traceForm_apply_lie_apply' R L L x y z) hx₀ hx₁

namespace LieIdeal

variable (I : LieIdeal R L)

/-- The orthogonal complement of an ideal with respect to the killing form is an ideal. -/
noncomputable def killingCompl : LieIdeal R L :=
  { LinearMap.ker ((killingForm R L).compl₁₂ LinearMap.id I.subtype) with
    lie_mem := by
      intro x y hy
      ext ⟨z, hz⟩
      suffices killingForm R L ⁅x, y⁆ z = 0 by simpa
      rw [LieModule.traceForm_comm, ← LieModule.traceForm_apply_lie_apply, LieModule.traceForm_comm]
      simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
        Submodule.mem_toAddSubmonoid, LinearMap.mem_ker] at hy
      replace hy := LinearMap.congr_fun hy ⟨⁅z, x⁆, lie_mem_left R L I z x hz⟩
      simpa using hy }

@[simp] lemma mem_killingCompl {x : L} :
    x ∈ I.killingCompl ↔ ∀ y ∈ I, killingForm R L x y = 0 := by
  change x ∈ LinearMap.ker ((killingForm R L).compl₁₂ LinearMap.id I.subtype) ↔ _
  simp only [LinearMap.mem_ker, LieModule.traceForm_apply_apply, LinearMap.ext_iff,
    LinearMap.compl₁₂_apply, LinearMap.id_coe, id_eq, Submodule.coeSubtype,
    LieModule.traceForm_apply_apply, LinearMap.zero_apply, Subtype.forall]
  rfl

lemma coe_killingCompl_top :
    killingCompl R L ⊤ = LinearMap.ker (killingForm R L) := by
  ext
  simp [LinearMap.ext_iff]

variable [IsDomain R] [IsPrincipalIdealRing R]

lemma killingForm_eq :
    killingForm R I = I.restrictBilinear (killingForm R L) :=
  LieSubmodule.traceForm_eq_of_le_idealizer I I $ by simp

lemma restrictBilinear_killingForm :
    I.restrictBilinear (killingForm R L) = LieModule.traceForm R I L :=
  rfl

@[simp] lemma le_killingCompl_top_of_isLieAbelian [IsLieAbelian I] :
    I ≤ LieIdeal.killingCompl R L ⊤ := by
  intro x (hx : x ∈ I)
  simp only [mem_killingCompl, LieSubmodule.mem_top, forall_true_left]
  intro y
  rw [LieModule.traceForm_comm, LieModule.traceForm_apply_apply]
  exact LieSubmodule.traceForm_eq_zero_of_isTrivial I I (by simp) _ hx

end LieIdeal

namespace LieAlgebra

/-- We say a Lie algebra is Killing if its Killing form is non-singular.

NB: The is not standard terminology (the literature does not seem to name Lie algebras with this
property). -/
class IsKilling : Prop :=
  /-- We say a Lie algebra is Killing if its Killing form is non-singular. -/
  killingCompl_top_eq_bot : LieIdeal.killingCompl R L ⊤ = ⊥

attribute [simp] IsKilling.killingCompl_top_eq_bot

namespace IsKilling

variable [IsKilling R L]

@[simp] lemma ker_killingForm_eq_bot :
    LinearMap.ker (killingForm R L) = ⊥ := by
  simp [← LieIdeal.coe_killingCompl_top, killingCompl_top_eq_bot]

/-- If the Killing form of a Lie algebra is non-singular, it remains non-singular when restricted
to a Cartan subalgebra. -/
lemma ker_restrictBilinear_of_isCartanSubalgebra_eq_bot
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker (H.restrictBilinear (killingForm R L)) = ⊥ := by
  have h : Codisjoint (rootSpace H 0) (LieModule.posFittingComp R H L) :=
    (LieModule.isCompl_weightSpace_zero_posFittingComp R H L).codisjoint
  replace h : Codisjoint (H : Submodule R L) (LieModule.posFittingComp R H L : Submodule R L) := by
    rwa [codisjoint_iff, ← LieSubmodule.coe_toSubmodule_eq_iff, LieSubmodule.sup_coe_toSubmodule,
      LieSubmodule.top_coeSubmodule, rootSpace_zero_eq R L H, LieSubalgebra.coe_toLieSubmodule,
      ← codisjoint_iff] at h
  suffices this : ∀ m₀ ∈ H, ∀ m₁ ∈ LieModule.posFittingComp R H L, killingForm R L m₀ m₁ = 0 by
    simp [LinearMap.ker_restrictBilinear_eq_of_codisjoint h this]
  intro m₀ h₀ m₁ h₁
  exact killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting R L H (le_zeroRootSubalgebra R L H h₀) h₁

lemma restrictBilinear_killingForm (H : LieSubalgebra R L) :
    H.restrictBilinear (killingForm R L) = LieModule.traceForm R H L :=
  rfl

/-- The converse of this is true over a field of characteristic zero. There are counterexamples
over fields with positive characteristic. -/
instance isSemisimple [IsDomain R] [IsPrincipalIdealRing R] : IsSemisimple R L := by
  refine' (isSemisimple_iff_no_abelian_ideals R L).mpr fun I hI ↦ _
  rw [eq_bot_iff, ← killingCompl_top_eq_bot]
  exact I.le_killingCompl_top_of_isLieAbelian

-- TODO: formalize a positive-characteristic counterexample to the above instance

instance instIsLieAbelian_of_isCartanSubalgebra
    [IsDomain R] [IsPrincipalIdealRing R] [IsArtinian R L]
    (H : LieSubalgebra R L) [H.IsCartanSubalgebra] [LieModule.IsTriangularizable R H L] :
    IsLieAbelian H :=
  LieModule.isLieAbelian_of_ker_traceForm_eq_bot R H L <|
    ker_restrictBilinear_of_isCartanSubalgebra_eq_bot R L H

end IsKilling

end LieAlgebra

end LieAlgebra
