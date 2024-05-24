/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.Algebra.Lie.Derivation.Killing
import Mathlib.Algebra.Lie.Killing
import Mathlib.Algebra.Lie.Weights.Chain
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.JordanChevalley

/-!
# Roots of Lie algebras with non-degenerate Killing forms

The file contains definitions and results about roots of Lie algebras with non-degenerate Killing
forms.

## Main definitions
 * `LieAlgebra.IsKilling.ker_restrict_eq_bot_of_isCartanSubalgebra`: if the Killing form of
   a Lie algebra is non-singular, it remains non-singular when restricted to a Cartan subalgebra.
 * `LieAlgebra.IsKilling.instIsLieAbelianOfIsCartanSubalgebra`: if the Killing form of a Lie
   algebra is non-singular, then its Cartan subalgebras are Abelian.
 * `LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`: over a perfect field, if a Lie
   algebra has non-degenerate Killing form, Cartan subalgebras contain only semisimple elements.
 * `LieAlgebra.IsKilling.span_weight_eq_top`: given a splitting Cartan subalgebra `H` of a
   finite-dimensional Lie algebra with non-singular Killing form, the corresponding roots span the
   dual space of `H`.
 * `LieAlgebra.IsKilling.coroot`: the coroot corresponding to a root.
 * `LieAlgebra.IsKilling.isCompl_ker_weight_span_coroot`: given a root `α` with respect to a Cartan
   subalgebra `H`, we have a natural decomposition of `H` as the kernel of `α` and the span of the
   coroot corresponding to `α`.

-/

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

namespace LieAlgebra

namespace IsKilling

variable [IsKilling R L] [Module.Finite R L] [Module.Free R L]

/-- If the Killing form of a Lie algebra is non-singular, it remains non-singular when restricted
to a Cartan subalgebra. -/
lemma ker_restrict_eq_bot_of_isCartanSubalgebra
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker ((killingForm R L).restrict H) = ⊥ := by
  have h : Codisjoint (rootSpace H 0) (LieModule.posFittingComp R H L) :=
    (LieModule.isCompl_weightSpace_zero_posFittingComp R H L).codisjoint
  replace h : Codisjoint (H : Submodule R L) (LieModule.posFittingComp R H L : Submodule R L) := by
    rwa [codisjoint_iff, ← LieSubmodule.coe_toSubmodule_eq_iff, LieSubmodule.sup_coe_toSubmodule,
      LieSubmodule.top_coeSubmodule, rootSpace_zero_eq R L H, LieSubalgebra.coe_toLieSubmodule,
      ← codisjoint_iff] at h
  suffices this : ∀ m₀ ∈ H, ∀ m₁ ∈ LieModule.posFittingComp R H L, killingForm R L m₀ m₁ = 0 by
    simp [LinearMap.BilinForm.ker_restrict_eq_of_codisjoint h this]
  intro m₀ h₀ m₁ h₁
  exact killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting R L H (le_zeroRootSubalgebra R L H h₀) h₁

lemma restrict_killingForm (H : LieSubalgebra R L) :
    (killingForm R L).restrict H = LieModule.traceForm R H L :=
  rfl

@[simp] lemma ker_traceForm_eq_bot_of_isCartanSubalgebra
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker (LieModule.traceForm R H L) = ⊥ :=
  ker_restrict_eq_bot_of_isCartanSubalgebra R L H

lemma traceForm_cartan_nondegenerate
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    (LieModule.traceForm R H L).Nondegenerate := by
  simp [LinearMap.BilinForm.nondegenerate_iff_ker_eq_bot]

instance instIsLieAbelianOfIsCartanSubalgebra
    [IsDomain R] [IsPrincipalIdealRing R] [IsArtinian R L]
    (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    IsLieAbelian H :=
  LieModule.isLieAbelian_of_ker_traceForm_eq_bot R H L <|
    ker_restrict_eq_bot_of_isCartanSubalgebra R L H

end IsKilling

section Field

open FiniteDimensional LieModule Set
open Submodule (span subset_span)

variable [FiniteDimensional K L]
  (H : LieSubalgebra K L) [H.IsCartanSubalgebra] [IsTriangularizable K H L]

/-- For any `α` and `β`, the corresponding root spaces are orthogonal with respect to the Killing
form, provided `α + β ≠ 0`. -/
lemma killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero {α β : H → K} {x y : L}
    (hx : x ∈ rootSpace H α) (hy : y ∈ rootSpace H β) (hαβ : α + β ≠ 0) :
    killingForm K L x y = 0 := by
  /- If `ad R L z` is semisimple for all `z ∈ H` then writing `⟪x, y⟫ = killingForm K L x y`, there
  is a slick proof of this lemma that requires only invariance of the Killing form as follows.
  For any `z ∈ H`, we have:
  `α z • ⟪x, y⟫ = ⟪α z • x, y⟫ = ⟪⁅z, x⁆, y⟫ = - ⟪x, ⁅z, y⁆⟫ = - ⟪x, β z • y⟫ = - β z • ⟪x, y⟫`.
  Since this is true for any `z`, we thus have: `(α + β) • ⟪x, y⟫ = 0`, and hence the result.
  However the semisimplicity of `ad R L z` is (a) non-trivial and (b) requires the assumption
  that `K` is a perfect field and `L` has non-degenerate Killing form. -/
  let σ : (H → K) → (H → K) := fun γ ↦ α + (β + γ)
  have hσ : ∀ γ, σ γ ≠ γ := fun γ ↦ by simpa only [σ, ← add_assoc] using add_left_ne_self.mpr hαβ
  let f : Module.End K L := (ad K L x) ∘ₗ (ad K L y)
  have hf : ∀ γ, MapsTo f (rootSpace H γ) (rootSpace H (σ γ)) := fun γ ↦
    (mapsTo_toEnd_weightSpace_add_of_mem_rootSpace K L H L α (β + γ) hx).comp <|
      mapsTo_toEnd_weightSpace_add_of_mem_rootSpace K L H L β γ hy
  classical
  have hds := DirectSum.isInternal_submodule_of_independent_of_iSup_eq_top
    (LieSubmodule.independent_iff_coe_toSubmodule.mp <| independent_weightSpace K H L)
    (LieSubmodule.iSup_eq_top_iff_coe_toSubmodule.mp <| iSup_weightSpace_eq_top K H L)
  exact LinearMap.trace_eq_zero_of_mapsTo_ne hds σ hσ hf

/-- Elements of the `α` root space which are Killing-orthogonal to the `-α` root space are
Killing-orthogonal to all of `L`. -/
lemma mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg
    {α : H → K} {x : L} (hx : x ∈ rootSpace H α)
    (hx' : ∀ y ∈ rootSpace H (-α), killingForm K L x y = 0) :
    x ∈ LinearMap.ker (killingForm K L) := by
  rw [LinearMap.mem_ker]
  ext y
  have hy : y ∈ ⨆ β, rootSpace H β := by simp [iSup_weightSpace_eq_top K H L]
  induction hy using LieSubmodule.iSup_induction' with
  | hN β y hy =>
    by_cases hαβ : α + β = 0
    · exact hx' _ (add_eq_zero_iff_neg_eq.mp hαβ ▸ hy)
    · exact killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H hx hy hαβ
  | h0 => simp
  | hadd => simp_all

namespace IsKilling

variable [IsKilling K L]

/-- If a Lie algebra `L` has non-degenerate Killing form, the only element of a Cartan subalgebra
whose adjoint action on `L` is nilpotent, is the zero element.

Over a perfect field a much stronger result is true, see
`LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`. -/
lemma eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra {x : L} (hx : x ∈ H)
    (hx' : _root_.IsNilpotent (ad K L x)) : x = 0 := by
  suffices ⟨x, hx⟩ ∈ LinearMap.ker (traceForm K H L) by simpa using this
  simp only [LinearMap.mem_ker]
  ext y
  have comm : Commute (toEnd K H L ⟨x, hx⟩) (toEnd K H L y) := by
    rw [commute_iff_lie_eq, ← LieHom.map_lie, trivial_lie_zero, LieHom.map_zero]
  rw [traceForm_apply_apply, ← LinearMap.mul_eq_comp, LinearMap.zero_apply]
  exact (LinearMap.isNilpotent_trace_of_isNilpotent (comm.isNilpotent_mul_left hx')).eq_zero

open Module.End in
lemma isSemisimple_ad_of_mem_isCartanSubalgebra [PerfectField K] {x : L} (hx : x ∈ H) :
    (ad K L x).IsSemisimple := by
  /- Using Jordan-Chevalley, write `ad K L x` as a sum of its semisimple and nilpotent parts. -/
  obtain ⟨N, -, S, hS₀, hN, hS, hSN⟩ := (ad K L x).exists_isNilpotent_isSemisimple
  replace hS₀ : Commute (ad K L x) S := Algebra.commute_of_mem_adjoin_self hS₀
  set x' : H := ⟨x, hx⟩
  rw [eq_sub_of_add_eq hSN.symm] at hN
  /- Note that the semisimple part `S` is just a scalar action on each root space. -/
  have aux {α : H → K} {y : L} (hy : y ∈ rootSpace H α) : S y = α x' • y := by
    replace hy : y ∈ (ad K L x).maxGenEigenspace (α x') :=
      (weightSpace_le_weightSpaceOf L x' α) hy
    rw [maxGenEigenspace_eq] at hy
    set k := maxGenEigenspaceIndex (ad K L x) (α x')
    rw [apply_eq_of_mem_genEigenspace_of_comm_of_isSemisimple_of_isNilpotent_sub hy hS₀ hS hN]
  /- So `S` obeys the derivation axiom if we restrict to root spaces. -/
  have h_der (y z : L) (α β : H → K) (hy : y ∈ rootSpace H α) (hz : z ∈ rootSpace H β) :
      S ⁅y, z⁆ = ⁅S y, z⁆ + ⁅y, S z⁆ := by
    have hyz : ⁅y, z⁆ ∈ rootSpace H (α + β) :=
      mapsTo_toEnd_weightSpace_add_of_mem_rootSpace K L H L α β hy hz
    rw [aux hy, aux hz, aux hyz, smul_lie, lie_smul, ← add_smul, ← Pi.add_apply]
  /- Thus `S` is a derivation since root spaces span. -/
  replace h_der (y z : L) : S ⁅y, z⁆ = ⁅S y, z⁆ + ⁅y, S z⁆ := by
    have hy : y ∈ ⨆ α : H → K, rootSpace H α := by simp [iSup_weightSpace_eq_top]
    have hz : z ∈ ⨆ α : H → K, rootSpace H α := by simp [iSup_weightSpace_eq_top]
    induction hy using LieSubmodule.iSup_induction'
    · induction hz using LieSubmodule.iSup_induction'
      · next α y hy β z hz => exact h_der y z α β hy hz
      · simp
      · next h h' => simp only [lie_add, map_add, h, h']; abel
    · simp
    · next h h' => simp only [add_lie, map_add, h, h']; abel
  /- An equivalent form of the derivation axiom used in `LieDerivation`. -/
  replace h_der : ∀ y z : L, S ⁅y, z⁆ = ⁅y, S z⁆ - ⁅z, S y⁆ := by
    simp_rw [← lie_skew (S _) _, add_comm, ← sub_eq_add_neg] at h_der; assumption
  /- Bundle `S` as a `LieDerivation`. -/
  let S' : LieDerivation K L L := ⟨S, h_der⟩
  /- Since `L` has non-degenerate Killing form, `S` must be inner, corresponding to some `y : L`. -/
  obtain ⟨y, hy⟩ := LieDerivation.IsKilling.exists_eq_ad S'
  /- `y` commutes with all elements of `H` because `S` has eigenvalue 0 on `H`, `S = ad K L y`. -/
  have hy' (z : L) (hz : z ∈ H) : ⁅y, z⁆ = 0 := by
    rw [← LieSubalgebra.mem_toLieSubmodule, ← rootSpace_zero_eq] at hz
    simp [← ad_apply (R := K), ← LieDerivation.coe_ad_apply_eq_ad_apply, hy, aux hz]
  /- Thus `y` belongs to `H` since `H` is self-normalizing. -/
  replace hy' : y ∈ H := by
    suffices y ∈ H.normalizer by rwa [LieSubalgebra.IsCartanSubalgebra.self_normalizing] at this
    exact (H.mem_normalizer_iff y).mpr fun z hz ↦ hy' z hz ▸ LieSubalgebra.zero_mem H
  /- It suffices to show `x = y` since `S = ad K L y` is semisimple. -/
  suffices x = y by rwa [this, ← LieDerivation.coe_ad_apply_eq_ad_apply y, hy]
  rw [← sub_eq_zero]
  /- This will follow if we can show that `ad K L (x - y)` is nilpotent. -/
  apply eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra K L H (H.sub_mem hx hy')
  /- Which is true because `ad K L (x - y) = N`. -/
  replace hy : S = ad K L y := by rw [← LieDerivation.coe_ad_apply_eq_ad_apply y, hy]
  rwa [LieHom.map_sub, hSN, hy, add_sub_cancel_right, eq_sub_of_add_eq hSN.symm]

variable {K L} in
/-- The restriction of the Killing form to a Cartan subalgebra, as a linear equivalence to the
dual. -/
@[simps!]
noncomputable def cartanEquivDual :
    H ≃ₗ[K] Module.Dual K H :=
  (traceForm K H L).toDual <| traceForm_cartan_nondegenerate K L H

/-- This is Proposition 4.18 from [carter2005] except that we use
`LieModule.exists_forall_lie_eq_smul` instead of Lie's theorem (and so avoid
assuming `K` has characteristic zero). -/
lemma cartanEquivDual_symm_apply_mem_corootSpace (α : Weight K H L) :
    (cartanEquivDual H).symm α ∈ corootSpace α := by
  obtain ⟨e : L, he₀ : e ≠ 0, he : ∀ x, ⁅x, e⁆ = α x • e⟩ := exists_forall_lie_eq_smul K H L α
  have heα : e ∈ rootSpace H α := (mem_weightSpace L α e).mpr fun x ↦ ⟨1, by simp [← he x]⟩
  obtain ⟨f, hfα, hf⟩ : ∃ f ∈ rootSpace H (-α), killingForm K L e f ≠ 0 := by
    contrapose! he₀
    simpa using mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H heα he₀
  suffices ⁅e, f⁆ = killingForm K L e f • ((cartanEquivDual H).symm α : L) from
    (mem_corootSpace α).mpr <| Submodule.subset_span ⟨(killingForm K L e f)⁻¹ • e,
      Submodule.smul_mem _ _ heα, f, hfα, by simpa [inv_smul_eq_iff₀ hf]⟩
  set α' := (cartanEquivDual H).symm α
  rw [← sub_eq_zero, ← Submodule.mem_bot (R := K), ← ker_killingForm_eq_bot]
  apply mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg (α := (0 : H → K))
  · simp only [rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule]
    refine sub_mem ?_ (H.smul_mem _ α'.property)
    simpa using mapsTo_toEnd_weightSpace_add_of_mem_rootSpace K L H L α (-α) heα hfα
  · intro z hz
    replace hz : z ∈ H := by simpa using hz
    replace he : ⁅z, e⁆ = α ⟨z, hz⟩ • e := by simpa using he ⟨z, hz⟩
    have hαz : killingForm K L α' (⟨z, hz⟩ : H) = α ⟨z, hz⟩ :=
      LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_cartan_nondegenerate K L H) _ _
    simp [traceForm_comm K L L ⁅e, f⁆, ← traceForm_apply_lie_apply, he, mul_comm _ (α ⟨z, hz⟩), hαz]

/-- Given a splitting Cartan subalgebra `H` of a finite-dimensional Lie algebra with non-singular
Killing form, the corresponding roots span the dual space of `H`. -/
@[simp]
lemma span_weight_eq_top :
    span K (range (Weight.toLinear K H L)) = ⊤ := by
  refine eq_top_iff.mpr (le_trans ?_ (LieModule.range_traceForm_le_span_weight K H L))
  rw [← traceForm_flip K H L, ← LinearMap.dualAnnihilator_ker_eq_range_flip,
    ker_traceForm_eq_bot_of_isCartanSubalgebra, Submodule.dualAnnihilator_bot]

@[simp]
lemma iInf_ker_weight_eq_bot :
    ⨅ α : Weight K H L, α.ker = ⊥ := by
  rw [← Subspace.dualAnnihilator_inj, Subspace.dualAnnihilator_iInf_eq,
    Submodule.dualAnnihilator_bot]
  simp [← LinearMap.range_dualMap_eq_dualAnnihilator_ker, ← Submodule.span_range_eq_iSup]

@[simp]
lemma corootSpace_zero_eq_bot :
    corootSpace (0 : H → K) = ⊥ := by
  refine eq_bot_iff.mpr fun x hx ↦ ?_
  suffices {x | ∃ y ∈ H, ∃ z ∈ H, ⁅y, z⁆ = x} = {0} by simpa [mem_corootSpace, this] using hx
  refine eq_singleton_iff_unique_mem.mpr ⟨⟨0, H.zero_mem, 0, H.zero_mem, zero_lie 0⟩, ?_⟩
  rintro - ⟨y, hy, z, hz, rfl⟩
  suffices ⁅(⟨y, hy⟩ : H), (⟨z, hz⟩ : H)⁆ = 0 by
    simpa only [Subtype.ext_iff, LieSubalgebra.coe_bracket, ZeroMemClass.coe_zero] using this
  simp

section CharZero

variable {K H L}
variable [CharZero K]

/-- The contrapositive of this result is very useful, taking `x` to be the element of `H`
corresponding to a root `α` under the identification between `H` and `H^*` provided by the Killing
form. -/
lemma eq_zero_of_apply_eq_zero_of_mem_corootSpace
    (x : H) (α : H → K) (hαx : α x = 0) (hx : x ∈ corootSpace α) :
    x = 0 := by
  rcases eq_or_ne α 0 with rfl | hα; · simpa using hx
  replace hx : x ∈ ⨅ β : Weight K H L, β.ker := by
    refine (Submodule.mem_iInf _).mpr fun β ↦ ?_
    obtain ⟨a, b, hb, hab⟩ :=
      exists_forall_mem_corootSpace_smul_add_eq_zero L α β hα β.weightSpace_ne_bot
    simpa [hαx, hb.ne'] using hab _ hx
  simpa using hx

lemma disjoint_ker_weight_corootSpace (α : Weight K H L) :
    Disjoint α.ker (corootSpace α) := by
  rw [disjoint_iff]
  refine (Submodule.eq_bot_iff _).mpr fun x ⟨hαx, hx⟩ ↦ ?_
  replace hαx : α x = 0 := by simpa using hαx
  exact eq_zero_of_apply_eq_zero_of_mem_corootSpace x α hαx hx

/-- The coroot corresponding to a root. -/
noncomputable def coroot (α : Weight K H L) : H :=
  2 • (α <| (cartanEquivDual H).symm α)⁻¹ • (cartanEquivDual H).symm α

lemma root_apply_cartanEquivDual_symm_ne_zero {α : Weight K H L} (hα : α.IsNonZero) :
    α ((cartanEquivDual H).symm α) ≠ 0 := by
  contrapose! hα
  suffices (cartanEquivDual H).symm α ∈ α.ker ⊓ corootSpace α by
    rw [(disjoint_ker_weight_corootSpace α).eq_bot] at this
    simpa using this
  exact Submodule.mem_inf.mp ⟨hα, cartanEquivDual_symm_apply_mem_corootSpace K L H α⟩

lemma root_apply_coroot {α : Weight K H L} (hα : α.IsNonZero) :
    α (coroot α) = 2 := by
  rw [← Weight.coe_coe]
  simpa [coroot] using inv_mul_cancel (root_apply_cartanEquivDual_symm_ne_zero hα)

@[simp] lemma coroot_eq_zero_iff {α : Weight K H L} :
    coroot α = 0 ↔ α.IsZero := by
  refine ⟨fun hα ↦ ?_, fun hα ↦ ?_⟩
  · by_contra contra
    simpa [hα, ← α.coe_coe, map_zero] using root_apply_coroot contra
  · simp [coroot, Weight.coe_toLinear_eq_zero_iff.mpr hα]

lemma coe_corootSpace_eq_span_singleton (α : Weight K H L) :
    LieSubmodule.toSubmodule (corootSpace α) = K ∙ coroot α := by
  if hα : α.IsZero then
    simp [hα.eq, coroot_eq_zero_iff.mpr hα]
  else
    set α' := (cartanEquivDual H).symm α
    have hα' : (cartanEquivDual H).symm α ≠ 0 := by simpa using hα
    have h₁ : (K ∙ coroot α) = K ∙ α' := by
      have : IsUnit (2 * (α α')⁻¹) := by simpa using root_apply_cartanEquivDual_symm_ne_zero hα
      change (K ∙ (2 • (α α')⁻¹ • α')) = _
      simpa [nsmul_eq_smul_cast (R := K), smul_smul] using Submodule.span_singleton_smul_eq this _
    have h₂ : (K ∙ (cartanEquivDual H).symm α : Submodule K H) ≤ corootSpace α := by
      simpa using cartanEquivDual_symm_apply_mem_corootSpace K L H α
    suffices finrank K (LieSubmodule.toSubmodule (corootSpace α)) ≤ 1 by
      rw [← finrank_span_singleton (K := K) hα'] at this
      exact h₁ ▸ (eq_of_le_of_finrank_le h₂ this).symm
    have h : finrank K H = finrank K α.ker + 1 :=
      (Module.Dual.finrank_ker_add_one_of_ne_zero <| Weight.coe_toLinear_ne_zero_iff.mpr hα).symm
    simpa [h] using Submodule.finrank_add_finrank_le_of_disjoint (disjoint_ker_weight_corootSpace α)

@[simp]
lemma corootSpace_eq_bot_iff {α : Weight K H L} :
    corootSpace α = ⊥ ↔ α.IsZero := by
  simp [← LieSubmodule.coeSubmodule_eq_bot_iff, coe_corootSpace_eq_span_singleton α]

lemma isCompl_ker_weight_span_coroot (α : Weight K H L) :
    IsCompl α.ker (K ∙ coroot α) := by
  if hα : α.IsZero then
    simpa [Weight.coe_toLinear_eq_zero_iff.mpr hα, coroot_eq_zero_iff.mpr hα, Weight.ker]
      using isCompl_top_bot
  else
    rw [← coe_corootSpace_eq_span_singleton]
    apply Module.Dual.isCompl_ker_of_disjoint_of_ne_bot (by aesop)
      (disjoint_ker_weight_corootSpace α)
    replace hα : corootSpace α ≠ ⊥ := by simpa using hα
    rwa [ne_eq, ← LieSubmodule.coe_toSubmodule_eq_iff] at hα

end CharZero

end IsKilling

end Field

end LieAlgebra
