/-
Copyright (c) 2024 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Derivation.Killing
public import Mathlib.Algebra.Lie.Killing
public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Algebra.Lie.Weights.Chain
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.JordanChevalley

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
* `LieAlgebra.IsKilling.finrank_rootSpace_eq_one`: root spaces are one-dimensional.

-/

@[expose] public section

variable (R K L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L] [Field K] [LieAlgebra K L]

namespace LieAlgebra

lemma restrict_killingForm (H : LieSubalgebra R L) :
    (killingForm R L).restrict H = LieModule.traceForm R H L :=
  rfl

namespace IsKilling

variable [IsKilling R L]

/-- If the Killing form of a Lie algebra is non-singular, it remains non-singular when restricted
to a Cartan subalgebra. -/
lemma ker_restrict_eq_bot_of_isCartanSubalgebra
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker ((killingForm R L).restrict H) = ⊥ := by
  have h : Codisjoint (rootSpace H 0) (LieModule.posFittingComp R H L) :=
    (LieModule.isCompl_genWeightSpace_zero_posFittingComp R H L).codisjoint
  replace h : Codisjoint (H : Submodule R L) (LieModule.posFittingComp R H L : Submodule R L) := by
    rwa [codisjoint_iff, ← LieSubmodule.toSubmodule_inj, LieSubmodule.sup_toSubmodule,
      LieSubmodule.top_toSubmodule, rootSpace_zero_eq R L H, LieSubalgebra.coe_toLieSubmodule,
      ← codisjoint_iff] at h
  suffices this : ∀ m₀ ∈ H, ∀ m₁ ∈ LieModule.posFittingComp R H L, killingForm R L m₀ m₁ = 0 by
    simp [LinearMap.BilinForm.ker_restrict_eq_of_codisjoint h this]
  intro m₀ h₀ m₁ h₁
  exact killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting R L H (le_zeroRootSubalgebra R L H h₀) h₁

@[simp] lemma ker_traceForm_eq_bot_of_isCartanSubalgebra
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    LinearMap.ker (LieModule.traceForm R H L) = ⊥ :=
  ker_restrict_eq_bot_of_isCartanSubalgebra R L H

lemma traceForm_cartan_nondegenerate
    [IsNoetherian R L] [IsArtinian R L] (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    (LieModule.traceForm R H L).Nondegenerate := by
  simp [LinearMap.separatingLeft_iff_ker_eq_bot,
    (LieModule.traceForm_isSymm R H L).isRefl.nondegenerate_iff_separatingLeft]

variable [Module.Free R L] [Module.Finite R L]

instance instIsLieAbelianOfIsCartanSubalgebra
    [IsDomain R] [IsPrincipalIdealRing R] [IsArtinian R L]
    (H : LieSubalgebra R L) [H.IsCartanSubalgebra] :
    IsLieAbelian H :=
  LieModule.isLieAbelian_of_ker_traceForm_eq_bot R H L <|
    ker_restrict_eq_bot_of_isCartanSubalgebra R L H

end IsKilling

section Field

open Module LieModule Set
open Submodule (span subset_span)

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

section
variable [IsTriangularizable K H L]

set_option backward.isDefEq.respectTransparency false in
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
  have hσ : ∀ γ, σ γ ≠ γ := fun γ ↦ by simpa only [σ, ← add_assoc] using add_ne_right.mpr hαβ
  let f : Module.End K L := (ad K L x) ∘ₗ (ad K L y)
  have hf : ∀ γ, MapsTo f (rootSpace H γ) (rootSpace H (σ γ)) := fun γ ↦
    (mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L α (β + γ) hx).comp <|
      mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L β γ hy
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr <| iSupIndep_genWeightSpace K H L)
    (LieSubmodule.iSup_toSubmodule_eq_top.mpr <| iSup_genWeightSpace_eq_top K H L)
  exact LinearMap.trace_eq_zero_of_mapsTo_ne hds σ hσ hf

/-- Elements of the `α` root space which are Killing-orthogonal to the `-α` root space are
Killing-orthogonal to all of `L`. -/
lemma mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg
    {α : H → K} {x : L} (hx : x ∈ rootSpace H α)
    (hx' : ∀ y ∈ rootSpace H (-α), killingForm K L x y = 0) :
    x ∈ LinearMap.ker (killingForm K L) := by
  rw [LinearMap.mem_ker]
  ext y
  have hy : y ∈ ⨆ β, rootSpace H β := by simp [iSup_genWeightSpace_eq_top K H L]
  induction hy using LieSubmodule.iSup_induction' with
  | mem β y hy =>
    by_cases hαβ : α + β = 0
    · exact hx' _ (add_eq_zero_iff_neg_eq.mp hαβ ▸ hy)
    · exact killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H hx hy hαβ
  | zero => simp
  | add => simp_all
end

end Field

end LieAlgebra

namespace LieModule

namespace Weight

open LieAlgebra IsKilling

variable {K L}

variable [FiniteDimensional K L] [IsKilling K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L] {α : Weight K H L}

instance : InvolutiveNeg (Weight K H L) where
  neg α := ⟨-α, by
    by_cases hα : α.IsZero
    · convert α.genWeightSpace_ne_bot; rw [hα, neg_zero]
    · intro e
      obtain ⟨x, hx, x_ne0⟩ := α.exists_ne_zero
      have := mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H hx
        (fun y hy ↦ by rw [rootSpace, e] at hy; rw [hy, map_zero])
      rw [ker_killingForm_eq_bot] at this
      exact x_ne0 this⟩
  neg_neg α := by ext; simp

@[simp] lemma coe_neg : ((-α : Weight K H L) : H → K) = -α := rfl

lemma IsZero.neg (h : α.IsZero) : (-α).IsZero := by ext; rw [coe_neg, h, neg_zero]

@[simp] lemma isZero_neg : (-α).IsZero ↔ α.IsZero := ⟨fun h ↦ neg_neg α ▸ h.neg, fun h ↦ h.neg⟩

lemma IsNonZero.neg (h : α.IsNonZero) : (-α).IsNonZero := fun e ↦ h (by simpa using e.neg)

@[simp] lemma isNonZero_neg {α : Weight K H L} : (-α).IsNonZero ↔ α.IsNonZero := isZero_neg.not

@[simp] lemma toLinear_neg {α : Weight K H L} : (-α).toLinear = -α.toLinear := rfl

end Weight

end LieModule

namespace LieAlgebra

open Module LieModule Set
open Submodule renaming span → span
open Submodule renaming subset_span → subset_span

namespace IsKilling

variable [FiniteDimensional K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]
variable [IsKilling K L]

/-- If a Lie algebra `L` has non-degenerate Killing form, the only element of a Cartan subalgebra
whose adjoint action on `L` is nilpotent, is the zero element.

Over a perfect field a much stronger result is true, see
`LieAlgebra.IsKilling.isSemisimple_ad_of_mem_isCartanSubalgebra`. -/
lemma eq_zero_of_isNilpotent_ad_of_mem_isCartanSubalgebra {x : L} (hx : x ∈ H)
    (hx' : _root_.IsNilpotent (ad K L x)) : x = 0 := by
  suffices ⟨x, hx⟩ ∈ LinearMap.ker (traceForm K H L) by
    simp only [ker_traceForm_eq_bot_of_isCartanSubalgebra, Submodule.mem_bot] at this
    exact (AddSubmonoid.mk_eq_zero H.toAddSubmonoid).mp this
  simp only [LinearMap.mem_ker]
  ext y
  have comm : Commute (toEnd K H L ⟨x, hx⟩) (toEnd K H L y) := by
    rw [commute_iff_lie_eq, ← LieHom.map_lie, trivial_lie_zero, map_zero]
  rw [traceForm_apply_apply, ← Module.End.mul_eq_comp, LinearMap.zero_apply]
  exact (LinearMap.isNilpotent_trace_of_isNilpotent (comm.isNilpotent_mul_right hx')).eq_zero

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

variable {K L} in
/-- The restriction of the Killing form to a Cartan subalgebra, as a linear equivalence to the
dual. -/
@[simps! apply_apply]
noncomputable def cartanEquivDual :
    H ≃ₗ[K] Module.Dual K H :=
  (traceForm K H L).toDual <| traceForm_cartan_nondegenerate K L H

variable {K L H}

/-- The coroot corresponding to a root. -/
noncomputable def coroot (α : Weight K H L) : H :=
  2 • (α <| (cartanEquivDual H).symm α)⁻¹ • (cartanEquivDual H).symm α

lemma traceForm_coroot (α : Weight K H L) (x : H) :
    traceForm K H L (coroot α) x = 2 • (α <| (cartanEquivDual H).symm α)⁻¹ • α x := by
  have : cartanEquivDual H ((cartanEquivDual H).symm α) x = α x := by
    rw [LinearEquiv.apply_symm_apply, Weight.toLinear_apply]
  rw [coroot, map_nsmul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply]
  congr 2

@[simp] lemma coroot_neg [IsTriangularizable K H L] (α : Weight K H L) :
    coroot (-α) = -coroot α := by
  simp [coroot]

variable [IsTriangularizable K H L]

lemma lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux
    {α : Weight K H L} {e f : L} (heα : e ∈ rootSpace H α) (hfα : f ∈ rootSpace H (-α))
    (aux : ∀ (h : H), ⁅h, e⁆ = α h • e) :
    ⁅e, f⁆ = killingForm K L e f • (cartanEquivDual H).symm α := by
  set α' := (cartanEquivDual H).symm α
  rw [← sub_eq_zero, ← Submodule.mem_bot (R := K), ← ker_killingForm_eq_bot]
  apply mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg (α := (0 : H → K))
  · simp only [rootSpace_zero_eq, LieSubalgebra.mem_toLieSubmodule]
    refine sub_mem ?_ (H.smul_mem _ α'.property)
    simpa using mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L α (-α) heα hfα
  · intro z hz
    replace hz : z ∈ H := by simpa using hz
    have he : ⁅z, e⁆ = α ⟨z, hz⟩ • e := aux ⟨z, hz⟩
    have hαz : killingForm K L α' (⟨z, hz⟩ : H) = α ⟨z, hz⟩ :=
      LinearMap.BilinForm.apply_toDual_symm_apply (hB := traceForm_cartan_nondegenerate K L H) _ _
    simp [traceForm_comm K L L ⁅e, f⁆, ← traceForm_apply_lie_apply, he, mul_comm _ (α ⟨z, hz⟩), hαz]

/-- This is Proposition 4.18 from [carter2005] except that we use
`LieModule.exists_forall_lie_eq_smul` instead of Lie's theorem (and so avoid
assuming `K` has characteristic zero). -/
lemma cartanEquivDual_symm_apply_mem_corootSpace (α : Weight K H L) :
    (cartanEquivDual H).symm α ∈ corootSpace α := by
  obtain ⟨e : L, he₀ : e ≠ 0, he : ∀ x, ⁅x, e⁆ = α x • e⟩ := exists_forall_lie_eq_smul K H L α
  have heα : e ∈ rootSpace H α := (mem_genWeightSpace L α e).mpr fun x ↦ ⟨1, by simp [← he x]⟩
  obtain ⟨f, hfα, hf⟩ : ∃ f ∈ rootSpace H (-α), killingForm K L e f ≠ 0 := by
    contrapose! he₀
    simpa using mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H heα he₀
  suffices ⁅e, f⁆ = killingForm K L e f • ((cartanEquivDual H).symm α : L) from
    (mem_corootSpace α).mpr <| Submodule.subset_span ⟨(killingForm K L e f)⁻¹ • e,
      Submodule.smul_mem _ _ heα, f, hfα, by simpa [inv_smul_eq_iff₀ hf]⟩
  exact lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux heα hfα he

@[simp] lemma coroot_mem_corootSpace (α : Weight K H L) :
    coroot α ∈ corootSpace α :=
  nsmul_mem (Submodule.smul_mem _ _ <| cartanEquivDual_symm_apply_mem_corootSpace α) _

/-- Given a splitting Cartan subalgebra `H` of a finite-dimensional Lie algebra with non-singular
Killing form, the corresponding roots span the dual space of `H`. -/
@[simp]
lemma span_weight_eq_top :
    span K (range (Weight.toLinear K H L)) = ⊤ := by
  refine eq_top_iff.mpr (le_trans ?_ (LieModule.range_traceForm_le_span_weight K H L))
  rw [← traceForm_flip K H L, ← LinearMap.dualAnnihilator_ker_eq_range_flip,
    ker_traceForm_eq_bot_of_isCartanSubalgebra, Submodule.dualAnnihilator_bot]

variable (K L H) in
@[simp]
lemma span_weight_isNonZero_eq_top :
    span K ({α : Weight K H L | α.IsNonZero}.image (Weight.toLinear K H L)) = ⊤ := by
  rw [← span_weight_eq_top]
  refine le_antisymm (Submodule.span_mono <| by simp) ?_
  suffices range (Weight.toLinear K H L) ⊆
    insert 0 ({α : Weight K H L | α.IsNonZero}.image (Weight.toLinear K H L)) by
    simpa only [Submodule.span_insert_zero] using Submodule.span_mono this
  rintro - ⟨α, rfl⟩
  simp only [mem_insert_iff, Weight.coe_toLinear_eq_zero_iff, mem_image, mem_setOf_eq]
  tauto

@[simp]
lemma iInf_ker_weight_eq_bot :
    ⨅ α : Weight K H L, α.ker = ⊥ := by
  rw [← Subspace.dualAnnihilator_inj, Subspace.dualAnnihilator_iInf_eq,
    Submodule.dualAnnihilator_bot]
  simp [← LinearMap.range_dualMap_eq_dualAnnihilator_ker, ← Submodule.span_range_eq_iSup]

section PerfectField

variable [PerfectField K]

open Module.End in
lemma isSemisimple_ad_of_mem_isCartanSubalgebra {x : L} (hx : x ∈ H) :
    (ad K L x).IsSemisimple := by
  /- Using Jordan-Chevalley, write `ad K L x` as a sum of its semisimple and nilpotent parts. -/
  obtain ⟨N, -, S, hS₀, hN, hS, hSN⟩ := (ad K L x).exists_isNilpotent_isSemisimple
  replace hS₀ : Commute (ad K L x) S := Algebra.commute_of_mem_adjoin_self hS₀
  set x' : H := ⟨x, hx⟩
  rw [eq_sub_of_add_eq hSN.symm] at hN
  /- Note that the semisimple part `S` is just a scalar action on each root space. -/
  have aux {α : H → K} {y : L} (hy : y ∈ rootSpace H α) : S y = α x' • y := by
    replace hy : y ∈ (ad K L x).maxGenEigenspace (α x') :=
      (genWeightSpace_le_genWeightSpaceOf L x' α) hy
    rw [maxGenEigenspace_eq] at hy
    set k := maxGenEigenspaceIndex (ad K L x) (α x')
    rw [apply_eq_of_mem_of_comm_of_isFinitelySemisimple_of_isNil hy hS₀ hS.isFinitelySemisimple hN]
  /- So `S` obeys the derivation axiom if we restrict to root spaces. -/
  have h_der (y z : L) (α β : H → K) (hy : y ∈ rootSpace H α) (hz : z ∈ rootSpace H β) :
      S ⁅y, z⁆ = ⁅S y, z⁆ + ⁅y, S z⁆ := by
    have hyz : ⁅y, z⁆ ∈ rootSpace H (α + β) :=
      mapsTo_toEnd_genWeightSpace_add_of_mem_rootSpace K L H L α β hy hz
    rw [aux hy, aux hz, aux hyz, smul_lie, lie_smul, ← add_smul, ← Pi.add_apply]
  /- Thus `S` is a derivation since root spaces span. -/
  replace h_der (y z : L) : S ⁅y, z⁆ = ⁅S y, z⁆ + ⁅y, S z⁆ := by
    have hy : y ∈ ⨆ α : H → K, rootSpace H α := by simp [iSup_genWeightSpace_eq_top]
    have hz : z ∈ ⨆ α : H → K, rootSpace H α := by simp [iSup_genWeightSpace_eq_top]
    induction hy using LieSubmodule.iSup_induction' with
    | mem α y hy =>
      induction hz using LieSubmodule.iSup_induction' with
      | mem β z hz => exact h_der y z α β hy hz
      | zero => simp
      | add _ _ _ _ h h' => simp only [lie_add, map_add, h, h']; abel
    | zero => simp
    | add _ _ _ _ h h' => simp only [add_lie, map_add, h, h']; abel
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
    simp [S', ← ad_apply (R := K), ← LieDerivation.coe_ad_apply_eq_ad_apply, hy, aux hz]
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
  rwa [map_sub, hSN, hy, add_sub_cancel_right, eq_sub_of_add_eq hSN.symm]

lemma lie_eq_smul_of_mem_rootSpace {α : H → K} {x : L} (hx : x ∈ rootSpace H α) (h : H) :
    ⁅h, x⁆ = α h • x := by
  replace hx : x ∈ (ad K L h).maxGenEigenspace (α h) :=
    genWeightSpace_le_genWeightSpaceOf L h α hx
  rw [(isSemisimple_ad_of_mem_isCartanSubalgebra
    h.property).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace,
    Module.End.mem_eigenspace_iff] at hx
  simpa using hx

lemma lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg
    {α : Weight K H L} {e f : L} (heα : e ∈ rootSpace H α) (hfα : f ∈ rootSpace H (-α)) :
    ⁅e, f⁆ = killingForm K L e f • (cartanEquivDual H).symm α := by
  apply lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg_aux heα hfα
  exact lie_eq_smul_of_mem_rootSpace heα

lemma coe_corootSpace_eq_span_singleton' (α : Weight K H L) :
    (corootSpace α).toSubmodule = K ∙ (cartanEquivDual H).symm α := by
  refine le_antisymm ?_ ?_
  · intro ⟨x, hx⟩ hx'
    have : {⁅y, z⁆ | (y ∈ rootSpace H α) (z ∈ rootSpace H (-α))} ⊆
        K ∙ ((cartanEquivDual H).symm α : L) := by
      rintro - ⟨e, heα, f, hfα, rfl⟩
      rw [lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα, SetLike.mem_coe,
        Submodule.mem_span_singleton]
      exact ⟨killingForm K L e f, rfl⟩
    simp only [LieSubmodule.mem_toSubmodule, mem_corootSpace] at hx'
    replace this := Submodule.span_mono this hx'
    rw [Submodule.span_span] at this
    rw [Submodule.mem_span_singleton] at this ⊢
    obtain ⟨t, rfl⟩ := this
    solve_by_elim
  · simp only [Submodule.span_singleton_le_iff_mem, LieSubmodule.mem_toSubmodule]
    exact cartanEquivDual_symm_apply_mem_corootSpace α

end PerfectField

section CharZero

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
      exists_forall_mem_corootSpace_smul_add_eq_zero L α β hα β.genWeightSpace_ne_bot
    simpa [hαx, hb.ne'] using hab _ hx
  simpa using hx

lemma disjoint_ker_weight_corootSpace (α : Weight K H L) :
    Disjoint α.ker (corootSpace α) := by
  rw [disjoint_iff]
  refine (Submodule.eq_bot_iff _).mpr fun x ⟨hαx, hx⟩ ↦ ?_
  replace hαx : α x = 0 := by simpa using hαx
  exact eq_zero_of_apply_eq_zero_of_mem_corootSpace x α hαx hx

lemma root_apply_cartanEquivDual_symm_ne_zero {α : Weight K H L} (hα : α.IsNonZero) :
    α ((cartanEquivDual H).symm α) ≠ 0 := by
  contrapose! hα
  suffices (cartanEquivDual H).symm α ∈ α.ker ⊓ corootSpace α by
    rw [(disjoint_ker_weight_corootSpace α).eq_bot] at this
    simpa using this
  exact Submodule.mem_inf.mp ⟨hα, cartanEquivDual_symm_apply_mem_corootSpace α⟩

lemma root_apply_coroot {α : Weight K H L} (hα : α.IsNonZero) :
    α (coroot α) = 2 := by
  rw [← Weight.coe_coe]
  simpa [coroot] using inv_mul_cancel₀ (root_apply_cartanEquivDual_symm_ne_zero hα)

@[simp] lemma coroot_eq_zero_iff {α : Weight K H L} :
    coroot α = 0 ↔ α.IsZero := by
  refine ⟨fun hα ↦ ?_, fun hα ↦ ?_⟩
  · by_contra contra
    simpa [hα, ← α.coe_coe, map_zero] using root_apply_coroot contra
  · simp [coroot, Weight.coe_toLinear_eq_zero_iff.mpr hα]

@[simp]
lemma coroot_zero [Nontrivial L] : coroot (0 : Weight K H L) = 0 := by simp [Weight.isZero_zero]

lemma coe_corootSpace_eq_span_singleton (α : Weight K H L) :
    (corootSpace α).toSubmodule = K ∙ coroot α := by
  if hα : α.IsZero then
    simp [hα.eq, coroot_eq_zero_iff.mpr hα]
  else
    set α' := (cartanEquivDual H).symm α
    suffices (K ∙ coroot α) = K ∙ α' by rw [coe_corootSpace_eq_span_singleton']; exact this.symm
    have : IsUnit (2 * (α α')⁻¹) := by simpa using root_apply_cartanEquivDual_symm_ne_zero hα
    change (K ∙ (2 • (α α')⁻¹ • α')) = _
    simpa [← Nat.cast_smul_eq_nsmul K, smul_smul] using Submodule.span_singleton_smul_eq this _

@[simp]
lemma corootSpace_eq_bot_iff {α : Weight K H L} :
    corootSpace α = ⊥ ↔ α.IsZero := by
  simp [← LieSubmodule.toSubmodule_eq_bot, coe_corootSpace_eq_span_singleton α]

lemma isCompl_ker_weight_span_coroot (α : Weight K H L) :
    IsCompl α.ker (K ∙ coroot α) := by
  if hα : α.IsZero then
    simpa [Weight.coe_toLinear_eq_zero_iff.mpr hα, coroot_eq_zero_iff.mpr hα, Weight.ker]
      using isCompl_top_bot
  else
    rw [← coe_corootSpace_eq_span_singleton]
    apply Module.Dual.isCompl_ker_of_disjoint_of_ne_bot (by simp_all)
      (disjoint_ker_weight_corootSpace α)
    replace hα : corootSpace α ≠ ⊥ := by simpa using hα
    rwa [ne_eq, ← LieSubmodule.toSubmodule_inj] at hα

lemma traceForm_eq_zero_of_mem_ker_of_mem_span_coroot {α : Weight K H L} {x y : H}
    (hx : x ∈ α.ker) (hy : y ∈ K ∙ coroot α) :
    traceForm K H L x y = 0 := by
  rw [← coe_corootSpace_eq_span_singleton, LieSubmodule.mem_toSubmodule, mem_corootSpace'] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨u, hu, v, -, huv⟩ := hz
    change killingForm K L (x : L) (z : L) = 0
    replace hx : α x = 0 := by simpa using hx
    rw [← huv, ← traceForm_apply_lie_apply, ← LieSubalgebra.coe_bracket_of_module,
      lie_eq_smul_of_mem_rootSpace hu, hx, zero_smul, map_zero, LinearMap.zero_apply]
  | zero => simp
  | add _ _ _ _ hx hy => simp [hx, hy]
  | smul _ _ _ hz => simp [hz]

@[simp] lemma orthogonal_span_coroot_eq_ker (α : Weight K H L) :
    (traceForm K H L).orthogonal (K ∙ coroot α) = α.ker := by
  if hα : α.IsZero then
    have hα' : coroot α = 0 := by simpa
    replace hα : α.ker = ⊤ := by ext; simp [hα]
    simp [hα, hα']
  else
    refine le_antisymm (fun x hx ↦ ?_) (fun x hx y hy ↦ ?_)
    · simp only [LinearMap.BilinForm.mem_orthogonal_iff] at hx
      specialize hx (coroot α) (Submodule.mem_span_singleton_self _)
      simp only [LinearMap.BilinForm.isOrtho_def, traceForm_coroot, smul_eq_mul, nsmul_eq_mul,
        Nat.cast_ofNat, mul_eq_zero, OfNat.ofNat_ne_zero, inv_eq_zero, false_or] at hx
      simpa using hx.resolve_left (root_apply_cartanEquivDual_symm_ne_zero hα)
    · have := traceForm_eq_zero_of_mem_ker_of_mem_span_coroot hx hy
      rwa [traceForm_comm] at this

@[simp] lemma coroot_eq_iff (α β : Weight K H L) :
    coroot α = coroot β ↔ α = β := by
  refine ⟨fun hyp ↦ ?_, fun h ↦ by rw [h]⟩
  if hα : α.IsZero then
    have hβ : β.IsZero := by
      rw [← coroot_eq_zero_iff] at hα ⊢
      rwa [← hyp]
    ext
    simp [hα.eq, hβ.eq]
  else
    have hβ : β.IsNonZero := by
      contrapose! hα
      simp only [← coroot_eq_zero_iff] at hα ⊢
      rwa [hyp]
    have : α.ker = β.ker := by
      rw [← orthogonal_span_coroot_eq_ker α, hyp, orthogonal_span_coroot_eq_ker]
    suffices (α : H →ₗ[K] K) = β by ext x; simpa using LinearMap.congr_fun this x
    apply Module.Dual.eq_of_ker_eq_of_apply_eq (coroot α) this
    · rw [Weight.toLinear_apply, root_apply_coroot hα, hyp, Weight.toLinear_apply,
        root_apply_coroot hβ]
    · simp [root_apply_coroot hα]

set_option backward.isDefEq.respectTransparency false in
lemma exists_isSl2Triple_of_weight_isNonZero {α : Weight K H L} (hα : α.IsNonZero) :
    ∃ h e f : L, IsSl2Triple h e f ∧ e ∈ rootSpace H α ∧ f ∈ rootSpace H (-α) := by
  obtain ⟨e, heα : e ∈ rootSpace H α, he₀ : e ≠ 0⟩ := α.exists_ne_zero
  obtain ⟨f', hfα, hf⟩ : ∃ f ∈ rootSpace H (-α), killingForm K L e f ≠ 0 := by
    contrapose! he₀
    simpa using mem_ker_killingForm_of_mem_rootSpace_of_forall_rootSpace_neg K L H heα he₀
  have hef := lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα
  let h : H := ⟨⁅e, f'⁆, hef ▸ Submodule.smul_mem _ _ (Submodule.coe_mem _)⟩
  have hh : α h ≠ 0 := by
    have : h = killingForm K L e f' • (cartanEquivDual H).symm α := by
      simp only [h, Subtype.ext_iff, hef]
      rw [Submodule.coe_smul_of_tower]
    rw [this, map_smul, smul_eq_mul, ne_eq, mul_eq_zero, not_or]
    exact ⟨hf, root_apply_cartanEquivDual_symm_ne_zero hα⟩
  let f := (2 * (α h)⁻¹) • f'
  replace hef : ⁅⁅e, f⁆, e⁆ = 2 • e := by
    have : ⁅⁅e, f'⁆, e⁆ = α h • e := lie_eq_smul_of_mem_rootSpace heα h
    rw [lie_smul, smul_lie, this, ← smul_assoc, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hh,
      mul_one, two_smul, two_smul]
  refine ⟨⁅e, f⁆, e, f, ⟨fun contra ↦ ?_, rfl, hef, ?_⟩, heα, Submodule.smul_mem _ _ hfα⟩
  · rw [contra] at hef
    have : IsAddTorsionFree L := .of_isTorsionFree K L
    simp only [zero_lie, eq_comm (a := (0 : L)), smul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hef
    contradiction
  · have : ⁅⁅e, f'⁆, f'⁆ = - α h • f' := lie_eq_smul_of_mem_rootSpace hfα h
    rw [lie_smul, lie_smul, smul_lie, this]
    simp [← smul_assoc, f, hh, mul_comm _ (2 * (α h)⁻¹)]

lemma _root_.IsSl2Triple.h_eq_coroot {α : Weight K H L} (hα : α.IsNonZero)
    {h e f : L} (ht : IsSl2Triple h e f) (heα : e ∈ rootSpace H α) (hfα : f ∈ rootSpace H (-α)) :
    h = coroot α := by
  have hef := lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg heα hfα
  lift h to H using by simpa only [← ht.lie_e_f, hef] using H.smul_mem _ (Submodule.coe_mem _)
  congr 1
  have key : α h = 2 := by
    have := lie_eq_smul_of_mem_rootSpace heα h
    rw [LieSubalgebra.coe_bracket_of_module, ht.lie_h_e_smul K] at this
    exact smul_left_injective K ht.e_ne_zero this.symm
  suffices ∃ s : K, s • h = coroot α by
    obtain ⟨s, hs⟩ := this
    replace this : s = 1 := by simpa [root_apply_coroot hα, key] using congr_arg α hs
    rwa [this, one_smul] at hs
  set α' := (cartanEquivDual H).symm α with hα'
  have h_eq : h = killingForm K L e f • α' := by
    simp only [hα', Subtype.ext_iff, ← ht.lie_e_f, hef]
    rw [Submodule.coe_smul_of_tower]
  use (2 • (α α')⁻¹) * (killingForm K L e f)⁻¹
  have hef₀ : killingForm K L e f ≠ 0 := by
    have := ht.h_ne_zero
    contrapose! this
    simpa [this] using h_eq
  rw [h_eq, smul_smul, mul_assoc, inv_mul_cancel₀ hef₀, mul_one, smul_assoc, coroot]

lemma finrank_rootSpace_eq_one (α : Weight K H L) (hα : α.IsNonZero) :
    finrank K (rootSpace H α) = 1 := by
  suffices ¬ 1 < finrank K (rootSpace H α) by
    have h₀ : finrank K (rootSpace H α) ≠ 0 := by
      convert_to finrank K (rootSpace H α).toSubmodule ≠ 0
      simpa using α.genWeightSpace_ne_bot
    lia
  intro contra
  obtain ⟨h, e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  let F : rootSpace H α →ₗ[K] K := killingForm K L f ∘ₗ (rootSpace H α).subtype
  have hF : LinearMap.ker F ≠ ⊥ := F.ker_ne_bot_of_finrank_lt <| by rwa [finrank_self]
  obtain ⟨⟨y, hyα⟩, hy, hy₀⟩ := (Submodule.ne_bot_iff _).mp hF
  replace hy : ⁅y, f⁆ = 0 := by
    have : killingForm K L y f = 0 := by simpa [F, traceForm_comm] using hy
    simpa [this] using lie_eq_killingForm_smul_of_mem_rootSpace_of_mem_rootSpace_neg hyα hfα
  have P : ht.symm.HasPrimitiveVectorWith y (-2 : K) :=
    { ne_zero := by simpa [LieSubmodule.mk_eq_zero] using hy₀
      lie_h := by simp only [neg_smul, neg_lie, ht.h_eq_coroot hα heα hfα,
        ← H.coe_bracket_of_module, lie_eq_smul_of_mem_rootSpace hyα (coroot α),
        root_apply_coroot hα]
      lie_e := by rw [← lie_skew, hy, neg_zero] }
  obtain ⟨n, hn⟩ := P.exists_nat
  assumption_mod_cast

/-- The embedded `sl₂` associated to a root. -/
noncomputable def sl2SubalgebraOfRoot {α : Weight K H L} (hα : α.IsNonZero) :
    LieSubalgebra K L := by
  choose h e f t ht using exists_isSl2Triple_of_weight_isNonZero hα
  exact t.toLieSubalgebra K

lemma mem_sl2SubalgebraOfRoot_iff {α : Weight K H L} (hα : α.IsNonZero) {h e f : L}
    (t : IsSl2Triple h e f) (hte : e ∈ rootSpace H α) (htf : f ∈ rootSpace H (-α)) {x : L} :
    x ∈ sl2SubalgebraOfRoot hα ↔ ∃ c₁ c₂ c₃ : K, x = c₁ • e + c₂ • f + c₃ • ⁅e, f⁆ := by
  simp only [sl2SubalgebraOfRoot, IsSl2Triple.mem_toLieSubalgebra_iff]
  generalize_proofs _ _ _ he hf
  obtain ⟨ce, hce⟩ : ∃ c : K, he.choose = c • e := by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨e, hte⟩ (by simpa using t.e_ne_zero)).mp
      (finrank_rootSpace_eq_one α hα) ⟨_, he.choose_spec.choose_spec.2.1⟩
    exact ⟨c, by simpa using hc.symm⟩
  obtain ⟨cf, hcf⟩ : ∃ c : K, hf.choose = c • f := by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨f, htf⟩ (by simpa using t.f_ne_zero)).mp
      (finrank_rootSpace_eq_one (-α) (by simpa)) ⟨_, hf.choose_spec.2.2⟩
    exact ⟨c, by simpa using hc.symm⟩
  have hce₀ : ce ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hce
    exact he.choose_spec.choose_spec.1.e_ne_zero hce
  have hcf₀ : cf ≠ 0 := by
    rintro rfl
    simp only [zero_smul] at hcf
    exact he.choose_spec.choose_spec.1.f_ne_zero hcf
  simp_rw [hcf, hce]
  refine ⟨fun ⟨c₁, c₂, c₃, hx⟩ ↦ ⟨c₁ * ce, c₂ * cf, c₃ * cf * ce, ?_⟩,
    fun ⟨c₁, c₂, c₃, hx⟩ ↦ ⟨c₁ * ce⁻¹, c₂ * cf⁻¹, c₃ * ce⁻¹ * cf⁻¹, ?_⟩⟩
  · simp [hx, mul_smul]
  · simp [hx, mul_smul, hce₀, hcf₀]

/-- The `sl₂` subalgebra associated to a root, regarded as a Lie submodule over the Cartan
subalgebra. -/
noncomputable def sl2SubmoduleOfRoot {α : Weight K H L} (hα : α.IsNonZero) :
    LieSubmodule K H L where
  __ := sl2SubalgebraOfRoot hα
  lie_mem {h} x hx := by
    suffices ⁅(h : L), x⁆ ∈ sl2SubalgebraOfRoot hα by simpa
    obtain ⟨h', e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
    replace hx : x ∈ sl2SubalgebraOfRoot hα := hx
    obtain ⟨c₁, c₂, c₃, rfl⟩ := (mem_sl2SubalgebraOfRoot_iff hα ht heα hfα).mp hx
    rw [mem_sl2SubalgebraOfRoot_iff hα ht heα hfα, lie_add, lie_add, lie_smul, lie_smul, lie_smul]
    have he_wt : ⁅(h : L), e⁆ = α h • e := lie_eq_smul_of_mem_rootSpace heα h
    have hf_wt : ⁅(h : L), f⁆ = (-α) h • f := lie_eq_smul_of_mem_rootSpace hfα h
    have hef_zero : ⁅(h : L), ⁅e, f⁆⁆ = 0 := by
      suffices h_coroot_in_zero : ⁅e, f⁆ ∈ rootSpace H (0 : H → K) from
        lie_eq_smul_of_mem_rootSpace h_coroot_in_zero h ▸ (zero_smul K ⁅e, f⁆)
      rw [ht.lie_e_f, IsSl2Triple.h_eq_coroot hα ht heα hfα, rootSpace_zero_eq K L H]
      exact (coroot α).property
    exact ⟨c₁ * α h, c₂ * (-α h), 0, by simp [he_wt, hf_wt, hef_zero, smul_smul]⟩

/-- The coroot space of `α` viewed as a submodule of the ambient Lie algebra `L`.
This represents the image of the coroot space under the inclusion `H ↪ L`. -/
noncomputable abbrev corootSubmodule (α : Weight K H L) : LieSubmodule K H L :=
  LieSubmodule.map H.toLieSubmodule.incl (corootSpace α)

open Submodule in
lemma sl2SubmoduleOfRoot_eq_sup (α : Weight K H L) (hα : α.IsNonZero) :
    sl2SubmoduleOfRoot hα = genWeightSpace L α ⊔ genWeightSpace L (-α) ⊔ corootSubmodule α := by
  ext x
  obtain ⟨h', e, f, ht, heα, hfα⟩ := exists_isSl2Triple_of_weight_isNonZero hα
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · replace hx : x ∈ sl2SubalgebraOfRoot hα := hx
    obtain ⟨c₁, c₂, c₃, rfl⟩ := (mem_sl2SubalgebraOfRoot_iff hα ht heα hfα).mp hx
    refine add_mem (add_mem ?_ ?_) ?_
    · exact mem_sup_left <| mem_sup_left <| smul_mem _ _ heα
    · exact mem_sup_left <| mem_sup_right <| smul_mem _ _ hfα
    · suffices ∃ y ∈ corootSpace α, H.subtype y = c₃ • h' from
        mem_sup_right <| by simpa [ht.lie_e_f, -Subtype.exists]
      refine ⟨c₃ • coroot α, smul_mem _ _ <| by simp, ?_⟩
      rw [IsSl2Triple.h_eq_coroot hα ht heα hfα, map_smul, subtype_apply]
  · have aux {β : Weight K H L} (hβ : β.IsNonZero) {y g : L}
        (hy : y ∈ genWeightSpace L β) (hg : g ∈ rootSpace H β) (hg_ne_zero : g ≠ 0) :
        ∃ c : K, y = c • g := by
      obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' ⟨g, hg⟩
        (by rwa [ne_eq, LieSubmodule.mk_eq_zero])).mp (finrank_rootSpace_eq_one β hβ) ⟨y, hy⟩
      exact ⟨c, by simpa using hc.symm⟩
    obtain ⟨x_αneg, hx_αneg, x_h, ⟨y, hy_coroot, rfl⟩, rfl⟩ := mem_sup.mp hx
    obtain ⟨x_pos, hx_pos, x_neg, hx_neg, rfl⟩ := mem_sup.mp hx_αneg
    obtain ⟨c₁, rfl⟩ := aux hα hx_pos heα ht.e_ne_zero
    obtain ⟨c₂, rfl⟩ := aux (Weight.IsNonZero.neg hα) hx_neg hfα ht.f_ne_zero
    obtain ⟨c₃, rfl⟩ : ∃ c₃ : K, c₃ • coroot α = y := by
      simpa [← mem_span_singleton, ← coe_corootSpace_eq_span_singleton α]
    change _ ∈ sl2SubalgebraOfRoot hα
    rw [mem_sl2SubalgebraOfRoot_iff hα ht heα hfα]
    use c₁, c₂, c₃
    simp [ht.lie_e_f, IsSl2Triple.h_eq_coroot hα ht heα hfα, -LieSubmodule.incl_coe]

lemma sl2SubmoduleOfRoot_ne_bot (α : Weight K H L) (hα : α.IsNonZero) :
    sl2SubmoduleOfRoot hα ≠ ⊥ := by
  rw [sl2SubmoduleOfRoot_eq_sup]
  exact ne_bot_of_le_ne_bot α.genWeightSpace_ne_bot (le_sup_of_le_left le_sup_left)

/-- The collection of roots as a `Finset`. -/
noncomputable abbrev _root_.LieSubalgebra.root : Finset (Weight K H L) := {α | α.IsNonZero}

set_option backward.isDefEq.respectTransparency false in
lemma restrict_killingForm_eq_sum :
    (killingForm K L).restrict H = ∑ α ∈ H.root, (α : H →ₗ[K] K).smulRight (α : H →ₗ[K] K) := by
  rw [restrict_killingForm, traceForm_eq_sum_finrank_nsmul' K H L]
  refine Finset.sum_congr rfl fun χ hχ ↦ ?_
  replace hχ : χ.IsNonZero := by simpa [LieSubalgebra.root] using hχ
  simp [finrank_rootSpace_eq_one _ hχ]

end CharZero

end IsKilling

end LieAlgebra
