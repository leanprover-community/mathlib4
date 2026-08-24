/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Jiedong Jiang, Edison Xie
-/
module

public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Algebra.WithZeroTopology

/-!
# Completion of Valuations

This file defines the extension of a valuation on a field `K` to its uniform completion
`Completion K`, assuming the valuation is compatible with the topology on `K`.

## Main definitions

- `Valuation.extension` : extends a valuation on a field `K` to `Completion K`, provided
  the valuation is compatible with the topology on `K`.
- `UniformSpace.Completion.valuativeRel` : the valuative relation on `Completion K`,
  extending the one on `K` that is compatible with the topology.

## Main statements

- `UniformSpace.Completion.isValuativeTopology` : the extended valuative relation on
  `Completion K` is compatible with the topology.
- `Valuation.extension.compatible` : if `v` is compatible with the valuative relation on `K`,
  then `v.extension` is compatible with the valuative relation on `Completion K`.

## TODO

The current approach relies on the field structure of `K`, it can be genralized to
arbitrary commutative rings.

- Upgrade `WithZeroTopology.topologicalSpace` to `WithZeroTopology.uniformSpace`.
- Generalize `Valuation.extension` from fields to arbitrary commutative rings by first
showing that the original valuation is uniformly continuous.
- Split this file into two parts: one about valuation extension in general, and another
  about the theory specific to valued fields (the `DivisionRing` and `Field` sections).
-/

@[expose] public section

open Valuation ValuativeRel IsValuativeTopology UniformSpace MonoidWithZeroHom ValueGroup₀
open Set Filter Topology

variable {R K Γ₀ : Type*}

section DivisionRing

variable [DivisionRing K]

section InversionEstimate

variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

-- The following is the main technical lemma ensuring that inversion is continuous
-- in the topology induced by a valuation on a division ring (i.e. the next instance)
-- and the fact that a valued field is completable
-- [BouAC, VI.5.1 Lemme 1]
theorem Valuation.inversion_estimate {x y : K} {γ : Γ₀ˣ} (y_ne : y ≠ 0)
    (h : v (x - y) < min (γ * (v y * v y)) (v y)) : v (x⁻¹ - y⁻¹) < γ := by
  have veq : v x = v y := Valuation.map_eq_of_sub_lt v (lt_of_lt_of_le h (min_le_right _ _))
  have x_ne : x ≠ 0 := fun _ ↦ by simp_all
  refine lt_of_eq_of_lt ?_ (mul_inv_lt_of_lt_mul₀ (lt_of_lt_of_le h (min_le_left _ _)) :
    v (x - y) * (v y * v y)⁻¹ < ↑γ)
  nth_rw 1 [← veq, mul_inv_rev, mul_comm, mul_assoc, mul_comm]
  simp [← map_inv₀, ← map_mul, mul_sub, sub_mul, v.map_sub_swap, x_ne, y_ne]

theorem Valuation.inversion_estimate' {x y r s : K} (y_ne : y ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (h : v (x - y) < min ((v s / v r) * (v y * v y)) (v y)) : v (x⁻¹ - y⁻¹) * v r < v s := by
  refine (?_ : _ < _).trans_eq <| div_mul_cancel₀ (a := v s) (b := v r) (by simpa using hr)
  grw [Valuation.inversion_estimate v (x := x) y_ne (γ := (.mk0 (v s / v r) (by simp_all))) h]
  <;> simp [zero_lt_iff, hr]

end InversionEstimate

namespace IsValuativeTopology

variable [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]

/-- The topology coming from a valuation on a division ring makes it a topological division ring
[BouAC, VI.5.1 middle of Proposition 1] -/
instance (priority := 100) isTopologicalDivisionRing : IsTopologicalDivisionRing K where
  continuousAt_inv₀ x x_ne s s_in := by
    obtain ⟨γ, hs⟩ := (valuation K).mem_nhds_iff.mp s_in
    rw [mem_map, (valuation K).mem_nhds_iff]
    let γ' := Units.mk0 (Valuation.restrict _ x) ((valuation K).restrict.ne_zero_iff.mpr x_ne)
    refine ⟨min (γ * (γ' * γ')) γ', fun y y_in ↦ hs ?_⟩
    simp only [mem_ofPred_eq, Units.min_val, Units.val_mul] at y_in
    refine inversion_estimate (Γ₀ := (ofClass (valuation K)).ValueGroup₀) _ x_ne ?_
    simpa +zetaDelta using y_in

/-- A division ring with topology coming from a valuation is a Hausdorff space. -/
instance (priority := 100) t2Space : T2Space K := by
  refine IsTopologicalAddGroup.t2Space_of_zero_sep fun x x_ne ↦
    ⟨{ k | valuation K k < valuation K x }, ?_, fun h => lt_irrefl (valuation K x) h⟩
  rw [(valuation K).mem_nhds_iff]
  use Units.mk0 (restrict₀ _ x) ((valuation K).restrict.ne_zero_iff.mpr x_ne)
  intro y hy
  simpa [restrict_lt_iff_lt_embedding] using hy

/-- The restriction of a compatible valuation to its image group is compatible. -/
instance [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [v.Compatible] :
    v.restrict.Compatible where
  vle_iff_le x y := by rw [v.vle_iff_le, restrict_le_iff]

section ContinuousAt

variable [LinearOrderedCommGroupWithZero Γ₀] [TopologicalSpace Γ₀] (v : Valuation K Γ₀)
  [v.Compatible]

/-- A compatible valuation is locally constant, hence continuous, at every point where it does
not vanish, for any topology on `Γ₀`. -/
theorem continuousAt_valuation_of_ne_zero {x : K} (h : v x ≠ 0) : ContinuousAt v x :=
  Filter.EventuallyEq.continuousAt (y := v x) (v.locally_const h)

end ContinuousAt

section WithZeroTopology

open WithZeroTopology

variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [v.Compatible]

/-- For `y : K` with `v y ≠ 0`, the open ball `{x | v x < v y}` is a neighbourhood of `0`. -/
theorem eventually_lt_nhds_zero {y : K} (hy : v y ≠ 0) : ∀ᶠ x in 𝓝 (0 : K), v x < v y :=
  (v.mem_nhds_zero_iff _).2
    ⟨Units.mk0 _ (mt v.restrict_eq_zero_iff.1 hy), fun _ hx ↦ v.restrict_lt_iff.1 hx⟩

theorem continuous_valuation_of_surjective (hsurj : Function.Surjective v) : Continuous v := by
  refine continuous_iff_continuousAt.2 fun x ↦ (eq_or_ne x 0).casesOn ?_ fun h ↦
    continuousAt_valuation_of_ne_zero _ (v.ne_zero_iff.2 h)
  rintro rfl
  rw [continuousAt_def', map_zero, WithZeroTopology.tendsto_zero]
  exact fun γ hγ ↦ (hsurj γ).choose_spec ▸ eventually_lt_nhds_zero v <| (hsurj γ).choose_spec ▸ hγ

theorem continuous_restrict : Continuous (v.restrict : K → (ValueGroup₀ (.ofClass v))) :=
  continuous_valuation_of_surjective v.restrict (restrict₀_surjective _)

lemma valuation_isClosedMap :
    IsClosedMap (v.restrict : K → (ValueGroup₀ (.ofClass v))) := by
  refine IsClosedMap.of_nonempty fun U hU hU' ↦ ?_
  simp only [← isOpen_compl_iff, isOpen_iff_mem_nhds, mem_compl_iff, v.mem_nhds_iff,
    subset_compl_comm, compl_ofPred, not_lt] at hU
  simp only [isClosed_iff, mem_image, map_eq_zero, exists_eq_right, ne_eq, image_subset_iff]
  refine (em _).imp_right fun h ↦ ?_
  obtain ⟨γ, h⟩ := hU _ h
  simp only [sub_zero] at h
  refine ⟨γ.1, γ.ne_zero, h.trans fun h ↦ ?_⟩
  simp

end WithZeroTopology

end IsValuativeTopology

end DivisionRing

section Field

variable [Field K] [ValuativeRel K] [UniformSpace K] [IsValuativeTopology K]

namespace IsValuativeTopology

/-- A valued field is completable. -/
instance (priority := 100) [IsUniformAddGroup K] : CompletableTopField K where
  __ := (inferInstance : T0Space K)
  nice F hF h0 := by
    obtain ⟨γ₀, M₀, M₀_in, H₀⟩ : ∃ γ₀ : (ValueGroup₀ (.ofClass (valuation K)))ˣ, ∃ M ∈ F,
        ∀ x ∈ M, (γ₀.1) ≤ (valuation K).restrict x := by
      rcases inf_eq_bot_iff.mp h0 with ⟨U, U_in, M, M_in, H⟩
      rcases ((valuation K).mem_nhds_zero_iff _).mp U_in with ⟨γ₀, hU⟩
      exact ⟨γ₀, M, M_in, fun x xM ↦ le_of_not_gt (fun hyp ↦ Set.mem_empty_iff_false x|>.1 <| H ▸
        ⟨mem_of_subset_of_mem hU hyp, ‹_›⟩)⟩
    rw [(valuation K).cauchy_iff] at hF ⊢
    refine ⟨hF.1.map _, fun γ ↦ ?_⟩
    rcases hF.2 (min (γ * γ₀ * γ₀) γ₀) with ⟨M₁, M₁_in, H₁⟩
    refine ⟨(fun x : K => x⁻¹) '' (M₀ ∩ M₁), by simp_all [-Filter.map_inv], ?_⟩
    rintro _ ⟨x, ⟨x_in₀, x_in₁⟩, rfl⟩ _ ⟨y, ⟨_, y_in₁⟩, rfl⟩
    refine inversion_estimate _ ((valuation K).restrict.ne_zero_iff.mp fun h ↦ ?_) ?_
    · simpa [h] using H₀ x x_in₀
    · refine lt_of_lt_of_le (H₁ x x_in₁ y y_in₁) ?_
      grw [Units.min_val, mul_assoc, Units.val_mul, Units.val_mul, H₀ x x_in₀]

end IsValuativeTopology

namespace Valuation

variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [v.Compatible]

open WithZeroTopology

/-- The extension of the valuation of a valued field to the completion of the field. -/
noncomputable def extensionFun : Completion K → ValueGroup₀ (.ofClass v) :=
  Completion.isDenseInducing_coe.extend v.restrict

@[simp, norm_cast]
theorem extensionFun_extends (x : K) : v.extensionFun (x : Completion K) = v.restrict x := by
  refine Completion.isDenseInducing_coe.extend_eq_of_tendsto ?_
  rw [← Completion.isDenseInducing_coe.nhds_eq_comap]
  exact (continuous_restrict v).continuousAt

variable [IsUniformAddGroup K]

/-- For a nonzero element `x₀` of the completion of `K`, the valuation `v` is constant on the
elements of `K` close to `x₀`, with value `v z₀` for any `z₀ : K` close enough to `x₀`. -/
theorem exists_eventually_map_eq {x₀ : Completion K} (hx₀ : x₀ ≠ 0) :
    ∃ z₀ : K, z₀ ≠ 0 ∧ ∀ᶠ x in Filter.comap ((↑) : K → Completion K) (𝓝 x₀), v x = v z₀ := by
  -- the open set `{x | v x = 1}` of `K` is the preimage of an open set `W` of the completion
  obtain ⟨W, hW, hW₁⟩ : ∃ W : Set (Completion K), IsOpen W ∧
      ∀ x : K, (x : Completion K) ∈ W ↔ v x = 1 := by
    simpa [Set.ext_iff] using
      Completion.isDenseInducing_coe.isInducing.isOpen_iff.1 (v.isOpen_sphere one_ne_zero)
  -- the open set `{z | z ≠ 0 ∧ x₀ * z⁻¹ ∈ W}` contains `x₀`, hence contains some `z₀ : K`
  obtain ⟨z₀, hz₀, hz₀'⟩ : ∃ z₀ : K, z₀ ≠ 0 ∧ x₀ * (z₀ : Completion K)⁻¹ ∈ W := by
    simpa [← Completion.coe_zero] using Completion.denseRange_coe.exists_mem_open
      ((continuousOn_const.mul continuousOn_inv₀).isOpen_inter_preimage isOpen_compl_singleton hW)
      ⟨x₀, hx₀, by simpa [hx₀, Completion.coe_one] using (hW₁ 1).2 (map_one v)⟩
  -- for `x : K` in the open neighbourhood `(· * z₀⁻¹) ⁻¹' W` of `x₀`, `v (x * z₀⁻¹) = 1`
  refine ⟨z₀, hz₀, Filter.mem_of_superset (Filter.preimage_mem_comap
    ((hW.preimage (continuous_id.mul continuous_const)).mem_nhds hz₀')) fun x hx ↦
    (mul_inv_eq_one₀ (v.ne_zero_iff.2 hz₀)).1 ?_⟩
  rwa [← map_inv₀, ← map_mul, ← hW₁, Completion.coe_mul, ← Completion.coe_inv]

theorem continuous_extensionFun : Continuous v.extensionFun := by
  refine Completion.isDenseInducing_coe.continuous_extend fun x₀ ↦ ?_
  rcases eq_or_ne x₀ 0 with rfl | h
  · refine ⟨0, ?_⟩
    rw [← Completion.coe_zero, ← Completion.isDenseInducing_coe.nhds_eq_comap]
    exact (continuous_restrict v).tendsto' 0 0 (map_zero v.restrict)
  · obtain ⟨z₀, -, hz₀⟩ := v.exists_eventually_map_eq h
    exact ⟨_, tendsto_const_nhds.congr' (hz₀.mono fun x hx ↦ (v.restrict_inj.2 hx).symm)⟩

/-- the extension of a valuation on a division ring to its completion. -/
noncomputable def extension : Valuation (Completion K) Γ₀ where
  toFun := ValueGroup₀.embedding ∘ v.extensionFun
  map_zero' := by
    rw [Function.comp_apply, map_eq_zero, ← v.restrict.map_zero (R := K),
      ← v.extensionFun_extends (0 : K), Completion.coe_zero]
  map_one' := by
    rw [Function.comp_apply, ← Completion.coe_one, v.extensionFun_extends (1 : K),
      Valuation.map_one _, map_one]
  map_mul' x y := by
    simp only [Function.comp_apply, ← map_mul]
    rw [embedding_strictMono.injective.eq_iff]
    apply Completion.induction_on₂ x y
      (p := fun x y => v.extensionFun (x * y) = v.extensionFun x * v.extensionFun y)
    · have c1 : Continuous fun x : Completion K × Completion K => v.extensionFun (x.1 * x.2) :=
        v.continuous_extensionFun.comp (continuous_fst.mul continuous_snd)
      have c2 : Continuous fun x : Completion K × Completion K =>
          v.extensionFun x.1 * v.extensionFun x.2 :=
        (v.continuous_extensionFun.comp continuous_fst).mul
          (v.continuous_extensionFun.comp continuous_snd)
      exact isClosed_eq c1 c2
    · intro x y
      norm_cast
      exact Valuation.map_mul _ _ _
  map_add_le_max' x y := by
    simp_rw [le_max_iff, Function.comp_apply]
    rw [embedding_strictMono.le_iff_le, embedding_strictMono.le_iff_le (f := embedding)]
    apply Completion.induction_on₂ x y (p := fun x y => v.extensionFun (x + y)
      ≤ v.extensionFun x ∨ v.extensionFun (x + y) ≤ v.extensionFun y)
    · have cont : Continuous v.extensionFun := v.continuous_extensionFun
      exact (isClosed_le (by fun_prop) <| cont.comp continuous_fst).union
          (isClosed_le (by fun_prop) <| cont.comp continuous_snd)
    · intro x y
      norm_cast
      exact le_max_iff.mp (v.restrict.map_add x y)

lemma extension_def (x : Completion K) : v.extension x =
    embedding (v.extensionFun x) := rfl

lemma extension_ofClass_apply {x : Completion K} :
    (MonoidWithZeroHom.ofClass v.extension) x = embedding (v.extensionFun x) := rfl

@[simp]
lemma extension_apply_coe (x : K) :
    v.extension (x : Completion K) = v x := by
  simp [extension_def]

@[simp]
lemma extensionFun_eq_zero_iff {x : Completion K} : v.extensionFun x = 0 ↔ x = 0 := by
  suffices v.extension x = 0 ↔ x = 0 by
    simpa only [extension_def, map_eq_zero]
  rw [Valuation.zero_iff]

lemma extension_le_iff_extensionFun_le {x y : Completion K} :
    v.extension x ≤ v.extension y ↔ v.extensionFun x ≤ v.extensionFun y :=
  embedding_strictMono (f := ofClass v).le_iff_le

/-- The extension of `v` to the completion of `K` is locally constant away from `0`. -/
lemma extension_locally_const {x : Completion K} (h : x ≠ 0) :
    { y | v.extension y = v.extension x } ∈ 𝓝 x :=
  Filter.mem_of_superset (v.continuous_extensionFun.continuousAt.preimage_mem_nhds
    (WithZeroTopology.singleton_mem_nhds_of_ne_zero (v.extensionFun_eq_zero_iff.not.2 h)))
    fun _ hy ↦ congrArg embedding hy

/-- Every neighbourhood of `x` in the completion of `K` contains an element `r` of `K` with
`v r = v.extension x`. -/
lemma exists_coe_mem_extension_eq {x : Completion K} {U : Set (Completion K)} (hU : U ∈ 𝓝 x) :
    ∃ r : K, (r : Completion K) ∈ U ∧ v.extension x = v r := by
  rcases eq_or_ne x 0 with rfl | h
  · exact ⟨0, by rw [Completion.coe_zero]; exact mem_of_mem_nhds hU, by simp⟩
  · obtain ⟨r, hr, hr' : v.extension _ = v.extension x⟩ :=
      Completion.denseRange_coe.mem_nhds (inter_mem hU (v.extension_locally_const h))
    exact ⟨r, hr, by simpa using hr'.symm⟩

/-- Every neighbourhood of `(x, y)` in the completion of `K` contains a pair `(r, s)` of elements
of `K` with `v r = v.extension x` and `v s = v.extension y`. -/
lemma exists_coe_mem_extension_eq₂ {x y : Completion K} {U : Set (Completion K × Completion K)}
    (hU : U ∈ 𝓝 (x, y)) : ∃ r s : K, ((r : Completion K), (s : Completion K)) ∈ U ∧
      v.extension x = v r ∧ v.extension y = v s := by
  obtain ⟨V, hV, W, hW, hVW⟩ := mem_nhds_prod_iff.1 hU
  obtain ⟨r, hr, hvr⟩ := v.exists_coe_mem_extension_eq hV
  obtain ⟨s, hs, hvs⟩ := v.exists_coe_mem_extension_eq hW
  exact ⟨r, s, hVW ⟨hr, hs⟩, hvr, hvs⟩

lemma exists_coe_eq_map (x : Completion K) : ∃ r : K, v.extension x = v r :=
  (v.exists_coe_mem_extension_eq univ_mem).imp fun _ ↦ And.right

lemma closure_image_coe_le : closure ((Prod.map (↑) (↑)) '' {(x, y) : K × K | v x ≤ v y}) =
    {(x, y) | v.extension x ≤ v.extension y} := by
  apply subset_antisymm
  · rw [IsClosed.closure_subset_iff]
    · simp
    · simpa [extension_le_iff_extensionFun_le] using OrderClosedTopology.isClosed_le'.preimage
        (v.continuous_extensionFun.prodMap v.continuous_extensionFun)
  · rintro ⟨x, y⟩ h
    rw [mem_closure_iff_nhds]
    intro U hU
    obtain ⟨r, s, hU, hvr, hvs⟩ := v.exists_coe_mem_extension_eq₂ hU
    exact ⟨(r, s), hU, (r, s), by simpa [hvr, hvs] using h, rfl⟩

-- Bourbaki CA VI §5 no.3 Proposition 5 (d)
theorem closure_coe_completion_v_lt {r : Γ₀} (hr : r ≠ 0) :
    closure ((↑) '' { x : K | v x < r }) =
    { x : Completion K | v.extension x < r } := by
  ext x
  simp only [mem_ofPred_eq, mem_closure_iff_nhds]
  refine ⟨fun hx ↦ ?_, fun hx t ht ↦ ?_⟩
  · rcases eq_or_ne x 0 with rfl | h
    · simp [zero_lt_iff, hr]
    · obtain ⟨_, hy : v.extension _ = v.extension x, y, hy' : v y < r, rfl⟩ :=
        hx _ (v.extension_locally_const h)
      rwa [← hy, extension_apply_coe]
  · obtain ⟨y, hy, hy'⟩ := v.exists_coe_mem_extension_eq ht
    exact ⟨y, hy, y, by simpa [← hy'] using hx, rfl⟩

theorem closure_coe_completion_v_mul_v_lt {r s : K} (hr : r ≠ 0) (hs : s ≠ 0) :
    closure ((↑) '' { x : K | v x * v r < v s }) =
    { x : Completion K | v.extension x * v r < v s } := by
  have hrs : v s / v r ≠ 0 := by simp [hr, hs]
  convert v.closure_coe_completion_v_lt hrs using 3
  all_goals simp [← lt_div_iff₀, zero_lt_iff, hr]

/-- The function underlying `Valuation.valueGroup₀ExtensionHom`: it sends `v.restrict x` to
`v.extension.restrict x` for `x : K`. It is characterised by
`Valuation.embedding_valueGroup₀ExtensionHomFun`. -/
noncomputable def valueGroup₀ExtensionHomFun (a : ValueGroup₀ (.ofClass v)) :
    ValueGroup₀ (.ofClass v.extension) :=
  v.extension.restrict (Function.surjInv (restrict₀_surjective (.ofClass v)) a : K)

@[simp]
theorem embedding_valueGroup₀ExtensionHomFun (a : ValueGroup₀ (.ofClass v)) :
    embedding (v.valueGroup₀ExtensionHomFun a) = embedding a := by
  rw [valueGroup₀ExtensionHomFun, embedding_restrict, extension_apply_coe, ← v.embedding_restrict,
    v.restrict_def, Function.surjInv_eq (restrict₀_surjective (.ofClass v)) a]

/-- The zero-preserving monoid homomorphism from the `ValueGroup₀` of the valuation on `K` to
that of the extension to its completion. -/
noncomputable def valueGroup₀ExtensionHom :
    ValueGroup₀ (.ofClass v) →*₀ ValueGroup₀ (.ofClass v.extension) where
  toFun := v.valueGroup₀ExtensionHomFun
  map_zero' := embedding_injective (by simp)
  map_one' := embedding_injective (by simp)
  map_mul' _ _ := embedding_injective (by simp)

@[simp]
theorem embedding_valueGroup₀ExtensionHom (a : ValueGroup₀ (.ofClass v)) :
    embedding (v.valueGroup₀ExtensionHom a) = embedding a :=
  v.embedding_valueGroup₀ExtensionHomFun a

@[simp]
theorem valueGroup₀ExtensionHom_restrict (x : K) :
    v.valueGroup₀ExtensionHom (v.restrict x) = v.extension.restrict x :=
  embedding_injective (by simp)

/-- The isomorphism from the `ValueGroup₀` of the valuation on `K` to that of the extension to
its completion. -/
noncomputable def valueGroup₀ExtensionEquiv :
    ValueGroup₀ (.ofClass v) ≃* ValueGroup₀ (.ofClass v.extension) :=
  MulEquiv.ofBijective v.valueGroup₀ExtensionHom
    ⟨fun _ _ h ↦ embedding_injective (by simpa using congrArg embedding h), fun y ↦ by
      obtain ⟨z, rfl⟩ := restrict₀_surjective (.ofClass v.extension) y
      obtain ⟨r, hr⟩ := v.exists_coe_eq_map z
      exact ⟨v.restrict r, embedding_injective (by simp [hr])⟩⟩

@[simp]
theorem embedding_valueGroup₀ExtensionEquiv (a : ValueGroup₀ (.ofClass v)) :
    embedding (v.valueGroup₀ExtensionEquiv a) = embedding a :=
  v.embedding_valueGroup₀ExtensionHom a

@[simp]
theorem embedding_valueGroup₀ExtensionEquiv_symm (a : ValueGroup₀ (.ofClass v.extension)) :
    embedding (v.valueGroup₀ExtensionEquiv.symm a) = embedding a := by
  rw [← v.embedding_valueGroup₀ExtensionEquiv, MulEquiv.apply_symm_apply]

/-- `Valuation.closure_coe_completion_v_lt`, stated for the open balls of `v.restrict`. -/
theorem closure_coe_ball_restrict (γ : (ValueGroup₀ (.ofClass v))ˣ) :
    closure ((↑) '' { x : K | v.restrict x < γ.1 }) =
      { x : Completion K | v.extension x < embedding γ.1 } := by
  rw [show { x : K | v.restrict x < γ.1 } = { x : K | v x < embedding γ.1 } from
    Set.ext fun _ ↦ v.restrict_lt_iff_lt_embedding]
  exact v.closure_coe_completion_v_lt (by simp)

/-- The neighbourhoods of `0` in the completion of `K` have a basis given by the open balls of
`v.extension.restrict`. This is `Valuation.hasBasis_nhds_zero` for `v.extension`, proved before
the instance `IsValuativeTopology (Completion K)` is available. -/
theorem extension_hasBasis_nhds_zero :
    (𝓝 (0 : Completion K)).HasBasis (fun _ ↦ True)
      fun γ : (ValueGroup₀ (.ofClass v.extension))ˣ ↦ { x | v.extension.restrict x < γ.1 } := by
  have h := v.hasBasis_nhds_zero.hasBasis_of_isDenseInducing Completion.isDenseInducing_coe
  rw [Completion.coe_zero] at h
  simp only [closure_coe_ball_restrict] at h
  refine h.to_hasBasis (fun γ _ ↦ ⟨Units.mk0 (v.valueGroup₀ExtensionEquiv γ.1) (by simp),
      trivial, fun x hx ↦ ?_⟩) fun γ _ ↦ ⟨Units.mk0 (v.valueGroup₀ExtensionEquiv.symm γ.1)
      (by simp), trivial, fun x hx ↦ ?_⟩
  · simpa [v.extension.restrict_lt_iff_lt_embedding] using hx
  · exact v.extension.restrict_lt_iff_lt_embedding.2 (by simpa using hx)

end Valuation

section Completion

variable [IsUniformAddGroup K]

noncomputable instance UniformSpace.Completion.valuativeRel : ValuativeRel (Completion K) :=
  .ofValuation (ValuativeRel.valuation K).extension

instance Valuation.extension.compatible' :
    (ValuativeRel.valuation K).extension.Compatible := Valuation.Compatible.ofValuation _

@[simp]
theorem UniformSpace.Completion.vle_iff_vle {x y : K} :
    (x : Completion K) ≤ᵥ (y : Completion K) ↔ x ≤ᵥ y :=
  calc
    _ ↔ (valuation K).extension x ≤ (valuation K).extension y := vle_iff_le _
    _ ↔ valuation K x ≤ valuation K y := by simp
    _ ↔ x ≤ᵥ y := (vle_iff_le _).symm

@[simp]
theorem UniformSpace.Completion.extension_veq_extension_iff {x y : K} :
    (x : Completion K) =ᵥ (y : Completion K) ↔ x =ᵥ y :=
  Iff.and vle_iff_vle vle_iff_vle

@[simp]
theorem UniformSpace.Completion.extension_vlt_extension_iff {x y : K} :
    (x : Completion K) <ᵥ (y : Completion K) ↔ x <ᵥ y :=
  Iff.not vle_iff_vle

instance UniformSpace.Completion.valuativeExtension : ValuativeExtension K (Completion K) where
  vle_iff_vle _ _ := vle_iff_vle

variable {Γ₀ Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ₀'] (v : Valuation K Γ₀) [v.Compatible]
  (v' : Valuation K Γ₀') [v'.Compatible]

instance UniformSpace.Completion.isValuativeTopology : IsValuativeTopology (Completion K) :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle (valuation K).extension fun {s} ↦ by
    simpa only [true_and] using (valuation K).extension_hasBasis_nhds_zero.mem_iff

theorem Valuation.extension.isEquiv : v.extension.IsEquiv v'.extension := by
  have h := v.closure_image_coe_le
  rw [show {(x, y) : K × K | v x ≤ v y} = {(x, y) : K × K | v' x ≤ v' y} from
    Set.ext fun ⟨_, _⟩ ↦ ValuativeRel.isEquiv v v' _ _, v'.closure_image_coe_le] at h
  exact fun x y ↦ (Set.ext_iff.1 h (x, y)).symm

instance Valuation.extension.compatible : v.extension.Compatible := by
  apply IsEquiv.compatible (v₁ := (valuation K).extension)
  exact Valuation.extension.isEquiv _ _

lemma extension_surjective_iff :
    Function.Surjective (v.extension : Completion K → Γ₀) ↔
      Function.Surjective (v : K → Γ₀) := by
  refine ⟨fun h γ ↦ ?_, fun h γ ↦ ?_⟩
  · obtain ⟨a, rfl⟩ := h γ
    exact (v.exists_coe_eq_map a).imp fun _ ↦ Eq.symm
  · obtain ⟨a, ha⟩ := h γ
    exact ⟨a, by simp [ha]⟩

instance {R : Type*} [CommSemiring R] [Algebra R K] [UniformContinuousConstSMul R K]
    [FaithfulSMul R K] : FaithfulSMul R (Completion K) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact (FaithfulSMul.algebraMap_injective K _).comp (FaithfulSMul.algebraMap_injective R K)

end Completion

end Field
