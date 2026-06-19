/-
Copyright (c) 2026 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Jiedong Jiang
-/
module

public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
public import Mathlib.Topology.Algebra.WithZeroTopology
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Topology.Algebra.Valued.ValuativeRel
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic
public import Mathlib.Tactic.Widget.GCongr

/-!
# Completion of Valuations

Let `R` be a ring equipped with a valuation `v` and the topology defined by the
valuation. We can define the completion of `R` with respect to this topology

We first show that `K` is a topological field, i.e. inversion is continuous
at every non-zero element.

In this file, we define the extension of valuation to its completion.


## TODO
Generalize the completion of valuation to arbitary commutative rings. One
may first define the uniform space structure on the value group and show
that the valuation is uniformly continuous. After this genralization, one can
decompose the file into two, the first about valuation extension, the
second about theory specific to valued field (section `DivisionRing` and `Field`).

-- rename everything....

- Completion of valuation
- Completion of valuative relation
- compatibility IsValuativeTopology
- compatibility Valuation.Compatible

Valued Field should be in another file. Completabletopfield,
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
  have hyp1 : v (x - y) < γ * (v y * v y) := lt_of_lt_of_le h (min_le_left _ _)
  have hyp1' : v (x - y) * (v y * v y)⁻¹ < γ := mul_inv_lt_of_lt_mul₀ hyp1
  have hyp2 : v (x - y) < v y := lt_of_lt_of_le h (min_le_right _ _)
  have key : v x = v y := Valuation.map_eq_of_sub_lt v hyp2
  have x_ne : x ≠ 0 := by
    intro h
    apply y_ne
    rw [h, v.map_zero] at key
    exact v.zero_iff.1 key.symm
  have decomp : x⁻¹ - y⁻¹ = x⁻¹ * (y - x) * y⁻¹ := by
    rw [mul_sub_left_distrib, sub_mul, mul_assoc, show y * y⁻¹ = 1 from mul_inv_cancel₀ y_ne,
      show x⁻¹ * x = 1 from inv_mul_cancel₀ x_ne, mul_one, one_mul]
  calc
    v (x⁻¹ - y⁻¹) = v (x⁻¹ * (y - x) * y⁻¹) := by rw [decomp]
    _ = v x⁻¹ * (v <| y - x) * v y⁻¹ := by repeat' rw [Valuation.map_mul]
    _ = (v x)⁻¹ * (v <| y - x) * (v y)⁻¹ := by rw [map_inv₀, map_inv₀]
    _ = (v <| y - x) * (v y * v y)⁻¹ := by rw [mul_assoc, mul_comm, key, mul_assoc, mul_inv_rev]
    _ = (v <| y - x) * (v y * v y)⁻¹ := rfl
    _ = (v <| x - y) * (v y * v y)⁻¹ := by rw [Valuation.map_sub_swap]
    _ < γ := hyp1'

theorem Valuation.inversion_estimate' {x y r s : K} (y_ne : y ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (h : v (x - y) < min ((v s / v r) * (v y * v y)) (v y)) : v (x⁻¹ - y⁻¹) * v r < v s := by
  have hr' : 0 < v r := by simp [zero_lt_iff, hr]
  let γ : Γ₀ˣ := .mk0 (v s / v r) (by simp [hs, hr])
  calc
    v (x⁻¹ - y⁻¹) * v r < γ * v r := by gcongr; exact Valuation.inversion_estimate v y_ne h
    _ = v s := div_mul_cancel₀ _ (by simpa)

end InversionEstimate

namespace IsValuativeTopology

variable [ValuativeRel K] [TopologicalSpace K] [IsValuativeTopology K]

/-- The topology coming from a valuation on a division ring makes it a topological division ring
[BouAC, VI.5.1 middle of Proposition 1] -/
instance (priority := 100) isTopologicalDivisionRing :
    IsTopologicalDivisionRing K :=
  { (by infer_instance : IsTopologicalRing K) with
    continuousAt_inv₀ x x_ne s s_in := by
      obtain ⟨γ, hs⟩ := (valuation K).mem_nhds_iff.mp s_in; clear s_in
      rw [mem_map, (valuation K).mem_nhds_iff]
      let γ' := Units.mk0 ((restrict₀ _) x) ((valuation K).restrict.ne_zero_iff.mpr x_ne)
      use min (γ * (γ' * γ')) γ'
      intro y y_in
      apply hs
      simp only [mem_setOf_eq, Units.min_val, Units.val_mul] at y_in
      exact inversion_estimate _ x_ne y_in }

/-- A division ring with topology coming from a valuation is a Hausdorff space. -/
instance (priority := 100) t2Space : T2Space K := by
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x x_ne
  refine ⟨{ k | valuation K k < valuation K x }, ?_, fun h => lt_irrefl (valuation K x) h⟩
  rw [(valuation K).mem_nhds_iff]
  set γ' := Units.mk0 (restrict₀ _ x) ((valuation K).restrict.ne_zero_iff.mpr x_ne) with hdef
  exact ⟨γ', fun y hy => by
    simp only [restrict_lt_iff_lt_embedding, hdef, sub_zero, Units.val_mk0,
      mem_setOf_eq, embedding_restrict₀] at hy
    simpa using hy⟩

section WithZeroTopology

open WithZeroTopology

-- variable [CommRing R] [TopologicalSpace R] [ValuativeRel R]
--   [TopologicalSpace R] [IsValuativeTopology R]
variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [v.Compatible]

theorem continuous_restrict : Continuous (v.restrict : K → (ValueGroup₀ (.ofClass v))) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with (rfl | h)
  · rw [ContinuousAt, map_zero, WithZeroTopology.tendsto_zero]
    intro γ hγ
    rw [Filter.Eventually, v.mem_nhds_zero_iff]
    use Units.mk0 γ hγ; rfl
  · have v_ne : (v.restrict x : ValueGroup₀ (.ofClass v)) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr h
    rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero v_ne]
    simp_rw [v.restrict_inj]
    apply v.locally_const (by simpa [restrict₀_apply] using v_ne)

theorem continuous_valuation_of_surjective (hsurj : Function.Surjective v) :
    Continuous v := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with (rfl | h)
  · rw [ContinuousAt, map_zero, WithZeroTopology.tendsto_zero]
    intro γ hγ
    rw [Filter.Eventually, v.mem_nhds_zero_iff]
    obtain ⟨x, hx⟩ := hsurj γ
    use Units.mk0 (restrict₀ (.ofClass v) x) (by simp [restrict₀_apply, hx, hγ])
    simp only [Units.val_mk0, setOf_subset_setOf, ← v.restrict_def, Valuation.restrict_lt_iff, hx,
      imp_self, implies_true]
  · have h0 : v x ≠ 0 := (Valuation.ne_zero_iff _).mpr h
    rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero h0]
    exact v.locally_const (by simpa using h0)

lemma valuation_isClosedMap :
    IsClosedMap (v.restrict : K → (ValueGroup₀ (.ofClass v))) := by
  refine IsClosedMap.of_nonempty ?_
  intro U hU hU'
  simp only [← isOpen_compl_iff, isOpen_iff_mem_nhds, mem_compl_iff, v.mem_nhds_iff,
    subset_compl_comm, compl_setOf, not_lt] at hU
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
    have : ∃ γ₀ : (ValueGroup₀ (.ofClass (valuation K)))ˣ, ∃ M ∈ F,
        ∀ x ∈ M, (γ₀.1) ≤ (valuation K).restrict x := by
      rcases inf_eq_bot_iff.mp h0 with ⟨U, U_in, M, M_in, H⟩
      rcases ((valuation K).mem_nhds_zero_iff _).mp U_in with ⟨γ₀, hU⟩
      refine ⟨γ₀, M, M_in, fun x xM ↦ le_of_not_gt (fun hyp ↦ ?_)⟩
      have : x ∈ U ∩ M := ⟨hU hyp, xM⟩
      rwa [H] at this
    rcases this with ⟨γ₀, M₀, M₀_in, H₀⟩
    rw [(valuation K).cauchy_iff] at hF ⊢
    refine ⟨hF.1.map _, fun γ ↦ ?_⟩
    rcases hF.2 (min (γ * γ₀ * γ₀) γ₀) with ⟨M₁, M₁_in, H₁⟩
    refine ⟨(fun x : K => x⁻¹) '' (M₀ ∩ M₁), ?_, ?_⟩
    · rw [mem_map]
      exact mem_of_superset (inter_mem M₀_in M₁_in) (subset_preimage_image _ _)
    · rintro _ ⟨x, ⟨x_in₀, x_in₁⟩, rfl⟩ _ ⟨y, ⟨_, y_in₁⟩, rfl⟩
      apply inversion_estimate
      · refine (valuation K).restrict.ne_zero_iff.mp fun h ↦ ?_
        simpa [h] using H₀ x x_in₀
      · refine lt_of_lt_of_le (H₁ x x_in₁ y y_in₁) ?_
        grw [Units.min_val, mul_assoc, Units.val_mul, Units.val_mul, H₀ x x_in₀]

end IsValuativeTopology

namespace Valuation

variable [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀) [v.Compatible]

open WithZeroTopology

/-- The extension of the valuation of a valued field to the completion of the field. -/
noncomputable def extension : Completion K → ValueGroup₀ (.ofClass v) :=
  Completion.isDenseInducing_coe.extend v.restrict

@[simp, norm_cast]
theorem extension_extends (x : K) : v.extension (x : Completion K) = v.restrict x := by
  refine Completion.isDenseInducing_coe.extend_eq_of_tendsto ?_
  rw [← Completion.isDenseInducing_coe.nhds_eq_comap]
  exact (continuous_restrict v).continuousAt

variable [IsUniformAddGroup K]

theorem continuous_extension : Continuous v.extension := by
  refine Completion.isDenseInducing_coe.continuous_extend ?_
  intro x₀
  rcases eq_or_ne x₀ 0 with (rfl | h)
  · refine ⟨0, ?_⟩
    rw [← Completion.coe_zero, ← Completion.isDenseInducing_coe.isInducing.nhds_eq_comap]
    exact (continuous_restrict v).tendsto' 0 0 (map_zero v.restrict)
  · have preimage_one : v ⁻¹' {(1 : Γ₀)} ∈ 𝓝 (1 : K) := by
      have : (v (1 : K) : Γ₀) ≠ 0 := by
        rw [Valuation.map_one]
        exact zero_ne_one.symm
      convert! v.locally_const this
      ext x
      rw [Valuation.map_one, mem_preimage, mem_singleton_iff, mem_setOf_eq]
    obtain ⟨V, V_in, hV⟩ : ∃ V ∈ 𝓝 1,
        ∀ x : K, (x : Completion K) ∈ V → v x = 1 := by
      rwa [Completion.isDenseInducing_coe.nhds_eq_comap, mem_comap] at preimage_one
    have : ∃ V' ∈ 𝓝 1, 0 ∉ V' ∧ ∀ x (_ : x ∈ V') y (_ : y ∈ V'),
        x * y⁻¹ ∈ V := by
      have : Tendsto (fun p : Completion K × Completion K => p.1 * p.2⁻¹)
          ((𝓝 1) ×ˢ (𝓝 1)) (𝓝 1) := by
        rw [← nhds_prod_eq]
        conv =>
          congr
          rfl
          rfl
          rw [← one_mul (1 : Completion K)]
        refine Tendsto.mul continuous_fst.continuousAt (Tendsto.comp ?_ continuous_snd.continuousAt)
        convert! (continuousAt_inv₀ (zero_ne_one.symm : 1 ≠ (0 : Completion K))).tendsto
        exact inv_one.symm
      rcases tendsto_prod_self_iff.mp this V V_in with ⟨U, U_in, hU⟩
      let hatKstar := ({0}ᶜ : Set <| Completion K)
      have : hatKstar ∈ 𝓝 1 := compl_singleton_mem_nhds zero_ne_one.symm
      exact ⟨U ∩ hatKstar, Filter.inter_mem U_in this,
        ⟨fun ⟨_, h'⟩ ↦ h' rfl, fun x ⟨hx, _⟩ y ⟨hy, _⟩ ↦ hU _ _  hx hy⟩⟩
    rcases this with ⟨V', V'_in, zeroV', hV'⟩
    have nhds_right : (fun x => x * x₀) '' V' ∈ 𝓝 x₀ := by
      have l : Function.LeftInverse (fun x => x * x₀⁻¹) fun x => x * x₀ := by
        intro x
        simp only [mul_assoc, mul_inv_cancel₀ h, mul_one]
      have r : Function.RightInverse (fun x => x * x₀⁻¹) fun x => x * x₀ := by
        intro x
        simp only [mul_assoc, inv_mul_cancel₀ h, mul_one]
      have c : Continuous fun x => x * x₀⁻¹ := by fun_prop
      rw [image_eq_preimage_of_inverse l r]
      rw [← mul_inv_cancel₀ h] at V'_in
      exact c.continuousAt V'_in
    have : ∃ z₀ : K, ∃ y₀ ∈ V', ↑z₀ = y₀ * x₀ ∧ z₀ ≠ 0 := by
      rcases Completion.denseRange_coe.mem_nhds nhds_right with ⟨z₀, y₀, y₀_in, H : y₀ * x₀ = z₀⟩
      refine ⟨z₀, y₀, y₀_in, ⟨H.symm, ?_⟩⟩
      rintro rfl
      exact mul_ne_zero (ne_of_mem_of_not_mem y₀_in zeroV') h H
    rcases this with ⟨z₀, y₀, y₀_in, hz₀, z₀_ne⟩
    have vz₀_ne : v.restrict z₀ ≠ 0 := by rwa [Valuation.ne_zero_iff]
    refine ⟨v.restrict z₀, ?_⟩
    rw [WithZeroTopology.tendsto_of_ne_zero vz₀_ne, eventually_comap]
    filter_upwards [nhds_right] with x x_in a ha
    rcases x_in with ⟨y, y_in, rfl⟩
    have : (v.restrict (a * z₀⁻¹)) = 1 := by
      rw [v.restrict_def, ValueGroup₀.restrict₀_eq_one_iff]
      apply hV
      have : (z₀⁻¹ : K) = (z₀ : Completion K)⁻¹ := map_inv₀ Completion.coeRingHom z₀
      rw [Completion.coe_mul, this, ha, hz₀, mul_inv, mul_comm y₀⁻¹, ← mul_assoc, mul_assoc y,
        mul_inv_cancel₀ h, mul_one]
      solve_by_elim
    calc
      v.restrict a = v.restrict (a * z₀⁻¹ * z₀) := by rw [mul_assoc, inv_mul_cancel₀ z₀_ne, mul_one]
      _ = v.restrict (a * z₀⁻¹) * v.restrict z₀ := Valuation.map_mul _ _ _
      _ = v.restrict z₀ := by rw [this, one_mul]

/-- the extension of a valuation on a division ring to its completion. -/
noncomputable def extensionValuation : Valuation (Completion K) Γ₀ where
  toFun := ValueGroup₀.embedding ∘ v.extension
  map_zero' := by
    rw [Function.comp_apply, map_eq_zero, ← v.restrict.map_zero (R := K),
      ← v.extension_extends (0 : K), Completion.coe_zero]
  map_one' := by
    rw [Function.comp_apply, ← Completion.coe_one, v.extension_extends (1 : K),
      Valuation.map_one _, map_one]
  map_mul' x y := by
    simp only [Function.comp_apply, ← map_mul]
    rw [embedding_strictMono.injective.eq_iff]
    apply Completion.induction_on₂ x y
      (p := fun x y => v.extension (x * y) = v.extension x * v.extension y)
    · have c1 : Continuous fun x : Completion K × Completion K => v.extension (x.1 * x.2) :=
        v.continuous_extension.comp (continuous_fst.mul continuous_snd)
      have c2 : Continuous fun x : Completion K × Completion K =>
          v.extension x.1 * v.extension x.2 :=
        (v.continuous_extension.comp continuous_fst).mul
          (v.continuous_extension.comp continuous_snd)
      exact isClosed_eq c1 c2
    · intro x y
      norm_cast
      exact Valuation.map_mul _ _ _
  map_add_le_max' x y := by
    simp_rw [le_max_iff, Function.comp_apply]
    rw [embedding_strictMono.le_iff_le, embedding_strictMono.le_iff_le (f := embedding)]
    apply Completion.induction_on₂ x y
      (p := fun x y => v.extension (x + y) ≤ v.extension x ∨ v.extension (x + y) ≤ v.extension y)
    · have cont : Continuous v.extension := v.continuous_extension
      exact (isClosed_le (by fun_prop) <| cont.comp continuous_fst).union
          (isClosed_le (by fun_prop) <| cont.comp continuous_snd)
    · intro x y
      norm_cast
      exact le_max_iff.mp (v.restrict.map_add x y)

-- rename this or change the statement
lemma extensionValuation_toFun (x : Completion K) : v.extensionValuation x =
    embedding (v.extension x) := rfl

lemma extensionValuation_ofClass_apply {x : Completion K} :
    (MonoidWithZeroHom.ofClass v.extensionValuation) x = embedding (v.extension x) := rfl

@[simp]
lemma extensionValuation_apply_coe (x : K) :
    v.extensionValuation (x : Completion K) = v x := by
  simp [extensionValuation_toFun]

@[simp]
lemma extension_eq_zero_iff {x : Completion K} : v.extension x = 0 ↔ x = 0 := by
  suffices v.extensionValuation x = 0 ↔ x = 0 by
    simpa only [extensionValuation_toFun, map_eq_zero]
  rw [Valuation.zero_iff]

lemma exists_coe_eq_v (x : Completion K) : ∃ r : K, v.extensionValuation x = v r := by
  rcases eq_or_ne x 0 with (rfl | h)
  · exact ⟨0, v.extensionValuation_apply_coe 0⟩
  · refine Completion.denseRange_coe.induction_on x ?_
      (fun a ↦ by simp [v.extensionValuation_apply_coe a])
    · simp only [extensionValuation_toFun]
      have hr (r : K) : ValueGroup₀.embedding (restrict₀ (.ofClass v) r) = v r := by
        simp [embedding_restrict₀]
      have h (a b : ValueGroup₀ (.ofClass v)) :
          ValueGroup₀.embedding a = ValueGroup₀.embedding b ↔ a = b := by
        rw [embedding_strictMono.injective.eq_iff]
      simp_rw [← hr, ← Valuation.restrict_def, h]
      convert! (valuation_isClosedMap v).isClosed_range.preimage v.continuous_extension
      simp_rw [eq_comm (a := v.extension _)]
      grind

-- Bourbaki CA VI §5 no.3 Proposition 5 (d)
theorem closure_coe_completion_v_lt {γ : Γ₀ˣ} :
    closure ((↑) '' { x : K | v x < (γ : Γ₀) }) =
    { x : Completion K | v.extensionValuation x < (γ : Γ₀) } := by
  ext x
  set γ₀' := v.extension x with hγ₀'_def
  set γ₀ := v.extensionValuation x with hγ₀_def
  have heq : γ₀ = embedding γ₀' := rfl
  suffices γ₀ ≠ 0 → (x ∈ closure ((↑) '' { x : K | v x < (γ : Γ₀) }) ↔ γ₀ < (γ : Γ₀)) by
    rcases eq_or_ne γ₀ 0 with h | h
    · simp only [(Valuation.zero_iff _).mp h, mem_setOf_eq, Valuation.map_zero, Units.zero_lt,
        iff_true]
      apply subset_closure
      exact ⟨0, by simp only [mem_setOf_eq, Valuation.map_zero, Units.zero_lt, true_and]; rfl⟩
    · exact this h
  intro h
  have h' : γ₀' ≠ 0 := by simpa only [heq, map_ne_zero] using h
  have hγ₀ : v.extension ⁻¹' {γ₀'} ∈ 𝓝 x :=
    (continuous_extension v).continuousAt.preimage_mem_nhds
      (WithZeroTopology.singleton_mem_nhds_of_ne_zero h')
  rw [mem_closure_iff_nhds']
  refine ⟨fun hx => ?_, fun hx s hs => ?_⟩
  · obtain ⟨⟨-, y, hy₁ : v y < (γ : Γ₀), rfl⟩, hy₂⟩ := hx _ hγ₀
    replace hy₂ : v y = γ₀ := by
      simp only [mem_preimage, v.extension_extends, mem_singleton_iff, v.restrict_def] at hy₂
      apply_fun embedding at hy₂
      simpa [heq] using hy₂
    rwa [← hy₂]
  · obtain ⟨y, hy₁, hy₂⟩ := Completion.denseRange_coe.mem_nhds (inter_mem hγ₀ hs)
    replace hy₁ : v y = γ₀ := by
      simp only [mem_preimage, v.extension_extends, mem_singleton_iff, v.restrict_def] at hy₁
      apply_fun embedding at hy₁
      simpa [heq] using hy₁
    rw [← hy₁] at hx
    exact ⟨⟨y, ⟨y, hx, rfl⟩⟩, hy₂⟩

theorem closure_coe_completion_v_mul_v_lt {r s : K} (hr : r ≠ 0) (hs : s ≠ 0) :
    closure ((↑) '' { x : K | v x * v r < v s }) =
    { x : Completion K | v.extensionValuation x * v r < v s } := by
  have hrs : v s / v r ≠ 0 := by simp [hr, hs]
  convert! v.closure_coe_completion_v_lt (γ := .mk0 _ hrs) using 3
  all_goals simp [← lt_div_iff₀, zero_lt_iff, hr]

/-- The zero-preserving monoid homomorphism from the `ValueGroup₀` of the valuation on `K` to
that of the extension to its completion. TODO: Split out the definiton of `(restrict₀_surjective
(.ofClass v) x).choose` and prove a spec lemma of it. Remove tactic `set` in the proof. -/
noncomputable def valueGroup₀_hom_extensionValuation :
    ValueGroup₀ (.ofClass v) →*₀ ValueGroup₀ (.ofClass v.extensionValuation) where
  toFun x := v.extensionValuation.restrict (restrict₀_surjective (.ofClass v) x).choose
  map_zero' := by simp [Valuation.restrict_def]
  map_one' := by
    apply_fun embedding using embedding_injective
    simpa using (restrict₀_surjective (.ofClass v) 1).choose_spec
  map_mul' a b := by
    set x := (restrict₀_surjective (.ofClass v) a).choose with hx_def
    have hx := (restrict₀_surjective (.ofClass v) a).choose_spec
    set y := (restrict₀_surjective (.ofClass v) b).choose with hy_def
    have hy := (restrict₀_surjective (.ofClass v) b).choose_spec
    set xy := (restrict₀_surjective (.ofClass v) (a * b)).choose with hxy_def
    have hxy := (restrict₀_surjective (.ofClass v) (a * b)).choose_spec
    rw [← hx_def] at hx
    rw [← hy_def] at hy
    rw [← hxy_def] at hxy
    apply_fun embedding at hxy
    apply_fun embedding at hx
    apply_fun embedding at hy
    simp only [embedding_restrict₀, coe_ofClass, map_mul] at hxy hx hy
    simp only [Valuation.restrict_def, restrict₀_apply, coe_ofClass, extensionValuation_apply_coe,
      map_eq_zero, mul_dite, mul_zero, dite_mul, zero_mul]
    by_cases hx0 : x = 0
    · simpa [← hx, hx0] using hxy
    · by_cases hy0 : y = 0
      · simpa [← hy, hy0] using hxy
      · rw [dif_neg, dif_neg, dif_neg]
        · simp only [← WithZero.coe_mul, MulMemClass.mk_mul_mk, WithZero.coe_inj, Subtype.mk.injEq]
          rw [← Units.mk0_mul]
          · ext
            simp [Units.val_mk0, hx, hy, hxy]
          · aesop
        · simpa
        · simpa
        · simp [extensionValuation_apply_coe, hxy, ← hx, ← hy, hx0, hy0]

/-- The zero-preserving monoid homomorphism from the `ValueGroup₀` of the valuation on `K` to
  that of the extension to its completion. -/
noncomputable def valueGroup₀_equiv_extensionValuation :
    ValueGroup₀ (.ofClass v) ≃* ValueGroup₀ (.ofClass v.extensionValuation) := by
  refine MulEquiv.ofBijective v.valueGroup₀_hom_extensionValuation ⟨?_, ?_⟩
  · intro a b hab
    set x := (restrict₀_surjective (.ofClass v) a).choose with hx_def
    have hx := (restrict₀_surjective (.ofClass v) a).choose_spec
    set y := (restrict₀_surjective (.ofClass v) b).choose with hy_def
    have hy := (restrict₀_surjective (.ofClass v) b).choose_spec
    apply_fun embedding using embedding_injective
    apply_fun embedding at hx
    apply_fun embedding at hy
    simp only [← hx_def, embedding_restrict₀, coe_ofClass, ← hy_def] at hx hy
    simp only [valueGroup₀_hom_extensionValuation, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk] at hab
    have : v.extensionValuation.restrict (algebraMap K _ x) =
      v.extensionValuation.restrict (algebraMap _ _ y) := hab
    simp only [restrict_def, restrict₀_apply, v.extensionValuation_ofClass_apply, map_eq_zero,
      extension_eq_zero_iff] at this
    by_cases ha0 : a = 0
    · have h0 : v.extensionValuation ((algebraMap K (Completion K)) x) = 0 := by
        simpa [ha0, v.extension_eq_zero_iff, map_eq_zero] using hx
      simp only [MonoidWithZeroHom.coe_ofClass, h0, reduceDIte, map_eq_zero, left_eq_dite_iff,
        WithZero.zero_ne_coe, imp_false, not_not] at this
      simp [ha0, ← hy, this]
    · apply_fun embedding at ha0 using embedding_injective (f := (.ofClass v))
      have h0 : v.extensionValuation ((algebraMap K (Completion K)) x) ≠ 0 := by
        simp only [ne_eq, map_eq_zero]
        intro h
        simp [h, ← hx] at ha0
      have h0' : v.extensionValuation ((algebraMap K (Completion K)) y) ≠ 0 := by
        have hb0 : b ≠ 0 := by
          apply_fun embedding at hab using embedding_injective (f := (.ofClass v))
          simp only [← hx_def, Valuation.embedding_restrict, extensionValuation_apply_coe,
            ← hy_def] at hab
          simpa [← hx, hab, hy] using ha0
        apply_fun embedding at hb0 using embedding_injective (f := (.ofClass v))
        simp only [ne_eq, map_eq_zero]
        intro h
        simp [h, ← hy] at hb0
      simp only [MonoidWithZeroHom.coe_ofClass, h0, reduceDIte, h0', WithZero.coe_inj,
        Subtype.mk.injEq, Units.mk0_inj, embedding_inj] at this
      simp only [Completion.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply,
        extension_extends, Valuation.restrict_inj] at this
      rwa [← hx, ← hy]
  · intro x
    obtain ⟨k', hk'⟩ := restrict₀_surjective (.ofClass v.extensionValuation) x
    use v.extension k'
    have := (restrict₀_surjective (.ofClass v) (v.extension k')).choose_spec
    apply_fun embedding at this
    simpa [← embedding_inj, valueGroup₀_hom_extensionValuation, Valuation.restrict_def, ← hk',
      ← extensionValuation_toFun] using this

end Valuation

section Completion

variable [IsUniformAddGroup K]

noncomputable instance UniformSpace.Completion.valuativeRel : ValuativeRel (Completion K) :=
  .ofValuation (ValuativeRel.valuation K).extensionValuation

instance Valuation.extensionValuation.compatible' :
    (ValuativeRel.valuation K).extensionValuation.Compatible := Valuation.Compatible.ofValuation _

variable {Γ₀ Γ₀' : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [LinearOrderedCommGroupWithZero Γ₀'] (v : Valuation K Γ₀) [v.Compatible]
  (v' : Valuation K Γ₀') [v'.Compatible]


open ValueGroupWithZero in
lemma foo [Ring R] [temp : ValuativeRel R] [top : TopologicalSpace R]
    (v : Valuation R Γ₀) [v.Compatible] (x : R) (γ : ValueGroupWithZero R) :
    v.restrict x < (orderMonoidIso v) γ ↔ (valuation R) x < γ := sorry

open ValueGroupWithZero in
lemma foo_star [Ring R] [temp : ValuativeRel R] [top : TopologicalSpace R]
    (v : Valuation R Γ₀) [v.Compatible] (x : R) (γ : (ValueGroupWithZero R)ˣ) :
    v.restrict x < (orderMonoidIso v) γ ↔ (valuation R) x < γ := by
  rw [foo]

open ValueGroupWithZero in
lemma foo_symm [Ring R] [temp : ValuativeRel R] [top : TopologicalSpace R]
    (v : Valuation R Γ₀) [v.Compatible] (x : R) (γ : (ValueGroup₀ (.ofClass v))) :
    v.restrict x < γ ↔ (valuation R) (x) < (orderMonoidIso v).symm γ := sorry

open ValueGroupWithZero in
lemma foo_symm_star [Ring R] [temp : ValuativeRel R] [top : TopologicalSpace R]
    (v : Valuation R Γ₀) [v.Compatible] (x : R) (γ : (ValueGroup₀ (.ofClass v))ˣ) :
    v.restrict x < γ ↔ (valuation R) (x) < (orderMonoidIso v).symm γ := by rw [foo_symm]

example (a b c : ℝ) : a = b → (c < a ↔ c < b) := by
 intro h
 rw [h]

open ValueGroupWithZero in
theorem IsValuativeTopology.mk_valuation [Ring R] [ValuativeRel R]
    [TopologicalSpace R] (v : Valuation R Γ₀) [v.Compatible]
    (H : ∀ {s : Set R} {x : R}, s ∈ 𝓝 x ↔ ∃ (γ : (ValueGroup₀ (.ofClass v))ˣ),
    (fun (x₁ : R) ↦ x + x₁) '' {z : R | v.restrict z < γ} ⊆ s) :
    IsValuativeTopology R := by
  constructor
  refine fun {s x} ↦ ⟨fun h_mem ↦ ?_, fun ⟨γ, hγ⟩ ↦
    H.mpr ⟨Units.mk0 ((orderMonoidIso v) γ) (by simp), subset_trans (by simp) hγ⟩⟩
  obtain ⟨γ, hγ⟩ := H.mp h_mem
  exact ⟨Units.mk0 ((orderMonoidIso v).symm γ) (by simp), subset_trans (by simp) hγ⟩

theorem IsValuativeTopology.mk₀_valuation [Ring R] [ValuativeRel R] [TopologicalSpace R]
    (v : Valuation R Γ₀) [v.Compatible]
    (H : ∀ {s : Set R} {x : R}, s ∈ 𝓝 x ↔ ∃ (γ : (ValueGroup₀ (.ofClass v))ˣ),
    (fun (x₁ : R) ↦ x + x₁) '' {z : R | v.restrict z < γ} ⊆ s) :
    IsValuativeTopology R := IsValuativeTopology.mk_valuation v (fun {s x} ↦ by rw [H])


theorem foo (x : Completion K) (γ : (ValueGroup₀ (.ofClass v))ˣ) : v.extensionValuation.restrict x <
    ((Units.map v.valueGroup₀_equiv_extensionValuation.toMonoidHom) γ).1 ↔
    embedding (v.extension x) < embedding γ.1 := by
  simp only [MulEquiv.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe]
  rw [embedding_strictMono.lt_iff_lt, Valuation.restrict_def, restrict₀_apply]
  by_cases hx0 : x = 0
  · simp only [hx0]
    rw [dif_pos (map_zero _)]
    · simp only [valueGroup₀_equiv_extensionValuation, valueGroup₀_hom_extensionValuation,
      MulEquiv.ofBijective_apply, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
      rw [Valuation.restrict_def, restrict₀_apply, dif_neg]
      · have hext : v.extension 0 = 0 := by rw [extension_eq_zero_iff]
        simp [hext]
      · simp [← v.restrict.zero_iff, v.restrict_def,
          (restrict₀_surjective (.ofClass v) _).choose_spec]
  · rw [dif_neg (by simp [hx0])]
    · set y := (restrict₀_surjective (.ofClass v) γ).choose with hy_def
      have hy := (restrict₀_surjective (.ofClass v) γ).choose_spec
      apply_fun embedding at hy
      simp only [← hy_def, embedding_restrict₀, MonoidWithZeroHom.coe_ofClass] at hy
      simp only [MonoidWithZeroHom.coe_ofClass, extensionValuation_toFun,
        valueGroup₀_equiv_extensionValuation, valueGroup₀_hom_extensionValuation,
        MulEquiv.ofBijective_apply, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
      rw [Valuation.restrict_def, restrict₀_apply, ← hy_def, dif_neg]
      · simp only [MonoidWithZeroHom.coe_ofClass, extensionValuation_toFun, extension_extends,
        Valuation.embedding_restrict, WithZero.coe_lt_coe, Subtype.mk_lt_mk,
        ← Units.val_lt_val, Units.val_mk0]
        convert embedding_strictMono (f := (.ofClass v)).lt_iff_lt
      · simp only [MonoidWithZeroHom.coe_ofClass, extensionValuation_apply_coe, map_eq_zero, ← ne_eq]
        apply_fun v
        simp [hy]



-- need a intro method of IsValuativeTopology only talk about nbhd of zero (with uniform add group)
-- refactor file Mathlib.Topology.Algebra.Valued.ValuativeRel
-- theorem IsValuativeTopology.mk₀ : IsValuativeTopology := sorry
-- given any valuation compatible, can be checked using this valuation
#check Real
instance : IsValuativeTopology (Completion K) := by
  apply IsValuativeTopology.of_zero
  intro s
  let v := valuation K
  suffices HasBasis (𝓝 (0 : Completion K)) (fun _ ↦ True)
      fun γ : (ValueGroup₀ (.ofClass v))ˣ ↦ { x | v.extensionValuation x <
        (Units.map (ValueGroup₀.embedding (f := (.ofClass v))) γ).1 } by
    rw [this.mem_iff]
    simp only [extensionValuation_toFun, Units.coe_map, MonoidHom.coe_coe, true_and]
    have (x : Completion K) (γ : (ValueGroup₀ (.ofClass v))ˣ) : v.extensionValuation.restrict x <
        ((Units.map v.valueGroup₀_equiv_extensionValuation.toMonoidHom) γ).1 ↔
        embedding (v.extension x) < embedding γ.1 := by
      simp only [MulEquiv.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe]
      rw [embedding_strictMono.lt_iff_lt, Valuation.restrict_def, restrict₀_apply]
      by_cases hx0 : x = 0
      · simp only [hx0]
        rw [dif_pos (map_zero _)]
        · simp only [valueGroup₀_equiv_extensionValuation, valueGroup₀_hom_extensionValuation,
          MulEquiv.ofBijective_apply, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
          rw [Valuation.restrict_def, restrict₀_apply, dif_neg]
          · have hext : v.extension 0 = 0 := by rw [extension_eq_zero_iff]
            simp [hext]
          · simp [← v.restrict.zero_iff, v.restrict_def,
              (restrict₀_surjective (.ofClass v) _).choose_spec]
      · rw [dif_neg (by simp [hx0])]
        · set y := (restrict₀_surjective (.ofClass v) γ).choose with hy_def
          have hy := (restrict₀_surjective (.ofClass v) γ).choose_spec
          apply_fun embedding at hy
          simp only [← hy_def, embedding_restrict₀, MonoidWithZeroHom.coe_ofClass] at hy
          simp only [MonoidWithZeroHom.coe_ofClass, extensionValuation_toFun,
            valueGroup₀_equiv_extensionValuation, valueGroup₀_hom_extensionValuation,
            MulEquiv.ofBijective_apply, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk]
          rw [Valuation.restrict_def, restrict₀_apply, ← hy_def, dif_neg]
          · simp only [MonoidWithZeroHom.coe_ofClass, extensionValuation_toFun, extension_extends,
            Valuation.embedding_restrict, WithZero.coe_lt_coe, Subtype.mk_lt_mk,
            ← Units.val_lt_val, Units.val_mk0]
            convert embedding_strictMono (f := (.ofClass v)).lt_iff_lt
          · simp only [MonoidWithZeroHom.coe_ofClass, extensionValuation_apply_coe, map_eq_zero, ← ne_eq]
            apply_fun v
            simp [hy]
    refine ⟨fun ⟨γ, h⟩ ↦ ?_, fun ⟨γ, h⟩ ↦ ?_⟩
    · use Units.map ((ValueGroupWithZero.orderMonoidIso v.extensionValuation).symm.toMonoidHom.comp
        v.valueGroup₀_equiv_extensionValuation.toMonoidHom) γ
      simp only [OrderMonoidIso.toMulEquiv_eq_coe, MulEquiv.toMonoidHom_eq_coe, Units.map_comp,
        MonoidHom.coe_comp, Function.comp_apply, Units.coe_map, MonoidHom.coe_coe,
        OrderMonoidIso.coe_mulEquiv, valuation_lt_symm_orderMonoidIso]
      convert! h
      apply this
    · use Units.map (v.valueGroup₀_equiv_extensionValuation.symm.toMonoidHom.comp
        (ValueGroupWithZero.orderMonoidIso v.extensionValuation)) γ
      simp only [← this]
      simp only [MulEquiv.toMonoidHom_eq_coe, Units.map_comp, MonoidHom.coe_comp,
        Function.comp_apply, Units.coe_map, MonoidHom.coe_coe, MulEquiv.apply_symm_apply,
        restrict_lt_orderMonoidIso]
      convert! h
  simp_rw [← closure_coe_completion_v_lt, Units.coe_map]
  convert! v.hasBasis_nhds_zero.hasBasis_of_isDenseInducing Completion.isDenseInducing_coe
  simp [Valuation.restrict_lt_iff_lt_embedding]

@[simp]
theorem Valuation.extensionValuation.isEquiv_iff :
    v.extensionValuation.IsEquiv v'.extensionValuation := by

  have := isEquiv v v'
  intro x y
  apply UniformSpace.Completion.induction_on₂ (p := fun x y ↦ v.extensionValuation x ≤
    v.extensionValuation y ↔ v'.extensionValuation x ≤ v'.extensionValuation y)
  · sorry -- union of closed
  · simpa

instance Valuation.extensionValuation.compatible : v.extensionValuation.Compatible := by
  apply Valuation.IsEquiv.compatible (v₁ := (ValuativeRel.valuation K).extensionValuation)
  simp [ValuativeRel.isEquiv]

end Completion



-- @[simp]
-- theorem valuedCompletion_apply (x : K) : Valued.v (x : Completion K) = v x := by
--   simp [Valued.v]

-- lemma valuedCompletion_surjective_iff :
--     Function.Surjective (v : Completion K → Γ₀) ↔ Function.Surjective (v : K → Γ₀) := by
--   constructor <;> intro h γ <;> obtain ⟨a, ha⟩ := h γ
--   · induction a using Completion.induction_on
--     · by_cases H : ∃ x : K, (v : K → Γ₀) x = γ
--       · simp [H]
--       · simp only [H, imp_false]
--         rcases eq_or_ne γ 0 with rfl | hγ
--         · simp at H
--         · obtain ⟨r, hr⟩ := h γ
--           have hr' : restrict₀ (.ofClass (valuedCompletion (K := K)).v) r ≠ 0 := by
--             rw [ne_eq, ← embedding_inj, embedding_restrict₀ r]
--             simpa [hr]
--           convert! isClosed_univ.sdiff (isOpen_sphere (Completion K) hr') using 1
--           ext x
--           simp [← hr, ← v.restrict_def, v.restrict_inj]
--     · exact ⟨_, by simpa using ha⟩
--   · exact ⟨a, by simp [ha]⟩

-- instance {R : Type*} [CommSemiring R] [Algebra R K] [UniformContinuousConstSMul R K]
--     [FaithfulSMul R K] : FaithfulSMul R (Completion K) := by
--   rw [faithfulSMul_iff_algebraMap_injective R (Completion K)]
--   exact (FaithfulSMul.algebraMap_injective K (Completion K)).comp (FaithfulSMul.algebraMap_injective R K)

end Field




-- section ValuativeRel

-- variable [Ring R] [UniformSpace R] [IsTopologicalRing R] [IsUniformAddGroup R] [ValuativeRel R]
--   [IsValuativeTopology R]

-- instance UniformSpace.Completion.valuativeRel : ValuativeRel R := sorry
-- -- UniformSpace.Completion.extension₂ for relations

-- instance UniformSpace.Completion.isValuativeTopology : IsValuativeTopology R := sorry

-- end ValuativeRel

-- section Compatible

-- variable [Ring R] [UniformSpace R] [IsTopologicalRing R] [IsUniformAddGroup R] [ValuativeRel R]
--   [IsValuativeTopology R] [LinearOrderedCommGroupWithZero Γ₀]

-- instance Valuation.compatible_completion (v : Valuation R Γ₀) [v.Compatible] :
--     v.completion.Compatible := sorry

-- end Compatible
