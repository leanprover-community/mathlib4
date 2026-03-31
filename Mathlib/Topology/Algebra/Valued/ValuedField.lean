/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.WithZeroTopology
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Valued fields and their completions

In this file we study the topology of a field `K` endowed with a valuation (in our application
to adic spaces, `K` will be the valuation field associated to some valuation on a ring, defined in
valuation.basic).

We already know from valuation.topology that one can build a topology on `K` which
makes it a topological ring.

The first goal is to show `K` is a topological *field*, i.e. inversion is continuous
at every non-zero element.

The next goal is to prove `K` is a *completable* topological field. This gives us
a completion `hat K` which is a topological field. We also prove that `K` is automatically
separated, so the map from `K` to `hat K` is injective.

Then we extend the valuation given on `K` to a valuation on `hat K`.
-/

@[expose] public section


open Filter Set

open Topology

section DivisionRing

variable {K : Type*} [DivisionRing K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section ValuationTopologicalDivisionRing

section InversionEstimate

variable (v : Valuation K Γ₀)

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

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Valued

/-- The topology coming from a valuation on a division ring makes it a topological division ring
[BouAC, VI.5.1 middle of Proposition 1] -/
instance (priority := 100) Valued.isTopologicalDivisionRing [Valued K Γ₀] :
    IsTopologicalDivisionRing K :=
  { (by infer_instance : IsTopologicalRing K) with
    continuousAt_inv₀ x x_ne s s_in := by
      obtain ⟨γ, hs⟩ := Valued.mem_nhds.mp s_in; clear s_in
      rw [mem_map, Valued.mem_nhds]
      let γ' := Units.mk0 ((ValueGroup₀.restrict₀ _) x) (v.restrict.ne_zero_iff.mpr x_ne)
      use min (γ * (γ' * γ')) γ'
      intro y y_in
      apply hs
      simp only [mem_setOf_eq, Units.min_val, Units.val_mul] at y_in
      exact Valuation.inversion_estimate _ x_ne y_in }

/-- A valued division ring is separated. -/
instance (priority := 100) ValuedRing.separated [Valued K Γ₀] : T0Space K := by
  suffices T2Space K by infer_instance
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x x_ne
  refine ⟨{ k | v k < v x }, ?_, fun h => lt_irrefl _ h⟩
  rw [Valued.mem_nhds]
  set γ' := Units.mk0 ((ValueGroup₀.restrict₀ _) x) (v.restrict.ne_zero_iff.mpr x_ne) with hdef
  exact ⟨γ', fun y hy => by
    simp only [Valuation.restrict_lt_iff_lt_embedding, hdef, sub_zero, Units.val_mk0,
      mem_setOf_eq, embedding_restrict₀] at hy
    simpa using hy⟩

section

open WithZeroTopology

open Valued

theorem Valued.continuous_valuation [hv : Valued K Γ₀] :
    Continuous (v.restrict : K → (ValueGroup₀ hv.v)) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with (rfl | h)
  · rw [ContinuousAt, map_zero, WithZeroTopology.tendsto_zero]
    intro γ hγ
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    use Units.mk0 γ hγ; rfl
  · have v_ne : (v.restrict x : ValueGroup₀ hv.v) ≠ 0 := (Valuation.ne_zero_iff _).mpr h
    rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero v_ne]
    simp_rw [v.restrict_inj]
    apply Valued.locally_const (by simpa [restrict₀_apply] using v_ne)

theorem Valued.continuous_valuation_of_surjective [hv : Valued K Γ₀]
    (hsurj : Function.Surjective hv.v) : Continuous hv.v := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with (rfl | h)
  · rw [ContinuousAt, map_zero, WithZeroTopology.tendsto_zero]
    intro γ hγ
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    obtain ⟨x, hx⟩ := hsurj γ
    use Units.mk0 (restrict₀ hv.v x) (by simp [restrict₀_apply, hx, hγ])
    simp only [Units.val_mk0, setOf_subset_setOf, ← v.restrict_def, Valuation.restrict_lt_iff, hx,
      imp_self, implies_true]
  · have h0 : hv.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr h
    rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero h0]
    exact Valued.locally_const (by simpa using h0)

end

end ValuationTopologicalDivisionRing

end DivisionRing

namespace Valued

open UniformSpace

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀]

local notation "hat " => Completion

set_option backward.isDefEq.respectTransparency false in
/-- A valued field is completable. -/
instance (priority := 100) completable : CompletableTopField K :=
  { ValuedRing.separated with
    nice := by
      rintro F hF h0
      have : ∃ γ₀ : (MonoidWithZeroHom.ValueGroup₀ hv.v)ˣ, ∃ M ∈ F,
          ∀ x ∈ M, (γ₀.1) ≤ v.restrict x := by
        rcases Filter.inf_eq_bot_iff.mp h0 with ⟨U, U_in, M, M_in, H⟩
        rcases Valued.mem_nhds_zero.mp U_in with ⟨γ₀, hU⟩
        exists γ₀, M, M_in
        intro x xM
        apply le_of_not_gt _
        intro hyp
        have : x ∈ U ∩ M := ⟨hU hyp, xM⟩
        rwa [H] at this
      rcases this with ⟨γ₀, M₀, M₀_in, H₀⟩
      rw [Valued.cauchy_iff] at hF ⊢
      refine ⟨hF.1.map _, ?_⟩
      replace hF := hF.2
      intro γ
      rcases hF (min (γ * γ₀ * γ₀) γ₀) with ⟨M₁, M₁_in, H₁⟩
      clear hF
      use (fun x : K => x⁻¹) '' (M₀ ∩ M₁)
      constructor
      · rw [mem_map]
        apply mem_of_superset (Filter.inter_mem M₀_in M₁_in)
        exact subset_preimage_image _ _
      · rintro _ ⟨x, ⟨x_in₀, x_in₁⟩, rfl⟩ _ ⟨y, ⟨_, y_in₁⟩, rfl⟩
        simp only
        specialize H₁ x x_in₁ y y_in₁
        replace x_in₀ := H₀ x x_in₀
        clear H₀
        apply Valuation.inversion_estimate
        · have : (v.restrict x) ≠ 0 := by
            intro h
            rw [h] at x_in₀
            simp at x_in₀
          exact (Valuation.ne_zero_iff _).mp this
        · refine lt_of_lt_of_le H₁ ?_
          grw [Units.min_val, mul_assoc, Units.val_mul, Units.val_mul, x_in₀] }

open MonoidWithZeroHom WithZeroTopology

lemma valuation_isClosedMap : IsClosedMap (v.restrict : K → (ValueGroup₀ hv.v)) := by
  refine IsClosedMap.of_nonempty ?_
  intro U hU hU'
  simp only [← isOpen_compl_iff, isOpen_iff_mem_nhds, mem_compl_iff, mem_nhds, subset_compl_comm,
    compl_setOf, not_lt] at hU
  simp only [isClosed_iff, mem_image, map_eq_zero, exists_eq_right, ne_eq, image_subset_iff]
  refine (em _).imp_right fun h ↦ ?_
  obtain ⟨γ, h⟩ := hU _ h
  simp only [sub_zero] at h
  refine ⟨γ.1, γ.ne_zero, h.trans ?_⟩
  intro
  simp

-- NOTE: added because inferInstance fails to find it.
/-- The `ValueGroup₀` of the valuation on K is a `LinearOrderedCommGroupWithZero`. -/
local instance : LinearOrderedCommGroupWithZero (ValueGroup₀ hv.v) :=
  MonoidWithZeroHom.ValueGroup₀.instLinearOrderedCommGroupWithZero

/-- The extension of the valuation of a valued field to the completion of the field. -/
noncomputable def extension : hat K → ValueGroup₀ hv.v :=
  Completion.isDenseInducing_coe.extend (v.restrict : K → (ValueGroup₀ hv.v))

set_option backward.isDefEq.respectTransparency false in
theorem continuous_extension : Continuous (Valued.extension : hat K → ValueGroup₀ hv.v) := by
  refine Completion.isDenseInducing_coe.continuous_extend ?_
  intro x₀
  rcases eq_or_ne x₀ 0 with (rfl | h)
  · refine ⟨0, ?_⟩
    rw [← Completion.coe_zero, ← Completion.isDenseInducing_coe.isInducing.nhds_eq_comap]
    exact Valued.continuous_valuation.tendsto' 0 0 (map_zero v.restrict)
  · have preimage_one : v ⁻¹' {(1 : Γ₀)} ∈ 𝓝 (1 : K) := by
      have : (v (1 : K) : Γ₀) ≠ 0 := by
        rw [Valuation.map_one]
        exact zero_ne_one.symm
      convert Valued.locally_const this
      ext x
      rw [Valuation.map_one, mem_preimage, mem_singleton_iff, mem_setOf_eq]
    obtain ⟨V, V_in, hV⟩ : ∃ V ∈ 𝓝 (1 : hat K), ∀ x : K, (x : hat K) ∈ V → (v x : Γ₀) = 1 := by
      rwa [Completion.isDenseInducing_coe.nhds_eq_comap, mem_comap] at preimage_one
    have : ∃ V' ∈ 𝓝 (1 : hat K), (0 : hat K) ∉ V' ∧ ∀ (x) (_ : x ∈ V') (y) (_ : y ∈ V'),
      x * y⁻¹ ∈ V := by
      have : Tendsto (fun p : hat K × hat K => p.1 * p.2⁻¹) ((𝓝 1) ×ˢ (𝓝 1)) (𝓝 1) := by
        rw [← nhds_prod_eq]
        conv =>
          congr
          rfl
          rfl
          rw [← one_mul (1 : hat K)]
        refine
          Tendsto.mul continuous_fst.continuousAt (Tendsto.comp ?_ continuous_snd.continuousAt)
        convert (continuousAt_inv₀ (zero_ne_one.symm : 1 ≠ (0 : hat K))).tendsto
        exact inv_one.symm
      rcases tendsto_prod_self_iff.mp this V V_in with ⟨U, U_in, hU⟩
      let hatKstar := ({0}ᶜ : Set <| hat K)
      have : hatKstar ∈ 𝓝 (1 : hat K) := compl_singleton_mem_nhds zero_ne_one.symm
      exact ⟨U ∩ hatKstar, Filter.inter_mem U_in this,
        ⟨fun ⟨_, h'⟩ ↦ h' rfl, fun x ⟨hx, _⟩ y ⟨hy, _⟩ ↦ hU _ _  hx hy⟩⟩
    rcases this with ⟨V', V'_in, zeroV', hV'⟩
    have nhds_right : (fun x => x * x₀) '' V' ∈ 𝓝 x₀ := by
      have l : Function.LeftInverse (fun x : hat K => x * x₀⁻¹) fun x : hat K => x * x₀ := by
        intro x
        simp only [mul_assoc, mul_inv_cancel₀ h, mul_one]
      have r : Function.RightInverse (fun x : hat K => x * x₀⁻¹) fun x : hat K => x * x₀ := by
        intro x
        simp only [mul_assoc, inv_mul_cancel₀ h, mul_one]
      have c : Continuous fun x : hat K => x * x₀⁻¹ := by fun_prop
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
    have : (v.restrict (a * z₀⁻¹) ) = 1 := by
      rw [v.restrict_def, ValueGroup₀.restrict₀_eq_one_iff]
      apply hV
      have : (z₀⁻¹ : K) = (z₀ : hat K)⁻¹ := map_inv₀ (Completion.coeRingHom : K →+* hat K) z₀
      rw [Completion.coe_mul, this, ha, hz₀, mul_inv, mul_comm y₀⁻¹, ← mul_assoc, mul_assoc y,
        mul_inv_cancel₀ h, mul_one]
      solve_by_elim
    calc
      v.restrict a = v.restrict (a * z₀⁻¹ * z₀) := by rw [mul_assoc, inv_mul_cancel₀ z₀_ne, mul_one]
      _ = v.restrict (a * z₀⁻¹) * v.restrict z₀ := Valuation.map_mul _ _ _
      _ = v.restrict z₀ := by rw [this, one_mul]

@[simp, norm_cast]
theorem extension_extends (x : K) : extension (x : hat K) = v.restrict x := by
  refine Completion.isDenseInducing_coe.extend_eq_of_tendsto ?_
  rw [← Completion.isDenseInducing_coe.nhds_eq_comap]
  exact Valued.continuous_valuation.continuousAt

open MonoidWithZeroHom.ValueGroup₀

set_option backward.isDefEq.respectTransparency false in
/-- the extension of a valuation on a division ring to its completion. -/
noncomputable def extensionValuation : Valuation (hat K) Γ₀ where
  toFun := ValueGroup₀.embedding ∘ Valued.extension
  map_zero' := by
    rw [Function.comp_apply, map_eq_zero, ← v.restrict.map_zero (R := K),
      ← Valued.extension_extends (0 : K), Completion.coe_zero]
  map_one' := by
    rw [Function.comp_apply, ← Completion.coe_one, Valued.extension_extends (1 : K),
      Valuation.map_one _, map_one]
  map_mul' x y := by
    simp only [Function.comp_apply, ← map_mul]
    rw [embedding_strictMono.injective.eq_iff]
    apply Completion.induction_on₂ x y
      (p := fun x y => extension (x * y) = extension x * extension y)
    · have c1 : Continuous fun x : hat K × hat K => Valued.extension (x.1 * x.2) :=
        Valued.continuous_extension.comp (continuous_fst.mul continuous_snd)
      have c2 : Continuous fun x : hat K × hat K => Valued.extension x.1 * Valued.extension x.2 :=
        (Valued.continuous_extension.comp continuous_fst).mul
          (Valued.continuous_extension.comp continuous_snd)
      exact isClosed_eq c1 c2
    · intro x y
      norm_cast
      exact Valuation.map_mul _ _ _
  map_add_le_max' x y := by
    simp_rw [le_max_iff, Function.comp_apply]
    rw [embedding_strictMono.le_iff_le, embedding_strictMono.le_iff_le (f := embedding)]
    apply Completion.induction_on₂ x y
      (p := fun x y => extension (x + y) ≤ extension x ∨ extension (x + y) ≤ extension y)
    · have cont : Continuous (Valued.extension : hat K → _) := Valued.continuous_extension
      exact (isClosed_le (by fun_prop) <| cont.comp continuous_fst).union
          (isClosed_le (by fun_prop) <| cont.comp continuous_snd)
    · intro x y
      norm_cast
      exact le_max_iff.mp (v.restrict.map_add x y)

lemma extensionValuation_toFun (x : hat K) : Valued.extensionValuation x =
    ValueGroup₀.embedding (Valued.extension x) := rfl

@[simp]
lemma extensionValuation_apply_coe (x : K) :
    Valued.extensionValuation (x : hat K) = v x := by
  rw [extensionValuation_toFun, extension_extends, Valuation.restrict_def, embedding_restrict₀]

@[simp]
lemma extension_eq_zero_iff {x : hat K} : extension x = 0 ↔ x = 0 := by
  suffices extensionValuation x = 0 ↔ x = 0 by
    simpa only [extensionValuation_toFun, map_eq_zero]
  rw [Valuation.zero_iff]

set_option backward.isDefEq.respectTransparency false in
lemma exists_coe_eq_v (x : hat K) : ∃ r : K, extensionValuation x = v r := by
  rcases eq_or_ne x 0 with (rfl | h)
  · exact ⟨0, extensionValuation_apply_coe 0⟩
  · refine Completion.denseRange_coe.induction_on x ?_
      (fun a ↦ by simp [extensionValuation_apply_coe a])
    · simp only [extensionValuation_toFun]
      have hr (r : K) : ValueGroup₀.embedding (restrict₀ hv.v r) = v r := by
        rw [embedding_restrict₀]
      have h (a b : ValueGroup₀ hv.v) : ValueGroup₀.embedding a = ValueGroup₀.embedding b ↔
          a = b := by rw [embedding_strictMono.injective.eq_iff]
      simp_rw [← hr, ← Valuation.restrict_def, h]
      convert valuation_isClosedMap.isClosed_range.preimage (continuous_extension (hv := hv))
      simp_rw [eq_comm (a := extension _)]
      ext; simp

-- Bourbaki CA VI §5 no.3 Proposition 5 (d)
theorem closure_coe_completion_v_lt {γ : Γ₀ˣ} :
    closure ((↑) '' { x : K | v x < (γ : Γ₀) }) =
    { x : hat K | extensionValuation x < (γ : Γ₀) } := by
  ext x
  set γ₀' := extension x with hγ₀'_def
  set γ₀ := extensionValuation x with hγ₀_def
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
  have hγ₀ : extension ⁻¹' {γ₀'} ∈ 𝓝 x :=
    continuous_extension.continuousAt.preimage_mem_nhds
      (WithZeroTopology.singleton_mem_nhds_of_ne_zero h')
  rw [mem_closure_iff_nhds']
  refine ⟨fun hx => ?_, fun hx s hs => ?_⟩
  · obtain ⟨⟨-, y, hy₁ : v y < (γ : Γ₀), rfl⟩, hy₂⟩ := hx _ hγ₀
    replace hy₂ : v y = γ₀ := by
      simp only [mem_preimage, extension_extends, mem_singleton_iff, v.restrict_def] at hy₂
      rw [← embedding_restrict₀, hy₂, heq]
    rwa [← hy₂]
  · obtain ⟨y, hy₁, hy₂⟩ := Completion.denseRange_coe.mem_nhds (inter_mem hγ₀ hs)
    replace hy₁ : v y = γ₀ := by
      simp only [mem_preimage, extension_extends, mem_singleton_iff, v.restrict_def] at hy₁
      rw [← embedding_restrict₀, hy₁, heq]
    rw [← hy₁] at hx
    exact ⟨⟨y, ⟨y, hx, rfl⟩⟩, hy₂⟩

theorem closure_coe_completion_v_mul_v_lt {r s : K} (hr : r ≠ 0) (hs : s ≠ 0) :
    closure ((↑) '' { x : K | v x * v r < v s }) =
    { x : hat K | extensionValuation x * v r < v s } := by
  have hrs : v s / v r ≠ 0 := by simp [hr, hs]
  convert closure_coe_completion_v_lt (γ := .mk0 _ hrs) using 3
  all_goals simp [← lt_div_iff₀, zero_lt_iff, hr]

set_option backward.isDefEq.respectTransparency false in
/-- The zero-preserving monoid homomorphism from the `ValueGroup₀` of the valuation on `K` to
  that of the extension to its completion. -/
noncomputable def valueGroup₀_hom_extensionValuation :
    (ValueGroup₀ hv.v) →*₀ (ValueGroup₀ hv.extensionValuation) where
  toFun x := hv.extensionValuation.restrict (restrict₀_surjective hv.v x).choose
  map_zero' := by simp [Valuation.restrict_def]
  map_one' := by
    rw [← embedding_strictMono.injective.eq_iff, Valuation.restrict_def, map_one]
    erw [embedding_restrict₀] -- Should disappear when `ValueGroup₀` takes a `MonoidWithZeroHom`.
    simp only [Valuation.toMonoidWithZeroHom_coe_eq_coe,
      extensionValuation_toFun, extension_extends, ← map_one (embedding (f := hv.v))]
    rw [embedding_strictMono.injective.eq_iff]
    exact (restrict₀_surjective hv.v 1).choose_spec
  map_mul' a b := by
    simp only [restrict₀_apply, map_eq_zero, Valuation.restrict_def, extensionValuation_apply_coe,
      mul_dite, mul_zero, dite_mul, zero_mul]
    set x := (restrict₀_surjective hv.v a).choose with hx_def
    set hx := (restrict₀_surjective hv.v a).choose_spec
    set y := (restrict₀_surjective hv.v b).choose with hy_def
    set hy := (restrict₀_surjective hv.v b).choose_spec
    set xy := (restrict₀_surjective hv.v (a * b)).choose with hxy_def
    set hxy := (restrict₀_surjective hv.v (a * b)).choose_spec
    rw [← hx_def] at hx
    rw [← hy_def] at hy
    rw [← hxy_def] at hxy
    by_cases hx0 : x = 0
    · have h0 : xy = 0 := by
        simp [← v.restrict.zero_iff, v.restrict_def, hxy, ← hx, hx0]
      simp [hx0, h0]
    · by_cases hy0 : y = 0
      · have h0 : xy = 0 := by
          simp [← v.restrict.zero_iff, v.restrict_def, hxy, ← hy, hy0]
        simp [hy0, h0]
      · rw [dif_neg, dif_neg, dif_neg]
        · simp only [← WithZero.coe_mul, MulMemClass.mk_mul_mk, WithZero.coe_inj, Subtype.mk.injEq]
          rw [← Units.mk0_mul]
          · ext
            simp only [Units.val_mk0]
            rw [Units.val_mk0, ← map_mul, ← v.restrict_inj, map_mul]
            simp [v.restrict_def, hx, hy, hxy]
          · aesop
        · simp [hx0]
        · simp [hy0]
        · rw [extensionValuation_apply_coe, ← restrict₀_eq_zero_iff, hxy, ← hx, ← hy]
          simp [hx0, hy0]

set_option backward.isDefEq.respectTransparency false in
/-- The zero-preserving monoid homomorphism from the `ValueGroup₀` of the valuation on `K` to
  that of the extension to its completion. -/
noncomputable def valueGroup₀_equiv_extensionValuation :
    (ValueGroup₀ hv.v) ≃* (ValueGroup₀ hv.extensionValuation) := by
  refine MulEquiv.ofBijective (valueGroup₀_hom_extensionValuation (hv := hv)) ⟨?_, ?_⟩
  · intro a b hab
    set x := (restrict₀_surjective hv.v a).choose with hx_def
    set hx := (restrict₀_surjective hv.v a).choose_spec
    set y := (restrict₀_surjective hv.v b).choose with hy_def
    set hy := (restrict₀_surjective hv.v b).choose_spec
    simp only [valueGroup₀_hom_extensionValuation, coe_mk, ZeroHom.coe_mk] at hab
    have : hv.extensionValuation.restrict (algebraMap K _ x) =
       hv.extensionValuation.restrict (algebraMap _ _ y) := hab
    simp only [restrict₀_apply, map_eq_zero, extensionValuation_toFun,
      Valuation.restrict_def] at this
    by_cases ha0 : a = 0
    · have h0 : extension ((algebraMap K (hat K)) x) = 0 := by
        simp only [extension_eq_zero_iff, map_eq_zero]
        rw [← hx_def, ha0] at hx
        simpa using hx
      simp only [h0, ↓reduceDIte, extension_eq_zero_iff, map_eq_zero, embedding_apply,
        left_eq_dite_iff, WithZero.zero_ne_coe, imp_false, not_not] at this
      rw [restrict₀_apply, dif_pos] at hy
      · rw [ha0, hy]
      · rw [Valuation.zero_iff, ← this]
    · have h0 : extension ((algebraMap K (hat K)) x) ≠ 0 := by
        simp only [ne_eq, extension_eq_zero_iff, map_eq_zero]
        rw [← hx_def] at hx
        simpa [← hx] using ha0
      have h0' : extension ((algebraMap K (hat K)) y) ≠ 0 := by
        have hb0 : b ≠ 0 := by
          rw [← hx_def, ← hy_def, Valuation.restrict_inj, extensionValuation_toFun,
            extensionValuation_toFun, embedding_strictMono.injective.eq_iff,
            extension_extends, extension_extends, v.restrict_def, v.restrict_def,
            hx, hy] at hab
          simpa [hab] using ha0
        simp only [ne_eq, extension_eq_zero_iff, map_eq_zero]
        rw [← hy_def] at hy
        simpa [← hy] using hb0
      simp only [h0, ↓reduceDIte,  h0', WithZero.coe_inj, Subtype.mk.injEq, Units.mk0_inj] at this
      erw [embedding_strictMono.injective.eq_iff, extension_extends, extension_extends] at this
      simp only [Valuation.restrict_def, Algebra.algebraMap_self, RingHom.id_apply] at this
      rw [hx, hy] at this
      exact this
  · intro x
    obtain ⟨k', hk'⟩ := restrict₀_surjective extensionValuation x
    obtain ⟨k, hk⟩ := restrict₀_surjective Valued.v (extension k')
    use extension k'
    simp only [valueGroup₀_hom_extensionValuation, Valuation.restrict_def, coe_mk, ZeroHom.coe_mk]
    rw [← hk', ← embedding_strictMono.injective.eq_iff]
    erw [embedding_restrict₀, embedding_restrict₀]
    simp only [Valuation.toMonoidWithZeroHom_coe_eq_coe,
      extensionValuation_toFun, extension_extends]
    rw [embedding_strictMono.injective.eq_iff]
    exact (restrict₀_surjective hv.v _).choose_spec

set_option backward.isDefEq.respectTransparency false in
noncomputable instance valuedCompletion : Valued (hat K) Γ₀ where
  v := extensionValuation
  is_topological_valuation s := by
    suffices HasBasis (𝓝 (0 : hat K)) (fun _ => True)
        fun γ : (ValueGroup₀ hv.v)ˣ => { x | extensionValuation x <
          (Units.map (ValueGroup₀.embedding (f := hv.v)) γ).1 } by
      rw [this.mem_iff]
      simp only [extensionValuation_toFun, Units.coe_map, MonoidHom.coe_coe, true_and]
      have (x : hat K) (γ : (ValueGroup₀ hv.v)ˣ) : extensionValuation.restrict x <
          ((Units.map valueGroup₀_equiv_extensionValuation.toMonoidHom) γ).1 ↔
          embedding (extension x) < embedding γ.1 := by
        simp only [MulEquiv.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe]
        rw [embedding_strictMono.lt_iff_lt, Valuation.restrict_def, restrict₀_apply]
        by_cases hx0 : x = 0
        · simp only [hx0]
          rw [dif_pos (map_zero _)]
          · simp only [valueGroup₀_equiv_extensionValuation, valueGroup₀_hom_extensionValuation,
              MulEquiv.ofBijective_apply, coe_mk, ZeroHom.coe_mk]
            rw [Valuation.restrict_def, restrict₀_apply, dif_neg]
            · have hext : hv.extension 0 = 0 := by rw [extension_eq_zero_iff]
              simp [hext]
            · simp [← v.restrict.zero_iff, v.restrict_def,
                (restrict₀_surjective hv.v _).choose_spec]
        · rw [dif_neg (by simp [hx0])]
          · set y := (restrict₀_surjective hv.v γ).choose with hy_def
            set hy := (restrict₀_surjective hv.v γ).choose_spec
            simp only [extensionValuation_toFun, valueGroup₀_equiv_extensionValuation,
              valueGroup₀_hom_extensionValuation,
              MulEquiv.ofBijective_apply, coe_mk, ZeroHom.coe_mk]
            rw [Valuation.restrict_def, restrict₀_apply, ← hy_def, dif_neg]
            · simp only [extensionValuation_toFun, extension_extends, WithZero.coe_lt_coe,
                Subtype.mk_lt_mk, ← Units.val_lt_val, Units.val_mk0]
              rw [embedding_strictMono.lt_iff_lt, v.restrict_def, hy]
            · rw [extensionValuation_apply_coe, ← restrict₀_eq_zero_iff, hy]
              simp
      refine ⟨fun ⟨γ, h⟩ ↦ ?_, fun ⟨γ, h⟩ ↦ ?_⟩
      · use Units.map valueGroup₀_equiv_extensionValuation.toMonoidHom γ
        convert h
        apply this
      · use Units.map valueGroup₀_equiv_extensionValuation.symm.toMonoidHom γ
        convert h
        rw [← this]
        simp [Valuation.restrict_def, restrict₀_apply]
    simp_rw [← closure_coe_completion_v_lt, Units.coe_map]
    convert (hasBasis_nhds_zero K Γ₀).hasBasis_of_isDenseInducing Completion.isDenseInducing_coe
    rw [Valuation.restrict_lt_iff_lt_embedding]; rfl

@[simp]
theorem valuedCompletion_apply (x : K) : Valued.v (x : hat K) = v x := by
  simp only [Valued.v, extensionValuation_toFun]
  rw [← embedding_restrict₀ x, extension_extends x, v.restrict_def]

lemma valuedCompletion_surjective_iff :
    Function.Surjective (v : hat K → Γ₀) ↔ Function.Surjective (v : K → Γ₀) := by
  constructor <;> intro h γ <;> obtain ⟨a, ha⟩ := h γ
  · induction a using Completion.induction_on
    · by_cases H : ∃ x : K, (v : K → Γ₀) x = γ
      · simp [H]
      · simp only [H, imp_false]
        rcases eq_or_ne γ 0 with rfl | hγ
        · simp at H
        · obtain ⟨r, hr⟩ := h γ
          have hr' : restrict₀ valuedCompletion.v r ≠ 0 := by
            erw [ne_eq, ← embedding_strictMono.injective.eq_iff, embedding_restrict₀ r, hr,
              map_zero]
            exact hγ
          convert isClosed_univ.sdiff (isOpen_sphere (hat K) hr') using 1
          ext x
          simp only [← hr, mem_setOf_eq, mem_diff, mem_univ, true_and, ← v.restrict_def,
            v.restrict_inj]
    · exact ⟨_, by simpa using ha⟩
  · exact ⟨a, by simp [ha]⟩

instance {R : Type*} [CommSemiring R] [Algebra R K] [UniformContinuousConstSMul R K]
    [FaithfulSMul R K] : FaithfulSMul R (hat K) := by
  rw [faithfulSMul_iff_algebraMap_injective R (hat K)]
  exact (FaithfulSMul.algebraMap_injective K (hat K)).comp (FaithfulSMul.algebraMap_injective R K)

end Valued

section Notation

namespace Valued

variable (K : Type*) [Field K] {Γ₀ : outParam Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [vK : Valued K Γ₀]

/-- A `Valued` version of `Valuation.integer`, enabling the notation `𝒪[K]` for the
valuation integers of a valued field `K`. -/
@[reducible]
def integer : Subring K := (vK.v).integer

@[inherit_doc]
scoped notation "𝒪[" K "]" => Valued.integer K

/-- An abbreviation for `IsLocalRing.maximalIdeal 𝒪[K]` of a valued field `K`, enabling the notation
`𝓂[K]` for the maximal ideal in `𝒪[K]` of a valued field `K`. -/
@[reducible]
def maximalIdeal : Ideal 𝒪[K] := IsLocalRing.maximalIdeal 𝒪[K]

@[inherit_doc]
scoped notation "𝓂[" K "]" => maximalIdeal K

/-- An abbreviation for `IsLocalRing.ResidueField 𝒪[K]` of a `Valued` instance, enabling the
notation `𝓀[K]` for the residue field of a valued field `K`. -/
@[reducible]
def ResidueField := IsLocalRing.ResidueField (𝒪[K])

@[inherit_doc]
scoped notation "𝓀[" K "]" => ResidueField K

end Valued

end Notation
