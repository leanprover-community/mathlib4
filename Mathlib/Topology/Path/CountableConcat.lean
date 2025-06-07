/-
Copyright (c) 2024 Ben Eltschig. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Eltschig
-/
import Mathlib.Data.Nat.Log
import Mathlib.Topology.Path

/-!
# Countable concatenations of paths

In this file we provide a way to concatenate countably many paths leading up to a point into a
single path whenever that is possible. This is occasionally useful to construct a path passing
through some convergent sequence of points.

## Main definitions

* `Path.countableConcat γ x hγx`: the concatenation of countably many paths `γ n` leading up to
  some point `x`, given that these paths converge in some precise sense (`hγx`) to `x`.
* `Path.countableConcat_eq_trans`: the recurrence relation fulfilled by `Path.countableConcat`,
  showing that `Path.countableConcat γ x hγx` is the concatenation of `γ 0` with the countable
  concatenation with the remaining paths.
* `Path.map_countableConcat`: countable concatenation commutes with `Path.map`, i.e. the image of a
  countable concatenation of paths is the concatenation of the images.
-/

noncomputable section

open Topology unitInterval Set Filter

namespace Path

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {s : ℕ → X}

/-- The concatenation of countably many paths leading up to some point `x` as a function. The
corresponding path is defined separately because continuity takes some effort to prove. -/
def countableConcatFun (γ : (n : ℕ) → Path (s n) (s (n + 1))) (x : X) : I → X := fun t ↦ by
  let n := Nat.log 2 ⌊(σ t).1⁻¹⌋₊
  refine if ht : t < 1 then γ n ⟨2 * (1 - σ t * (2 ^ n : ℕ)), ?_, ?_⟩ else x
  <;> have ht' := symm_one ▸ symm_lt_symm.2 ht <;> have ht'' := coe_pos.2 ht'
  · suffices (σ t : ℝ) * (2 ^ n : ℕ) ≤ 1 by linarith
    calc
      _ ≤ (σ t).1 * ⌊(σ t).1⁻¹⌋₊ := ?_
      _ ≤ (σ t).1 * (σ t).1⁻¹    := by gcongr; exact Nat.floor_le <| by simp [t.2.2]
      _ = 1                      := mul_inv_cancel₀ ht''.ne'
    gcongr
    exact Nat.pow_log_le_self _ (Nat.floor_pos.2 <| (one_le_inv₀ ht'').2 (σ t).2.2).ne'
  · suffices h : 1 ≤ (σ t : ℝ) * (2 * (2 ^ n : ℕ)) by rw [mul_left_comm] at h; linarith
    refine (mul_inv_cancel₀ ht''.ne').symm.le.trans <|
      mul_le_mul_of_nonneg_left ?_ (σ t).2.1
    rw [← Nat.cast_ofNat, ← Nat.cast_mul, ← Nat.pow_succ']
    exact (Nat.lt_succ_floor _).le.trans <| Nat.cast_le.2 <| Nat.succ_le_of_lt <|
      Nat.lt_pow_succ_log_self one_lt_two _

/-- On closed intervals [1 - 2 ^ n, 1 - 2 ^ (n + 1)], `countableConcatFun γ x` agrees with a
reparametrisation of `γ n`. -/
lemma countableConcatFun_eqOn (γ : (n : ℕ) → Path (s n) (s (n + 1))) {x : X} (n : ℕ) :
    Set.EqOn (countableConcatFun γ x) (fun t ↦ (γ n).extend (2 * (1 - (1 - t) * (2 ^ n))))
    (Set.Icc (σ ⟨(2 ^ n)⁻¹, by simp [inv_le_one₀, one_le_pow₀]⟩)
      (σ ⟨(2 ^ (n+1))⁻¹, by simp [inv_le_one₀, one_le_pow₀]⟩)) := fun t ht ↦ by
  simp only [Set.mem_Icc, ← Subtype.coe_le_coe, coe_symm_eq] at ht
  have ht' : t < 1 := coe_lt_one.1 <| ht.2.trans_lt <| by simp
  have ht'' : 0 < 1 - t.1 := by linarith [coe_lt_one.2 ht']
  simp only [countableConcatFun, ht', ↓reduceDIte, coe_symm_eq]
  by_cases hn : Nat.log 2 ⌊(1 - t : ℝ)⁻¹⌋₊ = n
  · refine congr (by rw [hn]) ?_
    rw [Set.projIcc_of_mem _ <| Set.mem_Icc.1 ⟨?_, ?_⟩]
    · simp [hn]
    · have h := mul_le_mul_of_nonneg_right ht.1 (a := 2 ^ n) (by simp)
      rw [sub_mul, inv_mul_cancel₀ (by simp)] at h
      linarith
    · have h := mul_le_mul_of_nonneg_right ht.2 (a := 2 ^ (n+1)) (by simp)
      rw [sub_mul, inv_mul_cancel₀ (by simp), pow_succ] at h
      linarith
  · replace hn : Nat.log 2 ⌊(1 - t : ℝ)⁻¹⌋₊ = n + 1 := by
      refine le_antisymm ?_ <| n.succ_le_of_lt <| (Ne.symm hn).lt_of_le ?_
      · refine (Nat.log_mono_right <| Nat.floor_le_floor <| inv_anti₀ (by simp) <|
          le_sub_comm.1 ht.2).trans ?_
        rw [← Nat.cast_ofNat (R := ℝ), ← Nat.cast_pow, inv_inv, Nat.floor_natCast,
          Nat.log_pow one_lt_two _]
      · refine le_trans ?_ <| Nat.log_mono_right <| Nat.floor_le_floor <| inv_anti₀ ht'' <|
          sub_le_comm.1 ht.1
        rw [← Nat.cast_ofNat (R := ℝ), ← Nat.cast_pow, inv_inv, Nat.floor_natCast,
          Nat.log_pow one_lt_two _]
    have ht'' : 2 * (1 - (1 - t.1) * 2 ^ n) = 1 := by
      suffices h : t.1 = 1 - (2 ^ (n + 1))⁻¹ by
        rw [h, pow_succ]; simp [mul_sub, show (2 : ℝ) - 1 = 1 by ring]
      refine le_antisymm ht.2 ?_
      rw [sub_le_comm, ← hn, ← Nat.cast_ofNat (R := ℝ), ← Nat.cast_pow]
      refine le_trans (by rw [inv_inv]) <| inv_anti₀ (by simp) <| (Nat.cast_le.2 <|
        Nat.pow_log_le_self 2 ?_).trans <| Nat.floor_le (inv_pos.2 ht'').le
      exact (Nat.floor_pos.2 <| (one_le_inv₀ ht'').2 (σ t).2.2).ne'
    rw [ht'', extend_one]; convert (γ (n + 1)).source
    simp [hn, pow_succ]
    linarith

lemma countableConcatFun_one {γ : (n : ℕ) → Path (s n) (s (n + 1))} {x : X} :
    countableConcatFun γ x 1 = x := by
  simp [countableConcatFun]

/-- The concatenation of countably many paths `γ n` leading up to some point `x`. The condition
`hγx` is the precise condition needed in order for the concatenation to be continuous at `1`. -/
def countableConcat (γ : (n : ℕ) → Path (s n) (s (n + 1))) (x : X)
    (hγx : Tendsto (fun x : ℕ × I ↦ γ x.1 x.2) (atTop ×ˢ ⊤) (𝓝 x)) : Path (s 0) x where
  toFun := countableConcatFun γ x
  continuous_toFun := by
    refine continuous_iff_continuousAt.2 fun t ↦ ?_
    by_cases ht : t < 1
    · have ht' := symm_one ▸ symm_lt_symm.2 ht; have ht'' := coe_pos.2 ht'
      have hγ' : ∀ n, ContinuousOn (countableConcatFun γ x) _ :=
        fun n ↦ (Continuous.continuousOn (by continuity)).congr <| countableConcatFun_eqOn γ n
      cases h : Nat.log 2 ⌊(σ t : ℝ)⁻¹⌋₊ with
      | zero =>
        refine ContinuousOn.continuousAt (s := Set.Iic ⟨2⁻¹, by simp, ?_⟩) ?_ ?_
        · convert hγ' 0 using 1
          rw [← Set.Icc_bot, show (⊥ : I) = 0 by rfl]; convert rfl using 2 <;> ext
          all_goals simp [show (1 : ℝ) - 2⁻¹ = 2⁻¹ by ring, (one_div (2 : ℝ)) ▸ one_half_lt_one.le]
        · refine Iic_mem_nhds <| Subtype.coe_lt_coe.1 (?_ : t.1 < 2⁻¹)
          rw [Nat.log_eq_zero_iff, or_iff_left one_lt_two.not_le, Nat.floor_lt (inv_pos.2 ht'').le,
            inv_lt_comm₀ (by exact ht'') two_pos, coe_symm_eq, lt_sub_comm] at h
          exact h.trans_eq (by ring)
      | succ n =>
        refine ContinuousOn.continuousAt (s := Set.Icc
          ⟨1 - (2 ^ n)⁻¹, by simp [inv_le_one_of_one_le₀ <| one_le_pow₀ one_le_two (M₀ := ℝ)]⟩
          ⟨1 - (2 ^ (n + 2))⁻¹, by
            simp [inv_le_one_of_one_le₀ <| one_le_pow₀ one_le_two (M₀ := ℝ)]⟩) ?_ ?_
        · convert (hγ' n).union_isClosed isClosed_Icc isClosed_Icc <| hγ' (n + 1) using 1
          rw [add_assoc, one_add_one_eq_two, Set.Icc_union_Icc_eq_Icc]
          · rfl
          · simp only [symm_le_symm, Subtype.mk_le_mk]
            exact inv_anti₀ (by simp) <| pow_le_pow_right₀ one_le_two (by simp)
          · simp only [symm_le_symm, Subtype.mk_le_mk]
            exact inv_anti₀ (by simp) <| pow_le_pow_right₀ one_le_two (by simp)
        · refine Icc_mem_nhds ?_ ?_ <;> rw [← Subtype.coe_lt_coe, Subtype.coe_mk]
          · replace h := h.symm.le; rw [← Nat.pow_le_iff_le_log one_lt_two (Nat.floor_pos.2 <|
              (one_le_inv₀ ht'').2 (σ t).2.2).ne', Nat.le_floor_iff (inv_pos.2 ht'').le,
              le_inv_comm₀ (by simp) ht'', coe_symm_eq, sub_le_comm] at h
            refine (sub_lt_sub_left (inv_strictAnti₀ (by simp) ?_) 1).trans_le h
            rw [Nat.cast_pow, Nat.cast_ofNat]
            exact pow_lt_pow_right₀ one_lt_two n.lt_succ_self
          · replace h := h.trans_lt (Nat.lt_succ_self _); rw [← Nat.lt_pow_iff_log_lt one_lt_two
              (Nat.floor_pos.2 <| (one_le_inv₀ ht'').2 (σ t).2.2).ne', Nat.floor_lt
              (inv_pos.2 ht'').le, inv_lt_comm₀ ht'' (by simp), coe_symm_eq, lt_sub_comm] at h
            exact h.trans_eq <| by simp
    · rw [unitInterval.lt_one_iff_ne_one, not_ne_iff] at ht; rw [ht]
      unfold ContinuousAt
      intro u hu
      rw [countableConcatFun_one] at hu
      let ⟨n, hn⟩ : ∃ n : ℕ, ∀ m, n ≤ m → ∀ t, γ m t ∈ u := by
        simpa [tendsto_def, mem_prod_top] using hγx hu
      rw [mem_map, mem_nhds_iff]
      use Set.Ioi ⟨1 - (2 ^ n)⁻¹, by rw [sub_nonneg, inv_le_one₀] <;> simp [one_le_pow₀], by simp⟩
      refine ⟨fun t ht ↦ ?_, isOpen_Ioi, by simp [← coe_lt_one]⟩
      by_cases ht' : t < 1
      · have ht'' := symm_one ▸ symm_lt_symm.2 ht'; have ht''' := coe_pos.2 ht''
        simp only [mem_preimage, countableConcatFun, ht', reduceDIte]
        refine hn _ ?_ _
        rw [← Nat.pow_le_iff_le_log one_lt_two (Nat.floor_pos.2 <| (one_le_inv₀ ht''').2
          (σ t).2.2).ne', Nat.le_floor_iff (inv_pos.2 ht''').le, le_inv_comm₀ (by simp) ht''',
          coe_symm_eq, sub_le_comm]
        apply le_of_lt; simpa using ht
      · rw [unitInterval.lt_one_iff_ne_one, not_ne_iff] at ht'; rw [ht']
        rw [mem_preimage, countableConcatFun_one]; exact mem_of_mem_nhds hu
  source' := by simp [countableConcatFun]
  target' := by simp [countableConcatFun]

private lemma one_sub_half_div_two_pow_mem_unitInterval {t : I} {n : ℕ} :
    (1 - (t : ℝ) / 2) / 2 ^ n ∈ I :=
  ⟨div_nonneg (by linarith [t.2.2]) (by simp), (div_le_one₀ (by simp)).2 <| by
    linarith [one_le_pow₀ (M₀ := ℝ) one_le_two (n := n), t.2.1]⟩

/-- Evaluating `Path.countableConcat` at 1-(1-t/2)/2^n yields `γ n t`. -/
lemma countableConcat_applyAt {γ : (n : ℕ) → Path (s n) (s (n + 1))} {x : X}
    (hγx : Tendsto (fun x : ℕ × I ↦ γ x.1 x.2) (atTop ×ˢ ⊤) (𝓝 x)) (n : ℕ) (t : I) :
    countableConcat γ x hγx (σ ⟨(1 - t / 2) / 2 ^ n, one_sub_half_div_two_pow_mem_unitInterval⟩) =
    γ n t := by
  rw [countableConcat, coe_mk_mk]
  refine (countableConcatFun_eqOn γ n ⟨?_, ?_⟩).trans ?_
  · rw [symm_le_symm, Subtype.mk_le_mk, ← one_div]
    exact div_le_div_of_nonneg_right (by linarith [t.2.1]) (by simp)
  · rw [symm_le_symm, Subtype.mk_le_mk, pow_succ', ← one_div, ← div_div]
    exact div_le_div_of_nonneg_right (by linarith [t.2.2]) (by simp)
  · simp [mul_div_cancel₀ t.1 two_pos.ne']

/-- The concatenation of a sequence of paths is the same as the concatenation of the first path
with the concatenation of the remaining paths. -/
lemma countableConcat_eq_trans {γ : (n : ℕ) → Path (s n) (s (n + 1))} {x : X}
    (hγx : Tendsto (fun x : ℕ × I ↦ γ x.1 x.2) (atTop ×ˢ ⊤) (𝓝 x)) :
    countableConcat γ x hγx = (γ 0).trans (countableConcat (fun n ↦ γ (n + 1)) x <|
      hγx.comp ((tendsto_add_atTop_nat 1).prodMap tendsto_id)) := by
  ext t
  by_cases ht : (t : ℝ) ≤ 1 / 2 <;> dsimp [trans, countableConcat] <;> simp only [ht, ↓reduceIte]
  · refine (countableConcatFun_eqOn γ 0 ?_).trans <| by simp
    simpa [← Subtype.coe_le_coe, show (1 - 2⁻¹ : ℝ) = 2⁻¹ by ring] using ht
  · apply lt_of_not_le at ht
    by_cases ht' : t < 1
    · dsimp [extend, IccExtend, countableConcatFun]
      have ht'' : 0 < 1 - t.1 := by linarith [unitInterval.coe_lt_one.2 ht']
      have h : (projIcc 0 1 one_pos.le (2 * t.1 - 1) : ℝ) = 2 * t - 1 := by
        rw [projIcc_of_mem _ ⟨by linarith, by linarith⟩]
      simp only [ht', ↓reduceDIte, ← Subtype.coe_lt_coe, h, Icc.coe_one,
        show 2 * t.1 - 1 < 1 by linarith]
      refine congr (congrArg (fun n ↦ ⇑(γ n)) ?_) ?_
      · rw [h, ← sub_add, ← add_sub_right_comm, one_add_one_eq_two, ← mul_one_sub,
          mul_inv, ← div_eq_inv_mul, Nat.floor_div_ofNat, Nat.log_div_base]
        refine (Nat.sub_one_add_one (Nat.log_pos one_lt_two ?_).ne').symm
        rw [Nat.le_floor_iff (inv_pos.2 ht'').le]
        exact le_inv_of_le_inv₀ ht'' <| by linarith
      · rw [Subtype.mk_eq_mk, ← sub_add, ← add_sub_right_comm, one_add_one_eq_two, ← mul_one_sub,
          mul_inv, ← div_eq_inv_mul]
        rw [Nat.floor_div_ofNat, Nat.log_div_base]
        simp_rw [Nat.cast_pow]; rw [pow_sub₀ _ two_pos.ne' ?_]
        · ring
        · rw [← Nat.pow_le_iff_le_log one_lt_two <| (Nat.floor_pos.2 <| (one_le_inv₀ ht'').2
            (by exact (σ t).2.2)).ne', Nat.le_floor_iff (inv_pos.2 ht'').le]
          exact le_inv_of_le_inv₀ ht'' <| by linarith
    · rw [show t = 1 by simpa [unitInterval.lt_one_iff_ne_one] using ht']
      simp [show (2 - 1 : ℝ) = 1 by ring, countableConcatFun]

/-- The image of a countable concatenation of paths is the concatenation of the images. -/
lemma map_countableConcat {γ : (n : ℕ) → Path (s n) (s (n + 1))} {x : X}
    {hγx : Tendsto (fun x : ℕ × I ↦ γ x.1 x.2) (atTop ×ˢ ⊤) (𝓝 x)} {f : X → Y} (hf : Continuous f) :
    (countableConcat γ x hγx).map hf =
      countableConcat (fun n ↦ (γ n).map hf) (f x) ((hf.tendsto x).comp hγx) := by
  ext t
  by_cases ht : t < 1 <;> simp [countableConcat, countableConcatFun, ht]

end Path
