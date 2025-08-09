/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Lie.Semisimple.Defs
import Mathlib.Algebra.Lie.Weights.Linear
import Mathlib.Algebra.Module.Submodule.Union

/-!
# Geck's construction of a Lie algebra associated to a root system yields semisimple algebras

This file contains a proof that `RootPairing.GeckConstruction.lieAlgebra` yields semisimple Lie
algebras.

## Main definitions:
...

-/

noncomputable section

namespace RootPairing.GeckConstruction

open Function Module.End
open Set hiding diagonal
open scoped Matrix

variable {ι K M N : Type*}
  [DecidableEq ι] [Fintype ι]
  [Field K] [CharZero K]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootSystem ι K M N} [P.IsCrystallographic]
  {b : P.Base}

open Module Submodule in
omit [DecidableEq ι] in
lemma exists_distinct_blah :
    ∃ d : ι → K, (∀ i, d i ≠ 0) ∧ Pairwise ((· ≠ ·) on d) ∧
      d ∈ span K (range fun (i : b.support) j ↦ (P.pairingIn ℤ j i : K)) := by
  rcases isEmpty_or_nonempty ι; · simpa using ⟨0, Submodule.zero_mem _⟩
  set p := span K (range fun (i : b.support) j ↦ (P.pairingIn ℤ j i : K))
  let f : ι ⊕ {(i, j) : ι × ι | i ≠ j} → Dual K (ι → K) :=
    Sum.elim LinearMap.proj
      (fun ij ↦ LinearMap.proj (R := K) (φ := fun _ ↦ K) ij.1.1 - LinearMap.proj ij.1.2)
  suffices ∃ d ∈ p, ∀ i, f i d ≠ 0 by
    obtain ⟨d, hp, hf⟩ := this
    refine ⟨d, fun i ↦ hf (Sum.inl i), fun i j h ↦ ?_, hp⟩
    simpa [f, sub_eq_zero] using hf (Sum.inr ⟨⟨i, j⟩, h⟩)
  apply Module.Dual.exists_forall_mem_ne_zero_of_forall_exists p f
  rintro (i | ⟨⟨i, j⟩, h : i ≠ j⟩)
  · obtain ⟨j, hj, hj₀⟩ := b.exists_mem_support_pos_pairingIn_ne_zero i
    refine ⟨fun i ↦ P.pairingIn ℤ i j, subset_span ⟨⟨j, hj⟩, rfl⟩, ?_⟩
    rw [ne_eq, P.pairingIn_eq_zero_iff] at hj₀
    simpa [f, ne_eq, Int.cast_eq_zero]
  · obtain ⟨k, hk, hk'⟩ : ∃ k ∈ b.support, P.pairingIn ℤ i k ≠ P.pairingIn ℤ j k := by
      contrapose! h
      apply b.injective_pairingIn
      aesop
    simpa [f, p, sub_eq_zero] using
      ⟨fun i ↦ P.pairingIn ℤ i k, subset_span ⟨⟨k, hk⟩, rfl⟩, by simpa⟩

open LieModule Matrix Submodule in
lemma bar {χ : cartanSubalgebra' b → K} (hχ : χ ≠ 0) {w : b.support ⊕ ι → K} (hw₀ : w ≠ 0)
    (hw : w ∈ genWeightSpace (b.support ⊕ ι → K) χ) :
    ∃ (i : ι) (t : K), t • w = Pi.single (Sum.inr i) 1 := by
  cases isEmpty_or_nonempty ι; · (suffices w = 0 by contradiction); apply Subsingleton.elim
  have aux (d : b.support ⊕ ι → K) (μ : K) :
      (diagonal d).toLin' - μ • 1 = (diagonal (d - μ • 1)).toLin' := by
    aesop (add simp Pi.single_apply)
  replace aux (d : b.support ⊕ ι → K) (x : cartanSubalgebra' b) (hdx : x = diagonal d) :
      w ∈ genWeightSpaceOf (b.support ⊕ ι → K) (χ x) x ↔
        ∃ k, diagonal ((d - χ x • 1) ^ k) *ᵥ w = 0 := by
    set μ := χ x
    obtain ⟨⟨x, hx⟩, hx'⟩ := x
    replace hdx : x = diagonal d := by simpa using hdx
    simp [mem_genWeightSpaceOf, hdx, aux, ← toLin'_pow, diagonal_pow]
  obtain ⟨i, hi⟩ : ∃ i, w (Sum.inr i) ≠ 0 := by
    obtain ⟨l, hl⟩ : ∃ l, χ (h' l) ≠ 0 := by
      replace hw₀ : genWeightSpace (b.support ⊕ ι → K) χ ≠ ⊥ := by
        contrapose! hw₀; rw [LieSubmodule.eq_bot_iff] at hw₀; exact hw₀ _ hw
      let χ' : cartanSubalgebra' b →ₗ[K] K := (Weight.mk χ hw₀).toLinear
      replace hχ : χ' ≠ 0 := by contrapose! hχ; ext x; simpa using LinearMap.congr_fun hχ x
      contrapose! hχ
      apply LinearMap.ext_on (span_range_h'_eq_top b)
      rintro - ⟨l, rfl⟩
      simp [χ', hχ l]
    contrapose! hw₀
    suffices ∀ i : b.support, w (Sum.inl i) = 0 by aesop
    intro i
    replace hw := genWeightSpace_le_genWeightSpaceOf (b.support ⊕ ι → K) (h' l) χ hw
    rw [aux (Sum.elim 0 (P.pairingIn ℤ · l)) (h' l) (h_eq_diagonal l)] at hw
    obtain ⟨k, hk⟩ := hw
    replace hk := congr_fun hk (Sum.inl i)
    simpa [Matrix.mulVec_eq_sum, Matrix.diagonal_apply, hl] using hk
  refine ⟨i, (w (Sum.inr i))⁻¹, ?_⟩
  suffices ∃ d : ι → K, (∀ i, d i ≠ 0) ∧ Pairwise ((· ≠ ·) on d) ∧
      diagonal (Sum.elim 0 d) ∈ cartanSubalgebra b by
    obtain ⟨d, hd₀, hd₁, hd₂⟩ := this
    let x : cartanSubalgebra' b :=
      ⟨⟨diagonal (Sum.elim 0 d), cartanSubalgebra_le_lieAlgebra hd₂⟩, hd₂⟩
    replace hw := genWeightSpace_le_genWeightSpaceOf (b.support ⊕ ι → K) x χ hw
    rw [aux (Sum.elim 0 d) x rfl] at hw
    obtain ⟨k, hk⟩ := hw
    obtain ⟨hχx, hk₀⟩ : d i = χ x ∧ k ≠ 0 := by
      simpa [hi, Matrix.mulVec_eq_sum, Matrix.diagonal_apply, sub_eq_zero] using
        congr_fun hk (Sum.inr i)
    ext (j | j)
    · have : χ x ≠ 0 := hχx ▸ hd₀ i
      simpa [hi, Matrix.mulVec_eq_sum, Matrix.diagonal_apply, hk₀, this] using
        congr_fun hk (Sum.inl j)
    · rcases eq_or_ne i j with rfl | hij
      · simp [hi]
      · suffices w (Sum.inr j) = 0 by simpa [hij, hi]
        suffices d j ≠ χ x by
          simpa [Matrix.mulVec_eq_sum, Matrix.diagonal_apply, sub_eq_zero, this] using
            congr_fun hk (Sum.inr j)
        rw [← hχx]
        exact hd₁ <| by simp [hij.symm]
  simp_rw [cartanSubalgebra, LieSubalgebra.mem_mk_iff', diagonal_elim_mem_span_h_iff]
  exact exists_distinct_blah

open LieModule Submodule in
lemma baz :
    letI u (i : b.support) : b.support ⊕ ι → K := Pi.single (Sum.inl i) 1
    genWeightSpace (b.support ⊕ ι → K) (0 : cartanSubalgebra' b → K) = span K (range u) := by
  let u (i : b.support) : b.support ⊕ ι → K := Pi.single (Sum.inl i) 1
  apply le_antisymm
  · intro w hw
    replace hw : ∀ (x) (hx : x ∈ lieAlgebra b), ⟨x, hx⟩ ∈ cartanSubalgebra' b →
        ∃ k, (x.toLin' ^ k) w = 0 := by simpa [mem_genWeightSpace] using hw
    rw [Pi.mem_span_range_single_inl_iff]
    intro i
    obtain ⟨j, hj⟩ : ∃ j : b.support, P.pairingIn ℤ i j ≠ 0 := by
      obtain ⟨j, hj, hj₀⟩ := b.exists_mem_support_pos_pairingIn_ne_zero i
      rw [ne_eq, P.pairingIn_eq_zero_iff] at hj₀
      exact ⟨⟨j, hj⟩, hj₀⟩
    obtain ⟨k, hk⟩ := hw (h j) (h_mem_lieAlgebra j) (h_mem_cartanSubalgebra' j _)
    simpa [h_eq_diagonal, ← Matrix.toLin'_pow, Matrix.fromBlocks_diagonal_pow, Matrix.diagonal_pow,
      Matrix.mulVec_eq_sum, Matrix.diagonal_apply, hj] using congr_fun hk (Sum.inr i)
  · rw [span_le]
    rintro - ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LieSubmodule.mem_toSubmodule, LieModule.mem_genWeightSpace]
    intro ⟨⟨x, hx'⟩, hx⟩
    use 1
    ext j
    suffices x j (Sum.inl i) = 0 by simpa
    replace hx : x ∈ span K (range h) := by simpa [cartanSubalgebra] using hx
    clear hx'
    induction hx using span_induction with
    | mem x h => obtain ⟨i, rfl⟩ := h; cases j <;> simp [h]
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul t u _ hu => simp [hu]

/-- An auxiliary lemma en route to `RootPairing.GeckConstruction.instIsIrreducible` (where the same
conclusion is proved with the hypothesis `hi` weakened to just `U ≠ ⊥`). -/
private lemma instIsIrreducible_aux₀ [P.IsReduced] [P.IsIrreducible]
    {U : LieSubmodule K (lieAlgebra b) (b.support ⊕ ι → K)} {i : ι}
    (hi : Pi.single (Sum.inr i) 1 ∈ U) :
    U = ⊤ := by
  letI _i := P.indexNeg
  let u (i : b.support) : b.support ⊕ ι → K := Pi.single (Sum.inl i) 1
  let v (i : ι) : b.support ⊕ ι → K := Pi.single (Sum.inr i) 1
  have hωu (i : b.support) : ω b *ᵥ (u i) = u i := by
    ext (j | j) <;> simp [ω, u, Pi.single_apply, Matrix.one_apply]
  have hωv (i : ι) : ω b *ᵥ (v i) = v (-i) := by ext (j | j) <;> simp [ω, v, Pi.single_apply]
  change v i ∈ U at hi
  obtain ⟨j, hj⟩ : ∃ j : b.support, u j ∈ U := by
    revert U
    apply b.induction_add i
    · intro i h U hi
      replace hi : v i ∈ ωConjLieSubmodule U := by simpa [hωv]
      obtain ⟨j, hj⟩ := h hi
      exact ⟨j, by simpa [hωu] using hj⟩
    · intro j hj U hj'
      let f' : lieAlgebra b := ⟨f ⟨j, hj⟩, f_mem_lieAlgebra _⟩
      have : ⁅f', v j⁆ = u ⟨j, hj⟩ := f_v_same ⟨j, hj⟩
      replace this : u ⟨j, hj⟩ ∈ U := by
        rw [← this]
        exact U.lie_mem (x := f') hj'
      exact ⟨⟨j, hj⟩, this⟩
    · intro j k l h₁ h₂ hk U hl
      have : ⁅f ⟨k, hk⟩, v l⁆ = (P.chainTopCoeff k l + 1 : K) • v j := f_v_ne h₁
      replace this : (P.chainTopCoeff k l + 1 : K) • v j ∈ U := by
        rw [← this]
        let f' : lieAlgebra b := ⟨f ⟨k, hk⟩, f_mem_lieAlgebra _⟩
        change ⁅f', v l⁆ ∈ U
        exact U.lie_mem hl
      exact h₂ <| (U.smul_mem_iff (by norm_cast)).mp this
  have aux (k : b.support) : u k ∈ U := by
    refine b.induction_on_cartanMatrix (fun k : b.support ↦ u k ∈ U) hj (fun l l' hl₁ hl₂ ↦ ?_)
    suffices (↑|b.cartanMatrix l' l| : K) • u l' ∈ U from (U.smul_mem_iff (by simpa)).mp this
    rw [Int.cast_smul_eq_zsmul, ← lie_e_lie_f_apply l' l]
    let e' : lieAlgebra b := ⟨e l', e_mem_lieAlgebra l'⟩
    let f' : lieAlgebra b := ⟨f l', f_mem_lieAlgebra l'⟩
    change ⁅e', ⁅f', u l⁆⁆ ∈ U
    exact U.lie_mem <| U.lie_mem hl₁
  clear! j i
  suffices ∀ j, v j ∈ U by
    simp_rw [← LieSubmodule.toSubmodule_eq_top, eq_top_iff,
      ← (Pi.basisFun K (b.support ⊕ ι)).span_eq, Submodule.span_le, range_subset_iff,
      Pi.basisFun_apply]
    aesop
  intro j
  revert U
  apply b.induction_add j
  · intro j h U hU
    suffices v j ∈ ωConjLieSubmodule U by simpa [hωv] using this
    exact h fun k ↦ by simp [hωu, hU]
  · intro k hk U aux
    have : ⁅e ⟨k, hk⟩, u ⟨k, hk⟩⁆ = (2 : K) • v k := e_u_same ⟨k, hk⟩
    let e' : lieAlgebra b := ⟨e ⟨k, hk⟩, e_mem_lieAlgebra ⟨k, hk⟩⟩
    change ⁅e', u ⟨k, hk⟩⁆ = _ at this
    replace aux := U.lie_mem (x := e') <| aux ⟨k, hk⟩
    rw [this] at aux
    exact (U.smul_mem_iff two_ne_zero).mp aux
  · intro k l m hm hk hl U aux
    rw [add_comm] at hm
    let e' : lieAlgebra b := ⟨e ⟨l, hl⟩, e_mem_lieAlgebra _⟩
    have : ⁅e', v k⁆ = (P.chainBotCoeff l k + 1 : K) • v m := e_v_ne hm
    replace this : (P.chainBotCoeff l k + 1 : K) • v m ∈ U := by
      rw [← this]
      exact U.lie_mem (hk aux)
    exact (U.smul_mem_iff (by norm_cast)).mp this

set_option maxHeartbeats 500000 in -- Temporary
open LieModule Submodule in
lemma bar' (U : LieSubmodule K (cartanSubalgebra' b) (b.support ⊕ ι → K))
    (hU : ¬ U ≤ genWeightSpace (b.support ⊕ ι → K) 0) :
    ∃ i, Pi.single (Sum.inr i) 1 ∈ U := by
  let v (i : ι) : b.support ⊕ ι → K := Pi.single (Sum.inr i) 1
  let H := cartanSubalgebra' b
  have key (χ : H → K) (hχ : χ ≠ 0) (hχ' : LieModule.genWeightSpace U χ ≠ ⊥) :
      ∃ i, v i ∈ (LieModule.genWeightSpace U χ).map U.incl := by
    obtain ⟨w, hw, hw₀⟩ : ∃ w ∈ LieModule.genWeightSpace U χ, w ≠ 0 := by
      simpa only [ne_eq, LieSubmodule.eq_bot_iff, not_forall, exists_prop] using hχ'
    replace hw : U.incl w ∈ LieModule.genWeightSpace (b.support ⊕ ι → K) χ :=
      LieModule.map_genWeightSpace_le (f := U.incl) <| by simpa
    obtain ⟨i, t, hi : t • w = v i⟩ := bar hχ (by simpa) hw
    use i
    rw [LieModule.map_genWeightSpace_eq_of_injective U.injective_incl, LieSubmodule.range_incl,
      ← hi, LieSubmodule.mem_inf]
    exact ⟨SMulMemClass.smul_mem _ hw, SMulMemClass.smul_mem _ w.property⟩
  obtain ⟨x, hx⟩ : ∃ x : U, x ∉ LieModule.genWeightSpace U (0 : H → K) := by
    contrapose! hU
    refine le_trans ?_ <| LieModule.map_genWeightSpace_le (f := U.incl)
    exact fun x hx ↦ by simpa [hx] using hU ⟨x, hx⟩
  suffices ∃ᵉ (χ : H → K) (i : ι), v i ∈ (LieModule.genWeightSpace U χ).map U.incl by
    obtain ⟨χ, i, hi⟩ := this
    exact ⟨i, LieSubmodule.map_incl_le hi⟩
  suffices ∃ χ : H → K, χ ≠ 0 ∧ LieModule.genWeightSpace U χ ≠ ⊥ by
    obtain ⟨χ, hχ₀, hχ⟩ := this
    exact ⟨χ, key χ hχ₀ hχ⟩
  contrapose! hx
  -- TODO Pretty gross from here: does the broader API need some love or is this PEBKAC?
  have aux := iSup_split (LieModule.genWeightSpace U) fun χ : H → K ↦ χ = 0
  rw [biSup_congr hx] at aux
  change _ = _ ⊔ (⨆ χ ∈ {χ : H → K | χ ≠ 0}, ⊥) at aux
  rw [biSup_const ⟨1, by simp⟩, sup_bot_eq] at aux
  change _ = ⨆ χ ∈ {χ : H → K | χ = 0}, _ at aux
  simp_rw [setOf_eq_eq_singleton, iSup_singleton] at aux
  rw [← aux, LieModule.iSup_genWeightSpace_eq_top K H U]
  simp

-- TODO Turn this `variable` into a lemma: it is always true and may be proved via Perron-Frobenius
-- See https://leanprover.zulipchat.com/#narrow/channel/116395-maths/topic/Eigenvalues.20of.20Cartan.20matrices/near/516844801
variable [Fact ((4 - b.cartanMatrix).det ≠ 0)]

open LieModule Submodule in
lemma foo
    (U : LieSubmodule K (lieAlgebra b) (b.support ⊕ ι → K)) (hU : U ≠ ⊥) :
    ∃ i, Pi.single (Sum.inr i) 1 ∈ U := by
  let u (i : b.support) : b.support ⊕ ι → K := Pi.single (Sum.inl i) 1
  let v (i : ι) : b.support ⊕ ι → K := Pi.single (Sum.inr i) 1
  let H := cartanSubalgebra' b
  let U' : LieSubmodule K H (b.support ⊕ ι → K) := {U with lie_mem := U.lie_mem}
  have hU' : U'.toSubmodule = U.toSubmodule := rfl
  apply bar' U'
  contrapose! hU
  replace hU : U ≤ span K (range u) := by
    rwa [← baz, ← hU', LieSubmodule.toSubmodule_le_toSubmodule]
  refine (LieSubmodule.eq_bot_iff _).mpr fun x hx ↦ ?_
  obtain ⟨c, hc⟩ : ∃ c : b.support → K, ∑ i, c i • u i = x :=
    (mem_span_range_iff_exists_fun K).mp <| hU hx
  suffices c = 0 by simp [this, ← hc]
  have hCM : (4 - b.cartanMatrix).det ≠ 0 := Fact.out
  contrapose! hCM
  suffices ((Int.castRingHom K).mapMatrix (4 - b.cartanMatrix)).det = 0 by
    simpa only [← RingHom.map_det, eq_intCast, Int.cast_eq_zero] using this
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨c, hCM, ?_⟩
  simp only [RingHom.mapMatrix_apply]
  suffices (b.cartanMatrix.map abs).map (↑) *ᵥ c = 0 by simpa using this
  ext j
  simp only [Matrix.mulVec_eq_sum, op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply,
    Matrix.transpose_apply, Matrix.map_apply, smul_eq_mul, Pi.zero_apply]
  have key : ⁅e j, x⁆ ∈ U := U.lie_mem (x := ⟨e j, e_mem_lieAlgebra j⟩) hx
  have aux (k : b.support) : ⁅e j, u k⁆ = |b.cartanMatrix j k| • v j := e_u j k
  simp_rw [← hc, lie_sum, lie_smul, aux, smul_comm (M := K), ← smul_assoc, ← Finset.sum_smul,
    zsmul_eq_mul, mul_comm] at key
  suffices v j ∉ U by
    by_contra contra
    rw [← LieSubmodule.mem_toSubmodule, U.smul_mem_iff contra] at key
    contradiction
  intro contra
  suffices ∀ {x : b.support ⊕ ι → K} (hx : x ∈ span K (range u)), x (Sum.inr j) = 0 by
    simpa [v] using this (hU contra)
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x h => obtain ⟨i, rfl⟩ := h; simp [u]
  | zero => simp
  | add u v _ _ hu hv => simp [hu, hv]
  | smul t u _ hu => simp [hu]

/-- Lemma 4.2 from [Geck](Geck2017). -/
instance instIsIrreducible [P.IsReduced] [P.IsIrreducible] [Nonempty ι] :
    LieModule.IsIrreducible K (lieAlgebra b) (b.support ⊕ ι → K) := by
  refine LieModule.IsIrreducible.mk fun U hU ↦ ?_
  let v (i : ι) : b.support ⊕ ι → K := Pi.single (Sum.inr i) 1
  set H := cartanSubalgebra' b
  suffices ∃ i, v i ∈ U by obtain ⟨i, hi⟩ := this; exact instIsIrreducible_aux₀ hi
  exact foo U hU


end RootPairing.GeckConstruction
