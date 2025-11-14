/-
Copyright (c) 2024 Lucas Whitfield. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucas Whitfield, Johan Commelin
-/
import Mathlib.Algebra.Lie.Weights.Basic
import Mathlib.RingTheory.Finiteness.Nilpotent

/-!
# Lie's theorem for Solvable Lie algebras.

Lie's theorem asserts that Lie modules of solvable Lie algebras over fields of characteristic 0
have a common eigenvector for the action of all elements of the Lie algebra.
This result is named `LieModule.exists_forall_lie_eq_smul_of_isSolvable`.
-/

namespace LieModule

section

/-
The following variables generalize the setting where:
- `R` is a principal ideal domain of characteristic zero,
- `L` is a Lie algebra over `R`,
- `V` is a Lie algebra module over `L`
- `A` is a Lie ideal of `L`.
Besides generalizing, it also make the proof of `lie_stable` syntactically smoother.
-/
variable {R L A V : Type*} [CommRing R]
variable [IsPrincipalIdealRing R] [IsDomain R] [CharZero R]
variable [LieRing L] [LieAlgebra R L]
variable [LieRing A] [LieAlgebra R A]
variable [Bracket L A] [Bracket A L]
variable [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
variable [LieRingModule L V] [LieModule R L V]
variable [LieRingModule A V] [LieModule R A V]
variable [IsLieTower L A V] [IsLieTower A L V]

variable (χ : A → R)

open Module (finrank)
open LieModule

local notation "π" => LieModule.toEnd R _ V

private abbrev T (w : A) : Module.End R V := (π w) - χ w • 1

/-- An auxiliary lemma used only in the definition `LieModule.weightSpaceOfIsLieTower` below. -/
private lemma weightSpaceOfIsLieTower_aux (z : L) (v : V) (hv : v ∈ weightSpace V χ) :
    ⁅z, v⁆ ∈ weightSpace V χ := by
  rw [mem_weightSpace] at hv ⊢
  intro a
  rcases eq_or_ne v 0 with (rfl | hv')
  · simp only [lie_zero, smul_zero]
  suffices χ ⁅z, a⁆ = 0 by
    rw [leibniz_lie, hv a, lie_smul, lie_swap_lie, hv, this, zero_smul, neg_zero, zero_add]
  let U' : ℕ →o Submodule R V :=
  { toFun n := Submodule.span R {((π z)^i) v | i < n},
    monotone' i j h := Submodule.span_mono (fun _ ⟨c, hc, hw⟩ ↦ ⟨c, lt_of_lt_of_le hc h, hw⟩) }
  have map_U'_le (n : ℕ) : Submodule.map (π z) (U' n) ≤ U' (n + 1) := by
    simp only [OrderHom.coe_mk, Submodule.map_span, toEnd_apply_apply, U']
    apply Submodule.span_mono
    suffices ∀ a < n, ∃ b < n + 1, ((π z) ^ b) v = ((π z) ^ (a + 1)) v by simpa [pow_succ']
    aesop
  have T_apply_succ (w : A) (n : ℕ) :
      Submodule.map (T χ w) (U' (n + 1)) ≤ U' n := by
    simp only [OrderHom.coe_mk, U', Submodule.map_span, Submodule.span_le, Set.image_subset_iff]
    simp only [Set.subset_def, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    induction n generalizing w
    · simp only [zero_add, Nat.lt_one_iff, LinearMap.sub_apply, LieModule.toEnd_apply_apply,
        LinearMap.smul_apply, Module.End.one_apply, forall_eq, pow_zero, hv w, sub_self, zero_mem]
    · next n hn =>
      intro m hm
      obtain (hm | rfl) : m < n + 1 ∨ m = n + 1 := by cutsat
      · exact U'.mono (Nat.le_succ n) (hn w m hm)
      have H : ∀ w, ⁅w, (π z ^ n) v⁆ = (T χ w) ((π z ^ n) v) + χ w • ((π z ^ n) v) := by simp
      rw [T, LinearMap.sub_apply, pow_succ', Module.End.mul_apply, LieModule.toEnd_apply_apply,
        LieModule.toEnd_apply_apply, LinearMap.smul_apply, Module.End.one_apply, leibniz_lie,
        lie_swap_lie w z, H, H, lie_add, lie_smul, add_sub_assoc, add_sub_assoc, sub_self, add_zero]
      refine add_mem (neg_mem <| add_mem ?_ ?_) ?_
      · exact U'.mono n.le_succ (hn _ n n.lt_succ_self)
      · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, n.lt_succ_self, rfl⟩)
      · exact map_U'_le _ <| Submodule.mem_map_of_mem <| hn w n n.lt_succ_self
  set U : LieSubmodule R A V :=
  { toSubmodule := ⨆ k : ℕ, U' k
    lie_mem {w} x hx := by
      rw [show ⁅w, x⁆ = (T χ w) x + χ w • x by simp]
      apply add_mem _ (Submodule.smul_mem _ _ hx)
      set U := ⨆ k : ℕ, U' k
      suffices Submodule.map (T χ w) U ≤ U from this <| Submodule.mem_map_of_mem hx
      rw [Submodule.map_iSup, iSup_le_iff]
      rintro (_ | i)
      · simp [U']
      · exact (T_apply_succ w i).trans (le_iSup _ _) }
  have hzU (x : V) (hx : x ∈ U) : (π z) x ∈ U := by
    suffices Submodule.map (π z) U ≤ U from this <| Submodule.mem_map_of_mem hx
    simp only [U, Submodule.map_iSup, iSup_le_iff]
    exact fun i ↦ (map_U'_le i).trans (le_iSup _ _)
  have trace_za_zero : (LieModule.toEnd R A _ ⁅z, a⁆).trace R U = 0 := by
    have hres : LieModule.toEnd R A U ⁅z, a⁆ = ⁅(π z).restrict hzU, LieModule.toEnd R A U a⁆ := by
      ext ⟨x, hx⟩
      change ⁅⁅z, a⁆, x⁆ = ⁅z, ⁅a, x⁆⁆ - ⁅a, ⁅z, x⁆⁆
      simp only [leibniz_lie z a, add_sub_cancel_right]
    rw [hres, LinearMap.trace_lie]
  have trace_T_U_zero (w : A) : (T χ w).trace R U = 0 := by
    have key (i : ℕ) (hi : i ≠ 0) : ∃ j < i, Submodule.map (T χ w) (U' i) ≤ U' j := by
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
      exact ⟨j, j.lt_succ_self, T_apply_succ w j⟩
    apply IsNilpotent.eq_zero
    apply LinearMap.isNilpotent_trace_of_isNilpotent
    rw [Module.End.isNilpotent_iff_of_finite]
    suffices ⨆ i, U' i ≤ Module.End.maxGenEigenspace (T χ w) 0 by
      intro x
      specialize this x.2
      simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero] at this
      peel this with n hn
      ext
      simp only [ZeroMemClass.coe_zero, ← hn]; clear hn
      induction n <;> simp_all [pow_succ']
    apply iSup_le
    intro i x hx
    simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero]
    induction i using Nat.strong_induction_on generalizing x
    next i ih =>
    obtain rfl | hi := eq_or_ne i 0
    · simp_all [U']
    obtain ⟨j, hj, hj'⟩ := key i hi
    obtain ⟨k, hk⟩ := ih j hj (hj' <| Submodule.mem_map_of_mem hx)
    use k+1
    rw [pow_succ, Module.End.mul_apply, hk]
  have trace_za : (toEnd R A _ ⁅z, a⁆).trace R U = χ ⁅z, a⁆ • (finrank R U) := by
    simpa [T, sub_eq_zero] using trace_T_U_zero ⁅z, a⁆
  suffices finrank R U ≠ 0 by simp_all
  suffices Nontrivial U from Module.finrank_pos.ne'
  have hvU : v ∈ U := by
    apply Submodule.mem_iSup_of_mem 1
    apply Submodule.subset_span
    use 0, zero_lt_one
    rw [pow_zero, Module.End.one_apply]
  exact nontrivial_of_ne ⟨v, hvU⟩ 0 <| by simp [hv']

variable (R V) in
/-- The weight space of `V` with respect to `χ : A → R`, a priori a Lie submodule for `A`, is also a
Lie submodule for `L`. -/
def weightSpaceOfIsLieTower (χ : A → R) : LieSubmodule R L V :=
  { toSubmodule := weightSpace V χ
    lie_mem {z v} hv := weightSpaceOfIsLieTower_aux χ z v hv }

end

section

variable {k : Type*} [Field k]
variable {L : Type*} [LieRing L] [LieAlgebra k L]
variable {V : Type*} [AddCommGroup V] [Module k V] [LieRingModule L V] [LieModule k L V]

variable [CharZero k] [Module.Finite k V]

open Submodule in
theorem exists_nontrivial_weightSpace_of_lieIdeal [LieModule.IsTriangularizable k L V]
    (A : LieIdeal k L) (hA : IsCoatom A.toSubmodule)
    (χ₀ : Module.Dual k A) [Nontrivial (weightSpace V χ₀)] :
    ∃ (χ : Module.Dual k L), Nontrivial (weightSpace V χ) := by
  obtain ⟨z, -, hz⟩ := SetLike.exists_of_lt (hA.lt_top)
  let e : (k ∙ z) ≃ₗ[k] k := (LinearEquiv.toSpanNonzeroSingleton k L z <| by aesop).symm
  have he : ∀ x, e x • z = x := by simp [e]
  have hA : IsCompl A.toSubmodule (k ∙ z) := isCompl_span_singleton_of_isCoatom_of_notMem hA hz
  let π₁ : L →ₗ[k] A       := A.toSubmodule.linearProjOfIsCompl (k ∙ z) hA
  let π₂ : L →ₗ[k] (k ∙ z) := (k ∙ z).linearProjOfIsCompl ↑A hA.symm
  set W : LieSubmodule k L V := weightSpaceOfIsLieTower k V χ₀
  obtain ⟨c, hc⟩ : ∃ c, (toEnd k _ W z).HasEigenvalue c := by
    have : Nontrivial W := inferInstanceAs (Nontrivial (weightSpace V χ₀))
    apply Module.End.exists_hasEigenvalue_of_genEigenspace_eq_top
    exact LieModule.IsTriangularizable.maxGenEigenspace_eq_top z
  obtain ⟨⟨v, hv⟩, hvc⟩ := hc.exists_hasEigenvector
  have hv' : ∀ (x : ↥A), ⁅x, v⁆ = χ₀ x • v := by
    simpa [W, weightSpaceOfIsLieTower, mem_weightSpace] using hv
  use (χ₀.comp π₁) + c • (e.comp π₂)
  refine nontrivial_of_ne ⟨v, ?_⟩ 0 ?_
  · rw [mem_weightSpace]
    intro x
    have hπ : (π₁ x : L) + π₂ x = x := hA.projection_add_projection_eq_self x
    suffices ⁅hA.symm.projection x, v⁆ = (c • e (π₂ x)) • v by
      calc ⁅x, v⁆
          = ⁅π₁ x, v⁆       + ⁅hA.symm.projection x, v⁆ := congr(⁅$hπ.symm, v⁆) ▸ add_lie _ _ _
        _ =  χ₀ (π₁ x) • v  + (c • e (π₂ x)) • v        := by rw [hv' (π₁ x), this]
        _ = _ := by simp [add_smul]
    calc ⁅hA.symm.projection x, v⁆
        = e (π₂ x) • ↑(c • ⟨v, hv⟩ : W)   := by
          rw [IsCompl.projection_apply, ← he, smul_lie, ← hvc.apply_eq_smul]; rfl
      _ = (c • e (π₂ x)) • v              := by rw [smul_assoc, smul_comm]; rfl
  · simpa [ne_eq, LieSubmodule.mk_eq_zero] using hvc.right

variable (k L V)
variable [Nontrivial V]

open LieAlgebra

-- This lemma is the central inductive argument in the proof of Lie's theorem below.
-- The statement is identical to `LieModule.exists_forall_lie_eq_smul_of_isSolvable`
-- except that it additionally assumes a finiteness hypothesis.
private lemma exists_forall_lie_eq_smul_of_isSolvable_of_finite
    (L : Type*) [LieRing L] [LieAlgebra k L] [LieRingModule L V] [LieModule k L V]
    [IsSolvable L] [LieModule.IsTriangularizable k L V] [Module.Finite k L] :
    ∃ χ : Module.Dual k L, Nontrivial (weightSpace V χ) := by
  obtain H|⟨A, hA, hAL⟩ := eq_top_or_exists_le_coatom (derivedSeries k L 1).toSubmodule
  · obtain _ | _ := subsingleton_or_nontrivial L
    · use 0
      simpa [mem_weightSpace, nontrivial_iff] using exists_pair_ne V
    · rw [LieSubmodule.toSubmodule_eq_top] at H
      exact ((derivedSeries_lt_top_of_solvable k L).ne H).elim
  lift A to LieIdeal k L
  · intros
    exact hAL <| LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)
  obtain ⟨χ', _⟩ := exists_forall_lie_eq_smul_of_isSolvable_of_finite A
  exact exists_nontrivial_weightSpace_of_lieIdeal A hA χ'
termination_by Module.finrank k L
decreasing_by
  simp_wf
  rw [← finrank_top k L]
  apply Submodule.finrank_lt_finrank_of_lt
  exact hA.lt_top

/-- **Lie's theorem**: Lie modules of solvable Lie algebras over fields of characteristic 0
have a common eigenvector for the action of all elements of the Lie algebra.

See `LieModule.exists_nontrivial_weightSpace_of_isNilpotent` for the variant that
assumes that `L` is nilpotent and drops the condition that `k` is of characteristic zero. -/
theorem exists_nontrivial_weightSpace_of_isSolvable
    [IsSolvable L] [LieModule.IsTriangularizable k L V] :
    ∃ χ : Module.Dual k L, Nontrivial (weightSpace V χ) := by
  let imL := (toEnd k L V).range
  let toEndo : L →ₗ[k] imL := LinearMap.codRestrict imL.toSubmodule (toEnd k L V)
      (fun x ↦ LinearMap.mem_range.mpr ⟨x, rfl⟩ : ∀ x : L, (toEnd k L V) x ∈ imL)
  have ⟨χ, h⟩ := exists_forall_lie_eq_smul_of_isSolvable_of_finite k V imL
  use χ.comp toEndo
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : weightSpace V χ)
  refine nontrivial_of_ne ⟨v, ?_⟩ 0 ?_
  · rw [mem_weightSpace] at hv ⊢
    intro x
    apply hv (toEndo x)
  · simpa using hv0

end

end LieModule
