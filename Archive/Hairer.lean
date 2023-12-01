import Mathlib

noncomputable section

section missing_polynomial
open MvPolynomial Submodule

variable {R σ : Type*} [CommSemiring R] (n : ℕ)

lemma totalDegree_le_iff_mem_span {R σ : Type*} [CommSemiring R] {n : ℕ}
    {P : MvPolynomial σ R} : totalDegree P ≤ n ↔
    P ∈ span R ((fun c : σ →₀ ℕ ↦ monomial c (1 : R)) '' {s : σ →₀ ℕ | s.sum (fun _ e ↦ e) ≤ n}) := by
  sorry

/- Is this really missing?? -/
def evalAtₗ {R σ : Type*} [CommSemiring R] (x : σ → R) : MvPolynomial σ R →ₗ[R] R where
  toFun P := eval x P
  map_add' := by simp
  map_smul' := by simp

lemma finite_stuff' [Finite σ] (N : ℕ) : {s : Multiset σ | Multiset.card s ≤ N}.Finite := by
  classical
  have := Fintype.ofFinite σ
  let S := N • (Finset.univ.val : Multiset σ)
  apply Finset.finite_toSet (Multiset.toFinset (Multiset.powerset S)) |>.subset
  intro s hs
  rw [Set.mem_setOf] at hs
  rw [Finset.mem_coe, Multiset.mem_toFinset, Multiset.mem_powerset, Multiset.le_iff_count]
  intro x
  simp only [S, Multiset.count_nsmul, Multiset.count_univ, mul_one]
  exact le_trans (s.count_le_card x) hs

lemma finite_stuff [Finite σ] (N : ℕ) : {s : σ →₀ ℕ | s.sum (fun _ e ↦ e) ≤ N}.Finite := by
  classical
  change {s : σ →₀ ℕ | s.sum (fun _ => id) ≤ N}.Finite
  simp only [← Finsupp.card_toMultiset]
  refine Set.Finite.of_finite_image ?_ (Multiset.toFinsupp.symm.injective.injOn _)
  convert finite_stuff' N
  swap; assumption
  ext x
  rw [← AddEquiv.coe_toEquiv]
  simp
  sorry

end missing_polynomial

section missing_linear_algebra

open Module Submodule BigOperators

variable {K V V' ι : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommMonoid V'] [Module K V']
   {B : V' →ₗ[K] Dual K V} {m : ι → V'}

lemma exists_predual_of_finite {μ : ι → Dual K V} [FiniteDimensional K V]
    (hμ : LinearIndependent K μ) {s : Set ι} (i : ι) :
    ∃ v : V, μ i v = 1 ∧ ∀ j ∈ s, j ≠ i → μ j v = 0 := by
sorry

lemma exists_predual {μ : ι → Dual K V} (hμ : LinearIndependent K μ) {s : Set ι} (hs : s.Finite)
    (i : ι) : ∃ v : V, μ i v = 1 ∧ ∀ j ∈ s, j ≠ i → μ j v = 0 := by
  sorry

lemma exists_stuff (hm : LinearIndependent K (B ∘ m)) {s : Set ι} (hs : s.Finite) (i : ι) :
    ∃ v : V, B (m i) v = 1 ∧ ∀ j ∈ s , j ≠ i → B (m j) v = 0 :=
  exists_predual hm hs i

variable (hm : LinearIndependent K (B ∘ m)) {s : Set ι} (hs : s.Finite)

def stuff (i : ι) : V := (exists_stuff hm hs i).choose

lemma stuff_eval_self (i : ι) : B (m i) (stuff hm hs i) = 1 := (exists_stuff hm hs i).choose_spec.1

lemma stuff_eval_other {i j : ι} (hj : j ∈ s) (h : j ≠ i) : B (m j) (stuff hm hs i) = 0 :=
  (exists_stuff hm hs i).choose_spec.2 j hj h

lemma foo {s : Set ι} (hs : s.Finite) (μ : V' →ₗ[K] K) :
    ∃ φ : V, ∀ v' ∈ span K (m '' s), μ v' = B v' φ := by
  use ∑ i in hs.toFinset, (μ (m i)) • stuff hm hs i
  intro v' hv'
  apply span_induction hv' (p := fun v' ↦ μ v' = B v' (∑ i in hs.toFinset, (μ (m i)) • stuff hm hs i))
  all_goals clear v' hv'
  · rintro _ ⟨i, hi, rfl⟩
    have : ∀ j ∈ hs.toFinset, j ≠ i → B (m i) (μ (m j) • stuff hm hs j) = 0 := by
      intros j _ hij
      rw [map_smul, stuff_eval_other hm hs hi hij.symm, smul_zero]
    rw [map_sum, Finset.sum_eq_single_of_mem i (hs.mem_toFinset.mpr hi) this, map_smul,
        stuff_eval_self, smul_eq_mul, mul_one]
  · simp only [_root_.map_zero, map_sum, map_smul, LinearMap.zero_apply, smul_eq_mul, mul_zero,
    Finset.sum_const_zero]
  · intros x y hx hy
    simp [map_add, hx, hy, mul_add, ← Finset.sum_add_distrib]
  · intros a v' hv'
    simp only [map_smul, hv', map_sum, smul_eq_mul, Finset.mul_sum, LinearMap.smul_apply]

end missing_linear_algebra

open Metric Set MeasureTheory Module
open MvPolynomial hiding support
open Function hiding eval

section normed
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E E' F  : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

variable (𝕜 E F) in
def SmoothSupportedOn (n : ℕ∞) (s : Set E) : Submodule 𝕜 (E → F) where
  carrier := { f : E → F | tsupport f ⊆ s ∧ ContDiff 𝕜 n f }
  add_mem' hf hg := ⟨sorry, hf.2.add hg.2⟩
  zero_mem' :=
    ⟨(tsupport_eq_empty_iff.mpr rfl).subset.trans (empty_subset _), contDiff_const (c := 0)⟩
  smul_mem' r f hf :=
    ⟨(closure_mono <| support_smul_subset_right r f).trans hf.1, contDiff_const.smul hf.2⟩

variable {n : ℕ∞} {s : Set E}

instance : FunLike (SmoothSupportedOn 𝕜 E F n s) E (fun _ ↦ F) where
  coe := Subtype.val
  coe_injective' := Subtype.coe_injective
end normed

def L {ι : Type*} [Fintype ι] :
  MvPolynomial ι ℝ →ₗ[ℝ] Dual ℝ (SmoothSupportedOn ℝ (EuclideanSpace ℝ ι) ℝ ⊤ (closedBall 0 1)) where
    toFun p :=
      { toFun := fun f ↦ ∫ x : EuclideanSpace ℝ ι, eval x p • f x
        map_add' := sorry
        map_smul' := sorry }
    map_add' := sorry
    map_smul' := sorry

lemma indep (ι : Type*) [Fintype ι] : LinearIndependent ℝ (L ∘ fun c : ι →₀ ℕ ↦ monomial c 1) := by
  sorry

lemma hairer (N : ℕ) (ι : Type*) [Fintype ι] :
    ∃ (ρ : EuclideanSpace ℝ ι → ℝ), tsupport ρ ⊆ closedBall 0 1 ∧ ContDiff ℝ ⊤ ρ ∧
    ∀ (p : MvPolynomial ι ℝ), p.totalDegree ≤ N →
    ∫ x : EuclideanSpace ℝ ι, eval x p • ρ x = eval 0 p :=
  let ⟨⟨φ, supp_φ, diff_φ⟩, hφ⟩ :=  foo (indep ι) (finite_stuff _) (evalAtₗ 0)
  ⟨φ, supp_φ, diff_φ, fun P hP ↦ (hφ P (totalDegree_le_iff_mem_span.1 hP)).symm⟩
