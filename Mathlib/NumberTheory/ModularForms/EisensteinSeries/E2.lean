import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.UniformConvergence



open ModularForm EisensteinSeries UpperHalfPlane TopologicalSpace  intervalIntegral
  Metric Filter Function Complex MatrixGroups Finset

open scoped Interval Real Topology BigOperators Nat

noncomputable section


/-- This is an auxilary summand used to define the Eisenstein serires `G2`. -/
def e2Summand (m : ℤ) (z : ℍ) : ℂ := ∑' (n : ℤ), eisSummand 2 ![m, n] z

/-- The Eisenstein series of weight `2` and level `1` defined as the limit as `N` tends to
infinity of the partial sum of `m` in `[N,N)` of `e2Summand m`. This sum over non-symmetric
intervals is handy in proofs of its transformation property. -/
def G2 : ℍ → ℂ := fun z => limUnder (atTop) (fun N : ℕ => ∑ m ∈ Ico (-N : ℤ) N, e2Summand m z)

def E2 : ℍ → ℂ := (1 / (2 * riemannZeta 2)) •  G2

def D2 (γ : SL(2, ℤ)) : ℍ → ℂ := fun z => (2 * π * Complex.I * γ 1 0) / (denom γ z)

lemma Eis_isBigO (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    (fun n => ((r z * ‖![n, m]‖))⁻¹) := by
    rw [Asymptotics.isBigO_iff']
    refine ⟨1, Real.zero_lt_one, ?_⟩
    filter_upwards with n
    have := EisensteinSeries.summand_bound z (k := 1) (by norm_num) ![m, n]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Real.rpow_neg_one, norm_inv, Nat.succ_eq_add_one, Nat.reduceAdd, mul_inv_rev, norm_mul,
      norm_norm, Real.norm_eq_abs, one_mul, ge_iff_le] at *
    apply le_trans this
    rw [abs_norm, mul_comm, show |r z| = r z by rw [abs_eq_self];  exact (r_pos z).le, norm_symm]

lemma linear_bigO2 (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n => ((n : ℝ)⁻¹)  := by
  have h1 := Eis_isBigO m z
  apply  Asymptotics.IsBigO.trans h1
  rw [@Asymptotics.isBigO_iff']
  refine ⟨|(r z)|⁻¹, by simp [ne_of_gt (r_pos z)], ?_⟩
  rw [eventually_iff_exists_mem]
  refine ⟨{0}ᶜ, Set.Finite.compl_mem_cofinite (Set.finite_singleton 0), ?_⟩
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Nat.succ_eq_add_one, Nat.reduceAdd,
    mul_inv_rev, norm_mul, norm_inv, norm_norm, Real.norm_eq_abs, abs_norm]
  intro n hn
  rw [mul_comm]
  gcongr
  simpa using abs_le_left_of_norm m n

lemma linear_bigO (m : ℤ) (z : ℍ) : (fun (n : ℤ) => ((m : ℂ) * z + n)⁻¹) =O[cofinite]
    fun n => (|(n : ℝ)|⁻¹)  := by
  have := Asymptotics.IsBigO.abs_right (linear_bigO2 m z)
  simp_rw [abs_inv] at this
  exact this

lemma linear_bigO_pow (m : ℤ) (z : ℍ) (k : ℕ) :
    (fun (n : ℤ) => ((((m : ℂ) * z + n)) ^ k )⁻¹) =O[cofinite] fun n => ((|(n : ℝ)| ^ k)⁻¹)  := by
  simp_rw [← inv_pow]
  apply Asymptotics.IsBigO.pow
  apply linear_bigO m z


lemma summable_hammerTime  {α : Type} [NormedField α] [CompleteSpace α] (f  : ℤ → α) (a : ℝ)
    (hab : 1 < a) (hf : (fun n => (f n)⁻¹) =O[cofinite] fun n => (|(n : ℝ)| ^ (a : ℝ))⁻¹) :
    Summable fun n => (f n)⁻¹ := by
  apply summable_of_isBigO _ hf
  have := Real.summable_abs_int_rpow hab
  apply this.congr
  intro b
  refine Real.rpow_neg ?_ a
  exact abs_nonneg (b : ℝ)

lemma G2_summable_aux (n : ℤ) (z : ℍ) (k : ℤ) (hk : 2 ≤ k) :
    Summable fun d : ℤ => ((((n : ℂ) * z) + d) ^ k)⁻¹ := by
  apply summable_hammerTime _ k
  · norm_cast
  · lift k to ℕ using (by linarith)
    have := linear_bigO_pow n z k
    norm_cast at *

lemma pnat_div_upper (n : ℕ+) (z : ℍ) : 0 < (-(n : ℂ) / z).im := by
  norm_cast
  rw [div_im]
  simp only [Int.cast_neg, Int.cast_natCast, neg_im, natCast_im, neg_zero, coe_re, zero_mul,
    zero_div, neg_re, natCast_re, coe_im, neg_mul, zero_sub, Left.neg_pos_iff, gt_iff_lt]
  rw [@div_neg_iff]
  right
  simp only [Left.neg_neg_iff, Nat.cast_pos, PNat.pos, mul_pos_iff_of_pos_left, Complex.normSq_pos,
    ne_eq]
  refine ⟨z.2, ne_zero z⟩

lemma e2Summand_summable (z : ℍ) (n : ℤ) : Summable fun b : ℤ ↦ 1 / (((b : ℂ) * ↑z + ↑n) ^ 2) := by
  have := (G2_summable_aux (-n) ⟨-1 /z, by simpa using pnat_div_upper 1 z⟩  2
      (by norm_num)).mul_left ((z : ℂ)^2)⁻¹
  apply this.congr
  intro b
  simp only [UpperHalfPlane.coe, Int.cast_neg, neg_mul]
  field_simp
  norm_cast
  congr 1
  rw [← mul_pow]
  congr
  have hz := ne_zero z --this come our with a coe that should be fixed
  simp only [UpperHalfPlane.coe, ne_eq] at hz
  field_simp
  ring

lemma Asymptotics.IsBigO.map {α β ι γ : Type*} [Norm α] [Norm β] {f : ι → α} {g : ι → β}
  {p : Filter ι} (hf : f =O[p] g) (c : γ → ι)  :
    (fun (n : γ) => f (c n)) =O[p.comap c] fun n => g (c n) := by
  rw [isBigO_iff] at *
  obtain ⟨C, hC⟩ := hf
  refine ⟨C, ?_⟩
  simp only [eventually_comap] at *
  filter_upwards [hC] with n hn
  exact fun a ha ↦ Eq.mpr (id (congrArg (fun _a ↦ ‖f _a‖ ≤ C * ‖g _a‖) ha)) hn

lemma Asymptotics.IsBigO.nat_of_int {α β: Type*} [Norm α] [SeminormedAddCommGroup β] {f : ℤ → α}
    {g : ℤ → β}  (hf : f =O[cofinite] g) :   (fun (n : ℕ) => f n) =O[cofinite] fun n => g n := by
  have := Asymptotics.IsBigO.map hf Nat.cast
  simp only [Int.cofinite_eq, isBigO_sup, comap_sup, Asymptotics.isBigO_sup] at *
  rw [Nat.cofinite_eq_atTop]
  simpa using this.2
