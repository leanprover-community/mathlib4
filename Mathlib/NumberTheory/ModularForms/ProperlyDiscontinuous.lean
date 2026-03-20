import Mathlib.NumberTheory.Modular

open MatrixGroups UpperHalfPlane Complex Matrix SpecialLinearGroup

noncomputable section

lemma UpperHalfPlane.isCompact_im_pos_lower_bound {K : Set ℍ} (hK : IsCompact K) :
    ∃ δ > 0, ∀ z ∈ K, δ ≤ z.im := by
  by_cases hne : K.Nonempty
  · match hK.exists_isMinOn hne continuous_im.continuousOn with
    | ⟨x, hxK, hxmin⟩ => exact ⟨_, x.im_pos, hxmin⟩
  · exact ⟨1, by grind [Set.not_nonempty_iff_eq_empty]⟩

/-
PROBLEM
Helper: compact subsets of ℍ have bounded coordinates

PROVIDED SOLUTION
Since the coercion coe : ℍ → ℂ is continuous and K is compact, the image is compact in ℂ, hence
bounded. Use IsCompact.isBounded and Metric.isBounded_iff_nonneg or exists_norm_le.
-/
lemma UpperHalfPlane.isCompact_bounded {K : Set ℍ} (hK : IsCompact K) :
    ∃ M : ℝ, ∀ z ∈ K, ‖(z : ℂ)‖ ≤ M :=
  hK.exists_bound_of_continuousOn (by fun_prop)

lemma SL2Z_finite_of_bounded_entries (A B C D : ℝ) :
    {γ : SL(2, ℤ) | |↑(γ 0 0)| ≤ A ∧ |↑(γ 0 1)| ≤ B ∧ |↑(γ 1 0)| ≤ C ∧ |↑(γ 1 1)| ≤ D}.Finite := by
  -- The set of possible values for each entry of γ is finite.
  have h_finite_entries (r : ℝ) : Set.Finite {x : ℤ | abs (x : ℝ) ≤ r} :=
    Set.Finite.subset (Set.finite_Icc (-⌈r⌉₊ : ℤ) ⌈r⌉₊)
      fun x hx => ⟨neg_le_of_abs_le <| mod_cast hx.out.trans <| Nat.le_ceil _,
        le_of_abs_le <| mod_cast hx.out.trans <| Nat.le_ceil _⟩
  -- Therefore, the set of possible matrices γ is also finite.
  have h_finite_matrices : Set.Finite {γ : Matrix (Fin 2) (Fin 2) ℤ |
      (|γ 0 0| : ℝ) ≤ A ∧ (|γ 0 1| : ℝ) ≤ B ∧ (|γ 1 0| : ℝ) ≤ C ∧ (|γ 1 1| : ℝ) ≤ D} :=
    .subset (.pi fun i => .pi fun j => h_finite_entries <| !![A, B; C, D] i j)
      fun γ hγ => by simpa [and_assoc] using hγ
  exact h_finite_matrices.preimage Subtype.val_injective.injOn

/-
PROBLEM
Show that for compact K, L ⊆ ℍ and γ ∈ SL(2,ℤ), if there exists z ∈ K with γ • z ∈ L,
then the entries of γ are bounded. Combined with `SL2Z_finite_of_bounded_entries`,
this gives `ProperlyDiscontinuousSMul`.

PROVIDED SOLUTION
If K or L is empty, the set of relevant γ is empty hence finite.
Otherwise, by `isCompact_im_pos_lower_bound` and `isCompact_bounded`, we get:
- δ_K, δ_L > 0 with z.im ≥ δ_K for z ∈ K and w.im ≥ δ_L for w ∈ L
- M_K, M_L with ‖z‖ ≤ M_K for z ∈ K and ‖w‖ ≤ M_L for w ∈ L

For γ = [[a,b],[c,d]] and z ∈ K with w = γ•z ∈ L:
  w.im = z.im / |cz+d|², so |cz+d|² ≤ z.im/δ_L ≤ (M_K + 1)/δ_L =: C²
  Since |cz+d|² = (c·re(z)+d)² + (c·im(z))², we get:
  |c|·im(z) ≤ C, so |c| ≤ C/δ_K
  |c·re(z)+d| ≤ C, so |d| ≤ C + |c|·M_K

  Similarly |az+b|² = |w|²·|cz+d|² (from w = (az+b)/(cz+d)), so:
  |az+b|² ≤ M_L²·C² =: D²
  |a|·im(z) ≤ D, so |a| ≤ D/δ_K
  |a·re(z)+b| ≤ D, so |b| ≤ D + |a|·M_K

So all entries are bounded by some B depending on K, L. Apply `SL2Z_finite_of_bounded_entries`.

We need to show: for compact K, L ⊆ ℍ, {γ | (γ • · '' K) ∩ L ≠ ∅} is finite.

If K or L is empty, this set is empty hence finite. So assume both nonempty.

Use the three helper lemmas:
- `UpperHalfPlane.isCompact_im_pos_lower_bound` gives δ_K > 0, δ_L > 0 with z.im ≥ δ_K for z ∈ K
  and w.im ≥ δ_L for w ∈ L
- `UpperHalfPlane.isCompact_bounded` gives M_K, M_L bounding ‖(z : ℂ)‖ for z in K resp L

For γ = [[a,b],[c,d]] with γ•z ∈ L for some z ∈ K, the key relation is:
  (γ•z).im = z.im / |cz+d|² (from UpperHalfPlane.im_smul_eq_div_normSq, noting det = 1 for SL)

So |cz+d|² ≤ z.im/δ_L. Since ‖z‖ ≤ M_K, z.im ≤ M_K, so |cz+d|² ≤ M_K/δ_L.

Now |cz+d|² = (c·re(z)+d)² + c²·im(z)², so:
  c²·δ_K² ≤ c²·im(z)² ≤ M_K/δ_L, giving |c| ≤ √(M_K/δ_L)/δ_K
  |c·re(z)+d| ≤ √(M_K/δ_L), so |d| ≤ √(M_K/δ_L) + |c|·M_K

Similarly γ•z = (az+b)/(cz+d), so |az+b| = |γ•z|·|cz+d| ≤ M_L·√(M_K/δ_L).
Then |a|·δ_K ≤ |a|·im(z) ≤ |az+b| (from imaginary part) ≤ M_L·√(M_K/δ_L).
And |b| ≤ |az+b| + |a|·M_K.

So all entries bounded by some B. The set of such γ is a subset of the finite set from
`SL2Z_finite_of_bounded_entries B`. Use Set.Finite.subset to finish.
-/
instance : ProperlyDiscontinuousSMul SL(2, ℤ) ℍ := by
  -- Let's choose any two compact sets K and L in the upper half-plane.
  suffices h_compact : ∀ K L : Set ℍ, IsCompact K → IsCompact L →
      Set.Finite {a : SL(2, ℤ) | ∃ z ∈ K, a • z ∈ L} by
    constructor
    aesop
  intros K L hK hL
  obtain ⟨δ_K, hδKpos, hδK⟩ : ∃ δ_K > 0, ∀ {z}, z ∈ K → δ_K ≤ z.im :=
    UpperHalfPlane.isCompact_im_pos_lower_bound hK
  obtain ⟨δ_L, hδLpos, hδL⟩ : ∃ δ_L > 0, ∀ {z}, z ∈ L → δ_L ≤ z.im :=
    UpperHalfPlane.isCompact_im_pos_lower_bound hL
  -- Let M_K and M_L be bounds for the norms of elements in K and L, respectively.
  obtain ⟨M_K, hM_K⟩ : ∃ M_K, ∀ {z}, z ∈ K → ‖(z : ℂ)‖ ≤ M_K := isCompact_bounded hK
  obtain ⟨M_L, hM_L⟩ : ∃ M_L, ∀ {w}, w ∈ L → ‖(w : ℂ)‖ ≤ M_L := isCompact_bounded hL
  -- For any γ ∈ SL(2,ℤ) with γ • z ∈ L for some z ∈ K, we have |γ • z| ≤ M_L and |z| ≤ M_K.
  -- We will derive bounds for the entries of `γ` from this.
  suffices h_bound : ∀ γ : SL(2, ℤ), ∀ z ∈ K, γ • z ∈ L →
      (|γ 0 0| : ℝ) ≤ (M_L * √(M_K / δ_L)) / δ_K ∧
      (|γ 0 1| : ℝ) ≤ (M_L * √(M_K / δ_L)) + (M_L * √(M_K / δ_L)) / δ_K * M_K ∧
      (|γ 1 0| : ℝ) ≤ √(M_K / δ_L) / δ_K ∧
      (|γ 1 1| : ℝ) ≤ √(M_K / δ_L) + √(M_K / δ_L) / δ_K * M_K from
    (SL2Z_finite_of_bounded_entries ..).subset (fun γ ⟨z, hz, hγ⟩ ↦ h_bound γ z hz hγ)
  intros γ z hz hγz
  have h_im : (γ • z).im = z.im / ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ^ 2 := by
    convert UpperHalfPlane.im_smul_eq_div_normSq _ _ using 1
    simp [Complex.normSq, Complex.sq_norm, denom]
  -- First bound the size of `c * z + d`.
  have h_bound_czdsq : ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ^ 2 ≤ M_K / δ_L := by
    have := hδL hγz
    rw [h_im, le_div_iff₀ <| by positivity [denom_ne_zero γ z]] at this
    grw [le_div_iff₀' hδLpos, ← hM_K hz, this, ← coe_im, Complex.im_le_norm]
  have h_bound_czd : ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ≤ √(M_K / δ_L) :=
    Real.le_sqrt_of_sq_le h_bound_czdsq
  -- Use this to bound the size of `a * z + b`.
  have h_bound_azb : ‖(γ 0 0 : ℂ) * z + γ 0 1‖ ≤ M_L * √(M_K / δ_L) := by
    suffices ‖(γ 0 0 : ℂ) * z + γ 0 1‖ ^ 2 ≤ M_L ^ 2 * (M_K / δ_L) by
        rw [← Real.sqrt_sq (show 0 ≤ M_L from le_trans (norm_nonneg _) (hM_L hγz)),
          ← Real.sqrt_mul (sq_nonneg _)]
        exact Real.le_sqrt_of_sq_le this
    suffices ‖(γ 0 0 : ℂ) * z + γ 0 1‖ ≤ M_L * ‖(γ 1 0 : ℂ) * z + γ 1 1‖ from
      le_trans (pow_le_pow_left₀ (norm_nonneg _) this 2) (by nlinarith)
    suffices ‖(γ 0 0 : ℂ) * z + γ 0 1‖ / ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ≤ M_L by
      rwa [div_le_iff₀ (norm_pos_iff.mpr <|
        show (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0 from denom_ne_zero γ z)] at this
    simpa [UpperHalfPlane.specialLinearGroup_apply] using hM_L hγz
  -- Extract bounds on the individual entries from this.
  have h_bound_a : |(γ 0 0 : ℝ)| * δ_K ≤ M_L * √(M_K / δ_L) := by
    have h_bound_entries : |(γ 0 0 : ℝ)| * z.im ≤ ‖(γ 0 0 : ℂ) * z + γ 0 1‖ := by
      grw [← abs_im_le_norm]
      simp [abs_of_pos z.im_pos]
    grw [← h_bound_azb, ← h_bound_entries, hδK hz]
  have h_bound_b : |(γ 0 1 : ℝ)| ≤ M_L * √(M_K / δ_L) + |(γ 0 0 : ℝ)| * M_K := by
    refine le_trans ?_ (add_le_add h_bound_azb
      (mul_le_mul_of_nonneg_left (hM_K hz) (abs_nonneg _)))
    have := norm_add_le ((γ 0 0 : ℂ) * z + γ 0 1) (-(γ 0 0 : ℂ) * z)
    simp_all +decide [Complex.normSq, Complex.norm_def]
  have h_bound_c : |(γ 1 0 : ℝ)| * δ_K ≤ √(M_K / δ_L) := by
    suffices ‖(γ 1 0 : ℂ) * z + γ 1 1‖ ≥ |(γ 1 0 : ℝ)| * z.im by
      nlinarith [hδK hz, show (|↑ (γ 1 0)| : ℝ) ≥ 0 by positivity]
    norm_num [Complex.normSq, Complex.norm_def]
    apply Real.le_sqrt_of_sq_le
    norm_num [mul_pow]
    nlinarith only [sq_nonneg ((γ 1 0 : ℝ) * z.re + (γ 1 1 : ℝ))]
  have h_bound_d : |(γ 1 1 : ℝ)| ≤ √(M_K / δ_L) + |(γ 1 0 : ℝ)| * M_K := by
    have := norm_add_le ((γ 1 0 : ℂ) * z + γ 1 1) (- (γ 1 0 : ℂ) * z) ;
    simp_all +decide only [ModularGroup.sl_moeb, Fin.isValue, neg_mul, add_neg_cancel_comm,
      norm_intCast, norm_neg, Complex.norm_mul, ge_iff_le]
    exact le_trans this (add_le_add h_bound_czd
        (mul_le_mul_of_nonneg_left (hM_K hz) (abs_nonneg _)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [le_div_iff₀] <;> linarith
  · refine le_trans h_bound_b ?_
    gcongr
    · exact (norm_nonneg _).trans (hM_K hz)
    · rw [le_div_iff₀] <;> linarith
  · rw [le_div_iff₀] <;> linarith
  · apply le_trans h_bound_d
    gcongr
    · exact (norm_nonneg _).trans (hM_K hz)
    · rw [le_div_iff₀] <;> linarith

end
