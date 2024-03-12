import Mathlib

open NumberField Units IsCyclotomicExtension.Rat InfinitePlace

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {3} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ ↑(3 : ℕ+)) (u : (𝓞 K)ˣ)

theorem unit_mem : ↑u ∈
    ({1, -1, hζ.toInteger, -hζ.toInteger, hζ.toInteger ^ 2, -hζ.toInteger ^ 2} : Set (𝓞 K)) := by
  have hrank : rank K = 0 := by
    dsimp [rank]
    rw [card_eq_NrRealPlaces_add_NrComplexPlaces, nrRealPlaces_eq_zero (n := 3) K (by decide),
      zero_add, nrComplexPlaces_eq_totient_div_two (n := 3)]
    rfl
  obtain ⟨x, ⟨_, hxu, -⟩, -⟩ := exist_unique_eq_mul_prod _ u
  replace hxu : u = x := by
    rw [← mul_one x.1]
    convert hxu
    convert Finset.prod_empty.symm
    rw [Finset.univ_eq_empty_iff, hrank]
    infer_instance
  obtain ⟨n, hnpos, hn⟩ := isOfFinOrder_iff_pow_eq_one.1 <| (CommGroup.mem_torsion _ _).1 x.2
  replace hn : (↑u : K) ^ ((⟨n, hnpos⟩ : ℕ+) : ℕ) = 1 := by
    norm_cast
    simp [hxu, hn]
  have hodd : Odd ((3 : ℕ+) : ℕ) := by decide
  obtain ⟨r, hr3, hru⟩ := hζ.exists_pow_or_neg_mul_pow_of_pow_eq_one hodd hn
  replace hr : r ∈ Finset.Ico 0 3 := Finset.mem_Ico.2 ⟨by simp, hr3⟩
  replace hru : ↑u = hζ.toInteger ^ r ∨ ↑u = -hζ.toInteger ^ r := by
    rcases hru with (h | h)
    · left; ext; exact h
    · right; ext; exact h
  fin_cases hr
  · rcases hru with (h | h) <;> simp [h]
  · rcases hru with (h | h) <;> simp [h]
  · rcases hru with (h | h)
    · apply Set.mem_insert_of_mem; apply Set.mem_insert_of_mem; simp [h]
    · apply Set.mem_insert_of_mem; apply Set.mem_insert_of_mem; simp [h]

theorem foo : ¬(∃ n : ℤ, (3 : 𝓞 K) ∣ (hζ.toInteger - n : 𝓞 K)) := by
  intro ⟨n, x, h⟩
  have h3pos : 0 < 3 := by decide
  have hp : Fact (Nat.Prime (⟨3, h3pos⟩ : ℕ+)) := ⟨by norm_num⟩
  let pB := hζ.integralPowerBasis'
  have hdim : pB.dim = 2 := by
    simp only [IsPrimitiveRoot.power_basis_int'_dim, PNat.val_ofNat, Nat.reduceSucc, pB]
    rfl
  replace hdim : 1 < pB.dim := by simp [hdim]
  rw [sub_eq_iff_eq_add] at h
  replace h := pB.basis.ext_elem_iff.1 h ⟨1, hdim⟩
  have := pB.basis_eq_pow ⟨1, hdim⟩
  rw [hζ.integralPowerBasis'_gen] at this
  simp only [PowerBasis.coe_basis, pow_one] at this
  rw [← this, show pB.gen = pB.gen ^ (⟨1, hdim⟩: Fin pB.dim).1 from by simp, ← pB.basis_eq_pow,
    pB.basis.repr_self_apply] at h
  simp only [↓reduceIte, map_add, Finsupp.coe_add, Pi.add_apply] at h
  rw [show (3 : 𝓞 K) * x = (3 : ℤ) • x from by simp, ← pB.basis.coord_apply,
    LinearMap.map_smul, ← zsmul_one, ← pB.basis.coord_apply, LinearMap.map_smul,
    show 1 = pB.gen ^ (⟨0, by linarith⟩: Fin pB.dim).1 from by simp, ← pB.basis_eq_pow,
    pB.basis.coord_apply, pB.basis.coord_apply, pB.basis.repr_self_apply] at h
  simp only [smul_eq_mul, Fin.mk.injEq, zero_ne_one, ↓reduceIte, mul_zero, add_zero] at h
  have hdvd : ¬ ((3 : ℤ) ∣ 1) := by norm_num
  apply hdvd
  exact ⟨_, h⟩

theorem eq_pow_prime_of_unit_of_congruent (hcong : ∃ n : ℤ, (3 : 𝓞 K) ∣ (↑u - n : 𝓞 K)) :
    ∃ v, u = v ^ (3 : ℕ) := by
  have h3 : Odd 3 := by decide
  have h3pos : 0 < 3 := by decide
  have hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have hu : IsUnit hζ.toInteger :=
    IsPrimitiveRoot.isUnit (IsPrimitiveRoot.coe_submonoidClass_iff.1 hζ) h3pos
  have := unit_mem hζ u
  have h2 : (hζ.pow_of_coprime 2 (by decide)).toInteger = hζ.toInteger ^ 2 := by ext; simp
  simp only [Set.mem_insert_iff, val_eq_one, Set.mem_singleton_iff] at this
  rcases this with (rfl | h | h | h | h | h)
  · exact ⟨1, by simp⟩
  · exact ⟨-1, by simp [← Units.eq_iff, h, h3]⟩
  · exfalso
    apply foo hζ
    rw [← h]
    exact hcong
  · exfalso
    apply foo hζ
    obtain ⟨n, x, hx⟩ := hcong
    rw [sub_eq_iff_eq_add] at hx
    refine ⟨-n, -x, ?_⟩
    rw [← neg_eq_iff_eq_neg.2 h, hx]
    simp
  · exfalso
    apply foo <| hζ.pow_of_coprime 2 (by decide)
    rw [h2, ← h]
    exact hcong
  · exfalso
    apply foo <| hζ.pow_of_coprime 2 (by decide)
    obtain ⟨n, x, hx⟩ := hcong
    refine ⟨-n, -x, ?_⟩
    rw [h2, mul_neg, ← hx, ← neg_eq_iff_eq_neg.2 h]
    simp only [Int.cast_neg, sub_neg_eq_add, neg_sub]
    ring
