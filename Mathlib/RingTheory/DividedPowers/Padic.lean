/-
Copyright (c) 2025 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/

import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.DividedPowers.RatAlgebra

/-! # Divided powers on ℤ_[p]

Given a divided power algebra `(B, J, δ)` and an injective ring morphism `f : A →+* B`, if `I` is
an `A`-ideal such that `I.map f = J` and such that for all `n : ℕ`, `x ∈ I`, the preimage of
`hJ.dpow n (f x)` under `f` belongs to `I`, we get an induced divided power structure on `I`.

We specialize this construction to the coercion map `ℤ_[p] →+* ℚ_[p]` to get a divided power
structure on the ideal `(p) ⊆ ℤ_[p]`. This divided power structure is given by the family of maps
`fun n x ↦ x^n / n!`.

TODO: If `K` is a `p`-adic local field with ring of integers `R` and uniformizer `π` such that
`p = u * π^e` for some unit `u`, then the ideal `(π) ⊆ R` has divided powers if and only if
`e ≤ p - 1`.

-/

namespace PadicInt

open DividedPowers DividedPowers.OfInvertibleFactorial Nat Ring

variable (p : ℕ) [hp : Fact p.Prime]

section Factorial

theorem sub_one_mul_padicValNat_factorial_lt_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    (p - 1) * padicValNat p n.factorial < n := by
  have hpn : ((p - 1 : ℕ) : ℝ) * (padicValNat p n ! : ℝ) = n - (p.digits n).sum := by
    rw [← cast_mul, sub_one_mul_padicValNat_factorial n, cast_sub (digit_sum_le p n)]
  rw [← Nat.cast_lt (α := ℝ), Nat.cast_mul, hpn]
  have hnil : p.digits n ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hn
  apply sub_lt_self _
  exact_mod_cast Nat.sum_pos_iff_exists_pos.mpr ⟨(p.digits n).getLast hnil,
    List.getLast_mem hnil, Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero p hn)⟩

theorem padicValNat_factorial_lt_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    padicValNat p n.factorial < n := by
  apply lt_of_le_of_lt _ (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn)
  conv_lhs => rw [← one_mul (padicValNat p n !)]
  gcongr
  exact le_sub_one_of_lt (Nat.Prime.one_lt hp.elim)

theorem padicValNat_factorial_le (n : ℕ) : padicValNat p n.factorial ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · exact le_of_lt (padicValNat_factorial_lt_of_ne_zero p hn)

end Factorial

section Injective

open Function

variable {A B : Type*} [CommSemiring A] [CommSemiring B] (I : Ideal A) (J : Ideal B)

/-- Given a divided power algebra `(B, J, δ)` and an injective ring morphism `f : A →+* B`, if `I`
is an `A`-ideal such that `I.map f = J` and such that for all `n : ℕ`, `x ∈ I`, the preimage of
`hJ.dpow n (f x)` under `f` belongs to `I`, this is the induced divided power structure on `I`. -/
noncomputable def dividedPowers_of_injective (f : A →+* B) (hf : Injective f)
    (hJ : DividedPowers J) (hIJ : I.map f = J)
    (hmem : ∀ (n : ℕ) {x : A} (_ : x ∈ I), ∃ (y : A) (_ : n ≠ 0 → y ∈ I), f y = hJ.dpow n (f x)) :
    DividedPowers I where
  dpow n x := open Classical in if hx : x ∈ I then f.toFun.invFun (hJ.dpow n (f x)) else 0
  dpow_null hx := by simp [dif_neg hx]
  dpow_zero {x} hx := by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, dif_pos hx]
    have h1 : f.toFun.invFun 1 = 1 := by
      simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
        MonoidHom.coe_coe, ← hf.eq_iff, map_one]
      rw [invFun_eq ⟨1, map_one f⟩]
    rw [← h1, hJ.dpow_zero (hIJ ▸ Ideal.mem_map_of_mem f hx)]
    rfl
  dpow_one hx := by
    simp only [dif_pos hx]
    obtain ⟨y, hy, h⟩ := hmem 1 hx
    rw [hJ.dpow_one (hIJ ▸ Ideal.mem_map_of_mem f hx)] at h ⊢
    simp [← h, Function.leftInverse_invFun hf y, hy, hf h]
  dpow_mem {n x} hn hx := by
    obtain ⟨y, hy, h⟩ := hmem n hx
    simp [dif_pos hx, ← h, Function.leftInverse_invFun hf y, hy hn]
  dpow_add {n x y} hx hy := by
    have hxy : x + y ∈ I := Ideal.add_mem _ hx hy
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, dif_pos hxy, dif_pos hx, dif_pos hy]
    rw [← hf.eq_iff, map_sum]
    obtain ⟨a, ha, h⟩ := hmem n hxy
    by_cases hn0 : n = 0
    · simp only [hn0, Finset.antidiagonal_zero, Prod.mk_zero_zero, map_mul, Prod.snd_zero,
        Finset.sum_singleton, Prod.fst_zero, hJ.dpow_zero (hIJ ▸ Ideal.mem_map_of_mem f hx),
        invFun_eq ⟨1, map_one f⟩,  hJ.dpow_zero (hIJ ▸ Ideal.mem_map_of_mem f hy),
        hJ.dpow_zero (hIJ ▸ Ideal.mem_map_of_mem f hxy), mul_one]
    · rw [invFun_eq ⟨a, h⟩, map_add,
        hJ.dpow_add (hIJ ▸ Ideal.mem_map_of_mem f hx) (hIJ ▸ Ideal.mem_map_of_mem f hy)]
      apply Finset.sum_congr rfl
      intros m hm
      rw [map_mul]
      congr
      · obtain ⟨ax, _, hax⟩ := hmem m.1 hx
        rw [invFun_eq ⟨ax, hax⟩]
      · obtain ⟨ay, _, hay⟩ := hmem m.2 hy
        rw [invFun_eq ⟨ay, hay⟩]
  dpow_mul {n a x} hx := by
    have hax : a * x ∈ I := Ideal.mul_mem_left _ _ hx
    obtain ⟨b, _, hb⟩ := hmem n hx
    obtain ⟨c, _, hc⟩ := hmem n hax
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, dif_pos hax, dif_pos hx]
    rw [← hf.eq_iff, map_mul f (a^n), invFun_eq ⟨b, hb⟩, invFun_eq ⟨c, hc⟩, map_mul,
      hJ.dpow_mul (hIJ ▸ Ideal.mem_map_of_mem f hx), map_pow]
  mul_dpow {m n x} hx := by
    obtain ⟨a, _, ha⟩ := hmem m hx
    obtain ⟨b, _, hb⟩ := hmem n hx
    obtain ⟨c, _, hc⟩ := hmem (m + n) hx
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe, dif_pos hx, ← hf.eq_iff, map_mul]
    rw [invFun_eq ⟨a, ha⟩, invFun_eq ⟨b, hb⟩,  invFun_eq ⟨c, hc⟩,
      hJ.mul_dpow (hIJ ▸ Ideal.mem_map_of_mem f hx), map_natCast]
  dpow_comp {n m x} hm hx := by
    classical
    obtain ⟨a, _, ha⟩ := hmem m hx
    obtain ⟨b, _, hb⟩ := hmem (n * m) hx
    have hc : f ((n.uniformBell m) * b) = (n.uniformBell m) * hJ.dpow (n * m) (f x) := by
      simp [hb]
    have hinv : invFun f.toFun (hJ.dpow m (f x)) ∈ I := by
      obtain ⟨y, hy, h⟩ := hmem m hx
      simp [← h, Function.leftInverse_invFun hf y, hy hm]
    simp only [dif_pos hx, dif_pos hinv]
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [← hf.eq_iff, invFun_eq ⟨a, ha⟩, map_mul, invFun_eq ⟨b, hb⟩,
      hJ.dpow_comp hm (hIJ ▸ Ideal.mem_map_of_mem f hx), map_natCast,
      invFun_eq ⟨(n.uniformBell m) * b, hc⟩]

end Injective

section Padic

/-- The family `ℕ → ℚ_[p] → ℚ_[p]` given by `dpow n x = x ^ n / n!`. -/
private noncomputable def dpow' : ℕ → ℚ_[p] → ℚ_[p] := fun m x => inverse (m ! : ℚ_[p]) * x ^ m

lemma dpow'_norm_le_of_ne_zero {n : ℕ} (hn : n ≠ 0) {x : ℤ_[p]}
    (hx : x ∈ Ideal.span {(p : ℤ_[p])}) : ‖dpow' p n x‖ ≤ (p : ℝ)⁻¹ := by
  unfold dpow'
  by_cases hx0 : x = 0
  · rw [hx0]
    simp [inverse_eq_inv', coe_zero, ne_eq, hn, not_false_eq_true, zero_pow, mul_zero,
      norm_zero, inv_nonneg, cast_nonneg]
  · have hlt : (padicValNat p n.factorial : ℤ) < n := by
      exact_mod_cast padicValNat_factorial_lt_of_ne_zero p hn
    have hnorm : 0 < ‖(n ! : ℚ_[p])‖ := by
      simp only [norm_pos_iff, ne_eq, cast_eq_zero]
      exact factorial_ne_zero n
    rw [← zpow_neg_one, ← Nat.cast_one (R := ℤ), Padic.norm_le_pow_iff_norm_lt_pow_add_one]
    simp only [inverse_eq_inv', padicNormE.mul, norm_inv, _root_.norm_pow, padic_norm_e_of_padicInt,
      cast_one, Int.reduceNeg, neg_add_cancel, zpow_zero]
    rw [norm_eq_zpow_neg_valuation hx0, inv_mul_lt_one₀ hnorm, Padic.norm_eq_zpow_neg_valuation
      (cast_ne_zero.mpr n.factorial_ne_zero), ← zpow_natCast, ← zpow_mul]
    gcongr
    · exact_mod_cast Nat.Prime.one_lt hp.elim
    · simp only [neg_mul, Padic.valuation_natCast, neg_lt_neg_iff]
      apply lt_of_lt_of_le hlt
      conv_lhs => rw [← one_mul (n : ℤ)]
      gcongr
      norm_cast
      rwa [← PadicInt.mem_span_pow_iff_le_valuation x hx0, pow_one]

lemma dpow'_int (n : ℕ) {x : ℤ_[p]} (hx : x ∈ Ideal.span {(p : ℤ_[p])}) : ‖dpow' p n x‖ ≤ 1 := by
  unfold dpow'
  by_cases hn : n = 0
  · simp [hn, factorial_zero, cast_one, inverse_one, pow_zero, mul_one, norm_one, le_refl]
  · apply le_trans (dpow'_norm_le_of_ne_zero p hn hx)
    rw [← zpow_neg_one, ← zpow_zero ↑p]
    gcongr
    · exact_mod_cast Nat.Prime.one_le hp.elim
    · norm_num

lemma Coe.ringHom_apply (x : ℤ_[p]) : Coe.ringHom x = (x : ℚ_[p]) := rfl

lemma coe_sum {α : Type*} (s : Finset α) (f : α → ℤ_[p]) :
    (((∑ z ∈ s, f z) : ℤ_[p]) : ℚ_[p]) = ∑ z ∈ s, (f z : ℚ_[p]) := by
  simp [← Coe.ringHom_apply, map_sum PadicInt.Coe.ringHom f s]

theorem dpow'_mem {n : ℕ} {x : ℤ_[p]} (hm : n ≠ 0) (hx : x ∈ Ideal.span {↑p}) :
    ⟨dpow' p n x, dpow'_int p n hx⟩ ∈ Ideal.span {(p : ℤ_[p])} := by
  have hiff := PadicInt.norm_le_pow_iff_mem_span_pow ⟨dpow' p n x, dpow'_int p n hx⟩ 1
  rw [pow_one] at hiff
  rw [← hiff]
  simp only [dif_pos hx, cast_one, zpow_neg_one]
  exact dpow'_norm_le_of_ne_zero p hm hx

/-- The family `ℕ → Ideal.span {(p : ℤ_[p])} → ℤ_[p]` given by `dpow n x = x ^ n / n!` is a
  divided power structure on the `ℤ_[p]`-ideal `(p)`. -/
noncomputable def dividedPowers : DividedPowers (Ideal.span {(p : ℤ_[p])}) := by
  classical
  refine dividedPowers_of_injective (Ideal.span {(p : ℤ_[p])}) (⊤)
    PadicInt.Coe.ringHom ((Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a)
    (RatAlgebra.dividedPowers (⊤ : Ideal ℚ_[p])) ?_ ?_
  · rw [Ideal.map_span, Set.image_singleton, map_natCast]
    simp only [Ideal.span_singleton_eq_top, isUnit_iff_ne_zero, ne_eq, cast_eq_zero]
    exact Nat.Prime.ne_zero hp.elim
  · intro n x hx
    have hx' : (x : ℚ_[p]) ∈ (⊤ : Ideal ℚ_[p]) := trivial
    exact ⟨⟨dpow' p n x, dpow'_int p n hx⟩, fun hn ↦ dpow'_mem p hn hx, by
      simp [dpow', inverse_eq_inv', Coe.ringHom_apply, RatAlgebra.dpow_apply,
        Submodule.mem_top, ↓reduceIte]⟩

open Function

lemma dividedPowers_eq (n : ℕ) (x : ℤ_[p]) :
    (dividedPowers p).dpow n x = open Classical in
      if hx : x ∈ Ideal.span {(p : ℤ_[p])} then ⟨dpow' p n x, dpow'_int p n hx⟩ else 0 := by
  simp only [dividedPowers, dividedPowers_of_injective]
  split_ifs with hx
  · have hinj : Injective (PadicInt.Coe.ringHom (p := p)) :=
      (Set.injective_codRestrict Subtype.property).mp fun ⦃a₁ a₂⦄ a ↦ a
    have heq : Coe.ringHom ⟨dpow' p n x, dpow'_int p n hx⟩ =
        inverse (n ! : ℚ_[p]) * Coe.ringHom x ^ n := by
      simp [dpow', inverse_eq_inv', Coe.ringHom_apply]
    rw [← hinj.eq_iff, RatAlgebra.dpow_apply, if_pos (by trivial), ← heq]
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [apply_invFun_apply (f := Coe.ringHom)]
  · rfl

end Padic

end PadicInt
