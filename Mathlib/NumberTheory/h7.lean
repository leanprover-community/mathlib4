/-
Copyright (c) 2024 Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michail Karatarakis
-/
import Mathlib.NumberTheory.NumberField.House
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.Order

set_option autoImplicit true
set_option linter.style.multiGoal false
set_option linter.style.cases false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars true
set_option linter.style.longFile 0

open BigOperators Module.Free Fintype NumberField Embeddings FiniteDimensional
  Matrix Set Polynomial Finset IntermediateField Complex

noncomputable section

lemma ExistsAlgInt {K : Type*} [Field K] [NumberField K] (α : K) :
  ∃ k : ℤ, k ≠ 0 ∧ IsIntegral ℤ (k • α) := by
  obtain ⟨y, hy, hf⟩ := exists_integral_multiples ℤ ℚ (L := K) {α}
  refine ⟨y, hy, hf α (mem_singleton_self _)⟩

def c'_both {K : Type*} [Field K] [NumberField K] (α : K) :
   {c : ℤ | c ≠ 0 ∧ IsIntegral ℤ (c • α)} :=
  ⟨(ExistsAlgInt α).choose, (ExistsAlgInt α).choose_spec⟩

lemma adjoin_le_adjoin_more (α β : ℂ) (_ : IsAlgebraic ℚ α) (_ : IsAlgebraic ℚ β) :
  (adjoin _ {α} ≤ adjoin ℚ {α, β}) ∧ (adjoin _ {β} ≤ adjoin ℚ {α, β}) :=
  ⟨by apply adjoin.mono; intros x hx; left; exact hx,
   by apply adjoin.mono; intros x hx; right; exact hx⟩

lemma isNumberField_adjoin_alg_numbers (α β γ : ℂ)
  (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β) (hγ : IsAlgebraic ℚ γ) :
    NumberField (adjoin ℚ {α, β, γ}) :=  {
  to_charZero := charZero_of_injective_algebraMap (algebraMap ℚ _).injective
  to_finiteDimensional := finiteDimensional_adjoin (fun x hx => by
    cases' hx with ha hb; · simp_rw [ha, isAlgebraic_iff_isIntegral.1 hα]
    cases' hb with hb hc; · simp_rw [hb, isAlgebraic_iff_isIntegral.1 hβ]
    simp_rw [mem_singleton_iff.1 hc, isAlgebraic_iff_isIntegral.1 hγ])}

--#check canonicalEmbedding

lemma getElemsInNF (α β γ : ℂ) (hα : IsAlgebraic ℚ α)
    (hβ : IsAlgebraic ℚ β) (hγ : IsAlgebraic ℚ γ) :
      ∃ (K : Type) (_ : Field K) (_ : NumberField K)
      (σ : K →+* ℂ) (_ : DecidableEq (K →+* ℂ)),
    ∃ (α' β' γ' : K), α = σ α' ∧ β = σ β' ∧ γ = σ γ' := by
  have  hab := adjoin.mono ℚ {α, β} {α, β, γ}
    fun x hxab => by cases' hxab with hxa hxb; left; exact hxa; right; left; exact hxb
  have hac := adjoin.mono ℚ {α, γ} {α, β, γ}
    fun x hx => by cases' hx with hsf hff; left; exact hsf; right; right; exact hff
  use adjoin ℚ {α, β, γ}
  constructor
  use isNumberField_adjoin_alg_numbers α β γ hα hβ hγ
  use { toFun := fun x => x.1, map_one' := rfl, map_mul' := fun x y => rfl
        map_zero' := rfl, map_add' := fun x y => rfl}
  use Classical.typeDecidableEq (↥ℚ⟮α, β, γ⟯ →+* ℂ)
  simp only [exists_and_left, exists_and_right, RingHom.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, Subtype.exists, exists_prop, exists_eq_right']
  exact ⟨adjoin_simple_le_iff.1 fun _ hx =>
     hab ((adjoin_le_adjoin_more α β hα hβ).1 hx),
    adjoin_simple_le_iff.1 fun _ hx =>  hab (by
    apply adjoin.mono; intros x hx;
    · right; exact hx;
    · exact hx),
    adjoin_simple_le_iff.1 fun _ hx =>
    hac ((adjoin_le_adjoin_more α γ hα hγ).2 hx)⟩

open Differentiable AnalyticAt

theorem zero_if_order_inf : ∀ (f : ℂ → ℂ) z (hf : ∀ z, AnalyticAt ℂ f z),
  (∀ z, f z = 0) → AnalyticAt.order (hf z) = ⊤ := by
  intros f z hf h0
  rw [AnalyticAt.order_eq_top_iff]
  refine (AnalyticAt.frequently_eq_iff_eventually_eq (hf z) ?_).mp ?_
  · exact analyticAt_const
  · refine Filter.Frequently.of_forall ?_
    · intros x
      exact h0 x

theorem order_inf_if_zero : ∀ (f : ℂ → ℂ) z (hf : ∀ z, AnalyticAt ℂ f z),
 AnalyticAt.order (hf z) = ⊤ → (∀ z, f z = 0) := by
  intros f z hf hr
  have := AnalyticAt.order_eq_top_iff (hf z)
  rw [this] at hr
  rw [← AnalyticAt.frequently_eq_iff_eventually_eq (hf z)] at hr
  have hfon : AnalyticOnNhd ℂ f univ := by {
    unfold AnalyticOnNhd
    intros x hx
    simp_all only}
  have :=  AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero (hfon) ?_ ?_ hr
  · exact fun z ↦ this trivial
  · exact isPreconnected_univ
  · exact trivial
  · exact analyticAt_const

lemma zero_iff_order_inf : ∀ (f : ℂ → ℂ) z (hf : ∀ z, AnalyticAt ℂ f z),
  (∀ z, f z = 0) ↔ AnalyticAt.order (hf z) = ⊤ := by
  intros f z hf
  constructor
  · exact zero_if_order_inf f z hf
  · exact order_inf_if_zero f z hf

lemma analytic_iter_deriv (k : ℕ) (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z) :
  ∀ z : ℂ, AnalyticAt ℂ (iteratedDeriv k f) z := by
  intro z
  rw [← Eq.symm iteratedDeriv_eq_iterate]
  exact AnalyticAt.iterated_deriv (hf z) k

lemma eq_order_sub_one (k : ℕ) (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z)
 (hfdev : ∀ z : ℂ, AnalyticAt ℂ (iteratedDeriv k f) z) :
  ∀ z : ℂ, AnalyticAt.order (hfdev z) = AnalyticAt.order (hf z) - 1 := by {
    intros z
    have := AnalyticAt.iterated_deriv (hf z) k
    by_contra H
    sorry
  }

-- lemma: if the order of f is n > 0, then the order of the *single* derivative of f is n - 1
lemma order_gt_zero_then_deriv_n_neg_1 (f : ℂ → ℂ) (hf : ∀ z, AnalyticAt ℂ f z)
   (hfdev : ∀ z : ℂ, AnalyticAt ℂ (iteratedDeriv k f) z)  :
 (∀ z : ℂ, 0 < AnalyticAt.order (hf z)) →
   ∀ z, AnalyticAt.order (hfdev z) = AnalyticAt.order (hf z) - 1 := by {
    intros H
    intros z
    sorry
   }

lemma order_geq_k_then_deriv_n_neg_1 (f : ℂ → ℂ) (z₀ : ℂ) (hf : ∀ z, AnalyticAt ℂ f z)
   (hfdev : ∀ z : ℂ, AnalyticAt ℂ (iteratedDeriv k f) z) :
   (∀ z : ℂ, k ≤ AnalyticAt.order (hf z)) → ∀ z, AnalyticAt.order (hfdev z) = n - k := by {
    intros hof z
    induction' k with k hk
    · simp only [iteratedDeriv_zero, CharP.cast_eq_zero, tsub_zero]
      have (z₀ : ℂ) :  (hf z).order = n.toNat ↔ ∃ g, AnalyticAt ℂ g z₀ ∧ g z₀ ≠ 0 ∧
         ∀ᶠ (z : ℂ ) in nhds z₀, f z = (z - z₀) ^ n.toNat • g z := by {
        rw [order_eq_nat_iff]
        sorry
      }
      sorry
    · sorry
   }

-- lemma: if the order of f is n > 0, then the order of the *single* derivative of f is n - 1
--   this follows from the definition (characterization?) of the order as being (z - z₀)^n*g(z)
-- lemma: by induction if the order ≥ k, then the order of the k-th derivative is n - k

-- have hfoo : ∀ (z : ℂ), AnalyticAt ℂ (iteratedDeriv k f) z :=
 -- by {exact fun z ↦ analytic_iter_deriv k f hf z}
-- have := order_inf_if_zero (iteratedDeriv k f) z hfoo

lemma iterated_deriv_eq_zero_iff_order_eq_n :
  ∀ n (f : ℂ → ℂ) z (hf : ∀ z, AnalyticAt ℂ f z) (ho : AnalyticAt.order (hf z) ≠ ⊤)
   (hfdev : ∀ z : ℂ, AnalyticAt ℂ (iteratedDeriv k f) z),
  (∀ k < n, AnalyticAt.order (hfdev z) = 0) ∧ (iteratedDeriv k f z ≠ 0)
    ↔ AnalyticAt.order (hf z) = n := by
  intros n f z hf hord hfdev
  constructor
  · intros H
    obtain ⟨H1, H2⟩ := H
    sorry
  · intros H
    constructor
    · intros k hk
      sorry
    · by_contra H
      sorry

lemma iterated_deriv_eq_zero_imp_n_leq_order : ∀ (f : ℂ → ℂ) z₀ (hf : ∀ z, AnalyticAt ℂ f z)
   (ho : ∀ z, AnalyticAt.order (hf z) ≠ ⊤),
 (∀ k < n, iteratedDeriv k f z₀ = 0) → n ≤ AnalyticAt.order (hf z₀) := by

intros f z hf ho hd
rw [le_iff_eq_or_lt]
left
apply Eq.symm
rw [← iterated_deriv_eq_zero_iff_order_eq_n]
constructor
· intros k hkn
  sorry
· sorry
· exact ho z
· sorry









lemma cexp_mul : deriv (fun x => cexp (c * x)) x = c * cexp (c * x) := by
  change deriv (fun x => exp ((fun x => c * x) x)) x = c * exp (c * x)
  rw [deriv_cexp]
  · rw [deriv_mul]
    · simp only [deriv_const', zero_mul, deriv_id'', mul_one, zero_add]
      exact CommMonoid.mul_comm (cexp (c * x)) c
    · exact differentiableAt_const c
    · exact differentiableAt_id'
  · apply mul <| differentiable_const _; exact differentiable_id'

lemma IsIntegral_assoc (K : Type) [Field K]
{x y : ℤ} (z : ℤ) (α : K) (ha : IsIntegral ℤ (z • α)) :
  IsIntegral ℤ ((x * y * z : ℤ) • α) := by
  have : ((x * y * z : ℤ) • α) = (x * y) • (z • α) := by
    simp only [Int.cast_mul, zsmul_eq_mul, mul_assoc (↑x * ↑y : K) z α]
  conv => enter [2]; rw [this]
  apply IsIntegral.smul _ ha

-- lemma IsIntegral_assoc' (K : Type) [Field K]
-- {x y : ℤ} (z : ℤ) (α : K) (ha : IsIntegral ℤ (z • α)) :
--   IsIntegral ℤ (abs (x * y * z : ℤ) • α) := by
--   have : ((x * y * z : ℤ) • α) = (x * y) • (z • α) := by
--     simp only [Int.cast_mul, zsmul_eq_mul, mul_assoc (↑x * ↑y : K) z α]
--   conv => enter [2]; rw [this]
--   apply IsIntegral.smul _ ha

lemma IsIntegral.Cast(K : Type) [Field K]  (a : ℤ) : IsIntegral ℤ (a : K) :=
  map_isIntegral_int (algebraMap ℤ K) (Algebra.IsIntegral.isIntegral _)

lemma IsIntegral.Nat (K : Type) [Field K] (a : ℕ) : IsIntegral ℤ (a : K) := by
  have : (a : K) = ((a : ℤ) : K) := by simp only [Int.cast_natCast]
  rw [this]; apply IsIntegral.Cast

lemma triple_comm (K : Type) [Field K]  (a b c : ℤ) (x y z : K) :
 ((a*b)*c) • ((x*y)*z) = a•x * b•y * c•z := by
  simp only [zsmul_eq_mul, Int.cast_mul]; ring

variable (α β : ℂ) (hirr : ∀ i j : ℤ, β ≠ i / j) (htriv : α ≠ 0 ∧ α ≠ 1)

open Complex

include htriv in
lemma γneq0 : α ^ β ≠ 0 := fun H => by
  simp_all only [cpow_eq_zero_iff, ne_eq,false_and]

include hirr in
lemma βneq0 : β ≠ 0 := fun H => by apply hirr 0 1; simpa [div_one];

variable (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
  (K : Type) [Field K]
  (σ : K →+* ℂ)
  (hd : DecidableEq (K →+* ℂ))
  (α' β' γ' : K) (habc : α = σ α' ∧ β = σ β' ∧ α ^ β = σ γ')

include habc htriv hirr in
lemma hneq0 : α' ≠ 0 ∧ β' ≠ 0 ∧ γ' ≠ 0 := by
  constructor
  · intros H; apply htriv.1; rwa [habc.1, _root_.map_eq_zero]
  · constructor
    · intros H; apply βneq0 β hirr ; rwa [habc.2.1, _root_.map_eq_zero]
    · intros H; apply γneq0 α β htriv (by rwa [habc.2.2, _root_.map_eq_zero])

include hirr htriv habc in
lemma β'ne_zero : β' ≠ 0 := by {
  intros H
  have := hneq0 α β hirr htriv K σ α' β' γ' habc
  apply this.2.1
  subst H
  simp_all only [map_zero, ne_eq, map_eq_zero,
    not_false_eq_true, true_and, not_true_eq_false, false_and, and_false]}

variable [NumberField K]

def c' (α : K) : ℤ := c'_both α

lemma c'_IsIntegral (α : K) : IsIntegral ℤ (c' K α • α) := (c'_both α).2.2

def c₁ := abs ((c' K α') * (c' K β') * (c' K γ'))

lemma c₁_α : IsIntegral ℤ (c₁ K α' β' γ' • α') := by
  have h := IsIntegral_assoc (x := c' K γ') (y := c' K β') K (c' K α') α' (c'_IsIntegral K α')
  rw [c₁]
  conv => enter [2]; rw [mul_comm, mul_comm (c' K α') (c' K β'), ← mul_assoc]
  cases' abs_choice (c' K γ' * c' K β' * c' K α') with H1 H2
  · rw [H1]; exact h
  · rw [H2]
    simp_all only [zsmul_eq_mul, Int.cast_mul, abs_eq_neg_self, neg_smul, IsIntegral.neg_iff]

lemma c₁_β : IsIntegral ℤ (c₁ K α' β' γ' • β') := by
  have h := IsIntegral_assoc (x := c' K γ') (y := c' K α') K (c' K β') β' (c'_IsIntegral K β')
  rw [c₁, mul_comm, ← mul_assoc]
  cases' abs_choice (c' K γ' * c' K α' * c' K β' ) with H1 H2
  · rw [H1]; exact h
  · rw [H2]
    simp_all only [zsmul_eq_mul, Int.cast_mul, abs_eq_neg_self, neg_smul, IsIntegral.neg_iff]

lemma c₁_γ : IsIntegral ℤ (c₁ K α' β' γ' • γ') := by
  have h := IsIntegral_assoc (x := c' K α') (y := c' K β') K (c' K γ') γ' (c'_IsIntegral K γ')
  rw [c₁]
  cases' abs_choice ((c' K α' * c' K β' * c' K γ')) with H1 H2
  · rw [H1]; exact h
  · rw [H2]
    simp_all only [zsmul_eq_mul, Int.cast_mul, abs_eq_neg_self, neg_smul, IsIntegral.neg_iff]

lemma c₁b  (n : ℕ) : 1 ≤ n → k ≤ n - 1 → 1 ≤ (a : ℕ) → 1 ≤ (b : ℕ) →
  IsIntegral ℤ ((c₁ K α' β' γ')^(n - 1) • (a + b • β') ^ k) := by  {
  intros hn hkn ha hb
  have : (c₁ K α' β' γ')^(n - 1) = (c₁ K α' β' γ')^(n - 1 - k) * (c₁ K α' β' γ')^k := by {
    simp_all only [← pow_add, Nat.sub_add_cancel]}
  rw [this]
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, nsmul_eq_mul, mul_assoc]
  apply IsIntegral.mul
  · apply IsIntegral.pow
    · apply IsIntegral.Cast
  rw [← mul_pow]
  apply IsIntegral.pow
  rw [mul_add]
  apply IsIntegral.add
  · apply IsIntegral.mul <| IsIntegral.Cast _ _
    · apply IsIntegral.Nat
  rw [mul_comm, mul_assoc]
  apply IsIntegral.mul <| IsIntegral.Nat _ _
  rw [mul_comm, ← zsmul_eq_mul]
  exact c₁_β K α' β' γ'}

lemma c₁ac (u : K) (n k a l : ℕ) (hnk : a*l ≤ n*k) (H : IsIntegral ℤ (↑(c₁ K α' β' γ') * u)) :
  IsIntegral ℤ ((c₁ K α' β' γ')^(n*k) • u ^ (a*l)) := by
  have : (c₁ K α' β' γ') ^ (n * k) = (c₁ K α' β' γ') ^ (n * k - a * l)*(c₁ K α' β' γ')^(a*l) := by
    rw [← pow_add]; simp_all only [Nat.sub_add_cancel]
  rw[this, zsmul_eq_mul]
  simp only [Int.cast_mul, Int.cast_pow, nsmul_eq_mul]; rw [mul_assoc]
  apply IsIntegral.mul; apply IsIntegral.pow; apply IsIntegral.Cast
  rw [← mul_pow]; exact IsIntegral.pow H _

variable (q : ℕ)

abbrev h := Module.finrank ℚ K

def m := 2 * h K + 2

def n := q^2 / (2 * m K)

variable (u : Fin (m K * n K q)) (t : Fin (q * q)) (hq0 : 0 < q)

open Nat in include hq0 in
lemma c1a :
  let a : ℕ := (finProdFinEquiv.symm.1 t).1 + 1
  let l : ℕ := (finProdFinEquiv.symm.1 u).1 + 1
 IsIntegral ℤ ((c₁ K α' β' γ')^(m K * q) • (α'^ (a * l : ℕ))) := by
  intros a l
  apply c₁ac K α' β' γ' α' (m K) q a l ?_ ?_
  · rw [mul_comm]
    exact Nat.mul_le_mul
      (add_le_of_le_sub (le_of_ble_eq_true rfl)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).1.isLt))
      (add_le_of_le_sub hq0 (le_sub_one_of_lt ((finProdFinEquiv.symm.1 t).1).isLt))
  · rw [← zsmul_eq_mul]; exact c₁_α K α' β' γ'

open Nat in include hq0 in
lemma c1c :
  let b : ℕ := (finProdFinEquiv.symm.1 t).2 + 1
  let l : ℕ := (finProdFinEquiv.symm.1 u).1 + 1
 IsIntegral ℤ ((c₁ K α' β' γ') ^ (m K * q) • (γ'^(b * l : ℕ))) := by
  intros b l
  apply c₁ac K α' β' γ' γ' (m K) q b l ?_ ?_
  · rw [mul_comm]
    exact Nat.mul_le_mul
      (add_le_of_le_sub (le_of_ble_eq_true rfl)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).1.isLt))
        (add_le_of_le_sub hq0 (le_sub_one_of_lt (finProdFinEquiv.symm.1 t).2.isLt))
  · rw [← zsmul_eq_mul]; exact c₁_γ K α' β' γ'

abbrev sys_coeffs :
 Fin (q *q) → (Fin (m K *n K q)) → K := fun i j => by
  let a : ℕ := (finProdFinEquiv.symm.1 i).1 + 1
  let b : ℕ := (finProdFinEquiv.symm.1 i).2 + 1
  let k : ℕ := (finProdFinEquiv.symm.1 j).2
  let l : ℕ := (finProdFinEquiv.symm.1 j).1 + 1
  exact (a + b • β')^k * α' ^(a * l) * γ' ^(b * l)

variable (h2mq : 2 * m K ∣ q ^ 2)

include hq0 h2mq in
lemma one_le_n : 1 ≤ n K q := by {
  simp only [n]
  rw [Nat.one_le_div_iff]
  · apply Nat.le_of_dvd (Nat.pow_pos hq0) h2mq
  · exact Nat.zero_lt_succ (Nat.mul 2 (2 * h K + 1) + 1)}

abbrev c_coeffs := (c₁ K α' β' γ')^(n K q - 1) *
  (c₁ K α' β' γ')^(m K * q) * ((c₁ K α' β' γ')^(m K * q))

open Nat in include hq0 h2mq in
lemma c₁IsInt :
  IsIntegral ℤ (((c_coeffs K α' β' γ' q)) • sys_coeffs K α' β' γ' q t u) := by
  let c₁ := (c₁ K α' β' γ')
  let a : ℕ := (finProdFinEquiv.symm.1 t).1 + 1
  let b : ℕ := (finProdFinEquiv.symm.1 t).2 + 1
  let k : ℕ := (finProdFinEquiv.symm.1 u).2
  let l : ℕ := (finProdFinEquiv.symm.1 u).1 + 1
  rw [triple_comm K
    (c₁^(n K q - 1) : ℤ)
    (c₁^(m K * q) : ℤ)
    (c₁^(m K * q) : ℤ)
    (((a : ℕ) + b • β')^(k : ℕ))
    (α' ^ (a * l))
    (γ' ^ (b * (l)))]
  rw [mul_assoc]
  apply IsIntegral.mul
  · exact c₁b K α' β' γ' (n K q) (one_le_n K q hq0 h2mq)
      (le_sub_one_of_lt (finProdFinEquiv.symm.1 u).2.isLt)
      (le_add_left 1 (finProdFinEquiv.symm.1 t).1)
      (le_add_left 1 (finProdFinEquiv.symm.1 t).2)
  · exact IsIntegral.mul (c1a K α' β' γ' q u t hq0) (c1c K α' β' γ' q u t hq0)

lemma c₁neq0 : c₁ K α' β' γ' ≠ 0 := by
  unfold c₁
  have hcα := (c'_both α').2.1
  have hcβ := (c'_both β').2.1
  have hcγ := (c'_both γ').2.1
  unfold c'
  simp_all only [ne_eq, mem_setOf_eq, mul_eq_zero, or_self, not_false_eq_true]
  simp_all only [abs_eq_zero, mul_eq_zero, or_self, not_false_eq_true]

lemma c_coeffs_neq_zero : c_coeffs K α' β' γ' q ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ (c₁neq0 K α' β' γ'))
    (pow_ne_zero _ (c₁neq0 K α' β' γ'))) (pow_ne_zero _ (c₁neq0 K α' β' γ'))

def A : Matrix (Fin (m K * n K q)) (Fin (q * q)) (𝓞 K) :=
  fun i j => RingOfIntegers.restrict _
   (fun _ => (c₁IsInt K α' β' γ' q i j hq0 h2mq)) ℤ

include hirr htriv habc in
lemma α'_neq_zero :
  let a : ℕ := (finProdFinEquiv.symm.1 t).1 + 1
  let l : ℕ := (finProdFinEquiv.symm.1 u).1 + 1
  α' ^ ((↑↑a) * (l)) ≠ 0 :=
    pow_ne_zero _ (hneq0 α β hirr htriv K σ α' β' γ' habc).1

include hirr htriv habc in
lemma γ'_neq_zero :
  let b : ℕ := (finProdFinEquiv.symm.1 t).2 + 1
  let l : ℕ := (finProdFinEquiv.symm.1 u).1 + 1

 γ' ^ ((↑↑b) * (↑↑l)) ≠ 0 :=
  pow_ne_zero _ (hneq0 α β hirr htriv K σ α' β' γ' habc).2.2

include hirr habc in
lemma β'_neq_zero (k : ℕ) :
  let a : ℕ := (finProdFinEquiv.symm.1 t).1 + 1
  let b : ℕ := (finProdFinEquiv.symm.1 t).2 + 1

 (↑↑a + (↑b) • β') ^ ↑↑k ≠ 0 := by

  intros a b
  apply pow_ne_zero
  intro h
  have h : β' = (↑↑a)/(-(↑b)) := by
    rw [eq_div_iff_mul_eq]
    rw [← eq_neg_iff_add_eq_zero] at h
    rw [mul_neg, mul_comm, h]
    have : (↑↑b) ≠ 0 := by
      simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero,
      one_ne_zero, and_false, not_false_eq_true]
      unfold b
      simp only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply, Fin.coe_modNat,
        AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
    unfold b
    simp only [Equiv.toFun_as_coe, Nat.cast_one, nsmul_eq_mul]
    have : (↑↑b) ≠ 0 := by
      simp only [ne_eq, AddLeftCancelMonoid.add_eq_zero,
      one_ne_zero, and_false, not_false_eq_true]
      unfold b
      simp only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply, Fin.coe_modNat,
        AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true]
    intros H
    apply this
    norm_cast at H
    exact H.1
  apply hirr (↑a) (-(↑b))
  rw [habc.2.1, h]
  simp only [neg_add_rev, map_div₀, map_add, map_natCast, map_one, map_neg, Int.cast_add,
    Int.cast_natCast, Int.cast_one, Int.reduceNeg, Int.cast_neg]

include hirr htriv habc in
lemma sys_coeffs_ne_zero : sys_coeffs K α' β' γ' q t u ≠ 0 := by
  unfold sys_coeffs
  simp only [mul_eq_zero, pow_eq_zero_iff', not_or, not_and, Decidable.not_not]
  rw [mul_assoc]
  apply mul_ne_zero
    (mod_cast β'_neq_zero α β hirr K σ α' β' γ' habc q t (finProdFinEquiv.symm.1 u).2)
  · exact mul_ne_zero (mod_cast α'_neq_zero α β hirr htriv K σ α' β' γ' habc q u t)
      (mod_cast γ'_neq_zero α β hirr htriv K σ α' β' γ' habc q u t)

include hirr htriv habc u t in
lemma hM_neq0 : A K α' β' γ' q hq0 h2mq ≠ 0 := by
  simp (config := { unfoldPartialApp := true }) only [A]
  rw [Ne, funext_iff]
  simp only [zpow_natCast, zsmul_eq_mul]
  simp only [RingOfIntegers.restrict,
    zpow_natCast, zsmul_eq_mul, RingOfIntegers.map_mk]
  intros H
  specialize H u
  rw [funext_iff] at H
  specialize H t
  simp only [Int.cast_mul, Int.cast_pow, Prod.mk.eta, zero_apply] at H
  injection H with H
  simp only [mul_eq_zero, pow_eq_zero_iff', Int.cast_eq_zero, ne_eq, not_or, or_self_right] at H
  cases' H with H1 H2
  · cases' H1 with H1 H11
    rcases H1 with ⟨H1, H11⟩
    · apply c₁neq0 K α' β' γ'
      assumption
    · apply c₁neq0 K α' β' γ'
      exact H11.1
  · unfold sys_coeffs at H2
    simp only [Nat.cast_add, Nat.cast_one, nsmul_eq_mul, mul_eq_zero, pow_eq_zero_iff', ne_eq,
      AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, or_self, not_false_eq_true,
      pow_eq_zero_iff] at H2
    cases' H2 with H2 H22
    · obtain ⟨H2, H22⟩ := H2
      apply β'_neq_zero α β hirr K σ α' β' γ' habc q t (finProdFinEquiv.symm.1 u).2
      simp_all only [ne_eq, map_eq_zero, nsmul_eq_mul, Nat.cast_add,
       Nat.cast_one, not_false_eq_true, zero_pow]
      simp_all only [ne_eq, map_zero, not_true_eq_false, zero_ne_one, not_false_eq_true, and_true]
    · exact (hneq0 α β hirr htriv K σ α' β' γ' habc).2.2 H22.1

lemma cardmn : Fintype.card (Fin (m K * n K q)) = m K * n K q := by
  simp only [card_prod, Fintype.card_fin]

lemma cardqq : card (Fin (q*q)) = q * q := by
  simp only [card_prod, Fintype.card_fin]

lemma hm : 0 < m K := Nat.zero_lt_succ (2 * h K + 1)

include hq0 h2mq in
lemma h0m : 0 < m K * n K q := mul_pos (hm K) (one_le_n K q hq0 h2mq)

include hq0 h2mq in
lemma hmn : m K * n K q < q*q := by
  rw [← Nat.mul_div_eq_iff_dvd] at h2mq
  rw [← pow_two q, ← mul_lt_mul_left (Nat.zero_lt_two)]
  rw [← mul_assoc, n, h2mq, lt_mul_iff_one_lt_left]
  · exact one_lt_two
  · exact Nat.pow_pos hq0

lemma housec1_gt_zero : 0 ≤ house.c₁ K := by {
  unfold house.c₁
  apply mul_nonneg
  rw [le_iff_eq_or_lt]
  right
  simp only [Nat.cast_pos]
  exact Module.finrank_pos
  unfold house.c₂
  apply mul_nonneg
  simp only [le_sup_iff, zero_le_one, true_or]
  exact house.supOfBasis_nonneg K}

def c₂ : ℝ := max 1 ((c₁ K α' β' γ') ^ (1 + 2*(m K) * Nat.sqrt (2*(m K))))

def house_pow_le (α : K) (i : ℕ) : house (α^i) ≤ house α ^ i := by {
  unfold house
  simp only [map_pow]
  apply norm_pow_le ((canonicalEmbedding K) α)}

abbrev c₃ : ℝ :=
  max 1 (|c₂ K α' β' γ'| * Nat.sqrt (2*m K)* (1 + house (β'))*
    (house (α') ^ (2*m K^2)) * house (γ') ^(2*m K^2))

include hq0 h2mq t u in
lemma hAkl : ∀ (k : Fin (m K * n K q)) (l : Fin (q * q)),
  house ((algebraMap (𝓞 K) K)
  (A K α' β' γ' q hq0 h2mq k l)) ≤
  (c₃ K α' β' γ') ^ (n K q : ℝ) * ↑(n K q : ℝ)^(((n K q - 1)/2) : ℝ) := by  {
    simp (config := { unfoldPartialApp := true }) only [A, sys_coeffs]
    simp only [RingOfIntegers.restrict, zsmul_eq_mul, RingOfIntegers.map_mk]
    intros u t
    let a : ℕ := (finProdFinEquiv.symm.1 t).1 + 1
    let b : ℕ := (finProdFinEquiv.symm.1 t).2 + 1
    let k : ℕ := (finProdFinEquiv.symm.1 u).2
    let l : ℕ := (finProdFinEquiv.symm.1 u).1 + 1
    have f : (-1 / 2 + ↑(n K q : ℝ) * (1 / 2)) = (((n K q : ℝ) - 1)/2) := by ring
    calc
         _ ≤ house (c_coeffs K α' β' γ' q : K) *
           house ((a + b • β')) ^ k *
           house (α') ^ (a * l) *
           house (γ') ^ (b * l) := ?_

        _ ≤ (c₃ K α' β' γ') := ?_

        _ ≤ (c₃ K α' β' γ')^(n K q : ℝ) := ?_

        _ ≤ (c₃ K α' β' γ')^(n K q : ℝ) * ↑(n K q : ℝ)^(((n K q - 1)/2) : ℝ) := ?_

    · trans
      apply house_mul_le
      trans
      apply mul_le_mul_of_nonneg_left
      · rw [mul_assoc]
      apply house_nonneg
      trans
      apply mul_le_mul_of_nonneg_left
      apply house_mul_le
      apply house_nonneg
      trans
      · apply mul_le_mul_of_nonneg_left
        · apply mul_le_mul_of_nonneg_left
          · apply house_mul_le
          apply house_nonneg
        · apply house_nonneg
      rw [← mul_assoc]
      rw [← mul_assoc]
      apply mul_le_mul
      apply mul_le_mul
      apply mul_le_mul
      · rfl
      · unfold a b k
        apply house_pow_le
      · apply house_nonneg
      · apply house_nonneg
      · apply house_pow_le
      · apply house_nonneg
      · rw [mul_nonneg_iff]
        left
        constructor
        · apply house_nonneg
        · apply pow_nonneg
          apply house_nonneg
      · apply house_pow_le
      · apply house_nonneg
      · rw [mul_nonneg_iff]
        left
        constructor
        · rw [mul_nonneg_iff]
          left
          constructor
          · apply house_nonneg
          · apply pow_nonneg
            apply house_nonneg
        · apply pow_nonneg
          apply house_nonneg
    · simp only [house_intCast, Int.cast_abs]
      unfold c₃
      simp only [Int.cast_mul, Int.cast_pow, nsmul_eq_mul]
      rw [← pow_add, ← pow_add]
      simp only [le_sup_iff]
      right
      apply mul_le_mul
      apply mul_le_mul
      rw [mul_assoc]
      apply mul_le_mul
      · simp only [abs_pow, abs_abs]
        unfold c₂
        rw [← abs_pow]
        apply abs_le_abs
        simp only [le_sup_iff]
        right
        refine Bound.pow_le_pow_right_of_le_one_or_one_le ?_
        left
        constructor
        · sorry
        · sorry
        · trans
          · have :  -(c₁ K α' β' γ' : ℝ) ^ (n K q - 1 + m K * q + m K * q) ≤ 0 := by {
            simp only [Left.neg_nonpos_iff]
            apply pow_nonneg
            simp only [Int.cast_nonneg]
            unfold c₁
            apply abs_nonneg
            }
            exact this
          · simp only [le_sup_iff, zero_le_one, true_or]
      · sorry
      · apply pow_nonneg
        apply house_nonneg
      · simp only [abs_nonneg]
      · have : (house α' ^ (a * l : ℝ) ≤ house α' ^ (2 * m K ^ 2 : ℝ))
          → (house α' ^ (a * l) ≤ house α' ^ (2 * m K ^ 2)) := by {
            intros H
            norm_cast at H
          }
        apply this
        sorry
        --apply Real.rpow_le_rpow_of_exponent_le

      · apply pow_nonneg
        apply house_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · simp only [abs_nonneg]
          · simp only [Nat.cast_nonneg]
        · trans
          · exact zero_le_one
          · simp only [le_add_iff_nonneg_right]
            apply house_nonneg
      · sorry
      · apply pow_nonneg
        apply house_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · apply mul_nonneg
            · simp only [abs_nonneg]
            · simp only [Nat.cast_nonneg]
          · trans
            · exact zero_le_one
            · simp only [le_add_iff_nonneg_right]
              apply house_nonneg
        · apply pow_nonneg
          apply house_nonneg
    · nth_rw 1 [← Real.rpow_one ((c₃ K α' β' γ'))]
      apply Real.rpow_le_rpow_of_exponent_le
      · apply le_max_left
      · simp only [Nat.one_le_cast]; exact one_le_n K q hq0 h2mq
    · nth_rw  1 [← mul_one (c₃ K α' β' γ' ^ (n K q : ℝ))]
      apply mul_le_mul_of_nonneg_left
      · apply Real.one_le_rpow
        · simp only [Nat.one_le_cast]; exact one_le_n K q hq0 h2mq
        · apply div_nonneg
          · simp only [sub_nonneg, Nat.one_le_cast]; exact one_le_n K q hq0 h2mq
          · exact zero_le_two
      · apply Real.rpow_nonneg
        · simp only [c₃, Nat.cast_add, Nat.cast_one, le_max_iff, zero_le_one, true_or]}

-- def c₄ : ℝ := ((c₂ K α' β' γ') * ((q : ℝ) + (q : ℝ) * house β')*
--     (house α')^(Nat.sqrt (2*m K))*(house γ')^(Nat.sqrt (2*m K)))
def applylemma82 := NumberField.house.exists_ne_zero_int_vec_house_le K
  (A K α' β' γ' q hq0 h2mq)
  (hM_neq0 α β hirr htriv K σ α' β' γ' habc q u t hq0 h2mq )
  (h0m K q hq0 h2mq)
  (hmn K q hq0 h2mq)
  (cardqq q)
  (hAkl K α' β' γ' q u t hq0 h2mq )
  (cardmn K q)

def η : Fin (q * q) → 𝓞 K :=
  (applylemma82 α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq).choose

abbrev c₄ := max 1 (house.c₁ K *
  ((house.c₁ K) * ↑(q * q : ℝ) *
  (c₃ K α' β' γ' ^ ↑(n K q : ℝ) * ↑(n K q : ℝ) ^ ((↑(n K q : ℝ) - 1) / 2))) ^
  (↑(m K * n K q : ℝ) / (↑(q * q : ℝ) - ↑(m K * n K q : ℝ))))

open NumberField.house in
include hq0 h2mq hd hirr htriv habc in
lemma fromlemma82_bound :
  house (algebraMap (𝓞 K) K (η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t))
    ≤ (c₄ K hd α' β' γ' q) ^
    (n K q : ℝ) * ((n K q)^((1/2)*((n K q)+1)) : ℝ) := by
  obtain ⟨η, ⟨htneq0, ⟨hMt0,hbound⟩⟩⟩ :=
  applylemma82 α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  calc _ ≤ (c₄ K hd α' β' γ' q) := by {
    simp only [Real.rpow_natCast, le_max_iff]
    right
    exact mod_cast
      ((applylemma82 α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq).choose_spec).2.2 t}
       _ ≤ (c₄ K hd α' β' γ' q)^(n K q : ℝ) := ?_
       _ ≤ (c₄ K hd α' β' γ' q)^(n K q : ℝ) *
            ((n K q)^((1/2)*((n K q) + 1)) : ℝ) := ?_
  · nth_rw  1 [← Real.rpow_one (c₄ K hd α' β' γ' q)]
    apply Real.rpow_le_rpow_of_exponent_le
    · apply le_max_left
    simp only [Nat.one_le_cast]
    exact one_le_n K q hq0 h2mq
  · nth_rw  1 [← mul_one (c₄ K hd α' β' γ' q ^ (n K q : ℝ))]
    apply mul_le_mul_of_nonneg_left
    · simp only [Nat.reduceDiv, zero_mul, pow_zero, le_refl]
    apply Real.rpow_nonneg
    unfold c₄
    simp only [Real.rpow_natCast, le_max_iff, zero_le_one, true_or]

open Complex

include htriv in
lemma log_zero_zero : log α ≠ 0 := by
  intro h
  have := congr_arg exp h
  rw [exp_log, exp_zero] at this
  apply htriv.2; exact this; exact htriv.1

lemma decompose_ij (i j : Fin (q * q)) : i = j ↔
  (finProdFinEquiv.symm.1 i).1 = (finProdFinEquiv.symm.1 j).1 ∧
    ((finProdFinEquiv.symm.1 i).2 : Fin q) = (finProdFinEquiv.symm.1 j).2 := by
  apply Iff.intro
  · intro H; rw [H]; constructor <;> rfl
  · intro H
    rcases H with ⟨H1, H2⟩
    have : finProdFinEquiv.symm.1 i = finProdFinEquiv.symm.1 j := by
      rw [← Prod.eta (finProdFinEquiv.symm.toFun i), H1]
      rw [← Prod.eta (finProdFinEquiv.symm.toFun j), H2]
    clear H1 H2
    have := congr_arg finProdFinEquiv.toFun this
    simp only [Equiv.toFun_as_coe, EmbeddingLike.apply_eq_iff_eq,
      Prod.mk.injEq] at this
    assumption

def ρ : Fin (q * q) → ℂ := fun i => by
  let a : ℕ := (finProdFinEquiv.symm.1 i).1 + 1
  let b : ℕ := (finProdFinEquiv.symm.1 i).2 + 1
  exact (a + (b • β)) * Complex.log α

include hirr htriv in
lemma hdistinct : ∀ (i j : Fin (q * q)), i ≠ j → ρ α β q i ≠ ρ α β q j := by
  intros i j hij
  rw [ne_eq, decompose_ij] at hij
  rw [not_and'] at hij
  unfold ρ
  simp only [not_or, ne_eq, mul_eq_mul_right_iff, not_or]
  constructor
  · by_cases Heq : (finProdFinEquiv.symm.1 i).2 = (finProdFinEquiv.symm.1 j).2
    · rw [Heq]
      have := hij Heq
      intro H
      apply this
      simp only [Equiv.toFun_as_coe, nsmul_eq_mul, add_left_inj, Nat.cast_inj] at H
      exact Fin.eq_of_val_eq H
    · let i2 : ℕ  := (finProdFinEquiv.symm.toFun i).2 + 1
      let j2 : ℕ := (finProdFinEquiv.symm.toFun j).2 + 1
      let i1 : ℕ  := (finProdFinEquiv.symm.toFun i).1 + 1
      let j1 : ℕ  := (finProdFinEquiv.symm.toFun j).1 + 1
      have hb := hirr (i1 - j1) (j2 - i2)
      rw [← ne_eq]
      change i1 + i2 • β ≠ j1 + j2 • β
      intros H
      apply hb
      have h1 : i1 + i2 • β = j1 + j2 • β  ↔
        (i1 + i2 • β) - (j1 + j2 • β) = 0 := by {
           exact Iff.symm sub_eq_zero
        }
      rw [h1] at H
      have h2 : ↑i1 + ↑i2 • β - (↑j1 + ↑j2 • β) = 0 ↔
         ↑i1 + i2 • β - ↑j1 - ↑j2 • β = 0 := by {
          simp_all only [ne_eq, Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
          Fin.coe_divNat, Nat.cast_add,
            Int.ofNat_ediv, Nat.cast_one, add_sub_add_right_eq_sub, Int.cast_sub,
            Fin.coe_modNat, Int.ofNat_emod,
            nsmul_eq_mul, iff_true, sub_self, add_sub_cancel_left, i1, j1, j2, i2]}
      rw [h2] at H
      have h3 : ↑i1 + i2 • β - ↑j1 - j2 • β = 0 ↔ ↑i1 - ↑j1 + ↑i2 • β - ↑j2 • β = 0 := by {
        ring_nf}
      rw [h3] at H
      have hij2 : i2 ≠ j2 := by {
        by_contra HC
        apply Heq
        refine Fin.eq_of_val_eq ?_
        unfold i2 j2 at HC
        simp only [add_left_inj, i2,
          j1, i1, j2] at HC
        exact HC}
      have h4 : ↑i1 - ↑j1 + ↑i2 • β - ↑j2 • β = 0 ↔
        ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • β = 0 := by {
        rw [sub_eq_add_neg]
        simp only [nsmul_eq_mul]
        rw [← neg_mul]
        rw [add_assoc]
        rw [← add_mul]
        simp only [smul_eq_mul]
        rw [← sub_eq_add_neg]}
      rw [h4] at H
      have h5 : ↑i1 - ↑j1 + (i2 - ↑j2 : ℂ) • β =0 ↔
       ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • β) := by {
        rw [add_eq_zero_iff_eq_neg]}
      rw [h5] at H
      have h6 : ↑i1 - ↑j1 = - ((i2 - ↑j2 : ℂ) • β) ↔ ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • β := by {
        refine Eq.congr_right ?_
        simp only [smul_eq_mul]
        rw [← neg_mul]
        simp only [neg_sub]}
      rw [h6] at H
      have h7 : ↑i1 - ↑j1 = (↑j2 - ↑i2 : ℂ) • β ↔ (↑i1 - ↑j1) /(↑j2 - ↑i2 : ℂ) =  β := by {
        simp only [smul_eq_mul]
        rw [div_eq_iff]
        rw [mul_comm]
        intros HC
        apply hij2
        rw [sub_eq_zero] at HC
        simp only [Nat.cast_inj] at HC
        exact HC.symm}
      rw [h7] at H
      rw [H.symm]
      simp only [Int.cast_sub, Int.cast_natCast, i2, j1, i1, j2]
  · exact log_zero_zero α htriv

def V := vandermonde (fun t => ρ α β q t)

include α β hirr htriv in
lemma vandermonde_det_ne_zero : det (V α β q) ≠ 0 := by
  unfold V
  by_contra H
  rw [Matrix.det_vandermonde_eq_zero_iff] at H
  rcases H with ⟨i, j, ⟨hij, hij'⟩⟩
  have := hdistinct α β hirr htriv q i j
  simp only [ne_eq, Prod.mk.injEq, not_and] at this
  apply this
  intros H'
  · apply hij' H'
  · exact hij

open Differentiable Complex

def R : Fin (q*q) → ℂ → ℂ := fun _ x =>
  ∑ t, σ ((η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq) t) * exp (ρ α β q t * x)

def iteratedDeriv_of_R (k : ℕ):
  iteratedDeriv k (fun x => (R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t) x) =
 fun x => ∑ t, (σ ((η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq) t)) *
    exp (ρ α β q t * x) * (ρ α β q t)^k := by
  induction' k with k hk
  · simp only [iteratedDeriv_zero, pow_zero, mul_one]; rfl
  · simp only [iteratedDeriv_succ]
    conv => enter [1]; rw [hk]
    ext x
    rw [deriv, fderiv_sum]
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply,
      fderiv_eq_smul_deriv, deriv_mul_const_field', differentiableAt_const,
      deriv_const_mul_field', smul_eq_mul, one_mul]
    rw [Finset.sum_congr rfl]
    intros t ht
    rw [mul_assoc, mul_assoc, mul_eq_mul_left_iff, map_eq_zero]; left
    rw [cexp_mul, mul_assoc, (pow_succ' (ρ α β q t) k)]
    · rw [mul_comm, mul_assoc, mul_eq_mul_left_iff,
         Eq.symm (pow_succ' (ρ α β q t) k)]; left; rfl
    · intros i hi
      apply mul ?_ (differentiable_const (ρ α β q i ^ k))
      · apply mul <| differentiable_const _
        apply Differentiable.cexp
        apply mul (differentiable_const _) (differentiable_id')

lemma iteratedDeriv_of_R_is_zero (k : ℕ)
(hR : (R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq  t) = 0) :
  iteratedDeriv k (fun x => R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t x) x = 0 := by {
rw [iteratedDeriv]
simp_all only
obtain ⟨left, right⟩ := htriv
obtain ⟨left_1, right_1⟩ := habc
obtain ⟨left_2, right_1⟩ := right_1
subst left_1 left_2
simp_all only [Pi.zero_apply, iteratedFDeriv_zero_fun, ContinuousMultilinearMap.zero_apply]}

include α β hirr htriv in
lemma vecMul_of_R_zero (k : ℕ)
  (hR : R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t = 0) :
  (V α β q).vecMul (fun t =>
  σ ((η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq) t)) = 0 := by
  unfold V
  rw [funext_iff]
  intros t
  simp only [Pi.zero_apply]
  have : iteratedDeriv k
    (fun x => R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t x) = 0 := by {
   rw [funext_iff]
   intros x
   simp only [Pi.zero_apply]
   apply iteratedDeriv_of_R_is_zero
   exact hR}
  rw [funext_iff] at this
  simp only [Pi.zero_apply] at this
  have deriv_eq : iteratedDeriv k
    (fun x => (R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq  t) x) =
   fun x => ∑ t, (σ ((η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq) t)) *
    exp (ρ α β q t * x) * (ρ α β q t)^k := by {
      exact iteratedDeriv_of_R α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq k}
  have deriv_eq_0 : iteratedDeriv k
    (fun x => (R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t) x) 0 = 0 := by {
      exact this 0}
  rw [← deriv_eq_0]
  rw [deriv_eq]
  simp only [mul_zero, exp_zero, mul_one]
  unfold vecMul
  unfold dotProduct
  unfold vandermonde
  simp only [of_apply]
  rw [Finset.sum_congr rfl]
  intros t ht
  simp only [mul_eq_mul_left_iff, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  left
  sorry

lemma η_eq_zero (k : ℕ)
   (hR : R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq  t = 0) :
    (fun t => σ (η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t)) = 0 := by
  apply eq_zero_of_vecMul_eq_zero
  · apply vandermonde_det_ne_zero α β hirr htriv q
  · rw [funext_iff]
    simp only [Pi.zero_apply]
    have := vecMul_of_R_zero α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq k hR
    rwa [funext_iff] at this

-- lemma det V ≠ 0
-- from det_vandermonde_eq_zero_iff
-- but need to navigate Fin q * Fin q

-- R is zero function → lemma V * ηvec = 0
-- by series expansion of R(x) and exponential and sums

-- ηvec = 0
-- linear algebra

include α β hirr htriv in
lemma ηvec_eq_zero
  (hVecMulEq0 : (V α β q).vecMul
   (fun t => σ ((η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq) t )) = 0) :
    (fun t => σ ((η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq) t )) = 0 := by {
  apply eq_zero_of_vecMul_eq_zero (vandermonde_det_ne_zero α β hirr htriv q) hVecMulEq0}

include α β hirr htriv K σ α' β' γ' habc q t hd h2mq u hq0 in
lemma hbound_sigma :
  (η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq) ≠ 0 := by
  intros H
  have := (applylemma82 α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq).choose_spec.1
  apply this
  unfold η at H
  simp only [ne_eq, finProdFinEquiv_symm_apply, Equiv.symm_apply_apply] at H
  simp only [ne_eq, Pi.zero_apply, map_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  simp only [Nat.cast_mul, Real.rpow_natCast, Prod.forall]
  simp_all only [Nat.cast_mul, Real.rpow_natCast, Prod.forall, ne_eq, not_true_eq_false]

include α β hirr htriv σ α' β' γ' habc q t in
lemma R_nonzero (k : ℕ) :
  R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t ≠ 0 := by
  by_contra H
  have HC := (ηvec_eq_zero α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq)
    (vecMul_of_R_zero α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq k H)
  simp only at HC
  apply hbound_sigma α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  rw [funext_iff] at HC
  simp only [Pi.zero_apply, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff] at HC
  unfold η at *
  ext t
  specialize HC t
  simp only [ne_eq, Pi.zero_apply, map_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  exact HC






--order (IsAnalyticRAtl α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq).choose
--variable (hdistinct : ∀ (i j : Fin (q * q)), i ≠ j → ρ α β q i ≠ ρ α β q j)

-- where l is the index over which you minimize
-- l0 is the index where the minimum is attained
variable  (hγ : γ = α ^ β)

include htriv habc in
lemma sys_coeffs_bar :
  let l : ℕ := (finProdFinEquiv.symm.1 u).1 + 1
  let k : ℕ := (finProdFinEquiv.symm.1 u).2
  Complex.exp (ρ α β q t * ↑l) * ρ α β q t ^ k *
  Complex.log α ^ (-↑k : ℤ) = σ (sys_coeffs K α' β' γ' q t u) := by {
    let a : ℕ := ↑(finProdFinEquiv.symm.toFun t).1 + 1;
    let b : ℕ := ↑(finProdFinEquiv.symm.toFun t).2 + 1;
    intros l k
    nth_rw 2 [ρ]
    rw [mul_pow]
    rw [mul_assoc]
    rw [mul_assoc]
    have  : (Complex.log α ^ k * Complex.log α ^ (-k : ℤ)) = 1 := by {
      simp only [zpow_neg, zpow_natCast]
      refine Complex.mul_inv_cancel ?_
      by_contra H
      apply log_zero_zero α htriv
      simp only [pow_eq_zero_iff', ne_eq] at H
      apply H.1
    }
    rw [this]
    rw [mul_one]
    unfold sys_coeffs
    rw [mul_comm]
    change _ = σ ((↑a + b • β') ^ k * (α' ^ (a * l)) * (γ' ^ (b * l)))
    rw [map_mul]
    rw [map_mul]
    nth_rw 1 [mul_assoc]
    have : σ ((↑a + b • β') ^ k) = (↑a + ↑b * β) ^ k := by {
      simp only [nsmul_eq_mul, map_pow, map_add, map_natCast, map_mul]
      simp_all only [k, a, b]
    }
    rw [this]
    rw [map_pow]
    rw [map_pow]
    have : ((↑(finProdFinEquiv.symm.toFun t).1 + 1 : ℕ) +
    ((finProdFinEquiv.symm.toFun t).2 + 1 : ℕ) • β) ^ k * cexp (ρ α β q t * ↑l) =
     (↑a + ↑b * β)^k * cexp (ρ α β q t * ↑l) := by {
      simp_all only [ne_eq, map_eq_zero, Equiv.toFun_as_coe,
      finProdFinEquiv_symm_apply, Fin.coe_modNat, Int.ofNat_emod,
        zpow_neg, Fin.coe_divNat, Nat.cast_add, Nat.cast_one,
        nsmul_eq_mul, map_pow, map_add, map_natCast, map_one,
        map_mul, k, b, a, l]
       }
    rw [this]
    simp only [mul_eq_mul_left_iff, pow_eq_zero_iff']
    left
    rw [ρ]
    have :  cexp ((↑(↑(finProdFinEquiv.symm.toFun t).1 + 1 : ℕ)
      + (↑(finProdFinEquiv.symm.toFun t).2 + 1 : ℕ ) • β) * Complex.log α * ↑l) =
        cexp ((↑a + ↑b • β) * Complex.log α * l) :=  by {
          simp_all only [ne_eq, map_eq_zero, Equiv.toFun_as_coe,
           finProdFinEquiv_symm_apply, Fin.coe_modNat,
            Int.ofNat_emod, zpow_neg, Fin.coe_divNat, Nat.cast_add, Nat.cast_one,
            nsmul_eq_mul, map_pow, map_add,
            map_natCast, map_one, map_mul, k, l, b, a]
        }
    rw [this]
    have : σ α' ^ (a * l) * σ γ' ^ (b * l) = α ^ (a * l) * (σ γ')^ (b * l) := by {
      rw [habc.1]}
    rw [this]
    have : σ γ' = α^β := by {
      rw [habc.2.2]}
    rw [this]
    have : Complex.exp (Complex.log α) = α := by {
      apply Complex.exp_log
      exact htriv.1}
    rw [← cpow_nat_mul]
    have : cexp ((↑a + b • β) * Complex.log α * ↑l) = α ^ (a * l) * α ^ (↑(b * l) * β) ↔
      cexp ((↑a + b • β) * Complex.log α * ↑l) = α ^ ((a * l) + (↑(b * l) * β)) := by {
        rw [cpow_add]
        simp only [nsmul_eq_mul, Nat.cast_mul]
        norm_cast
        exact htriv.1
      }
    rw [this]
    rw [cpow_def_of_ne_zero]
    have : Complex.log α * (↑a * ↑l + ↑(b * l) * β) = (↑a + b • β) * Complex.log α * ↑l := by {
      nth_rw 4 [mul_comm]
      have : ( ↑(l * b) * β) =
         ( ↑((b * β) * l)) := by {
          simp only [Nat.cast_mul]
          exact mul_rotate (↑l) (↑b) β
         }
      rw [this]
      have : (↑a * ↑l + ((b * β) * l)) = ((↑a  + (b * β)) * l) := by {
        exact Eq.symm (RightDistribClass.right_distrib (↑a) (↑b * β) ↑l)
      }
      rw [this, mul_comm, mul_assoc]
      nth_rw 3 [mul_comm]
      rw [← mul_assoc, nsmul_eq_mul]
    }
    rw [this]
    exact htriv.1}

lemma sys_coeffs_foo :
  let l : ℕ := (finProdFinEquiv.symm.1 u).1 + 1
  let k : ℕ := (finProdFinEquiv.symm.1 u).2
  (log α)^(-k : ℤ) *
  iteratedDeriv k (R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t) l =
   ∑ t, σ ↑(η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t)
     * σ (sys_coeffs K α' β' γ' q t u) := by {
  intros l k
  rw [iteratedDeriv_of_R, mul_sum, Finset.sum_congr rfl]
  intros t ht
  rw [mul_assoc, mul_comm, mul_assoc]
  simp only [mul_eq_mul_left_iff, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
  left
  exact sys_coeffs_bar α β htriv K σ α' β' γ' habc q u t}


include α β σ hq0 h2mq hd hirr htriv σ α' β' γ' habc h2mq  in
lemma iteratedDeriv_vanishes :
  let l : ℕ := (finProdFinEquiv.symm.1 u).1 + 1
  --let k : ℕ := (finProdFinEquiv.symm.1 u).2
  ∀ k, k < n K q →
  iteratedDeriv k (R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t) l = 0 := by
  intros l k hl
  rw [iteratedDeriv_of_R]
  simp only
  have : ( (log α)^(-k : ℤ)) * ∑ t, σ ↑(η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t)
     * cexp (ρ α β q t * ↑l) * ρ α β q t ^ k = ( (log α)^(-k : ℤ)) * 0 ↔
       ∑ t, σ ↑(η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t)
     * cexp (ρ α β q t * ↑l) * ρ α β q t ^ k = 0 := by {
      rw [mul_right_inj']
      simp only [zpow_neg, zpow_natCast, ne_eq, inv_eq_zero, pow_eq_zero_iff', not_and,
        Decidable.not_not]
      intro h
      by_contra H
      apply log_zero_zero α htriv
      exact h}
  rw [← this]
  rw [mul_sum]
  simp only [zpow_natCast, mul_zero]
  conv => enter [1,2]; ext x; rw [mul_assoc, mul_comm, mul_assoc];
  --conv => enter [1,2]; ext x; rw [sys_coeffs_bar α β htriv K σ α' β' γ' habc q u x];
    --rw [← map_mul]
  have hMt0 :=
    (applylemma82 α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq).choose_spec.2.1
  unfold A at hMt0
  --rw [Finset.sum_eq_zero]
  simp only [RingOfIntegers.restrict, zsmul_eq_mul, RingOfIntegers.map_mk] at hMt0
  unfold mulVec at hMt0
  unfold dotProduct at hMt0
  rw [funext_iff] at hMt0
  have hMt0 := hMt0 u
  simp only [nsmul_eq_mul, Pi.zero_apply] at hMt0
  have : ∑ x, σ (↑(η α β hirr htriv K σ hd α' β' γ' habc q u x hq0 h2mq x)
    * sys_coeffs K α' β' γ' q x u) = 0 ↔
    ↑(c_coeffs K α' β' γ' q) * ∑ x, σ (↑(η α β hirr htriv K σ hd α' β' γ' habc q u x hq0 h2mq x)
     * sys_coeffs K α' β' γ' q x u) = ↑(c_coeffs K α' β' γ' q) * 0 := by {
      rw [mul_right_inj']
      norm_cast
      exact c_coeffs_neq_zero K α' β' γ' q
     }
  --rw [this]
  --rw [mul_sum]
  have h0 : ∑ x, ⟨(c_coeffs K α' β' γ' q) * sys_coeffs K α' β' γ' q x u, (by {
    refine (mem_integralClosure_iff ℤ K).mpr ?_
    have := c₁IsInt K α' β' γ' q u x hq0 h2mq
    simp only [zsmul_eq_mul] at this
    exact this
  })⟩ *
    (((applylemma82 α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq).choose) x) = 0 ↔
    (algebraMap (𝓞 K) K) (∑ x, ⟨(c_coeffs K α' β' γ' q) * sys_coeffs K α' β' γ' q x u, (by {
    refine (mem_integralClosure_iff ℤ K).mpr ?_
    have := (c₁IsInt K α' β' γ' q u x hq0 h2mq)
    simp only [zsmul_eq_mul] at this
    exact this
  })⟩ *
    (((applylemma82 α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq).choose) x) ) = 0 := sorry

  --rw [h0] at hMt0
  have h1 : ∑ x, ⟨(c_coeffs K α' β' γ' q) * sys_coeffs K α' β' γ' q x u, (by {
    refine (mem_integralClosure_iff ℤ K).mpr ?_
    have := (c₁IsInt K α' β' γ' q u x hq0 h2mq)
    simp only [zsmul_eq_mul] at this
    exact this
  })⟩ *
    (((applylemma82 α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq).choose) x) =
    ∑ x, ↑(c_coeffs K α' β' γ' q) * sys_coeffs K α' β' γ' q x u
      * (((applylemma82 α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq).choose) x) := by {
    simp only [map_sum]
    rw [Finset.sum_congr rfl]
    intros x hx
    simp only [map_mul, RingOfIntegers.map_mk]
    }
  sorry
  --simp only [Nat.cast_mul, Nat.cast_pow, ne_eq, map_sum, map_mul, RingOfIntegers.map_mk] at h1
  --simp only [map_sum, map_mul, RingOfIntegers.map_mk] at hMt0
  --rw [h1] at hMt0



----------------------
  --rw [map_sum σ] at hMt0



  -- have h1 : ∑ x, ⟨↑(c_coeffs K α' β' γ' q) * sys_coeffs K α' β' γ' q x u, ⋯⟩ * ⋯.choose x = 0
  --   ↔  ∑ x, ↑(c_coeffs K α' β' γ' q) * sys_coeffs K α' β' γ' q x u *
  --(↑(η α β hirr htriv K σ hd α' β' γ' habc q u x hq0 h2mq x)) = 0 := sorry

  -- have h1 : ∑ x, (η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq x) *
  -- sys_coeffs K α' β' γ' q x u = 0 ↔
  --   ∑ x, ↑(c_coeffs K α' β' γ' q) * sys_coeffs K α' β' γ' q x u *
  --(↑(η α β hirr htriv K σ hd α' β' γ' habc q u x hq0 h2mq x)) = 0 := by {
  --   rw [mul_sum]
  --   rw [Finset.sum_congr rfl]}

  -- --intros x hx
----------------------------
  -- have h2 : (∑ x, ⟨↑(c_coeffs K α' β' γ' q) * sys_coeffs K α' β' γ' q x u, (by {
  --   refine (mem_integralClosure_iff ℤ K).mpr ?_
  --   have := (c₁IsInt K α' β' γ' q u x hq0 h2mq)
  --   simp only [nsmul_eq_mul] at this
  --   exact this
  -- })⟩ * η x  : 𝓞 K) = 0 ↔ ∑ x, ↑(c_coeffs K α' β' γ' q) *
  --sys_coeffs K α' β' γ' q x u * (η x : 𝓞 K) = 0 := by {
  --   rw [← h1]
  --   simp_all only [Equiv.toFun_as_coe, finProdFinEquiv_symm_apply, Fin.coe_divNat,
   --Fin.coe_modNat, Int.ofNat_emod,
  --     zpow_neg, Nat.cast_add, Nat.cast_one, mul_zero, mul_eq_zero, inv_eq_zero,
  --or_iff_right_iff_imp, ne_eq,
  --     nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow, Pi.zero_apply, Real.rpow_natCast,
  -- Finset.mem_univ, map_zero, l, k]}
  -- rw [h2] at hMt0
  -- have h3 : ∑ x, ↑(c_coeffs K α' β' γ' q) * sys_coeffs K α' β' γ' q x u * (η x : 𝓞 K) = 0 ↔
  --   ↑(c_coeffs K α' β' γ' q) *  ∑ x, sys_coeffs K α' β' γ' q x u * (η x : 𝓞 K) = 0 := by {
  --   rw [mul_sum]
  --   rw [Finset.sum_congr rfl]
  --   intros x hx
  --   exact mul_assoc (↑(c_coeffs K α' β' γ' q)) (sys_coeffs K α' β' γ' q x u) ↑(η x)}
  -- rw [h3] at hMt0
  -- simp only [mul_eq_zero, pow_eq_zero_iff', Nat.cast_eq_zero, ne_eq,
  --   not_or, or_self_right, l, k] at hMt0
  -- cases' hMt0 with hMt0 hMt0
  -- · cases' hMt0 with hx hy
  --   · rcases hx with ⟨hx, hxx⟩
  --     by_contra H1
  --     apply c₁neq0 K α' β' γ'
  --     exact hx
  --   · rcases hy with ⟨hx, hxx⟩
  --     by_contra H2
  --     apply c₁neq0 K α' β' γ'
  --     exact hx
  -- · have : ∑ x, sys_coeffs K α' β' γ' q x u * ↑(η x) = 0 ↔
  --    σ (∑ x, sys_coeffs K α' β' γ' q x u * ↑(η x)) = 0 := by {
  --     exact Iff.symm (map_eq_zero σ)
  --    }
  --   rw [this] at hMt0
  --   simp only [map_sum] at hMt0
  --   rw [← hMt0]
  --   rw [Finset.sum_congr rfl]
  --   intros x hx
  --   rw [mul_comm]
  --   simp only [map_mul, mul_eq_mul_left_iff, mul_eq_zero, pow_eq_zero_iff', ne_eq,
  --     AddLeftCancelMonoid.add_eq_zero, Nat.div_eq_zero_iff, one_ne_zero, and_false, or_self,
  --     not_false_eq_true, pow_eq_zero_iff, map_eq_zero, l, k]
  --   left
  --   rw [Finset.sum_congr]










  -- have : (∑ x, ⟨↑(c_coeffs K α' β' γ' q) * sys_coeffs K α' β' γ' q x u, (by {
  --   refine (mem_integralClosure_iff ℤ K).mpr ?_
  --   have := (c₁IsInt K α' β' γ' q u x hq0 h2mq)
  --   simp only [nsmul_eq_mul] at this
  --   exact this
  -- })⟩ * η x  : 𝓞 K) = ∑ x, ↑(c_coeffs K α' β' γ' q) *
    --sys_coeffs K α' β' γ' q x u * (η x : 𝓞 K) := by {
  --    simp only [map_sum]
  --    rw [Finset.sum_congr rfl]
  --    intros x hx
  --    simp only [map_mul, RingOfIntegers.map_mk]
  -- }
  -- simp only [nsmul_eq_mul, Pi.zero_apply] at hMt0
  --rw [this] at hMt0
  --intros x


  -- simp only [nsmul_eq_mul, Pi.zero_apply] at hMt0
  -- rw [← mul_sum] at hMt0

  -- intros x hx
  -- simp only [nsmul_eq_mul] at hMt0
  -- simp only [map_mul, Equiv.toFun_as_coe, finProdFinEquiv_symm_apply,
  -- Fin.coe_divNat, Nat.cast_add,
  --   Nat.cast_one, Fin.coe_modNat, nsmul_eq_mul, map_pow, map_add,
  --map_natCast, map_one, mul_eq_zero,
  --   map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff, pow_eq_zero_iff', ne_eq,
  --   AddLeftCancelMonoid.add_eq_zero, Nat.div_eq_zero_iff, one_ne_zero, and_false, or_self,
  --   not_false_eq_true, pow_eq_zero_iff]
  -- left

 -- rw [← mul_right_inj']
--· exact Complex.log α
    --exact sys_coeffs_foo α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq l k
  --· exact log_zero_zero α htriv

  -- obtain ⟨η, ⟨htneq0, ⟨hMt0,hbound⟩⟩⟩ :=
  --   applylemma82 α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  -- unfold A at hMt0
  -- simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow] at hMt0

-- from lemma 8.2
-- lemma l : order R l ≥ n
-- from this you get r ≥ n

/-need this for order-/
lemma R_analyt_at_point (point : ℕ) :
 AnalyticAt ℂ (R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t) point := by
  apply Differentiable.analyticAt (sum fun _ _ =>
  (differentiable_const _).mul
    (differentiable_exp.comp ((differentiable_const _).mul differentiable_id')))

lemma analyticEverywhere : ∀ (z : ℂ),
  AnalyticAt ℂ (R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq  t) z := by {
  intros z
  apply Differentiable.analyticAt (sum fun _ _ =>
  (differentiable_const _).mul
    (differentiable_exp.comp ((differentiable_const _).mul differentiable_id')))}

def min_value_over_finset {γ : Type _} (f : Π _ : Finset.range (m K + 1), γ)
  [Fintype s] [Nonempty s] [LinearOrder γ] : γ := by
  apply Finset.min' (f '' Set.univ).toFinset
  simp only [Set.image_univ, Set.toFinset_range, Finset.image_nonempty,
    univ_eq_attach, attach_nonempty_iff]
  exact nonempty_range_succ

instance nonemptyFinsetRangeOfm : Nonempty (Finset (Finset.range ((m K + 1)))) :=
  instNonemptyOfInhabited

lemma IsAnalyticRAtl :
  AnalyticAt ℂ (R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t) u.1 := by
  apply Differentiable.analyticAt (sum fun _ _ =>
  (differentiable_const _).mul
    (differentiable_exp.comp ((differentiable_const _).mul differentiable_id')))

def order := AnalyticAt.order
  (IsAnalyticRAtl α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq)

--zero_iff_order_inf
lemma order_neq_top :
  order α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq ≠ ⊤ := by {
  unfold _root_.order
  intros H
  sorry
}

include α β σ K σ α' β' γ' u in
def r : ℕ := by
  apply @min_value_over_finset K _ _ _ _ _ _ (nonemptyFinsetRangeOfm K) _
  exact fun x =>
  (AnalyticAt.order
    (IsAnalyticRAtl α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq)).toNat

lemma r_qeq_0 :
  0 ≤ r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq := by {
    exact Nat.zero_le (r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq)}

lemma r_div_q_geq_0 :
  0 ≤ r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq / q  := by {
    simp_all only [zero_le]}

#check iterated_deriv_eq_zero_imp_n_leq_order
#check iterated_deriv_eq_zero_iff_order_eq_n
--on the board

-- lemma foo' : -- "order of f is not infinite, f is analytic at l"
--   (∀ k < n, iteratedDeriv k f l = 0) →
--   n ≤ order f l
--   sorry

lemma foo :
  let l : ℕ := (finProdFinEquiv.symm.1 u).1 + 1
  let k : ℕ := (finProdFinEquiv.symm.1 u).2
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let R := R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq  t

  (∀ k < n K q, iteratedDeriv k R l = 0) →
  n K q ≤ order α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq := by {
  intros l k r R order k
  unfold _root_.order
  apply iterated_deriv_eq_zero_imp_n_leq_order
  · intros z
    have := order_neq_top α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
    unfold _root_.order at this
    sorry
    --apply analyticEverywhere α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  · have := iteratedDeriv_vanishes α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
    intros k hk
    specialize this k hk
    rw [← this]
    sorry
  · exact fun z ↦ analyticEverywhere α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq z
  }

lemma rgeqn :
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  n K q ≤ r  := sorry

-- for the next lemma you need that if you take the minimum over a set, there is a value
-- in the set where the minimum is attained.
lemma exists_minimum_of_finset {α : Type _} [LinearOrder α] {s : Finset α} (hs : s.Nonempty) :
  ∃ x ∈ s, x = s.min' hs := by
  use s.min' hs
  constructor
  · exact s.min'_mem hs
  · rfl

-- you want somewhere a lemma that the order of R in l₀ is r

-- so yet another lemma: "there exists l₀ where the order of R in l₀ is r"
lemma exists_l₀_with_order_r :
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let R := R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t
  ∃ l₀ : Fin (m K), AnalyticAt.order
    (analyticEverywhere α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq l₀) = r := by
  intros r R
  let s := Finset.range (m K + 1)
  have hs : s.Nonempty := nonempty_range_succ
  have hmn : ∃ x ∈ s, x = s.min' hs := exists_minimum_of_finset hs
  obtain ⟨l₀, hl₀, hmin⟩ := hmn
  simp only at hmin
  use Fin.ofNat l₀
  rw [hmin]
  sorry


def l₀ : Fin (m K) :=
  (exists_l₀_with_order_r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq).choose
-- after that, you can define l₀ already!
-- these lemmas should go directly after the defintion of r
--on the board 1st lemma
lemma exists_nonzero_iteratedFDeriv :
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let R := R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t
  let o := (order α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq).toNat
  let l : ℕ := (finProdFinEquiv.symm.1 u).1 + 1
  let k : ℕ := (finProdFinEquiv.symm.1 u).2
  ∃ (l₀ : Fin (m K)), iteratedDeriv r R l₀ ≠ 0 := by {
  intros r R o l k
  use l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  have := iterated_deriv_eq_zero_iff_order_eq_n (k := k) (n K q) R l ?_ ?_
  · sorry
  · exact analyticEverywhere α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  · sorry
  }


-- you want somewhere a lemma that the order of R in each l is ≥ n
-- this follows from the fact that the R^(k)(l) = 0 for each k < n
-- which in turn follows from the equations that are solved in lemma 8.2
-- and the equivalence between derivatives being zero and the order
-- together this gives that r ≥ n
-- each of these lines should be a separate lemma!

-- you want somewhere a lemma that the order of R in each l is ≥ n
--   this follows from the fact that the R^(k)(l) = 0 for each k < n
lemma order_geq_n :
  let R := R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  ∀ l, n K q ≤
    AnalyticAt.order (analyticEverywhere α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq l) := by
  intros R r l
  apply iterated_deriv_eq_zero_imp_n_leq_order
  · intros z
    have := order_neq_top α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
    unfold _root_.order at this
    sorry
  · sorry

def cρ : ℤ := abs ((c₁ K α' β' γ')^(r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq) *
  (c₁ K α' β' γ')^(2*m K * q))

abbrev sys_coeffs' :
 Fin (q *q) → (Fin (m K *n K q)) → K := fun i j => by
  let a : ℕ := (finProdFinEquiv.symm.1 i).1 + 1
  let b : ℕ := (finProdFinEquiv.symm.1 i).2 + 1
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let l₀ : ℕ := (finProdFinEquiv.symm.1 j).1 + 1
  exact (a + b • β')^r * α' ^(a * l₀) * γ' ^(b * l₀)

lemma sys_coeffs'_ne_zero : sys_coeffs' α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq ≠ 0 := by
  unfold sys_coeffs'
  intros H
  rw [funext_iff] at H
  specialize H t
  rw [funext_iff] at H
  specialize H u
  simp only [Pi.zero_apply, mul_eq_zero, pow_eq_zero_iff',
    AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, or_self,
    not_false_eq_true, pow_eq_zero_iff] at H
  cases' H with H1 H2
  · cases' H1 with H1 H2
    · rcases H1 with ⟨h1, h2⟩
      apply β'_neq_zero α β hirr K σ α' β' γ' habc q t
        (r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq)
      rw [h1]
      simp only [pow_eq_zero_iff', ne_eq, true_and]
      exact h2
    · apply α'_neq_zero α β hirr htriv K σ α' β' γ' habc q u t
      simp only [pow_eq_zero_iff', ne_eq, true_and]
      exact H2
  · apply γ'_neq_zero α β hirr htriv K σ α' β' γ' habc q u t
    simp only [pow_eq_zero_iff', ne_eq, true_and]
    exact H2

def rho := ∑ t, (η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t) *
  sys_coeffs' α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t u

lemma rho_nonzero :
  rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq ≠ 0 := by
  unfold rho
  simp only [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff]
  intros H
  sorry

lemma cρ_ne_zero : cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq ≠ 0 := by
  unfold cρ
  intros H
  simp only [abs_eq_zero, mul_eq_zero, pow_eq_zero_iff', ne_eq, OfNat.ofNat_ne_zero, false_or,
    not_or] at H
  rcases H with ⟨H1,H2⟩
  have := c₁neq0 K α' β' γ'
  apply this
  exact H1
  apply c₁neq0 K α' β' γ'
  simp_all only [ne_eq, map_eq_zero]

lemma ρ_is_int : IsIntegral ℤ (cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  • rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq) := by
  unfold rho
  unfold cρ
  unfold sys_coeffs'

  cases' abs_choice (c₁ K α' β' γ' ^ r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
    * c₁ K α' β' γ' ^ (2 * m K * q)) with H1 H2
  · rw [H1]
    sorry
  · sorry

def c1ρ : 𝓞 K := RingOfIntegers.restrict _
  (fun _ => (ρ_is_int α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq)) ℤ

lemma eq5zero :
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let ρ := rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq
  let c₁ := c₁ K α' β' γ'
  let c1ρ := c1ρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let cρ := cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq

  1 ≤ norm (Algebra.norm ℚ ((algebraMap (𝓞 K) K) c1ρ))   := by {
  intros r ρ c₁ c1ρ cρ
  unfold c1ρ
  unfold _root_.c1ρ
  unfold RingOfIntegers.restrict
  simp only [zsmul_eq_mul]
  simp only [RingOfIntegers.map_mk, map_mul, norm_mul]

  have := @Algebra.norm_algebraMap ℚ _ K _ _
    (_root_.cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq)
  simp only [map_intCast] at this
  rw [this]
  simp only [norm_pow, Int.norm_cast_rat, ge_iff_le]

  have : ‖(Algebra.norm ℚ) (rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq)‖ ≠ 0 := by {
    rw [norm_ne_zero_iff]
    rw [Algebra.norm_ne_zero_iff]
    exact rho_nonzero α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq}

  have h0 : 0 < ‖_root_.cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq‖ := by {
    rw [norm_pos_iff]
    have := cρ_ne_zero α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
    unfold cρ at this
    exact this}

  have h1 : 1 ≤ ‖_root_.cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq‖
    ^ Module.finrank ℚ K := by {
      rw [one_le_pow_iff_of_nonneg]
      · rw [Int.norm_eq_abs]
        rw [Int.norm_eq_abs] at h0
        sorry
      · apply norm_nonneg
      · have : 0 < Module.finrank ℚ K  := by {exact Module.finrank_pos}
        simp_all only [ne_eq, norm_eq_zero, Algebra.norm_eq_zero_iff, norm_pos_iff]
        intro a
        simp_all only [lt_self_iff_false]}

  have h2 : 0 < ‖(Algebra.norm ℚ) (rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq)‖ := by {
    rw [norm_pos_iff]
    rw [Algebra.norm_ne_zero_iff]
    exact rho_nonzero α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq}

  calc 1 ≤ ‖_root_.cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq‖ ^ Module.finrank ℚ K := h1
       _ ≤ ‖_root_.cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq‖ ^ Module.finrank ℚ K *
         ‖(Algebra.norm ℚ) (rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq)‖ := ?_

  · nth_rw 1 [← mul_one (‖_root_.cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq‖
       ^ Module.finrank ℚ K)]
    rw [mul_le_mul_left]
    · sorry
    · rw [le_iff_eq_or_lt] at h1
      cases' h1 with h1 h1
      · rw [← h1]
        simp only [zero_lt_one]
      · trans
        · apply zero_lt_one
        · exact h1}

def c₅ : ℝ := max 2 (c₁ K α' β' γ' ^ ((h K : ℤ) * (2 * m K * q)))

lemma eq5 :
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq;
  let ρ := rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq;
  let c₁ := (c₁ K α' β' γ')
  let c1ρ := c1ρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq;
  let cρ := cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq;
  let c₅ := c₅ K α' β' γ' q

  c₅ ^ (- r : ℤ) < norm (Algebra.norm ℚ ρ) := by

  intros r ρ c₁ c1ρ cρ c₅

  simp only [zpow_neg, zpow_natCast, gt_iff_lt]

  have h1 : 1 ≤
    ‖(_root_.cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq)^ Module.finrank ℚ K‖ *
    ‖(Algebra.norm ℚ) (rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq)‖ := by {

  have := eq5zero α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  unfold c1ρ at this
  unfold _root_.c1ρ at this
  unfold RingOfIntegers.restrict at this
  simp only [zsmul_eq_mul] at this
  simp only [RingOfIntegers.map_mk, map_mul, norm_mul] at this

  have h := @Algebra.norm_algebraMap ℚ _ K _ _
    (_root_.cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq)
  simp only [map_intCast] at h
  simp only [norm_pow, Int.norm_cast_rat, ge_iff_le]
  rw [h] at this
  simp only [norm_pow, Int.norm_cast_rat] at this
  exact this}

  have h2 :
    ‖(_root_.cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq)^ Module.finrank ℚ K‖⁻¹ ≤
     norm (Algebra.norm ℚ ρ) := by {

      have : 0 < ‖ (_root_.cρ α β hirr
           htriv K σ hd α' β' γ' habc q u t hq0 h2mq)^ Module.finrank ℚ K‖ := by {
        rw [norm_pos_iff]
        simp only [ne_eq, pow_eq_zero_iff', Algebra.norm_eq_zero_iff, Int.cast_eq_zero, not_and,
          Decidable.not_not]
        intros H
        by_contra H1
        apply cρ_ne_zero α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
        exact H
        }

      rw [← mul_le_mul_left this]

      · rw [mul_inv_cancel₀]
        · simp_all only [norm_pow, ρ]
        · simp only [norm_pow, ne_eq, pow_eq_zero_iff', norm_eq_zero, not_and, Decidable.not_not,
          ρ]
          intros H
          rw [H] at this
          simp only [norm_pow, norm_zero, ρ] at this
          rw [zero_pow] at this
          by_contra H1
          simp_all only [norm_pow, lt_self_iff_false, ρ]
          · simp_all only [norm_pow, lt_self_iff_false, ρ]
            have : 0 < Module.finrank ℚ K := by {
            exact Module.finrank_pos}
            simp_all only [norm_zero, ne_eq, ρ]
            obtain ⟨left, right⟩ := htriv
            obtain ⟨left_1, right_1⟩ := habc
            obtain ⟨left_2, right_1⟩ := right_1
            subst left_2 left_1
            apply Aesop.BuiltinRules.not_intro
            intro a
            simp_all only [pow_zero, zero_lt_one, lt_self_iff_false]
            }

  calc _ = _ := ?_
       c₅ ^ ((-r : ℤ)) < c₁^ ((- h K : ℤ) * (r + 2 * m K * q) ) := ?_
       _ < ‖(_root_.cρ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq)
          ^ Module.finrank ℚ K‖⁻¹ := ?_
       _ ≤ norm (Algebra.norm ℚ ρ) := ?_

  · simp only [zpow_neg, zpow_natCast]
  · simp only [zpow_neg, zpow_natCast, neg_mul]
    rw [inv_lt_inv₀]
    · rw [mul_add]
      have : (h K : ℤ) * r + h K * (2 * m K * ↑q) = h K* r + h K * 2 * m K * ↑q := by
        rw [mul_assoc, mul_assoc, mul_assoc]
      rw [this]
      sorry
    · unfold c₅
      --unfold _root_.c₁
      trans
      · have : (0 : ℝ) < 1 := by {simp only [zero_lt_one]}
        apply this
      · unfold _root_.c₅
        apply one_lt_pow₀
        simp only [lt_sup_iff, Nat.one_lt_ofNat, true_or]
        sorry
    · trans
      · have : (0 : ℝ) < 1 := by {simp only [zero_lt_one]}
        apply this
      · apply one_lt_pow₀
        · sorry
        · sorry
  · unfold _root_.cρ
    rw [← pow_add]
    simp only [neg_mul, zpow_neg, abs_pow, norm_pow]
    rw [Int.norm_eq_abs]
    simp only [Int.cast_abs, abs_abs]
    rw [← pow_mul]
    sorry
  · exact h2






















def c₆ : ℝ := sorry

def c₇ : ℝ := sorry

def c₈ : ℝ := sorry --max (c₄^n * (n^(1/2)*(n+1))*q^2*(c₆*q)^n*(c₇)^(q : ℤ)) 1
--max (c₈^r) ((c₈)^r * r ^ (r+3/2))

lemma eq6 :
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq;
  let ρ := rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq;
  let c₄ := c₄ K hd α' β' γ' q
  let a : ℕ := (finProdFinEquiv.symm.1 t).1 + 1
  let b : ℕ := (finProdFinEquiv.symm.1 t).2 + 1
  let l₀ : ℕ := l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq

  house ρ ≤ c₈^r * r^(r + 3/2) := by {

  intros r  ρ c₄ a b l₀
  unfold ρ
  unfold rho

  calc _ ≤ (∑ t, house (↑(η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t) *
          sys_coeffs' α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t u)) := ?_

       _ ≤ (∑ t, house (algebraMap (𝓞 K) K
        (η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t)) *
          house (sys_coeffs' α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t u)) := ?_

       _ ≤ (∑ t, (c₄ ^ (n K q : ℝ)) * ((n K q)^((1/2)*((n K q)+1)) ) *
          house (sys_coeffs' α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t u)) := ?_

       _ ≤ (∑ t : Fin (q*q), (c₄ ^ (n K q : ℝ)) * ((n K q)^((1/2)*((n K q)+1)) ) *
           (house (a + b • β') ^ r * house (α') ^ (a * l₀) * house (γ') ^ (b * l₀))
           ) := ?_

       _ ≤  (∑ t : Fin (q*q), (c₄ ^ (n K q : ℝ)) * ((n K q)^ ((1/2)*(n K q +1))) *
         (Nat.sqrt (2*m K)* (1 + house (β'))* (house (α') ^ (2*m K^2)) * house (γ') ^(2*m K^2)))
           := ?_

       _ ≤ (q*q) *((c₄ ^ (n K q : ℝ)) *
         ((n K q)^((1/2)*((n K q)+1))) * (c₆* q) ^r * (c₇)^(q : ℤ)) := ?_

       _ ≤ c₈^r * r^( r + 3/2) := ?_

  · apply house_sum_le_sum_house
  · apply sum_le_sum
    intros i hi
    apply house_mul_le
  · apply sum_le_sum
    intros i hi
    have := fromlemma82_bound α β hirr htriv K σ hd α' β' γ' habc q u i hq0 h2mq
    apply mul_le_mul
    unfold c₄
    · exact this
    · apply Preorder.le_refl
    · apply house_nonneg
    · unfold c₄
      unfold _root_.c₄
      simp only [Real.rpow_natCast, Nat.reduceDiv, zero_mul, pow_zero, mul_one, le_sup_iff,
        zero_le_one, true_or, pow_nonneg]
  · apply sum_le_sum
    intros i hi
    apply mul_le_mul
    · simp only [Real.rpow_natCast, Nat.reduceDiv, zero_mul, pow_zero, mul_one, le_refl]
    · unfold sys_coeffs'
      trans
      · apply house_mul_le
      · rw [mul_comm]
        nth_rw 1 [mul_assoc]
        have : house (↑a + b • β') ^ r * (house α' ^ (a * l₀) * house γ' ^ (b * l₀)) =
          house γ' ^ (b * l₀) * (house (↑a + b • β') ^ r * (house α' ^ (a * l₀))) := by {
            rw [← mul_assoc]
            rw [mul_comm (house γ' ^ (b * l₀))]
          }
        rw [this]
        apply mul_le_mul
        · trans
          · apply house_pow_le
          · sorry
        · trans
          · apply house_mul_le
          · apply mul_le_mul
            · trans
              · apply house_pow_le
              · sorry
            · trans
              · apply house_pow_le
              · sorry
            · apply house_nonneg
            · apply pow_nonneg
              apply house_nonneg
        · apply house_nonneg
        · apply pow_nonneg
          · apply house_nonneg
    · apply house_nonneg
    · simp only [Real.rpow_natCast, Nat.reduceDiv, zero_mul, pow_zero, mul_one]
      unfold c₄
      unfold _root_.c₄
      simp only [le_sup_iff, zero_le_one, true_or, pow_nonneg]
  · apply sum_le_sum
    intros i hi
    simp only [Real.rpow_natCast, Nat.reduceDiv, zero_mul, pow_zero, mul_one, nsmul_eq_mul]
    apply mul_le_mul
    · simp only [le_refl]
    · apply mul_le_mul
      · sorry
      · sorry
      · apply pow_nonneg
        apply house_nonneg
      · apply mul_nonneg
        · apply mul_nonneg
          · simp only [Nat.cast_nonneg]
          · trans
            · apply zero_le_one
            · simp only [le_add_iff_nonneg_right]
              apply house_nonneg
        · apply pow_nonneg
          apply house_nonneg
    · apply mul_nonneg
      · apply mul_nonneg
        · apply pow_nonneg
          apply house_nonneg
        · apply pow_nonneg
          apply house_nonneg
      · apply pow_nonneg
        apply house_nonneg
    · unfold c₄
      unfold _root_.c₄
      simp only [le_sup_iff, zero_le_one, true_or, pow_nonneg]
  · rw [sum_const, card_univ, Fintype.card_fin]
    simp only [Real.rpow_natCast, Nat.reduceDiv, zero_mul, pow_zero, mul_one, nsmul_eq_mul,
      Nat.cast_mul, zpow_natCast]
    apply mul_le_mul
    · simp only [le_refl]
    · apply mul_le_mul
      · sorry
      · sorry
      · apply mul_nonneg
        · apply mul_nonneg
          · apply mul_nonneg
            · simp only [Nat.cast_nonneg]
            · trans
              · apply zero_le_one
              · simp only [le_add_iff_nonneg_right]
                apply house_nonneg
          · apply pow_nonneg
            apply house_nonneg
        · apply pow_nonneg
          apply house_nonneg
      · apply mul_nonneg
        · unfold c₄
          unfold _root_.c₄
          simp only [le_sup_iff, zero_le_one, true_or, pow_nonneg]
        · apply pow_nonneg
          sorry
    · apply mul_nonneg
      · unfold c₄
        unfold _root_.c₄
        simp only [le_sup_iff, zero_le_one, true_or, pow_nonneg]
      · apply mul_nonneg
        · apply mul_nonneg
          apply mul_nonneg
          · simp only [Nat.cast_nonneg]
          · trans
            · apply zero_le_one
            · simp only [le_add_iff_nonneg_right]
              apply house_nonneg
          · apply pow_nonneg
            apply house_nonneg
        · apply pow_nonneg
          apply house_nonneg
    · simp_all only [Nat.cast_pos, mul_nonneg_iff_of_pos_left, Nat.cast_nonneg]
  · sorry
}















lemma for_def_of_S (hl : l ∈ Finset.range (m K)) :
  let R := R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq;
  ∃ (R' : ℂ → ℂ), (∀ z, AnalyticAt ℂ R' z) ∧ ∀ x, R x = (x - l : ℂ) ^ r * R' x := sorry

def S : ℂ → ℂ := fun z => by
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let l₀ : ℕ := l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let R := R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq  t
  exact
  R z * (r.factorial)* (((z - l₀) ^ (-r : ℤ))
    * (∏ k ∈ range (m K) \ { l₀ }, ((l₀ - k)/ (z - k)) ^ r))

lemma holS :
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let S := S α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let l₀ := l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  ∀ x ∈ Metric.ball 0 (m K *(1 + (r/q))) \ {(l₀ : ℂ)},
  DifferentiableAt ℂ S x := by {
  intros r S l₀ z hz
  unfold S
  unfold _root_.S
  apply Differentiable.mul
  · apply Differentiable.mul
    · exact (sum fun _ _ =>
  (differentiable_const _).mul
    (differentiable_exp.comp ((differentiable_const _).mul differentiable_id')))
    · simp only [differentiable_const]
  · apply Differentiable.mul
    · apply Differentiable.zpow
      · simp only [differentiable_id',
          differentiable_const, Differentiable.sub]
      · left
        simp only [mem_diff, Metric.mem_ball,
          dist_zero_right, mem_singleton_iff] at hz
        intros x HX
        rw [sub_eq_zero] at HX
        sorry
    · sorry}

lemma hcauchy :
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let l₀ := l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let S := S α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq

  (2 * ↑Real.pi * I)⁻¹ * (∮ z in C(0, m K *(1 + (r / q))), (z - l₀)⁻¹ * S z) = S l₀ := by

  intros r l₀ S

  apply two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
  · have : Set.Countable {(l₀ : ℂ)} := countable_singleton (l₀ : ℂ)
    exact this
  · have : (l₀ : ℂ) ∈ Metric.ball 0 (m K * (1 + ↑r / ↑q)) := by {
    simp only [Metric.mem_ball, dist_zero_right]
    simp only [norm_natCast]
    have : (l₀ : ℝ) < m K := by {
      simp only [Nat.cast_lt]
      unfold l₀
      unfold _root_.l₀
      simp only [ne_eq, Fin.is_lt]}
    trans
    · exact this
    · apply lt_mul_right
      · exact mod_cast hm K
      · simp only [lt_add_iff_pos_right]
        apply div_pos
        · --simp only [Nat.cast_pos]
          sorry
        · simp only [Nat.cast_pos]
          exact hq0}
    exact this
  · intros x hx
    apply @DifferentiableWithinAt.continuousWithinAt ℂ _ _ _ _ _ _ _ _ _
    refine DifferentiableAt.differentiableWithinAt ?_
    apply holS
    simp only [mem_diff, Metric.mem_ball, dist_zero_right, mem_singleton_iff]
    simp only [Metric.mem_closedBall, dist_zero_right] at hx
    rw [le_iff_eq_or_lt] at hx
    sorry
  · apply holS

lemma newρ :
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let l₀ := l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let S := S α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let ρ := rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq

  σ ρ = log α ^ (-r : ℤ) * ((2 * ↑Real.pi * I)⁻¹ *
    (∮ z in C(0, m K *(1+ (r/q))), (z - l₀)⁻¹ * S z)) := by

  intros r l₀ S ρ

  calc _ = (log α)^(- r : ℤ) * S l₀ := ?_
       _ = log α ^ (-r : ℤ) * ((2 * ↑Real.pi * I)⁻¹ *
      (∮ z in C(0, m K *(1 + (r/q))), (z - l₀)⁻¹ * S z)) := ?_
  · sorry
  · rw [hcauchy]

def c₉ : ℝ := sorry

def c₁₀ : ℝ := sorry

lemma abs_R :
  let R := R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq  t
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let l₀ := l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let S := S α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let ρ := rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq
  let η := η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let c₄ := c₄ K hd α' β' γ' q

  norm (R z) ≤ (c₁₀)^r * r^(1/2*(r+3)) := by

  intros R r l₀ S ρ η c₄

  calc _ ≤ ∑ t, (‖σ ↑(_root_.η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t)‖
          * ‖cexp (_root_.ρ α β q t * z)‖) := ?_
       _ ≤ ∑ t : Fin (q*q), ((c₄)^(n K q : ℝ) * (n K q) ^((1/2)*(n K q +1)) *
         (Real.exp ((q+q*(norm β))* m K *(1+r/q))*(norm α))) := ?_
       _ ≤ (q*q) * ((c₄)^(n K q : ℝ) * (n K q) ^((1/2)*(n K q +1))*(c₉)^(r+q)) := ?_
       _ ≤ (c₁₀)^r * r^(1/2*(r+3)) := ?_
  · unfold R
    unfold _root_.R
    apply norm_sum_le_of_le
    intros b hb
    simp only [Complex.norm_mul, le_refl]
  · apply sum_le_sum
    intros i hi
    apply mul_le_mul
    · have lemma82 := fromlemma82_bound α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
      unfold c₄
      have : house ((algebraMap (𝓞 K) K)
        (_root_.η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq t)) =
        ‖σ ↑(_root_.η α β hirr htriv K σ hd α' β' γ' habc q u i hq0 h2mq i)‖ := sorry
      rw [← this]
      exact lemma82
    · have : ∀ i, ‖cexp (_root_.ρ α β q i * z)‖ ≤
         (Real.exp ((q+q*(norm β))* m K *(1+r/q))*(norm α)) := sorry
      apply this
    · apply norm_nonneg
    · unfold c₄
      simp only [Real.rpow_natCast, Nat.reduceDiv, zero_mul,
        pow_zero, mul_one, le_sup_iff,
        zero_le_one, true_or, pow_nonneg]
  · simp only [Real.rpow_natCast, Nat.reduceDiv, zero_mul, pow_zero,
    mul_one, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
    apply mul_le_mul
    · simp only [le_refl]
    · apply mul_le_mul
      · simp only [le_refl]
      · sorry
      · apply mul_nonneg
        · trans
          · apply zero_le_one
          · simp only [Real.one_le_exp_iff]
            apply mul_nonneg
            · apply mul_nonneg
              · have : (q : ℝ) = q * 1 := by {simp only [mul_one]}
                nth_rw 1 [this]
                rw [← mul_add]
                apply mul_nonneg
                · simp only [Nat.cast_nonneg]
                · trans
                  · apply zero_le_one
                  · simp only [le_add_iff_nonneg_right, norm_nonneg]
              · simp only [Nat.cast_nonneg]
            · trans
              · apply zero_le_one
              · simp only [le_add_iff_nonneg_right]
                sorry
        · apply norm_nonneg
      · unfold c₄
        unfold _root_.c₄
        simp only [Real.rpow_natCast, le_sup_iff, zero_le_one, true_or, pow_nonneg]
    · apply mul_nonneg
      · unfold c₄
        unfold _root_.c₄
        simp only [Real.rpow_natCast, le_sup_iff, zero_le_one, true_or, pow_nonneg]
      · apply mul_nonneg
        · trans
          · apply zero_le_one
          · simp only [Real.one_le_exp_iff]
            apply mul_nonneg
            · apply mul_nonneg
              · have : (q : ℝ) = q * 1 := by {simp only [mul_one]}
                nth_rw 1 [this]
                rw [← mul_add]
                apply mul_nonneg
                · simp only [Nat.cast_nonneg]
                · trans
                  · apply zero_le_one
                  · simp only [le_add_iff_nonneg_right, norm_nonneg]
              · simp only [Nat.cast_nonneg]
            · trans
              · apply zero_le_one
              · simp only [le_add_iff_nonneg_right]
                sorry
        · apply norm_nonneg
    · apply mul_nonneg
      · simp only [Nat.cast_nonneg]
      · simp only [Nat.cast_nonneg]
  · sorry

lemma abs_hmrqzl₀ :
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let l₀ := l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq

  ∀ (hz : z ∈ Metric.sphere 0 (m K *(1+ (r/q)))), m K *r/q ≤ norm (z - l₀ : ℂ) := by

  intros r l₀ hz

  calc _ = (m K* (1 + r/q) - m K : ℝ) := ?_
       _ ≤ norm z - norm (l₀ : ℂ) := ?_
       _ ≤ norm (z - l₀) := ?_

  · ring
  · simp only [hz, norm_natCast]
    have hlm : (l₀ : ℝ) < m K := by {
        unfold l₀
        unfold _root_.l₀
        simp only [Nat.cast_lt, Fin.is_lt]}
    simp only [mem_sphere_iff_norm, sub_zero] at hz
    rw [hz]
    simp only [tsub_le_iff_right, ge_iff_le]
    have : ↑(m K) * (1 + ↑r / ↑q) - ↑l₀ =
      ↑(m K) * (1 + ↑r / ↑q) + (- ↑l₀ : ℝ) := rfl
    rw [this]
    rw [add_assoc]
    simp only [le_add_iff_nonneg_right, le_neg_add_iff_add_le, add_zero, Nat.cast_le, ge_iff_le]
    rw [le_iff_lt_or_eq ]
    left
    simp only [Nat.cast_lt] at hlm
    exact hlm
  · exact norm_sub_norm_le z ↑l₀

lemma abs_z_k (k : Fin (m K)) :

  let R := R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq  t
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let l₀ : ℕ := l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let S := S α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let ρ := rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq
  let η := η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq

  ∀ (hz : z ∈ Metric.sphere 0 (m K *(1 + (r/q)))), (m K) * r/q ≤ norm (z-k : ℂ) := by

  intros R r l₀ S ρ η hz

  calc _ = (m K* (1 + r/q) - m K : ℝ) := ?_
       _ ≤ norm z - norm (k : ℂ) := ?_
       _ ≤ norm (z - k) := ?_
  · ring
  · simp only [hz, norm_natCast]
    have hlm : (k : ℝ) < m K := by {
        simp only [Nat.cast_lt, Fin.is_lt]}
    simp only [mem_sphere_iff_norm, sub_zero] at hz
    rw [hz]
    simp only [tsub_le_iff_right, ge_iff_le]
    have : ↑(m K) * (1 + ↑r / ↑q) - ↑k =
      ↑(m K) * (1 + ↑r / ↑q) + (- ↑k : ℝ) := rfl
    rw [this]
    rw [add_assoc]
    simp only [le_add_iff_nonneg_right,
      le_neg_add_iff_add_le, add_zero, Nat.cast_le, ge_iff_le]
    rw [le_iff_lt_or_eq ]
    left
    simp only [Nat.cast_lt] at hlm
    exact hlm
  · exact norm_sub_norm_le z k

def c₁₁ : ℝ := sorry

def c₁₂ : ℝ := sorry

lemma blah :
  let R := R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq  t
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let l₀ : ℕ := l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let S := S α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  --let ρ := rho α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  --let η := η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq

  norm (S z) ≤ (c₁₂)^r * ( ( 3 - m K) / 2 + 3 / 2) := by

  intros R r l₀ S
  calc
      _ = norm ((R z) * (r.factorial) * (((z - l₀) ^ (-r : ℤ)) *
          ∏ k ∈ Finset.range (m K) \ {(l₀)}, ((l₀ - k) / (z - k)) ^ r) : ℂ) := ?_

      _ = r.factorial * (norm (R z) * norm ( (1/(z - l₀ : ℂ) ^ r)) *
            norm (∏ k ∈ Finset.range ((m K)) \
                {(l₀)}, ((l₀ - k) / (z - k)) ^ r)) := ?_

      _ ≤ r.factorial * ((c₁₀)^r * r^(1/2*(r+3)) * (c₁₁)^r * (q/r)^(m K *r)) := ?_

      _ ≤ (c₁₂)^r*((3-m K)/2 + 3 /2) := ?_

  · unfold S
    unfold _root_.S
    rfl
  · simp only [zpow_neg, zpow_natCast, Complex.norm_mul,
      norm_natCast, norm_inv, norm_pow, norm_prod, Complex.norm_div, one_div]
    nth_rewrite 2 [mul_assoc]
    nth_rewrite 2 [← mul_assoc]
    simp only [mul_eq_mul_right_iff, mul_eq_zero, inv_eq_zero,
      pow_eq_zero_iff', norm_eq_zero, ne_eq]
    left
    exact Eq.symm (Nat.cast_comm r.factorial ‖R z‖)
  · apply mul_le_mul
    · simp only [le_refl]
    · rw [mul_assoc]
      rw [mul_assoc]
      · apply mul_le_mul
        · have : norm (R z) ≤ (c₁₀)^r * r^(1/2*(r+3)) :=
          abs_R α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
          exact this
        · sorry
        · apply mul_nonneg
          · apply norm_nonneg
          · apply norm_nonneg
        · sorry
    · apply mul_nonneg
      · apply mul_nonneg
        · simp only [norm_nonneg]
        · simp only [inv_nonneg, norm_nonneg, pow_nonneg]
      · simp only [norm_nonneg]
    · simp only [Nat.cast_nonneg]
  · sorry




















def c₁₃ : ℝ := sorry

def hρ :
  let R := R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq  t
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let l₀ := l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let S := S α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let ρ := rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq
  let η := η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq

  σ ρ  = ((2 * Real.pi)⁻¹ * ∮ (z : ℂ) in
    C(0, m K* (1 + ↑r / ↑q)), (z - ↑l₀)⁻¹ * S z) := sorry

lemma eq8 :
  let R := R α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq t
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let l₀ := l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let S := S α β hirr htriv  K σ hd α' β' γ' habc q u t hq0 h2mq
  let ρ := rho α β hirr htriv K σ hd α' β' γ' habc q u hq0 h2mq
  let η := η α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq

  norm (σ ρ) ≤ (c₁₃)^r*r^(r*(3-m K)/2 +3/2) := by

  intros R r l₀ S ρ η

  calc _ = norm ((2 * Real.pi)⁻¹ * ∮ (z : ℂ) in
           C(0, m K* (1 + ↑r / ↑q)), (z - ↑l₀)⁻¹ * S z) := ?_

       _ ≤ norm ((2 * Real.pi)⁻¹) * norm (∮ (z : ℂ) in
          C(0, m K * (1 + ↑r / ↑q)), (z - ↑l₀)⁻¹ * S z) := ?_

       _ ≤ norm ((log α))^((-r : ℤ)) * m K *(1+r/q)*
                (c₁₂)^r * r^(r*(3-m K)/2 + 3/2) * q/(m K * r) := ?_

       _ ≤ (c₁₃)^r * r^(r * (3- m K)/2 + 3/2)  := ?_

  · rw [hρ]
  · simp_all [l₀, S, r]
  · sorry
  · sorry

def c₁₄ : ℝ := sorry

lemma use6and8 :
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let l₀ := l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let S := S α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq

  (Algebra.norm ℚ ρ) ≤ (c₁₄)^r * r^((-r : ℤ)/2 + 3 * h K/2) := by

  intros r l₀ S

  have : (((h K -1) : ℤ) * (r + 3/2 : ℤ) + (3-m K) * r * 1/2 + 3/2) =
    ((-r : ℤ)/2 + 3 * h K/2) := by {
      sorry
    }

  calc _ ≤ ((c₁₄)^r) * r^ ((h K -1) * (r + 3/2 : ℤ) + (3-m K) * r * 1/2 + 3/2) := ?_
       _ = ((c₁₄)^r) * r^ ((-r : ℤ)/2 + 3 * h K/2) := ?_
  · sorry
  · rw [← this]

def c₁₅ : ℝ := c₁₄ * c₅ K α' β' γ' q

include α β σ hq0 h2mq hd hirr htriv K σ α' β' γ' habc h2mq u t in
theorem main :
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  r ^ ((r - 3 * (h K)) / 2) ≥ c₁₅ K α' β' γ' q ^ r := by

  have := rgeqn α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  sorry
  --use r_geq_n K α β hirr htriv σ hd α' β' γ' habc q u t hq0 h2mq

lemma use5 :
  let r := r α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let l₀ := l₀ α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq
  let S := S α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq

  r^((r - 3 * (h K)) / 2) < c₁₅ K α' β' γ' q ^r := by

  intros r l₀ S

  calc _ < c₁₄^r * (c₅ K α' β' γ' q) ^r := ?_
       _ = (c₁₅ K α' β' γ' q) ^r := ?_
  · sorry
  · rw [← mul_pow]
    simp only [c₁₅]

--include hα hβ α β σ hq0 h2mq hd hirr htriv K σ h2mq t q in
theorem hilbert7 (α β : ℂ) (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β)
  (htriv : α ≠ 0 ∧ α ≠ 1) (hirr : ∀ i j : ℤ, β ≠ i / j) :
    Transcendental ℚ (α ^ β) := fun hγ => by

  obtain ⟨K, hK, hNK, σ, hd, α', β', γ', habc⟩ := getElemsInNF α β (α^β) hα hβ hγ

  let q : ℕ := 5

  let t : Fin (q * q) := sorry

  have hq0 : 0 < q := Nat.zero_lt_succ 4

  let m : ℕ := m K

  let u : Fin (m * n K q) := sorry

  have h2mq : 2 * m ∣ q ^ 2 := by {
    refine Dvd.dvd.pow ?_ ?_
    · sorry
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
    }

  have main := main α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq

  have use5 := use5 α β hirr htriv K σ hd α' β' γ' habc q u t hq0 h2mq

  simp only at use5

  apply absurd main
  simp only [ge_iff_le, not_le]
  exact use5















































































































--   -- let ρ : (Fin q × Fin q) → (Fin m × Fin r) → K := fun (a,b) (l₀,k) =>
--   --   algebraMap (𝓞 K) K (η (a, b))

--   let ρ : (Fin q × Fin q)  → K := fun (a,b) =>
--      algebraMap (𝓞 K) K (η (a, b))

--     -- ((a+1) + (b+1) * β')^(r : ℤ)
--     -- * α'^((a+1) * (l₀+1 : ℤ))
--     -- * γ' ^((b+1) * (l₀+1 : ℤ))

--   let c₅ : ℝ := c₁^(h*r + h*2*m K*q : ℤ)

  --The norm of an algebraic integer is again an integer,
  --because it is equal (up to sign)
   --  to the constant term of the characteristic polynomial.
  --fix this (N (c₁^(r+2mq) ρ)) = c₁^r+2mq*N(ρ)
  -- have eq5 (t : Fin q × Fin q) (u : Fin m × Fin r) : c₅^((-r : ℤ)) <
  --   norm (Algebra.norm ℚ (ρ t)) := by
  --     calc c₅^((-r : ℤ)) < c₁^((- h : ℤ)*(r + 2*m K*q)) := by {
  --       simp only [zpow_neg, zpow_natCast, neg_mul]
  --       rw [inv_lt_inv]
  --       · rw [mul_add]
  --         have : (h:ℤ) * r + ↑h * (2 * m K* ↑q) = (h :ℤ)* ↑r + ↑h * 2 * m K* ↑q := by
  --           rw [mul_assoc, mul_assoc, mul_assoc]
  --         rw [this]
  --         refine lt_self_pow ?h ?hm
  --         · rw [← one_zpow ((h : ℤ)* ↑r + ↑h * 2 * m K* ↑q )]
  --           simp only [one_zpow]
  --           simp only [c₁]
  --           simp only [Int.cast_mul, Int.cast_max, Int.cast_one]
  --           apply one_lt_pow
  --           · sorry
  --           · sorry
  --         · sorry
  --       · sorry
  --       · sorry
  --     }
  --       _ < norm (Algebra.norm ℚ (ρ t)):= sorry

--   let c₄' : ℝ  := c₄ ^ n * (↑n ^ (1 / 2) * (↑n + 1))

--   let c₆ : ℝ := sorry

--   let c₇ : ℝ := sorry

--   let c₈ : ℝ := max (c₄^n * (n^(1/2)*(n+1))*q^2*(c₆*q)^n*(c₇)^(q : ℤ)) 1

--   let c₈' : ℝ := max (c₈^r) ((c₈)^r * r ^ (r+3/2))

--   have eq6 (t : Fin q × Fin q) (u : Fin m × Fin r) :
--     house (ρ t) ≤ c₈' := by
--     calc _ ≤ c₄' := by {
--         simp only [c₄']
--         exact fromlemma82_bound t
--         }
--          _ ≤c₄'*(q^2*(c₆*q)^n*(c₇)^(q : ℤ)) := by {
--           apply  le_mul_of_one_le_right
--           · calc 0 ≤ 1 := sorry
--                  _ ≤ c₄' := sorry
--           · sorry
--          }
--          _ ≤ (c₈^r) := by { sorry
--           --apply le_max_left
--           }
--          _ ≤ c₈' := by {
--           simp only [c₈']
--           apply le_max_left
--           }

--   let S : (Fin m × Fin n) → ℂ → ℂ := fun (l₀, k) z =>
--     (r.factorial) * (R (l₀, k) z) / ((z - l₀) ^ r) *
--       ∏ k in Finset.range ((r - 1)) \ {(l₀ : ℕ)}, ((l₀ - k) / (z - k)) ^ r

--   -- --have hR : 0 < (m*(1+ (r/q)) : ℝ) := sorry
--   have alt_cauchy (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--       (∮ z in C(0, m*(1+ (r/q))), (z - l₀)⁻¹ * (S (l₀,k) z)) =
--         (2 * ↑Real.pi * I) •  S (l₀,k) l₀ := by
--     apply _root_.DifferentiableOn.circleIntegral_sub_inv_smul
--     · sorry
--     · simp only [Metric.mem_ball, dist_zero_right, norm_nat]
--       have : (l₀ : ℝ) < m := by simp only [Nat.cast_lt, Fin.is_lt]
--       trans
--       · exact this
--       · apply lt_mul_right
--         · exact mod_cast hm
--         · sorry

--   have hcauchy : ∀ (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q), (2 * ↑Real.pi * I)⁻¹ *
--     (∮ z in C(0, m*(1+ (r/q))), (z - l₀)⁻¹ * (S (l₀,k) z)) = S (l₀,k) l₀ := fun k l₀ t => by
--    apply two_pi_I_inv_smul_circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
--     · have : Set.Countable {(l₀ : ℂ)} := countable_singleton (l₀ : ℂ)
--       exact this
--     · have : (l₀ : ℂ) ∈ Metric.ball 0 (m K* (1 + ↑r / ↑q)) := by {
--       simp only [Metric.mem_ball, dist_zero_right, norm_nat]
--       have : (l₀ : ℝ) < m := by simp only [Nat.cast_lt, Fin.is_lt]
--       trans
--       · exact this
--       · apply lt_mul_right
--         · exact mod_cast hm
--         · sorry}
--       exact this
--     · intros x hx
--       simp only [Metric.mem_closedBall, dist_zero_right, norm_eq_abs] at hx
--       simp only [Prod.mk.eta, div_pow, prod_div_distrib, S]
--       simp only [Prod.mk.eta, sum_prod_type, R]
--       sorry

--     · have : ∀ z ∈ Metric.ball 0 (m K *(1+ (r/q))) \ {(l₀ : ℂ)},
--          DifferentiableAt ℂ (S (l₀, k)) z := by {
--       intros z hz
--       simp only [mem_diff, Metric.mem_ball, dist_zero_right, norm_eq_abs,
--         mem_singleton_iff] at hz
--       rcases hz with ⟨hzabs, hzneq⟩
--       --simp only [S,R]
--       -- have : DifferentiableAt ℂ (R (l₀, k)) z := by {
--       --   simp only [DifferentiableAt]
--       --   use fderiv ℂ (R (l₀, k)) z
--       --   --use ∑ t, σ (η t) *σ (ρ t) * exp (σ (ρ t) * l₀)
--       -- }
--       simp only [DifferentiableAt]
--       use fderiv ℂ (S (l₀, k)) z
--       sorry
--       }
--       exact this

-- lemma alt_cauchy :
--   let r := r K α β hirr htriv σ hd α' β' γ' habc q u t hq0 h2mq
--   let S := S K α β hirr htriv σ hd α' β' γ' habc q u t hq0 h2mq
--   let l₀ := l₀ K α β hirr htriv σ hd α' β' γ' habc q u t hq0 h2mq

--   (∮ z in C(0, m K * (1+ (r/q))), (z - l₀)⁻¹ * (S z)) = (2 * ↑Real.pi * I) • S l₀ := by

--   let l₀ := l₀ K α β hirr htriv σ hd α' β' γ' habc q u t hq0 h2mq

--   apply _root_.DifferentiableOn.circleIntegral_sub_inv_smul
--   · refine differentiableOn ?_
--     sorry
--   · simp only [Metric.mem_ball, dist_zero_right]
--     have : (l₀ : ℝ) < (m K) := by
--       simp only [Nat.cast_lt, Fin.is_lt]
--       unfold l₀
--       unfold _root_.l₀
--       simp only [ne_eq, Fin.is_lt]
--     trans
--     · simp only [norm_natCast]
--       exact this
--     · apply lt_mul_right
--       · simp only [Nat.cast_pos]
--         exact hm K
--       · simp_all only [Nat.cast_lt, lt_add_iff_pos_right,
--           Nat.cast_pos, div_pos_iff_of_pos_right, l₀]
--         sorry

--   have newρ (z : ℂ) (hz : z ∈ Metric.ball 0 (m K *(1+ (r/q))))
--           (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--       σ (ρ t) = log (α) ^ (-r : ℤ) * ((2 * ↑Real.pi * I)⁻¹ *
--         (∮ z in C(0, m*(1+ (r/q))), (z - l₀)⁻¹ * (S (l₀,k) z))) := by
--         calc
--       _ = (log (α))^(- r : ℤ) * (S  (l₀,k) l₀) := sorry
--       _ = log (α) ^ (-r : ℤ) * ((2 * ↑Real.pi * I)⁻¹ *
--       (∮ z in C(0, m*(1+ (r/q))), (z - l₀)⁻¹ * (S (l₀,k) z))) := by
--     {rw [← hcauchy]
--      exact t}

--   let c₉ : ℝ := sorry

--   let c₁₀ : ℝ := sorry

--   have abs_R (z : ℂ) (hz : z ∈ Metric.ball 0 (m K *(1+ (r/q)))) (k : Fin n)
--         (l₀ : Fin m) (t : Fin q × Fin q) :
--     norm (R (l₀, k) z) ≤ (c₁₀)^r * r^(1/2*(r+3)):= calc
--        _ ≤ q^2 * ‖σ (η t)‖*
--           Real.exp ((q+q*(norm (β)))*(Real.log (norm (α)))*m K*(1+r/q)) := by {
--             simp only [Prod.mk.eta, sum_prod_type, norm_eq_abs, R]
--             sorry

--           }
--        _ ≤ q^2 * (c₄)^n *n ^((1/2)*(n+1))*(c₉)^(r+q) := sorry
--        _ ≤ (c₁₀)^r * r^(1/2*(r+3)) := sorry

--   have abs_hmrqzl₀ (z : ℂ) (hz : z ∈ Metric.sphere 0 (m K *(1+ (r/q))))
--      (k : Fin n) (l₀ : Fin m) : m*r/q ≤ norm (z - l₀) := calc
--           _ = (m * (1 + r/q) - m : ℝ) := by {ring}
--           _ ≤ norm z - norm l₀ := by {
--           simp only [hz, norm_natCast]
--           have : (l₀ : ℝ) < m := by {
--             simp only [Nat.cast_lt, Fin.is_lt]
--             }
--           sorry
--           --rwa [sub_lt_sub_iff_left]
--           }
--           _ ≤ norm (z - l₀) := by {apply AbsoluteValue.le_sub}
--   have abs_z_k (k : Fin n) (l₀ : Fin m) (z : ℂ) (hz : z ∈ Metric.sphere 0 (m K *(1+ (r/q)))) :
--         m*r/q ≤ norm (z-k) := by
--     calc _ ≤ norm (z - l₀) := abs_hmrqzl₀ z hz k l₀
--          _ ≤ norm (z-k) := by { sorry
--           --aesop --          }
--   let c₁₁ : ℝ := sorry

--   have abs_denom (z : ℂ)(hz : z ∈ Metric.sphere 0 (m K *(1+ (r/q)))) (k : Fin n) (l₀ : Fin m) :
--     norm (((z - l₀)^(-r : ℤ))* ∏ k ∈ Finset.range (m + 1) \ {(l₀: ℕ)}, ((l₀ - k)/(z-k))^r)
--            ≤ (c₁₁)^r * (q/r)^(m*r) := sorry

--   let c₁₂ : ℝ := sorry

--   have (z : ℂ) (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--           norm (S (l₀, k) z) ≤ (c₁₂)^r*((3-m)/2 + 3 /2) := calc
--           _ = norm ((r.factorial) * (R (l₀, k) z) / ((z - l₀) ^ r) *
--               ∏ k in Finset.range ((r - 1)) \ {(l₀ : ℕ)}, ((l₀ - k) / (z - k)) ^ r) := rfl
--           _ = r.factorial * (norm ((R (l₀, k) z)) * norm ( (1/(z - l₀) ^ r)) *
--             norm (∏ k in Finset.range ((r - 1)) \
--                 {(l₀ : ℕ)}, ((l₀ - k) / (z - k)) ^ r)) := by {
--             simp only [_root_.map_mul]
--             simp only [map_div₀, _root_.map_mul, norm_natCast, map_pow, div_pow,
--               prod_div_distrib, map_prod, one_div, map_inv₀]
--             have : norm (R (l₀, k) z) / norm (z - ↑↑l₀) ^ r=
--              norm (R (l₀, k) z) * (1/  norm (z - ↑↑l₀) ^ r) := by {
--               rw [mul_one_div]
--              }
--             norm_cast at this
--             sorry
--             }
--           _ ≤  r.factorial*((c₁₀)^r*r^((r+3)/2)*(c₁₁)^r*(q/r)^(m*r)) := by {
--             rw [mul_le_mul_left]
--             · sorry
--             · simp only [Nat.cast_pos]
--               exact Nat.factorial_pos r
--           }
--           _ ≤ (c₁₂)^r*((3-m)/2 + 3 /2) := sorry
--   let c₁₃ : ℝ := sorry

--   let hρ (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--     σ (ρ t) = ((2 * Real.pi)⁻¹ * ∮ (z : ℂ) in
--         C(0, m K* (1 + ↑r / ↑q)), (z - ↑l₀)⁻¹ * S  (l₀, k) z) := sorry

--   have eq8 (z : ℂ) (k : Fin n) (l₀ : Fin m) (t : Fin q × Fin q) :
--     norm (σ (ρ t))≤ (c₁₃)^r*r^(r*(3-m)/2 +3/2) := by
--       calc _ = norm ((2 * Real.pi)⁻¹ * ∮ (z : ℂ) in
--         C(0, m K* (1 + ↑r / ↑q)), (z - ↑l₀)⁻¹ * S  (l₀, k) z) := by {rw [hρ k l₀ t]}
--            _≤ norm ((2 * Real.pi)⁻¹) *  norm (∮ (z : ℂ) in
--         C(0, m K* (1 + ↑r / ↑q)),(z - ↑l₀)⁻¹ * S  (l₀, k) z) := by {
--           simp only [_root_.map_mul]
--           simp only [_root_.mul_inv_rev, ofReal_mul, ofReal_inv,
--            ofReal_ofNat, _root_.map_mul, map_inv₀, norm_ofReal, norm_ofNat,
--             le_refl]}
--            _ ≤ norm ((log (α)))^((-r : ℤ))*m K*(1+r/q)*
--         (c₁₂)^r*r^(r*(3-m)/2 +3/2)*q/(m*r) := by sorry
--            _ ≤ (c₁₃)^r*r^(r*(3-m)/2 +3/2)  := by sorry

--   let c₁₄ : ℝ := sorry

--   have use6and8 : (Algebra.norm ℚ ρ) ≤ (c₁₄)^r*r^((-r:ℤ)/2+3*h/2) := calc
--           _ ≤ (c₁₄)^r*r^((h-1)*(r+3/2)+(3-m)*r*1/2 +3/2) := sorry
--           _ = (c₁₄)^r*r^((-r : ℤ)/2+3*h/2) := sorry

--   have final_ineq : r^(r/2 - 3*h/2) ≥ c₁₅^r := sorry
--   exact ⟨r,  hr, final_ineq⟩
--   --sorry
-- include hα hβ
-- theorem hilbert7 : Transcendental ℚ (α ^ β) := fun hγ => by
--   obtain ⟨K, hK, hNK, σ, hd, α', β', γ', ha,hb, hc⟩ := getElemsInNF α β (α^β) hα hβ hγ
--   --have hq0 : 0 < q := sorry
--   rcases (main K α β σ α' β' γ' q) with ⟨r, ⟨hr, hs⟩⟩
--     -- only now you define t
--   have use5 : r^(r/2 - 3*h K/2) < c₁₅^r := calc
--     _ <  c₁₄^r * c₅^r := by sorry
--     _ = c₁₅^r := by {
--       rw [← mul_pow]
--       simp only [c₁₅]}
--   linarith
