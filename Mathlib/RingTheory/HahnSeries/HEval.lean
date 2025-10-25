/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.Summable
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Evaluation of power series in Hahn Series

We describe a class of ring homomorphisms from multivariable formal power series to Hahn series,
given by substitution of the generating variables to elements of strictly positive order.
In the single variable case, we use this homomorphism to characterize invertible Hahn series whose
coefficients are in a commutative domain.

## Main Definitions
 * `HahnSeries.SummableFamily.powerSeriesFamily`: A summable family of Hahn series whose elements
   are non-negative powers of a fixed positive-order Hahn series multiplied by the coefficients of a
   formal power series.
 * `HahnSeries.SummableFamily.mvPowerSeriesFamily` : A summable family made of monomials with
   natural number exponents, where
  the variables are taken from finite set of positive order Hahn series.
 * `PowerSeries.heval` : An `R`-algebra homomorphism from `PowerSeries R` to `HahnSeries Γ R` given
  by sending the generator to a positive-order element.
 * `MvPowerSeries.heval` : An `R`-algebra homomorphism from `MvPowerSeries σ R` to `HahnSeries Γ R`
  for `σ` finite, given by sending each element of `σ` to a positive-order element.

## Main results
  * `mvPowerSeries_family_prod_eq_family_mul` : `hsum` of `heval` of a product is equal to the
    product of `hsum`s of `hevals` for multivariable power series.
  * `isUnit_of_isUnit_leadingCoeff` : A Hahn Series with invertible leading coefficient is
    invertible.
  * `isUnit_iff` : If the coefficient ring is a domain, then any invertible Hahn series has
    invertible leading coefficient.

## TODO
  * Rewrite invertibility in terms of power series evaluation?
## Main results
  * A HahnSeries module structure on summable families.
## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

open Finset Function

noncomputable section

variable {Γ Γ' R V α β σ : Type*}

theorem sum_eq_top [AddCommMonoid Γ] (s : Finset σ) (f : σ → WithTop Γ)
    (h : ∃ i ∈ s, f i = ⊤) : ∑ i ∈ s, f i = ⊤ := by
  induction s using cons_induction with
  | empty => simp_all only [notMem_empty, false_and, exists_false]
  | cons i s his ih =>
    obtain ⟨j, hj⟩ := h
    by_cases hjs : j ∈ s
    · simp only [sum_cons, WithTop.add_eq_top]
      exact Or.inr <| ih <| Exists.intro j ⟨hjs, hj.2⟩
    · classical
      have hij : j = i := eq_of_mem_insert_of_notMem (cons_eq_insert i s his ▸ hj.1) hjs
      rw [sum_cons, ← hij, hj.2, WithTop.add_eq_top]
      exact Or.inl rfl
-- #find_home! sum_eq_top --[Mathlib.Algebra.BigOperators.Group.Finset]

theorem add_ne_top [AddCommMonoid Γ] {x y : WithTop Γ} (hx : x ≠ ⊤)
    (hy : y ≠ ⊤) : x + y ≠ ⊤ := by
  by_contra h
  rw [WithTop.add_eq_top] at h
  simp_all only [ne_eq, or_self]
--#find_home! add_ne_top --[Mathlib.Algebra.Order.Monoid.Unbundled.WithTop]

theorem add_untop [AddCommMonoid Γ] {x y : WithTop Γ} (hx : x ≠ ⊤) (hy : y ≠ ⊤) :
    (x + y).untop (add_ne_top hx hy) = x.untop hx + y.untop hy :=
  (WithTop.untop_eq_iff (add_ne_top hx hy)).mpr (by simp)
--#find_home! add_untop --[Mathlib.Algebra.Order.Monoid.Unbundled.WithTop]

theorem sum_untop [AddCommMonoid Γ] (s : Finset σ) {f : σ → WithTop Γ}
    (h : ∀ i, ¬ f i = ⊤) (hs : ¬∑ i ∈ s, f i = ⊤) :
    (∑ i ∈ s, f i).untop hs = ∑ i ∈ s, ((f i).untop (h i)) := by
  induction s using cons_induction with
  | empty => simp
  | cons i s his ih =>
    simp only [sum_cons]
    rw [sum_cons, WithTop.add_eq_top, not_or] at hs
    rw [add_untop (h i) hs.2]
    exact congrArg (HAdd.hAdd ((f i).untop (h i))) (ih hs.right)
--#find_home! sum_untop --[Mathlib.Algebra.BigOperators.Group.Finset]

namespace HahnSeries

namespace SummableFamily

theorem support_prod_subset_add_support [AddCommMonoid Γ] [PartialOrder Γ] [CommSemiring R]
    [IsOrderedCancelAddMonoid Γ] (σ : Type*) (x : σ →₀ HahnSeries Γ R) (s : Finset σ) :
    haveI : AddCommMonoid (Set Γ) := Set.addCommMonoid
    (∏ i ∈ s, (x i)).support ⊆ ∑ i ∈ s, (x i).support := by
  refine Finset.cons_induction ?_ ?_ s
  · rw [prod_empty, ← single_zero_one]
    exact support_single_subset
  · intros _ _ _ his _ hg
    simp_all only [prod_cons, mem_support, ne_eq, sum_cons]
    exact support_mul_subset_add_support.trans (Set.add_subset_add (fun ⦃a⦄ a ↦ a) his) hg

theorem support_MVpow_subset_closure_support [AddCommMonoid Γ] [PartialOrder Γ] [CommSemiring R]
    [IsOrderedCancelAddMonoid Γ] (σ : Type*) (x : σ →₀ HahnSeries Γ R) (n : σ →₀ ℕ) :
    (∏ i ∈ x.support, (x i) ^ (n i)).support ⊆ AddSubmonoid.closure (⋃ i : σ, (x i).support) := by
  refine Finset.cons_induction ?_ ?_ x.support
  · rw [prod_empty, ← single_zero_one]
    have h₂ : 0 ∈ AddSubmonoid.closure (⋃ i, (x i).support) := by
      exact AddSubmonoid.zero_mem (AddSubmonoid.closure (⋃ i, (x i).support))
    intro g hg
    simp_all
  · intro i _ _ hx
    rw [prod_cons]
    have hi : (x i ^ n i).support ⊆ AddSubmonoid.closure (⋃ i, (x i).support) :=
      (support_pow_subset_closure (x i) (n i)).trans <| AddSubmonoid.closure_mono <|
        Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
    exact (support_mul_subset_add_support (x := x i ^ n i)).trans (AddSubmonoid.add_subset hi hx)

theorem support_MVpow_subset_closure [AddCommMonoid Γ] [PartialOrder Γ] [CommSemiring R]
    [IsOrderedCancelAddMonoid Γ] {σ : Type*} (s : Finset σ) (x : σ →₀ HahnSeries Γ R) (n : σ →₀ ℕ) :
    (∏ i ∈ s, (x i) ^ (n i)).support ⊆ AddSubmonoid.closure (⋃ i : σ, (x i).support) := by
  refine Finset.cons_induction ?_ ?_ s
  · rw [prod_empty, ← single_zero_one]
    have h₂ : 0 ∈ AddSubmonoid.closure (⋃ i, (x i).support) := by
      exact AddSubmonoid.zero_mem (AddSubmonoid.closure (⋃ i, (x i).support))
    intro g hg
    simp_all
  · intro i _ _ hx
    rw [prod_cons]
    have hi : (x i ^ n i).support ⊆ AddSubmonoid.closure (⋃ i, (x i).support) :=
      (support_pow_subset_closure (x i) (n i)).trans <| AddSubmonoid.closure_mono <|
        Set.subset_iUnion_of_subset i fun ⦃a⦄ a ↦ a
    exact (support_mul_subset_add_support (x := x i ^ n i)).trans (AddSubmonoid.add_subset hi hx)

theorem isPWO_iUnion_support_MVpow_support [LinearOrder Γ] [AddCommMonoid Γ] [CommSemiring R]
    [IsOrderedCancelAddMonoid Γ] (σ : Type*) (x : σ →₀ HahnSeries Γ R)
    (hx : ∀ i : σ, 0 ≤ (x i).order) :
    (⋃ n : σ →₀ ℕ, (∏ i ∈ x.support, (x i) ^ (n i)).support).IsPWO := by
  refine Set.IsPWO.mono (Set.IsPWO.addSubmonoid_closure ?_ ?_)
    (Set.iUnion_subset fun n => support_MVpow_subset_closure x.support x n)
  · intro g hg
    simp only [Set.mem_iUnion, mem_support, ne_eq] at hg
    obtain ⟨i, hi⟩ := hg
    exact (hx i).trans (order_le_of_coeff_ne_zero hi)
  · have h : ⋃ i, (x i).support =
        (⋃ i ∈ x.support, (x i).support) ∪ (⋃ i ∉ x.support, (x i).support) := by
      classical
      simp_rw [← Set.iUnion_ite, ite_id (x _).support]
    rw [h, Set.isPWO_union]
    constructor
    · exact (isPWO_bUnion x.support).mpr fun i _ ↦ isPWO_support (x i)
    · rw [show (⋃ i, ⋃ (_ : i ∉ x.support), (x i).support) = ∅ by simp_all]
      exact Set.isPWO_empty

theorem isPWO_iUnion_support_MVpow [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ]
    [CommSemiring R] {σ : Type*} [Fintype σ] (x : σ →₀ HahnSeries Γ R)
    (hx : ∀ i : σ, 0 ≤ (x i).order) :
    (⋃ n : σ →₀ ℕ, (∏ i, (x i) ^ (n i)).support).IsPWO := by
  refine Set.IsPWO.mono ?_ (Set.iUnion_subset fun n => support_MVpow_subset_closure Finset.univ x n)
  refine Set.IsPWO.addSubmonoid_closure ?_ ?_
  · intro g hg
    simp only [Set.mem_iUnion, mem_support, ne_eq] at hg
    obtain ⟨i, hi⟩ := hg
    exact (hx i).trans (order_le_of_coeff_ne_zero hi)
  · rw [show ⋃ i, (x i).support = ⋃ i ∈ univ, (x i).support by simp]
    exact (isPWO_bUnion univ).mpr fun i _ => isPWO_support (x i)

section PowerSeriesFamily

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R]

omit [IsOrderedCancelAddMonoid Γ] in
lemma supp_eq_univ_of_pos (σ : Type*) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : y.support = Set.univ (α := σ) := by
  have hy₁ : ∀ i : σ, y i ≠ 0 := fun i => ne_zero_of_order_ne (ne_of_gt (hy i))
  exact Set.eq_univ_of_univ_subset fun i _ => by simp_all

/-- A finsupp whose every element has positive order has fintype source. -/
def Fintype_of_pos_order (σ : Type*) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : Fintype σ := by
  refine Set.fintypeOfFiniteUniv ?_
  rw [← supp_eq_univ_of_pos σ y hy]
  exact finite_toSet y.support

omit [IsOrderedCancelAddMonoid Γ] in
lemma supp_eq_univ_of_pos_fintype (σ : Type*) [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : y.support = Finset.univ (α := σ) :=
  eq_univ_of_forall fun i => Finsupp.mem_support_iff.mpr (ne_zero_of_order_ne (ne_of_gt (hy i)))

variable [CommRing V] [Algebra R V]
--

/-- A summable family of Hahn series whose elements are scalar multiples of non-negative powers of a
fixed Hahn series. The scalar multiples are given by the coefficients of a power series. If the Hahn
series has nonpositive order, then we use the junk value zero instead of the Hahn series. -/
abbrev powerSeriesFamily (x : HahnSeries Γ V) (f : PowerSeries R) : SummableFamily Γ V ℕ :=
  smulFamily (fun n => f.coeff n) (powers x)

@[simp]
theorem powerSeriesFamily_of_not_orderTop_pos {x : HahnSeries Γ V} (hx : ¬ 0 < x.orderTop)
    (f : PowerSeries R) :
    powerSeriesFamily x f = powerSeriesFamily 0 f := by
  ext n g
  obtain rfl | hn := eq_or_ne n 0 <;> simp [*]

theorem powerSeriesFamily_of_orderTop_pos {x : HahnSeries Γ V} (hx : 0 < x.orderTop)
    (f : PowerSeries R) (n : ℕ) :
    powerSeriesFamily x f n = f.coeff n • x ^ n := by
  simp [hx]

@[simp]
theorem powerSeriesFamily_hsum_zero (f : PowerSeries R) :
    (powerSeriesFamily 0 f).hsum = f.constantCoeff • (1 : HahnSeries Γ V) := by
  ext g
  by_cases hg : g = 0
  · simp only [hg, coeff_hsum]
    rw [finsum_eq_single _ 0 (fun n hn ↦ by simp [hn])]
    simp
  · rw [coeff_hsum, finsum_eq_zero_of_forall_eq_zero
      fun n ↦ (by by_cases hn : n = 0 <;> simp [hg, hn])]
    simp [hg]

theorem powerSeriesFamily_add {x : HahnSeries Γ V} (f g : PowerSeries R) :
    powerSeriesFamily x (f + g) = powerSeriesFamily x f + powerSeriesFamily x g := by
  ext1 n
  by_cases hx : 0 < x.orderTop <;> · simp [hx, add_smul]

theorem powerSeriesFamily_smul {x : HahnSeries Γ V} (f : PowerSeries R) (r : R) :
    powerSeriesFamily x (r • f) = HahnSeries.single (0 : Γ) r • powerSeriesFamily x f := by
  ext1 n
  simp [mul_smul]

theorem support_powerSeriesFamily_subset {x : HahnSeries Γ V} (a b : PowerSeries R) (g : Γ) :
    ((powerSeriesFamily x (a * b)).coeff g).support ⊆
    (((powerSeriesFamily x a).mul (powerSeriesFamily x b)).coeff g).support.image
      fun i => i.1 + i.2 := by
  by_cases h : 0 < x.orderTop
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    have he : ∃ c ∈ antidiagonal n, (PowerSeries.coeff c.1) a • (PowerSeries.coeff c.2) b •
        ((powers x) n).coeff g ≠ 0 := by
      refine exists_ne_zero_of_sum_ne_zero ?_
      simpa [PowerSeries.coeff_mul, sum_smul, mul_smul, h] using hn
    simp only [powers_of_orderTop_pos h, mem_antidiagonal] at he
    obtain ⟨c, hcn, hc⟩ := he
    simp only [coe_image, Set.Finite.coe_toFinset, Set.mem_image]
    use c
    simp only [mul_toFun, smulFamily_toFun, Function.mem_support, hcn,
      and_true]
    rw [powers_of_orderTop_pos h c.1, powers_of_orderTop_pos h c.2, Algebra.smul_mul_assoc,
      Algebra.mul_smul_comm, ← pow_add, hcn]
    simp [hc]
  · simp only [coeff_support, Set.Finite.toFinset_subset, support_subset_iff]
    intro n hn
    by_cases hz : n = 0
    · have : g = 0 ∧ (a.constantCoeff * b.constantCoeff) • (1 : V) ≠ 0 := by
        simpa [hz, h] using hn
      simp only [coe_image, Set.mem_image]
      use (0, 0)
      simp [this.2, this.1, h, hz, smul_smul, mul_comm]
    · simp [h, hz] at hn

theorem powerSeriesFamily_ext (x : HahnSeries Γ V) (f g : PowerSeries R) :
    powerSeriesFamily x f = powerSeriesFamily x g ↔
      ∀ n, powerSeriesFamily x f n = powerSeriesFamily x g n :=
  SummableFamily.ext_iff

omit [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] in
theorem coeff_sum {α} (s : Finset α) (f : α → HahnSeries Γ R) (g : Γ) :
    (Finset.sum s f).coeff g = Finset.sum s (fun i => (f i).coeff g) :=
  cons_induction_on s (by simp) fun i t hit hc => by rw [sum_cons, sum_cons, coeff_add, hc]

theorem finsum_prod {R} [AddCommMonoid R] (f : ℕ × ℕ →₀ R) :
    ∑ᶠ (i : ℕ), ∑ᶠ (j : ℕ),  f (i, j) = ∑ᶠ (i : ℕ × ℕ), f i :=
  Eq.symm (finsum_curry (fun ab ↦ f ab) (Finsupp.finite_support f))

theorem finsum_antidiagonal_prod [AddCommMonoid α] [HasAntidiagonal α] (f : α × α →₀ R) :
    ∑ᶠ (i : α), (∑ j ∈ antidiagonal i, f j) =
    ∑ᶠ (i : α × α), f i := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s := f.support) (fun i _ => by simp_all),
    finsum_eq_sum_of_support_subset _ (s := (f.support.image fun i => i.1 + i.2)) ?_, sum_sigma']
  · refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) ?_ ?_ ?_ ?_).symm
    · exact fun x _ y _ hxy => by simp_all
    · intro x hx
      simp_all only [mem_coe, Finsupp.mem_support_iff, ne_eq, coe_sigma, coe_image,
        Set.mem_sigma_iff, Set.mem_image, Prod.exists, mem_antidiagonal, and_true]
      use x.1, x.2
    · intro x hx h
      simp_all only [mem_sigma, mem_image, Finsupp.mem_support_iff, ne_eq, Prod.exists,
        mem_antidiagonal, Set.mem_image, mem_coe, not_exists, not_and]
      have h0 : ∀ i j : α, ⟨i + j, (i, j)⟩ = x → f (i, j) = 0 := by
        intro i j
        contrapose!
        exact h i j
      refine h0 x.snd.1 x.snd.2 ?_
      simp_all only [Prod.mk.eta, Sigma.eta]
    · exact fun x _ => rfl
  · intro x hx
    simp_all only [Function.mem_support, ne_eq, coe_image, Set.mem_image, mem_coe,
      Finsupp.mem_support_iff, Prod.exists]
    have h1 := exists_ne_zero_of_sum_ne_zero hx
    use h1.choose.1, h1.choose.2
    refine ⟨h1.choose_spec.2, ?_⟩
    · rw [← @mem_antidiagonal]
      exact h1.choose_spec.1

--#find_home! finsum_antidiagonal_prod --[Mathlib.RingTheory.Adjoin.Basic]
theorem hsum_powerSeriesFamily_mul {x : HahnSeries Γ V} (a b : PowerSeries R) :
    (powerSeriesFamily x (a * b)).hsum =
    ((powerSeriesFamily x a).mul (powerSeriesFamily x b)).hsum := by
  by_cases h : 0 < x.orderTop;
  · ext g
    simp only [coeff_hsum_eq_sum, smulFamily_toFun, h, powers_of_orderTop_pos,
      HahnSeries.coeff_smul, mul_toFun, Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
    rw [sum_subset (support_powerSeriesFamily_subset a b g)
      (fun i hi his ↦ by simpa [h, PowerSeries.coeff_mul, sum_smul] using his)]
    simp only [coeff_support, mul_toFun, smulFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, HahnSeries.coeff_smul, PowerSeries.coeff_mul, sum_smul]
    rw [sum_sigma']
    refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) (fun _ _ _ _ => by simp) ?_ ?_
      (fun _ _ => by simp [smul_smul, mul_comm, pow_add])).symm
    · intro ij hij
      simp only [coe_sigma, coe_image, Set.mem_sigma_iff, Set.mem_image, Prod.exists, mem_coe,
        mem_antidiagonal, and_true]
      use ij.1, ij.2
      simp_all
    · intro i hi his
      have hisc : ∀ j k : ℕ, ⟨j + k, (j, k)⟩ = i → (PowerSeries.coeff k) b •
          (PowerSeries.coeff j a • (x ^ j * x ^ k).coeff g) = 0 := by
        intro m n
        contrapose!
        simp only [powers_of_orderTop_pos h, Set.Finite.coe_toFinset, Set.mem_image,
          Function.mem_support, ne_eq, Prod.exists, not_exists, not_and] at his
        exact his m n
      simp only [mem_sigma, mem_antidiagonal] at hi
      rw [mul_comm ((PowerSeries.coeff i.snd.1) a), ← hi.2, mul_smul, pow_add]
      exact hisc i.snd.1 i.snd.2 <| Sigma.eq hi.2 (by simp)
  · simp only [h, not_false_eq_true, powerSeriesFamily_of_not_orderTop_pos,
      powerSeriesFamily_hsum_zero, map_mul, hsum_mul]
    rw [smul_mul_smul_comm, mul_one]

end PowerSeriesFamily

section MVpowers

variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R] [CommRing V]
[Algebra R V] {x : HahnSeries Γ V} (hx : 0 < x.orderTop)

-- use Finsupp.sumFinsuppAddEquivProdFinsupp and maybe Finsupp.lsingle
-- see also Finsupp.restrictSupportEquiv

/-- An equiv between finsupp and maps from a finset. -/
def equiv_map_on_finset_finsupp (s : Finset σ) :
    ((i : σ) → i ∈ s → ℕ) ≃ ({i // i ∈ s} →₀ ℕ) where
  toFun f := Finsupp.equivFunOnFinite.symm (fun i => f i.1 i.2)
  invFun f := fun i hi => (Finsupp.equivFunOnFinite f) ⟨i, hi⟩
  left_inv := congrFun rfl
  right_inv f := by simp

/-- The equivalence between maps on a finite totality and finitely supported functions. -/
def equiv_map_on_fintype_finsupp [Fintype σ] :
    ((i : σ) → i ∈ Finset.univ → ℕ) ≃ (σ →₀ ℕ) where
  toFun f := Finsupp.equivFunOnFinite.symm (fun i => f i (mem_univ i))
  invFun f := fun i _ => (Finsupp.equivFunOnFinite f) i
  left_inv f := by simp
  right_inv f := by simp

/-- A multivariable family given by all possible unit-coefficient monomials -/
def mvPowers [Fintype σ] (y : σ →₀ HahnSeries Γ V) :
    SummableFamily Γ V (σ →₀ ℕ) :=
  Equiv equiv_map_on_fintype_finsupp (PiFamily Finset.univ (fun _ => ℕ)
    (fun i => powers (y i)))

@[simp]
theorem mvPowers_apply {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (n : σ →₀ ℕ) :
    (mvPowers y) n = ∏ i, y i ^ n i := by
  simp [mvPowers, equiv_map_on_fintype_finsupp, hy]

open Classical in
theorem mvpow_finite_co_support {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (g : Γ) :
    {a : (σ →₀ ℕ) | (∏ i, y i ^ a i).coeff g ≠ 0}.Finite := by
  have h : ∀ a : (σ →₀ ℕ), (∏ i : σ, y i ^ a i) = ∏ x : σ,
      if _ : x ∈ univ then y x ^ a x else 1 :=
    fun a => by simp
  suffices {a : ((i : σ) → i ∈ univ → ℕ) | ((fun b => ∏ x : σ,
      if h : x ∈ univ then y x ^ b x h else 1) a).coeff g ≠ 0}.Finite from by
    simp_rw [h]
    refine Set.Finite.of_surjOn (fun a => Finsupp.onFinset univ (fun i => a i (mem_univ i))
      (fun i _ ↦ mem_univ i)) (fun a ha => ?_) this
    simp_all only [dite_eq_ite, ite_true, implies_true, dite_true, mem_univ, ne_eq,
      Set.mem_setOf_eq, Set.mem_image]
    use fun i _ => a i
    exact ⟨ha, by ext; simp⟩
  exact pi_finite_co_support Finset.univ _ g (fun i => isPWO_iUnion_support_powers
    (zero_le_orderTop_iff.mp <| le_of_lt (hy i)))
    (fun i g => by simp only [pow_finite_co_support (hy i) g])

/-- A summable family given by substituting a multivariable power series into positive order
elements. -/
abbrev mvPowerSeriesFamily [Fintype σ] (y : σ →₀ HahnSeries Γ V)
    (f : MvPowerSeries σ R) :
    SummableFamily Γ V (σ →₀ ℕ) :=
  smulFamily (fun n => MvPowerSeries.coeff n f) (mvPowers y)

theorem mvPowerSeriesFamily_toFun [Fintype σ] (y : σ →₀ HahnSeries Γ V)
    (hy : ∀ i, 0 < (y i).orderTop) (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    mvPowerSeriesFamily y f n =
      (MvPowerSeries.coeff n f) • ∏ i, (y i) ^ (n i) := by
  simp [hy]

theorem mvPowerSeriesFamilyAdd [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (f g : MvPowerSeries σ R) :
    mvPowerSeriesFamily y (f + g) = mvPowerSeriesFamily y f + mvPowerSeriesFamily y g := by
  ext1 n
  simp [add_smul]

theorem mvPowerSeriesFamilySMul [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (r : R) (f : MvPowerSeries σ R) :
    mvPowerSeriesFamily y (r • f) =
      (HahnSeries.single (0 : Γ) r) • (mvPowerSeriesFamily y f) := by
  ext1 n
  simp only [smulFamily_toFun, map_smul, smul_eq_mul, mvPowers, equiv_map_on_fintype_finsupp,
      Finsupp.equivFunOnFinite_apply, Equiv_toFun, Equiv.coe_fn_symm_mk, PiFamily_toFun, mem_univ,
      ↓reduceDIte, powers_toFun, smul_apply, HahnModule.of_smul,
      Algebra.mul_smul_comm, single_zero_mul_eq_smul]
  rw [mul_comm, Equiv.eq_symm_apply, HahnModule.of_smul, mul_smul]

/-!
open Classical in
theorem mvPowerSeriesFamily_supp_subset {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (a b : MvPowerSeries σ R) (g : Γ) :
    ((mvPowerSeriesFamily y hy (a * b)).coeff g).support ⊆
    (((mvPowerSeriesFamily y hy a).mul (mvPowerSeriesFamily y hy b)).coeff g).support.image
      fun i => i.1 + i.2 := by
  simp_all only [coeff_support, mvPowerSeriesFamily_toFun, coeff_smul, smul_eq_mul, mul_toFun,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Set.Finite.toFinset_subset, coe_image,
    Set.Finite.coe_toFinset, support_subset_iff, ne_eq, Set.mem_image, Function.mem_support,
    Prod.exists]
  intro n hn
  simp_rw [MvPowerSeries.coeff_mul, ← ne_eq, sum_smul, mul_smul] at hn
  have he : ∃p ∈ antidiagonal n, ¬((MvPowerSeries.coeff R p.1) a •
      (MvPowerSeries.coeff R p.2) b • ((mvPowers y hy) n).coeff g) = 0 :=
    exists_ne_zero_of_sum_ne_zero hn
  use he.choose.1, he.choose.2
  refine ⟨?_, mem_antidiagonal.mp he.choose_spec.1⟩
  rw [← mul_assoc, mul_comm ((MvPowerSeries.coeff R he.choose.2) b)]
  simp_rw [mvPowers_apply, ← prod_mul_distrib, ← pow_add]
  convert he.choose_spec.2
  · exact Eq.symm (mvPowers_apply y hy n)
  · exact Eq.symm (mvPowers_apply y hy n)
  · simp [mvPowers, equiv_map_on_fintype_finsupp]
    congr 1
    funext i
    have h : he.choose.1 i + he.choose.2 i = n i := by
      rw [← Finsupp.add_apply, mem_antidiagonal.mp he.choose_spec.1]
    congr
    convert h
    · exact Iff.symm mem_antidiagonal
    · exact Eq.symm (mvPowers_apply y hy n)
    · exact Iff.symm mem_antidiagonal
    · exact Eq.symm (mvPowers_apply y hy n)

theorem prod_mul {σ M : Type*} [Fintype σ] [CommMonoid M] (i : (σ →₀ ℕ) × (σ →₀ ℕ)) (y : σ → M) :
    (∏ i_1 : σ, y i_1 ^ i.1 i_1) * ∏ i_1 : σ, y i_1 ^ i.2 i_1 = ∏ x : σ, y x ^ (i.1 + i.2) x := by
  rw [← prod_mul_distrib, prod_congr rfl]
  intro _ _
  rw [Finsupp.add_apply, pow_add]

theorem mvPowerSeries_family_prod_eq_family_mul {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (a b : MvPowerSeries σ R) :
    (mvPowerSeriesFamily y hy (a * b)).hsum =
    ((mvPowerSeriesFamily y hy a).mul (mvPowerSeriesFamily y hy b)).hsum := by
  ext g
  classical
  simp only [mvPowerSeriesFamily_toFun, MvPowerSeries.coeff_mul, Finset.sum_smul,
    ← Finset.sum_product, coeff_hsum_eq_sum, mul_toFun, mvPowers_apply]
  rw [sum_subset (mvPowerSeriesFamily_supp_subset y hy a b g)]
  · rw [← HahnSeries.sum_coeff, sum_sigma', sum_coeff]
    refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) ?_ ?_ ?_ ?_).symm
    · intro ij _ kl _
      simp_all
    · intro ij hij
      simp_all only [coeff_support, mul_toFun, mvPowerSeriesFamily_toFun, mvPowers_apply,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc, coeff_smul, smul_eq_mul,
        Set.Finite.coe_toFinset, Function.mem_support, ne_eq, coe_sigma, coe_image,
        Set.mem_sigma_iff, Set.mem_image, Prod.exists, mem_coe, mem_antidiagonal, and_true]
      use ij.1, ij.2
    · intro i hi his
      simp_all only [coeff_support, mul_toFun, mvPowerSeriesFamily_toFun, mvPowers_apply,
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc, coeff_smul, smul_eq_mul, mem_sigma,
        mem_image, Set.Finite.mem_toFinset, Function.mem_support, ne_eq, Prod.exists,
        mem_antidiagonal, Set.Finite.coe_toFinset, Set.mem_image, not_exists, not_and]
      have hisc : ∀ j k : σ →₀ ℕ, ⟨j + k, (j, k)⟩ = i → (MvPowerSeries.coeff R k) b *
          ((MvPowerSeries.coeff R j) a * ((∏ p, y p ^ j p) * (∏ q, y q ^ k q)).coeff g) = 0 := by
        intro m n
        contrapose!
        exact his m n
      rw [mul_comm ((MvPowerSeries.coeff R i.snd.1) a), ← hi.2, mul_assoc]
      have hp : ∀ j k : σ →₀ ℕ, ∏ i_1 : σ, y i_1 ^ (j + k) i_1 =
          (∏ i' : σ, y i' ^ j i') * ∏ j' : σ, y j' ^ k j' := by
        intro j k
        rw [prod_mul (j, k)]
      rw [hp]
      exact hisc i.snd.1 i.snd.2 <| Sigma.eq hi.2 (by simp)
    · intro i _
      simp only
      rw [smul_mul_smul_comm]
      congr 2
      exact prod_mul i y
  · intro i hi his
    simp_all only [coeff_support, mul_toFun, mvPowerSeriesFamily_toFun, mvPowers_apply,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, coeff_smul, smul_eq_mul, mem_image,
      Set.Finite.mem_toFinset, Function.mem_support, ne_eq, Prod.exists, Decidable.not_not,
      HahnSeries.sum_coeff]
    rw [MvPowerSeries.coeff_mul, sum_mul] at his
    exact his
-/

end MVpowers

end SummableFamily

end HahnSeries

namespace PowerSeries

open HahnSeries SummableFamily

variable [AddCommMonoid Γ] [LinearOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommRing R] (x : HahnSeries Γ R)

/-- The `R`-algebra homomorphism from `R[[X]]` to `HahnSeries Γ R` given by sending the power series
variable `X` to a positive order element `x` and extending to infinite sums. -/
@[simps]
def heval : PowerSeries R →ₐ[R] HahnSeries Γ R where
  toFun f := (powerSeriesFamily x f).hsum
  map_one' := by
    simp only [hsum, smulFamily_toFun, coeff_one, powers_toFun, ite_smul, one_smul,
      zero_smul]
    ext g
    simp only
    rw [finsum_eq_single _ (0 : ℕ) (fun n hn => by simp_all)]
    simp
  map_mul' a b := by
    simp only [← hsum_mul, hsum_powerSeriesFamily_mul]
  map_zero' := by
    simp only [hsum, smulFamily_toFun, map_zero, powers_toFun, zero_smul,
      coeff_zero, finsum_zero, mk_eq_zero, Pi.zero_def]
  map_add' a b := by
    simp only [powerSeriesFamily_add, hsum_add]
  commutes' r := by
    simp only [algebraMap_eq]
    ext g
    simp only [coeff_hsum, smulFamily_toFun, coeff_C, ite_smul, zero_smul]
    rw [finsum_eq_single _ 0 fun n hn => by simp [hn]]
    by_cases hg : g = 0 <;> simp [powers_toFun, hg, Algebra.algebraMap_eq_smul_one]

theorem heval_of_orderTop_not_pos (hx : ¬ 0 < x.orderTop) (a : PowerSeries R) :
    heval x a = constantCoeff a • 1 := by
  simp [powerSeriesFamily_of_not_orderTop_pos hx]

theorem heval_mul {a b : PowerSeries R} : heval x (a * b) = heval x a * heval x b :=
  map_mul (heval x) a b

theorem heval_C (r : R) : heval x (C r) = r • 1 := by
  ext g
  simp only [heval_apply, coeff_hsum, smulFamily_toFun, powers_toFun, HahnSeries.coeff_smul,
    HahnSeries.coeff_one, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [finsum_eq_single _ 0 (fun n hn ↦ by simp [coeff_ne_zero_C hn])]
  by_cases hg : g = 0 <;> · simp

theorem heval_X (hx : 0 < x.orderTop) : heval x X = x := by
  rw [X_eq, monomial_eq_mk, heval_apply, powerSeriesFamily, smulFamily]
  simp only [coeff_mk, powers_toFun, hx, ↓reduceIte, ite_smul, one_smul, zero_smul]
  ext g
  rw [coeff_hsum, finsum_eq_single _ 1 (fun n hn ↦ by simp [hn])]
  simp

theorem heval_unit (u : (PowerSeries R)ˣ) : IsUnit (heval x u) := by
  refine isUnit_iff_exists_inv.mpr ?_
  use heval x u.inv
  rw [← heval_mul, Units.val_inv, map_one]

theorem coeff_heval (f : PowerSeries R) (g : Γ) :
    (heval x f).coeff g = ∑ᶠ n, ((powerSeriesFamily x f).coeff g) n := by
  rw [heval_apply, coeff_hsum]
  exact rfl

theorem coeff_heval_zero (f : PowerSeries R) :
    (heval x f).coeff 0 = PowerSeries.constantCoeff f := by
  rw [coeff_heval, finsum_eq_single (fun n => ((powerSeriesFamily x f).coeff 0) n) 0,
    ← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp [powers_toFun]
  · intro n hn
    simp only [coeff_toFun, smulFamily_toFun, HahnSeries.coeff_smul, smul_eq_mul]
    refine mul_eq_zero_of_right (coeff n f) (coeff_eq_zero_of_lt_orderTop ?_)
    by_cases h : 0 < x.orderTop
    · refine (lt_of_lt_of_le ((nsmul_pos_iff hn).mpr h) ?_)
      simp [h, orderTop_nsmul_le_orderTop_pow]
    · simp [h, hn]

end PowerSeries

namespace MvPowerSeries

open HahnSeries SummableFamily

variable [LinearOrder Γ] [AddCommMonoid Γ] [IsOrderedCancelAddMonoid Γ] [CommRing R] {σ : Type*}
[Fintype σ] (y : σ →₀ HahnSeries Γ R) (hy : ∀ i, 0 < (y i).orderTop)
/-!
/-- The `R`-algebra homomorphism from `R[[X₁,…,Xₙ]]` to `HahnSeries Γ R` given by sending each power
series variable `Xᵢ` to a positive order element. -/
@[simps]
def heval {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R) :
    MvPowerSeries σ R →ₐ[R] HahnSeries Γ R where
  toFun f := (mvPowerSeriesFamily y f).hsum
  map_one' := by
    classical
    simp only [hsum, mvPowerSeriesFamily_toFun, MvPowerSeries.coeff_one, ite_smul, one_smul,
      zero_smul, mvPowers_apply]
    ext g
    simp_rw [finsum_eq_single (fun i =>
      (if i = 0 then ∏ i_1 : σ, (if 0 < (y i_1).orderTop then y i_1 else 0) ^ i i_1 else 0).coeff g)
      (0 : σ →₀ ℕ) (fun n hn => by simp_all)]
    rw [if_true, Fintype.prod_eq_one (fun i_1 ↦
      (if 0 < (y i_1).orderTop then y i_1 else 0) ^ (0 : σ →₀ ℕ) i_1) (congrFun rfl)]
  map_mul' a b := by
    simp only [← hsum_family_mul]
    exact mvPowerSeries_family_prod_eq_family_mul y hy a b
  map_zero' := by
    simp only [hsum, mvPowerSeriesFamily_toFun, map_zero, mvPowers_apply, zero_smul, coeff_zero,
      finsum_zero, mk_eq_zero, Pi.zero_def]
  map_add' a b := by
    ext g
    simp only [coeff_hsum, map_add, mvPowers_apply, coeff_smul,
      smul_eq_mul, add_mul, coeff_add', Pi.add_apply]
    rw [← finsum_add_distrib (finite_co_support (mvPowerSeriesFamily y a) g)
      (finite_co_support (mvPowerSeriesFamily y b) g)]
    exact finsum_congr fun s => by rw [mvPowerSeriesFamilyAdd, add_apply, coeff_add]
  commutes' r := by
    simp only [MvPowerSeries.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply,
      algebraMap_apply, C_apply]
    ext g
    classical
    simp only [coeff_hsum, mvPowerSeriesFamily_toFun, mvPowers_apply, coeff_smul, smul_eq_mul]
    rw [finsum_eq_single _ 0 (fun s hs => by simp [hs, MvPowerSeries.coeff_C])]
    by_cases hg : g = 0 <;> simp [hg, Algebra.algebraMap_eq_smul_one']

theorem heval_mul {a b : MvPowerSeries σ R} :
    heval y (a * b) = (heval y a) * heval y b :=
  map_mul (heval y) a b

theorem heval_unit (u : (MvPowerSeries σ R)ˣ) : IsUnit (heval y u) := by
  refine isUnit_iff_exists_inv.mpr ?_
  use heval y hy u.inv
  rw [← heval_mul, Units.val_inv, map_one]

theorem heval_coeff (f : MvPowerSeries σ R) (g : Γ) :
    (heval y f).coeff g = ∑ᶠ n, ((mvPowerSeriesFamily y f).coeff g) n := by
  rw [heval_apply, coeff_hsum]
  exact rfl

theorem heval_coeff_zero (f : MvPowerSeries σ R) :
    (heval y f).coeff 0 = MvPowerSeries.constantCoeff σ R f := by
  rw [heval_coeff, finsum_eq_single (fun n => ((mvPowerSeriesFamily y f).coeff 0) n) 0,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp_all
  · intro n hn
    simp_all only [ne_eq, coeff_toFun, mvPowerSeriesFamily_toFun, mvPowers_apply, coeff_smul,
      smul_eq_mul]
    refine mul_eq_zero_of_right ((MvPowerSeries.coeff R n) f) (coeff_eq_zero_of_lt_orderTop ?_)
    refine lt_of_lt_of_le ?_ (sum_orderTop_le_orderTop_prod _)
    by_cases h : ∑ i, (y i ^ n i).orderTop = ⊤
    · simp [h]
    · have hi : ∀ i, ¬(y i ^ n i).orderTop = ⊤ := by
        intro i
        contrapose h
        simp_all only [Decidable.not_not]
        exact sum_eq_top univ _ <| Exists.intro i ⟨mem_univ i, h⟩
      refine (WithTop.lt_untop_iff h).mp ?_
      rw [sum_untop univ hi h]
      rw [Finsupp.ext_iff, Mathlib.Tactic.PushNeg.not_forall_eq] at hn
      simp only [Finsupp.coe_zero, Pi.zero_apply] at hn
      refine sum_pos' ?_ ?_
      · intro i _
        by_cases hni : n i = 0
        · rw [WithTop.le_untop_iff, hni, pow_zero]
          by_cases hz : (1 : HahnSeries Γ R) = 0
          · simp [hz]
          · rw [WithTop.coe_zero, zero_le_orderTop_iff, order_one]
        · rw [WithTop.le_untop_iff]
          refine LE.le.trans ?_ orderTop_nsmul_le_orderTop_pow
          rw [WithTop.coe_zero]
          exact nsmul_nonneg (le_of_lt (hy i)) (n i)
      · obtain ⟨i, hni⟩ := hn
        use i
        constructor
        · exact mem_univ i
        · rw [WithTop.lt_untop_iff]
          refine lt_of_lt_of_le ?_ orderTop_nsmul_le_orderTop_pow
          rw [WithTop.coe_zero]
          exact (nsmul_pos_iff hni).mpr (hy i)

-/
end MvPowerSeries
