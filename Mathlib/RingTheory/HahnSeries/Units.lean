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
  * `powers` : A summable family made of natural number powers of a positive order Hahn series.
  * `PowerSeriesFamily` : A variant of `powers` where powers are multiplied by coefficients of a
  formal power series.
  * `mvPowerSeriesFamily` : A summable family made of monomials with natural number exponents, where
  the variables are taken from finite set of positive order Hahn series.
  * `PowerSeries.heval` : An `R`-algebra homomorphism from `PowerSeries R` to `HahnSeries Γ R` given
  by sending the generator to a positive-order element.
  * `MvPowerSeries.heval` : An `R`-algebra homomorphism from `MvPowerSeries σ R` to `HahnSeries Γ R`
  for `σ` finite, given by sending each element of `σ` to a positive-order element.

## Main results
  * If `R` is a commutative domain, and `Γ` is a linearly ordered additive commutative group, then
  a Hahn series is a unit if and only if its leading term is a unit in `R`.

## TODO
  * Rewrite invertibility in terms of power series evaluation.

## Main results

  * `isUnit_of_isUnit_leadingCoeff` : A Hahn Series with invertible leading coefficient is
    invertible.
  * `isUnit_iff` : If the coefficient ring is a domain, then any invertible Hahn series has
    invertible leading coefficient.
  * A HahnSeries module structure on summable families.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

open Finset Function

open Pointwise

noncomputable section

variable {Γ Γ' R V α β σ : Type*}

theorem sum_eq_top [AddCommMonoid Γ] (s : Finset σ) (f : σ → WithTop Γ)
    (h : ∃i ∈ s, f i = ⊤) : ∑ i ∈ s, f i = ⊤ := by
  induction s using cons_induction with
  | empty => simp_all only [not_mem_empty, false_and, exists_false]
  | cons i s his ih =>
    obtain ⟨j, hj⟩ := h
    by_cases hjs : j ∈ s
    · simp only [sum_cons, WithTop.add_eq_top]
      exact Or.inr <| ih <| Exists.intro j ⟨hjs, hj.2⟩
    · classical
      have hij : j = i := eq_of_mem_insert_of_not_mem (cons_eq_insert i s his ▸ hj.1) hjs
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
    rw [sum_cons, WithTop.add_eq_top, Mathlib.Tactic.PushNeg.not_or_eq] at hs
    rw [add_untop (h i) hs.2]
    exact congrArg (HAdd.hAdd ((f i).untop (h i))) (ih hs.right)
--#find_home! sum_untop --[Mathlib.Algebra.BigOperators.Group.Finset]

namespace HahnSeries

namespace SummableFamily

section PowerSeriesFamily

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R]

variable {x : HahnSeries Γ R}

theorem smul_pow_finite_co_support (hx : 0 < x.orderTop) (f : ℕ → R) (g : Γ) :
    Set.Finite {a | ((fun n ↦ f n • x ^ n) a).coeff g ≠ 0} :=
  Set.Finite.subset (pow_finite_co_support hx g) fun n hn hng => (by simp_all)

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

lemma supp_eq_univ_of_pos_fintype (σ : Type*) [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : y.support = Finset.univ (α := σ) :=
  eq_univ_of_forall fun i => Finsupp.mem_support_iff.mpr (ne_zero_of_order_ne (ne_of_gt (hy i)))

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
    (zero_le_orderTop_iff.mp (le_of_lt (hy i))))
    (fun i g => by simp only [pow_finite_co_support (hy i) g])

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

end PowerSeriesFamily

section MVpowers

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R] {x : HahnSeries Γ R}
(hx : 0 < x.orderTop)

-- use Finsupp.sumFinsuppAddEquivProdFinsupp and maybe Finsupp.lsingle
-- see also Finsupp.restrictSupportEquiv

/-- An equiv between finsupp and maps from a finset. -/
def equiv_map_on_finset_finsupp {σ : Type*} (s : Finset σ) :
    ((i : σ) → i ∈ s → ℕ) ≃ ({i // i ∈ s} →₀ ℕ) where
  toFun f := Finsupp.equivFunOnFinite.symm (fun i => f i.1 i.2)
  invFun f := fun i hi => (Finsupp.equivFunOnFinite f) ⟨i, hi⟩
  left_inv := congrFun rfl
  right_inv f := by simp

/-- The equivalence between maps on a finite totality and finitely supported functions.-/
def equiv_map_on_fintype_finsupp {σ : Type*} [Fintype σ] :
    ((i : σ) → i ∈ Finset.univ → ℕ) ≃ (σ →₀ ℕ) where
  toFun f := Finsupp.equivFunOnFinite.symm (fun i => f i (mem_univ i))
  invFun f := fun i _ => (Finsupp.equivFunOnFinite f) i
  left_inv f := by simp
  right_inv f := by simp

/-- A multivariable family given by all possible unit-coefficient monomials -/
def mvPowers {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) : SummableFamily Γ R (σ →₀ ℕ) :=
  Equiv equiv_map_on_fintype_finsupp
    (PiFamily Finset.univ (fun _ => ℕ) (fun i => powers (y i) (hy i)))

@[simp]
theorem mvPowers_apply {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (n : σ →₀ ℕ) :
    (mvPowers y hy) n = ∏ i, y i ^ n i := by
  simp [mvPowers, equiv_map_on_fintype_finsupp]

theorem isPWO_iUnion_support_smul_MVpowers {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (f : MvPowerSeries σ R) :
    (⋃ a, ((fun n ↦ (MvPowerSeries.coeff R n) f • (mvPowers y hy) n) a).support).IsPWO := by
  simp_rw [mvPowers_apply]
  exact isPWO_iUnion_support_MVpow (fun n => MvPowerSeries.coeff R n f) y
    (fun i => zero_le_orderTop_iff.mp <| le_of_lt (hy i))

/-- A summable family given by substituting a multivariable power series into positive order
elements.-/
@[simps]
def mvPowerSeriesFamily {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (f : MvPowerSeries σ R) : SummableFamily Γ R (σ →₀ ℕ) where
  toFun n := (MvPowerSeries.coeff R n f) • mvPowers y hy n
  isPWO_iUnion_support' := isPWO_iUnion_support_smul_MVpowers y hy f
  finite_co_support' g := Set.Finite.subset (mvpow_finite_co_support y hy g) fun a ha hng => by
    simp_all [mvPowers, equiv_map_on_fintype_finsupp]

theorem mvPowerSeriesFamilyAdd {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (f g : MvPowerSeries σ R) :
    mvPowerSeriesFamily y hy (f + g) = mvPowerSeriesFamily y hy f + mvPowerSeriesFamily y hy g := by
  ext1 n
  simp [add_smul]

theorem mvPowerSeriesFamilySMul {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (r : R) (f : MvPowerSeries σ R) :
    mvPowerSeriesFamily y hy (r • f) =
      (HahnSeries.single (0 : Γ) r) • (mvPowerSeriesFamily y hy f) := by
  ext1 n
  simp only [mvPowerSeriesFamily_toFun, map_smul, smul_eq_mul, mvPowers,
    equiv_map_on_fintype_finsupp, Finsupp.equivFunOnFinite_apply, Equiv_toFun, Equiv.coe_fn_symm_mk,
    PiFamily_toFun, mem_univ, ↓reduceDIte, powers_toFun, smul_apply, HahnModule.of_smul,
    Algebra.mul_smul_comm, single_zero_mul_eq_smul]
  rw [mul_comm, Equiv.eq_symm_apply, HahnModule.of_smul, mul_smul]

open Classical in
theorem mvPowerSeriesFamily_supp_subset {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) (a b : MvPowerSeries σ R) (g : Γ) :
    ((mvPowerSeriesFamily y hy (a * b)).coeff g).support ⊆
    (((mvPowerSeriesFamily y hy a).mul (mvPowerSeriesFamily y hy b)).coeff g).support.image
      fun i => i.1 + i.2 := by
  simp_all only [coeff_support, mvPowerSeriesFamily_toFun, mvPowers_apply, HahnSeries.coeff_smul,
    smul_eq_mul, mul_toFun, Algebra.mul_smul_comm, Algebra.smul_mul_assoc,
    Set.Finite.toFinset_subset, coe_image, Set.Finite.coe_toFinset, support_subset_iff, ne_eq,
    Set.mem_image, Function.mem_support, Prod.exists]
  intro n hn
  rw [MvPowerSeries.coeff_mul, ← ne_eq, sum_mul] at hn
  have he : ∃p ∈ antidiagonal n, ¬(MvPowerSeries.coeff R p.1) a *
      (MvPowerSeries.coeff R p.2) b * (∏ i : σ, y i ^ n i).coeff g = 0 :=
    exists_ne_zero_of_sum_ne_zero hn
  use he.choose.1, he.choose.2
  refine ⟨?_, mem_antidiagonal.mp he.choose_spec.1⟩
  rw [← mul_assoc, mul_comm ((MvPowerSeries.coeff R he.choose.2) b)]
  simp_rw [← prod_mul_distrib, ← pow_add, ← Finsupp.add_apply, mem_antidiagonal.mp he.choose_spec.1]
  exact he.choose_spec.2

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
  · rw [← HahnSeries.coeff_sum, sum_sigma', coeff_sum]
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
        Algebra.mul_smul_comm, Algebra.smul_mul_assoc, HahnSeries.coeff_smul, smul_eq_mul,
        mem_sigma, mem_image, Set.Finite.mem_toFinset, Function.mem_support, ne_eq, Prod.exists,
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
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, HahnSeries.coeff_smul, smul_eq_mul, mem_image,
      Set.Finite.mem_toFinset, Function.mem_support, ne_eq, Prod.exists, Decidable.not_not,
      HahnSeries.coeff_sum]
    rw [MvPowerSeries.coeff_mul, sum_mul] at his
    exact his

end MVpowers

end SummableFamily

end HahnSeries

namespace MvPowerSeries

open HahnSeries SummableFamily

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R] {σ : Type*} [Fintype σ]
(y : σ →₀ HahnSeries Γ R) (hy : ∀ i, 0 < (y i).orderTop)

/-- The `R`-algebra homomorphism from `R[[X]]` to `HahnSeries Γ R` given by sending the power series
variable `X` to a positive order element `x`. -/
@[simps]
def heval {σ : Type*} [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i, 0 < (y i).orderTop) : MvPowerSeries σ R →ₐ[R] HahnSeries Γ R where
  toFun f := (mvPowerSeriesFamily y hy f).hsum
  map_one' := by
    classical
    simp only [hsum, mvPowerSeriesFamily_toFun, MvPowerSeries.coeff_one, ite_smul, one_smul,
      zero_smul, mvPowers_apply]
    ext g
    simp_rw [finsum_eq_single (fun i => (if i = 0 then ∏ i_1 : σ, y i_1 ^ i i_1 else 0).coeff g)
      (0 : σ →₀ ℕ) (fun n hn => by simp_all)]
    rw [if_true]
    rw [Fintype.prod_eq_one (fun i_1 ↦ y i_1 ^ (0 : σ →₀ ℕ) i_1) (congrFun rfl)]
  map_mul' a b := by
    simp only [← hsum_mul]
    exact mvPowerSeries_family_prod_eq_family_mul y hy a b
  map_zero' := by
    simp only [hsum, mvPowerSeriesFamily_toFun, map_zero, mvPowers_apply, zero_smul,
      HahnSeries.coeff_zero, finsum_zero, mk_eq_zero, Pi.zero_def]
  map_add' a b := by
    ext g
    simp only [coeff_hsum, map_add, mvPowers_apply, SummableFamily.coeff_smul,
      smul_eq_mul, add_mul, coeff_add', Pi.add_apply]
    rw [← finsum_add_distrib (finite_co_support (mvPowerSeriesFamily y hy a) g)
      (finite_co_support (mvPowerSeriesFamily y hy b) g)]
    exact finsum_congr fun s => by rw [mvPowerSeriesFamilyAdd, add_apply, coeff_add]
  commutes' r := by
    simp only [MvPowerSeries.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply,
      algebraMap_apply, C_apply]
    ext g
    classical
    simp only [coeff_hsum, mvPowerSeriesFamily_toFun, mvPowers_apply, SummableFamily.coeff_smul,
      smul_eq_mul]
    rw [finsum_eq_single _ 0 (fun s hs => by simp [hs, MvPowerSeries.coeff_C])]
    by_cases hg : g = 0 <;> simp [hg, Algebra.algebraMap_eq_smul_one']

theorem heval_mul {a b : MvPowerSeries σ R} :
    heval y hy (a * b) = (heval y hy a) * heval y hy b :=
  map_mul (heval y hy) a b

theorem heval_unit (u : (MvPowerSeries σ R)ˣ) : IsUnit (heval y hy u) := by
  refine isUnit_iff_exists_inv.mpr ?_
  use heval y hy u.inv
  rw [← heval_mul, Units.val_inv, map_one]

theorem heval_coeff (f : MvPowerSeries σ R) (g : Γ) :
    (heval y hy f).coeff g = ∑ᶠ n, ((mvPowerSeriesFamily y hy f).coeff g) n := by
  rw [heval_apply, coeff_hsum]
  exact rfl

theorem heval_coeff_zero (f : MvPowerSeries σ R) :
    (heval y hy f).coeff 0 = MvPowerSeries.constantCoeff σ R f := by
  rw [heval_coeff, finsum_eq_single (fun n => ((mvPowerSeriesFamily y hy f).coeff 0) n) 0,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  · simp_all
  · intro n hn
    simp_all only [ne_eq, coeff_toFun, mvPowerSeriesFamily_toFun, mvPowers_apply,
      SummableFamily.coeff_smul, smul_eq_mul]
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

end MvPowerSeries

namespace HahnSeries

section Inversion

variable [LinearOrderedAddCommGroup Γ]

section CommRing

variable [CommRing R]

theorem one_minus_single_mul (x y : HahnSeries Γ R) (r : R) (hr : r * x.leadingCoeff = 1)
    (hxy : x = y + x.leadingTerm) : 1 - single (-order x) r * x = -(single (-x.order) r * y) := by
  nth_rw 2 [hxy]
  rw [mul_add, leadingTerm_eq, single_mul_single, ← leadingCoeff_eq, hr, neg_add_cancel,
    sub_add_eq_sub_sub_swap, sub_eq_neg_self, sub_eq_zero_of_eq]
  exact rfl

theorem unit_aux2 (x : HahnSeries Γ R) {r : R} (hr : r * x.leadingCoeff = 1) :
    0 < (1 - single (-x.order) r * x).orderTop := by
  let y := (x - x.leadingTerm)
  by_cases hy : y = 0
  · have hrx : (single (-order x)) r * x = 1 := by
      nth_rw 2 [eq_of_sub_eq_zero hy]
      simp only [leadingTerm_eq, single_mul_single, neg_add_cancel, hr, ← leadingCoeff_eq]
      exact rfl
    simp only [hrx, sub_self, orderTop_zero, WithTop.top_pos]
  have hr' : ∀ (s : R), r * s = 0 → s = 0 :=
    fun s hs => by rw [← one_mul s, ← hr, mul_right_comm, hs, zero_mul]
  have hy' : 0 < (single (-x.order) r * y).order := by
    rw [(order_mul_single_of_nonzero_divisor hr' hy), lt_neg_add_iff_lt]
    exact order_lt_add_single_support_order (sub_add_cancel x x.leadingTerm).symm hy
  simp only [one_minus_single_mul x y r hr (sub_add_cancel x x.leadingTerm).symm, orderTop_neg]
  exact zero_lt_orderTop_of_order hy'

theorem isUnit_of_isUnit_leadingCoeff {x : HahnSeries Γ R} (hx : IsUnit x.leadingCoeff) :
    IsUnit x := by
  let ⟨⟨u, i, ui, iu⟩, h⟩ := hx
  rw [Units.val_mk] at h
  rw [h] at iu
  have h' := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux2 x iu)
  rw [sub_sub_cancel] at h'
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_eq_one _ _ h')

theorem isUnit_iff2 [IsDomain R] {x : HahnSeries Γ R} :
    IsUnit x ↔ IsUnit (x.leadingCoeff) := by
  refine { mp := ?mp, mpr := isUnit_of_isUnit_leadingCoeff }
  rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
  refine
    isUnit_of_mul_eq_one (u.leadingCoeff) (i.leadingCoeff)
      ((coeff_mul_order_add_order u i).symm.trans ?_)
  rw [ui, coeff_one, if_pos]
  rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ui, order_one]

end CommRing

/-!
open Classical in
instance instField [Field R] : Field (HahnSeries Γ R) where
  __ : IsDomain (HahnSeries Γ R) := inferInstance
  inv x :=
    if x0 : x = 0 then 0
    else
      (single (-x.order)) (x.leadingCoeff)⁻¹ *
        (SummableFamily.powers (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_iff.mpr x0)))).hsum
  inv_zero := dif_pos rfl
  mul_inv_cancel x x0 := (congr rfl (dif_neg x0)).trans <| by
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers
        (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_iff.mpr x0)))
    rw [sub_sub_cancel] at h
    rw [← mul_assoc, mul_comm x, h]
  nnqsmul := _
  nnqsmul_def := fun q a => rfl
  qsmul := _
  qsmul_def := fun q a => rfl
-/

end Inversion

end HahnSeries
