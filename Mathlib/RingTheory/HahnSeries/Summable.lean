/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.PowerSeries.Basic


#align_import ring_theory.hahn_series from "leanprover-community/mathlib"@"a484a7d0eade4e1268f4fb402859b6686037f965"

/-!
# Hahn Series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`.  We introduce a notion of
summability for possibly infinite families of series, and prove that a Hahn Series with invertible
leading coefficient is invertible.  We also show that when the coefficient ring is a domain, then
the converse holds.

## Main Definitions
  * A `HahnSeries.SummableFamily` is a family of Hahn series such that the union of their supports
  is well-founded and only finitely many are nonzero at any given coefficient. They have a formal
  sum, `HahnSeries.SummableFamily.hsum`, which can be bundled as a `LinearMap` as
  `HahnSeries.SummableFamily.lsum`. Note that this is different from `Summable` in the valuation
  topology, because there are topologically summable families that do not satisfy the axioms of
  `HahnSeries.SummableFamily`, and formally summable families whose sums do not converge
  topologically.

## Main results

  * A Hahn series with commutative ring coefficients is invertible if its leading term is
    invertible.

## TODO

  * Substitution of finitely many formal variables into elements of strictly positive orderTop
    induces a ring homomorphism.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

set_option linter.uppercaseLean3 false

open Finset Function

open scoped Classical
open Pointwise

noncomputable section

variable {Γ Γ' R V α β : Type*}

namespace HahnSeries

theorem support_pow_subset_closure [OrderedCancelAddCommMonoid Γ] [Semiring R] (x : HahnSeries Γ R)
    (n : ℕ) : support (x ^ n) ⊆ AddSubmonoid.closure (support x) := by
  induction' n with n ih <;> intro g hn
  · simp_all only [Nat.zero_eq, pow_zero, mem_support, one_coeff, ne_eq, ite_eq_right_iff,
    not_forall, exists_prop, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem (AddSubmonoid.closure (support x))
  · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (ih hi) (AddSubmonoid.subset_closure hj))

theorem support_smul_pow_subset_closure [OrderedCancelAddCommMonoid Γ] [Semiring R]
    (f : ℕ → R) (x : HahnSeries Γ R) (n : ℕ) :
    (f n • x ^ n).support ⊆ AddSubmonoid.closure x.support :=
  (Function.support_const_smul_subset (f n) (x ^ n).coeff).trans (support_pow_subset_closure x n)

theorem support_prod_subset_add_support [OrderedCancelAddCommMonoid Γ] [CommSemiring R]
    (σ : Type*) (x : σ →₀ HahnSeries Γ R) (s : Finset σ):
    (∏ i ∈ s, (x i)).support ⊆ ∑ i ∈ s, (x i).support := by
  refine Finset.cons_induction ?_ ?_ s
  · rw [prod_empty, sum_empty, ← single_zero_one, ← Set.singleton_zero]
    exact support_single_subset
  · intros _ _ _ his _ hg
    simp_all only [cons_eq_insert, not_false_eq_true, prod_insert, sum_insert]
    exact support_mul_subset_add_support.trans (Set.add_subset_add (fun ⦃a⦄ a ↦ a) his) hg

theorem support_MVpow_subset_closure [OrderedCancelAddCommMonoid Γ] [CommSemiring R]
    (σ : Type*) (x : σ →₀ HahnSeries Γ R) (n : σ →₀ ℕ) :
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

theorem support_smul_MVpow_subset_closure [OrderedCancelAddCommMonoid Γ] [CommSemiring R]
    (σ : Type*) (f : (σ →₀ ℕ) → R) (x : σ →₀ HahnSeries Γ R) (n : σ →₀ ℕ) :
    support (f n • ∏ i ∈ x.support, (x i) ^ (n i)) ⊆
      AddSubmonoid.closure (⋃ i : σ, (x i).support) := by
  exact (Function.support_const_smul_subset (f n) (∏ i ∈ x.support, x i ^ n i).coeff).trans
    (support_MVpow_subset_closure σ x n)

theorem isPWO_iUnion_support_MVpow [LinearOrderedCancelAddCommMonoid Γ] [CommSemiring R]
    (σ : Type*) (f : (σ →₀ ℕ) → R) (x : σ →₀ HahnSeries Γ R) (hx : ∀ i : σ, 0 ≤ (x i).order) :
    (⋃ n : σ →₀ ℕ, (f n •  ∏ i ∈ x.support, (x i) ^ (n i)).support).IsPWO := by
  refine Set.IsPWO.mono ?_ (Set.iUnion_subset fun n => support_smul_MVpow_subset_closure σ f x n)
  refine Set.IsPWO.addSubmonoid_closure ?_ ?_
  · intro g hg
    simp only [Set.mem_iUnion, mem_support, ne_eq] at hg
    obtain ⟨i, hi⟩ := hg
    exact (hx i).trans (order_le_of_coeff_ne_zero hi)
  · have h : ⋃ i, (x i).support =
        (⋃ i ∈ x.support, (x i).support) ∪ (⋃ i ∉ x.support, (x i).support) := by
      simp_rw [← Set.iUnion_ite, ite_id (x _).support]
    rw [h, Set.isPWO_union]
    constructor
    · exact (isPWO_bUnion x.support).mpr fun i _ ↦ isPWO_support (x i)
    · rw [show (⋃ i, ⋃ (_ : i ∉ x.support), (x i).support) = ∅ by simp_all]
      exact Set.isPWO_empty

/-!
theorem isPWO_iUnion_support_MVpow' [LinearOrderedCancelAddCommMonoid Γ] [CommSemiring R]
    {σ : Type*} (s : Finset σ) (f : (σ →₀ ℕ) → R) (x : σ →₀ HahnSeries Γ R)
    (hx : ∀ i : σ, 0 ≤ (x i).order) :
    (⋃ n : σ →₀ ℕ, (f n •  ∏ i ∈ s, (x i) ^ (n i)).support).IsPWO := by
  sorry
-/

theorem isPWO_iUnion_support_smul_pow [LinearOrderedCancelAddCommMonoid Γ] [Semiring R] (f : ℕ → R)
    (x : HahnSeries Γ R) (hx : 0 ≤ x.order) :
    (⋃ n : ℕ, (f n • x ^ n).support).IsPWO :=
  (x.isPWO_support'.addSubmonoid_closure
    fun _ hg => le_trans hx (order_le_of_coeff_ne_zero (Function.mem_support.mp hg))).mono
    (Set.iUnion_subset fun n => support_smul_pow_subset_closure f x n)

theorem isPWO_iUnion_support_powers [LinearOrderedCancelAddCommMonoid Γ] [Semiring R]
    (x : HahnSeries Γ R) (hx : 0 ≤ x.order) : (⋃ n : ℕ, (x ^ n).support).IsPWO := by
  have _ := isPWO_iUnion_support_smul_pow (fun n => 1) x hx
  simp_all only [one_smul]
#align hahn_series.is_pwo_Union_support_powers HahnSeries.isPWO_iUnion_support_powers

section

variable (Γ) (R) [PartialOrder Γ] [AddCommMonoid R]

/-- A family of Hahn series whose formal coefficient-wise sum is a Hahn series.  For each
coefficient of the sum to be well-defined, we require that only finitely many series are nonzero at
any given coefficient.  For the formal sum to be a Hahn series, we require that the union of the
supports of the constituent series is well-founded. -/
structure SummableFamily (α : Type*) where
  /-- A parametrized family of Hahn series. -/
  toFun : α → HahnSeries Γ R
  isPWO_iUnion_support' : Set.IsPWO (⋃ a : α, (toFun a).support)
  finite_co_support' : ∀ g : Γ, { a | (toFun a).coeff g ≠ 0 }.Finite
#align hahn_series.summable_family HahnSeries.SummableFamily

end

namespace SummableFamily

section AddCommMonoid

variable [PartialOrder Γ] [AddCommMonoid R] {α : Type*}

instance : FunLike (SummableFamily Γ R α) α (HahnSeries Γ R) where
  coe := toFun
  coe_injective' | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

theorem isPWO_iUnion_support (s : SummableFamily Γ R α) : Set.IsPWO (⋃ a : α, (s a).support) :=
  s.isPWO_iUnion_support'
#align hahn_series.summable_family.is_pwo_Union_support HahnSeries.SummableFamily.isPWO_iUnion_support

theorem finite_co_support (s : SummableFamily Γ R α) (g : Γ) :
    (Function.support fun a => (s a).coeff g).Finite :=
  s.finite_co_support' g
#align hahn_series.summable_family.finite_co_support HahnSeries.SummableFamily.finite_co_support

theorem coe_injective : @Function.Injective (SummableFamily Γ R α) (α → HahnSeries Γ R) (⇑) :=
  DFunLike.coe_injective
#align hahn_series.summable_family.coe_injective HahnSeries.SummableFamily.coe_injective

@[ext]
theorem ext {s t : SummableFamily Γ R α} (h : ∀ a : α, s a = t a) : s = t :=
  DFunLike.ext s t h
#align hahn_series.summable_family.ext HahnSeries.SummableFamily.ext

instance : Add (SummableFamily Γ R α) :=
  ⟨fun x y =>
    { toFun := x + y
      isPWO_iUnion_support' :=
        (x.isPWO_iUnion_support.union y.isPWO_iUnion_support).mono
          (by
            rw [← Set.iUnion_union_distrib]
            exact Set.iUnion_mono fun a => support_add_subset)
      finite_co_support' := fun g =>
        ((x.finite_co_support g).union (y.finite_co_support g)).subset
          (by
            intro a ha
            change (x a).coeff g + (y a).coeff g ≠ 0 at ha
            rw [Set.mem_union, Function.mem_support, Function.mem_support]
            contrapose! ha
            rw [ha.1, ha.2, add_zero]) }⟩

instance : Zero (SummableFamily Γ R α) :=
  ⟨⟨0, by simp, by simp⟩⟩

instance : Inhabited (SummableFamily Γ R α) :=
  ⟨0⟩

@[simp]
theorem coe_add {s t : SummableFamily Γ R α} : ⇑(s + t) = s + t :=
  rfl
#align hahn_series.summable_family.coe_add HahnSeries.SummableFamily.coe_add

theorem add_apply {s t : SummableFamily Γ R α} {a : α} : (s + t) a = s a + t a :=
  rfl
#align hahn_series.summable_family.add_apply HahnSeries.SummableFamily.add_apply

@[simp]
theorem coe_zero : ((0 : SummableFamily Γ R α) : α → HahnSeries Γ R) = 0 :=
  rfl
#align hahn_series.summable_family.coe_zero HahnSeries.SummableFamily.coe_zero

theorem zero_apply {a : α} : (0 : SummableFamily Γ R α) a = 0 :=
  rfl
#align hahn_series.summable_family.zero_apply HahnSeries.SummableFamily.zero_apply

instance : AddCommMonoid (SummableFamily Γ R α) where
  zero := 0
  nsmul := nsmulRec
  zero_add s := by
    ext
    apply zero_add
  add_zero s := by
    ext
    apply add_zero
  add_comm s t := by
    ext
    apply add_comm
  add_assoc r s t := by
    ext
    apply add_assoc

/-- The coefficient function of a summable family, as a finsupp on the parameter type. -/
@[simps]
def coeff (s : SummableFamily Γ R α) (g : Γ) : α →₀ R where
  support := (s.finite_co_support g).toFinset
  toFun a := (s a).coeff g
  mem_support_toFun a := by simp

@[simp]
theorem coeff_def (s : SummableFamily Γ R α) (a : α) (g : Γ) : s.coeff g a = (s a).coeff g :=
  rfl

/-- The infinite sum of a `SummableFamily` of Hahn series. -/
def hsum (s : SummableFamily Γ R α) : HahnSeries Γ R where
  coeff g := ∑ᶠ i, (s i).coeff g
  isPWO_support' :=
    s.isPWO_iUnion_support.mono fun g => by
      contrapose
      rw [Set.mem_iUnion, not_exists, Function.mem_support, Classical.not_not]
      simp_rw [mem_support, Classical.not_not]
      intro h
      rw [finsum_congr h, finsum_zero]
#align hahn_series.summable_family.hsum HahnSeries.SummableFamily.hsum

@[simp]
theorem hsum_coeff {s : SummableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g :=
  rfl
#align hahn_series.summable_family.hsum_coeff HahnSeries.SummableFamily.hsum_coeff

theorem support_hsum_subset {s : SummableFamily Γ R α} : s.hsum.support ⊆ ⋃ a : α, (s a).support :=
  fun g hg => by
  rw [mem_support, hsum_coeff, finsum_eq_sum _ (s.finite_co_support _)] at hg
  obtain ⟨a, _, h2⟩ := exists_ne_zero_of_sum_ne_zero hg
  rw [Set.mem_iUnion]
  exact ⟨a, h2⟩
#align hahn_series.summable_family.support_hsum_subset HahnSeries.SummableFamily.support_hsum_subset

@[simp]
theorem hsum_add {s t : SummableFamily Γ R α} : (s + t).hsum = s.hsum + t.hsum := by
  ext g
  simp only [hsum_coeff, add_coeff, add_apply]
  exact finsum_add_distrib (s.finite_co_support _) (t.finite_co_support _)
#align hahn_series.summable_family.hsum_add HahnSeries.SummableFamily.hsum_add

theorem hsum_coeff_sum {s : SummableFamily Γ R α} {g : Γ} :
    s.hsum.coeff g = ∑ i ∈ (s.coeff g).support, (s i).coeff g := by
  simp [finsum_eq_sum _ (s.finite_co_support _)]

theorem hsum_coeff_subset_sum {s : SummableFamily Γ R α} {g : Γ} {t : Finset α}
    (h : { a | (s a).coeff g ≠ 0 } ⊆ t) : s.hsum.coeff g = ∑ i ∈ t, (s i).coeff g := by
  rw [hsum_coeff_sum]
  refine sum_subset (Set.Finite.toFinset_subset.mpr h) ?_
  simp_all

/-- The summable family made of a single Hahn series. -/
@[simps]
def single (x : HahnSeries Γ R) : SummableFamily Γ R Unit where
  toFun _ := x
  isPWO_iUnion_support' :=
    Eq.mpr (congrArg (fun s ↦ s.IsPWO) (Set.iUnion_const x.support)) x.isPWO_support
  finite_co_support' g := Set.toFinite {a | ((fun _ ↦ x) a).coeff g ≠ 0}

@[simp]
theorem hsum_single (x : HahnSeries Γ R) : (single x).hsum = x := by
  ext g
  simp only [hsum_coeff, single_toFun, finsum_unique]

/-- A summable family induced by an equivalence of the parametrizing type. -/
@[simps]
def Equiv (e : α ≃ β) (s : SummableFamily Γ R α) : SummableFamily Γ R β where
  toFun b := s (e.symm b)
  isPWO_iUnion_support' := by
    refine Set.IsPWO.mono s.isPWO_iUnion_support fun g => ?_
    simp only [Set.mem_iUnion, mem_support, ne_eq, forall_exists_index]
    exact fun b hg => Exists.intro (e.symm b) hg
  finite_co_support' g :=
    (Equiv.set_finite_iff e.subtypeEquivOfSubtype').mp <| s.finite_co_support' g

@[simp]
theorem hsum_equiv (e : α ≃ β) (s : SummableFamily Γ R α) : (Equiv e s).hsum = s.hsum := by
  ext g
  simp only [hsum_coeff, Equiv_toFun]
  exact finsum_eq_of_bijective e.symm (Equiv.bijective e.symm) fun x => rfl

end AddCommMonoid

section AddCommGroup

variable [PartialOrder Γ] [AddCommGroup R] {s t : SummableFamily Γ R α} {a : α}

instance : Neg (SummableFamily Γ R α) :=
  ⟨fun s =>
    { toFun := fun a => -s a
      isPWO_iUnion_support' := by
        simp_rw [support_neg]
        exact s.isPWO_iUnion_support
      finite_co_support' := fun g => by
        simp only [neg_coeff', Pi.neg_apply, Ne, neg_eq_zero]
        exact s.finite_co_support g }⟩

instance : AddCommGroup (SummableFamily Γ R α) :=
  { inferInstanceAs (AddCommMonoid (SummableFamily Γ R α)) with
    zsmul := zsmulRec
    add_left_neg := fun a => by
      ext
      apply add_left_neg }

@[simp]
theorem coe_neg : ⇑(-s) = -s :=
  rfl
#align hahn_series.summable_family.coe_neg HahnSeries.SummableFamily.coe_neg

theorem neg_apply : (-s) a = -s a :=
  rfl
#align hahn_series.summable_family.neg_apply HahnSeries.SummableFamily.neg_apply

@[simp]
theorem coe_sub : ⇑(s - t) = s - t :=
  rfl
#align hahn_series.summable_family.coe_sub HahnSeries.SummableFamily.coe_sub

theorem sub_apply : (s - t) a = s a - t a :=
  rfl
#align hahn_series.summable_family.sub_apply HahnSeries.SummableFamily.sub_apply

end AddCommGroup

section SMul

variable [PartialOrder Γ] [PartialOrder Γ'] [VAdd Γ Γ'] [OrderedCancelVAdd Γ Γ'] [AddCommMonoid V]

theorem smul_support_subset_prod [AddCommMonoid R] [SMulWithZero R V] (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (gh : Γ × Γ') :
    (Function.support fun (i : α × β) ↦ (s i.1).coeff gh.1 • (t i.2).coeff gh.2) ⊆
    ((s.finite_co_support' gh.1).prod (t.finite_co_support' gh.2)).toFinset := by
    intro ab hab
    simp_all only [Function.mem_support, ne_eq, Set.Finite.coe_toFinset, Set.mem_prod,
      Set.mem_setOf_eq]
    refine ⟨left_ne_zero_of_smul hab, right_ne_zero_of_smul hab⟩

theorem smul_support_finite [AddCommMonoid R] [SMulWithZero R V] (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (gh : Γ × Γ') :
    (Function.support fun (i : α × β) ↦ (s i.1).coeff gh.1 • (t i.2).coeff gh.2).Finite :=
  Set.Finite.subset (Set.toFinite ((s.finite_co_support' gh.1).prod
    (t.finite_co_support' gh.2)).toFinset) (smul_support_subset_prod s t gh)

theorem isPWO_iUnion_support_prod [AddCommMonoid R] [SMulWithZero R V] {s : α → HahnSeries Γ R}
    {t : β → HahnSeries Γ' V} (hs : (⋃ a, (s a).support).IsPWO) (ht : (⋃ b, (t b).support).IsPWO) :
    (⋃ (a : α × β), ((fun a ↦ (HahnModule.of R).symm
      ((s a.1) • (HahnModule.of R) (t a.2))) a).support).IsPWO := by
  apply (hs.vAdd ht).mono
  have hsupp : ∀ a : α × β, support ((fun a ↦ s a.1 • (HahnModule.of R) (t a.2)) a) ⊆
      (s a.1).support +ᵥ (t a.2).support := by
    intro a
    rw [show t a.2 = (HahnModule.of R).symm ((HahnModule.of R) (t a.2)) by rfl]
    simp only
    exact HahnModule.support_smul_subset_vAdd_support (x := s a.1)
  refine Set.Subset.trans (Set.iUnion_mono fun a => (hsupp a)) ?_
  simp_all only [Set.iUnion_subset_iff, Prod.forall]
  exact fun a b => Set.vadd_subset_vadd (Set.subset_iUnion_of_subset a fun x y ↦ y)
    (Set.subset_iUnion_of_subset b fun x y ↦ y)

theorem finite_co_support_prod [AddCommMonoid R] [SMulWithZero R V] (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (g : Γ') :
    Finite {(a : α × β) | ((fun (a : α × β) ↦ (HahnModule.of R).symm (s a.1 • (HahnModule.of R)
      (t a.2))) a).coeff g ≠ 0} := by
  apply ((vAddAntidiagonal s.isPWO_iUnion_support t.isPWO_iUnion_support g).finite_toSet.biUnion'
    _).subset _
  · exact fun ij _ => Function.support fun a =>
      ((s a.1).coeff ij.1) • ((t a.2).coeff ij.2)
  · exact fun gh _ => smul_support_finite s t gh
  · exact fun a ha => by
      simp only [smul_coeff, ne_eq, Set.mem_setOf_eq] at ha
      obtain ⟨ij, hij⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
      simp only [mem_coe, mem_vAddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq,
        Function.mem_support, exists_prop, Prod.exists]
      exact ⟨ij.1, ij.2, ⟨⟨a.1, left_ne_zero_of_smul hij.2⟩, ⟨a.2, right_ne_zero_of_smul hij.2⟩,
        ((mem_vAddAntidiagonal _ _ _).mp hij.1).2.2⟩, hij.2⟩

/-- An elementwise scalar multiplication of one summable family on another. -/
@[simps]
def FamilySMul [AddCommMonoid R] [SMulWithZero R V] (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) : (SummableFamily Γ' V (α × β)) where
  toFun a := (HahnModule.of R).symm (s (a.1) • ((HahnModule.of R) (t (a.2))))
  isPWO_iUnion_support' := isPWO_iUnion_support_prod s.isPWO_iUnion_support t.isPWO_iUnion_support
  finite_co_support' g := finite_co_support_prod s t g

/-!
theorem cosupp_subset_iunion_cosupp_left [AddCommMonoid R] (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (g : Γ') {gh : Γ × Γ'}
    (hgh : gh ∈ vAddAntidiagonal s.isPWO_iUnion_support t.isPWO_iUnion_support g) :
    Set.Finite.toFinset (s.finite_co_support (gh.1)) ⊆
    (vAddAntidiagonal s.isPWO_iUnion_support t.isPWO_iUnion_support g).biUnion
      fun (g' : Γ × Γ') => Set.Finite.toFinset (s.finite_co_support (g'.1)) := by
  intro a ha
  simp_all only [mem_vAddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq, Set.Finite.mem_toFinset,
    Function.mem_support, mem_biUnion, Prod.exists, exists_and_right, exists_and_left]
  exact Exists.intro gh.1 ⟨⟨hgh.1, Exists.intro gh.2 hgh.2⟩, ha⟩
-/

theorem sum_vAddAntidiagonal_eq [AddCommMonoid R] [SMulWithZero R V] (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (g : Γ') (a : α × β) :
    ∑ x ∈ vAddAntidiagonal (s a.1).isPWO_support' (t a.2).isPWO_support' g, (s a.1).coeff x.1 •
      (t a.2).coeff x.2 = ∑ x ∈ vAddAntidiagonal s.isPWO_iUnion_support' t.isPWO_iUnion_support' g,
      (s a.1).coeff x.1 • (t a.2).coeff x.2 := by
  refine sum_subset (fun gh hgh => ?_) fun gh hgh h => ?_
  · simp_all only [mem_vAddAntidiagonal, Function.mem_support, Set.mem_iUnion, mem_support]
    refine ⟨Exists.intro a.1 hgh.1, Exists.intro a.2 hgh.2.1, trivial⟩
  · by_cases hs : (s a.1).coeff gh.1 = 0
    · exact smul_eq_zero_of_left hs ((t a.2).coeff gh.2)
    · simp_all

theorem family_smul_coeff [Semiring R] [Module R V] (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (g : Γ') :
    (FamilySMul s t).hsum.coeff g = ∑ gh ∈ vAddAntidiagonal s.isPWO_iUnion_support
      t.isPWO_iUnion_support g, (s.hsum.coeff gh.1) • (t.hsum.coeff gh.2) := by
  rw [hsum_coeff]
  simp only [hsum_coeff_sum, FamilySMul_toFun, HahnModule.smul_coeff, Equiv.symm_apply_apply]
  simp_rw [sum_vAddAntidiagonal_eq, Finset.smul_sum, Finset.sum_smul]
  rw [← sum_finsum_comm _ _ <| fun gh _ => smul_support_finite s t gh]
  refine sum_congr rfl fun gh _ => ?_
  rw [finsum_eq_sum _ (smul_support_finite s t gh), ← sum_product_right']
  refine sum_subset (fun ab hab => ?_) (fun ab _ hab => by simp_all)
  have hsupp := smul_support_subset_prod s t gh
  simp_all only [mem_vAddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq, Set.Finite.mem_toFinset,
    Function.mem_support, Set.Finite.coe_toFinset, support_subset_iff, Set.mem_prod,
    Set.mem_setOf_eq, Prod.forall, coeff_support, mem_product]
  exact hsupp ab.1 ab.2 hab

theorem hsum_family_smul [Semiring R] [Module R V] (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) :
    (FamilySMul s t).hsum = (HahnModule.of R).symm (s.hsum • (HahnModule.of R) (t.hsum)) := by
  ext g
  rw [family_smul_coeff, HahnModule.smul_coeff, Equiv.symm_apply_apply]
  refine Eq.symm (sum_of_injOn (fun a ↦ a) (fun _ _ _ _ h ↦ h) ?_ ?_ fun _ _ => by simp)
  · intro gh hgh
    simp_all only [mem_coe, mem_vAddAntidiagonal, mem_support, ne_eq, Set.mem_iUnion, and_true]
    constructor
    · rw [hsum_coeff_sum] at hgh
      have h' := Finset.exists_ne_zero_of_sum_ne_zero hgh.1
      simp_all
    · by_contra hi
      simp_all
  · intro gh _ hgh'
    simp only [Set.image_id', mem_coe, mem_vAddAntidiagonal, mem_support, ne_eq, not_and] at hgh'
    by_cases h : s.hsum.coeff gh.1 = 0
    · exact smul_eq_zero_of_left h (t.hsum.coeff gh.2)
    · simp_all

instance [AddCommMonoid R] [SMulWithZero R V] : SMul (HahnSeries Γ R) (SummableFamily Γ' V β) where
  smul x t := Equiv (Equiv.punitProd β) <| FamilySMul (single x) t

theorem smul_eq [AddCommMonoid R] [SMulWithZero R V] {x : HahnSeries Γ R}
    {t : SummableFamily Γ' V β} : x • t = Equiv (Equiv.punitProd β) (FamilySMul (single x) t) :=
  rfl

@[simp]
theorem smul_apply [AddCommMonoid R] [SMulWithZero R V] {x : HahnSeries Γ R}
    {s : SummableFamily Γ' V α} {a : α} :
    (x • s) a = (HahnModule.of R).symm (x • HahnModule.of R (s a)) :=
  rfl
#align hahn_series.summable_family.smul_apply HahnSeries.SummableFamily.smul_apply

@[simp]
theorem hsum_smul' [Semiring R] [Module R V] {x : HahnSeries Γ R} {s : SummableFamily Γ' V α} :
    (x • s).hsum = (HahnModule.of R).symm (x • HahnModule.of R s.hsum) := by
  rw [smul_eq, hsum_equiv, hsum_family_smul, hsum_single]

end SMul

section Semiring

variable {Γ' : Type*} [OrderedCancelAddCommMonoid Γ] [PartialOrder Γ'] [AddAction Γ Γ']
  [OrderedCancelVAdd Γ Γ'] [Semiring R] [AddCommMonoid V] [Module R V] {α : Type*}

instance : Module (HahnSeries Γ R) (SummableFamily Γ' V α) where
  smul := (· • ·)
  smul_zero _ := ext fun _ => by simp
  zero_smul _ := ext fun _ => by simp
  one_smul _ := ext fun _ => by rw [smul_apply, HahnModule.one_smul', Equiv.symm_apply_apply]
  add_smul _ _ _  := ext fun _ => by simp [add_smul]
  smul_add _ _ _ := ext fun _ => by simp
  mul_smul _ _ _ := ext fun _ => by simp [HahnModule.instModule.mul_smul]

theorem hsum_smul {x : HahnSeries Γ R} {s : SummableFamily Γ R α} :
    (x • s).hsum = x * s.hsum := by
  rw [hsum_smul', of_symm_smul_of_eq_mul]
#align hahn_series.summable_family.hsum_smul HahnSeries.SummableFamily.hsum_smul

/-- The summation of a `summable_family` as a `LinearMap`. -/
@[simps]
def lsum : SummableFamily Γ R α →ₗ[HahnSeries Γ R] HahnSeries Γ R where
  toFun := hsum
  map_add' _ _ := hsum_add
  map_smul' _ _ := hsum_smul
#align hahn_series.summable_family.lsum HahnSeries.SummableFamily.lsum

@[simp]
theorem hsum_sub {R : Type*} [Ring R] {s t : SummableFamily Γ R α} :
    (s - t).hsum = s.hsum - t.hsum := by
  rw [← lsum_apply, LinearMap.map_sub, lsum_apply, lsum_apply]
#align hahn_series.summable_family.hsum_sub HahnSeries.SummableFamily.hsum_sub

/-- Pointwise multiplication of summable families. -/
@[simps]
def FamilyMul {β : Type*} (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    (SummableFamily Γ R (α × β)) where
  toFun a := s (a.1) * t (a.2)
  isPWO_iUnion_support' := by
    simp_rw [← smul_eq_mul]
    exact (FamilySMul s t).isPWO_iUnion_support'
  finite_co_support' g := by
    simp_rw [← smul_eq_mul]
    exact (FamilySMul s t).finite_co_support' g

theorem familymul_eq_familysmul {β : Type*} (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    FamilyMul s t = FamilySMul s t :=
  rfl

theorem family_mul_coeff {β : Type*} (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) (g : Γ) :
    (FamilyMul s t).hsum.coeff g = ∑ gh ∈ addAntidiagonal s.isPWO_iUnion_support
      t.isPWO_iUnion_support g, (s.hsum.coeff gh.1) * (t.hsum.coeff gh.2) := by
  simp_rw [← smul_eq_mul, familymul_eq_familysmul]
  exact family_smul_coeff s t g

theorem hsum_family_mul {β : Type*} (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    (FamilyMul s t).hsum = s.hsum * t.hsum := by
  rw [← smul_eq_mul, familymul_eq_familysmul]
  exact hsum_family_smul s t

/-!
theorem pi_PWO_iUnion_support {σ : Type*} (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*)
    {t : Π i : σ, (α i) → HahnSeries Γ R}
    (ht : ∀ i : σ, (⋃ a : α i, ((t i) a).support).IsPWO) :
    (⋃ a : (i : σ) → i ∈ s → α i,
      (∏ i ∈ s, if h : i ∈ s then (t i) (a i h) else 1).support).IsPWO := by
  refine cons_induction ?_ ?_ s
  · simp only [prod_empty]
    have h : ⋃ (a : (i : σ) → i ∈ (∅ : Finset σ) → α i) , support (1 : HahnSeries Γ R) ⊆ {0} := by
      simp
    exact Set.Subsingleton.isPWO <| Set.subsingleton_of_subset_singleton h
  · intro a s' has hp
    refine (isPWO_iUnion_support_prod (ht a) hp).mono ?_
    intro g hg
    simp_all only [dite_true, mem_cons, not_false_eq_true, prod_cons, or_false,
      or_true, Set.mem_iUnion, mem_support, ne_eq, Prod.exists]
    obtain ⟨i, hi⟩ := hg

    sorry

    have hsupp : ∀ a : α × β, support ((fun a ↦ s a.1 • (HahnModule.of R) (t a.2)) a) ⊆
        (s a.1).support +ᵥ (t a.2).support := by
      intro a
      rw [show t a.2 = (HahnModule.of R).symm ((HahnModule.of R) (t a.2)) by rfl]
      simp only
      exact HahnModule.support_smul_subset_vAdd_support (x := s a.1)

theorem pi_finite_co_support {σ : Type*} (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*) (g : Γ)
    {t : Π i : σ, (α i) → HahnSeries Γ R} (htp : ∀ i : σ, (⋃ a : α i, ((t i) a).support).IsPWO)
    (htfc : ∀ i : σ, {a : α i | ((t i) a).coeff g ≠ 0}.Finite) :
    {a : (i : σ) → i ∈ s → α i |
      ((fun a ↦ ∏ i ∈ s, if h : i ∈ s then (t i) (a i h) else 1) a).coeff g ≠ 0}.Finite := by
  sorry

/-- A summable family made from a finite collection of summable families. -/
def PiFamily {σ : Type*} (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*)
    (t : Π i : σ, SummableFamily Γ R (α i)) : (SummableFamily Γ R (Π i ∈ s, α i)) where
  toFun a := Finset.prod s fun i => if h : i ∈ s then (t i) (a i h) else 1
  isPWO_iUnion_support' := pi_PWO_iUnion_support s α fun i => (t i).isPWO_iUnion_support
  finite_co_support' g :=
    pi_finite_co_support s α g (fun i => (t i).isPWO_iUnion_support)
      (fun i => (t i).finite_co_support g)

theorem hsum_pi_family {σ : Type*} (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*)
    (t : Π i : σ, SummableFamily Γ R (α i)) :
    (PiFamily s α t).hsum = ∏ i ∈ s, (t i).hsum := by
  sorry
-/

end Semiring

section OfFinsupp

variable [PartialOrder Γ] [AddCommMonoid R] {α : Type*}

/-- A family with only finitely many nonzero elements is summable. -/
def ofFinsupp (f : α →₀ HahnSeries Γ R) : SummableFamily Γ R α where
  toFun := f
  isPWO_iUnion_support' := by
    apply (f.support.isPWO_bUnion.2 fun a _ => (f a).isPWO_support).mono
    refine Set.iUnion_subset_iff.2 fun a g hg => ?_
    have haf : a ∈ f.support := by
      rw [Finsupp.mem_support_iff, ← support_nonempty_iff]
      exact ⟨g, hg⟩
    exact Set.mem_biUnion haf hg
  finite_co_support' g := by
    refine f.support.finite_toSet.subset fun a ha => ?_
    simp only [coeff.addMonoidHom_apply, mem_coe, Finsupp.mem_support_iff, Ne,
      Function.mem_support]
    contrapose! ha
    simp [ha]
#align hahn_series.summable_family.of_finsupp HahnSeries.SummableFamily.ofFinsupp

@[simp]
theorem coe_ofFinsupp {f : α →₀ HahnSeries Γ R} : ⇑(SummableFamily.ofFinsupp f) = f :=
  rfl
#align hahn_series.summable_family.coe_of_finsupp HahnSeries.SummableFamily.coe_ofFinsupp

@[simp]
theorem hsum_ofFinsupp {f : α →₀ HahnSeries Γ R} : (ofFinsupp f).hsum = f.sum fun _ => id := by
  ext g
  simp only [hsum_coeff, coe_ofFinsupp, Finsupp.sum, Ne]
  simp_rw [← coeff.addMonoidHom_apply, id]
  rw [map_sum, finsum_eq_sum_of_support_subset]
  intro x h
  simp only [coeff.addMonoidHom_apply, mem_coe, Finsupp.mem_support_iff, Ne]
  contrapose! h
  simp [h]
#align hahn_series.summable_family.hsum_of_finsupp HahnSeries.SummableFamily.hsum_ofFinsupp

end OfFinsupp

section EmbDomain

variable [PartialOrder Γ] [AddCommMonoid R] {α β : Type*}

/-- A summable family can be reindexed by an embedding without changing its sum. -/
def embDomain (s : SummableFamily Γ R α) (f : α ↪ β) : SummableFamily Γ R β where
  toFun b := if h : b ∈ Set.range f then s (Classical.choose h) else 0
  isPWO_iUnion_support' := by
    refine s.isPWO_iUnion_support.mono (Set.iUnion_subset fun b g h => ?_)
    by_cases hb : b ∈ Set.range f
    · dsimp only at h
      rw [dif_pos hb] at h
      exact Set.mem_iUnion.2 ⟨Classical.choose hb, h⟩
    · simp [-Set.mem_range, dif_neg hb] at h
  finite_co_support' g :=
    ((s.finite_co_support g).image f).subset
      (by
        intro b h
        by_cases hb : b ∈ Set.range f
        · simp only [Ne, Set.mem_setOf_eq, dif_pos hb] at h
          exact ⟨Classical.choose hb, h, Classical.choose_spec hb⟩
        · simp only [Ne, Set.mem_setOf_eq, dif_neg hb, zero_coeff, not_true_eq_false] at h)
#align hahn_series.summable_family.emb_domain HahnSeries.SummableFamily.embDomain

variable (s : SummableFamily Γ R α) (f : α ↪ β) {a : α} {b : β}

theorem embDomain_apply :
    s.embDomain f b = if h : b ∈ Set.range f then s (Classical.choose h) else 0 :=
  rfl
#align hahn_series.summable_family.emb_domain_apply HahnSeries.SummableFamily.embDomain_apply

@[simp]
theorem embDomain_image : s.embDomain f (f a) = s a := by
  rw [embDomain_apply, dif_pos (Set.mem_range_self a)]
  exact congr rfl (f.injective (Classical.choose_spec (Set.mem_range_self a)))
#align hahn_series.summable_family.emb_domain_image HahnSeries.SummableFamily.embDomain_image

@[simp]
theorem embDomain_notin_range (h : b ∉ Set.range f) : s.embDomain f b = 0 := by
  rw [embDomain_apply, dif_neg h]
#align hahn_series.summable_family.emb_domain_notin_range HahnSeries.SummableFamily.embDomain_notin_range

@[simp]
theorem hsum_embDomain : (s.embDomain f).hsum = s.hsum := by
  ext g
  simp only [hsum_coeff, embDomain_apply, apply_dite HahnSeries.coeff, dite_apply, zero_coeff]
  exact finsum_emb_domain f fun a => (s a).coeff g
#align hahn_series.summable_family.hsum_emb_domain HahnSeries.SummableFamily.hsum_embDomain

end EmbDomain

section PowerSeriesFamily

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R]

-- consider substitutions of power series in finitely many variables, using finitely many
-- positive-orderTop elements.

theorem co_support_zero (g : Γ) : {a | ¬((0 : HahnSeries Γ R) ^ a).coeff g = 0} ⊆ {0} := by
  simp_all only [Set.subset_singleton_iff, Set.mem_setOf_eq]
  intro n hn
  by_contra h'
  simp_all only [ne_eq, not_false_eq_true, zero_pow, zero_coeff, not_true_eq_false]

variable {x : HahnSeries Γ R} (hx : 0 < x.orderTop)

theorem pow_finite_co_support (g : Γ) : Set.Finite {a | ((fun n ↦ x ^ n) a).coeff g ≠ 0} := by
  have hpwo : Set.IsPWO (⋃ n, support (x ^ n)) :=
    isPWO_iUnion_support_powers x (zero_le_orderTop_iff.mp <| le_of_lt hx)
  by_cases hox : x = 0
  · rw [hox]
    exact Set.Finite.subset (Set.finite_singleton 0) (co_support_zero g)
  by_cases hg : g ∈ ⋃ n : ℕ, { g | (x ^ n).coeff g ≠ 0 }
  swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
  apply hpwo.isWF.induction hg
  intro y ys hy
  refine'
    ((((addAntidiagonal x.isPWO_support hpwo y).finite_toSet.biUnion fun ij hij =>
                  hy ij.snd _ _).image
              Nat.succ).union
          (Set.finite_singleton 0)).subset
      _
  · exact (mem_addAntidiagonal.1 (mem_coe.1 hij)).2.1
  · obtain ⟨hi, _, rfl⟩ := mem_addAntidiagonal.1 (mem_coe.1 hij)
    exact lt_add_of_pos_left ij.2 <| lt_of_lt_of_le ((zero_lt_orderTop_iff hox).mp hx) <|
      order_le_of_coeff_ne_zero <| Function.mem_support.mp hi
  · rintro (_ | n) hn
    · exact Set.mem_union_right _ (Set.mem_singleton 0)
    · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
      refine' Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨j, i⟩, Set.mem_iUnion.2 ⟨_, hi⟩⟩, rfl⟩
      simp only [mem_coe, mem_addAntidiagonal, mem_support, ne_eq, Set.mem_iUnion]
      exact ⟨hj, ⟨n, hi⟩, add_comm j i⟩

theorem smul_pow_finite_co_support (f : ℕ → R) (g : Γ) :
    Set.Finite {a | ((fun n ↦ f n • x ^ n) a).coeff g ≠ 0} :=
  Set.Finite.subset (pow_finite_co_support hx g) fun n hn hng => (by simp_all)

lemma supp_eq_univ_of_pos' (σ : Type*) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : y.support = Set.univ (α := σ) := by
  have hy₁ : ∀ i : σ, y i ≠ 0 := fun i => ne_zero_of_order_ne (ne_of_gt (hy i))
  exact Set.eq_univ_of_univ_subset fun i _ => by simp_all

/-- A finsupp whose every element has positive order has fintype source. -/
def Fintype_of_pos_order (σ : Type*) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : Fintype σ := by
  refine Set.fintypeOfFiniteUniv ?_
  rw [← supp_eq_univ_of_pos' σ y hy]
  exact finite_toSet y.support

lemma supp_eq_univ_of_pos (σ : Type*) [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : y.support = Finset.univ (α := σ) :=
  eq_univ_of_forall fun i => Finsupp.mem_support_iff.mpr (ne_zero_of_order_ne (ne_of_gt (hy i)))

/-!
theorem mvpow_finite_co_support {σ : Type*} {s : Finset σ} (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i ∈ s, 0 < (y i).order) (g : Γ) :
    Set.Finite {a : (s →₀ ℕ) | --{a | ((fun n ↦ ∏ i ∈ s, y i ^ n ⟨i, ⋯⟩) a).coeff g ≠ 0}
      ((fun n : (s →₀ ℕ) ↦ ∏ i ∈ s, y i ^ n ⟨i, _⟩) a).coeff g ≠ 0} := by
  refine cons_induction ?_ ?_ s
  · simp_all only [prod_empty, one_coeff, ne_eq, ite_eq_right_iff, Classical.not_imp]
    exact Set.toFinite {a | g = 0 ∧ ¬1 = 0}
  · intro i s his hs
    simp_rw [prod_cons]

    sorry
  have hpwo : Set.IsPWO (⋃ n : (σ →₀ ℕ), (∏ i, (y i) ^ (n i)).support) := by
    have hpwo' := isPWO_iUnion_support_MVpow σ (fun n => 1) y (fun i => le_of_lt (hy i))
    simp only [one_smul, supp_eq_univ_of_pos σ y hy] at hpwo'
    exact hpwo'
  by_cases hg : g ∈ ⋃ n : (σ →₀ ℕ), { g | (∏ i, (y i) ^ (n i)).coeff g ≠ 0 }
  swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
  simp_all only [one_smul]
  by_cases h0 : g = 0
  · refine Set.Finite.subset (Set.finite_singleton 0) ?_
    intro a
    contrapose
    simp only [Set.mem_singleton_iff, ne_eq, Set.mem_setOf_eq, Decidable.not_not]
    intro ha
    obtain ⟨i, hi⟩ : ∃(i : σ), a i ≠ 0 := not_forall.mp fun h ↦ ha (Finsupp.ext h)

    refine coeff_eq_zero_of_lt_order ?_

    sorry

  sorry

/-- A summable family of Hahn series given by substituting the multivariable power series generators
into positive order Hahn series.-/
def mvPowerSeriesFamily {σ : Type*} (s : Finset σ) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i ∈ s, 0 < (y i).order) : SummableFamily Γ R (s →₀ ℕ) where
  toFun n := ∏ i ∈ s, y i ^ n ⟨i, _⟩
  isPWO_iUnion_support' := by
    refine cons_induction (Set.IsPWO.mono (Set.isPWO_singleton 0) (by simp)) ?_ s
    intro i s his hp
    simp_rw [prod_cons]
    sorry
--    isPWO_iUnion_support_MVpow σ f y (fun i => le_of_lt (hy i))
  finite_co_support' g := by
    refine Set.Finite.subset (mvpow_finite_co_support y hy g) ?_
    intro n hn hng
    simp_all only [smul_coeff, smul_eq_mul, ne_eq, Set.mem_setOf_eq]
    rw [supp_eq_univ_of_pos σ y hy] at hn
    exact (ne_zero_and_ne_zero_of_mul hn).2 hng
-/

/-- A summable family of Hahn series given by substituting the power series variable `X` into the
positive order Hahn series `x`.-/
@[simps]
def PowerSeriesFamily (f : PowerSeries R) : SummableFamily Γ R ℕ where
  toFun n := (PowerSeries.coeff R n f) • x ^ n
  isPWO_iUnion_support' := isPWO_iUnion_support_smul_pow (fun n => PowerSeries.coeff R n f) x
    (zero_le_orderTop_iff.mp <| le_of_lt hx)
  finite_co_support' g := smul_pow_finite_co_support hx (fun n => PowerSeries.coeff R n f) g

theorem powerSeriesFamilyAdd (f g : PowerSeries R) :
    PowerSeriesFamily hx (f + g) = PowerSeriesFamily hx f + PowerSeriesFamily hx g := by
  ext1 n
  simp [add_smul]

theorem powerSeriesFamilySMul (r : R) (f : PowerSeries R) :
    PowerSeriesFamily hx (r • f) = (HahnSeries.single (0 : Γ) r) • (PowerSeriesFamily hx f) := by
  ext1 n
  rw [PowerSeriesFamily_toFun, LinearMapClass.map_smul, smul_apply, PowerSeriesFamily_toFun,
    HahnModule.single_zero_smul_eq_smul, smul_assoc, HahnModule.of_symm_smul,
    Equiv.symm_apply_apply]

/-- This is missing a suitable isomorphism. -/
def mvpowerseries_family_aux {σ : Type*} (s : Finset σ) (f : PowerSeries R)
    (t : SummableFamily Γ R (s →₀ ℕ)) : SummableFamily Γ R ((s →₀ ℕ) × ℕ) :=
  FamilyMul t (PowerSeriesFamily hx f)

theorem sum_coeff {α} (s : Finset α) (f : α → HahnSeries Γ R) (g : Γ) :
    (Finset.sum s f).coeff g = Finset.sum s (fun i => (f i).coeff g) :=
  cons_induction_on s (by simp) fun i t hit hc => by rw [sum_cons, sum_cons, add_coeff, hc]

theorem finsum_prod {R} [AddCommMonoid R] (f : ℕ × ℕ →₀ R) :
    ∑ᶠ (i : ℕ), ∑ᶠ (j : ℕ),  f (i, j) = ∑ᶠ (i : ℕ × ℕ), f i :=
  Eq.symm (finsum_curry (fun ab ↦ f ab) (Finsupp.finite_support f))

theorem finsum_antidiagonal_prod [AddCommMonoid α] [HasAntidiagonal α] (f : α × α →₀ R) :
    ∑ᶠ (i : α), (∑ j ∈ antidiagonal i, f j) =
    ∑ᶠ (i : α × α), f i := by
  rw [finsum_eq_sum_of_support_subset _ (s := f.support) (fun i _ => by simp_all),
    finsum_eq_sum_of_support_subset _ (s := (f.support.image fun i => i.1 + i.2)) ?_, sum_sigma']
  refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) ?_ ?_ ?_ ?_).symm
  · exact fun x _ y _ hxy => by simp_all
  · intro x hx
    simp_all only [mem_coe, Finsupp.mem_support_iff, ne_eq, coe_sigma, coe_image, Set.mem_sigma_iff,
      Set.mem_image, Prod.exists, mem_antidiagonal, and_true]
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

theorem power_series_family_supp_subset (a b : PowerSeries R) (g : Γ) :
    ((PowerSeriesFamily hx (a * b)).coeff g).support ⊆
    (((PowerSeriesFamily hx a).FamilyMul (PowerSeriesFamily hx b)).coeff g).support.image
      fun i => i.1 + i.2 := by
  simp_all only [coeff_support, PowerSeriesFamily_toFun, smul_coeff, smul_eq_mul, FamilyMul_toFun,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, Set.Finite.toFinset_subset, coe_image,
    Set.Finite.coe_toFinset, support_subset_iff, ne_eq, Set.mem_image, Function.mem_support,
    Prod.exists]
  intro n hn
  rw [PowerSeries.coeff_mul, ← ne_eq, sum_mul] at hn
  have he : ∃p ∈ antidiagonal n, ¬((PowerSeries.coeff R p.1) a *
      (PowerSeries.coeff R p.2) b * (x ^ n).coeff g) = 0 :=
    exists_ne_zero_of_sum_ne_zero hn
  use he.choose.1, he.choose.2
  refine ⟨?_, mem_antidiagonal.mp he.choose_spec.1⟩
  rw [← pow_add, mem_antidiagonal.mp he.choose_spec.1, mul_left_comm, ← mul_assoc]
  exact he.choose_spec.2

/-!  have hf : (fun (i : ℕ × ℕ) => ((PowerSeries.coeff R i.1) a • x ^ i.1 *
      (PowerSeries.coeff R i.2) b • x ^ i.2).coeff g).support.Finite := by
    refine (((PowerSeriesFamily hx a).FamilyMul
      (PowerSeriesFamily hx b)).finite_co_support' g).subset ?_
    intro y hy
    simp_all [FamilyMul, PowerSeriesFamily_toFun]
  let f : ℕ × ℕ →₀ R := Finsupp.ofSupportFinite _ hf -/

theorem power_series_family_prod_eq_family_mul (a b : PowerSeries R) :
    (PowerSeriesFamily hx (a * b)).hsum =
    ((PowerSeriesFamily hx a).FamilyMul (PowerSeriesFamily hx b)).hsum := by
  ext g
  simp only [PowerSeriesFamily_toFun, PowerSeries.coeff_mul, Finset.sum_smul, ← Finset.sum_product,
    hsum_coeff_sum, FamilyMul_toFun]
  rw [sum_subset (power_series_family_supp_subset hx a b g)]
  rw [← @HahnSeries.sum_coeff, sum_sigma', sum_coeff]
  refine (Finset.sum_of_injOn (fun x => ⟨x.1 + x.2, x⟩) ?_ ?_ ?_ ?_).symm
  · intro ij _ kl _
    simp_all
  · intro ij hij
    simp_all only [coeff_support, FamilyMul_toFun, PowerSeriesFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_coeff, smul_eq_mul, Set.Finite.coe_toFinset,
      Function.mem_support, ne_eq, coe_sigma, coe_image, Set.mem_sigma_iff, Set.mem_image,
      Prod.exists, mem_coe, mem_antidiagonal, and_true]
    use ij.1, ij.2
  · intro i hi his
    simp_all only [coeff_support, FamilyMul_toFun, PowerSeriesFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_coeff, smul_eq_mul, mem_sigma, mem_image,
      Set.Finite.mem_toFinset, Function.mem_support, ne_eq, Prod.exists, mem_antidiagonal,
      Set.Finite.coe_toFinset, Set.mem_image, not_exists, not_and]
    have hisc : ∀ j k : ℕ, ⟨j + k, (j, k)⟩ = i → (PowerSeries.coeff R k) b *
        ((PowerSeries.coeff R j) a * (x ^ j * x ^ k).coeff g) = 0 := by
      intro m n
      contrapose!
      exact his m n
    rw [mul_comm ((PowerSeries.coeff R i.snd.1) a), ← hi.2, mul_assoc, pow_add]
    exact hisc i.snd.1 i.snd.2 <| Sigma.eq hi.2 (by simp)
  · intro i _
    simp only
    rw [smul_mul_smul, pow_add]
  · intro i hi his
    simp_all only [coeff_support, FamilyMul_toFun, PowerSeriesFamily_toFun, Algebra.mul_smul_comm,
      Algebra.smul_mul_assoc, smul_coeff, smul_eq_mul, mem_image, Set.Finite.mem_toFinset,
      Function.mem_support, ne_eq, Prod.exists, Decidable.not_not, HahnSeries.sum_coeff]
    rw [@PowerSeries.coeff_mul, sum_mul] at his
    exact his

end PowerSeriesFamily

end SummableFamily

section PowerSeriesSubst

open SummableFamily

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R] {x : HahnSeries Γ R}
(hx : 0 < x.orderTop)

-- Should I call this PowerSeries.heval?

/-- The ring homomorphism from `R[[X]]` to `HahnSeries Γ R` given by sending the power series
variable `X` to a positive order element `x`. -/
def PowerSeriesSubst : PowerSeries R →ₐ[R] HahnSeries Γ R where
  toFun f := (PowerSeriesFamily hx f).hsum
  map_one' := by
    simp only [hsum, PowerSeriesFamily_toFun, PowerSeries.coeff_one, ite_smul, one_smul, zero_smul]
    ext g
    simp only
    rw [finsum_eq_single (fun i => (if i = 0 then x ^ i else 0).coeff g) (0 : ℕ)
      (fun n hn => by simp_all), pow_zero, ← zero_pow_eq 0, pow_zero]
  map_mul' a b := by
    simp only [← hsum_family_mul, power_series_family_prod_eq_family_mul]
  map_zero' := by
    simp only [hsum, PowerSeriesFamily_toFun, map_zero, zero_smul, zero_coeff, finsum_zero]
    exact rfl
  map_add' a b := by
    simp only [powerSeriesFamilyAdd, hsum_add]
  commutes' r := by
    simp only [PowerSeries.algebraMap_apply, algebraMap_apply, Algebra.id.map_eq_id,
      RingHom.id_apply, C_apply]
    ext g
    simp only [hsum_coeff, PowerSeriesFamily_toFun, smul_coeff, smul_eq_mul, PowerSeries.coeff_C]
    rw [finsum_eq_single _ 0 fun n hn => by simp_all, single_coeff, pow_zero, one_coeff, mul_ite,
      mul_one, mul_zero]
    exact rfl

theorem subst_mul {a b : PowerSeries R} :
    PowerSeriesSubst hx (a * b) = (PowerSeriesSubst hx a) * PowerSeriesSubst hx b :=
  AlgHom.map_mul (PowerSeriesSubst hx) a b

theorem subst_power_series_unit (u : (PowerSeries R)ˣ) {x : HahnSeries Γ R} (hx : x.orderTop > 0) :
    IsUnit (PowerSeriesSubst hx u) := by
  refine isUnit_iff_exists_inv.mpr ?_
  use PowerSeriesSubst hx u.inv
  rw [← subst_mul, Units.val_inv, map_one]

/-!
theorem isUnit_of_leadingCoeff_one_order_zero {x : HahnSeries Γ R}
    (hx : x.leadingCoeff = 1) (hxo : x.order = 0) :  IsUnit x := by
  have h₁ : x.leadingTerm = 1 := by
    rw [leadingTerm, ]
  have h : 0 < (x - 1).orderTop := by


theorem isUnit_of_isUnit_leadingCoeff_order_add_unit {x : HahnSeries Γ R}
    (hx : IsUnit x.leadingCoeff) (hxo : IsAddUnit x.order) : IsUnit x := by
  let ⟨⟨u, i, ui, iu⟩, h⟩ := hx
  rw [Units.val_mk] at h
  rw [h] at iu
  have h' : ((single (IsAddUnit.addUnit hxo).neg i) * x).leadingCoeff = 1 := by
    rw [leadingCoeff_mul_of_nonzero, leadingCoeff_of_single]
    exact iu
    rw [leadingCoeff_of_single]
    --by_cases hz : 0 = (1 : R)
    sorry
-/

end PowerSeriesSubst

namespace SummableFamily

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R] {x : HahnSeries Γ R}
(hx : 0 < x.orderTop)

/-- Powers of an element of positive order (or zero) form a summable family. -/
def powers : SummableFamily Γ R ℕ := PowerSeriesFamily hx (PowerSeries.mk 1)
#align hahn_series.summable_family.powers HahnSeries.SummableFamily.powers

@[simp]
theorem powers_toFun (n : ℕ) : (powers hx) n = x ^ n := by
  ext
  simp [powers]

@[simp]
theorem coe_powers : ⇑(powers hx) = HPow.hPow x := by
  ext
  simp
#align hahn_series.summable_family.coe_powers HahnSeries.SummableFamily.coe_powers

theorem embDomain_succ_smul_powers :
    (x • powers hx).embDomain ⟨Nat.succ, Nat.succ_injective⟩ =
      powers hx - ofFinsupp (Finsupp.single 0 1) := by
  apply SummableFamily.ext
  rintro (_ | n)
  · rw [embDomain_notin_range, sub_apply, powers_toFun, pow_zero, coe_ofFinsupp,
      Finsupp.single_eq_same, sub_self]
    rw [Set.mem_range, not_exists]
    exact Nat.succ_ne_zero
  · refine' Eq.trans (embDomain_image _ ⟨Nat.succ, Nat.succ_injective⟩) _
    simp only [smul_apply, powers_toFun, smul_eq_mul, coe_sub, coe_powers, coe_ofFinsupp,
      Pi.sub_apply, pow_succ', ne_eq, self_eq_add_left, add_eq_zero, one_ne_zero, and_false,
      not_false_eq_true, Finsupp.single_eq_of_ne, sub_zero]
    exact rfl
#align hahn_series.summable_family.emb_domain_succ_smul_powers HahnSeries.SummableFamily.embDomain_succ_smul_powers

theorem one_sub_self_mul_hsum_powers : (1 - x) * (powers hx).hsum = 1 := by
  rw [← hsum_smul, sub_smul 1 x (powers hx), one_smul, hsum_sub, ←
    hsum_embDomain (x • powers hx) ⟨Nat.succ, Nat.succ_injective⟩, embDomain_succ_smul_powers]
  simp only [hsum_sub, hsum_ofFinsupp, id_eq, Finsupp.sum_single_index, sub_sub_cancel]
#align hahn_series.summable_family.one_sub_self_mul_hsum_powers HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers

end SummableFamily

section Inversion

section Monoid

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R]

theorem one_minus_single_mul' {x y : HahnSeries Γ R} (r : R) (hr : r * x.leadingCoeff = 1)
    (hxy : x = y + x.leadingTerm) (hxo : IsAddUnit x.order) :
    1 - single (IsAddUnit.addUnit hxo).neg r * x = -(single (IsAddUnit.addUnit hxo).neg r * y) := by
  nth_rw 2 [hxy]
  rw [mul_add, leadingTerm_eq, single_mul_single, ← leadingCoeff_eq, hr, AddUnits.neg_eq_val_neg,
    IsAddUnit.val_neg_add, sub_add_eq_sub_sub_swap, sub_eq_neg_self, sub_eq_zero_of_eq]
  exact rfl

theorem unit_aux' (x : HahnSeries Γ R) {r : R} (hr : r * x.leadingCoeff = 1)
    (hxo : IsAddUnit x.order) : 0 < (1 - single (IsAddUnit.addUnit hxo).neg r * x).orderTop := by
  let y := (x - x.leadingTerm)
  by_cases hy : y = 0
  · have hrx : (single (IsAddUnit.addUnit hxo).neg) r * x = 1 := by
      nth_rw 2 [eq_of_sub_eq_zero hy] -- get a bad loop without `nth_rw`
      simp only [AddUnits.neg_eq_val_neg, leadingTerm_eq, ← leadingCoeff_eq, single_mul_single,
        IsAddUnit.val_neg_add, hr, single_zero_one]
    simp only [hrx, sub_self, orderTop_zero, WithTop.zero_lt_top]
  have hr' : ∀ (s : R), r * s = 0 → s = 0 :=
    fun s hs => by rw [← one_mul s, ← hr, mul_right_comm, hs, zero_mul]
  have hy' : 0 < (single (IsAddUnit.addUnit hxo).neg r * y).order := by
    rw [(order_mul_single_of_nonzero_divisor hr' hy)]
    refine pos_of_lt_add_right (a := x.order) ?_
    rw [← add_assoc, add_comm x.order, AddUnits.neg_eq_val_neg, IsAddUnit.val_neg_add, zero_add]
    exact order_lt_add_single_support_order (sub_add_cancel x x.leadingTerm).symm hy
  simp only [one_minus_single_mul' r hr (sub_add_cancel x x.leadingTerm).symm, orderTop_neg]
  exact zero_lt_orderTop_of_order hy'

theorem isUnit_of_isUnit_leadingCoeff_AddUnitOrder {x : HahnSeries Γ R} (hx : IsUnit x.leadingCoeff)
    (hxo : IsAddUnit x.order) : IsUnit x := by
  let ⟨⟨u, i, ui, iu⟩, h⟩ := hx
  rw [Units.val_mk] at h
  rw [h] at iu
  have h' := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux' x iu hxo)
  rw [sub_sub_cancel] at h'
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_eq_one _ _ h')

end Monoid

variable [LinearOrderedAddCommGroup Γ]

section CommRing

variable [CommRing R]

theorem neg_eq_addUnit_neg {G : Type*} [AddGroup G] (g : G) :
    -g = (IsAddUnit.addUnit (AddGroup.isAddUnit g)).neg := by
  simp only [AddUnits.neg_eq_val_neg, AddUnits.val_neg_eq_neg_val, IsAddUnit.addUnit_spec]
--#find_home! neg_eq_addUnit_neg --[Mathlib.Algebra.Group.Units]

theorem one_minus_single_mul (x y : HahnSeries Γ R) (r : R) (hr : r * x.leadingCoeff = 1)
    (hxy : x = y + x.leadingTerm) : 1 - single (-order x) r * x = -(single (-x.order) r * y) := by
  rw [neg_eq_addUnit_neg]
  exact one_minus_single_mul' r hr hxy (AddGroup.isAddUnit x.order)

theorem unit_aux (x : HahnSeries Γ R) {r : R} (hr : r * x.leadingCoeff = 1) :
    0 < (1 - single (-x.order) r * x).orderTop := by
  rw [neg_eq_addUnit_neg]
  exact unit_aux' x hr (AddGroup.isAddUnit x.order)
#align hahn_series.unit_aux HahnSeries.unit_aux

theorem isUnit_of_isUnit_leadingCoeff {x : HahnSeries Γ R} (hx : IsUnit x.leadingCoeff) :
    IsUnit x := by
  exact isUnit_of_isUnit_leadingCoeff_AddUnitOrder hx (AddGroup.isAddUnit x.order)

theorem isUnit_iff [IsDomain R] {x : HahnSeries Γ R} :
    IsUnit x ↔ IsUnit (x.leadingCoeff) := by
  refine { mp := ?mp, mpr := isUnit_of_isUnit_leadingCoeff }
  rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
  refine'
    isUnit_of_mul_eq_one (u.leadingCoeff) (i.leadingCoeff)
      ((mul_coeff_order_add_order u i).symm.trans _)
  rw [ui, one_coeff, if_pos]
  rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ui, order_one]
#align hahn_series.is_unit_iff HahnSeries.isUnit_iff

end CommRing

instance instField [Field R] : Field (HahnSeries Γ R) where
  __ : IsDomain (HahnSeries Γ R) := inferInstance
  inv x :=
    if x0 : x = 0 then 0
    else
      (single (-x.order)) (x.leadingCoeff)⁻¹ *
        (SummableFamily.powers (unit_aux x (inv_mul_cancel (leadingCoeff_ne_iff.mpr x0)))).hsum
  inv_zero := dif_pos rfl
  mul_inv_cancel x x0 := (congr rfl (dif_neg x0)).trans $ by
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers
        (unit_aux x (inv_mul_cancel (leadingCoeff_ne_iff.mpr x0)))
    rw [sub_sub_cancel] at h
    rw [← mul_assoc, mul_comm x, h]
  nnqsmul := _
  qsmul := _

end Inversion

end HahnSeries
