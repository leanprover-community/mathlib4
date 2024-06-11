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

variable {Γ : Type*} {R : Type*}

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
    s.hsum.coeff g = ∑ i ∈ Set.Finite.toFinset (s.finite_co_support g), (s i).coeff g := by
  rw [hsum_coeff, finsum_eq_sum _ (s.finite_co_support _)]

end AddCommMonoid

section AddCommGroup

variable [PartialOrder Γ] [AddCommGroup R] {α : Type*} {s t : SummableFamily Γ R α} {a : α}

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

variable {α β Γ' V : Type*} [PartialOrder Γ] [PartialOrder Γ'] [OrderedCancelVAdd Γ Γ']
  [NonUnitalNonAssocSemiring R] [AddCommMonoid V] [SMulWithZero R V]

/-- A convolutive scalar multiplication action of one summable family on another. -/
@[simps]
def FamilySMul (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) :
    (SummableFamily Γ' V (α × β)) where
  toFun a := (HahnModule.of R).symm (s (a.1) • ((HahnModule.of R) (t (a.2))))
  isPWO_iUnion_support' := by
    apply (s.isPWO_iUnion_support.vAdd t.isPWO_iUnion_support).mono
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
  finite_co_support' g := by
    apply ((vAddAntidiagonal s.isPWO_iUnion_support t.isPWO_iUnion_support g).finite_toSet.biUnion'
      _).subset _
    · exact fun ij _ => Function.support fun a =>
        ((s a.1).coeff ij.1) • (((HahnModule.of R) (t a.2)).coeff ij.2)
    · exact fun ij _ => by
        refine Set.Finite.subset (Set.Finite.prod (s.finite_co_support ij.1)
          (t.finite_co_support ij.2)) ?_
        simp only [support_subset_iff, ne_eq, Set.mem_prod, Function.mem_support, Prod.forall]
        exact fun a b hab => ne_zero_and_ne_zero_of_smul hab
    · exact fun a ha => by
        simp only [smul_coeff, ne_eq, Set.mem_setOf_eq] at ha
        obtain ⟨ij, hij⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
        simp only [mem_coe, mem_vAddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq,
          Function.mem_support, exists_prop, Prod.exists]
        exact ⟨ij.1, ij.2, ⟨⟨a.1, (ne_zero_and_ne_zero_of_smul hij.2).1⟩,
          ⟨a.2, (ne_zero_and_ne_zero_of_smul hij.2).2⟩,
          ((mem_vAddAntidiagonal _ _ _).mp hij.1).2.2⟩, hij.2⟩

/-!
theorem family_smul_coeff (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ') :
    (FamilySMul s t).hsum.coeff g =
      ∑ gh ∈ vAddAntidiagonal s.isPWO_iUnion_support t.isPWO_iUnion_support g,
        (∑ i ∈ Set.Finite.toFinset (s.finite_co_support gh.1), (s i).coeff gh.1) •
        (∑ i ∈ Set.Finite.toFinset (t.finite_co_support gh.2), (t i).coeff gh.2) := by
  simp only [FamilySMul_toFun, hsum_coeff_sum, HahnModule.smul_coeff, Equiv.symm_apply_apply]

  sorry

theorem hsum_family_smul (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) :
    (FamilySMul s t).hsum = (HahnModule.of R).symm (s.hsum • (HahnModule.of R) (t.hsum)) := by
  ext g
  rw [family_smul_coeff, HahnModule.smul_coeff]
  refine Eq.symm (sum_of_injOn (fun a ↦ a) (fun _ _ _ _ h ↦ h) ?_ ?_ ?_)
  · intro gh hgh
    simp_all only [mem_coe, mem_vAddAntidiagonal, mem_support, ne_eq, Set.mem_iUnion, and_true]
    constructor
    · rw [hsum_coeff_sum] at hgh
      have h' := Finset.exists_ne_zero_of_sum_ne_zero hgh.1
      simp_all only [Set.Finite.mem_toFinset, Function.mem_support, ne_eq, and_self]
    · have h := hgh.2.1


      sorry
  · sorry
  · sorry
-/

end SMul

section Semiring

variable [OrderedCancelAddCommMonoid Γ] [Semiring R] {α : Type*}

instance : SMul (HahnSeries Γ R) (SummableFamily Γ R α) where
  smul x s :=
    { toFun := fun a => x * s a
      isPWO_iUnion_support' := by
        apply (x.isPWO_support.add s.isPWO_iUnion_support).mono
        refine Set.Subset.trans (Set.iUnion_mono fun a => support_mul_subset_add_support) ?_
        intro g
        simp only [Set.mem_iUnion, exists_imp]
        exact fun a ha => (Set.add_subset_add (Set.Subset.refl _) (Set.subset_iUnion _ a)) ha
      finite_co_support' := fun g => by
        apply ((addAntidiagonal x.isPWO_support s.isPWO_iUnion_support g).finite_toSet.biUnion'
            fun ij _ => ?_).subset fun a ha => ?_
        · exact fun ij _ => Function.support fun a => (s a).coeff ij.2
        · apply s.finite_co_support
        · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support ha
          simp only [exists_prop, Set.mem_iUnion, mem_addAntidiagonal, mul_coeff, mem_support,
            isPWO_support, Prod.exists]
          exact ⟨i, j, mem_coe.2 (mem_addAntidiagonal.2 ⟨hi, Set.mem_iUnion.2 ⟨a, hj⟩, rfl⟩), hj⟩ }

@[simp]
theorem smul_apply {x : HahnSeries Γ R} {s : SummableFamily Γ R α} {a : α} : (x • s) a = x * s a :=
  rfl
#align hahn_series.summable_family.smul_apply HahnSeries.SummableFamily.smul_apply

instance : Module (HahnSeries Γ R) (SummableFamily Γ R α) where
  smul := (· • ·)
  smul_zero _ := ext fun _ => mul_zero _
  zero_smul _ := ext fun _ => zero_mul _
  one_smul _ := ext fun _ => one_mul _
  add_smul _ _ _  := ext fun _ => add_mul _ _ _
  smul_add _ _ _ := ext fun _ => mul_add _ _ _
  mul_smul _ _ _ := ext fun _ => mul_assoc _ _ _

@[simp]
theorem hsum_smul {x : HahnSeries Γ R} {s : SummableFamily Γ R α} : (x • s).hsum = x * s.hsum := by
  ext g
  simp only [mul_coeff, hsum_coeff, smul_apply]
  refine
    (Eq.trans (finsum_congr fun a => ?_)
          (finsum_sum_comm (addAntidiagonal x.isPWO_support s.isPWO_iUnion_support g)
            (fun i ij => x.coeff (Prod.fst ij) * (s i).coeff ij.snd) ?_)).trans
      ?_
  · refine sum_subset (addAntidiagonal_mono_right
      (Set.subset_iUnion (fun j => support (toFun s j)) a)) ?_
    rintro ⟨i, j⟩ hU ha
    rw [mem_addAntidiagonal] at *
    rw [Classical.not_not.1 fun con => ha ⟨hU.1, con, hU.2.2⟩, mul_zero]
  · rintro ⟨i, j⟩ _
    refine (s.finite_co_support j).subset ?_
    simp_rw [Function.support_subset_iff', Function.mem_support, Classical.not_not]
    intro a ha
    rw [ha, mul_zero]
  · refine (sum_congr rfl ?_).trans (sum_subset (addAntidiagonal_mono_right ?_) ?_).symm
    · rintro ⟨i, j⟩ _
      rw [mul_finsum]
      apply s.finite_co_support
    · intro x hx
      simp only [Set.mem_iUnion, Ne, mem_support]
      contrapose! hx
      simp [hx]
    · rintro ⟨i, j⟩ hU ha
      rw [mem_addAntidiagonal] at *
      rw [← hsum_coeff, Classical.not_not.1 fun con => ha ⟨hU.1, con, hU.2.2⟩,
        mul_zero]
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

/-- Multiplication of summable families - should rewrite in terms of FamilySMul. -/
def FamilyMul {β : Type*} (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    (SummableFamily Γ R (α × β)) where
  toFun a := s (a.1) * t (a.2)
  isPWO_iUnion_support' := by
    apply (s.isPWO_iUnion_support.add t.isPWO_iUnion_support).mono
    refine Set.Subset.trans (Set.iUnion_mono fun a => support_mul_subset_add_support) ?_
    simp_all only [Set.iUnion_subset_iff, Prod.forall]
    exact fun a b => Set.add_subset_add (Set.subset_iUnion_of_subset a fun x y ↦ y)
      (Set.subset_iUnion_of_subset b fun x y ↦ y)
  finite_co_support' g := by
    apply ((addAntidiagonal s.isPWO_iUnion_support t.isPWO_iUnion_support g).finite_toSet.biUnion'
      _).subset _
    · exact fun ij _ => Function.support fun a => ((s a.1).coeff ij.1) * ((t a.2).coeff ij.2)
    · exact fun ij _ => by
        refine Set.Finite.subset (Set.Finite.prod (s.finite_co_support ij.1)
          (t.finite_co_support ij.2)) ?_
        simp only [support_subset_iff, ne_eq, Set.mem_prod, Function.mem_support, Prod.forall]
        exact fun a b hab => ne_zero_and_ne_zero_of_mul hab
    · exact fun a ha => by
        simp only [mul_coeff, ne_eq, Set.mem_setOf_eq] at ha
        obtain ⟨ij, hij⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
        simp only [mem_coe, mem_addAntidiagonal, Set.mem_iUnion, mem_support, ne_eq,
          Function.mem_support, exists_prop, Prod.exists]
        exact ⟨ij.1, ij.2, ⟨⟨a.1, (ne_zero_and_ne_zero_of_mul hij.2).1⟩,
          ⟨a.2, (ne_zero_and_ne_zero_of_mul hij.2).2⟩, (mem_addAntidiagonal.mp hij.1).2.2⟩, hij.2⟩



--def piFamily {σ : Type*} [Fintype σ] (β : σ → Type*)

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

section powers

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
    isPWO_iUnion_support_powers x (zero_le_order_of_orderTop <| le_of_lt hx)
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
    exact lt_add_of_pos_left ij.2 <| lt_of_lt_of_le (zero_lt_order_of_orderTop hx hox) <|
      order_le_of_coeff_ne_zero <| Function.mem_support.mp hi
  · rintro (_ | n) hn
    · exact Set.mem_union_right _ (Set.mem_singleton 0)
    · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
      refine' Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨j, i⟩, Set.mem_iUnion.2 ⟨_, hi⟩⟩, rfl⟩
      simp only [mem_coe, mem_addAntidiagonal, mem_support, ne_eq, Set.mem_iUnion]
      exact ⟨hj, ⟨n, hi⟩, add_comm j i⟩

theorem smul_pow_finite_co_support (f : ℕ → R) (g : Γ) :
    Set.Finite {a | ((fun n ↦ f n • x ^ n) a).coeff g ≠ 0} := by
  refine Set.Finite.subset (pow_finite_co_support hx g) ?_
  intro n hn hng
  simp_all

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
theorem mvpow_finite_co_support (σ : Type*) [Fintype σ] (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) (g : Γ) :
    Set.Finite {a : (σ →₀ ℕ) |
      ((fun n : (σ →₀ ℕ) ↦ ∏ i, y i ^ n i) a).coeff g ≠ 0} := by
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
@[simps]
def mvPowerSeriesFamily (σ : Type*) [Fintype σ] (f : (σ →₀ ℕ) → R) (y : σ →₀ HahnSeries Γ R)
    (hy : ∀ i : σ, 0 < (y i).order) : SummableFamily Γ R (σ →₀ ℕ) where
  toFun n := f n • ∏ i ∈ y.support, y i ^ n i
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_MVpow σ f y (fun i => le_of_lt (hy i))
  finite_co_support' g := by
    refine Set.Finite.subset (mvpow_finite_co_support σ y hy g) ?_
    intro n hn hng
    simp_all only [smul_coeff, smul_eq_mul, ne_eq, Set.mem_setOf_eq]
    rw [supp_eq_univ_of_pos σ y hy] at hn
    exact (ne_zero_and_ne_zero_of_mul hn).2 hng
-/

/-- A summable family of Hahn series given by substituting the power series variable `X` into the
positive order Hahn series `x`.-/
@[simps]
def powerSeriesFamily (f : PowerSeries R) : SummableFamily Γ R ℕ where
  toFun n := (PowerSeries.coeff R n f) • x ^ n
  isPWO_iUnion_support' := isPWO_iUnion_support_smul_pow (fun n => PowerSeries.coeff R n f) x
    (zero_le_order_of_orderTop <| le_of_lt hx)
  finite_co_support' g := smul_pow_finite_co_support hx (fun n => PowerSeries.coeff R n f) g

theorem powerSeriesFamilyAdd (f g : PowerSeries R) :
    powerSeriesFamily hx (f + g) = powerSeriesFamily hx f + powerSeriesFamily hx g := by
  ext1 n
  simp [add_smul]

theorem powerSeriesFamilySMul (r : R) (f : PowerSeries R) :
    powerSeriesFamily hx (r • f) = (single (0 : Γ) r) • (powerSeriesFamily hx f) := by
  ext1 n
  rw [powerSeriesFamily_toFun, LinearMapClass.map_smul, smul_apply, powerSeriesFamily_toFun,
    single_zero_mul_eq_smul, smul_assoc]

/-!
/-- A summable family of Hahn series given by subtituting ... -/
def powerSeriesProdFamily (f g : PowerSeries R) : SummableFamily Γ R (ℕ × ℕ) where
  toFun n := ((PowerSeries.coeff R n.1 f) * (PowerSeries.coeff R n.2 g)) • x ^ (n.1 + n.2)
  isPWO_iUnion_support' := (x.isPWO_support'.addSubmonoid_closure fun _ hg => le_trans
    (zero_le_order_of_orderTop <| le_of_lt hx)
    (order_le_of_coeff_ne_zero (Function.mem_support.mp hg))).mono
    (Set.iUnion_subset fun n => (Function.support_const_smul_subset
      ((PowerSeries.coeff R n.1 f) * (PowerSeries.coeff R n.2 g)) (x ^ (n.1 + n.2)).coeff).trans
      (support_pow_subset_closure x (n.1 + n.2)))
  finite_co_support' a := by
    let s : ℕ → Set (ℕ × ℕ) :=
      fun n => {k ∈ addAntidiagonal _ _ n | (((PowerSeries.coeff R k.1) f *
        (PowerSeries.coeff R k.2) g) • x ^ (k.1 + k.2)).coeff a ≠ 0}
    let t : Set ℕ := {k | ((fun n ↦ x ^ n) k).coeff a ≠ 0}
    have ht := (pow_finite_co_support hx a)
    have hs : Prop := sorry --finite antidiagonal: ∀ i ∈ t, (s i).Finite
      --(fun k => Set.AddAntidiagonal.finite_of_isPWO ?_ ?_ k)
    have he : Prop := sorry--coeff a is zero away from cosupport
    refine Set.Finite.subset (Set.Finite.iUnion ht hs he) ?_ -- need to show cosupport ⊆ iUnion
    sorry -- try finsum_mem_biUnion

theorem xxx (n : ℕ) : Finite (Set.addAntidiagonal Set.univ Set.univ n) :=
  Set.AddAntidiagonal.finite_of_isWF (Set.isWF_univ_iff.mpr wellFounded_lt)
    (Set.isWF_univ_iff.mpr wellFounded_lt) n


theorem finsumAntidiagonal {R} [AddCommMonoid R] (f : ℕ × ℕ →₀ R) :
    ∑ᶠ (i : ℕ), (∑ i_1 ∈ antidiagonal i, f i_1) = ∑ᶠ (i : ℕ × ℕ), f i := by

  -- sum_bij or sum_nbij with sum_sigma?
  sorry
-/

theorem sum_coeff {α} (s : Finset α) (f : α → HahnSeries Γ R) (g : Γ) :
    (Finset.sum s f).coeff g = Finset.sum s (fun i => (f i).coeff g) := by
  refine cons_induction_on s ?_ ?_
  · simp
  · intro i t hit hc
    rw [sum_cons, sum_cons, add_coeff, hc]

theorem finsum_prod {R} [AddCommMonoid R] (f : ℕ × ℕ →₀ R) :
    ∑ᶠ (i : ℕ), ∑ᶠ (j : ℕ),  f (i, j) = ∑ᶠ (i : ℕ × ℕ), f i := by
  exact Eq.symm (finsum_curry (fun ab ↦ f ab) (Finsupp.finite_support f))

/-!
/-- The ring homomorphism from `R[[X]]` to `HahnSeries Γ R` given by sending the power series
variable `X` to a positive order element `x`. -/
def powerSeriesComp : PowerSeries R →ₐ[R] HahnSeries Γ R where
  toFun f := (powerSeriesFamily hx f).hsum
  map_one' := by
    simp only [hsum, powerSeriesFamily_toFun, PowerSeries.coeff_one, ite_smul, one_smul, zero_smul]
    ext g
    simp only
    rw [finsum_eq_single (fun i => (if i = 0 then x ^ i else 0).coeff g) (0 : ℕ)
      (fun n hn => by simp_all), pow_zero, ← zero_pow_eq 0, pow_zero]
  map_mul' a b := by
    ext g
    simp only [hsum_coeff_sum, powerSeriesFamily_toFun]

    simp only [powerSeriesFamily_toFun, mul_coeff, PowerSeries.coeff_mul,
      Finset.sum_smul, smul_coeff, ← Finset.sum_product, sum_coeff]

    -- write f * g as a double sum. write each coefficient of X ^ n as a finite sum.
    -- make a summable family parametrized by ℕ × ℕ.
    -- Finset.sum_product and Finset.sum_mul_sum
    -- write more haves and use nbij theorems
    sorry
  map_zero' := by
    simp only [hsum, powerSeriesFamily_toFun, map_zero, zero_smul, zero_coeff, finsum_zero]
    exact rfl
  map_add' a b := by
    simp [powerSeriesFamilyAdd]
  commutes' r := by
    simp only
    rw [@PowerSeries.algebraMap_apply]
    rw [@algebraMap_apply]
    simp only [Algebra.id.map_eq_id, RingHom.id_apply, C_apply]
    ext g
    simp only [hsum_coeff, powerSeriesFamily_toFun, smul_coeff, smul_eq_mul, PowerSeries.coeff_C,
      ite_mul, zero_mul]
    rw [finsum_eq_single _ 0 ?_]
    · simp only [↓reduceIte, pow_zero, one_coeff, mul_ite, mul_one, mul_zero, single_coeff]
      aesop
    · intro n hn
      simp_all

-/
-- define composition with any `f : R[[X]]`.  Show that multiplication of substituted power series
--corresponds to substitution of products., i.e., elements of strictly positive orderTop yield
-- ring homomorphisms.

/-- Powers of an element of positive order (or zero) form a summable family. -/
@[simps]
def powers : SummableFamily Γ R ℕ where
  toFun n := x ^ n
  isPWO_iUnion_support' := isPWO_iUnion_support_powers x (zero_le_order_of_orderTop <| le_of_lt hx)
  finite_co_support' g := by
    have h : {a | ((fun n ↦ x ^ n) a).coeff g ≠ 0} ⊆ {n | (x ^ n).coeff g ≠ 0} := by
      intro n hn
      simp_all only [ne_eq, Set.mem_setOf_eq, not_false_eq_true]
    exact Set.Finite.subset (pow_finite_co_support hx g) h
#align hahn_series.summable_family.powers HahnSeries.SummableFamily.powers

@[simp]
theorem coe_powers : ⇑(powers hx) = HPow.hPow x :=
  rfl
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
    simp only [smul_apply, powers_toFun, Algebra.mul_smul_comm, coe_sub, coe_ofFinsupp,
      Pi.sub_apply, ne_eq, not_false_eq_true, Finsupp.single_eq_of_ne, sub_zero, pow_succ']
#align hahn_series.summable_family.emb_domain_succ_smul_powers HahnSeries.SummableFamily.embDomain_succ_smul_powers

theorem one_sub_self_mul_hsum_powers : (1 - x) * (powers hx).hsum = 1 := by
  rw [← hsum_smul, sub_smul 1 x (powers hx), one_smul, hsum_sub, ←
    hsum_embDomain (x • powers hx) ⟨Nat.succ, Nat.succ_injective⟩, embDomain_succ_smul_powers]
  simp only [hsum_sub, hsum_ofFinsupp, id_eq, Finsupp.sum_single_index, sub_sub_cancel]
#align hahn_series.summable_family.one_sub_self_mul_hsum_powers HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers

end powers

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
      simp only [leadingTerm_eq, single_mul_single, AddUnits.neg_eq_val_neg, IsAddUnit.val_neg_add,
        hr, ← leadingCoeff_eq]
      exact rfl
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
        (SummableFamily.powers (unit_aux x (inv_mul_cancel (leadingCoeff_ne_iff.mp x0)))).hsum
  inv_zero := dif_pos rfl
  mul_inv_cancel x x0 := (congr rfl (dif_neg x0)).trans $ by
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers
        (unit_aux x (inv_mul_cancel (leadingCoeff_ne_iff.mp x0)))
    rw [sub_sub_cancel] at h
    rw [← mul_assoc, mul_comm x, h]
  nnqsmul := _
  qsmul := _

end Inversion

end HahnSeries
