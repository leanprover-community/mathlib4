/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Summable families of Hahn Series
We introduce a notion of formal summability for families of Hahn series, and define a formal sum
function. This theory is applied to characterize invertible Hahn series whose coefficients are in a
commutative domain.

## Main Definitions
  * A `HahnSeries.SummableFamily` is a family of Hahn series such that the union of the supports
  is partially well-ordered and only finitely many are nonzero at any given coefficient. Note that
  this is different from `Summable` in the valuation topology, because there are topologically
  summable families that do not satisfy the axioms of `HahnSeries.SummableFamily`, and formally
  summable families whose sums do not converge topologically.
  * The formal sum, `HahnSeries.SummableFamily.hsum` can be bundled as a `LinearMap` via
  `HahnSeries.SummableFamily.lsum`.
  * `FamilySMul`, `FamilyMul`, and `PiFamily` are the pointwise scalar multiplication and
  multiplication operations on a pair or collection of summable families.

## Main results
  * `FamilySMul`, `FamilyMul`, and `PiFamily` are compatible with `hsum`.  That is, the product of
  sums is equal to the sum of pointwise products.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/


open Finset Function

open Pointwise

noncomputable section

variable {Γ Γ' R V α β σ : Type*}

namespace HahnSeries

section

/-- A family of Hahn series whose formal coefficient-wise sum is a Hahn series.  For each
coefficient of the sum to be well-defined, we require that only finitely many series are nonzero at
any given coefficient.  For the formal sum to be a Hahn series, we require that the union of the
supports of the constituent series is partially well-ordered. -/
structure SummableFamily (Γ) (R) [PartialOrder Γ] [AddCommMonoid R] (α : Type*) where
  /-- A parametrized family of Hahn series. -/
  toFun : α → HahnSeries Γ R
  isPWO_iUnion_support' : Set.IsPWO (⋃ a : α, (toFun a).support)
  finite_co_support' : ∀ g : Γ, { a | (toFun a).coeff g ≠ 0 }.Finite

end

namespace SummableFamily

section AddCommMonoid

variable [PartialOrder Γ] [AddCommMonoid R]

instance : FunLike (SummableFamily Γ R α) α (HahnSeries Γ R) where
  coe := toFun
  coe_injective' | ⟨_, _, _⟩, ⟨_, _, _⟩, rfl => rfl

theorem isPWO_iUnion_support (s : SummableFamily Γ R α) : Set.IsPWO (⋃ a : α, (s a).support) :=
  s.isPWO_iUnion_support'

theorem finite_co_support (s : SummableFamily Γ R α) (g : Γ) :
    (Function.support fun a => (s a).coeff g).Finite :=
  s.finite_co_support' g

theorem coe_injective : @Function.Injective (SummableFamily Γ R α) (α → HahnSeries Γ R) (⇑) :=
  DFunLike.coe_injective

@[ext]
theorem ext {s t : SummableFamily Γ R α} (h : ∀ a : α, s a = t a) : s = t :=
  DFunLike.ext s t h

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

theorem add_apply {s t : SummableFamily Γ R α} {a : α} : (s + t) a = s a + t a :=
  rfl

@[simp]
theorem coe_zero : ((0 : SummableFamily Γ R α) : α → HahnSeries Γ R) = 0 :=
  rfl

theorem zero_apply {a : α} : (0 : SummableFamily Γ R α) a = 0 :=
  rfl

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

@[simp]
theorem coeff_hsum {s : SummableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g :=
  rfl

@[deprecated (since := "2025-01-31")] alias hsum_coeff := coeff_hsum

@[simp]
theorem hsum_zero : (0 : SummableFamily Γ R α).hsum = 0 := by
  ext
  simp

theorem support_hsum_subset {s : SummableFamily Γ R α} : s.hsum.support ⊆ ⋃ a : α, (s a).support :=
  fun g hg => by
  rw [mem_support, coeff_hsum, finsum_eq_sum _ (s.finite_co_support _)] at hg
  obtain ⟨a, _, h2⟩ := exists_ne_zero_of_sum_ne_zero hg
  rw [Set.mem_iUnion]
  exact ⟨a, h2⟩

@[simp]
theorem hsum_add {s t : SummableFamily Γ R α} : (s + t).hsum = s.hsum + t.hsum := by
  ext g
  simp only [coeff_hsum, coeff_add, add_apply]
  exact finsum_add_distrib (s.finite_co_support _) (t.finite_co_support _)

theorem coeff_hsum_eq_sum_of_subset {s : SummableFamily Γ R α} {g : Γ} {t : Finset α}
    (h : { a | (s a).coeff g ≠ 0 } ⊆ t) : s.hsum.coeff g = ∑ i ∈ t, (s i).coeff g := by
  simp only [coeff_hsum, finsum_eq_sum _ (s.finite_co_support _)]
  exact sum_subset (Set.Finite.toFinset_subset.mpr h) (by simp)

@[deprecated (since := "2025-01-31")] alias hsum_coeff_eq_sum_of_subset :=
  coeff_hsum_eq_sum_of_subset

theorem coeff_hsum_eq_sum {s : SummableFamily Γ R α} {g : Γ} :
    s.hsum.coeff g = ∑ i ∈ (s.coeff g).support, (s i).coeff g := by
  simp only [coeff_hsum, finsum_eq_sum _ (s.finite_co_support _), coeff_support]

@[deprecated (since := "2025-01-31")] alias hsum_coeff_eq_sum := coeff_hsum_eq_sum

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
  simp only [coeff_hsum, single_toFun, finsum_unique]

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
  simp only [coeff_hsum, Equiv_toFun]
  exact finsum_eq_of_bijective e.symm (Equiv.bijective e.symm) fun x => rfl

theorem hsum_subsingleton [Subsingleton α] {s : SummableFamily Γ R α} (a : α) :
    s.hsum = s a := by
  haveI : Unique α := uniqueOfSubsingleton a
  let e : Unit ≃ α := Equiv.ofUnique Unit α
  have he : ∀u : Unit, e u = a := fun u ↦ (fun f ↦ (Equiv.apply_eq_iff_eq_symm_apply f).mpr) e rfl
  have hs : Equiv e.symm s = single (s a) := by ext; simp [he]
  rw [← hsum_equiv e.symm, hs, hsum_single]

/-- The summable family given by multiplying every series in a summable family by a scalar. -/
@[simps]
def smulFamily [AddCommMonoid V] [SMulWithZero R V] (f : α → R) (s : SummableFamily Γ V α) :
    SummableFamily Γ V α where
  toFun a := (f a) • s a
  isPWO_iUnion_support' := by
    refine Set.IsPWO.mono s.isPWO_iUnion_support fun g hg => ?_
    simp_all only [Set.mem_iUnion, mem_support, coeff_smul, ne_eq]
    obtain ⟨i, hi⟩ := hg
    exact Exists.intro i <| right_ne_zero_of_smul hi
  finite_co_support' g := by
    refine Set.Finite.subset (s.finite_co_support g) fun i hi => ?_
    simp_all only [coeff_smul, ne_eq, Set.mem_setOf_eq, Function.mem_support]
    exact right_ne_zero_of_smul hi

theorem hsum_smulFamily [AddCommMonoid V] [SMulWithZero R V] (f : α → R)
    (s : SummableFamily Γ V α) (g : Γ) :
    (smulFamily f s).hsum.coeff g = ∑ᶠ i, (f i) • ((s i).coeff g) :=
  rfl

theorem le_hsum_support_mem {s : SummableFamily Γ R α} {g g' : Γ}
    (hg : ∀ b : α, ∀ g' ∈ (s b).support, g ≤ g') (hg' : g' ∈ s.hsum.support) : g ≤ g' := by
  rw [mem_support, coeff_hsum_eq_sum] at hg'
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hg'
  exact hg i g' hi

theorem hsum_orderTop_of_le {s : SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (s a).orderTop)
    (hg : ∀ b : α, ∀ g' ∈ (s b).support, g ≤ g') (hna : ∀b : α, b ≠ a → (s b).coeff g = 0) :
    s.hsum.orderTop = g :=
  orderTop_eq_of_le (ne_of_eq_of_ne (by rw [coeff_hsum, finsum_eq_single (fun i ↦ (s i).coeff g) a
    hna]) (coeff_orderTop_ne ha.symm)) fun _ hg' => le_hsum_support_mem hg hg'

theorem hsum_leadingCoeff_of_le {s : SummableFamily Γ R α} {g : Γ} {a : α} (ha : g = (s a).orderTop)
    (hg : ∀ b : α, ∀ g' ∈ (s b).support, g ≤ g') (hna : ∀b : α, b ≠ a → (s b).coeff g = 0) :
    s.hsum.leadingCoeff = (s a).coeff g := by
  rw [leadingCoeff, hsum_orderTop_of_le ha hg hna, coeffTop_eq, coeff_hsum,
    finsum_eq_single (fun i ↦ (s i).coeff g) a hna]

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
        simp only [coeff_neg, Pi.neg_apply, Ne, neg_eq_zero]
        exact s.finite_co_support g }⟩

instance : AddCommGroup (SummableFamily Γ R α) :=
  { inferInstanceAs (AddCommMonoid (SummableFamily Γ R α)) with
    zsmul := zsmulRec
    neg_add_cancel := fun a => by
      ext
      apply neg_add_cancel }

@[simp]
theorem coe_neg : ⇑(-s) = -s :=
  rfl

theorem neg_apply : (-s) a = -s a :=
  rfl

@[simp]
theorem coe_sub : ⇑(s - t) = s - t :=
  rfl

theorem sub_apply : (s - t) a = s a - t a :=
  rfl

end AddCommGroup

section SMul

variable [PartialOrder Γ] [PartialOrder Γ'] [AddCommMonoid V]

instance [Zero R] [SMulWithZero R V] : SMul R (SummableFamily Γ' V β) :=
  ⟨fun r t =>
    { toFun := r • t
      isPWO_iUnion_support' := t.isPWO_iUnion_support.mono (Set.iUnion_mono fun i =>
        Pi.smul_apply r t i ▸ Function.support_const_smul_subset r _)
      finite_co_support' := by
        intro g
        refine (t.finite_co_support g).subset ?_
        intro i hi
        simp only [Pi.smul_apply, coeff_smul, ne_eq, Set.mem_setOf_eq] at hi
        simp only [Function.mem_support, ne_eq]
        exact right_ne_zero_of_smul hi } ⟩

variable [AddCommMonoid R] [SMulWithZero R V]

theorem smul_support_subset_prod (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (gh : Γ × Γ') :
    (Function.support fun (i : α × β) ↦ (s i.1).coeff gh.1 • (t i.2).coeff gh.2) ⊆
    ((s.finite_co_support' gh.1).prod (t.finite_co_support' gh.2)).toFinset := by
    intro ab hab
    simp_all only [Function.mem_support, ne_eq, Set.Finite.coe_toFinset, Set.mem_prod,
      Set.mem_setOf_eq]
    refine ⟨left_ne_zero_of_smul hab, right_ne_zero_of_smul hab⟩

theorem smul_support_finite (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (gh : Γ × Γ') :
    (Function.support fun (i : α × β) ↦ (s i.1).coeff gh.1 • (t i.2).coeff gh.2).Finite :=
  Set.Finite.subset (Set.toFinite ((s.finite_co_support' gh.1).prod
    (t.finite_co_support' gh.2)).toFinset) (smul_support_subset_prod s t gh)

variable [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ']

open HahnModule

theorem isPWO_iUnion_support_prod_smul {s : α → HahnSeries Γ R}
    {t : β → HahnSeries Γ' V} (hs : (⋃ a, (s a).support).IsPWO) (ht : (⋃ b, (t b).support).IsPWO) :
    (⋃ (a : α × β), ((fun a ↦ (HahnModule.of R).symm
      ((s a.1) • (HahnModule.of R) (t a.2))) a).support).IsPWO := by
  apply (hs.vadd ht).mono
  have hsupp : ∀ a : α × β, support ((fun a ↦ (HahnModule.of R).symm
      (s a.1 • (HahnModule.of R) (t a.2))) a) ⊆ (s a.1).support +ᵥ (t a.2).support := by
    intro a
    apply Set.Subset.trans (fun x hx => _) support_vaddAntidiagonal_subset_vadd
    · exact (s a.1).isPWO_support
    · exact (t a.2).isPWO_support
    intro x hx
    contrapose! hx
    simp only [Set.mem_setOf_eq, not_nonempty_iff_eq_empty] at hx
    rw [mem_support, not_not, HahnModule.coeff_smul, hx, sum_empty]
  refine Set.Subset.trans (Set.iUnion_mono fun a => (hsupp a)) ?_
  simp_all only [Set.iUnion_subset_iff, Prod.forall]
  exact fun a b => Set.vadd_subset_vadd (Set.subset_iUnion_of_subset a fun x y ↦ y)
    (Set.subset_iUnion_of_subset b fun x y ↦ y)

theorem finite_co_support_prod_smul (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (g : Γ') :
    Finite {(a : α × β) | ((fun (a : α × β) ↦ (HahnModule.of R).symm (s a.1 • (HahnModule.of R)
      (t a.2))) a).coeff g ≠ 0} := by
  apply ((VAddAntidiagonal s.isPWO_iUnion_support t.isPWO_iUnion_support g).finite_toSet.biUnion'
    _).subset _
  · exact fun ij _ => Function.support fun a =>
      ((s a.1).coeff ij.1) • ((t a.2).coeff ij.2)
  · exact fun gh _ => smul_support_finite s t gh
  · exact fun a ha => by
      simp only [coeff_smul, ne_eq, Set.mem_setOf_eq] at ha
      obtain ⟨ij, hij⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
      simp only [mem_coe, mem_vaddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq,
        Function.mem_support, exists_prop, Prod.exists]
      exact ⟨ij.1, ij.2, ⟨⟨a.1, left_ne_zero_of_smul hij.2⟩, ⟨a.2, right_ne_zero_of_smul hij.2⟩,
        ((mem_vaddAntidiagonal _ _ _).mp hij.1).2.2⟩, hij.2⟩

/-- An elementwise scalar multiplication of one summable family on another. -/
@[simps]
def smul (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) : SummableFamily Γ' V (α × β) where
  toFun ab := (of R).symm (s (ab.1) • ((of R) (t (ab.2))))
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_prod_smul s.isPWO_iUnion_support t.isPWO_iUnion_support
  finite_co_support' g := finite_co_support_prod_smul s t g

@[deprecated (since := "2024-11-17")] noncomputable alias FamilySMul := smul

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

theorem sum_vAddAntidiagonal_eq (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (g : Γ') (a : α × β) :
    ∑ x ∈ VAddAntidiagonal (s a.1).isPWO_support' (t a.2).isPWO_support' g, (s a.1).coeff x.1 •
      (t a.2).coeff x.2 = ∑ x ∈ VAddAntidiagonal s.isPWO_iUnion_support' t.isPWO_iUnion_support' g,
      (s a.1).coeff x.1 • (t a.2).coeff x.2 := by
  refine sum_subset (fun gh hgh => ?_) fun gh hgh h => ?_
  · simp_all only [mem_vaddAntidiagonal, Function.mem_support, Set.mem_iUnion, mem_support]
    refine ⟨Exists.intro a.1 hgh.1, Exists.intro a.2 hgh.2.1, trivial⟩
  · by_cases hs : (s a.1).coeff gh.1 = 0
    · exact smul_eq_zero_of_left hs ((t a.2).coeff gh.2)
    · simp_all

theorem coeff_smul {R} {V} [Semiring R] [AddCommMonoid V] [Module R V]
    (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ') :
    (smul s t).hsum.coeff g = ∑ gh ∈ VAddAntidiagonal s.isPWO_iUnion_support
      t.isPWO_iUnion_support g, (s.hsum.coeff gh.1) • (t.hsum.coeff gh.2) := by
  rw [coeff_hsum]
  simp only [coeff_hsum_eq_sum, smul_toFun, HahnModule.coeff_smul, Equiv.symm_apply_apply]
  simp_rw [sum_vAddAntidiagonal_eq, Finset.smul_sum, Finset.sum_smul]
  rw [← sum_finsum_comm _ _ <| fun gh _ => smul_support_finite s t gh]
  refine sum_congr rfl fun gh _ => ?_
  rw [finsum_eq_sum _ (smul_support_finite s t gh), ← sum_product_right']
  refine sum_subset (fun ab hab => ?_) (fun ab _ hab => by simp_all)
  have hsupp := smul_support_subset_prod s t gh
  simp_all only [mem_vaddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq, Set.Finite.mem_toFinset,
    Function.mem_support, Set.Finite.coe_toFinset, support_subset_iff, Set.mem_prod,
    Set.mem_setOf_eq, Prod.forall, coeff_support, mem_product]
  exact hsupp ab.1 ab.2 hab

@[deprecated (since := "2024-11-17")] alias family_smul_coeff := coeff_smul

theorem smul_hsum {R} {V} [Semiring R] [AddCommMonoid V] [Module R V]
    (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) :
    (smul s t).hsum = (of R).symm (s.hsum • (of R) (t.hsum)) := by
  ext g
  rw [coeff_smul s t g, HahnModule.coeff_smul, Equiv.symm_apply_apply]
  refine Eq.symm (sum_of_injOn (fun a ↦ a) (fun _ _ _ _ h ↦ h) (fun _ hgh => ?_)
    (fun gh _ hgh => ?_) fun _ _ => by simp)
  · simp_all only [mem_coe, mem_vaddAntidiagonal, mem_support, ne_eq, Set.mem_iUnion, and_true]
    constructor
    · rw [coeff_hsum_eq_sum] at hgh
      have h' := Finset.exists_ne_zero_of_sum_ne_zero hgh.1
      simp_all
    · by_contra hi
      simp_all
  · simp only [Set.image_id', mem_coe, mem_vaddAntidiagonal, mem_support, ne_eq, not_and] at hgh
    by_cases h : s.hsum.coeff gh.1 = 0
    · exact smul_eq_zero_of_left h (t.hsum.coeff gh.2)
    · simp_all

@[deprecated (since := "2024-11-17")] alias hsum_family_smul := smul_hsum

instance [AddCommMonoid R] [SMulWithZero R V] : SMul (HahnSeries Γ R) (SummableFamily Γ' V β) where
  smul x t := Equiv (Equiv.punitProd β) <| smul (single x) t

theorem smul_eq {x : HahnSeries Γ R} {t : SummableFamily Γ' V β} :
    x • t = Equiv (Equiv.punitProd β) (smul (single x) t) :=
  rfl

@[simp]
theorem smul_apply {x : HahnSeries Γ R}
    {s : SummableFamily Γ' V α} {a : α} :
    (x • s) a = (HahnModule.of R).symm (x • HahnModule.of R (s a)) :=
  rfl

@[simp]
theorem hsum_smul_module (R) (V) [Semiring R] [AddCommMonoid V] [Module R V] {x : HahnSeries Γ R}
    {s : SummableFamily Γ' V α} :
    (x • s).hsum = (of R).symm (x • of R s.hsum) := by
  rw [smul_eq, hsum_equiv, smul_hsum, hsum_single]

end SMul

section Semiring

variable [OrderedCancelAddCommMonoid Γ] [PartialOrder Γ'] [AddAction Γ Γ']
  [IsOrderedCancelVAdd Γ Γ'] [Semiring R] [AddCommMonoid V] [Module R V]

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
  rw [hsum_smul_module, of_symm_smul_of_eq_mul]

/-- The summation of a `summable_family` as a `LinearMap`. -/
@[simps]
def lsum : SummableFamily Γ R α →ₗ[HahnSeries Γ R] HahnSeries Γ R where
  toFun := hsum
  map_add' _ _ := hsum_add
  map_smul' _ _ := hsum_smul

@[simp]
theorem hsum_sub {R} [Ring R] {s t : SummableFamily Γ R α} :
    (s - t).hsum = s.hsum - t.hsum := by
  rw [← lsum_apply, LinearMap.map_sub, lsum_apply, lsum_apply]

theorem isPWO_iUnion_support_prod_mul {s : α → HahnSeries Γ R} {t : β → HahnSeries Γ R}
    (hs : (⋃ a, (s a).support).IsPWO) (ht : (⋃ b, (t b).support).IsPWO) :
    (⋃ (a : α × β), ((fun a ↦ ((s a.1) * (t a.2))) a).support).IsPWO :=
  isPWO_iUnion_support_prod_smul hs ht

theorem finite_co_support_prod_mul (s : SummableFamily Γ R α)
    (t : SummableFamily Γ R β) (g : Γ) :
    Finite {(a : α × β) | ((fun (a : α × β) ↦ (s a.1 * t a.2)) a).coeff g ≠ 0} :=
  finite_co_support_prod_smul s t g

/-- A summable family given by pointwise multiplication of a pair of summable families. -/
@[simps]
def mul (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    (SummableFamily Γ R (α × β)) where
  toFun a := s (a.1) * t (a.2)
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_prod_mul s.isPWO_iUnion_support t.isPWO_iUnion_support
  finite_co_support' g := finite_co_support_prod_mul s t g

theorem mul_eq_smul {β : Type*} (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    mul s t = smul s t :=
  rfl

theorem coeff_hsum_mul {β : Type*} (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) (g : Γ) :
    (mul s t).hsum.coeff g = ∑ gh ∈ addAntidiagonal s.isPWO_iUnion_support
      t.isPWO_iUnion_support g, (s.hsum.coeff gh.1) * (t.hsum.coeff gh.2) := by
  simp_rw [← smul_eq_mul, mul_eq_smul]
  exact coeff_smul s t g

@[deprecated (since := "2025-01-31")] alias mul_coeff := coeff_hsum_mul

theorem hsum_mul {β : Type*} (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    (mul s t).hsum = s.hsum * t.hsum := by
  rw [← smul_eq_mul, mul_eq_smul]
  exact smul_hsum s t

open Classical in
theorem pi_PWO_iUnion_support (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*)
    {t : Π i : σ, (α i) → HahnSeries Γ R}
    (ht : ∀ i : σ, (⋃ a : α i, ((t i) a).support).IsPWO) :
    (⋃ a : (i : σ) → i ∈ s → α i,
      (∏ i ∈ s, if h : i ∈ s then (t i) (a i h) else 1).support).IsPWO := by
  induction s using cons_induction with
  | empty =>
    simp only [prod_empty]
    have h : ⋃ (_ : (i : σ) → i ∈ (∅ : Finset σ) → α i) , support (1 : HahnSeries Γ R) ⊆ {0} := by
      simp
    exact Set.Subsingleton.isPWO <| Set.subsingleton_of_subset_singleton h
  | cons a s' has hp =>
    refine (isPWO_iUnion_support_prod_mul (ht a) hp).mono ?_
    intro g hg
    simp_all only [dite_true, mem_cons, not_false_eq_true, prod_cons, or_false,
      or_true, Set.mem_iUnion, mem_support, ne_eq, Prod.exists]
    obtain ⟨f, hf⟩ := hg
    use f a (mem_cons_self a s'), fun i hi => f i (mem_cons_of_mem hi)
    have hor : ∏ i ∈ s', (if h : i = a ∨ i ∈ s' then t i (f i (mem_cons.mpr h)) else 1) =
        ∏ i ∈ s', if h : i ∈ s' then t i (f i (mem_cons_of_mem h)) else 1 := by
      refine prod_congr rfl fun x hx => ?_
      simp_all only [dite_true, or_true]
    exact hor ▸ hf

open Classical in
/-- delete this? -/
theorem cosupp_subset_iunion_cosupp_left {V} [AddCommMonoid V] (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (g : Γ') {gh : Γ × Γ'}
    (hgh : gh ∈ VAddAntidiagonal s.isPWO_iUnion_support t.isPWO_iUnion_support g) :
    Set.Finite.toFinset (s.finite_co_support (gh.1)) ⊆
    (VAddAntidiagonal s.isPWO_iUnion_support t.isPWO_iUnion_support g).biUnion
      fun (g' : Γ × Γ') => Set.Finite.toFinset (s.finite_co_support (g'.1)) := by
  intro a ha
  simp_all only [mem_vaddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq, Set.Finite.mem_toFinset,
    Function.mem_support, mem_biUnion, Prod.exists, exists_and_right, exists_and_left]
  exact Exists.intro gh.1 ⟨⟨hgh.1, Exists.intro gh.2 hgh.2⟩, ha⟩

open Classical in
theorem pi_finite_co_support {σ : Type*} (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*) (g : Γ)
    {t : Π i : σ, (α i) → HahnSeries Γ R} (htp : ∀ i : σ, (⋃ a : α i, ((t i) a).support).IsPWO)
    (htfc : ∀ i : σ, ∀ h : Γ, {a : α i | ((t i) a).coeff h ≠ 0}.Finite) :
    {a : (i : σ) → i ∈ s → α i |
      ((fun a ↦ ∏ i ∈ s, if h : i ∈ s then (t i) (a i h) else 1) a).coeff g ≠ 0}.Finite := by
  induction s using cons_induction generalizing g with
  | empty => exact Set.Subsingleton.finite fun x _ y _ =>
    (funext₂ fun j hj => False.elim ((List.mem_nil_iff j).mp hj))
  | cons a s' has hp =>
    simp_all only [ne_eq, dite_true, not_false_eq_true, or_false, or_true]
    simp only [prod_cons, mem_cons, true_or, ↓reduceDIte, coeff_mul]
    have hor : ∀ b : (i : σ) → i ∈ (cons a s' has) → α i,
        ∏ i ∈ s', (if h : i ∈ cons a s' has then t i (b i h) else 1) =
        ∏ i ∈ s', if h : i ∈ s' then t i (b i (mem_cons_of_mem h)) else 1 :=
      fun b => prod_congr rfl fun x hx => (by simp [*])
    apply ((addAntidiagonal (htp a) (pi_PWO_iUnion_support s' α htp) g).finite_toSet.biUnion'
      _).subset _
    · exact fun ij _ => {b : (i : σ) → i ∈ (cons a s' has) → α i |
        (t a (b a (mem_cons_self a s'))).coeff ij.1 *
        (∏ i ∈ s', if h : i ∈ (cons a s' has) then (t i) (b i h) else 1).coeff ij.2 ≠ 0}
    · intro gh hgh
      simp_rw [hor _, ne_eq]
      refine Set.Finite.of_finite_image (f := fun (b : (i : σ) → i ∈ cons a s' has → α i) =>
        (b a (mem_cons_self a s'), fun (i : σ) (hi : i ∈ s') => b i (mem_cons_of_mem hi)))
        ((Set.Finite.prod (htfc a gh.1) (hp gh.2)).subset ?_) ?_
      · intro x hx
        simp_all only [Set.mem_image, Set.mem_prod, Set.mem_setOf_eq]
        obtain ⟨y, hy⟩ := hx
        constructor
        · have h : x.1 = y a (mem_cons_self a s') := by rw [← hy.2]
          exact left_ne_zero_of_mul (h ▸ hy.1)
        · have h : x.2 = fun i hi ↦ y i (mem_cons_of_mem hi) := by rw [← hy.2]
          simp_rw [h]
          exact right_ne_zero_of_mul hy.1
      · refine Injective.injOn ?_
        intro x y hxy
        simp_all only [dite_true, cons_eq_insert, mem_insert, or_true, mem_coe, mem_addAntidiagonal,
          Set.mem_iUnion, mem_support, ne_eq, Prod.mk.injEq]
        ext i hi
        by_cases hhi : i = a
        · exact hhi ▸ hxy.1
        · exact congrFun (congrFun hxy.2 i) (Or.resolve_left (mem_cons.mp hi) hhi)
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      have hhx := exists_ne_zero_of_sum_ne_zero hx
      simp only [mem_coe, mem_addAntidiagonal, Set.mem_iUnion, mem_support, ne_eq,
        mem_cons, Set.mem_setOf_eq, exists_prop, Prod.exists]
      use hhx.choose.1, hhx.choose.2
      refine ⟨⟨?_, ?_⟩, hhx.choose_spec.2⟩
      · use x a (mem_cons_self a s')
        exact left_ne_zero_of_mul hhx.choose_spec.2
      · refine ⟨?_, (Finset.mem_addAntidiagonal.mp hhx.choose_spec.1).2.2⟩
        use fun i hi => x i (mem_cons_of_mem hi)
        have h := right_ne_zero_of_mul hhx.choose_spec.2
        have hpr :
            ∏ x_1 ∈ s', (if h : x_1 = a ∨ x_1 ∈ s' then t x_1 (x x_1 (mem_cons.mpr h)) else 1) =
            ∏ x_1 ∈ s', (if h : x_1 ∈ s' then t x_1 (x x_1 (mem_cons_of_mem h)) else 1) :=
          prod_congr rfl fun i hi => (by simp [hi])
        simp_all [hpr]

open Classical in
/-- A summable family made from pointwise multiplication along a finite collection of summable
families. -/
@[simps]
def PiFamily (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*)
    (t : Π i : σ, SummableFamily Γ R (α i)) : (SummableFamily Γ R (Π i ∈ s, α i)) where
  toFun a := Finset.prod s fun i => if h : i ∈ s then (t i) (a i h) else 1
  isPWO_iUnion_support' := pi_PWO_iUnion_support s α fun i => (t i).isPWO_iUnion_support
  finite_co_support' g :=
    pi_finite_co_support s α g (fun i => (t i).isPWO_iUnion_support)
      (fun i g' => (t i).finite_co_support g')

@[simp]
theorem cons_pi_prod_mem (s : Finset σ) (α : σ → Type*) {a : σ} (has : a ∉ s)
    (f : (i : σ) → i ∈ cons a s has → α i) : (consPiProd α has f).1 = f a (mem_cons_self a s) :=
  rfl

@[simp]
theorem cons_pi_prod_not_mem (s : Finset σ) (α : σ → Type*) {a : σ} (has : a ∉ s)
    (f : (i : σ) → i ∈ cons a s has → α i) :
    (consPiProd α has f).2 = fun i hi => f i (mem_cons_of_mem hi) :=
  rfl

open Classical in
@[simp]
theorem prod_pi_cons_mem (s : Finset σ) (α : σ → Type*) {a : σ} (has : a ∉ s)
    (f : α a × ((i : σ) → i ∈ s → α i)) :
    prodPiCons α has f a (mem_cons_self a s) = f.1 := by
  simp [prodPiCons]

open Classical in
theorem piFamily_cons (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*)
    (t : Π i : σ, SummableFamily Γ R (α i)) {a : σ} (has : a ∉ s) :
    Equiv (consPiProdEquiv α has) (PiFamily (cons a s has) α t) = mul (t a) (PiFamily s α t) := by
  ext1 _
  simp only [consPiProdEquiv, Equiv_toFun, Equiv.coe_fn_symm_mk, PiFamily_toFun, mem_cons,
    prod_cons, true_or, ↓reduceDIte, prod_pi_cons_mem, mul_toFun]
  congr 1
  refine prod_congr rfl ?_
  intro i hi
  rw [dif_pos hi, dif_pos (Or.inr hi)]
  simp [prodPiCons, dif_neg (ne_of_mem_of_not_mem hi has)]

theorem hsum_pi_family (s : Finset σ) {R} [CommSemiring R] (α : σ → Type*)
    (t : Π i : σ, SummableFamily Γ R (α i)) :
    (PiFamily s α t).hsum = ∏ i ∈ s, (t i).hsum := by
  induction s using cons_induction with
  | empty =>
    ext g
    simp only [coeff_hsum, PiFamily_toFun, not_mem_empty, ↓reduceDIte, prod_const_one, coeff_one,
      prod_empty]
    classical
    refine finsum_eq_single (fun _ ↦ if g = 0 then 1 else 0)
      (fun i hi => False.elim ((List.mem_nil_iff i).mp hi)) ?_
    · intro f hf
      by_contra
      have hhf : f = fun i hi => False.elim ((List.mem_nil_iff i).mp hi) := by
        ext i hi
        exact False.elim ((List.mem_nil_iff i).mp hi)
      apply hf hhf
  | cons a s' has hp =>
    rw [prod_cons, ← hp, ← hsum_mul, ← piFamily_cons, hsum_equiv]

section Fintype

variable [Fintype σ]

open Classical in
theorem pi_PWO_iUnion_support_Fintype {R} [CommSemiring R] (α : σ → Type*)
    {t : Π i : σ, (α i) → HahnSeries Γ R}
    (ht : ∀ i : σ, (⋃ a : α i, ((t i) a).support).IsPWO) :
    (⋃ a : (i : σ) → α i, (∏ i, (t i) (a i)).support).IsPWO := by
  induction Finset.univ (α := σ) using cons_induction with
  | empty =>
    simp only [prod_empty]
    refine Set.Subsingleton.isPWO ?_
    by_cases h : Nontrivial R
    · rw [support_one, Set.iUnion_singleton_eq_range]
      intro x hx y hy
      simp_all [Set.mem_range, exists_prop', support_one, Set.iUnion_singleton_eq_range]
    · simp [← @single_zero_one,
        ← subsingleton_iff_zero_eq_one.mpr (not_nontrivial_iff_subsingleton.mp h)]
  | cons a s has hp =>
    refine (isPWO_iUnion_support_prod_mul (ht a) hp).mono ?_
    intro g hg
    simp_all only [dite_true, mem_cons, not_false_eq_true, prod_cons, or_false,
      or_true, Set.mem_iUnion, mem_support, ne_eq, Prod.exists]
    obtain ⟨f, hf⟩ := hg
    use f a, fun i => f i


open Classical in
/-- The equivalence between a pi type over a fintype and a pi type on `univ`. -/
@[simps]
def univ_equiv (α : σ → Type*) :
    ((i : σ) → α i) ≃ ((i : σ) → i ∈ Finset.univ → α i) where
  toFun a := fun i _ ↦ a i
  invFun a := fun i ↦ a i (Finset.mem_univ i)
  left_inv := congrFun rfl
  right_inv := congrFun rfl

open Classical in
theorem univ_equiv_Family {R} [CommSemiring R] (α : σ → Type*) (g : Γ)
    {t : Π i : σ, (α i) → HahnSeries Γ R} (a : (i : σ) → α i) :
    a ∈ {a : (i : σ) → α i | (∏ i, (t i) (a i)).coeff g ≠ 0} ↔
      univ_equiv α a ∈ {a : (i : σ) → i ∈ Finset.univ → α i |
        (∏ i, (t i) (a i (Finset.mem_univ i))).coeff g ≠ 0} := by
  simp_all

/-- The equivalence between a pi-parametrized family and the corresponding finset-parametrized
family.-/
def univ_equiv_Hahn {R} [CommSemiring R] (α : σ → Type*) (g : Γ)
    {t : Π i : σ, (α i) → HahnSeries Γ R} :
    {a : (i : σ) → α i | (∏ i, (t i) (a i)).coeff g ≠ 0} ≃
    {a : (i : σ) → i ∈ Finset.univ → α i | (∏ i, (t i) (a i (Finset.mem_univ i))).coeff g ≠ 0} where
  toFun a := ⟨univ_equiv α a, (univ_equiv_Family α g a).mp (Subtype.coe_prop a)⟩
  invFun a := ⟨(univ_equiv α).symm a, (univ_equiv_Family α g _).mpr (by simp)⟩
  left_inv a := by simp
  right_inv a := by simp
/-!
open Classical in
/-- A summable family made from pointwise multiplication along a finite collection of summable
families. -/
@[simps]
def PiFamily' {R} [CommSemiring R] (α : σ → Type*)
    (t : Π i : σ, SummableFamily Γ R (α i)) : (SummableFamily Γ R (Π i, α i)) where
  toFun a := ∏ i, (t i) (a i)
  isPWO_iUnion_support' := pi_PWO_iUnion_support' α fun i => (t i).isPWO_iUnion_support
  finite_co_support' g :=
    pi_finite_co_support Finset.univ α g (fun i => (t i).isPWO_iUnion_support)
      (fun i g' => (t i).finite_co_support g')
-/
end Fintype

end Semiring

section OfFinsupp

variable [PartialOrder Γ] [AddCommMonoid R]

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

@[simp]
theorem coe_ofFinsupp {f : α →₀ HahnSeries Γ R} : ⇑(SummableFamily.ofFinsupp f) = f :=
  rfl

@[simp]
theorem hsum_ofFinsupp {f : α →₀ HahnSeries Γ R} : (ofFinsupp f).hsum = f.sum fun _ => id := by
  ext g
  simp only [coeff_hsum, coe_ofFinsupp, Finsupp.sum, Ne]
  simp_rw [← coeff.addMonoidHom_apply, id]
  rw [map_sum, finsum_eq_sum_of_support_subset]
  intro x h
  simp only [coeff.addMonoidHom_apply, mem_coe, Finsupp.mem_support_iff, Ne]
  contrapose! h
  simp [h]

end OfFinsupp

section EmbDomain

variable [PartialOrder Γ] [AddCommMonoid R]

open Classical in
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
        · simp only [Ne, Set.mem_setOf_eq, dif_neg hb, coeff_zero, not_true_eq_false] at h)

variable (s : SummableFamily Γ R α) (f : α ↪ β) {a : α} {b : β}

open Classical in
theorem embDomain_apply :
    s.embDomain f b = if h : b ∈ Set.range f then s (Classical.choose h) else 0 :=
  rfl

@[simp]
theorem embDomain_image : s.embDomain f (f a) = s a := by
  rw [embDomain_apply, dif_pos (Set.mem_range_self a)]
  exact congr rfl (f.injective (Classical.choose_spec (Set.mem_range_self a)))

@[simp]
theorem embDomain_notin_range (h : b ∉ Set.range f) : s.embDomain f b = 0 := by
  rw [embDomain_apply, dif_neg h]

@[simp]
theorem hsum_embDomain : (s.embDomain f).hsum = s.hsum := by
  classical
  ext g
  simp only [coeff_hsum, embDomain_apply, apply_dite HahnSeries.coeff, dite_apply, coeff_zero]
  exact finsum_emb_domain f fun a => (s a).coeff g

end EmbDomain

section powers

theorem support_pow_subset_closure [OrderedCancelAddCommMonoid Γ] [Semiring R] (x : HahnSeries Γ R)
    (n : ℕ) : support (x ^ n) ⊆ AddSubmonoid.closure (support x) := by
  induction' n with n ih <;> intro g hn
  · simp only [pow_zero, mem_support, coeff_one, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
    simp only [hn, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem _
  · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (ih hi) (AddSubmonoid.subset_closure hj))

theorem isPWO_iUnion_support_powers [LinearOrderedCancelAddCommMonoid Γ] [Semiring R]
    {x : HahnSeries Γ R} (hx : 0 ≤ x.order) :
    (⋃ n : ℕ, (x ^ n).support).IsPWO :=
  (x.isPWO_support'.addSubmonoid_closure
    fun _ hg => le_trans hx (order_le_of_coeff_ne_zero (Function.mem_support.mp hg))).mono
    (Set.iUnion_subset fun n => support_pow_subset_closure x n)

theorem co_support_zero [OrderedCancelAddCommMonoid Γ] [Semiring R] (g : Γ) :
    {a | ¬((0 : HahnSeries Γ R) ^ a).coeff g = 0} ⊆ {0} := by
  simp only [Set.subset_singleton_iff, Set.mem_setOf_eq]
  intro n hn
  by_contra h'
  simp_all only [ne_eq, not_false_eq_true, zero_pow, coeff_zero, not_true_eq_false]

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R]

theorem pow_finite_co_support {x : HahnSeries Γ R} (hx : 0 < x.orderTop) (g : Γ) :
    Set.Finite {a | ((fun n ↦ x ^ n) a).coeff g ≠ 0} := by
  have hpwo : Set.IsPWO (⋃ n, support (x ^ n)) :=
    isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt hx)
  by_cases h0 : x = 0; · exact h0 ▸ Set.Finite.subset (Set.finite_singleton 0) (co_support_zero g)
  by_cases hg : g ∈ ⋃ n : ℕ, { g | (x ^ n).coeff g ≠ 0 }
  swap; · exact Set.finite_empty.subset fun n hn => hg (Set.mem_iUnion.2 ⟨n, hn⟩)
  apply hpwo.isWF.induction hg
  intro y ys hy
  refine ((((addAntidiagonal x.isPWO_support hpwo y).finite_toSet.biUnion
    fun ij hij => hy ij.snd (mem_addAntidiagonal.1 (mem_coe.1 hij)).2.1 ?_).image Nat.succ).union
      (Set.finite_singleton 0)).subset ?_
  · obtain ⟨hi, _, rfl⟩ := mem_addAntidiagonal.1 (mem_coe.1 hij)
    exact lt_add_of_pos_left ij.2 <| lt_of_lt_of_le ((zero_lt_orderTop_iff h0).mp hx) <|
      order_le_of_coeff_ne_zero <| Function.mem_support.mp hi
  · rintro (_ | n) hn
    · exact Set.mem_union_right _ (Set.mem_singleton 0)
    · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
      refine Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨j, i⟩, Set.mem_iUnion.2 ⟨?_, hi⟩⟩, rfl⟩
      simp only [mem_coe, mem_addAntidiagonal, mem_support, ne_eq, Set.mem_iUnion]
      exact ⟨hj, ⟨n, hi⟩, add_comm j i⟩

/-- A summable family of powers of a Hahn series `x`. If `x` has non-positive orderTop, then we
return the junk value zero. -/
def powers (x : HahnSeries Γ R) : SummableFamily Γ R ℕ where
  toFun n := if 0 < x.orderTop then x ^ n else 0
  isPWO_iUnion_support' := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt h)
    · simp [h]
  finite_co_support' g := by
    by_cases h : 0 < x.orderTop
    · simp only [h, ↓reduceIte]
      exact pow_finite_co_support h g
    · simp [h]

@[simp]
theorem powers_of_orderTop_pos {x : HahnSeries Γ R} (hx : 0 < x.orderTop) (n : ℕ) :
    powers x n = x ^ n := by
  simp [powers, hx]
  exact rfl

@[simp]
theorem powers_of_not_orderTop_pos {x : HahnSeries Γ R} (hx : ¬ 0 < x.orderTop) :
    powers x = 0 := by
  simp [powers, hx]
  exact rfl

variable {x : HahnSeries Γ R} (hx : 0 < x.orderTop)

include hx in
@[simp]
theorem coe_powers : ⇑(powers x) = HPow.hPow x := by
  ext1 n
  simp [hx]

include hx in
theorem embDomain_succ_smul_powers :
    (x • powers x).embDomain ⟨Nat.succ, Nat.succ_injective⟩ =
      powers x - ofFinsupp (Finsupp.single 0 1) := by
  apply SummableFamily.ext
  rintro (_ | n)
  · simp [hx]
  · simp only [coe_sub, coe_ofFinsupp, Pi.sub_apply, powers_of_orderTop_pos hx, ne_eq,
    self_eq_add_left, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
    Finsupp.single_eq_of_ne, sub_zero]
    simp only [embDomain_apply, Embedding.coeFn_mk, Nat.range_succ, Set.mem_setOf_eq,
      lt_add_iff_pos_left, add_pos_iff, Nat.lt_one_iff, pos_of_gt, or_true, ↓reduceDIte,
      Nat.succ_eq_add_one, add_left_inj, Classical.choose_eq, smul_apply, powers_of_orderTop_pos hx,
      smul_eq_mul]
    rw [add_comm, pow_add, pow_one]
    exact rfl

include hx in
theorem one_sub_self_mul_hsum_powers : (1 - x) * (powers x).hsum = 1 := by
  rw [← hsum_smul, sub_smul 1 x (powers x), one_smul, hsum_sub, ←
    hsum_embDomain (x • powers x) ⟨Nat.succ, Nat.succ_injective⟩, embDomain_succ_smul_powers hx]
  simp

end powers

end SummableFamily

section Inversion

section Monoid

variable [LinearOrderedCancelAddCommMonoid Γ] [CommRing R]

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

theorem one_minus_single_mul_addUnit {x y : HahnSeries Γ R} (r : R) (hr : r * x.leadingCoeff = 1)
    (hxy : x = y + x.leadingTerm) (hxo : IsAddUnit x.order) :
    1 - single (IsAddUnit.addUnit hxo).neg r * x = -(single (IsAddUnit.addUnit hxo).neg r * y) := by
  nth_rw 2 [hxy]
  rw [mul_add, leadingTerm_eq, single_mul_single, ← leadingCoeff_eq, hr, AddUnits.neg_eq_val_neg,
    IsAddUnit.val_neg_add, sub_add_eq_sub_sub_swap, sub_eq_neg_self, sub_eq_zero_of_eq]
  exact rfl

theorem unit_aux (x : HahnSeries Γ R) {r : R} (hr : r * x.leadingCoeff = 1)
    (hxo : IsAddUnit x.order) : 0 < (1 - single (IsAddUnit.addUnit hxo).neg r * x).orderTop := by
  let y := (x - x.leadingTerm)
  by_cases hy : y = 0
  · have hrx : (single (IsAddUnit.addUnit hxo).neg) r * x = 1 := by
      nth_rw 2 [eq_of_sub_eq_zero hy] -- get a bad loop without `nth_rw`
      simp only [AddUnits.neg_eq_val_neg, leadingTerm_eq, ← leadingCoeff_eq, single_mul_single,
        IsAddUnit.val_neg_add, hr, single_zero_one]
    simp only [hrx, sub_self, orderTop_zero, WithTop.top_pos]
  have hr' : ∀ (s : R), r * s = 0 → s = 0 :=
    fun s hs => by rw [← one_mul s, ← hr, mul_right_comm, hs, zero_mul]
  have hy' : 0 < (single (IsAddUnit.addUnit hxo).neg r * y).order := by
    rw [(order_mul_single_of_nonzero_divisor hr' hy)]
    refine pos_of_lt_add_right (a := x.order) ?_
    rw [← add_assoc, add_comm x.order, AddUnits.neg_eq_val_neg, IsAddUnit.val_neg_add, zero_add]
    exact order_lt_add_single_support_order (sub_add_cancel x x.leadingTerm).symm hy
  simp only [one_minus_single_mul_addUnit r hr (sub_add_cancel x x.leadingTerm).symm, orderTop_neg]
  exact zero_lt_orderTop_of_order hy'

theorem isUnit_of_isUnit_leadingCoeff_AddUnitOrder {x : HahnSeries Γ R} (hx : IsUnit x.leadingCoeff)
    (hxo : IsAddUnit x.order) : IsUnit x := by
  let ⟨⟨u, i, ui, iu⟩, h⟩ := hx
  rw [Units.val_mk] at h
  rw [h] at iu
  have h' := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu hxo)
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
  exact one_minus_single_mul_addUnit r hr hxy (AddGroup.isAddUnit x.order)

theorem isUnit_of_isUnit_leadingCoeff {x : HahnSeries Γ R} (hx : IsUnit x.leadingCoeff) :
    IsUnit x := by
  exact isUnit_of_isUnit_leadingCoeff_AddUnitOrder hx (AddGroup.isAddUnit x.order)

theorem isUnit_iff [IsDomain R] {x : HahnSeries Γ R} :
    IsUnit x ↔ IsUnit (x.leadingCoeff) := by
  refine { mp := ?mp, mpr := isUnit_of_isUnit_leadingCoeff }
  rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
  refine
    isUnit_of_mul_eq_one (u.leadingCoeff) (i.leadingCoeff)
      ((coeff_mul_order_add_order u i).symm.trans ?_)
  rw [ui, coeff_one, if_pos]
  rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ui, order_one]

end CommRing

open Classical in
instance instField [Field R] : Field (HahnSeries Γ R) where
  __ : IsDomain (HahnSeries Γ R) := inferInstance
  inv x :=
    if x0 : x = 0 then 0
    else
      (single (IsAddUnit.addUnit (AddGroup.isAddUnit x.order)).neg) (x.leadingCoeff)⁻¹ *
        (SummableFamily.powers _).hsum
  inv_zero := dif_pos rfl
  mul_inv_cancel x x0 := (congr rfl (dif_neg x0)).trans <| by
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers
        (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_iff.mpr x0)) (AddGroup.isAddUnit x.order))
    rw [sub_sub_cancel] at h
    rw [← mul_assoc, mul_comm x, h]
  nnqsmul := _
  nnqsmul_def := fun q a => rfl
  qsmul := _
  qsmul_def := fun q a => rfl

end Inversion

end HahnSeries
