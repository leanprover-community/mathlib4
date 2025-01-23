/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
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

## Main results
  * If `R` is a commutative domain, and `Γ` is a linearly ordered additive commutative group, then
  a Hahn series is a unit if and only if its leading term is a unit in `R`.

## TODO
  * Remove unnecessary domain hypotheses.
  * More general summable families, e.g., define the evaluation homomorphism from a power series
  ring taking `X` to a positive order element.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/


open Finset Function

open Pointwise

noncomputable section

variable {Γ Γ' R V α β : Type*}

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
theorem hsum_coeff {s : SummableFamily Γ R α} {g : Γ} : s.hsum.coeff g = ∑ᶠ i, (s i).coeff g :=
  rfl

theorem support_hsum_subset {s : SummableFamily Γ R α} : s.hsum.support ⊆ ⋃ a : α, (s a).support :=
  fun g hg => by
  rw [mem_support, hsum_coeff, finsum_eq_sum _ (s.finite_co_support _)] at hg
  obtain ⟨a, _, h2⟩ := exists_ne_zero_of_sum_ne_zero hg
  rw [Set.mem_iUnion]
  exact ⟨a, h2⟩

@[simp]
theorem hsum_add {s t : SummableFamily Γ R α} : (s + t).hsum = s.hsum + t.hsum := by
  ext g
  simp only [hsum_coeff, add_coeff, add_apply]
  exact finsum_add_distrib (s.finite_co_support _) (t.finite_co_support _)

theorem hsum_coeff_eq_sum_of_subset {s : SummableFamily Γ R α} {g : Γ} {t : Finset α}
    (h : { a | (s a).coeff g ≠ 0 } ⊆ t) : s.hsum.coeff g = ∑ i ∈ t, (s i).coeff g := by
  simp only [hsum_coeff, finsum_eq_sum _ (s.finite_co_support _)]
  exact sum_subset (Set.Finite.toFinset_subset.mpr h) (by simp)

theorem hsum_coeff_eq_sum {s : SummableFamily Γ R α} {g : Γ} :
    s.hsum.coeff g = ∑ i ∈ (s.coeff g).support, (s i).coeff g := by
  simp only [hsum_coeff, finsum_eq_sum _ (s.finite_co_support _), coeff_support]

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

/-- The summable family given by multiplying every series in a summable family by a scalar. -/
@[simps]
def smulFamily [AddCommMonoid V] [SMulWithZero R V] (f : α → R) (s : SummableFamily Γ V α) :
    SummableFamily Γ V α where
  toFun a := (f a) • s a
  isPWO_iUnion_support' := by
    refine Set.IsPWO.mono s.isPWO_iUnion_support fun g hg => ?_
    simp_all only [Set.mem_iUnion, mem_support, smul_coeff, ne_eq]
    obtain ⟨i, hi⟩ := hg
    exact Exists.intro i <| right_ne_zero_of_smul hi
  finite_co_support' g := by
    refine Set.Finite.subset (s.finite_co_support g) fun i hi => ?_
    simp_all only [smul_coeff, ne_eq, Set.mem_setOf_eq, Function.mem_support]
    exact right_ne_zero_of_smul hi

theorem hsum_smulFamily [AddCommMonoid V] [SMulWithZero R V] (f : α → R)
    (s : SummableFamily Γ V α) (g : Γ) :
    (smulFamily f s).hsum.coeff g = ∑ᶠ i, (f i) • ((s i).coeff g) :=
  rfl

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
        simp only [Pi.smul_apply, smul_coeff, ne_eq, Set.mem_setOf_eq] at hi
        simp only [Function.mem_support, ne_eq]
        exact right_ne_zero_of_smul hi } ⟩

variable [AddCommMonoid R] [SMulWithZero R V]

theorem smul_support_subset_prod (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (gh : Γ × Γ') :
    (Function.support fun (i : α × β) ↦ (s i.1).coeff gh.1 • (t i.2).coeff gh.2) ⊆
    ((s.finite_co_support' gh.1).prod (t.finite_co_support' gh.2)).toFinset := by
  intro _ hab
  simp_all only [Function.mem_support, ne_eq, Set.Finite.coe_toFinset, Set.mem_prod,
    Set.mem_setOf_eq]
  exact ⟨left_ne_zero_of_smul hab, right_ne_zero_of_smul hab⟩

theorem smul_support_finite (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (gh : Γ × Γ') :
    (Function.support fun (i : α × β) ↦ (s i.1).coeff gh.1 • (t i.2).coeff gh.2).Finite :=
  Set.Finite.subset (Set.toFinite ((s.finite_co_support' gh.1).prod
    (t.finite_co_support' gh.2)).toFinset) (smul_support_subset_prod s t gh)

variable [VAdd Γ Γ'] [IsOrderedCancelVAdd Γ Γ']

open HahnModule

theorem isPWO_iUnion_support_prod_smul {s : α → HahnSeries Γ R} {t : β → HahnSeries Γ' V}
    (hs : (⋃ a, (s a).support).IsPWO) (ht : (⋃ b, (t b).support).IsPWO) :
    (⋃ (a : α × β), ((fun a ↦ (of R).symm
      ((s a.1) • (of R) (t a.2))) a).support).IsPWO := by
  apply (hs.vadd ht).mono
  have hsupp : ∀ ab : α × β, support ((fun ab ↦ (of R).symm (s ab.1 • (of R) (t ab.2))) ab) ⊆
      (s ab.1).support +ᵥ (t ab.2).support := by
    intro ab
    refine Set.Subset.trans (fun x hx => ?_) (support_vaddAntidiagonal_subset_vadd
      (hs := (s ab.1).isPWO_support) (ht := (t ab.2).isPWO_support))
    contrapose! hx
    simp only [Set.mem_setOf_eq, not_nonempty_iff_eq_empty] at hx
    rw [mem_support, not_not, HahnModule.smul_coeff, hx, sum_empty]
  refine Set.Subset.trans (Set.iUnion_mono fun a => (hsupp a)) ?_
  simp_all only [Set.iUnion_subset_iff, Prod.forall]
  exact fun a b => Set.vadd_subset_vadd (Set.subset_iUnion_of_subset a fun x y ↦ y)
    (Set.subset_iUnion_of_subset b fun x y ↦ y)

theorem finite_co_support_prod_smul (s : SummableFamily Γ R α)
    (t : SummableFamily Γ' V β) (g : Γ') :
    Finite {(ab : α × β) |
      ((fun (ab : α × β) ↦ (of R).symm (s ab.1 • (of R) (t ab.2))) ab).coeff g ≠ 0} := by
  apply ((VAddAntidiagonal s.isPWO_iUnion_support t.isPWO_iUnion_support g).finite_toSet.biUnion'
    (fun gh _ => smul_support_finite s t gh)).subset _
  exact fun ab hab => by
    simp only [smul_coeff, ne_eq, Set.mem_setOf_eq] at hab
    obtain ⟨ij, hij⟩ := Finset.exists_ne_zero_of_sum_ne_zero hab
    simp only [mem_coe, mem_vaddAntidiagonal, Set.mem_iUnion, mem_support, ne_eq,
      Function.mem_support, exists_prop, Prod.exists]
    exact ⟨ij.1, ij.2, ⟨⟨ab.1, left_ne_zero_of_smul hij.2⟩, ⟨ab.2, right_ne_zero_of_smul hij.2⟩,
      ((mem_vaddAntidiagonal _ _ _).mp hij.1).2.2⟩, hij.2⟩

/-- An elementwise scalar multiplication of one summable family on another. -/
@[simps]
def smul (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) :
    (SummableFamily Γ' V (α × β)) where
  toFun ab := (of R).symm (s (ab.1) • ((of R) (t (ab.2))))
  isPWO_iUnion_support' :=
    isPWO_iUnion_support_prod_smul s.isPWO_iUnion_support t.isPWO_iUnion_support
  finite_co_support' g := finite_co_support_prod_smul s t g

@[deprecated (since := "2024-11-17")] noncomputable alias FamilySMul := smul

theorem sum_vAddAntidiagonal_eq (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ')
    (a : α × β) :
    ∑ x ∈ VAddAntidiagonal (s a.1).isPWO_support' (t a.2).isPWO_support' g, (s a.1).coeff x.1 •
      (t a.2).coeff x.2 = ∑ x ∈ VAddAntidiagonal s.isPWO_iUnion_support' t.isPWO_iUnion_support' g,
      (s a.1).coeff x.1 • (t a.2).coeff x.2 := by
  refine sum_subset (fun gh hgh => ?_) fun gh hgh h => ?_
  · simp_all only [mem_vaddAntidiagonal, Function.mem_support, Set.mem_iUnion, mem_support]
    exact ⟨Exists.intro a.1 hgh.1, Exists.intro a.2 hgh.2.1, trivial⟩
  · by_cases hs : (s a.1).coeff gh.1 = 0
    · exact smul_eq_zero_of_left hs ((t a.2).coeff gh.2)
    · simp_all

theorem smul_coeff {R} {V} [Semiring R] [AddCommMonoid V] [Module R V]
    (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) (g : Γ') :
    (smul s t).hsum.coeff g = ∑ gh ∈ VAddAntidiagonal s.isPWO_iUnion_support
      t.isPWO_iUnion_support g, (s.hsum.coeff gh.1) • (t.hsum.coeff gh.2) := by
  rw [hsum_coeff]
  simp only [hsum_coeff_eq_sum, smul_toFun, HahnModule.smul_coeff, Equiv.symm_apply_apply]
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

@[deprecated (since := "2024-11-17")] alias family_smul_coeff := smul_coeff

theorem smul_hsum {R} {V} [Semiring R] [AddCommMonoid V] [Module R V]
    (s : SummableFamily Γ R α) (t : SummableFamily Γ' V β) :
    (smul s t).hsum = (of R).symm (s.hsum • (of R) (t.hsum)) := by
  ext g
  rw [smul_coeff s t g, HahnModule.smul_coeff, Equiv.symm_apply_apply]
  refine Eq.symm (sum_of_injOn (fun a ↦ a) (fun _ _ _ _ h ↦ h) (fun _ hgh => ?_)
    (fun gh _ hgh => ?_) fun _ _ => by simp)
  · simp_all only [mem_coe, mem_vaddAntidiagonal, mem_support, ne_eq, Set.mem_iUnion, and_true]
    constructor
    · rw [hsum_coeff_eq_sum] at hgh
      have h' := Finset.exists_ne_zero_of_sum_ne_zero hgh.1
      simpa using h'
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
theorem smul_apply {x : HahnSeries Γ R} {s : SummableFamily Γ' V α} {a : α} :
    (x • s) a = (of R).symm (x • of R (s a)) :=
  rfl

@[simp]
theorem hsum_smul_module {R} {V} [Semiring R] [AddCommMonoid V] [Module R V] {x : HahnSeries Γ R}
    {s : SummableFamily Γ' V α} :
    (x • s).hsum = (of R).symm (x • of R s.hsum) := by
  rw [smul_eq, hsum_equiv, smul_hsum, hsum_single]

end SMul

section Semiring

variable [OrderedCancelAddCommMonoid Γ] [PartialOrder Γ'] [AddAction Γ Γ']
  [IsOrderedCancelVAdd Γ Γ'] [Semiring R]

instance [AddCommMonoid V] [Module R V] : Module (HahnSeries Γ R) (SummableFamily Γ' V α) where
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
theorem hsum_sub {R : Type*} [Ring R] {s t : SummableFamily Γ R α} :
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

theorem mul_coeff {β : Type*} (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) (g : Γ) :
    (mul s t).hsum.coeff g = ∑ gh ∈ addAntidiagonal s.isPWO_iUnion_support
      t.isPWO_iUnion_support g, (s.hsum.coeff gh.1) * (t.hsum.coeff gh.2) := by
  simp_rw [← smul_eq_mul, mul_eq_smul]
  exact smul_coeff s t g

theorem hsum_mul {β : Type*} (s : SummableFamily Γ R α) (t : SummableFamily Γ R β) :
    (mul s t).hsum = s.hsum * t.hsum := by
  rw [← smul_eq_mul, mul_eq_smul]
  exact smul_hsum s t

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

@[simp]
theorem coe_ofFinsupp {f : α →₀ HahnSeries Γ R} : ⇑(SummableFamily.ofFinsupp f) = f :=
  rfl

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

end OfFinsupp

section EmbDomain

variable [PartialOrder Γ] [AddCommMonoid R] {α β : Type*}

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
        · simp only [Ne, Set.mem_setOf_eq, dif_neg hb, zero_coeff, not_true_eq_false] at h)

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
  simp only [hsum_coeff, embDomain_apply, apply_dite HahnSeries.coeff, dite_apply, zero_coeff]
  exact finsum_emb_domain f fun a => (s a).coeff g

end EmbDomain

section powers

theorem support_pow_subset_closure [OrderedCancelAddCommMonoid Γ] [Semiring R] (x : HahnSeries Γ R)
    (n : ℕ) : support (x ^ n) ⊆ AddSubmonoid.closure (support x) := by
  induction' n with n ih <;> intro g hn
  · simp only [pow_zero, mem_support, one_coeff, ne_eq, ite_eq_right_iff, Classical.not_imp] at hn
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
  simp_all only [ne_eq, not_false_eq_true, zero_pow, zero_coeff, not_true_eq_false]

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

/-- The powers of an element of positive valuation form a summable family. -/
@[simps]
def powers (x : HahnSeries Γ R) (hx : 0 < x.orderTop) : SummableFamily Γ R ℕ where
  toFun n := x ^ n
  isPWO_iUnion_support' := isPWO_iUnion_support_powers (zero_le_orderTop_iff.mp <| le_of_lt hx)
  finite_co_support' g := pow_finite_co_support hx g

variable {x : HahnSeries Γ R} (hx : 0 < x.orderTop)

@[simp]
theorem coe_powers : ⇑(powers x hx) = HPow.hPow x :=
  rfl

theorem embDomain_succ_smul_powers :
    (x • powers x hx).embDomain ⟨Nat.succ, Nat.succ_injective⟩ =
      powers x hx - ofFinsupp (Finsupp.single 0 1) := by
  apply SummableFamily.ext
  rintro (_ | n)
  · rw [embDomain_notin_range, sub_apply, coe_powers, pow_zero, coe_ofFinsupp,
      Finsupp.single_eq_same, sub_self]
    rw [Set.mem_range, not_exists]
    exact Nat.succ_ne_zero
  · refine Eq.trans (embDomain_image _ ⟨Nat.succ, Nat.succ_injective⟩) ?_
    rw [smul_apply, powers_toFun, coe_sub, coe_powers, Pi.sub_apply, coe_ofFinsupp, pow_succ',
      Finsupp.single_eq_of_ne (Nat.zero_ne_add_one n), sub_zero, of_symm_smul_of_eq_mul]

theorem one_sub_self_mul_hsum_powers : (1 - x) * (powers x hx).hsum = 1 := by
  rw [← hsum_smul, sub_smul 1 x (powers x hx), one_smul, hsum_sub, ←
    hsum_embDomain (x • powers x hx) ⟨Nat.succ, Nat.succ_injective⟩, embDomain_succ_smul_powers]
  simp

end powers

end SummableFamily

section Inversion

variable [LinearOrderedAddCommGroup Γ]

section IsDomain

variable [CommRing R] [IsDomain R]

theorem unit_aux (x : HahnSeries Γ R) {r : R} (hr : r * x.leadingCoeff = 1) :
    0 < (1 - single (-x.order) r * x).orderTop := by
  by_cases hx : x = 0; · simp_all [hx]
  have hrz : r ≠ 0 := by
    intro h
    rw [h, zero_mul] at hr
    exact (zero_ne_one' R) hr
  refine lt_of_le_of_ne (le_trans ?_ min_orderTop_le_orderTop_sub) fun h => ?_
  · refine le_min (by rw [orderTop_one]) ?_
    refine le_trans ?_ orderTop_add_orderTop_le_orderTop_mul
    by_cases h : x = 0; · simp [h]
    rw [← order_eq_orderTop_of_ne h, orderTop_single
      (fun _ => by simp_all only [zero_mul, zero_ne_one]), ← @WithTop.coe_add,
      WithTop.coe_nonneg, neg_add_cancel]
  · apply coeff_orderTop_ne h.symm
    simp only [C_apply, single_mul_single, zero_add, mul_one, sub_coeff', Pi.sub_apply, one_coeff,
      ↓reduceIte]
    have hrc := mul_coeff_order_add_order ((single (-x.order)) r) x
    rw [order_single hrz, leadingCoeff_of_single, neg_add_cancel, hr] at hrc
    rw [hrc, sub_self]

theorem isUnit_iff {x : HahnSeries Γ R} : IsUnit x ↔ IsUnit (x.leadingCoeff) := by
  constructor
  · rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
    refine
      isUnit_of_mul_eq_one (u.leadingCoeff) (i.leadingCoeff)
        ((mul_coeff_order_add_order u i).symm.trans ?_)
    rw [ui, one_coeff, if_pos]
    rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ui, order_one]
  · rintro ⟨⟨u, i, ui, iu⟩, h⟩
    rw [Units.val_mk] at h
    rw [h] at iu
    have h := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu)
    rw [sub_sub_cancel] at h
    exact isUnit_of_mul_isUnit_right (isUnit_of_mul_eq_one _ _ h)

end IsDomain

open Classical in
instance instField [Field R] : Field (HahnSeries Γ R) where
  __ : IsDomain (HahnSeries Γ R) := inferInstance
  inv x :=
    if x0 : x = 0 then 0
    else
      (single (-x.order)) (x.leadingCoeff)⁻¹ *
        (SummableFamily.powers _ (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_iff.mpr x0)))).hsum
  inv_zero := dif_pos rfl
  mul_inv_cancel x x0 := (congr rfl (dif_neg x0)).trans <| by
    have h :=
      SummableFamily.one_sub_self_mul_hsum_powers
        (unit_aux x (inv_mul_cancel₀ (leadingCoeff_ne_iff.mpr x0)))
    rw [sub_sub_cancel] at h
    rw [← mul_assoc, mul_comm x, h]
  nnqsmul := _
  nnqsmul_def := fun _ _ => rfl
  qsmul := _
  qsmul_def := fun _ _ => rfl

end Inversion

end HahnSeries
