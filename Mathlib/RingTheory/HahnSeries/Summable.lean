/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Scott Carnahan
-/
import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.Algebra.EuclideanDomain.Instances
import Mathlib.RingTheory.Valuation.Basic

#align_import ring_theory.hahn_series from "leanprover-community/mathlib"@"a484a7d0eade4e1268f4fb402859b6686037f965"

/-!
# Hahn Series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`.  We introduce valuations and a notion of
summability for possibly infinite families of series.

## Main Definitions
  * `HahnSeries.addVal Γ R` defines an `AddValuation` on `HahnSeries Γ R` when `Γ` is linearly
    ordered.
  * A `HahnSeries.SummableFamily` is a family of Hahn series such that the union of their supports
  is well-founded and only finitely many are nonzero at any given coefficient. They have a formal
  sum, `HahnSeries.SummableFamily.hsum`, which can be bundled as a `LinearMap` as
  `HahnSeries.SummableFamily.lsum`. Note that this is different from `Summable` in the valuation
  topology, because there are topologically summable families that do not satisfy the axioms of
  `HahnSeries.SummableFamily`, and formally summable families whose sums do not converge
  topologically.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

set_option linter.uppercaseLean3 false

open Finset Function

open scoped Classical
open BigOperators Pointwise

noncomputable section

variable {Γ : Type*} {R : Type*}

namespace HahnSeries

section Valuation

variable (Γ R) [LinearOrderedCancelAddCommMonoid Γ] [Ring R] [IsDomain R]

/-- The additive valuation on `HahnSeries Γ R`, returning the smallest index at which
  a Hahn Series has a nonzero coefficient, or `⊤` for the 0 series.  -/
def addVal : AddValuation (HahnSeries Γ R) (WithTop Γ) :=
  AddValuation.of (fun x => if x = (0 : HahnSeries Γ R) then (⊤ : WithTop Γ) else x.order)
    (if_pos rfl) ((if_neg one_ne_zero).trans (by simp [order_of_ne]))
    (fun x y => by
      by_cases hx : x = 0
      · by_cases hy : y = 0 <;> · simp [hx, hy]
      · by_cases hy : y = 0
        · simp [hx, hy]
        · simp only [hx, hy, support_nonempty_iff, if_neg, not_false_iff, isWF_support]
          by_cases hxy : x + y = 0
          · simp [hxy]
          rw [if_neg hxy, ← WithTop.coe_min, WithTop.coe_le_coe]
          exact min_order_le_order_add hxy)
    fun x y => by
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    dsimp only
    rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← WithTop.coe_add, WithTop.coe_eq_coe,
      order_mul hx hy]
#align hahn_series.add_val HahnSeries.addVal

variable {Γ} {R}

theorem addVal_apply {x : HahnSeries Γ R} :
    addVal Γ R x = if x = (0 : HahnSeries Γ R) then (⊤ : WithTop Γ) else x.order :=
  AddValuation.of_apply _
#align hahn_series.add_val_apply HahnSeries.addVal_apply

@[simp]
theorem addVal_apply_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) : addVal Γ R x = x.order :=
  if_neg hx
#align hahn_series.add_val_apply_of_ne HahnSeries.addVal_apply_of_ne

theorem addVal_le_of_coeff_ne_zero {x : HahnSeries Γ R} {g : Γ} (h : x.coeff g ≠ 0) :
    addVal Γ R x ≤ g := by
  rw [addVal_apply_of_ne (ne_zero_of_coeff_ne_zero h), WithTop.coe_le_coe]
  exact order_le_of_coeff_ne_zero h
#align hahn_series.add_val_le_of_coeff_ne_zero HahnSeries.addVal_le_of_coeff_ne_zero

theorem zero_lt_order_of_addVal {x : HahnSeries Γ R} (hx : 0 < addVal Γ R x) (hxne : x ≠ 0) :
    0 < x.order := by
  simp_all only [addVal, AddValuation.of_apply, ite_false, WithTop.coe_pos]

theorem zero_le_order_of_addVal {x : HahnSeries Γ R} (hx : 0 < addVal Γ R x) : 0 ≤ x.order := by
  by_cases h : x = 0
  · refine le_of_eq ?_
    simp_all only [AddValuation.map_zero, WithTop.zero_lt_top, order_zero]
  · exact le_of_lt (zero_lt_order_of_addVal hx h)

theorem zero_lt_addVal_iff {x : HahnSeries Γ R} :
    0 < addVal Γ R x ↔ (0 ≤ x.order ∧ (x.order = 0 → x = 0)) := by
  refine { mp := fun hx => ?_, mpr := fun hx => ?_ }
  · refine { left := zero_le_order_of_addVal hx, right := fun hzero => ?_ }
    by_contra hxne
    have hxlt : 0 < x.order := zero_lt_order_of_addVal hx hxne
    rw [hzero, lt_self_iff_false] at hxlt
    exact hxlt
  · by_cases hzero : x = 0
    · simp_all only [addVal_apply, ite_eq_left_iff, WithTop.coe_ne_top, imp_false, not_not,
        reduceIte, WithTop.zero_lt_top]
    · simp_all only [imp_false, ne_eq, not_false_eq_true, addVal_apply_of_ne, WithTop.coe_pos]
      simp_all [lt_iff_le_and_ne]
      exact fun h => hx.right h.symm

end Valuation

theorem support_pow_subset_closure [OrderedCancelAddCommMonoid Γ] [Semiring R] (x : HahnSeries Γ R)
    (n : ℕ) : support (x ^ n) ⊆ AddSubmonoid.closure (support x) := by
  induction' n with n ih <;> intro g hn
  · simp_all only [Nat.zero_eq, pow_zero, mem_support, one_coeff, ne_eq, ite_eq_right_iff,
    not_forall, exists_prop, SetLike.mem_coe]
    exact AddSubmonoid.zero_mem (AddSubmonoid.closure (support x))
  · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
    exact SetLike.mem_coe.2 (AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure hi) (ih hj))

theorem isPWO_iUnion_support_powers [LinearOrderedCancelAddCommMonoid Γ] [Semiring R]
    (x : HahnSeries Γ R) (hx : 0 ≤ x.order) :
    (⋃ n : ℕ, (x ^ n).support).IsPWO :=
  (x.isPWO_support'.addSubmonoid_closure
    fun _ hg => le_trans hx (order_le_of_coeff_ne_zero (Function.mem_support.mp hg))).mono
    (Set.iUnion_subset fun n => support_pow_subset_closure x n)
#align hahn_series.is_pwo_Union_support_powers HahnSeries.isPWO_iUnion_support_powers

section

variable (Γ) (R) [PartialOrder Γ] [AddCommMonoid R]

/-- An infinite family of Hahn series which has a formal coefficient-wise sum.
  The requirements for this are that the union of the supports of the series is well-founded,
  and that only finitely many series are nonzero at any given coefficient. -/
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
        simp only [neg_coeff', Pi.neg_apply, Ne.def, neg_eq_zero]
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

section Semiring

variable [OrderedCancelAddCommMonoid Γ] [Semiring R] {α : Type*}

instance : SMul (HahnSeries Γ R) (SummableFamily Γ R α) where
  smul x s :=
    { toFun := fun a => x * s a
      isPWO_iUnion_support' := by
        apply (x.isPWO_support.add s.isPWO_iUnion_support).mono
        refine' Set.Subset.trans (Set.iUnion_mono fun a => support_mul_subset_add_support) _
        intro g
        simp only [Set.mem_iUnion, exists_imp]
        exact fun a ha => (Set.add_subset_add (Set.Subset.refl _) (Set.subset_iUnion _ a)) ha
      finite_co_support' := fun g => by
        refine'
          ((addAntidiagonal x.isPWO_support s.isPWO_iUnion_support g).finite_toSet.biUnion'
                fun ij _ => _).subset
            fun a ha => _
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
  refine'
    (Eq.trans (finsum_congr fun a => _)
          (finsum_sum_comm (addAntidiagonal x.isPWO_support s.isPWO_iUnion_support g)
            (fun i ij => x.coeff (Prod.fst ij) * (s i).coeff ij.snd) _)).trans
      _
  · refine' sum_subset (addAntidiagonal_mono_right
      (Set.subset_iUnion (fun j => support (toFun s j)) a)) _
    rintro ⟨i, j⟩ hU ha
    rw [mem_addAntidiagonal] at *
    rw [Classical.not_not.1 fun con => ha ⟨hU.1, con, hU.2.2⟩, mul_zero]
  · rintro ⟨i, j⟩ _
    refine' (s.finite_co_support j).subset _
    simp_rw [Function.support_subset_iff', Function.mem_support, Classical.not_not]
    intro a ha
    rw [ha, mul_zero]
  · refine' (sum_congr rfl _).trans (sum_subset (addAntidiagonal_mono_right _) _).symm
    · rintro ⟨i, j⟩ _
      rw [mul_finsum]
      apply s.finite_co_support
    · intro x hx
      simp only [Set.mem_iUnion, Ne.def, mem_support]
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

end Semiring

section OfFinsupp

variable [PartialOrder Γ] [AddCommMonoid R] {α : Type*}

/-- A family with only finitely many nonzero elements is summable. -/
def ofFinsupp (f : α →₀ HahnSeries Γ R) : SummableFamily Γ R α where
  toFun := f
  isPWO_iUnion_support' := by
    apply (f.support.isPWO_bUnion.2 fun a _ => (f a).isPWO_support).mono
    refine' Set.iUnion_subset_iff.2 fun a g hg => _
    have haf : a ∈ f.support := by
      rw [Finsupp.mem_support_iff, ← support_nonempty_iff]
      exact ⟨g, hg⟩
    exact Set.mem_biUnion haf hg
  finite_co_support' g := by
    refine' f.support.finite_toSet.subset fun a ha => _
    simp only [coeff.addMonoidHom_apply, mem_coe, Finsupp.mem_support_iff, Ne.def,
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
  simp only [hsum_coeff, coe_ofFinsupp, Finsupp.sum, Ne.def]
  simp_rw [← coeff.addMonoidHom_apply, id.def]
  rw [map_sum, finsum_eq_sum_of_support_subset]
  intro x h
  simp only [coeff.addMonoidHom_apply, mem_coe, Finsupp.mem_support_iff, Ne.def]
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
    refine' s.isPWO_iUnion_support.mono (Set.iUnion_subset fun b g h => _)
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
        · simp only [Ne.def, Set.mem_setOf_eq, dif_pos hb] at h
          exact ⟨Classical.choose hb, h, Classical.choose_spec hb⟩
        · simp only [Ne.def, Set.mem_setOf_eq, dif_neg hb, zero_coeff, not_true_eq_false] at h)
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

theorem co_support_zero (g : Γ) : {a | ¬((0 : HahnSeries Γ R) ^ a).coeff g = 0} ⊆ {0} := by
  simp_all only [Set.subset_singleton_iff, Set.mem_setOf_eq]
  intro n hn
  by_contra h'
  simp_all only [ne_eq, not_false_eq_true, zero_pow, zero_coeff, not_true_eq_false]

variable {x : HahnSeries Γ R} (hx : 0 ≤ x.order ∧ (x.order = 0 → x = 0))

theorem pow_finite_co_support (g : Γ) : Set.Finite {a | ((fun n ↦ x ^ n) a).coeff g ≠ 0} := by
  have hpwo : Set.IsPWO (⋃ n, support (x ^ n)) := isPWO_iUnion_support_powers x (hx.left)
  by_cases hox : 0 = x.order
  · simp only [ne_eq, hx.right hox.symm]
    exact Set.Finite.subset (Set.finite_singleton 0) (co_support_zero g)
  have hx' : 0 < x.order := by
    rw [@lt_iff_le_and_ne]
    exact { left := hx.left, right := hox }
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
    exact lt_add_of_pos_left ij.2 <| lt_of_lt_of_le hx' <| order_le_of_coeff_ne_zero <|
      Function.mem_support.mp hi
  · rintro (_ | n) hn
    · exact Set.mem_union_right _ (Set.mem_singleton 0)
    · obtain ⟨i, hi, j, hj, rfl⟩ := support_mul_subset_add_support hn
      refine' Set.mem_union_left _ ⟨n, Set.mem_iUnion.2 ⟨⟨i, j⟩, Set.mem_iUnion.2 ⟨_, hj⟩⟩, rfl⟩
      simp only [and_true_iff, Set.mem_iUnion, mem_addAntidiagonal, mem_coe, eq_self_iff_true,
        Ne.def, mem_support, Set.mem_setOf_eq]
      exact ⟨hi, n, hj⟩

/-- Powers of an element of positive order (or zero) form a summable family. -/
@[simps]
def powers : SummableFamily Γ R ℕ where
  toFun n := x ^ n
  isPWO_iUnion_support' := isPWO_iUnion_support_powers x (hx.left)
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
      Pi.sub_apply, ne_eq, not_false_eq_true, Finsupp.single_eq_of_ne, sub_zero, pow_succ]
#align hahn_series.summable_family.emb_domain_succ_smul_powers HahnSeries.SummableFamily.embDomain_succ_smul_powers

theorem one_sub_self_mul_hsum_powers : (1 - x) * (powers hx).hsum = 1 := by
  rw [← hsum_smul, sub_smul 1 x (powers hx), one_smul, hsum_sub, ←
    hsum_embDomain (x • powers hx) ⟨Nat.succ, Nat.succ_injective⟩, embDomain_succ_smul_powers]
  simp only [hsum_sub, hsum_ofFinsupp, id_eq, Finsupp.sum_single_index, sub_sub_cancel]
#align hahn_series.summable_family.one_sub_self_mul_hsum_powers HahnSeries.SummableFamily.one_sub_self_mul_hsum_powers

end powers

end SummableFamily

section Inversion

variable [LinearOrderedAddCommGroup Γ]

section CommRing

variable [CommRing R]

theorem one_minus_single_mul (x y : HahnSeries Γ R) (r : R) (hr : r * x.coeff x.order = 1)
    (hxy : x = y + (single x.order) (x.coeff x.order)) :
    1 - single (-order x) r * x = -(single (-x.order) r * y) := by
    nth_rw 2 [hxy]
    rw [mul_add, single_mul_single, hr, add_left_neg, sub_add_eq_sub_sub_swap, sub_eq_neg_self,
    sub_eq_zero_of_eq]
    exact rfl

theorem unit_aux (x : HahnSeries Γ R) {r : R} (hr : r * x.coeff x.order = 1) :
    0 ≤ (1 - single (-x.order) r * x).order ∧
      ((1 - single (-x.order) r * x).order = 0 → (1 - single (-x.order) r * x) = 0) := by
  let y := (x - (single x.order) (x.coeff x.order))
  by_cases hy : y = 0
  · have hx : x = (single x.order) (x.coeff x.order) := eq_of_sub_eq_zero hy
    have hrx : (single (-order x)) r * x = 1 := by
      nth_rw 2 [hx]
      simp only [single_mul_single, add_left_neg, hr]
      exact rfl
    simp only [hrx, sub_self, order_zero, le_refl, forall_true_left, and_self]
  have hxy : x = y + (single x.order) (x.coeff x.order) := by exact
    (sub_add_cancel x ((single (order x)) (x.coeff (order x)))).symm
  have hr' : ∀ (s : R), r * s = 0 → s = 0 :=
    fun s hs => by rw [← one_mul s, ← hr, mul_right_comm, hs, zero_mul]
  have hry : (single (-x.order) r * y).order = -x.order + y.order :=
    order_mul_single_of_nonzero_divisor hr' hy
  have hy' : 0 < (single (-x.order) r * y).order := by
    rw [hry, lt_neg_add_iff_lt]
    exact order_lt_add_single_support_order hxy hy
  simp only [one_minus_single_mul x y r hr hxy, order_neg]
  refine { left := le_of_lt hy', right := fun hxry => ?_ }
  rw [hxry, lt_self_iff_false] at hy'
  exact hy'.elim
#align hahn_series.unit_aux HahnSeries.unit_aux

theorem isUnit_of_isUnit_coeff_order {x : HahnSeries Γ R} (hx : IsUnit (x.coeff x.order)) :
    IsUnit x := by
  let ⟨⟨u, i, ui, iu⟩, h⟩ := hx
  rw [Units.val_mk] at h
  rw [h] at iu
  have h' := SummableFamily.one_sub_self_mul_hsum_powers (unit_aux x iu)
  rw [sub_sub_cancel] at h'
  exact isUnit_of_mul_isUnit_right (isUnit_of_mul_eq_one _ _ h')

theorem isUnit_iff [IsDomain R] {x : HahnSeries Γ R} :
    IsUnit x ↔ IsUnit (x.coeff x.order) := by
  refine { mp := ?mp, mpr := isUnit_of_isUnit_coeff_order }
  rintro ⟨⟨u, i, ui, iu⟩, rfl⟩
  refine'
    isUnit_of_mul_eq_one (u.coeff u.order) (i.coeff i.order)
      ((mul_coeff_order_add_order u i).symm.trans _)
  rw [ui, one_coeff, if_pos]
  rw [← order_mul (left_ne_zero_of_mul_eq_one ui) (right_ne_zero_of_mul_eq_one ui), ui, order_one]
#align hahn_series.is_unit_iff HahnSeries.isUnit_iff

end CommRing

instance [Field R] : Field (HahnSeries Γ R) :=
  { inferInstanceAs (IsDomain (HahnSeries Γ R)),
    inferInstanceAs (CommRing (HahnSeries Γ R)) with
    inv := fun x =>
      if x0 : x = 0 then 0
      else
        (single (-x.order)) (x.coeff x.order)⁻¹ *
          (SummableFamily.powers (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))).hsum
    inv_zero := dif_pos rfl
    mul_inv_cancel := fun x x0 => by
      refine' (congr rfl (dif_neg x0)).trans _
      have h :=
        SummableFamily.one_sub_self_mul_hsum_powers
          (unit_aux x (inv_mul_cancel (coeff_order_ne_zero x0)))
      rw [sub_sub_cancel] at h
      rw [← mul_assoc, mul_comm x, h]
    qsmul := qsmulRec _ }

end Inversion

section Binomial

variable [LinearOrderedAddCommGroup Γ] [CommRing R]

/-!
theorem order_binomial (g g' : Γ) (hgg' : g < g') (a b : R) (ha : a ≠ 0) :
    (single g a + single g' b).order = g := by
  rw [order]
-- write something in addition land.
  sorry

theorem isUnit_binomial (g g' : Γ) (hgg' : g < g') (a b : Units R) :
  IsUnit (single g a.val + single g' b.val) := by
  refine isUnit_of_isUnit_coeff_order ?_
  simp only [add_coeff', Pi.add_apply, single_coeff]

  sorry
-/

end Binomial

end HahnSeries
