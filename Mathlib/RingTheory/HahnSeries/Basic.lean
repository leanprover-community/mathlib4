/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.Group.Support
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Order.WellFoundedSet

/-!
# Hahn Series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`, with the most studied case being when `Γ` is
a linearly ordered abelian group and `R` is a field, in which case `HahnSeries Γ R` is a
valued field, with value group `Γ`.
These generalize Laurent series (with value group `ℤ`), and Laurent series are implemented that way
in the file `Mathlib/RingTheory/LaurentSeries.lean`.

## Main Definitions
* If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are partially well-ordered.
* `support x` is the subset of `Γ` whose coefficients are nonzero.
* `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise.
* `orderTop x` is a minimal element of `WithTop Γ` where `x` has a nonzero
  coefficient if `x ≠ 0`, and is `⊤` when `x = 0`.
* `order x` is a minimal element of `Γ` where `x` has a nonzero coefficient if `x ≠ 0`, and is zero
  when `x = 0`.
* `map` takes each coefficient of a Hahn series to its target under a zero-preserving map.
* `embDomain` preserves coefficients, but embeds the index set `Γ` in a larger poset.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/


open Finset Function

noncomputable section

/-- If `Γ` is linearly ordered and `R` has zero, then `HahnSeries Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded. -/
@[ext]
structure HahnSeries (Γ : Type*) (R : Type*) [PartialOrder Γ] [Zero R] where
  /-- The coefficient function of a Hahn Series. -/
  coeff : Γ → R
  isPWO_support' : (Function.support coeff).IsPWO

variable {Γ Γ' R S : Type*}

namespace HahnSeries

section Zero

variable [PartialOrder Γ] [Zero R]

theorem coeff_injective : Injective (coeff : HahnSeries Γ R → Γ → R) :=
  fun _ _ => HahnSeries.ext

@[simp]
theorem coeff_inj {x y : HahnSeries Γ R} : x.coeff = y.coeff ↔ x = y :=
  coeff_injective.eq_iff

/-- The support of a Hahn series is just the set of indices whose coefficients are nonzero.
  Notably, it is well-founded. -/
nonrec def support (x : HahnSeries Γ R) : Set Γ :=
  support x.coeff

@[simp]
theorem isPWO_support (x : HahnSeries Γ R) : x.support.IsPWO :=
  x.isPWO_support'

@[simp]
theorem isWF_support (x : HahnSeries Γ R) : x.support.IsWF :=
  x.isPWO_support.isWF

@[simp]
theorem mem_support (x : HahnSeries Γ R) (a : Γ) : a ∈ x.support ↔ x.coeff a ≠ 0 :=
  Iff.refl _

instance : Zero (HahnSeries Γ R) :=
  ⟨{  coeff := 0
      isPWO_support' := by simp }⟩

instance : Inhabited (HahnSeries Γ R) :=
  ⟨0⟩

instance [Subsingleton R] : Subsingleton (HahnSeries Γ R) :=
  ⟨fun _ _ => HahnSeries.ext (by subsingleton)⟩

theorem coeff_zero' : (0 : HahnSeries Γ R).coeff = 0 :=
  rfl

@[simp]
theorem coeff_zero {a : Γ} : (0 : HahnSeries Γ R).coeff a = 0 :=
  rfl

@[deprecated (since := "2025-01-31")] alias zero_coeff := coeff_zero

@[simp]
theorem coeff_fun_eq_zero_iff {x : HahnSeries Γ R} : x.coeff = 0 ↔ x = 0 :=
  coeff_injective.eq_iff' rfl

theorem ne_zero_of_coeff_ne_zero {x : HahnSeries Γ R} {g : Γ} (h : x.coeff g ≠ 0) : x ≠ 0 :=
  mt (fun x0 => (x0.symm ▸ coeff_zero : x.coeff g = 0)) h

@[simp]
theorem support_zero : support (0 : HahnSeries Γ R) = ∅ :=
  Function.support_zero

@[simp]
nonrec theorem support_nonempty_iff {x : HahnSeries Γ R} : x.support.Nonempty ↔ x ≠ 0 := by
  rw [support, support_nonempty_iff, Ne, coeff_fun_eq_zero_iff]

@[simp]
theorem support_eq_empty_iff {x : HahnSeries Γ R} : x.support = ∅ ↔ x = 0 :=
  Function.support_eq_empty_iff.trans coeff_fun_eq_zero_iff

/-- The map of Hahn series induced by applying a zero-preserving map to each coefficient. -/
@[simps]
def map [Zero S] (x : HahnSeries Γ R) {F : Type*} [FunLike F R S] [ZeroHomClass F R S] (f : F) :
    HahnSeries Γ S where
  coeff g := f (x.coeff g)
  isPWO_support' := x.isPWO_support.mono <| Function.support_comp_subset (ZeroHomClass.map_zero f) _

@[simp]
protected lemma map_zero [Zero S] (f : ZeroHom R S) :
    (0 : HahnSeries Γ R).map f = 0 := by
  ext; simp

/-- Change a HahnSeries with coefficients in HahnSeries to a HahnSeries on the Lex product. -/
def ofIterate [PartialOrder Γ'] (x : HahnSeries Γ (HahnSeries Γ' R)) :
    HahnSeries (Γ ×ₗ Γ') R where
  coeff := fun g => coeff (coeff x g.1) g.2
  isPWO_support' := by
    refine Set.PartiallyWellOrderedOn.subsetProdLex ?_ ?_
    · refine Set.IsPWO.mono x.isPWO_support' ?_
      simp_rw [Set.image_subset_iff, support_subset_iff, Set.mem_preimage, Function.mem_support]
      exact fun _ ↦ ne_zero_of_coeff_ne_zero
    · exact fun a => by simpa [Function.mem_support, ne_eq] using (x.coeff a).isPWO_support'

@[simp]
lemma mk_eq_zero (f : Γ → R) (h) : HahnSeries.mk f h = 0 ↔ f = 0 := by
  simp_rw [HahnSeries.ext_iff, funext_iff, coeff_zero, Pi.zero_apply]

/-- Change a Hahn series on a lex product to a Hahn series with coefficients in a Hahn series. -/
def toIterate [PartialOrder Γ'] (x : HahnSeries (Γ ×ₗ Γ') R) :
    HahnSeries Γ (HahnSeries Γ' R) where
  coeff := fun g => {
    coeff := fun g' => coeff x (g, g')
    isPWO_support' := Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_support' g
  }
  isPWO_support' := by
    have h₁ : (Function.support fun g => HahnSeries.mk (fun g' => x.coeff (g, g'))
        (Set.PartiallyWellOrderedOn.fiberProdLex x.isPWO_support' g)) = Function.support
        fun g => fun g' => x.coeff (g, g') := by
      simp only [Function.support, ne_eq, mk_eq_zero]
    rw [h₁, Function.support_curry' x.coeff]
    exact Set.PartiallyWellOrderedOn.imageProdLex x.isPWO_support'

/-- The equivalence between iterated Hahn series and Hahn series on the lex product. -/
@[simps]
def iterateEquiv [PartialOrder Γ'] :
    HahnSeries Γ (HahnSeries Γ' R) ≃ HahnSeries (Γ ×ₗ Γ') R where
  toFun := ofIterate
  invFun := toIterate
  left_inv := congrFun rfl
  right_inv := congrFun rfl

open Classical in
/-- `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. -/
def single (a : Γ) : ZeroHom R (HahnSeries Γ R) where
  toFun r :=
    { coeff := Pi.single a r
      isPWO_support' := (Set.isPWO_singleton a).mono Pi.support_single_subset }
  map_zero' := HahnSeries.ext (Pi.single_zero _)

variable {a b : Γ} {r : R}

@[simp]
theorem coeff_single_same (a : Γ) (r : R) : (single a r).coeff a = r := by
  classical exact Pi.single_eq_same (M := fun _ => R) a r

@[deprecated (since := "2025-01-31")] alias single_coeff_same := coeff_single_same

@[simp]
theorem coeff_single_of_ne (h : b ≠ a) : (single a r).coeff b = 0 := by
  classical exact Pi.single_eq_of_ne (M := fun _ => R) h r

@[deprecated (since := "2025-01-31")] alias single_coeff_of_ne := coeff_single_of_ne

open Classical in
theorem coeff_single : (single a r).coeff b = if b = a then r else 0 := by
  split_ifs with h <;> simp [h]

@[deprecated (since := "2025-01-31")] alias single_coeff := coeff_single

@[simp]
theorem support_single_of_ne (h : r ≠ 0) : support (single a r) = {a} := by
  classical exact Pi.support_single_of_ne h

theorem support_single_subset : support (single a r) ⊆ {a} := by
  classical exact Pi.support_single_subset

theorem eq_of_mem_support_single {b : Γ} (h : b ∈ support (single a r)) : b = a :=
  support_single_subset h

theorem single_eq_zero : single a (0 : R) = 0 :=
  (single a).map_zero

theorem single_injective (a : Γ) : Function.Injective (single a : R → HahnSeries Γ R) :=
  fun r s rs => by rw [← coeff_single_same a r, ← coeff_single_same a s, rs]

theorem single_ne_zero (h : r ≠ 0) : single a r ≠ 0 := fun con =>
  h (single_injective a (con.trans single_eq_zero.symm))

@[simp]
theorem single_eq_zero_iff {a : Γ} {r : R} : single a r = 0 ↔ r = 0 :=
  map_eq_zero_iff _ <| single_injective a

@[simp]
protected lemma map_single [Zero S] (f : ZeroHom R S) : (single a r).map f = single a (f r) := by
  ext g
  by_cases h : g = a <;> simp [h]

instance [Nonempty Γ] [Nontrivial R] : Nontrivial (HahnSeries Γ R) :=
  ⟨by
    obtain ⟨r, s, rs⟩ := exists_pair_ne R
    inhabit Γ
    refine ⟨single default r, single default s, fun con => rs ?_⟩
    rw [← coeff_single_same (default : Γ) r, con, coeff_single_same]⟩

section Order

open Classical in
/-- The orderTop of a Hahn series `x` is a minimal element of `WithTop Γ` where `x` has a nonzero
coefficient if `x ≠ 0`, and is `⊤` when `x = 0`. -/
def orderTop (x : HahnSeries Γ R) : WithTop Γ :=
  if h : x = 0 then ⊤ else x.isWF_support.min (support_nonempty_iff.2 h)

@[simp]
theorem orderTop_zero : orderTop (0 : HahnSeries Γ R) = ⊤ :=
  dif_pos rfl

@[simp]
theorem orderTop_of_Subsingleton [Subsingleton R] {x : HahnSeries Γ R} : x.orderTop = ⊤ :=
  (Subsingleton.eq_zero x) ▸ orderTop_zero

theorem orderTop_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) :
    orderTop x = x.isWF_support.min (support_nonempty_iff.2 hx) :=
  dif_neg hx

@[simp]
theorem ne_zero_iff_orderTop {x : HahnSeries Γ R} : x ≠ 0 ↔ orderTop x ≠ ⊤ := by
  constructor
  · exact fun hx => Eq.mpr (congrArg (fun h ↦ h ≠ ⊤) (orderTop_of_ne hx)) WithTop.coe_ne_top
  · contrapose!
    simp_all only [orderTop_zero, implies_true]

theorem orderTop_eq_top_iff {x : HahnSeries Γ R} : orderTop x = ⊤ ↔ x = 0 := by
  constructor
  · contrapose!
    exact ne_zero_iff_orderTop.mp
  · simp_all only [orderTop_zero, implies_true]

theorem orderTop_eq_of_le {x : HahnSeries Γ R} {g : Γ} (hg : g ∈ x.support)
    (hx : ∀ g' ∈ x.support, g ≤ g') : orderTop x = g := by
  rw [orderTop_of_ne <| support_nonempty_iff.mp <| Set.nonempty_of_mem hg,
    x.isWF_support.min_eq_of_le hg hx]

theorem untop_orderTop_of_ne_zero {x : HahnSeries Γ R} (hx : x ≠ 0) :
    WithTop.untop x.orderTop (ne_zero_iff_orderTop.mp hx) =
      x.isWF_support.min (support_nonempty_iff.2 hx) :=
  WithTop.coe_inj.mp ((WithTop.coe_untop (orderTop x) (ne_zero_iff_orderTop.mp hx)).trans
    (orderTop_of_ne hx))

theorem coeff_orderTop_ne {x : HahnSeries Γ R} {g : Γ} (hg : x.orderTop = g) :
    x.coeff g ≠ 0 := by
  have h : orderTop x ≠ ⊤ := by simp_all only [ne_eq, WithTop.coe_ne_top, not_false_eq_true]
  have hx : x ≠ 0 := ne_zero_iff_orderTop.mpr h
  rw [orderTop_of_ne hx, WithTop.coe_eq_coe] at hg
  rw [← hg]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)

theorem orderTop_le_of_coeff_ne_zero {Γ} [LinearOrder Γ] {x : HahnSeries Γ R}
    {g : Γ} (h : x.coeff g ≠ 0) : x.orderTop ≤ g := by
  rw [orderTop_of_ne (ne_zero_of_coeff_ne_zero h), WithTop.coe_le_coe]
  exact Set.IsWF.min_le _ _ ((mem_support _ _).2 h)

@[simp]
theorem orderTop_single (h : r ≠ 0) : (single a r).orderTop = a :=
  (orderTop_of_ne (single_ne_zero h)).trans
    (WithTop.coe_inj.mpr (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h)))))

theorem orderTop_single_le : a ≤ (single a r).orderTop := by
  by_cases hr : r = 0
  · simp only [hr, map_zero, orderTop_zero, le_top]
  · rw [orderTop_single hr]

theorem lt_orderTop_single {g g' : Γ} (hgg' : g < g') : g < (single g' r).orderTop :=
  lt_of_lt_of_le (WithTop.coe_lt_coe.mpr hgg') orderTop_single_le

theorem coeff_eq_zero_of_lt_orderTop {x : HahnSeries Γ R} {i : Γ} (hi : i < x.orderTop) :
    x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · exact coeff_zero
  contrapose! hi
  rw [← mem_support] at hi
  rw [orderTop_of_ne hx, WithTop.coe_lt_coe]
  exact Set.IsWF.not_lt_min _ _ hi

open Classical in
/-- A leading coefficient of a Hahn series is the coefficient of a lowest-order nonzero term, or
zero if the series vanishes. -/
def leadingCoeff (x : HahnSeries Γ R) : R :=
  if h : x = 0 then 0 else x.coeff (x.isWF_support.min (support_nonempty_iff.2 h))

@[simp]
theorem leadingCoeff_zero : leadingCoeff (0 : HahnSeries Γ R) = 0 :=
  dif_pos rfl

theorem leadingCoeff_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) :
    x.leadingCoeff = x.coeff (x.isWF_support.min (support_nonempty_iff.2 hx)) :=
  dif_neg hx

theorem leadingCoeff_eq_iff {x : HahnSeries Γ R} : x.leadingCoeff = 0 ↔ x = 0 := by
  refine { mp := ?_, mpr := fun hx => hx ▸ leadingCoeff_zero }
  contrapose!
  exact fun hx => (leadingCoeff_of_ne hx) ▸ coeff_orderTop_ne (orderTop_of_ne hx)

theorem leadingCoeff_ne_iff {x : HahnSeries Γ R} : x.leadingCoeff ≠ 0 ↔ x ≠ 0 :=
  leadingCoeff_eq_iff.not

@[simp]
theorem leadingCoeff_of_single {a : Γ} {r : R} : leadingCoeff (single a r) = r := by
  simp only [leadingCoeff, single_eq_zero_iff]
  by_cases h : r = 0 <;> simp [h]

theorem coeff_untop_eq_leadingCoeff {x : HahnSeries Γ R} (hx : x ≠ 0) :
    x.coeff (x.orderTop.untop (ne_zero_iff_orderTop.mp hx)) = x.leadingCoeff := by
  rw [HahnSeries.leadingCoeff_of_ne hx, (WithTop.untop_eq_iff _).mpr (HahnSeries.orderTop_of_ne hx)]

variable [Zero Γ]

open Classical in
/-- The order of a nonzero Hahn series `x` is a minimal element of `Γ` where `x` has a
  nonzero coefficient, the order of 0 is 0. -/
def order (x : HahnSeries Γ R) : Γ :=
  if h : x = 0 then 0 else x.isWF_support.min (support_nonempty_iff.2 h)

@[simp]
theorem order_zero : order (0 : HahnSeries Γ R) = 0 :=
  dif_pos rfl

theorem order_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) :
    order x = x.isWF_support.min (support_nonempty_iff.2 hx) :=
  dif_neg hx

theorem order_eq_orderTop_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) : order x = orderTop x := by
  rw [order_of_ne hx, orderTop_of_ne hx]

theorem coeff_order_ne_zero {x : HahnSeries Γ R} (hx : x ≠ 0) : x.coeff x.order ≠ 0 := by
  rw [order_of_ne hx]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)

theorem order_le_of_coeff_ne_zero {Γ} [Zero Γ] [LinearOrder Γ] {x : HahnSeries Γ R}
    {g : Γ} (h : x.coeff g ≠ 0) : x.order ≤ g :=
  le_trans (le_of_eq (order_of_ne (ne_zero_of_coeff_ne_zero h)))
    (Set.IsWF.min_le _ _ ((mem_support _ _).2 h))

@[simp]
theorem order_single (h : r ≠ 0) : (single a r).order = a :=
  (order_of_ne (single_ne_zero h)).trans
    (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h))))

theorem coeff_eq_zero_of_lt_order {x : HahnSeries Γ R} {i : Γ} (hi : i < x.order) :
    x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  contrapose! hi
  rw [← mem_support] at hi
  rw [order_of_ne hx]
  exact Set.IsWF.not_lt_min _ _ hi

theorem zero_lt_orderTop_iff {x : HahnSeries Γ R} (hx : x ≠ 0) :
    0 < x.orderTop ↔ 0 < x.order := by
  simp_all [orderTop_of_ne hx, order_of_ne hx]

theorem zero_lt_orderTop_of_order {x : HahnSeries Γ R} (hx : 0 < x.order) : 0 < x.orderTop := by
  by_cases h : x = 0
  · simp_all only [order_zero, lt_self_iff_false]
  · exact (zero_lt_orderTop_iff h).mpr hx

theorem zero_le_orderTop_iff {x : HahnSeries Γ R} : 0 ≤ x.orderTop ↔ 0 ≤ x.order := by
  by_cases h : x = 0
  · simp_all
  · simp_all [order_of_ne h, orderTop_of_ne h]

theorem leadingCoeff_eq {x : HahnSeries Γ R} : x.leadingCoeff = x.coeff x.order := by
  by_cases h : x = 0
  · rw [h, leadingCoeff_zero, coeff_zero]
  · rw [leadingCoeff_of_ne h, order_of_ne h]

end Order

section Domain

variable [PartialOrder Γ']

open Classical in
/-- Extends the domain of a `HahnSeries` by an `OrderEmbedding`. -/
def embDomain (f : Γ ↪o Γ') : HahnSeries Γ R → HahnSeries Γ' R := fun x =>
  { coeff := fun b : Γ' => if h : b ∈ f '' x.support then x.coeff (Classical.choose h) else 0
    isPWO_support' :=
      (x.isPWO_support.image_of_monotone f.monotone).mono fun b hb => by
        contrapose! hb
        rw [Function.mem_support, dif_neg hb, Classical.not_not] }

@[simp]
theorem embDomain_coeff {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {a : Γ} :
    (embDomain f x).coeff (f a) = x.coeff a := by
  rw [embDomain]
  dsimp only
  by_cases ha : a ∈ x.support
  · rw [dif_pos (Set.mem_image_of_mem f ha)]
    exact congr rfl (f.injective (Classical.choose_spec (Set.mem_image_of_mem f ha)).2)
  · rw [dif_neg, Classical.not_not.1 fun c => ha ((mem_support _ _).2 c)]
    contrapose! ha
    obtain ⟨b, hb1, hb2⟩ := (Set.mem_image _ _ _).1 ha
    rwa [f.injective hb2] at hb1

@[simp]
theorem embDomain_mk_coeff {f : Γ → Γ'} (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') {x : HahnSeries Γ R} {a : Γ} :
    (embDomain ⟨⟨f, hfi⟩, hf _ _⟩ x).coeff (f a) = x.coeff a :=
  embDomain_coeff

theorem embDomain_notin_image_support {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'}
    (hb : b ∉ f '' x.support) : (embDomain f x).coeff b = 0 :=
  dif_neg hb

theorem support_embDomain_subset {f : Γ ↪o Γ'} {x : HahnSeries Γ R} :
    support (embDomain f x) ⊆ f '' x.support := by
  intro g hg
  contrapose! hg
  rw [mem_support, embDomain_notin_image_support hg, Classical.not_not]

theorem embDomain_notin_range {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'} (hb : b ∉ Set.range f) :
    (embDomain f x).coeff b = 0 :=
  embDomain_notin_image_support fun con => hb (Set.image_subset_range _ _ con)

@[simp]
theorem embDomain_zero {f : Γ ↪o Γ'} : embDomain f (0 : HahnSeries Γ R) = 0 := by
  ext
  simp [embDomain_notin_image_support]

@[simp]
theorem embDomain_single {f : Γ ↪o Γ'} {g : Γ} {r : R} :
    embDomain f (single g r) = single (f g) r := by
  ext g'
  by_cases h : g' = f g
  · simp [h]
  rw [embDomain_notin_image_support, coeff_single_of_ne h]
  by_cases hr : r = 0
  · simp [hr]
  rwa [support_single_of_ne hr, Set.image_singleton, Set.mem_singleton_iff]

theorem embDomain_injective {f : Γ ↪o Γ'} :
    Function.Injective (embDomain f : HahnSeries Γ R → HahnSeries Γ' R) := fun x y xy => by
  ext g
  rw [HahnSeries.ext_iff, funext_iff] at xy
  have xyg := xy (f g)
  rwa [embDomain_coeff, embDomain_coeff] at xyg

end Domain

end Zero

section LocallyFiniteLinearOrder

variable [Zero R] [LinearOrder Γ]

theorem forallLTEqZero_supp_BddBelow (f : Γ → R) (n : Γ) (hn : ∀ (m : Γ), m < n → f m = 0) :
    BddBelow (Function.support f) := by
  simp only [BddBelow, Set.Nonempty, lowerBounds]
  use n
  intro m hm
  rw [Function.mem_support, ne_eq] at hm
  exact not_lt.mp (mt (hn m) hm)

theorem BddBelow_zero [Nonempty Γ] : BddBelow (Function.support (0 : Γ → R)) := by
  simp only [support_zero', bddBelow_empty]

variable [LocallyFiniteOrder Γ]

theorem suppBddBelow_supp_PWO (f : Γ → R) (hf : BddBelow (Function.support f)) :
    (Function.support f).IsPWO :=
  hf.isWF.isPWO

/-- Construct a Hahn series from any function whose support is bounded below. -/
@[simps]
def ofSuppBddBelow (f : Γ → R) (hf : BddBelow (Function.support f)) : HahnSeries Γ R where
  coeff := f
  isPWO_support' := suppBddBelow_supp_PWO f hf

@[simp]
theorem zero_ofSuppBddBelow [Nonempty Γ] : ofSuppBddBelow 0 BddBelow_zero = (0 : HahnSeries Γ R) :=
  rfl

theorem order_ofForallLtEqZero [Zero Γ] (f : Γ → R) (hf : f ≠ 0) (n : Γ)
    (hn : ∀ (m : Γ), m < n → f m = 0) :
    n ≤ order (ofSuppBddBelow f (forallLTEqZero_supp_BddBelow f n hn)) := by
  dsimp only [order]
  by_cases h : ofSuppBddBelow f (forallLTEqZero_supp_BddBelow f n hn) = 0
  cases h
  · exact (hf rfl).elim
  simp_all only [dite_false]
  rw [Set.IsWF.le_min_iff]
  intro m hm
  rw [HahnSeries.support, Function.mem_support, ne_eq] at hm
  exact not_lt.mp (mt (hn m) hm)

end LocallyFiniteLinearOrder

section Truncate
variable [Zero R]

/-- Zeros out coefficients of a `HahnSeries` at indices equal to or greater than `c`. -/
@[simps]
def truncate [PartialOrder Γ] (c : Γ) (x : HahnSeries Γ R) : HahnSeries Γ R where
  coeff i := open Classical in if c ≤ i then 0 else x.coeff i
  isPWO_support' := Set.IsPWO.mono x.isPWO_support (by simp)

theorem coeff_truncate_eq [LinearOrder Γ] {c i : Γ} (h : i < c) (x : HahnSeries Γ R) :
    (truncate c x).coeff i = x.coeff i := by
  simp [not_le_of_gt h]

theorem coeff_truncate_eq_zero [PartialOrder Γ] {c i : Γ} (h : c ≤ i) (x : HahnSeries Γ R) :
    (truncate c x).coeff i = 0 := by
  simp [h]


end Truncate

end HahnSeries
