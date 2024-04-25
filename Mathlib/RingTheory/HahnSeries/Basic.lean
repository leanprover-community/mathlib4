/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.Function.Support
import Mathlib.Order.WellFoundedSet

#align_import ring_theory.hahn_series from "leanprover-community/mathlib"@"a484a7d0eade4e1268f4fb402859b6686037f965"

/-!
# Hahn Series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`, with the most studied case being when `Γ` is
a linearly ordered abelian group and `R` is a field, in which case `HahnSeries Γ R` is a
valued field, with value group `Γ`.
These generalize Laurent series (with value group `ℤ`), and Laurent series are implemented that way
in the file `RingTheory/LaurentSeries`.

## Main Definitions
  * If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are partially well-ordered.
  * Laurent series over `R` are implemented as `HahnSeries ℤ R` in the file
    `RingTheory/LaurentSeries`.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

set_option linter.uppercaseLean3 false

open Finset Function
open scoped Classical

noncomputable section

/-- If `Γ` is linearly ordered and `R` has zero, then `HahnSeries Γ R` consists of
  formal series over `Γ` with coefficients in `R`, whose supports are well-founded. -/
@[ext]
structure HahnSeries (Γ : Type*) (R : Type*) [PartialOrder Γ] [Zero R] where
  coeff : Γ → R
  isPWO_support' : (Function.support coeff).IsPWO
#align hahn_series HahnSeries

variable {Γ : Type*} {R : Type*}

namespace HahnSeries

section Zero

variable [PartialOrder Γ] [Zero R]

theorem coeff_injective : Injective (coeff : HahnSeries Γ R → Γ → R) :=
  HahnSeries.ext
#align hahn_series.coeff_injective HahnSeries.coeff_injective

@[simp]
theorem coeff_inj {x y : HahnSeries Γ R} : x.coeff = y.coeff ↔ x = y :=
  coeff_injective.eq_iff
#align hahn_series.coeff_inj HahnSeries.coeff_inj

/-- The support of a Hahn series is just the set of indices whose coefficients are nonzero.
  Notably, it is well-founded. -/
nonrec def support (x : HahnSeries Γ R) : Set Γ :=
  support x.coeff
#align hahn_series.support HahnSeries.support

@[simp]
theorem isPWO_support (x : HahnSeries Γ R) : x.support.IsPWO :=
  x.isPWO_support'
#align hahn_series.is_pwo_support HahnSeries.isPWO_support

@[simp]
theorem isWF_support (x : HahnSeries Γ R) : x.support.IsWF :=
  x.isPWO_support.isWF
#align hahn_series.is_wf_support HahnSeries.isWF_support

@[simp]
theorem mem_support (x : HahnSeries Γ R) (a : Γ) : a ∈ x.support ↔ x.coeff a ≠ 0 :=
  Iff.refl _
#align hahn_series.mem_support HahnSeries.mem_support

instance : Zero (HahnSeries Γ R) :=
  ⟨{  coeff := 0
      isPWO_support' := by simp }⟩

instance : Inhabited (HahnSeries Γ R) :=
  ⟨0⟩

instance [Subsingleton R] : Subsingleton (HahnSeries Γ R) :=
  ⟨fun a b => a.ext b (Subsingleton.elim _ _)⟩

@[simp]
theorem zero_coeff {a : Γ} : (0 : HahnSeries Γ R).coeff a = 0 :=
  rfl
#align hahn_series.zero_coeff HahnSeries.zero_coeff

@[simp]
theorem coeff_fun_eq_zero_iff {x : HahnSeries Γ R} : x.coeff = 0 ↔ x = 0 :=
  coeff_injective.eq_iff' rfl
#align hahn_series.coeff_fun_eq_zero_iff HahnSeries.coeff_fun_eq_zero_iff

theorem ne_zero_of_coeff_ne_zero {x : HahnSeries Γ R} {g : Γ} (h : x.coeff g ≠ 0) : x ≠ 0 :=
  mt (fun x0 => (x0.symm ▸ zero_coeff : x.coeff g = 0)) h
#align hahn_series.ne_zero_of_coeff_ne_zero HahnSeries.ne_zero_of_coeff_ne_zero

@[simp]
theorem support_zero : support (0 : HahnSeries Γ R) = ∅ :=
  Function.support_zero
#align hahn_series.support_zero HahnSeries.support_zero

@[simp]
nonrec theorem support_nonempty_iff {x : HahnSeries Γ R} : x.support.Nonempty ↔ x ≠ 0 := by
  rw [support, support_nonempty_iff, Ne, coeff_fun_eq_zero_iff]
#align hahn_series.support_nonempty_iff HahnSeries.support_nonempty_iff

@[simp]
theorem support_eq_empty_iff {x : HahnSeries Γ R} : x.support = ∅ ↔ x = 0 :=
  support_eq_empty_iff.trans coeff_fun_eq_zero_iff
#align hahn_series.support_eq_empty_iff HahnSeries.support_eq_empty_iff

/-!
/-- Change a HahnSeries with coefficients in HahnSeries to a HahnSeries on the Lex product. -/
def of_iterate {Γ' : Type*} [PartialOrder Γ'] (x : HahnSeries Γ (HahnSeries Γ' R)) :
    HahnSeries (Γ ×ₗ Γ') R where
  coeff := fun g => coeff (coeff x g.1) g.2
  isPWO_support' := by
    intro f hf
    simp_all only
    have hf' : ∀ n, (f n).1 ∈ Function.support fun g ↦ x.coeff g := by
      intro n hn
      simp_all only [Function.mem_support, ne_eq]
      specialize hf n
      rw [hn] at hf
      exact hf rfl
    sorry
-- See Mathlib.Algebra.MvPolynomial.Monad for join and bind operations
need a monotone pair. have:
nonrec theorem IsPWO.exists_monotone_subseq (h : s.IsPWO) (f : ℕ → α) (hf : ∀ n, f n ∈ s) :
    ∃ g : ℕ ↪o ℕ, Monotone (f ∘ g) :=
  h.exists_monotone_subseq f hf
#align set.is_pwo.exists_monotone_subseq Set.IsPWO.exists_monotone_subseq
map sequence to Γ, get monotone subsequence (use ext property)
if stationary at a ∈ Γ, look inside {a} × Γ', get monotone subsequence.
if not stationary, use lex order.
/-- Change a Hahn series on a lex product to a Hahn series with coefficients in a Hahn series. -/
def to_iterate {Γ' : Type*} [PartialOrder Γ'] (x : HahnSeries (Γ ×ₗ Γ') R) :
    HahnSeries Γ (HahnSeries Γ' R) where
  coeff := fun g => {
    coeff := fun g' => coeff x (g, g')
    isPWO_support' := sorry
  }
  isPWO_support' := sorry
  * Equivalence between `HahnSeries Γ (HahnSeries Γ' R)` and `HahnSeries (Γ × Γ') R`
  * Use Set.WellFoundedOn.prod_lex_of_wellFoundedOn_fiber to iterate. (need PWO version)
-/

/-- `single a r` is the Hahn series which has coefficient `r` at `a` and zero otherwise. -/
def single (a : Γ) : ZeroHom R (HahnSeries Γ R) where
  toFun r :=
    { coeff := Pi.single a r
      isPWO_support' := (Set.isPWO_singleton a).mono Pi.support_single_subset }
  map_zero' := HahnSeries.ext _ _ (Pi.single_zero _)
#align hahn_series.single HahnSeries.single

variable {a b : Γ} {r : R}

@[simp]
theorem single_coeff_same (a : Γ) (r : R) : (single a r).coeff a = r :=
  Pi.single_eq_same (f := fun _ => R) a r
#align hahn_series.single_coeff_same HahnSeries.single_coeff_same

@[simp]
theorem single_coeff_of_ne (h : b ≠ a) : (single a r).coeff b = 0 :=
  Pi.single_eq_of_ne (f := fun _ => R) h r
#align hahn_series.single_coeff_of_ne HahnSeries.single_coeff_of_ne

theorem single_coeff : (single a r).coeff b = if b = a then r else 0 := by
  split_ifs with h <;> simp [h]
#align hahn_series.single_coeff HahnSeries.single_coeff

@[simp]
theorem support_single_of_ne (h : r ≠ 0) : support (single a r) = {a} :=
  Pi.support_single_of_ne h
#align hahn_series.support_single_of_ne HahnSeries.support_single_of_ne

theorem support_single_subset : support (single a r) ⊆ {a} :=
  Pi.support_single_subset
#align hahn_series.support_single_subset HahnSeries.support_single_subset

theorem eq_of_mem_support_single {b : Γ} (h : b ∈ support (single a r)) : b = a :=
  support_single_subset h
#align hahn_series.eq_of_mem_support_single HahnSeries.eq_of_mem_support_single

--@[simp] Porting note (#10618): simp can prove it
theorem single_eq_zero : single a (0 : R) = 0 :=
  (single a).map_zero
#align hahn_series.single_eq_zero HahnSeries.single_eq_zero

theorem single_injective (a : Γ) : Function.Injective (single a : R → HahnSeries Γ R) :=
  fun r s rs => by rw [← single_coeff_same a r, ← single_coeff_same a s, rs]
#align hahn_series.single_injective HahnSeries.single_injective

theorem single_ne_zero (h : r ≠ 0) : single a r ≠ 0 := fun con =>
  h (single_injective a (con.trans single_eq_zero.symm))
#align hahn_series.single_ne_zero HahnSeries.single_ne_zero

@[simp]
theorem single_eq_zero_iff {a : Γ} {r : R} : single a r = 0 ↔ r = 0 :=
  map_eq_zero_iff _ <| single_injective a
#align hahn_series.single_eq_zero_iff HahnSeries.single_eq_zero_iff

instance [Nonempty Γ] [Nontrivial R] : Nontrivial (HahnSeries Γ R) :=
  ⟨by
    obtain ⟨r, s, rs⟩ := exists_pair_ne R
    inhabit Γ
    refine' ⟨single default r, single default s, fun con => rs _⟩
    rw [← single_coeff_same (default : Γ) r, con, single_coeff_same]⟩

section Order

variable [Zero Γ]

/-- The order of a nonzero Hahn series `x` is a minimal element of `Γ` where `x` has a
  nonzero coefficient, the order of 0 is 0. -/
def order (x : HahnSeries Γ R) : Γ :=
  if h : x = 0 then 0 else x.isWF_support.min (support_nonempty_iff.2 h)
#align hahn_series.order HahnSeries.order

@[simp]
theorem order_zero : order (0 : HahnSeries Γ R) = 0 :=
  dif_pos rfl
#align hahn_series.order_zero HahnSeries.order_zero

theorem order_of_ne {x : HahnSeries Γ R} (hx : x ≠ 0) :
    order x = x.isWF_support.min (support_nonempty_iff.2 hx) :=
  dif_neg hx
#align hahn_series.order_of_ne HahnSeries.order_of_ne

theorem coeff_order_ne_zero {x : HahnSeries Γ R} (hx : x ≠ 0) : x.coeff x.order ≠ 0 := by
  rw [order_of_ne hx]
  exact x.isWF_support.min_mem (support_nonempty_iff.2 hx)
#align hahn_series.coeff_order_ne_zero HahnSeries.coeff_order_ne_zero

theorem order_le_of_coeff_ne_zero {Γ} [LinearOrderedCancelAddCommMonoid Γ] {x : HahnSeries Γ R}
    {g : Γ} (h : x.coeff g ≠ 0) : x.order ≤ g :=
  le_trans (le_of_eq (order_of_ne (ne_zero_of_coeff_ne_zero h)))
    (Set.IsWF.min_le _ _ ((mem_support _ _).2 h))
#align hahn_series.order_le_of_coeff_ne_zero HahnSeries.order_le_of_coeff_ne_zero

@[simp]
theorem order_single (h : r ≠ 0) : (single a r).order = a :=
  (order_of_ne (single_ne_zero h)).trans
    (support_single_subset
      ((single a r).isWF_support.min_mem (support_nonempty_iff.2 (single_ne_zero h))))
#align hahn_series.order_single HahnSeries.order_single

theorem coeff_eq_zero_of_lt_order {x : HahnSeries Γ R} {i : Γ} (hi : i < x.order) :
    x.coeff i = 0 := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
  contrapose! hi
  rw [← mem_support] at hi
  rw [order_of_ne hx]
  exact Set.IsWF.not_lt_min _ _ hi
#align hahn_series.coeff_eq_zero_of_lt_order HahnSeries.coeff_eq_zero_of_lt_order

end Order

section Domain

variable {Γ' : Type*} [PartialOrder Γ']

/-- Extends the domain of a `HahnSeries` by an `OrderEmbedding`. -/
def embDomain (f : Γ ↪o Γ') : HahnSeries Γ R → HahnSeries Γ' R := fun x =>
  { coeff := fun b : Γ' => if h : b ∈ f '' x.support then x.coeff (Classical.choose h) else 0
    isPWO_support' :=
      (x.isPWO_support.image_of_monotone f.monotone).mono fun b hb => by
        contrapose! hb
        rw [Function.mem_support, dif_neg hb, Classical.not_not] }
#align hahn_series.emb_domain HahnSeries.embDomain

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
#align hahn_series.emb_domain_coeff HahnSeries.embDomain_coeff

@[simp]
theorem embDomain_mk_coeff {f : Γ → Γ'} (hfi : Function.Injective f)
    (hf : ∀ g g' : Γ, f g ≤ f g' ↔ g ≤ g') {x : HahnSeries Γ R} {a : Γ} :
    (embDomain ⟨⟨f, hfi⟩, hf _ _⟩ x).coeff (f a) = x.coeff a :=
  embDomain_coeff
#align hahn_series.emb_domain_mk_coeff HahnSeries.embDomain_mk_coeff

theorem embDomain_notin_image_support {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'}
    (hb : b ∉ f '' x.support) : (embDomain f x).coeff b = 0 :=
  dif_neg hb
#align hahn_series.emb_domain_notin_image_support HahnSeries.embDomain_notin_image_support

theorem support_embDomain_subset {f : Γ ↪o Γ'} {x : HahnSeries Γ R} :
    support (embDomain f x) ⊆ f '' x.support := by
  intro g hg
  contrapose! hg
  rw [mem_support, embDomain_notin_image_support hg, Classical.not_not]
#align hahn_series.support_emb_domain_subset HahnSeries.support_embDomain_subset

theorem embDomain_notin_range {f : Γ ↪o Γ'} {x : HahnSeries Γ R} {b : Γ'} (hb : b ∉ Set.range f) :
    (embDomain f x).coeff b = 0 :=
  embDomain_notin_image_support fun con => hb (Set.image_subset_range _ _ con)
#align hahn_series.emb_domain_notin_range HahnSeries.embDomain_notin_range

@[simp]
theorem embDomain_zero {f : Γ ↪o Γ'} : embDomain f (0 : HahnSeries Γ R) = 0 := by
  ext
  simp [embDomain_notin_image_support]
#align hahn_series.emb_domain_zero HahnSeries.embDomain_zero

@[simp]
theorem embDomain_single {f : Γ ↪o Γ'} {g : Γ} {r : R} :
    embDomain f (single g r) = single (f g) r := by
  ext g'
  by_cases h : g' = f g
  · simp [h]
  rw [embDomain_notin_image_support, single_coeff_of_ne h]
  by_cases hr : r = 0
  · simp [hr]
  rwa [support_single_of_ne hr, Set.image_singleton, Set.mem_singleton_iff]
#align hahn_series.emb_domain_single HahnSeries.embDomain_single

theorem embDomain_injective {f : Γ ↪o Γ'} :
    Function.Injective (embDomain f : HahnSeries Γ R → HahnSeries Γ' R) := fun x y xy => by
  ext g
  rw [HahnSeries.ext_iff, Function.funext_iff] at xy
  have xyg := xy (f g)
  rwa [embDomain_coeff, embDomain_coeff] at xyg
#align hahn_series.emb_domain_injective HahnSeries.embDomain_injective

end Domain

end Zero

section LocallyFiniteLinearOrder

variable [Zero R] [LinearOrder Γ] [LocallyFiniteOrder Γ]

theorem suppBddBelow_supp_PWO (f : Γ → R) (hf : BddBelow (Function.support f)) :
    (Function.support f).IsPWO := Set.isWF_iff_isPWO.mp hf.wellFoundedOn_lt

theorem forallLTEqZero_supp_BddBelow (f : Γ → R) (n : Γ) (hn : ∀(m : Γ), m < n → f m = 0) :
    BddBelow (Function.support f) := by
  simp only [BddBelow, Set.Nonempty, lowerBounds]
  use n
  intro m hm
  rw [Function.mem_support, ne_eq] at hm
  exact not_lt.mp (mt (hn m) hm)

/-- Construct a Hahn series from any function whose support is bounded below. -/
@[simps]
def ofSuppBddBelow (f : Γ → R) (hf : BddBelow (Function.support f)) : HahnSeries Γ R where
  coeff := f
  isPWO_support' := suppBddBelow_supp_PWO f hf

theorem BddBelow_zero [Nonempty Γ] : BddBelow (Function.support (0 : Γ → R)) := by
  simp only [support_zero', bddBelow_empty]

@[simp]
theorem zero_ofSuppBddBelow [Nonempty Γ] : ofSuppBddBelow 0 BddBelow_zero = (0 : HahnSeries Γ R) :=
  rfl

theorem order_ofForallLtEqZero [Zero Γ] (f : Γ → R) (hf : f ≠ 0) (n : Γ)
    (hn : ∀(m : Γ), m < n → f m = 0) :
    n ≤ order (ofSuppBddBelow f (forallLTEqZero_supp_BddBelow f n hn)) := by
  dsimp only [order]
  by_cases h : ofSuppBddBelow f (forallLTEqZero_supp_BddBelow f n hn) = 0
  cases h
  exact (hf rfl).elim
  simp_all only [dite_false]
  rw [Set.IsWF.le_min_iff]
  intro m hm
  rw [HahnSeries.support, Function.mem_support, ne_eq] at hm
  exact not_lt.mp (mt (hn m) hm)

end LocallyFiniteLinearOrder

end HahnSeries
