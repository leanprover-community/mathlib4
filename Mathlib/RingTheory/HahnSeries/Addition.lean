/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.RingTheory.HahnSeries.Basic

#align_import ring_theory.hahn_series from "leanprover-community/mathlib"@"a484a7d0eade4e1268f4fb402859b6686037f965"

/-!
# Additive properties of Hahn series
If `Γ` is ordered and `R` has zero, then `HahnSeries Γ R` consists of formal series over `Γ` with
coefficients in `R`, whose supports are partially well-ordered. With further structure on `R` and
`Γ`, we can add further structure on `HahnSeries Γ R`.  When `R` has an addition operation,
`HahnSeries Γ R` also has addition by adding coefficients.

## Main Definitions
  * If `R` is a (commutative) additive monoid or group, then so is `HahnSeries Γ R`.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

set_option linter.uppercaseLean3 false

open Finset Function

open scoped Classical
open BigOperators

noncomputable section

variable {Γ R : Type*}

namespace HahnSeries

section Addition

variable [PartialOrder Γ]

section AddMonoid

variable [AddMonoid R]

instance : Add (HahnSeries Γ R) where
  add x y :=
    { coeff := x.coeff + y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_add _ _) }

instance : AddMonoid (HahnSeries Γ R) where
  zero := 0
  add := (· + ·)
  nsmul := nsmulRec
  add_assoc x y z := by
    ext
    apply add_assoc
  zero_add x := by
    ext
    apply zero_add
  add_zero x := by
    ext
    apply add_zero

@[simp]
theorem add_coeff' {x y : HahnSeries Γ R} : (x + y).coeff = x.coeff + y.coeff :=
  rfl
#align hahn_series.add_coeff' HahnSeries.add_coeff'

theorem add_coeff {x y : HahnSeries Γ R} {a : Γ} : (x + y).coeff a = x.coeff a + y.coeff a :=
  rfl
#align hahn_series.add_coeff HahnSeries.add_coeff

theorem support_add_subset {x y : HahnSeries Γ R} : support (x + y) ⊆ support x ∪ support y :=
  fun a ha => by
  rw [mem_support, add_coeff] at ha
  rw [Set.mem_union, mem_support, mem_support]
  contrapose! ha
  rw [ha.1, ha.2, add_zero]
#align hahn_series.support_add_subset HahnSeries.support_add_subset

theorem IsMinWFMinLEWFMinAdd {Γ} [LinearOrder Γ] {x y : HahnSeries Γ R} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : x + y ≠ 0) : min (Set.IsWF.min x.isWF_support (support_nonempty_iff.2 hx))
      (Set.IsWF.min y.isWF_support (support_nonempty_iff.2 hy)) ≤
      Set.IsWF.min (x + y).isWF_support (support_nonempty_iff.2 hxy) := by
  rw [(Set.IsWF.min_union _ _ _ _).symm]
  exact Set.IsWF.min_le_min_of_subset (support_add_subset (x := x) (y := y))

theorem min_orderTop_le_orderTop_add {Γ} [LinearOrder Γ] {x y : HahnSeries Γ R} :
    min x.orderTop y.orderTop ≤ (x + y).orderTop := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  by_cases hxy : x + y = 0; · simp [hxy]
  rw [orderTop_of_ne hx, orderTop_of_ne hy, orderTop_of_ne hxy, ← @WithTop.coe_min,
    WithTop.coe_le_coe]
  exact IsMinWFMinLEWFMinAdd hx hy hxy

theorem min_order_le_order_add {Γ} [Zero Γ] [LinearOrder Γ] {x y : HahnSeries Γ R}
    (hxy : x + y ≠ 0) : min x.order y.order ≤ (x + y).order := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [order_of_ne hx, order_of_ne hy, order_of_ne hxy]
  exact IsMinWFMinLEWFMinAdd hx hy hxy
#align hahn_series.min_order_le_order_add HahnSeries.min_order_le_order_add

theorem orderTop_add_eq {Γ} [Zero Γ] [LinearOrder Γ] {x y : HahnSeries Γ R}
    (hxy : x.orderTop < y.orderTop) : (x + y).orderTop = x.orderTop := by
  have hx : x ≠ 0 := ne_zero_iff_orderTop.mpr <| LT.lt.ne_top hxy
  let g : Γ := WithTop.untop x.orderTop (ne_zero_iff_orderTop.mp hx)
  have hg : g = x.orderTop := untop_orderTop_of_ne_zero hx
  have hcxyne : (x+y).coeff g ≠ 0 := by
    rw [show (x+y).coeff g = x.coeff g + y.coeff g from rfl,
      coeff_eq_zero_of_lt_orderTop (lt_of_eq_of_lt hg hxy), add_zero]
    exact coeff_orderTop_ne_zero hx hg.symm
  have hxyx : (x + y).orderTop ≤ x.orderTop := by
    rw [← hg]
    exact orderTop_le_of_coeff_ne_zero hcxyne
  exact le_antisymm hxyx (le_of_eq_of_le (min_eq_left_of_lt hxy).symm min_orderTop_le_orderTop_add)

/-- `single` as an additive monoid/group homomorphism -/
@[simps!]
def single.addMonoidHom (a : Γ) : R →+ HahnSeries Γ R :=
  { single a with
    map_add' := fun x y => by
      ext b
      by_cases h : b = a <;> simp [h] }
#align hahn_series.single.add_monoid_hom HahnSeries.single.addMonoidHom

/-- `coeff g` as an additive monoid/group homomorphism -/
@[simps]
def coeff.addMonoidHom (g : Γ) : HahnSeries Γ R →+ R where
  toFun f := f.coeff g
  map_zero' := zero_coeff
  map_add' _ _ := add_coeff
#align hahn_series.coeff.add_monoid_hom HahnSeries.coeff.addMonoidHom

section Domain

variable {Γ' : Type*} [PartialOrder Γ']

theorem embDomain_add (f : Γ ↪o Γ') (x y : HahnSeries Γ R) :
    embDomain f (x + y) = embDomain f x + embDomain f y := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_notin_range hg]
#align hahn_series.emb_domain_add HahnSeries.embDomain_add

end Domain

end AddMonoid

instance [AddCommMonoid R] : AddCommMonoid (HahnSeries Γ R) :=
  { inferInstanceAs (AddMonoid (HahnSeries Γ R)) with
    add_comm := fun x y => by
      ext
      apply add_comm }

section AddGroup

variable [AddGroup R]

instance : Neg (HahnSeries Γ R) where
  neg x :=
    { coeff := fun a => -x.coeff a
      isPWO_support' := by
        rw [Function.support_neg]
        exact x.isPWO_support }

instance : AddGroup (HahnSeries Γ R) :=
  { inferInstanceAs (AddMonoid (HahnSeries Γ R)) with
    zsmul := zsmulRec
    add_left_neg := fun x => by
      ext
      apply add_left_neg }

@[simp]
theorem neg_coeff' {x : HahnSeries Γ R} : (-x).coeff = -x.coeff :=
  rfl
#align hahn_series.neg_coeff' HahnSeries.neg_coeff'

theorem neg_coeff {x : HahnSeries Γ R} {a : Γ} : (-x).coeff a = -x.coeff a :=
  rfl
#align hahn_series.neg_coeff HahnSeries.neg_coeff

@[simp]
theorem support_neg {x : HahnSeries Γ R} : (-x).support = x.support := by
  ext
  simp
#align hahn_series.support_neg HahnSeries.support_neg

@[simp]
theorem sub_coeff' {x y : HahnSeries Γ R} : (x - y).coeff = x.coeff - y.coeff := by
  ext
  simp [sub_eq_add_neg]
#align hahn_series.sub_coeff' HahnSeries.sub_coeff'

theorem sub_coeff {x y : HahnSeries Γ R} {a : Γ} : (x - y).coeff a = x.coeff a - y.coeff a := by
  simp
#align hahn_series.sub_coeff HahnSeries.sub_coeff

@[simp]
theorem order_neg [Zero Γ] {f : HahnSeries Γ R} : (-f).order = f.order := by
  by_cases hf : f = 0
  · simp only [hf, neg_zero]
  simp only [order, support_neg, neg_eq_zero]
#align hahn_series.order_neg HahnSeries.order_neg

end AddGroup

instance [AddCommGroup R] : AddCommGroup (HahnSeries Γ R) :=
  { inferInstanceAs (AddCommMonoid (HahnSeries Γ R)),
    inferInstanceAs (AddGroup (HahnSeries Γ R)) with }

end Addition

section SMulZeroClass

variable [PartialOrder Γ] {V : Type*} [Zero V] [SMulZeroClass R V]

instance : SMul R (HahnSeries Γ V) :=
  ⟨fun r x =>
    { coeff := r • x.coeff
      isPWO_support' := x.isPWO_support.mono (Function.support_const_smul_subset r x.coeff) }⟩

@[simp]
theorem smul_coeff {r : R} {x : HahnSeries Γ V} {a : Γ} : (r • x).coeff a = r • x.coeff a :=
  rfl
#align hahn_series.smul_coeff HahnSeries.smul_coeff

instance : SMulZeroClass R (HahnSeries Γ V) :=
  { inferInstanceAs (SMul R (HahnSeries Γ V)) with
    smul_zero := by
      intro
      ext
      simp only [smul_coeff, zero_coeff, smul_zero]}

theorem order_smul_not_lt [Zero Γ] (r : R) (x : HahnSeries Γ V) (h : r • x ≠ 0) :
    ¬ (r • x).order < x.order := by
  have hx : x ≠ 0 := right_ne_zero_of_smul h
  simp_all only [order, dite_false]
  exact Set.IsWF.min_of_subset_not_lt_min (Function.support_smul_subset_right (fun _ => r) x.coeff)

theorem le_order_smul {Γ} [Zero Γ] [LinearOrder Γ] (r : R) (x : HahnSeries Γ V) (h : r • x ≠ 0) :
    x.order ≤ (r • x).order := le_of_not_lt (order_smul_not_lt r x h)

end SMulZeroClass

section DistribMulAction

variable [PartialOrder Γ] {V : Type*} [Monoid R] [AddMonoid V] [DistribMulAction R V]

instance : DistribMulAction R (HahnSeries Γ V) where
  smul := (· • ·)
  one_smul _ := by
    ext
    simp
  smul_zero _ := by
    ext
    simp
  smul_add _ _ _ := by
    ext
    simp [smul_add]
  mul_smul _ _ _ := by
    ext
    simp [mul_smul]

variable {S : Type*} [Monoid S] [DistribMulAction S V]

instance [SMul R S] [IsScalarTower R S V] : IsScalarTower R S (HahnSeries Γ V) :=
  ⟨fun r s a => by
    ext
    simp⟩

instance [SMulCommClass R S V] : SMulCommClass R S (HahnSeries Γ V) :=
  ⟨fun r s a => by
    ext
    simp [smul_comm]⟩

end DistribMulAction

section Module

variable [PartialOrder Γ] [Semiring R] {V : Type*} [AddCommMonoid V] [Module R V]

instance : Module R (HahnSeries Γ V) :=
  { inferInstanceAs (DistribMulAction R (HahnSeries Γ V)) with
    zero_smul := fun _ => by
      ext
      simp
    add_smul := fun _ _ _ => by
      ext
      simp [add_smul] }

/-- `single` as a linear map -/
@[simps]
def single.linearMap (a : Γ) : V →ₗ[R] HahnSeries Γ V :=
  { single.addMonoidHom a with
    map_smul' := fun r s => by
      ext b
      by_cases h : b = a <;> simp [h] }
#align hahn_series.single.linear_map HahnSeries.single.linearMap

/-- `coeff g` as a linear map -/
@[simps]
def coeff.linearMap (g : Γ) : HahnSeries Γ V →ₗ[R] V :=
  { coeff.addMonoidHom g with map_smul' := fun _ _ => rfl }
#align hahn_series.coeff.linear_map HahnSeries.coeff.linearMap

/-- `ofIterate` as a linear map. -/
@[simps]
def ofIterate.linearMap {Γ' : Type*} [PartialOrder Γ'] :
    HahnSeries Γ (HahnSeries Γ' V) →ₗ[R] HahnSeries (Γ ×ₗ Γ') V where
  toFun := ofIterate
  map_add' := by
    intro _ _
    ext _
    simp only [ofIterate, add_coeff', Pi.add_apply]
  map_smul' := by
    intro _ _
    ext _
    simp only [ofIterate, RingHom.id_apply, smul_coeff]

/-- `toIterate` as a linear map. -/
@[simps]
def toIterate.linearMap {Γ' : Type*} [PartialOrder Γ'] :
    HahnSeries (Γ ×ₗ Γ') V →ₗ[R] HahnSeries Γ (HahnSeries Γ' V) where
  toFun := toIterate
  map_add' := by
    intro _ _
    ext _
    simp only [toIterate, add_coeff', Pi.add_apply]
  map_smul' := by
    intro _ _
    ext _
    simp only [toIterate, RingHom.id_apply, smul_coeff]

section Domain

variable {Γ' : Type*} [PartialOrder Γ']

theorem embDomain_smul (f : Γ ↪o Γ') (r : R) (x : HahnSeries Γ R) :
    embDomain f (r • x) = r • embDomain f x := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_notin_range hg]
#align hahn_series.emb_domain_smul HahnSeries.embDomain_smul

/-- Extending the domain of Hahn series is a linear map. -/
@[simps]
def embDomainLinearMap (f : Γ ↪o Γ') : HahnSeries Γ R →ₗ[R] HahnSeries Γ' R where
  toFun := embDomain f
  map_add' := embDomain_add f
  map_smul' := embDomain_smul f
#align hahn_series.emb_domain_linear_map HahnSeries.embDomainLinearMap

end Domain

end Module

section LeadingTerm

-- add orderTop versions!

theorem nonzero_of_nonzero_add_single [Zero Γ] [PartialOrder Γ] [AddMonoid R]
    {x y : HahnSeries Γ R} (hxy : x = y + single x.order (x.coeff x.order)) (hy : y ≠ 0) :
    x ≠ 0 :=
  fun hx => by simp_all only [order_zero, zero_coeff, map_zero, add_zero, ne_eq, not_true_eq_false]

variable [LinearOrder Γ] [Zero Γ] [AddCancelCommMonoid R] {x y : HahnSeries Γ R}
  (hxy : x = y + single x.order (x.coeff x.order))

theorem coeff_of_add_single_order_eq_zero : y.coeff x.order = 0 := by
  have hx : x.coeff x.order = y.coeff x.order +
      ((single (order x)) (x.coeff (order x))).coeff x.order := by
    nth_rw 1 [hxy, add_coeff]
  rw [single_coeff_same, self_eq_add_left] at hx
  exact hx

theorem add_single_order_of_ne_order (hy : y ≠ 0) : x.order ≠ y.order :=
  fun h => (Eq.mpr (congrArg (fun g ↦ y.coeff g ≠ 0) h) (coeff_order_ne_zero hy))
    (coeff_of_add_single_order_eq_zero hxy)

theorem coeff_eq_of_not_order (g : Γ) (hg : g ≠ x.order) : y.coeff g = x.coeff g := by
  rw [hxy, add_coeff, single_coeff_of_ne hg, add_zero]

theorem support_subset_add_single_support : y.support ⊆ x.support :=
  fun g hg => if hgx : g = order x then ((fun _ ↦ hg (Eq.mpr (congrArg (fun g ↦ y.coeff g = 0) hgx)
    (coeff_of_add_single_order_eq_zero hxy))) hg).elim
    else fun hxg => hg (Eq.mp (congrArg (fun r ↦ r = 0)
    (coeff_eq_of_not_order hxy g hgx).symm) hxg)

theorem order_lt_add_single_support_order (hy : y ≠ 0) : x.order < y.order := by
  refine lt_of_le_of_ne ?_ (add_single_order_of_ne_order hxy hy)
  simp only [order]
  split <;> rename_i hz
  · exact ((nonzero_of_nonzero_add_single hxy hy) hz).elim
  · exact Set.IsWF.min_le_min_of_subset (support_subset_add_single_support hxy)

end LeadingTerm
