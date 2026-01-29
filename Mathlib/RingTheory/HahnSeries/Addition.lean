/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Pi.Lemmas
public import Mathlib.Algebra.Group.Support
public import Mathlib.Algebra.Module.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.RingTheory.HahnSeries.Basic
public import Mathlib.Tactic.FastInstance

/-!
# Additive properties of Hahn series
If `Γ` is ordered and `R` has zero, then `R⟦Γ⟧` consists of formal series over `Γ` with coefficients
in `R`, whose supports are partially well-ordered. With further structure on `R` and `Γ`, we can add
further structure on `R⟦Γ⟧`.  When `R` has an addition operation, `R⟦Γ⟧` also has addition by adding
coefficients.

## Main Definitions
* If `R` is a (commutative) additive monoid or group, then so is `R⟦Γ⟧`.

## References
- [J. van der Hoeven, *Operators on Generalized Power Series*][van_der_hoeven]
-/

@[expose] public section


open Finset Function

noncomputable section

variable {Γ Γ' R S U V α : Type*}

namespace HahnSeries

section SMulZeroClass

variable [PartialOrder Γ] {V : Type*} [Zero V] [SMulZeroClass R V]

instance : SMul R V⟦Γ⟧ :=
  ⟨fun r x =>
    { coeff := r • x.coeff
      isPWO_support' := x.isPWO_support.mono (Function.support_const_smul_subset ..) }⟩

theorem support_smul_subset (r : R) (x : HahnSeries Γ V) : (r • x).support ⊆ x.support :=
  Function.support_const_smul_subset ..

@[simp]
theorem coeff_smul' (r : R) (x : V⟦Γ⟧) : (r • x).coeff = r • x.coeff :=
  rfl

@[simp]
theorem coeff_smul {r : R} {x : V⟦Γ⟧} {a : Γ} : (r • x).coeff a = r • x.coeff a :=
  rfl

instance : SMulZeroClass R V⟦Γ⟧ where
  smul_zero _ := by
    ext
    simp only [coeff_smul, coeff_zero, smul_zero]

theorem orderTop_smul_not_lt (r : R) (x : V⟦Γ⟧) : ¬ (r • x).orderTop < x.orderTop := by
  by_cases hrx : r • x = 0
  · rw [hrx, orderTop_zero]
    exact not_top_lt
  · simp only [orderTop_of_ne_zero hrx, orderTop_of_ne_zero <| right_ne_zero_of_smul hrx,
      WithTop.coe_lt_coe]
    exact Set.IsWF.min_of_subset_not_lt_min (Function.support_smul_subset_right ..)

theorem orderTop_le_orderTop_smul {Γ} [LinearOrder Γ] (r : R) (x : V⟦Γ⟧) :
    x.orderTop ≤ (r • x).orderTop :=
  le_of_not_gt <| orderTop_smul_not_lt r x

theorem order_smul_not_lt [Zero Γ] (r : R) (x : V⟦Γ⟧) (h : r • x ≠ 0) :
    ¬ (r • x).order < x.order := by
  have hx : x ≠ 0 := right_ne_zero_of_smul h
  simp_all only [order, dite_false]
  exact Set.IsWF.min_of_subset_not_lt_min (Function.support_smul_subset_right ..)

theorem le_order_smul {Γ} [Zero Γ] [LinearOrder Γ] (r : R) (x : V⟦Γ⟧) (h : r • x ≠ 0) :
    x.order ≤ (r • x).order :=
  le_of_not_gt (order_smul_not_lt r x h)

@[simp]
theorem single_smul {g : Γ} {r : R} {s : V} : single g (r • s) = r • single g s := by
  ext g'
  by_cases h : g = g'
  · simp [h]
  · simp [coeff_single_of_ne (fun a ↦ h a.symm)]

theorem truncLT_smul [DecidableLT Γ] (c : Γ) (r : R) (x : V⟦Γ⟧) :
    truncLT c (r • x) = r • truncLT c x := by ext; simp

end SMulZeroClass

section Addition

variable [PartialOrder Γ]

section AddMonoid

variable [AddMonoid R]

instance : Add R⟦Γ⟧ where
  add x y :=
    { coeff := x.coeff + y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_add ..) }

theorem support_add_subset (x y : R⟦Γ⟧) : (x + y).support ⊆ x.support ∪ y.support :=
  Function.support_add ..

@[simp]
theorem coeff_add' (x y : R⟦Γ⟧) : (x + y).coeff = x.coeff + y.coeff :=
  rfl

theorem coeff_add {x y : R⟦Γ⟧} {a : Γ} : (x + y).coeff a = x.coeff a + y.coeff a :=
  rfl

@[simp] theorem single_add (a : Γ) (r s : R) : single a (r + s) = single a r + single a s := by
  classical
  ext : 1; exact Pi.single_add (f := fun _ => R) a r s

instance : AddMonoid R⟦Γ⟧ := fast_instance%
  coeff_injective.addMonoid _
    coeff_zero' coeff_add' (fun _ _ => coeff_smul' _ _)

theorem coeff_nsmul {x : R⟦Γ⟧} {n : ℕ} : (n • x).coeff = n • x.coeff := coeff_smul' _ _

@[simp]
protected lemma map_add [AddMonoid S] (f : R →+ S) {x y : R⟦Γ⟧} :
    ((x + y).map f : S⟦Γ⟧) = x.map f + y.map f := by
  ext; simp

/--
`addOppositeEquiv` is an additive monoid isomorphism between
Hahn series over `Γ` with coefficients in the opposite additive monoid `Rᵃᵒᵖ`
and the additive opposite of Hahn series over `Γ` with coefficients `R`.
-/
@[simps -isSimp]
def addOppositeEquiv : Rᵃᵒᵖ⟦Γ⟧ ≃+ R⟦Γ⟧ᵃᵒᵖ where
  toFun x := .op ⟨fun a ↦ (x.coeff a).unop, by convert x.isPWO_support; ext; simp⟩
  invFun x := ⟨fun a ↦ .op (x.unop.coeff a), by convert x.unop.isPWO_support; ext; simp⟩
  left_inv x := by simp
  right_inv x := by
    apply AddOpposite.unop_injective
    simp
  map_add' x y := by
    apply AddOpposite.unop_injective
    ext
    simp

@[simp]
lemma addOppositeEquiv_support (x : Rᵃᵒᵖ⟦Γ⟧) :
    (addOppositeEquiv x).unop.support = x.support := by
  ext
  simp [addOppositeEquiv_apply]

@[simp]
lemma addOppositeEquiv_symm_support (x : R⟦Γ⟧ᵃᵒᵖ) :
    (addOppositeEquiv.symm x).support = x.unop.support := by
  rw [← addOppositeEquiv_support, AddEquiv.apply_symm_apply]

@[simp]
lemma addOppositeEquiv_orderTop (x : Rᵃᵒᵖ⟦Γ⟧) :
    (addOppositeEquiv x).unop.orderTop = x.orderTop := by
  classical
  simp only [orderTop,
    addOppositeEquiv_support]
  simp only [addOppositeEquiv_apply, AddOpposite.unop_op, mk_eq_zero]
  simp_rw [HahnSeries.ext_iff, funext_iff]
  simp only [Pi.zero_apply, AddOpposite.unop_eq_zero_iff, coeff_zero]

@[simp]
lemma addOppositeEquiv_symm_orderTop (x : R⟦Γ⟧ᵃᵒᵖ) :
    (addOppositeEquiv.symm x).orderTop = x.unop.orderTop := by
  rw [← addOppositeEquiv_orderTop, AddEquiv.apply_symm_apply]

@[simp]
lemma addOppositeEquiv_leadingCoeff (x : Rᵃᵒᵖ⟦Γ⟧) :
    (addOppositeEquiv x).unop.leadingCoeff = x.leadingCoeff.unop := by
  classical
  obtain rfl | hx := eq_or_ne x 0
  · simp
  simp only [ne_eq, AddOpposite.unop_eq_zero_iff, EmbeddingLike.map_eq_zero_iff, hx,
    not_false_eq_true, leadingCoeff_of_ne_zero, addOppositeEquiv_orderTop]
  simp [addOppositeEquiv]

@[simp]
lemma addOppositeEquiv_symm_leadingCoeff (x : R⟦Γ⟧ᵃᵒᵖ) :
    (addOppositeEquiv.symm x).leadingCoeff = .op x.unop.leadingCoeff := by
  apply AddOpposite.unop_injective
  rw [← addOppositeEquiv_leadingCoeff, AddEquiv.apply_symm_apply, AddOpposite.unop_op]

protected theorem min_le_min_add {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} (hx : x ≠ 0)
    (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (Set.IsWF.min x.isWF_support (support_nonempty_iff.2 hx))
      (Set.IsWF.min y.isWF_support (support_nonempty_iff.2 hy)) ≤
      Set.IsWF.min (x + y).isWF_support (support_nonempty_iff.2 hxy) := by
  rw [← Set.IsWF.min_union]
  exact Set.IsWF.min_le_min_of_subset (support_add_subset (x := x) (y := y))

theorem min_orderTop_le_orderTop_add {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} :
    min x.orderTop y.orderTop ≤ (x + y).orderTop := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  by_cases hxy : x + y = 0; · simp [hxy]
  rw [orderTop_of_ne_zero hx, orderTop_of_ne_zero hy, orderTop_of_ne_zero hxy, ← WithTop.coe_min,
    WithTop.coe_le_coe]
  exact HahnSeries.min_le_min_add hx hy hxy

theorem min_order_le_order_add {Γ} [Zero Γ] [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x + y ≠ 0) : min x.order y.order ≤ (x + y).order := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [order_of_ne hx, order_of_ne hy, order_of_ne hxy]
  exact HahnSeries.min_le_min_add hx hy hxy

theorem orderTop_add_eq_left {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x.orderTop < y.orderTop) : (x + y).orderTop = x.orderTop := by
  have hx : x ≠ 0 := orderTop_ne_top.1 hxy.ne_top
  let g : Γ := Set.IsWF.min x.isWF_support (support_nonempty_iff.2 hx)
  have hcxyne : (x + y).coeff g ≠ 0 := by
    rw [coeff_add, coeff_eq_zero_of_lt_orderTop (lt_of_eq_of_lt (orderTop_of_ne_zero hx).symm hxy),
      add_zero]
    exact coeff_orderTop_ne (orderTop_of_ne_zero hx)
  have hxyx : (x + y).orderTop ≤ x.orderTop := by
    rw [orderTop_of_ne_zero hx]
    exact orderTop_le_of_coeff_ne_zero hcxyne
  exact le_antisymm hxyx (le_of_eq_of_le (min_eq_left_of_lt hxy).symm min_orderTop_le_orderTop_add)

theorem orderTop_add_eq_right {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : y.orderTop < x.orderTop) : (x + y).orderTop = y.orderTop := by
  simpa [← map_add, ← AddOpposite.op_add, hxy] using orderTop_add_eq_left
    (x := addOppositeEquiv.symm (.op y))
    (y := addOppositeEquiv.symm (.op x))

theorem leadingCoeff_add_eq_left {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x.orderTop < y.orderTop) : (x + y).leadingCoeff = x.leadingCoeff := by
  have hx : x ≠ 0 := orderTop_ne_top.1 hxy.ne_top
  have ho : (x + y).orderTop = x.orderTop := orderTop_add_eq_left hxy
  by_cases h : x + y = 0
  · rw [h, orderTop_zero] at ho
    rw [h, orderTop_eq_top.mp ho.symm]
  · simp_rw [leadingCoeff_of_ne_zero h, leadingCoeff_of_ne_zero hx, ho, coeff_add]
    rw [coeff_eq_zero_of_lt_orderTop (x := y) (by simpa using hxy), add_zero]

theorem leadingCoeff_add_eq_right {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : y.orderTop < x.orderTop) : (x + y).leadingCoeff = y.leadingCoeff := by
  simpa [← map_add, ← AddOpposite.op_add, hxy] using leadingCoeff_add_eq_left
    (x := addOppositeEquiv.symm (.op y))
    (y := addOppositeEquiv.symm (.op x))

theorem ne_zero_of_eq_add_single [Zero Γ] {x y : R⟦Γ⟧}
    (hxy : x = y + single x.order x.leadingCoeff) (hy : y ≠ 0) : x ≠ 0 := by
  by_contra h
  simp only [h, order_zero, leadingCoeff_zero, map_zero, add_zero] at hxy
  exact hy hxy.symm

theorem coeff_order_of_eq_add_single {R} [AddCancelCommMonoid R] [Zero Γ] {x y : R⟦Γ⟧}
    (hxy : x = y + single x.order x.leadingCoeff) : y.coeff x.order = 0 := by
  simpa [← leadingCoeff_eq] using congr(($hxy).coeff x.order)

theorem order_lt_order_of_eq_add_single {R} {Γ} [LinearOrder Γ] [Zero Γ] [AddCancelCommMonoid R]
    {x y : R⟦Γ⟧} (hxy : x = y + single x.order x.leadingCoeff) (hy : y ≠ 0) :
    x.order < y.order := by
  have : x.order ≠ y.order := by
    intro h
    have hyne : single y.order y.leadingCoeff ≠ 0 := single_ne_zero <| leadingCoeff_ne_zero.mpr hy
    rw [leadingCoeff_eq, ← h, coeff_order_of_eq_add_single hxy, single_eq_zero] at hyne
    exact hyne rfl
  refine lt_of_le_of_ne ?_ this
  simp only [order, ne_zero_of_eq_add_single hxy hy, ↓reduceDIte, hy]
  refine Set.IsWF.min_le_min_of_subset fun g hg ↦ ?_
  obtain rfl | hgx := eq_or_ne g x.order
  · simpa using coeff_order_eq_zero.not.2 <| ne_zero_of_eq_add_single hxy hy
  · have : x.coeff g = (y + (single x.order) x.leadingCoeff).coeff g := by rw [← hxy]
    rw [coeff_add, coeff_single_of_ne hgx, add_zero] at this
    simpa [this] using hg

/-- `single` as an additive monoid/group homomorphism -/
@[simps!]
def single.addMonoidHom (a : Γ) : R →+ R⟦Γ⟧ :=
  { single a with
    map_add' := single_add _ }

/-- `coeff g` as an additive monoid/group homomorphism -/
@[simps]
def coeff.addMonoidHom (g : Γ) : R⟦Γ⟧ →+ R where
  toFun f := f.coeff g
  map_zero' := coeff_zero
  map_add' _ _ := coeff_add

section Domain

variable [PartialOrder Γ']

theorem embDomain_add (f : Γ ↪o Γ') (x y : R⟦Γ⟧) :
    embDomain f (x + y) = embDomain f x + embDomain f y := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_notin_range hg]

end Domain

theorem truncLT_add [DecidableLT Γ] (c : Γ) (x y : R⟦Γ⟧) :
    truncLT c (x + y) = truncLT c x + truncLT c y := by
  ext i
  by_cases h : i < c <;> simp [h]

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid R]

instance : AddCommMonoid R⟦Γ⟧ where
  add_comm x y := by
    ext
    apply add_comm

@[simp]
theorem coeff_sum {s : Finset α} {x : α → R⟦Γ⟧} (g : Γ) :
    (∑ i ∈ s, x i).coeff g = ∑ i ∈ s, (x i).coeff g :=
  cons_induction rfl (fun i s his hsum => by rw [sum_cons, sum_cons, coeff_add, hsum]) s

theorem inf_orderTop_le_orderTop_sum {Γ} [LinearOrder Γ] {α : Type*} {x : α → HahnSeries Γ R}
    {s : Finset α} : (s.inf fun i => orderTop (x i)) ≤ (∑ i ∈ s, x i).orderTop := by
  refine le_orderTop_iff.mpr fun g hg => ?_
  simp_all only [WithTop.coe_lt_top, Finset.lt_inf_iff, coeff_sum]
  exact Finset.sum_eq_zero fun i hi ↦ coeff_eq_zero_of_lt_orderTop (hg i hi)

end AddCommMonoid

section NegZeroClass

variable [NegZeroClass R]

instance : Neg R⟦Γ⟧ where
  neg x := x.map (-ZeroHom.id _)

theorem support_neg_subset (x : R⟦Γ⟧) : (-x).support ⊆ x.support :=
  support_map_subset ..

@[simp]
theorem coeff_neg' (x : R⟦Γ⟧) : (-x).coeff = -x.coeff :=
  rfl

theorem coeff_neg {x : R⟦Γ⟧} {a : Γ} : (-x).coeff a = -x.coeff a :=
  rfl

end NegZeroClass

section AddGroup

variable [AddGroup R]

instance : Sub R⟦Γ⟧ where
  sub x y :=
    { coeff := x.coeff - y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_sub ..) }

theorem support_sub_subset (x y : R⟦Γ⟧) : (x - y).support ⊆ x.support ∪ y.support :=
  Function.support_sub ..

@[simp]
theorem coeff_sub' (x y : R⟦Γ⟧) : (x - y).coeff = x.coeff - y.coeff :=
  rfl

theorem coeff_sub {x y : R⟦Γ⟧} {a : Γ} : (x - y).coeff a = x.coeff a - y.coeff a :=
  rfl

instance : AddGroup R⟦Γ⟧ := fast_instance%
  coeff_injective.addGroup _
    coeff_zero' coeff_add' coeff_neg' coeff_sub'
    (fun _ _ => coeff_smul' _ _) (fun _ _ => coeff_smul' _ _)

@[simp]
theorem single_sub (a : Γ) (r s : R) : single a (r - s) = single a r - single a s :=
  map_sub (single.addMonoidHom a) _ _

@[simp]
theorem single_neg (a : Γ) (r : R) : single a (-r) = -single a r :=
  map_neg (single.addMonoidHom a) _

@[simp]
theorem support_neg {x : R⟦Γ⟧} : (-x).support = x.support := by
  ext
  simp

@[simp]
protected lemma map_neg [AddGroup S] (f : R →+ S) {x : R⟦Γ⟧} :
    ((-x).map f : S⟦Γ⟧) = -x.map f := by
  ext; simp

@[simp]
theorem orderTop_neg {x : R⟦Γ⟧} : (-x).orderTop = x.orderTop := by
  classical simp only [orderTop, support_neg, neg_eq_zero]

@[simp]
theorem order_neg [Zero Γ] {f : R⟦Γ⟧} : (-f).order = f.order := by
  classical
  by_cases hf : f = 0
  · simp only [hf, neg_zero]
  simp only [order, support_neg, neg_eq_zero]

theorem leadingCoeff_neg {x : R⟦Γ⟧} : (-x).leadingCoeff = -x.leadingCoeff := by
  obtain rfl | hx := eq_or_ne x 0 <;> simp [leadingCoeff_of_ne_zero, *]

@[simp]
theorem zsmul_coeff {x : R⟦Γ⟧} {n : ℤ} : (n • x).coeff = n • x.coeff := by
  cases n with
  | ofNat n => simp [Int.ofNat_eq_natCast, natCast_zsmul]
  | negSucc _ => simp [negSucc_zsmul]

@[simp]
protected lemma map_sub [AddGroup S] (f : R →+ S) {x y : R⟦Γ⟧} :
    ((x - y).map f : S⟦Γ⟧) = x.map f - y.map f := by
  ext; simp

theorem min_orderTop_le_orderTop_sub {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} :
    min x.orderTop y.orderTop ≤ (x - y).orderTop := by
  rw [sub_eq_add_neg, ← orderTop_neg (x := y)]
  exact min_orderTop_le_orderTop_add

theorem orderTop_sub {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x.orderTop < y.orderTop) : (x - y).orderTop = x.orderTop := by
  rw [sub_eq_add_neg]
  rw [← orderTop_neg (x := y)] at hxy
  exact orderTop_add_eq_left hxy

theorem leadingCoeff_sub {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧}
    (hxy : x.orderTop < y.orderTop) : (x - y).leadingCoeff = x.leadingCoeff := by
  rw [sub_eq_add_neg]
  rw [← orderTop_neg (x := y)] at hxy
  exact leadingCoeff_add_eq_left hxy

theorem sub_orderTop_ne_of_leadingCoeff_eq {x y : HahnSeries Γ R} {g : Γ}
    (hxg : x.orderTop = g) (hyg : y.orderTop = g) (hxyc : x.leadingCoeff = y.leadingCoeff) :
    (x - y).orderTop ≠ g := by
  refine orderTop_ne_of_coeff_eq_zero ?_
  have hx : x ≠ 0 := by
    rw [← orderTop_ne_top, hxg]
    exact WithTop.coe_ne_top
  rw [orderTop_of_ne_zero hx, WithTop.coe_eq_coe] at hxg
  have hy : y ≠ 0 := by
    rw [← orderTop_ne_top, hyg]
    exact WithTop.coe_ne_top
  rw [orderTop_of_ne_zero hy, WithTop.coe_eq_coe] at hyg
  simp only [leadingCoeff_of_ne_zero hx, leadingCoeff_of_ne_zero hy, untop_orderTop_of_ne_zero hx,
    untop_orderTop_of_ne_zero hy, hxg, hyg] at hxyc
  rwa [coeff_sub, sub_eq_zero]

theorem orderTop_sub_ne {x y : R⟦Γ⟧} {g : Γ}
    (hxg : x.orderTop = g) (hyg : y.orderTop = g) (hxyc : x.leadingCoeff = y.leadingCoeff) :
    (x - y).orderTop ≠ g := by
  refine orderTop_ne_of_coeff_eq_zero ?_
  have hx : x ≠ 0 := fun h ↦ by simp_all [orderTop_zero, WithTop.top_ne_coe]
  rw [orderTop_of_ne_zero hx, WithTop.coe_eq_coe] at hxg
  have hy : y ≠ 0 := fun h ↦ by simp_all [orderTop_zero, WithTop.top_ne_coe]
  rw [orderTop_of_ne_zero hy, WithTop.coe_eq_coe] at hyg
  simp only [leadingCoeff_of_ne_zero hx, leadingCoeff_of_ne_zero hy, untop_orderTop_of_ne_zero hx,
    untop_orderTop_of_ne_zero hy, hxg, hyg] at hxyc
  rwa [coeff_sub, sub_eq_zero]

theorem le_orderTop_of_leadingCoeff_eq {Γ} [LinearOrder Γ] {x y : R⟦Γ⟧} {g : Γ}
    (hxg : x.orderTop = g) (hyg : y.orderTop = g) (hxyc : x.leadingCoeff = y.leadingCoeff) :
    g < (x - y).orderTop :=
  lt_of_le_of_ne (le_of_eq_of_le (by rw [hxg, hyg, inf_idem]) min_orderTop_le_orderTop_sub)
    (orderTop_sub_ne hxg hyg hxyc).symm

end AddGroup

instance [AddCommGroup R] : AddCommGroup R⟦Γ⟧ where

end Addition

section DistribMulAction

variable [PartialOrder Γ] [Monoid R] [AddMonoid V] [DistribMulAction R V]

instance : DistribMulAction R V⟦Γ⟧ where
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

instance [SMul R S] [IsScalarTower R S V] : IsScalarTower R S V⟦Γ⟧ :=
  ⟨fun r s a => by
    ext
    simp⟩

instance [SMulCommClass R S V] : SMulCommClass R S V⟦Γ⟧ :=
  ⟨fun r s a => by
    ext
    simp [smul_comm]⟩

end DistribMulAction

section Module

variable [PartialOrder Γ] [Semiring R] [AddCommMonoid V] [Module R V]

instance : Module R V⟦Γ⟧ where
  zero_smul _ := by
    ext
    simp
  add_smul _ _ _ := by
    ext
    simp [add_smul]

/-- `single` as a linear map -/
@[simps]
def single.linearMap (a : Γ) : V →ₗ[R] V⟦Γ⟧ :=
  { single.addMonoidHom a with
    map_smul' := fun r s => by
      ext b
      by_cases h : b = a <;> simp [h] }

/-- `coeff g` as a linear map -/
@[simps]
def coeff.linearMap (g : Γ) : V⟦Γ⟧ →ₗ[R] V :=
  { coeff.addMonoidHom g with map_smul' := fun _ _ => rfl }

/-- `ofIterate` as a linear map. -/
@[simps]
def ofIterate.linearMap [PartialOrder Γ'] :
    HahnSeries Γ (HahnSeries Γ' V) →ₗ[R] HahnSeries (Γ ×ₗ Γ') V where
  toFun := ofIterate
  map_add' _ _ := by ext; simp [ofIterate]
  map_smul' _ _ := by ext; simp [ofIterate]

/-- `toIterate` as a linear map. -/
@[simps]
def toIterate.linearMap [PartialOrder Γ'] :
    HahnSeries (Γ ×ₗ Γ') V →ₗ[R] HahnSeries Γ (HahnSeries Γ' V) where
  toFun := toIterate
  map_add' _ _ := by ext; simp [toIterate]
  map_smul' _ _ := by ext; simp [toIterate]

@[simp]
protected lemma map_smul [AddCommMonoid U] [Module R U] (f : U →ₗ[R] V) {r : R} {x : U⟦Γ⟧} :
    (r • x).map f = r • (x.map f : V⟦Γ⟧) := by
  ext; simp

section Finsupp

variable (R) in
/-- `ofFinsupp` as a linear map. -/
@[simps]
def ofFinsuppLinearMap : (Γ →₀ V) →ₗ[R] V⟦Γ⟧ where
  toFun := ofFinsupp
  map_add' _ _ := by
    ext
    simp
  map_smul' _ _ := by
    ext
    simp

variable (R) in
@[simp]
theorem coeff_ofFinsuppLinearMap (f : Γ →₀ V) (a : Γ) :
    (ofFinsuppLinearMap R f).coeff a = f a := rfl

end Finsupp

section Domain

variable [PartialOrder Γ']

theorem embDomain_smul (f : Γ ↪o Γ') (r : R) (x : R⟦Γ⟧) :
    embDomain f (r • x) = r • embDomain f x := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_notin_range hg]

/-- Extending the domain of Hahn series is a linear map. -/
@[simps]
def embDomainLinearMap (f : Γ ↪o Γ') : R⟦Γ⟧ →ₗ[R] R⟦Γ'⟧ where
  toFun := embDomain f
  map_add' := embDomain_add f
  map_smul' := embDomain_smul f

end Domain

variable (R) in
/-- `HahnSeries.truncLT` as a linear map. -/
def truncLTLinearMap [DecidableLT Γ] (c : Γ) : V⟦Γ⟧ →ₗ[R] V⟦Γ⟧ where
  toFun := truncLT c
  map_add' := truncLT_add c
  map_smul' := truncLT_smul c

variable (R) in
@[simp]
theorem coe_truncLTLinearMap [DecidableLT Γ] (c : Γ) :
    (truncLTLinearMap R c : V⟦Γ⟧ → V⟦Γ⟧) = truncLT c := by rfl

end Module

section LeadingTerm

variable [LinearOrder Γ]

theorem orderTop_le_orderTop_add [AddMonoid R] {x y : HahnSeries Γ R}
    (h : x.orderTop ≤ y.orderTop) : x.orderTop ≤ (x + y).orderTop :=
  le_of_eq_of_le (min_eq_left h).symm min_orderTop_le_orderTop_add

theorem nonzero_of_nonzero_add_leading [AddMonoid R] {x y : HahnSeries Γ R}
    (hxy : x = y + x.leadingTerm) (hy : y ≠ 0) : x ≠ 0 := by
  intro hx
  rw [hx, leadingTerm_zero, add_zero] at hxy
  exact hy (id hxy.symm)

variable [AddCancelCommMonoid R] {x y : HahnSeries Γ R}

theorem coeff_add_leading (hxy : x = y + x.leadingTerm) (h : x ≠ 0) :
    y.coeff (x.isWF_support.min (support_nonempty_iff.2 h)) = 0 := by
  let xo := x.isWF_support.min (support_nonempty_iff.2 h)
  have hx : x.coeff xo = y.coeff xo + x.leadingTerm.coeff xo := by
    nth_rw 1 [hxy, coeff_add]
  have hxx : (leadingTerm x).coeff xo = x.leadingTerm.leadingCoeff := by
    rw [leadingCoeff_leadingTerm, leadingTerm_of_ne h, coeff_single_same]
  rw [hxx, leadingCoeff_leadingTerm] at hx
  have : x.leadingCoeff = x.coeff xo := by simp [leadingCoeff, orderTop, h, xo]
  rwa [this, right_eq_add] at hx

theorem add_leading_orderTop_ne (hxy : x = y + x.leadingTerm) (hy : y ≠ 0) :
    x.orderTop ≠ y.orderTop := by
  intro h
  have hyne : y.leadingTerm ≠ 0 := leadingTerm_ne_iff.mp hy
  have hx : x ≠ 0 := nonzero_of_nonzero_add_leading hxy hy
  simp only [orderTop_of_ne_zero hx, orderTop_of_ne_zero hy,
    WithTop.coe_eq_coe] at h
  have := coeff_add_leading hxy hx
  rw [h] at this
  rw [leadingTerm_of_ne hy, ← h, leadingCoeff_of_ne_zero hy, untop_orderTop_of_ne_zero hy, this,
    single_eq_zero] at hyne
  exact hyne rfl

theorem coeff_eq_of_not_orderTop (hxy : x = y + x.leadingTerm) (g : Γ) (hg : ↑g ≠ x.orderTop) :
    y.coeff g = x.coeff g := by
  rw [hxy, coeff_add, leadingTerm]
  simp only [left_eq_add]
  split_ifs with hx
  · simp only [coeff_zero]
  · simp only [orderTop_of_ne_zero hx, ne_eq, WithTop.coe_eq_coe] at hg
    exact coeff_single_of_ne hg

theorem support_subset_add_single_support (hxy : x = y + x.leadingTerm) :
    y.support ⊆ x.support := by
  intro g hg
  by_cases hgx : g = orderTop x
  · intro hx
    apply (coeff_orderTop_ne hgx.symm) hx
  · exact fun hxg => hg (Eq.mp (congrArg (fun r ↦ r = 0)
    (coeff_eq_of_not_orderTop hxy g hgx).symm) hxg)

theorem orderTop_lt_add_single_support_orderTop (hxy : x = y + x.leadingTerm) (hy : y ≠ 0) :
    x.orderTop < y.orderTop := by
  refine lt_of_le_of_ne ?_ (add_leading_orderTop_ne hxy hy)
  rw [orderTop_of_ne_zero hy, orderTop_of_ne_zero <| nonzero_of_nonzero_add_leading hxy hy]
  exact WithTop.coe_le_coe.mpr <| Set.IsWF.min_le_min_of_subset <|
    support_subset_add_single_support hxy

theorem order_lt_add_single_support_order [Zero Γ] (hxy : x = y + x.leadingTerm) (hy : y ≠ 0) :
    x.order < y.order := by
  rw [← WithTop.coe_lt_coe, order_eq_orderTop_of_ne_zero hy, order_eq_orderTop_of_ne_zero <|
    nonzero_of_nonzero_add_leading hxy hy]
  exact orderTop_lt_add_single_support_orderTop hxy hy

end LeadingTerm

end HahnSeries
