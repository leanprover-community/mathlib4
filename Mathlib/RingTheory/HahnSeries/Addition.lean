/-
Copyright (c) 2021 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.RingTheory.HahnSeries.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FastInstance

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


open Finset Function

noncomputable section

variable {Γ Γ' R S U V α : Type*}

namespace HahnSeries

section SMulZeroClass

variable [PartialOrder Γ] {V : Type*} [Zero V] [SMulZeroClass R V]

instance : SMul R (HahnSeries Γ V) :=
  ⟨fun r x =>
    { coeff := r • x.coeff
      isPWO_support' := x.isPWO_support.mono (Function.support_const_smul_subset r x.coeff) }⟩

@[simp]
theorem coeff_smul' (r : R) (x : HahnSeries Γ V) : (r • x).coeff = r • x.coeff :=
  rfl

@[simp]
theorem coeff_smul {r : R} {x : HahnSeries Γ V} {a : Γ} : (r • x).coeff a = r • x.coeff a :=
  rfl

@[deprecated (since := "2025-01-31")] alias smul_coeff := coeff_smul

instance : SMulZeroClass R (HahnSeries Γ V) :=
  { inferInstanceAs (SMul R (HahnSeries Γ V)) with
    smul_zero := by
      intro
      ext
      simp only [coeff_smul, coeff_zero, smul_zero]}

theorem orderTop_smul_not_lt (r : R) (x : HahnSeries Γ V) : ¬ (r • x).orderTop < x.orderTop := by
  by_cases hrx : r • x = 0
  · rw [hrx, orderTop_zero]
    exact not_top_lt
  · simp only [orderTop_of_ne hrx, orderTop_of_ne <| right_ne_zero_of_smul hrx, WithTop.coe_lt_coe]
    exact Set.IsWF.min_of_subset_not_lt_min
      (Function.support_smul_subset_right (fun _ => r) x.coeff)

theorem order_smul_not_lt [Zero Γ] (r : R) (x : HahnSeries Γ V) (h : r • x ≠ 0) :
    ¬ (r • x).order < x.order := by
  have hx : x ≠ 0 := right_ne_zero_of_smul h
  simp_all only [order, dite_false]
  exact Set.IsWF.min_of_subset_not_lt_min (Function.support_smul_subset_right (fun _ => r) x.coeff)

theorem le_order_smul {Γ} [Zero Γ] [LinearOrder Γ] (r : R) (x : HahnSeries Γ V) (h : r • x ≠ 0) :
    x.order ≤ (r • x).order :=
  le_of_not_gt (order_smul_not_lt r x h)

end SMulZeroClass

section Addition

variable [PartialOrder Γ]

section AddMonoid

variable [AddMonoid R]

instance : Add (HahnSeries Γ R) where
  add x y :=
    { coeff := x.coeff + y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_add _ _) }

@[simp]
theorem coeff_add' (x y : HahnSeries Γ R) : (x + y).coeff = x.coeff + y.coeff :=
  rfl

@[deprecated (since := "2025-01-31")] alias add_coeff' := coeff_add'

theorem coeff_add {x y : HahnSeries Γ R} {a : Γ} : (x + y).coeff a = x.coeff a + y.coeff a :=
  rfl

@[simp] theorem single_add (a : Γ) (r s : R) : single a (r + s) = single a r + single a s := by
  classical
  ext : 1; exact Pi.single_add (f := fun _ => R) a r s

@[deprecated (since := "2025-01-31")] alias add_coeff := coeff_add

instance : AddMonoid (HahnSeries Γ R) := fast_instance%
  coeff_injective.addMonoid _
    coeff_zero' coeff_add' (fun _ _ => coeff_smul' _ _)

theorem coeff_nsmul {x : HahnSeries Γ R} {n : ℕ} : (n • x).coeff = n • x.coeff := coeff_smul' _ _

@[deprecated (since := "2025-01-31")] alias nsmul_coeff := coeff_nsmul

@[simp]
protected lemma map_add [AddMonoid S] (f : R →+ S) {x y : HahnSeries Γ R} :
    ((x + y).map f : HahnSeries Γ S) = x.map f + y.map f := by
  ext; simp
/--
`addOppositeEquiv` is an additive monoid isomorphism between
Hahn series over `Γ` with coefficients in the opposite additive monoid `Rᵃᵒᵖ`
and the additive opposite of Hahn series over `Γ` with coefficients `R`.
-/
@[simps -isSimp]
def addOppositeEquiv : HahnSeries Γ (Rᵃᵒᵖ) ≃+ (HahnSeries Γ R)ᵃᵒᵖ where
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
lemma addOppositeEquiv_support (x : HahnSeries Γ (Rᵃᵒᵖ)) :
    (addOppositeEquiv x).unop.support = x.support := by
  ext
  simp [addOppositeEquiv_apply]

@[simp]
lemma addOppositeEquiv_symm_support (x : (HahnSeries Γ R)ᵃᵒᵖ) :
    (addOppositeEquiv.symm x).support = x.unop.support := by
  rw [← addOppositeEquiv_support, AddEquiv.apply_symm_apply]

@[simp]
lemma addOppositeEquiv_orderTop (x : HahnSeries Γ (Rᵃᵒᵖ)) :
    (addOppositeEquiv x).unop.orderTop = x.orderTop := by
  classical
  simp only [orderTop, AddOpposite.unop_op, mk_eq_zero, EmbeddingLike.map_eq_zero_iff,
    addOppositeEquiv_support, ne_eq]
  simp only [addOppositeEquiv_apply, AddOpposite.unop_op, mk_eq_zero, coeff_zero]
  simp_rw [HahnSeries.ext_iff, funext_iff]
  simp only [Pi.zero_apply, AddOpposite.unop_eq_zero_iff, coeff_zero]

@[simp]
lemma addOppositeEquiv_symm_orderTop (x : (HahnSeries Γ R)ᵃᵒᵖ) :
    (addOppositeEquiv.symm x).orderTop = x.unop.orderTop := by
  rw [← addOppositeEquiv_orderTop, AddEquiv.apply_symm_apply]

@[simp]
lemma addOppositeEquiv_leadingCoeff (x : HahnSeries Γ (Rᵃᵒᵖ)) :
    (addOppositeEquiv x).unop.leadingCoeff = x.leadingCoeff.unop := by
  classical
  simp only [leadingCoeff, AddOpposite.unop_op, mk_eq_zero, EmbeddingLike.map_eq_zero_iff,
    addOppositeEquiv_support, ne_eq]
  simp only [addOppositeEquiv_apply, AddOpposite.unop_op, mk_eq_zero, coeff_zero]
  simp_rw [HahnSeries.ext_iff, funext_iff]
  simp only [Pi.zero_apply, AddOpposite.unop_eq_zero_iff, coeff_zero]
  split <;> rfl

@[simp]
lemma addOppositeEquiv_symm_leadingCoeff (x : (HahnSeries Γ R)ᵃᵒᵖ) :
    (addOppositeEquiv.symm x).leadingCoeff = .op x.unop.leadingCoeff := by
  apply AddOpposite.unop_injective
  rw [← addOppositeEquiv_leadingCoeff, AddEquiv.apply_symm_apply, AddOpposite.unop_op]

theorem support_add_subset {x y : HahnSeries Γ R} : support (x + y) ⊆ support x ∪ support y :=
  fun a ha => by
  rw [mem_support, coeff_add] at ha
  rw [Set.mem_union, mem_support, mem_support]
  contrapose! ha
  rw [ha.1, ha.2, add_zero]

protected theorem min_le_min_add {Γ} [LinearOrder Γ] {x y : HahnSeries Γ R} (hx : x ≠ 0)
    (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (Set.IsWF.min x.isWF_support (support_nonempty_iff.2 hx))
      (Set.IsWF.min y.isWF_support (support_nonempty_iff.2 hy)) ≤
      Set.IsWF.min (x + y).isWF_support (support_nonempty_iff.2 hxy) := by
  rw [← Set.IsWF.min_union]
  exact Set.IsWF.min_le_min_of_subset (support_add_subset (x := x) (y := y))

theorem min_orderTop_le_orderTop_add {Γ} [LinearOrder Γ] {x y : HahnSeries Γ R} :
    min x.orderTop y.orderTop ≤ (x + y).orderTop := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  by_cases hxy : x + y = 0; · simp [hxy]
  rw [orderTop_of_ne hx, orderTop_of_ne hy, orderTop_of_ne hxy, ← WithTop.coe_min,
    WithTop.coe_le_coe]
  exact HahnSeries.min_le_min_add hx hy hxy

theorem min_order_le_order_add {Γ} [Zero Γ] [LinearOrder Γ] {x y : HahnSeries Γ R}
    (hxy : x + y ≠ 0) : min x.order y.order ≤ (x + y).order := by
  by_cases hx : x = 0; · simp [hx]
  by_cases hy : y = 0; · simp [hy]
  rw [order_of_ne hx, order_of_ne hy, order_of_ne hxy]
  exact HahnSeries.min_le_min_add hx hy hxy

theorem orderTop_add_eq_left {Γ} [LinearOrder Γ] {x y : HahnSeries Γ R}
    (hxy : x.orderTop < y.orderTop) : (x + y).orderTop = x.orderTop := by
  have hx : x ≠ 0 := ne_zero_iff_orderTop.mpr hxy.ne_top
  let g : Γ := Set.IsWF.min x.isWF_support (support_nonempty_iff.2 hx)
  have hcxyne : (x + y).coeff g ≠ 0 := by
    rw [coeff_add, coeff_eq_zero_of_lt_orderTop (lt_of_eq_of_lt (orderTop_of_ne hx).symm hxy),
      add_zero]
    exact coeff_orderTop_ne (orderTop_of_ne hx)
  have hxyx : (x + y).orderTop ≤ x.orderTop := by
    rw [orderTop_of_ne hx]
    exact orderTop_le_of_coeff_ne_zero hcxyne
  exact le_antisymm hxyx (le_of_eq_of_le (min_eq_left_of_lt hxy).symm min_orderTop_le_orderTop_add)

theorem orderTop_add_eq_right {Γ} [LinearOrder Γ] {x y : HahnSeries Γ R}
    (hxy : y.orderTop < x.orderTop) : (x + y).orderTop = y.orderTop := by
  simpa [← map_add, ← AddOpposite.op_add, hxy] using orderTop_add_eq_left
    (x := addOppositeEquiv.symm (.op y))
    (y := addOppositeEquiv.symm (.op x))

theorem leadingCoeff_add_eq_left {Γ} [LinearOrder Γ] {x y : HahnSeries Γ R}
    (hxy : x.orderTop < y.orderTop) : (x + y).leadingCoeff = x.leadingCoeff := by
  have hx : x ≠ 0 := ne_zero_iff_orderTop.mpr hxy.ne_top
  have ho : (x + y).orderTop = x.orderTop := orderTop_add_eq_left hxy
  by_cases h : x + y = 0
  · rw [h, orderTop_zero] at ho
    rw [h, orderTop_eq_top_iff.mp ho.symm]
  · rw [orderTop_of_ne h, orderTop_of_ne hx, WithTop.coe_eq_coe] at ho
    rw [leadingCoeff_of_ne h, leadingCoeff_of_ne hx, ho, coeff_add,
      coeff_eq_zero_of_lt_orderTop (lt_of_eq_of_lt (orderTop_of_ne hx).symm hxy), add_zero]

theorem leadingCoeff_add_eq_right {Γ} [LinearOrder Γ] {x y : HahnSeries Γ R}
    (hxy : y.orderTop < x.orderTop) : (x + y).leadingCoeff = y.leadingCoeff := by
  simpa [← map_add, ← AddOpposite.op_add, hxy] using leadingCoeff_add_eq_left
    (x := addOppositeEquiv.symm (.op y))
    (y := addOppositeEquiv.symm (.op x))

theorem ne_zero_of_eq_add_single [Zero Γ] {x y : HahnSeries Γ R}
    (hxy : x = y + single x.order x.leadingCoeff) (hy : y ≠ 0) : x ≠ 0 := by
  by_contra h
  simp only [h, order_zero, leadingCoeff_zero, map_zero, add_zero] at hxy
  exact hy hxy.symm

theorem coeff_order_of_eq_add_single {R} [AddCancelCommMonoid R] [Zero Γ] {x y : HahnSeries Γ R}
    (hxy : x = y + single x.order x.leadingCoeff) (h : x ≠ 0) :
    y.coeff x.order = 0 := by
  let xo := x.isWF_support.min (support_nonempty_iff.2 h)
  have : xo = x.order := (order_of_ne h).symm
  have hx : x.coeff xo = y.coeff xo + (single x.order x.leadingCoeff).coeff xo := by
    nth_rw 1 [hxy, coeff_add]
  have hxx :
      (single x.order x.leadingCoeff).coeff xo = (single x.order x.leadingCoeff).leadingCoeff := by
    simp [leadingCoeff_of_single, coeff_single, this]
  rw [← (leadingCoeff_of_ne h), hxx, leadingCoeff_of_single, right_eq_add, this] at hx
  exact hx

theorem order_lt_order_of_eq_add_single {R} {Γ} [LinearOrder Γ] [Zero Γ] [AddCancelCommMonoid R]
    {x y : HahnSeries Γ R} (hxy : x = y + single x.order x.leadingCoeff) (hy : y ≠ 0) :
    x.order < y.order := by
  have : x.order ≠ y.order := by
    intro h
    have hyne : single y.order y.leadingCoeff ≠ 0 := single_ne_zero <| leadingCoeff_ne_iff.mpr hy
    rw [leadingCoeff_eq, ← h, coeff_order_of_eq_add_single hxy <| ne_zero_of_eq_add_single hxy hy,
      single_eq_zero] at hyne
    exact hyne rfl
  refine lt_of_le_of_ne ?_ this
  simp only [order, ne_zero_of_eq_add_single hxy hy, ↓reduceDIte, hy]
  have : y.support ⊆ x.support := by
    intro g hg
    by_cases hgx : g = x.order
    · refine (mem_support x g).mpr ?_
      have : x.coeff x.order ≠ 0 := coeff_order_ne_zero <| ne_zero_of_eq_add_single hxy hy
      rwa [← hgx] at this
    · have : x.coeff g = (y + (single x.order) x.leadingCoeff).coeff g := by rw [← hxy]
      rw [coeff_add, coeff_single_of_ne hgx, add_zero] at this
      simpa [this] using hg
  exact Set.IsWF.min_le_min_of_subset this

/-- `single` as an additive monoid/group homomorphism -/
@[simps!]
def single.addMonoidHom (a : Γ) : R →+ HahnSeries Γ R :=
  { single a with
    map_add' := single_add _ }

/-- `coeff g` as an additive monoid/group homomorphism -/
@[simps]
def coeff.addMonoidHom (g : Γ) : HahnSeries Γ R →+ R where
  toFun f := f.coeff g
  map_zero' := coeff_zero
  map_add' _ _ := coeff_add

section Domain

variable [PartialOrder Γ']

theorem embDomain_add (f : Γ ↪o Γ') (x y : HahnSeries Γ R) :
    embDomain f (x + y) = embDomain f x + embDomain f y := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_notin_range hg]

end Domain

end AddMonoid

section AddCommMonoid

variable [AddCommMonoid R]

instance : AddCommMonoid (HahnSeries Γ R) :=
  { inferInstanceAs (AddMonoid (HahnSeries Γ R)) with
    add_comm := fun x y => by
      ext
      apply add_comm }

open BigOperators

@[simp]
theorem coeff_sum {s : Finset α} {x : α → HahnSeries Γ R} (g : Γ) :
    (∑ i ∈ s, x i).coeff g = ∑ i ∈ s, (x i).coeff g :=
  cons_induction rfl (fun i s his hsum => by rw [sum_cons, sum_cons, coeff_add, hsum]) s

end AddCommMonoid

section AddGroup

variable [AddGroup R]

instance : Neg (HahnSeries Γ R) where
  neg x :=
    { coeff := fun a => -x.coeff a
      isPWO_support' := by
        rw [Function.support_neg]
        exact x.isPWO_support }

@[simp]
theorem coeff_neg' (x : HahnSeries Γ R) : (-x).coeff = -x.coeff :=
  rfl

@[deprecated (since := "2025-01-31")] alias neg_coeff' := coeff_neg'

theorem coeff_neg {x : HahnSeries Γ R} {a : Γ} : (-x).coeff a = -x.coeff a :=
  rfl

@[deprecated (since := "2025-01-31")] alias neg_coeff := coeff_neg

instance : Sub (HahnSeries Γ R) where
  sub x y :=
    { coeff := x.coeff - y.coeff
      isPWO_support' := (x.isPWO_support.union y.isPWO_support).mono (Function.support_sub _ _) }

@[simp]
theorem coeff_sub' (x y : HahnSeries Γ R) : (x - y).coeff = x.coeff - y.coeff :=
  rfl

@[deprecated (since := "2025-01-31")] alias sub_coeff' := coeff_sub'

theorem coeff_sub {x y : HahnSeries Γ R} {a : Γ} : (x - y).coeff a = x.coeff a - y.coeff a :=
  rfl

@[deprecated (since := "2025-01-31")] alias sub_coeff := coeff_sub

instance : AddGroup (HahnSeries Γ R) := fast_instance%
  coeff_injective.addGroup _
    coeff_zero' coeff_add' (coeff_neg') (coeff_sub')
    (fun _ _ => coeff_smul' _ _) (fun _ _ => coeff_smul' _ _)

@[simp]
theorem single_sub (a : Γ) (r s : R) : single a (r - s) = single a r - single a s :=
  map_sub (single.addMonoidHom a) _ _

@[simp]
theorem single_neg (a : Γ) (r : R) : single a (-r) = -single a r :=
  map_neg (single.addMonoidHom a) _

@[simp]
theorem support_neg {x : HahnSeries Γ R} : (-x).support = x.support := by
  ext
  simp

@[simp]
protected lemma map_neg [AddGroup S] (f : R →+ S) {x : HahnSeries Γ R} :
    ((-x).map f : HahnSeries Γ S) = -(x.map f) := by
  ext; simp

theorem orderTop_neg {x : HahnSeries Γ R} : (-x).orderTop = x.orderTop := by
  classical simp only [orderTop, support_neg, neg_eq_zero]

@[simp]
theorem order_neg [Zero Γ] {f : HahnSeries Γ R} : (-f).order = f.order := by
  classical
  by_cases hf : f = 0
  · simp only [hf, neg_zero]
  simp only [order, support_neg, neg_eq_zero]

@[simp]
protected lemma map_sub [AddGroup S] (f : R →+ S) {x y : HahnSeries Γ R} :
    ((x - y).map f : HahnSeries Γ S) = x.map f - y.map f := by
  ext; simp

theorem min_orderTop_le_orderTop_sub {Γ} [LinearOrder Γ] {x y : HahnSeries Γ R} :
    min x.orderTop y.orderTop ≤ (x - y).orderTop := by
  rw [sub_eq_add_neg, ← orderTop_neg (x := y)]
  exact min_orderTop_le_orderTop_add

theorem orderTop_sub {Γ} [LinearOrder Γ] {x y : HahnSeries Γ R}
    (hxy : x.orderTop < y.orderTop) : (x - y).orderTop = x.orderTop := by
  rw [sub_eq_add_neg]
  rw [← orderTop_neg (x := y)] at hxy
  exact orderTop_add_eq_left hxy

theorem leadingCoeff_sub {Γ} [LinearOrder Γ] {x y : HahnSeries Γ R}
    (hxy : x.orderTop < y.orderTop) : (x - y).leadingCoeff = x.leadingCoeff := by
  rw [sub_eq_add_neg]
  rw [← orderTop_neg (x := y)] at hxy
  exact leadingCoeff_add_eq_left hxy

end AddGroup

instance [AddCommGroup R] : AddCommGroup (HahnSeries Γ R) :=
  { inferInstanceAs (AddCommMonoid (HahnSeries Γ R)),
    inferInstanceAs (AddGroup (HahnSeries Γ R)) with }

end Addition

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

variable [PartialOrder Γ] [Semiring R] [AddCommMonoid V] [Module R V]

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

/-- `coeff g` as a linear map -/
@[simps]
def coeff.linearMap (g : Γ) : HahnSeries Γ V →ₗ[R] V :=
  { coeff.addMonoidHom g with map_smul' := fun _ _ => rfl }

@[simp]
protected lemma map_smul [AddCommMonoid U] [Module R U] (f : U →ₗ[R] V) {r : R}
    {x : HahnSeries Γ U} : (r • x).map f = r • ((x.map f) : HahnSeries Γ V) := by
  ext; simp

section Domain

variable [PartialOrder Γ']

theorem embDomain_smul (f : Γ ↪o Γ') (r : R) (x : HahnSeries Γ R) :
    embDomain f (r • x) = r • embDomain f x := by
  ext g
  by_cases hg : g ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hg
    simp
  · simp [embDomain_notin_range hg]

/-- Extending the domain of Hahn series is a linear map. -/
@[simps]
def embDomainLinearMap (f : Γ ↪o Γ') : HahnSeries Γ R →ₗ[R] HahnSeries Γ' R where
  toFun := embDomain f
  map_add' := embDomain_add f
  map_smul' := embDomain_smul f

end Domain

end Module

end HahnSeries
