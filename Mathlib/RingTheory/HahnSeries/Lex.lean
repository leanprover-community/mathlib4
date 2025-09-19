/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Algebra.Order.Archimedean.Class
import Mathlib.Order.Hom.Lex
import Mathlib.Order.PiLex
import Mathlib.RingTheory.HahnSeries.Addition

/-!

# Lexicographical order on Hahn series

In this file, we define lexicographical ordered `Lex (HahnSeries Γ R)`, and show this
is a `LinearOrder` when `Γ` and `R` themselves are linearly ordered. Additionally,
it is an ordered group when `R` is.

## Main definitions

* `HahnSeries.finiteArchimedeanClassOrderIsoLex`: `FiniteArchimedeanClass` of `Lex (HahnSeries Γ R)`
  can be decomposed by `Γ`.

-/

namespace HahnSeries

variable {Γ R : Type*} [LinearOrder Γ]

section PartialOrder
variable [Zero R] [PartialOrder R]

instance : PartialOrder (Lex (HahnSeries Γ R)) :=
  PartialOrder.lift (toLex <| ofLex · |>.coeff) fun x y ↦ by simp

theorem lt_iff (a b : Lex (HahnSeries Γ R)) :
    a < b ↔ ∃ (i : Γ), (∀ (j : Γ), j < i → (ofLex a).coeff j = (ofLex b).coeff j)
    ∧ (ofLex a).coeff i < (ofLex b).coeff i := by rfl

end PartialOrder

section LinearOrder
variable [Zero R] [LinearOrder R]

noncomputable
instance : LinearOrder (Lex (HahnSeries Γ R)) where
  le_total a b := by
    rcases eq_or_ne a b with hab | hab
    · exact Or.inl hab.le
    · have hab := Function.ne_iff.mp <| HahnSeries.ext_iff.ne.mp hab
      let u := {i : Γ | (ofLex a).coeff i ≠ 0} ∪ {i : Γ | (ofLex b).coeff i ≠ 0}
      let v := {i : Γ | (ofLex a).coeff i ≠ (ofLex b).coeff i}
      have hvu : v ⊆ u := by
        intro i h
        rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
        contrapose! h
        rw [Set.notMem_setOf_iff, Mathlib.Tactic.PushNeg.not_ne_eq, h.1, h.2]
      have hv : v.IsWF :=
        ((ofLex a).isPWO_support'.isWF.union (ofLex b).isPWO_support'.isWF).subset hvu
      let i := hv.min hab
      have hji (j) : j < i → (ofLex a).coeff j = (ofLex b).coeff j :=
        not_imp_not.mp <| fun h' ↦ hv.not_lt_min hab h'
      have hne : (ofLex a).coeff i ≠ (ofLex b).coeff i := hv.min_mem hab
      obtain hi | hi := lt_or_gt_of_ne hne
      · exact Or.inl (le_of_lt ⟨i, hji, hi⟩)
      · exact Or.inr (le_of_lt ⟨i, fun j hj ↦ (hji j hj).symm, hi⟩)
  toDecidableLE := Classical.decRel _

@[simp]
theorem leadingCoeff_pos_iff {x : Lex (HahnSeries Γ R)} : 0 < (ofLex x).leadingCoeff ↔ 0 < x := by
  rw [lt_iff]
  constructor
  · intro hpos
    have hne : (ofLex x) ≠ 0 := leadingCoeff_ne_zero.mp hpos.ne.symm
    have htop : (ofLex x).orderTop ≠ ⊤ := orderTop_ne_top.2 hne
    refine ⟨(ofLex x).orderTop.untop htop, ?_, by simpa [coeff_untop_eq_leadingCoeff] using hpos⟩
    intro j hj
    simpa using (coeff_eq_zero_of_lt_orderTop ((WithTop.lt_untop_iff htop).mp hj)).symm
  · intro ⟨i, hj, hi⟩
    have horder : (ofLex x).orderTop = WithTop.some i := by
      apply orderTop_eq_of_le
      · simpa using hi.ne.symm
      · intro g hg
        contrapose! hg
        simpa using (hj g hg).symm
    have htop : (ofLex x).orderTop ≠ ⊤ := WithTop.ne_top_iff_exists.mpr ⟨i, horder.symm⟩
    have hne : ofLex x ≠ 0 := orderTop_ne_top.1 htop
    have horder' : (ofLex x).orderTop.untop htop = i := (WithTop.untop_eq_iff _).mpr horder
    rw [leadingCoeff_of_ne_zero hne, horder']
    simpa using hi

theorem leadingCoeff_nonneg_iff {x : Lex (HahnSeries Γ R)} :
    0 ≤ (ofLex x).leadingCoeff ↔ 0 ≤ x := by
  constructor
  · intro h
    obtain heq | hlt := h.eq_or_lt
    · exact le_of_eq (leadingCoeff_eq_zero.mp heq.symm).symm
    · exact (leadingCoeff_pos_iff.mp hlt).le
  · intro h
    obtain rfl | hlt := h.eq_or_lt
    · simp
    · exact (leadingCoeff_pos_iff.mpr hlt).le

theorem leadingCoeff_neg_iff {x : Lex (HahnSeries Γ R)} : (ofLex x).leadingCoeff < 0 ↔ x < 0 := by
  simpa using (leadingCoeff_nonneg_iff (x := x)).not

theorem leadingCoeff_nonpos_iff {x : Lex (HahnSeries Γ R)} :
    (ofLex x).leadingCoeff ≤ 0 ↔ x ≤ 0 := by
  simp [← not_lt]

end LinearOrder

section OrderedMonoid
variable [PartialOrder R] [AddCommMonoid R] [AddLeftStrictMono R] [IsOrderedAddMonoid R]

instance : IsOrderedAddMonoid (Lex (HahnSeries Γ R)) where
  add_le_add_left a b hab c := by
    obtain rfl | hlt := hab.eq_or_lt
    · simp
    · apply le_of_lt
      rw [lt_iff] at hlt ⊢
      obtain ⟨i, hj, hi⟩ := hlt
      refine ⟨i, ?_, ?_⟩
      · intro j hji
        simpa using congrArg ((ofLex c).coeff j + ·) (hj j hji)
      · simpa using add_lt_add_left hi ((ofLex c).coeff i)

end OrderedMonoid

section OrderedGroup
variable [LinearOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]

@[simp]
theorem support_abs (x : Lex (HahnSeries Γ R)) : (ofLex |x|).support = (ofLex x).support := by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle]
    simp
  · rw [abs_eq_self.mpr hge]

@[simp]
theorem orderTop_abs (x : Lex (HahnSeries Γ R)) : (ofLex |x|).orderTop = (ofLex x).orderTop := by
  obtain hle | hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle, ofLex_neg, orderTop_neg]
  · rw [abs_eq_self.mpr hge]

theorem order_abs [Zero Γ] (x : Lex (HahnSeries Γ R)) : (ofLex |x|).order = (ofLex x).order := by
  obtain rfl | hne := eq_or_ne x 0
  · simp
  · have hne' : ofLex x ≠ 0 := hne
    have habs : ofLex |x| ≠ 0 := by simpa using hne
    apply WithTop.coe_injective
    rw [order_eq_orderTop_of_ne_zero habs, order_eq_orderTop_of_ne_zero hne']
    apply orderTop_abs

theorem leadingCoeff_abs (x : Lex (HahnSeries Γ R)) :
    (ofLex |x|).leadingCoeff = |(ofLex x).leadingCoeff| := by
  obtain hlt | rfl | hgt := lt_trichotomy x 0
  · obtain hlt' := leadingCoeff_neg_iff.mpr hlt
    rw [abs_eq_neg_self.mpr hlt.le, abs_eq_neg_self.mpr hlt'.le, ofLex_neg, leadingCoeff_neg]
  · simp
  · obtain hgt' := leadingCoeff_pos_iff.mpr hgt
    rw [abs_eq_self.mpr hgt.le, abs_eq_self.mpr hgt'.le]

theorem abs_lt_abs_of_orderTop_ofLex {x y : Lex (HahnSeries Γ R)}
    (h : (ofLex y).orderTop < (ofLex x).orderTop) : |x| < |y| := by
  rw [← orderTop_abs x, ← orderTop_abs y] at h
  refine (lt_iff _ _).mpr ⟨(ofLex |y|).orderTop.untop h.ne_top, ?_, ?_⟩
  · simp +contextual [-orderTop_abs, coeff_eq_zero_of_lt_orderTop, h.trans']
  · simpa [-orderTop_abs, coeff_eq_zero_of_lt_orderTop, coeff_untop_eq_leadingCoeff, h]
      using h.ne_top

theorem archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLex {x y : Lex (HahnSeries Γ R)}
    (h : (ofLex x).orderTop = (ofLex y).orderTop) :
    ArchimedeanClass.mk x ≤ .mk y ↔
      ArchimedeanClass.mk (ofLex x).leadingCoeff ≤ .mk (ofLex y).leadingCoeff := by
  simp_rw [ArchimedeanClass.mk_le_mk]
  obtain rfl | hy := eq_or_ne y 0
  · -- special case: both `x` and `y` are zero
    simp_all
  -- general case: `x` and `y` are not zero
  have hx : x ≠ 0 := by simpa using orderTop_ne_top.1 <| h ▸ orderTop_ne_top.2 (by simpa using hy)
  have h' : (ofLex |x|).orderTop = (ofLex |y|).orderTop := by simpa using h
  constructor
  · -- `mk x ≤ mk y → mk x.leadingCoeff ≤ mk y.leadingCoeff`
    intro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    have hn' : |y| < (n + 1) • |x| :=
      lt_of_le_of_lt hn <| nsmul_lt_nsmul_left (by simpa using hx) (by simp)
    obtain ⟨j, hj, hi⟩ := (lt_iff _ _).mp hn'
    simp_rw [ofLex_smul, coeff_smul] at hj hi
    simp_rw [← leadingCoeff_abs]
    rw [leadingCoeff_of_ne_zero (by simpa using hy), leadingCoeff_of_ne_zero (by simpa using hx)]
    simp_rw [← h']
    obtain hjlt | hjeq | hjgt := lt_trichotomy (WithTop.some j) (ofLex |x|).orderTop
    · -- impossible case: `x` and `y` differ before their leading coefficients
      have hjlt' : j < (ofLex |y|).orderTop := h'.symm ▸ hjlt
      simp [coeff_eq_zero_of_lt_orderTop hjlt, coeff_eq_zero_of_lt_orderTop hjlt'] at hi
    · convert hi.le <;> exact (WithTop.untop_eq_iff _).mpr hjeq.symm
    · exact (hj _ ((WithTop.untop_lt_iff _).mpr hjgt)).le
  · -- `mk x.leadingCoeff ≤ mk y.leadingCoeff → mk x ≤ mk y`
    intro ⟨n, hn⟩
    refine ⟨n + 1, ((lt_iff _ _).mpr ?_).le⟩
    refine ⟨(ofLex x).orderTop.untop (by simpa using hx), ?_, ?_⟩
    · -- all coefficients before the leading coefficient are zero
      intro j hj
      trans 0
      · apply coeff_eq_zero_of_lt_orderTop
        simpa [← h] using hj
      · suffices (ofLex |x|).coeff j = 0 by simp [this]
        apply coeff_eq_zero_of_lt_orderTop
        simpa using hj
    -- the leading coefficient determines the relation
    rw [ofLex_smul, coeff_smul]
    suffices |(ofLex y).leadingCoeff| < (n + 1) • |(ofLex x).leadingCoeff| by
      simp_rw [← leadingCoeff_abs] at this
      rw [leadingCoeff_of_ne_zero (by simpa using hy), leadingCoeff_of_ne_zero (by simpa using hx)]
        at this
      convert this using 3 <;> simp [h]
    refine lt_of_le_of_lt hn <| nsmul_lt_nsmul_left ?_ (by simp)
    rwa [abs_pos, leadingCoeff_ne_zero]

theorem archimedeanClassMk_le_archimedeanClassMk_iff {x y : Lex (HahnSeries Γ R)} :
    ArchimedeanClass.mk x ≤ .mk y ↔
      (ofLex x).orderTop < (ofLex y).orderTop ∨
        (ofLex x).orderTop = (ofLex y).orderTop ∧
          ArchimedeanClass.mk (ofLex x).leadingCoeff ≤ .mk (ofLex y).leadingCoeff := by
  obtain hlt | heq | hgt := lt_trichotomy (ofLex x).orderTop (ofLex y).orderTop
  · -- when `x`'s order is less than `y`'s, this reduces to abs_lt_abs_of_orderTop_ofLex
    simpa [ArchimedeanClass.mk_le_mk, hlt] using
      ⟨1, by simpa using (abs_lt_abs_of_orderTop_ofLex hlt).le⟩
  · -- when `x` and `y` have the same order, this reduces to
    -- `archimedeanClass_le_iff_of_orderTop_eq`
    simpa [heq] using archimedeanClassMk_le_archimedeanClassMk_iff_of_orderTop_ofLex heq
  -- when `x`'s order is greater than `y`'s, neither side is true
  simp_rw [ArchimedeanClass.mk_le_mk]
  refine ⟨?_, by simp [hgt.not_gt, hgt.ne']⟩
  intro ⟨n, hn⟩
  contrapose! hn
  rw [← abs_nsmul]
  have hgt' : (ofLex y).orderTop < (ofLex (n • x)).orderTop := by
    apply lt_of_lt_of_le hgt
    simpa using orderTop_smul_not_lt n (ofLex x)
  exact abs_lt_abs_of_orderTop_ofLex hgt'

theorem archimedeanClassMk_eq_archimedeanClassMk_iff {x y : Lex (HahnSeries Γ R)} :
    ArchimedeanClass.mk x = ArchimedeanClass.mk y ↔
    (ofLex x).orderTop = (ofLex y).orderTop ∧
    ArchimedeanClass.mk (ofLex x).leadingCoeff = ArchimedeanClass.mk (ofLex y).leadingCoeff := by
  rw [le_antisymm_iff, archimedeanClassMk_le_archimedeanClassMk_iff,
    archimedeanClassMk_le_archimedeanClassMk_iff]
  constructor
  · simpa +contextual [or_imp, ne_of_gt, le_of_lt] using fun _ ↦ le_antisymm
  · intro ⟨horder, hcoeff⟩
    exact ⟨.inr ⟨horder, hcoeff.le⟩, .inr ⟨horder.symm, hcoeff.ge⟩⟩

variable (Γ R) in
/-- Finite archimedean classes of `Lex (HahnSeries Γ R)` decompose into lexicographical pairs
of `order` and the finite archimedean class of `leadingCoeff`. -/
noncomputable def finiteArchimedeanClassOrderHomLex :
    FiniteArchimedeanClass (Lex (HahnSeries Γ R)) →o Γ ×ₗ FiniteArchimedeanClass R :=
  FiniteArchimedeanClass.liftOrderHom
    (fun ⟨x, hx⟩ ↦ toLex
      ⟨(ofLex x).orderTop.untop (by simp [orderTop_of_ne_zero (show ofLex x ≠ 0 by exact hx)]),
      FiniteArchimedeanClass.mk (ofLex x).leadingCoeff (leadingCoeff_ne_zero.mpr hx)⟩)
    fun ⟨a, ha⟩ ⟨b, hb⟩ h ↦ by
      rw [Prod.Lex.le_iff]
      simp only [ofLex_toLex]
      rw [FiniteArchimedeanClass.mk_le_mk] at ⊢ h
      rw [WithTop.untop_eq_iff]
      simpa using archimedeanClassMk_le_archimedeanClassMk_iff.mp h

variable (Γ R) in
/-- The inverse of `finiteArchimedeanClassOrderHomLex`. -/
noncomputable def finiteArchimedeanClassOrderHomInvLex :
    Γ ×ₗ FiniteArchimedeanClass R →o FiniteArchimedeanClass (Lex (HahnSeries Γ R)) where
  toFun x := (ofLex x).2.liftOrderHom
    (fun a ↦ FiniteArchimedeanClass.mk (toLex (single (ofLex x).1 a.val)) (by
      simpa using a.prop))
    fun ⟨a, ha⟩ ⟨b, hb⟩ h ↦ by
      rw [FiniteArchimedeanClass.mk_le_mk, archimedeanClassMk_le_archimedeanClassMk_iff]
      simpa [ha, hb] using h
  monotone' a b := a.rec fun (ao, ac) ↦ b.rec fun (bo, bc) h ↦ by
    obtain h | ⟨rfl, hle⟩ := Prod.Lex.le_iff.mp h
    · induction ac using FiniteArchimedeanClass.ind with | mk a ha
      induction bc using FiniteArchimedeanClass.ind with | mk b hb
      simp [ofLex_toLex, FiniteArchimedeanClass.liftOrderHom_mk]
      rw [FiniteArchimedeanClass.mk_le_mk, archimedeanClassMk_le_archimedeanClassMk_iff]
      exact .inl (by simpa [ha, hb] using h)
    · exact OrderHom.monotone _ hle

variable (Γ R) in
/-- The correspondence between finite archimedean classes of `Lex (HahnSeries Γ R)`
and lexicographical pairs of `HahnSeries.orderTop` and the finite archimedean class of
`HahnSeries.leadingCoeff`. -/
noncomputable def finiteArchimedeanClassOrderIsoLex :
    FiniteArchimedeanClass (Lex (HahnSeries Γ R)) ≃o Γ ×ₗ FiniteArchimedeanClass R := by
  apply OrderIso.ofHomInv (finiteArchimedeanClassOrderHomLex Γ R)
    (finiteArchimedeanClassOrderHomInvLex Γ R)
  · ext x
    cases x with | h x
    obtain ⟨order, coeff⟩ := x
    induction coeff using FiniteArchimedeanClass.ind with | mk a ha
    simp [finiteArchimedeanClassOrderHomLex, finiteArchimedeanClassOrderHomInvLex, ha]
  · ext x
    induction x using FiniteArchimedeanClass.ind with | mk a ha
    simp [finiteArchimedeanClassOrderHomLex, finiteArchimedeanClassOrderHomInvLex,
      archimedeanClassMk_eq_archimedeanClassMk_iff, ha]

@[simp]
theorem finiteArchimedeanClassOrderIsoLex_apply_fst {x : Lex (HahnSeries Γ R)} (h : x ≠ 0) :
    (ofLex (finiteArchimedeanClassOrderIsoLex Γ R (FiniteArchimedeanClass.mk x h))).1 =
    (ofLex x).orderTop := by
  simp [finiteArchimedeanClassOrderIsoLex, finiteArchimedeanClassOrderHomLex]

@[simp]
theorem finiteArchimedeanClassOrderIsoLex_apply_snd {x : Lex (HahnSeries Γ R)} (h : x ≠ 0) :
    (ofLex (finiteArchimedeanClassOrderIsoLex Γ R (FiniteArchimedeanClass.mk x h))).2.val =
    ArchimedeanClass.mk (ofLex x).leadingCoeff := by
  simp [finiteArchimedeanClassOrderIsoLex, finiteArchimedeanClassOrderHomLex]

section Archimedean
variable [Archimedean R] [Nontrivial R]

variable (Γ R) in
/-- For `Archimedean` coefficients, there is a correspondence between finite
archimedean classes and `HahnSeries.orderTop` without the top element. -/
noncomputable def finiteArchimedeanClassOrderIso :
    FiniteArchimedeanClass (Lex (HahnSeries Γ R)) ≃o Γ :=
  have : Unique (FiniteArchimedeanClass R) := (nonempty_unique _).some
  (finiteArchimedeanClassOrderIsoLex Γ R).trans (Prod.Lex.prodUnique _ _)

@[simp]
theorem finiteArchimedeanClassOrderIso_apply {x : Lex (HahnSeries Γ R)} (h : x ≠ 0) :
    finiteArchimedeanClassOrderIso Γ R (FiniteArchimedeanClass.mk x h) = (ofLex x).orderTop := by
  simp [finiteArchimedeanClassOrderIso]

variable (Γ R) in
/-- For `Archimedean` coefficients, there is a correspondence between
archimedean classes (with top) and `HahnSeries.orderTop`. -/
noncomputable def archimedeanClassOrderIsoWithTop :
    ArchimedeanClass (Lex (HahnSeries Γ R)) ≃o WithTop Γ :=
  (FiniteArchimedeanClass.withTopOrderIso _).symm.trans
  (finiteArchimedeanClassOrderIso _ _).withTopCongr

@[simp]
theorem archimedeanClassOrderIsoWithTop_apply (x : Lex (HahnSeries Γ R)) :
    archimedeanClassOrderIsoWithTop Γ R (ArchimedeanClass.mk x) = (ofLex x).orderTop := by
  unfold archimedeanClassOrderIsoWithTop
  obtain rfl | h := eq_or_ne x 0 <;>
    simp [FiniteArchimedeanClass.withTopOrderIso_symm_apply, *]

end Archimedean

end OrderedGroup

section EmbDomain
variable [PartialOrder R] {Γ' : Type*} [LinearOrder Γ'] (f : Γ ↪o Γ')

/-- `HahnSeries.embDomain` as an `OrderEmbedding`. -/
@[simps]
noncomputable
def embDomainOrderEmbedding [Zero R] : Lex (HahnSeries Γ R) ↪o Lex (HahnSeries Γ' R) where
  toFun a := toLex (embDomain f (ofLex a))
  inj' := toLex.injective.comp (embDomain_injective.comp (ofLex.injective))
  map_rel_iff' {a b} := by
    simp_rw [le_iff_lt_or_eq, lt_iff]
    simp only [Function.Embedding.coeFn_mk, ofLex_toLex, EmbeddingLike.apply_eq_iff_eq]
    constructor
    · rintro (⟨i, hj, hi⟩ | heq)
      · have himem : i ∈ Set.range f := by
          contrapose! hi
          simp [embDomain_notin_range hi]
        obtain ⟨k, rfl⟩ := himem
        refine Or.inl ⟨k, fun j hjk ↦ ?_, by simpa using hi⟩
        simpa using hj (f j) (f.lt_iff_lt.mpr hjk)
      · exact Or.inr <| embDomain_injective.comp (ofLex.injective) heq
    · rintro (⟨i, hj, hi⟩ | rfl)
      · refine Or.inl ⟨f i, fun k hki ↦ ?_, by simpa using hi⟩
        by_cases hkmem : k ∈ Set.range f
        · obtain ⟨j', rfl⟩ := hkmem
          simpa using hj _ <| f.lt_iff_lt.mp hki
        · simp_rw [embDomain_notin_range hkmem]
      · simp

/-- `HahnSeries.embDomain` as an `OrderAddMonoidHom`. -/
@[simps]
noncomputable
def embDomainOrderAddMonoidHom [AddMonoid R] : Lex (HahnSeries Γ R) →+o Lex (HahnSeries Γ' R) where
  __ := (embDomainOrderEmbedding f).toOrderHom
  map_zero' := by simp
  map_add' := by simp [embDomainOrderEmbedding, embDomain_add]

theorem embDomainOrderAddMonoidHom_injective [AddMonoid R] :
    Function.Injective (embDomainOrderAddMonoidHom f (R := R)) :=
  (embDomainOrderEmbedding f).injective

end EmbDomain

end HahnSeries
