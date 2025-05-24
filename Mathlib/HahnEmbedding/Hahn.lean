import Mathlib.HahnEmbedding.ArchimedeanSubgroup
import Mathlib.HahnEmbedding.LinearPMap

import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Data.Rat.Star
import Mathlib.Order.PiLex
import Mathlib.RingTheory.HahnSeries.Addition

open Classical in
noncomputable
def HahnSeries.cut_fun (Γ : Type*) (R : Type*) [PartialOrder Γ] [Zero R]
    (c : Γ) (x : HahnSeries Γ R) : HahnSeries Γ R where
  coeff (i) := if c ≤ i then 0 else x.coeff i
  isPWO_support' := by
    apply Set.IsPWO.mono x.isPWO_support
    simp

noncomputable
def HahnSeries.cut (Γ : Type*) (R : Type*) [PartialOrder Γ] [Semiring R]
    (c : Γ) : HahnSeries Γ R →ₗ[R] HahnSeries Γ R where
  toFun := HahnSeries.cut_fun Γ R c
  map_add' := by
    intro x y
    unfold cut_fun
    apply HahnSeries.ext
    ext i
    simp only [coeff_add', Pi.add_apply]
    split_ifs
    · simp
    · simp
  map_smul' := by
    intro m x
    unfold cut_fun
    apply HahnSeries.ext
    ext i
    simp


instance HahnSeries.instPartialOrder (Γ : Type*) (R : Type*)
    [LinearOrder Γ] [Zero R] [PartialOrder R] : PartialOrder (HahnSeries Γ R) :=
  PartialOrder.lift (fun (x : HahnSeries Γ R) ↦ toLex x.coeff) (by
    intro x y
    simp
  )

noncomputable
instance HahnSeries.instLinearOrder (Γ : Type*) (R : Type*)
    [LinearOrder Γ] [Zero R] [LinearOrder R] : LinearOrder (HahnSeries Γ R) := {

  le_total := by
    intro a b
    suffices a < b ∨ a = b ∨ b < a by
      obtain lt|eq|gt := this
      · exact Or.inl lt.le
      · exact Or.inl eq.le
      · exact Or.inr gt.le
    rcases eq_or_ne a b with hab | hab
    · exact Or.inr (Or.inl hab)
    · have hab := (HahnSeries.ext_iff.ne).mp hab
      rw [Function.ne_iff] at hab
      let u := {i : Γ | a.coeff i ≠ 0} ∪ {i : Γ | b.coeff i ≠ 0}
      obtain h := a.isPWO_support'.isWF.union b.isPWO_support'.isWF
      let v := {i : Γ | a.coeff i ≠ b.coeff i}
      have hvu : v ⊆ u := by
        unfold u v
        intro i h
        simp only [Set.mem_setOf_eq] at h
        simp only [Set.mem_union, Set.mem_setOf_eq]
        rw [or_iff_not_imp_left]
        intro h2
        simp only [ne_eq, Decidable.not_not] at h2
        rw [h2] at h
        exact h.symm
      have hv : v.IsWF := h.subset hvu
      let i := hv.min hab
      have hri : ∀ j, j < i → a.coeff j = b.coeff j := by
        intro j
        rw [← not_imp_not]
        exact fun h' => hv.not_lt_min hab h'
      have hne : a.coeff i ≠ b.coeff i := hv.min_mem hab
      rcases lt_trichotomy (a.coeff i) (b.coeff i) with hi | hi
      exacts [Or.inl ⟨i, hri, hi⟩,
        Or.inr <| Or.inr <| ⟨i, fun j hj => (hri j hj).symm, hi.resolve_left hne⟩]


  toDecidableLE := by apply Classical.decRel

}

theorem HahnSeries.lt_iff {Γ : Type*} {R : Type*}
    [LinearOrder Γ] [Zero R] [PartialOrder R] (a b : HahnSeries Γ R) :
    a < b ↔ ∃ (i : Γ), (∀ (j : Γ), j < i → a.coeff j = b.coeff j) ∧ a.coeff i < b.coeff i := by
  rfl

instance HahnSeries.instOrderedAddMonoid (Γ : Type*) (R : Type*)
    [LinearOrder Γ] [PartialOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]:
    IsOrderedAddMonoid (HahnSeries Γ R) where
  add_le_add_left := by
    intro a b hab c
    obtain heq|hlt := eq_or_lt_of_le hab
    · rw [heq]
    · apply le_of_lt
      rw [HahnSeries.lt_iff] at hlt ⊢
      obtain ⟨i, hi⟩ := hlt
      use i
      aesop

theorem HahnSeries.leadingCoeff_eq_coeff {Γ : Type*} {R : Type*}
    [PartialOrder Γ] [Zero R]
    (x : HahnSeries Γ R) (hx : x.orderTop ≠ ⊤) : x.leadingCoeff = x.coeff (x.orderTop.untop hx) := by
  have hx : x ≠ 0 := ne_zero_iff_orderTop.mpr hx
  rw [HahnSeries.leadingCoeff_of_ne hx]
  rw [(WithTop.untop_eq_iff _).mpr (HahnSeries.orderTop_of_ne hx)]

theorem HahnSeries.leadingCoeff_neg {Γ : Type*} {R : Type*} [PartialOrder Γ] [AddGroup R]
    (x : HahnSeries Γ R) : (-x).leadingCoeff = -x.leadingCoeff := by
  by_cases hx : x = 0
  · rw [hx]
    simp
  · have hnx : -x ≠ 0 := neg_ne_zero.mpr hx
    have hx' : x.orderTop ≠ ⊤ := ne_zero_iff_orderTop.mp hx
    have hnx' : (-x).orderTop ≠ ⊤ := ne_zero_iff_orderTop.mp hnx
    rw [HahnSeries.leadingCoeff_eq_coeff x hx']
    rw [HahnSeries.leadingCoeff_eq_coeff (-x) hnx']
    rw [HahnSeries.coeff_neg]
    simp_rw [HahnSeries.orderTop_neg]

theorem HahnSeries.leadingCoeff_pos_iff {Γ : Type*} {R : Type*}
    [LinearOrder Γ] [LinearOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]
    (x : HahnSeries Γ R) : 0 < x.leadingCoeff ↔ 0 < x := by
  rw [HahnSeries.lt_iff]
  constructor
  · intro hpos
    have htop : x.orderTop ≠ ⊤ := by
      refine ne_zero_iff_orderTop.mp ?_
      refine leadingCoeff_ne_iff.mp ?_
      exact hpos.ne.symm
    use x.orderTop.untop htop
    constructor
    · intro j hj
      simp only [coeff_zero]
      refine (coeff_eq_zero_of_lt_orderTop ?_).symm
      exact (WithTop.lt_untop_iff htop).mp hj
    · rw [← HahnSeries.leadingCoeff_eq_coeff]
      simpa using hpos
  · intro h
    obtain ⟨i, hj, hi⟩ := h
    simp only [coeff_zero] at hi
    have horder : x.orderTop = WithTop.some i := by
      apply HahnSeries.orderTop_eq_of_le
      · simpa using hi.ne.symm
      · intro g hg
        contrapose! hg
        simpa using (hj g hg).symm
    have htop : x.orderTop ≠ ⊤ := WithTop.ne_top_iff_exists.mpr ⟨i, horder.symm⟩
    have horder' : x.orderTop.untop htop  = i :=
      (WithTop.untop_eq_iff _).mpr horder

    rw [HahnSeries.leadingCoeff_eq_coeff _ htop]
    rw [horder']
    exact hi

theorem HahnSeries.leadingCoeff_neg_iff {Γ : Type*} {R : Type*}
    [LinearOrder Γ] [LinearOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]
    (x : HahnSeries Γ R) : x.leadingCoeff < 0 ↔ x < 0 := by
  constructor
  · intro h
    contrapose! h
    obtain heq|hlt := eq_or_lt_of_le h
    · rw [← heq]
      simp
    · exact ((HahnSeries.leadingCoeff_pos_iff _).mpr hlt).le
  · intro h
    contrapose! h
    obtain heq|hlt := eq_or_lt_of_le h
    · exact (HahnSeries.leadingCoeff_eq_iff.mp heq.symm).symm.le
    · exact ((HahnSeries.leadingCoeff_pos_iff _).mp hlt).le


theorem HahnSeries.abs_order {Γ : Type*} {R : Type*}
    [LinearOrder Γ] [LinearOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]
    (x : HahnSeries Γ R) : |x|.orderTop = x.orderTop := by
  obtain hle|hge := le_total x 0
  · rw [abs_eq_neg_self.mpr hle]
    rw [HahnSeries.orderTop_neg]
  · rw [abs_eq_self.mpr hge]

theorem HahnSeries.abs_leadingCoeff {Γ : Type*} {R : Type*}
    [LinearOrder Γ] [LinearOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]
    (x : HahnSeries Γ R) : |x|.leadingCoeff = |x.leadingCoeff| := by
  obtain hlt|heq|hgt := lt_trichotomy x 0
  · obtain hlt' := (HahnSeries.leadingCoeff_neg_iff _).mpr hlt
    rw [abs_eq_neg_self.mpr hlt.le, abs_eq_neg_self.mpr hlt'.le]
    rw [HahnSeries.leadingCoeff_neg]
  · rw [heq]
    simp
  · obtain hgt' := (HahnSeries.leadingCoeff_pos_iff _).mpr hgt
    rw [abs_eq_self.mpr hgt.le, abs_eq_self.mpr hgt'.le]


theorem HahnSeries.archimedeanClass_eq_iff {Γ : Type*} {R : Type*}
    [LinearOrder Γ] [LinearOrder R] [AddCommGroup R] [IsOrderedAddMonoid R]
    [Archimedean R]
    {x y : HahnSeries Γ R} :
    archimedeanClass.mk x = archimedeanClass.mk y ↔ x.orderTop = y.orderTop := by

  by_cases hyt : y.orderTop = ⊤
  · rw [hyt]
    have hy0 : y = 0 := orderTop_eq_top_iff.mp hyt
    have hy0' : archimedeanClass.mk y = 0 := archimedeanClass.eq_zero_iff.mpr hy0
    rw [hy0']
    rw [archimedeanClass.eq_zero_iff]
    exact Iff.symm orderTop_eq_top_iff
  · by_cases hxt : x.orderTop = ⊤
    · rw [hxt]
      have hx0 : x = 0 := orderTop_eq_top_iff.mp hxt
      have hx0' : archimedeanClass.mk x = 0 := archimedeanClass.eq_zero_iff.mpr hx0
      rw [hx0']
      rw [eq_comm]
      nth_rw 2 [eq_comm]
      rw [archimedeanClass.eq_zero_iff]
      exact Iff.symm orderTop_eq_top_iff
    · have hy0 : y ≠ 0 := ne_zero_iff_orderTop.mpr hyt
      have hx0 : x ≠ 0 := ne_zero_iff_orderTop.mpr hxt
      rw [archimedeanClass.eq]
      constructor
      · intro ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩
        by_contra!
        obtain hxy|hxy := lt_or_gt_of_ne this
        · contrapose! hm
          use x.orderTop.untop (HahnSeries.ne_zero_iff_orderTop.mp hx0)
          constructor
          · simp only [coeff_nsmul, Pi.toLex_apply, Pi.smul_apply]
            intro j hj
            rw [HahnSeries.coeff_eq_zero_of_lt_orderTop (by
              rw [HahnSeries.abs_order]
              refine lt_trans ?_ hxy
              exact (WithTop.lt_untop_iff _).mp hj
            )]
            rw [HahnSeries.coeff_eq_zero_of_lt_orderTop (by
              rw [HahnSeries.abs_order]
              exact (WithTop.lt_untop_iff _).mp hj
            )]
            simp
          · simp only [ne_eq, coeff_nsmul, Pi.toLex_apply, Pi.smul_apply]
            rw [HahnSeries.coeff_eq_zero_of_lt_orderTop (by
              rw [HahnSeries.abs_order]
              simpa using hxy
            )]
            conv in x.orderTop =>
              rw [← HahnSeries.abs_order]
            rw [← HahnSeries.leadingCoeff_eq_coeff]
            simp only [smul_zero]
            rw [HahnSeries.leadingCoeff_pos_iff]
            simpa using hx0
        · contrapose! hn
          use y.orderTop.untop (HahnSeries.ne_zero_iff_orderTop.mp hy0)
          constructor
          · simp only [coeff_nsmul, Pi.toLex_apply, Pi.smul_apply]
            intro j hj
            rw [HahnSeries.coeff_eq_zero_of_lt_orderTop (by
              rw [HahnSeries.abs_order]
              refine lt_trans ?_ hxy
              exact (WithTop.lt_untop_iff _).mp hj
            )]
            rw [HahnSeries.coeff_eq_zero_of_lt_orderTop (by
              rw [HahnSeries.abs_order]
              exact (WithTop.lt_untop_iff _).mp hj
            )]
            simp
          · simp only [ne_eq, coeff_nsmul, Pi.toLex_apply, Pi.smul_apply]
            rw [HahnSeries.coeff_eq_zero_of_lt_orderTop (by
              rw [HahnSeries.abs_order]
              simpa using hxy
            )]
            conv in y.orderTop =>
              rw [← HahnSeries.abs_order]
            rw [← HahnSeries.leadingCoeff_eq_coeff]
            simp only [smul_zero]
            rw [HahnSeries.leadingCoeff_pos_iff]
            simpa using hy0
      · intro horder
        have hxc0 : x.leadingCoeff ≠ 0 := leadingCoeff_ne_iff.mpr hx0
        have hyc0 : y.leadingCoeff ≠ 0 := leadingCoeff_ne_iff.mpr hy0
        obtain ⟨m, hm⟩ := Archimedean.arch |x.leadingCoeff| (show 0 < |y.leadingCoeff| by exact abs_pos.mpr hyc0)
        obtain ⟨n, hn⟩ := Archimedean.arch |y.leadingCoeff| (show 0 < |x.leadingCoeff| by exact abs_pos.mpr hxc0)
        refine ⟨⟨m + 1, by simp, ?_⟩, ⟨n + 1, by simp, ?_⟩⟩
        · apply le_of_lt
          use x.orderTop.untop (HahnSeries.ne_zero_iff_orderTop.mp hx0)
          constructor
          · simp only [Pi.toLex_apply, coeff_nsmul, Pi.smul_apply]
            intro j hj
            rw [HahnSeries.coeff_eq_zero_of_lt_orderTop (by
              rw [HahnSeries.abs_order]
              exact (WithTop.lt_untop_iff _).mp hj
            )]
            rw [HahnSeries.coeff_eq_zero_of_lt_orderTop (by
              rw [HahnSeries.abs_order]
              rw [← horder]
              exact (WithTop.lt_untop_iff _).mp hj
            )]
            simp
          · simp only [ne_eq, Pi.toLex_apply, coeff_nsmul, Pi.smul_apply]
            conv in x.orderTop =>
              rw [← HahnSeries.abs_order]
            conv in x.orderTop =>
              rw [horder, ← HahnSeries.abs_order]
            rw [← HahnSeries.leadingCoeff_eq_coeff]
            rw [← HahnSeries.leadingCoeff_eq_coeff]
            rw [HahnSeries.abs_leadingCoeff]
            rw [HahnSeries.abs_leadingCoeff]
            apply lt_of_le_of_lt hm
            rw [add_smul, one_smul]
            simp only [lt_add_iff_pos_right, abs_pos]
            exact HahnSeries.leadingCoeff_ne_iff.mpr hy0
        · apply le_of_lt
          use y.orderTop.untop (HahnSeries.ne_zero_iff_orderTop.mp hy0)
          constructor
          · simp only [Pi.toLex_apply, coeff_nsmul, Pi.smul_apply]
            intro j hj
            rw [HahnSeries.coeff_eq_zero_of_lt_orderTop (by
              rw [HahnSeries.abs_order]
              exact (WithTop.lt_untop_iff _).mp hj
            )]
            rw [HahnSeries.coeff_eq_zero_of_lt_orderTop (by
              rw [HahnSeries.abs_order]
              rw [horder]
              exact (WithTop.lt_untop_iff _).mp hj
            )]
            simp
          · simp only [ne_eq, Pi.toLex_apply, coeff_nsmul, Pi.smul_apply]
            conv in y.orderTop =>
              rw [← HahnSeries.abs_order]
            conv in y.orderTop =>
              rw [← horder, ← HahnSeries.abs_order]
            rw [← HahnSeries.leadingCoeff_eq_coeff]
            rw [← HahnSeries.leadingCoeff_eq_coeff]
            rw [HahnSeries.abs_leadingCoeff]
            rw [HahnSeries.abs_leadingCoeff]
            apply lt_of_le_of_lt hn
            rw [add_smul, one_smul]
            simp only [lt_add_iff_pos_right, abs_pos]
            exact HahnSeries.leadingCoeff_ne_iff.mpr hx0

noncomputable
def HahnSeries.embDomainAddMonoidHom {Γ : Type*} {Γ' : Type*} {R : Type*}
    [LinearOrder Γ] [AddMonoid R] [PartialOrder R] [LinearOrder Γ'] (f : Γ ↪o Γ') :
    HahnSeries Γ R →+o HahnSeries Γ' R where
  toFun := HahnSeries.embDomain f
  map_zero' := by
    apply HahnSeries.embDomain_zero
  map_add' := by
    intro a b
    apply HahnSeries.embDomain_add
  monotone' := by
    intro a b h
    obtain hlt|heq := lt_or_eq_of_le h
    · apply le_of_lt
      rw [HahnSeries.lt_iff] at hlt ⊢
      obtain ⟨i, hj, hi⟩ := hlt
      use f i
      constructor
      · intro j hji
        by_cases hjmem : j ∈ Set.range f
        · obtain ⟨j', hj'⟩ := hjmem
          rw [← hj'] at ⊢ hji
          simp only [embDomain_coeff]
          apply hj
          exact (OrderEmbedding.lt_iff_lt f).mp hji
        · rw [HahnSeries.embDomain_notin_range hjmem, HahnSeries.embDomain_notin_range hjmem]
      · simpa using hi
    · rw [heq]

theorem HahnSeries.embDomainAddMonoidHom_injective {Γ : Type*} {Γ' : Type*} {R : Type*}
    [LinearOrder Γ] [AddMonoid R] [PartialOrder R] [LinearOrder Γ'] (f : Γ ↪o Γ') :
    Function.Injective (HahnSeries.embDomainAddMonoidHom f (R := R)) := by
  apply HahnSeries.embDomain_injective


notation:50 " a⁰[" l:50 "] " => {A : archimedeanClass l // A ≠ 0}


variable {M: Type*}
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M] [DivisibleBy M ℕ]

variable (M) in
@[ext]
structure SubEmbedding where
  f : M →ₗ.[ℚ] HahnSeries (a⁰[M]) ℝ

  strictMono : StrictMono f

  hdomain : ∀ A : archimedeanClass M, A ≠ 0 → ∀ a ∈ archimedeanGrade A, a ∈ f.domain
  anchor : ∀ A : archimedeanClass M, (hA : A ≠ 0) → ∀ a : M, (ha : a ∈ archimedeanGrade A) →
    (f ⟨a, hdomain A hA a ha⟩) =
    HahnSeries.single ⟨A, hA⟩ (archimedeanGrade.embedReal_linear A ⟨a, ha⟩)

  range_cut : ∀ x ∈ Set.range f, ∀ c : (a⁰[M]),
    (HahnSeries.cut _ _ c) x ∈ Set.range f

noncomputable
def SubEmbedding.to_orderAddMonoidHom (e : SubEmbedding M) :
    e.f.domain →+o HahnSeries (a⁰[M]) ℝ where
  toFun := e.f
  map_zero' := by simp
  map_add' := by
    intro x y
    rw [← LinearPMap.map_add]
  monotone' := e.strictMono.monotone

theorem SubEmbedding.eq_orderAddMonoidHom {e : SubEmbedding M} (x : e.f.domain) :
    e.f x = e.to_orderAddMonoidHom x := by rfl

theorem SubEmbedding.orderTop_eq_class (e : SubEmbedding M) {x : M} (hx : x ∈ e.f.domain)
    (hx0 : archimedeanClass.mk x ≠ 0) :
    (e.f ⟨x, hx⟩).orderTop = WithTop.some (⟨archimedeanClass.mk x, hx0⟩) := by

  have : Nontrivial (archimedeanGrade (archimedeanClass.mk x)) :=
      archimedeanGrade.nontrivial_of_nonzero hx0
  obtain ⟨⟨x', hx'mem⟩, hx'0⟩ := exists_ne (0 : archimedeanGrade (archimedeanClass.mk x))
  have hmkeq: archimedeanClass.mk x' = archimedeanClass.mk x := by
    refine archimedeanGrade.mem_class_of_nonzero hx0 hx'mem ?_
    simpa using hx'0
  have hclasseq : archimedeanClass.mk (⟨x', e.hdomain _ hx0 _ hx'mem⟩ : e.f.domain)
      = archimedeanClass.mk ⟨x, hx⟩ := by
    rw [archimedeanClass.eq] at hmkeq ⊢
    exact hmkeq

  obtain h := (archimedeanClass.map_mk_eq (to_orderAddMonoidHom e) hclasseq).symm
  rw [← eq_orderAddMonoidHom, ← eq_orderAddMonoidHom] at h

  have hfx0 : e.f ⟨x, hx⟩ ≠ 0 := by
    have : (0 : HahnSeries { A: archimedeanClass M // A ≠ 0 } ℝ) = e.f 0 := by simp
    rw [this]
    apply e.strictMono.injective.ne_iff.mpr
    simpa using hx0

  rw [HahnSeries.archimedeanClass_eq_iff] at h

  have : (e.f ⟨x', e.hdomain _ hx0 _ hx'mem⟩).orderTop = WithTop.some ⟨archimedeanClass.mk x',
      hmkeq.symm ▸ hx0⟩ := by
    apply HahnSeries.orderTop_eq_of_le
    · simp only [ne_eq, HahnSeries.mem_support]
      rw [e.anchor (archimedeanClass.mk x') (hmkeq.symm ▸ hx0) x' (hmkeq.symm ▸ hx'mem)]
      simp only [HahnSeries.coeff_single_same]
      apply (LinearMap.map_eq_zero_iff _ (Archimedean.embedReal_injective _)).ne.mpr
      simpa using hx'0
    · intro g' hg
      contrapose! hg
      simp only [ne_eq, HahnSeries.mem_support, Decidable.not_not]
      rw [e.anchor (archimedeanClass.mk x') (hmkeq.symm ▸ hx0) x' (hmkeq.symm ▸ hx'mem)]
      apply HahnSeries.coeff_single_of_ne
      exact hg.ne
  rw [this] at h
  rw [h]
  simpa using hmkeq

theorem SubEmbedding.coeff_nonzero_at_class (e : SubEmbedding M) {x : M} (hx : x ∈ e.f.domain)
    (hx0 : archimedeanClass.mk x ≠ 0) :
    (e.f ⟨x, hx⟩).coeff ⟨archimedeanClass.mk x, hx0⟩ ≠ 0 := by
  apply HahnSeries.coeff_orderTop_ne
  rw [SubEmbedding.orderTop_eq_class e hx hx0]


theorem SubEmbedding.coeff_zero_of_class_gt (e : SubEmbedding M) {x : M} (hx : x ∈ e.f.domain)
    {A : archimedeanClass M} (hA : A < archimedeanClass.mk x) :
    (e.f ⟨x, hx⟩).coeff ⟨A, archimedeanClass.ne_zero_of_lt hA⟩ = 0 := by
  by_cases hx0 : x = 0
  · have : (⟨x, hx⟩ : e.f.domain) = 0 := by
      simp [hx0]
    rw [this]
    simp
  · have hx0' : archimedeanClass.mk x ≠ 0 := archimedeanClass.eq_zero_iff.ne.mpr hx0
    apply HahnSeries.coeff_eq_zero_of_lt_orderTop
    rw [SubEmbedding.orderTop_eq_class e hx hx0']
    simpa using hA

def SubEmbedding.nhds (e : SubEmbedding M) (x : M) (A : archimedeanClass M) : Set M :=
  {y : M | y ∈ e.f.domain ∧ A < archimedeanClass.mk (x - y)}

theorem SubEmbedding.nhds_anti (e : SubEmbedding M) (x : M) : Antitone (nhds e x) := by
  intro a b h
  unfold nhds
  simp only [Set.le_eq_subset, Set.setOf_subset_setOf, and_imp]
  intro u hu hv
  exact ⟨hu, lt_of_le_of_lt h hv⟩

theorem SubEmbedding.map_eq (e : SubEmbedding M) (x : M) {A B1 B2 : archimedeanClass M}
    (hA : A ≠ 0)
    (h1 : A ≤ B1) (h2 : A ≤ B2) {y1 y2 : M} (hy1 : y1 ∈ nhds e x B1) (hy2 : y2 ∈ nhds e x B2) :
    (e.f ⟨y1, hy1.1⟩).coeff ⟨A, hA⟩ =
    (e.f ⟨y2, hy2.1⟩).coeff ⟨A, hA⟩ := by

  apply eq_of_sub_eq_zero
  rw [← Pi.sub_apply, ← HahnSeries.coeff_sub', ← LinearPMap.map_sub]
  apply SubEmbedding.coeff_zero_of_class_gt
  simp only
  have : y1 - y2 = (x - y2) + (-(x - y1)) := by abel
  rw [this]
  refine lt_of_lt_of_le ?_ (archimedeanClass.min_le_mk_add _ _)
  rw [archimedeanClass.mk_neg]
  simp only [lt_inf_iff]
  constructor
  · apply lt_of_le_of_lt h2
    exact hy2.2
  · apply lt_of_le_of_lt h1
    exact hy1.2

open Classical in
noncomputable
def SubEmbedding.eval (e : SubEmbedding M) (x : M) : (a⁰[M]) → ℝ :=
  fun A ↦
    if h : (SubEmbedding.nhds e x A).Nonempty then
      (e.f ⟨h.choose, h.choose_spec.1⟩).coeff A
    else
      0

theorem SubEmbedding.eval_eq (e : SubEmbedding M) (x : M) {A B : archimedeanClass M}
    (hA : A ≠ 0)
    (hAB : A ≤ B) {y : M} (hy : y ∈ nhds e x B) :
    eval e x ⟨A, hA⟩ =
    (e.f ⟨y, hy.1⟩).coeff ⟨A, hA⟩ := by

  have hnonempty : (nhds e x A).Nonempty := by
    refine Set.Nonempty.mono ?_ (Set.nonempty_of_mem hy)
    exact nhds_anti _ _ hAB

  unfold eval
  simp only [hnonempty, ↓reduceDIte]
  symm
  apply map_eq _ _ hA hAB (le_refl A) hy (Exists.choose_spec _)


theorem SubEmbedding.eval_isWF_support (e : SubEmbedding M) (x : M) :
    (eval e x).support.IsWF := by
  rw [Set.isWF_iff_no_descending_seq]
  by_contra!
  obtain ⟨seq, ⟨hanti, hmem⟩⟩ := this

  have hnonempty : (nhds e x (seq 0).val).Nonempty := by
    obtain hmem := hmem 0
    contrapose hmem with hempty
    simp only [ne_eq, Function.mem_support, Decidable.not_not]
    unfold eval
    simp [hempty]
  obtain ⟨y, hy⟩ := hnonempty

  have hmem' : ∀ n : ℕ , seq n ∈ Function.support ((e.f ⟨y, hy.1⟩).coeff) := by
    intro n
    obtain hmem := hmem n
    simp only [Function.mem_support] at hmem ⊢
    convert hmem using 1
    symm
    apply SubEmbedding.eval_eq e x _ (le_refl _)
    apply Set.mem_of_mem_of_subset hy
    apply SubEmbedding.nhds_anti
    simp only [Subtype.coe_le_coe]
    apply hanti.le_iff_le.mpr
    simp

  obtain hwf := (e.f ⟨y, hy.1⟩).isWF_support
  contrapose! hwf
  rw [Set.isWF_iff_no_descending_seq]
  simp only [not_forall, ne_eq, Decidable.not_not, not_exists, exists_prop, Set.not_not_mem]
  use seq
  exact ⟨hanti, hmem'⟩

noncomputable
def SubEmbedding.eval_hahn (e : SubEmbedding M) (x : M) :
    HahnSeries (a⁰[M]) ℝ where
  coeff := SubEmbedding.eval e x
  isPWO_support' := (eval_isWF_support e x).isPWO

theorem SubEmbedding.eval_ne_of_not_mem (e : SubEmbedding M) {x : M} (hx : x ∉ e.f.domain)
    (z : e.f.domain) :
    e.eval_hahn x ≠ e.f z := by

  by_contra! h

  have h1 (y : e.f.domain) (hxy : x ≠ y.val) : archimedeanClass.mk (x - y.val) ≤
      archimedeanClass.mk (z.val - y.val) := by

    have (A : (a⁰[M]))
      (hA : A.val < archimedeanClass.mk (x - y.val))  :
      (e.eval_hahn x).coeff A = (e.f y).coeff A := by
      apply SubEmbedding.eval_eq e x _ (le_refl _)
      unfold nhds
      simpa using hA

    conv at this =>
      intro A hA
      rw [h]
      rw [← sub_eq_zero]
      rw [← HahnSeries.coeff_sub]
      rw [← LinearPMap.map_sub]

    have hxy' : archimedeanClass.mk (x - y.val) ≠ 0 := by
      apply archimedeanClass.eq_zero_iff.ne.mpr
      exact sub_ne_zero_of_ne hxy

    have : WithTop.some (⟨archimedeanClass.mk (x - y.val), hxy'⟩ : (a⁰[M])) ≤
        (e.f (z - y)).orderTop := by
      contrapose! this
      have hsome : (e.f (z - y)).orderTop ≠ ⊤ := LT.lt.ne_top this
      rw [WithTop.ne_top_iff_exists] at hsome
      obtain ⟨order, horder⟩ := hsome
      use order
      constructor
      · rw [← horder] at this
        simpa using this
      · apply HahnSeries.coeff_orderTop_ne
        exact horder.symm

    by_cases hyz0 : archimedeanClass.mk (z - y).val = 0
    · simp only [ne_eq, AddSubgroupClass.coe_sub] at hyz0
      rw [hyz0]
      apply archimedeanClass.nonpos
    · rw [SubEmbedding.orderTop_eq_class e _ hyz0] at this
      simpa using this

  have h2 (y : e.f.domain) (hxy : x ≠ y.val) : archimedeanClass.mk (x - y.val) ≤
      archimedeanClass.mk (x - z.val) := by
    have : x - z.val = x - y.val + -(z.val - y.val) := by abel
    rw [this]
    refine le_trans ?_ (archimedeanClass.min_le_mk_add _ _)
    rw [archimedeanClass.mk_neg]
    simpa using h1 y hxy

  have h3 (y : e.f.domain) : archimedeanClass.mk (x - y.val) ≤
      archimedeanClass.mk (x - z.val) := by
    apply h2
    contrapose! hx
    rw [hx]
    simp

  have hxz0 : archimedeanClass.mk (x - z.val) ≠ 0 := by
    contrapose! hx with h0
    obtain h0' := archimedeanClass.eq_zero_iff.mp h0
    have : x = z.val := sub_eq_zero.mp h0'
    rw [this]
    simp

  obtain ⟨⟨v, xz'⟩, ⟨hv, hxz', hvxz⟩, _⟩  := archimedeanGrade.exists_add hxz0 (
    show x - z ∈ archimedeanSubgroup.toSubmodule (UpperSet.Ici (archimedeanClass.mk (x - z.val))) by
      rw [archimedeanSubgroup.mem_submodule_iff_mem]
      rw [archimedeanSubgroup.mem_iff]
      simp only [UpperSet.mem_Ici_iff, le_refl]
      -- For some reason the following below didn't get simp
      rw [UpperSet.carrier_eq_coe, UpperSet.coe_Ici]
      apply Set.nonempty_Ici
  )

  rw [archimedeanSubgroup.mem_submodule_iff_mem, archimedeanSubgroup.mem_iff (
    archimedeanClass.Ioi_nonempty hxz0)] at hv

  simp only [UpperSet.mem_Ioi_iff] at hv hxz'
  simp only at hvxz

  have hxzmem : z.val + xz' ∈ e.f.domain := by
    apply Submodule.add_mem
    · simp
    · exact e.hdomain _ hxz0 _ hxz'

  by_cases hv0 : archimedeanClass.mk v = 0
  · have hv0' : v = 0 := archimedeanClass.eq_zero_iff.mp hv0
    rw [hv0'] at hvxz
    simp only [zero_add] at hvxz
    obtain hvxz' := sub_eq_iff_eq_add'.mp hvxz.symm
    contrapose! hx
    rw [hvxz']
    exact hxzmem
  · have : Nontrivial (archimedeanGrade (archimedeanClass.mk v)) := by
      apply archimedeanGrade.nontrivial_of_nonzero
      exact hv0
    obtain ⟨⟨v', hvmem'⟩, hv'⟩ := exists_ne (0 : archimedeanGrade (archimedeanClass.mk v))
    have hv0' : v' ≠ 0 := Subtype.eq_iff.ne.mp hv'
    obtain hvmk' := archimedeanGrade.mem_class_of_nonzero hv0 hvmem' hv0'
    have : ∃ y ∈ e.f.domain, archimedeanClass.mk (x - y) = archimedeanClass.mk v'  := by
      use z.val + xz'
      constructor
      · exact hxzmem
      · rw [hvmk']
        congr 1
        rw [← sub_sub]
        rw [← hvxz]
        simp
    obtain ⟨y, hymem, hy⟩ := this
    obtain hwhat := h3 ⟨y, hymem⟩
    rw [hy] at hwhat
    rw [hvmk'] at hwhat
    obtain hwhat' := hwhat.trans_lt hv
    simp at hwhat'

theorem SubEmbedding.eval_lt (e : SubEmbedding M) {x : M} (hx : x ∉ e.f.domain)
    (y : e.f.domain) (h : x < y.val) :
    e.eval_hahn x < e.f y := by
  unfold eval_hahn
  rw [HahnSeries.lt_iff]
  simp only

  have h0 : archimedeanClass.mk (x - y.val) ≠ 0 :=
    archimedeanClass.eq_zero_iff.ne.mpr <| sub_ne_zero_of_ne h.ne

  use ⟨archimedeanClass.mk (x - y.val), h0⟩
  constructor
  · intro j hj
    have hy : y.val ∈ e.nhds x j.val := by
      unfold nhds
      simpa using hj
    rw [SubEmbedding.eval_eq e x j.prop (le_refl _) hy]
  · have hnonempty : (e.nhds x (archimedeanClass.mk (x - y.val))).Nonempty := by
      by_contra! hempty
      have : e.eval_hahn x = (HahnSeries.cut _ _ ⟨archimedeanClass.mk (x - y.val), h0⟩) (e.f y) := by
        ext i
        unfold HahnSeries.cut HahnSeries.cut_fun
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        split_ifs with hi
        · have hempty': ¬ (e.nhds x i.val).Nonempty := by
            contrapose! hempty
            refine Set.Nonempty.mono ?_ hempty
            apply SubEmbedding.nhds_anti
            simpa using hi
          unfold eval_hahn eval
          simp [hempty']
        · simp only [ne_eq, not_le] at hi
          unfold eval_hahn
          apply eval_eq e x _ (le_refl _)
          unfold nhds
          simpa using hi
      obtain hmem := e.range_cut (e.f y) (by simp) ⟨archimedeanClass.mk (x - y.val), h0⟩
      rw [← this] at hmem
      simp only [Set.mem_range] at hmem
      obtain ⟨z, hz⟩ := hmem
      obtain hzwhat := SubEmbedding.eval_ne_of_not_mem e hx z
      rw [hz] at hzwhat
      simp at hzwhat
    obtain ⟨z, hz⟩ := hnonempty
    rw [SubEmbedding.eval_eq e x h0 (le_refl _) hz]

    unfold nhds at hz
    simp only [Set.mem_setOf_eq] at hz

    have hzyclass : archimedeanClass.mk (z - y.val) = archimedeanClass.mk (x - y.val) := by
      symm
      have : z - y.val = x - y.val + (z - x) := by abel
      rw [this]
      apply archimedeanClass.mk_eq_mk_self_add_of_mk_lt
      rw [← archimedeanClass.mk_neg (z - x), neg_sub]
      exact hz.2

    have hzy0 : archimedeanClass.mk (z - y.val) ≠ 0 := hzyclass.symm ▸ h0

    have hzy : ⟨z, hz.1⟩ < y := by
      show z < y.val
      apply (sub_lt_sub_iff_right x).mp
      refine archimedeanClass.lt_of_mk_lt_mk ?_ (sub_nonneg_of_le h.le)
      rw [← archimedeanClass.mk_neg (z - x), neg_sub]
      rw [← archimedeanClass.mk_neg (y.val - x), neg_sub]
      exact hz.2

    have hzy := e.strictMono.lt_iff_lt.mpr hzy


    rw [HahnSeries.lt_iff] at hzy
    obtain ⟨i, hj, hi⟩ := hzy
    have hieq : i = ⟨archimedeanClass.mk (x - y.val), h0⟩ := by
      apply le_antisymm
      · by_contra! hlt
        obtain hj := hj ⟨archimedeanClass.mk (x - y.val), h0⟩ hlt
        obtain hj := sub_eq_zero_of_eq hj
        rw [← HahnSeries.coeff_sub, ← LinearPMap.map_sub] at hj
        simp_rw [← hzyclass] at hj
        contrapose! hj
        apply SubEmbedding.coeff_nonzero_at_class
      · contrapose! hi
        apply le_of_eq
        simp_rw [← hzyclass] at hi
        apply eq_of_sub_eq_zero
        rw [← HahnSeries.coeff_sub, ← LinearPMap.map_sub]
        apply coeff_zero_of_class_gt
        rw [← archimedeanClass.mk_neg, neg_sub]
        exact hi
    rw [hieq] at hi
    exact hi

/-- Ehhh -/
theorem SubEmbedding.lt_eval (e : SubEmbedding M) {x : M} (hx : x ∉ e.f.domain)
    (y : e.f.domain) (h : y.val < x) :
    e.f y < e.eval_hahn x := by
  unfold eval_hahn
  rw [HahnSeries.lt_iff]
  simp only

  have h0 : archimedeanClass.mk (x - y.val) ≠ 0 :=
    archimedeanClass.eq_zero_iff.ne.mpr <| sub_ne_zero_of_ne h.ne.symm

  have h0' := h0
  rw [← archimedeanClass.mk_neg, neg_sub] at h0'

  use ⟨archimedeanClass.mk (y.val - x), h0'⟩
  constructor
  · intro j hj
    have hy : y.val ∈ e.nhds x j.val := by
      unfold nhds
      simp only [ne_eq, Set.mem_setOf_eq, SetLike.coe_mem, true_and]
      rw [← archimedeanClass.mk_neg, neg_sub]
      exact hj
    rw [SubEmbedding.eval_eq e x j.prop (le_refl _) hy]
  · have hnonempty : (e.nhds x (archimedeanClass.mk (x - y.val))).Nonempty := by
      by_contra! hempty
      have : e.eval_hahn x = (HahnSeries.cut _ _ ⟨archimedeanClass.mk (x - y.val), h0⟩) (e.f y) := by
        ext i
        unfold HahnSeries.cut HahnSeries.cut_fun
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        split_ifs with hi
        · have hempty': ¬ (e.nhds x i.val).Nonempty := by
            contrapose! hempty
            refine Set.Nonempty.mono ?_ hempty
            apply SubEmbedding.nhds_anti
            simpa using hi
          unfold eval_hahn eval
          simp [hempty']
        · simp only [ne_eq, not_le] at hi
          unfold eval_hahn
          apply eval_eq e x _ (le_refl _)
          unfold nhds
          simpa using hi
      obtain hmem := e.range_cut (e.f y) (by simp) ⟨archimedeanClass.mk (x - y.val), h0⟩
      rw [← this] at hmem
      simp only [Set.mem_range] at hmem
      obtain ⟨z, hz⟩ := hmem
      obtain hzwhat := SubEmbedding.eval_ne_of_not_mem e hx z
      rw [hz] at hzwhat
      simp at hzwhat
    obtain ⟨z, hz⟩ := hnonempty
    obtain hrw := SubEmbedding.eval_eq e x h0' (
      show archimedeanClass.mk (y.val - x) ≤ archimedeanClass.mk (x - y.val) by
        rw [← archimedeanClass.mk_neg, neg_sub]
      ) hz
    rw [← archimedeanClass.mk_neg, neg_sub] at hz
    rw [hrw]

    unfold nhds at hz
    simp only [Set.mem_setOf_eq] at hz
    nth_rw 2 [← archimedeanClass.mk_neg] at hz
    rw [neg_sub] at hz


    have hzyclass : archimedeanClass.mk (y.val - z) = archimedeanClass.mk (y.val - x) := by
      symm
      have : y.val - z = y.val - x + (x - z) := by abel
      rw [this]
      apply archimedeanClass.mk_eq_mk_self_add_of_mk_lt
      rw [← archimedeanClass.mk_neg (x - z), neg_sub]
      exact hz.2

    have hzy0 : archimedeanClass.mk (y.val - z) ≠ 0 := hzyclass.symm ▸ h0'

    have hzy : y < ⟨z, hz.1⟩ := by
      show y.val < z
      apply (sub_lt_sub_iff_right x).mp
      refine archimedeanClass.lt_of_mk_lt_mk' ?_ (sub_nonpos_of_le h.le)
      exact hz.2

    have hzy := e.strictMono.lt_iff_lt.mpr hzy

    rw [HahnSeries.lt_iff] at hzy
    obtain ⟨i, hj, hi⟩ := hzy
    have hieq : i = ⟨archimedeanClass.mk (y.val - x), h0'⟩ := by
      apply le_antisymm
      · by_contra! hlt
        obtain hj := hj ⟨archimedeanClass.mk (y.val - x), h0'⟩ hlt
        obtain hj := sub_eq_zero_of_eq hj
        rw [← HahnSeries.coeff_sub, ← LinearPMap.map_sub] at hj
        simp_rw [← hzyclass] at hj
        contrapose! hj
        apply SubEmbedding.coeff_nonzero_at_class
      · contrapose! hi
        apply le_of_eq
        simp_rw [← hzyclass] at hi
        apply eq_of_sub_eq_zero
        rw [← HahnSeries.coeff_sub, ← LinearPMap.map_sub]
        apply coeff_zero_of_class_gt
        rw [← archimedeanClass.mk_neg, neg_sub]
        exact hi
    rw [hieq] at hi
    exact hi

noncomputable
abbrev SubEmbedding.ext_fun (e : SubEmbedding M) {x : M} (hx : x ∉ e.f.domain) :
    M →ₗ.[ℚ] HahnSeries (a⁰[M]) ℝ :=
  LinearPMap.supSpanSingleton e.f x (SubEmbedding.eval_hahn e x) hx


/-- TODO: generalize this-/
instance (Γ : Type*) [LinearOrder Γ] : OrderedSMul ℚ (HahnSeries Γ ℝ) := OrderedSMul.mk' (by
  intro a b c hab hc
  apply le_of_lt
  rw [HahnSeries.lt_iff] at ⊢ hab
  obtain ⟨i, hj, hi⟩ := hab
  use i
  constructor
  · intro j hji
    obtain hj := hj j hji
    rw [HahnSeries.coeff_smul, HahnSeries.coeff_smul]
    rw [hj]
  · rw [HahnSeries.coeff_smul, HahnSeries.coeff_smul]
    exact smul_lt_smul_of_pos_left hi hc

)

instance : OrderedSMul ℚ M := OrderedSMul.mk' (by
  intro a b c hab hc
  rw [DivisibleBy.rat_smul_eq, DivisibleBy.rat_smul_eq]
  apply (nsmul_le_nsmul_iff_left' (show c.den ≠ 0 by simp)).mp
  rw [DivisibleBy.div_cancel _ (by simp), DivisibleBy.div_cancel _ (by simp)]
  apply zsmul_le_zsmul_right
  · apply le_of_lt
    exact Rat.num_pos.mpr hc
  · exact hab.le

)

theorem SubEmbedding.ext_fun_strictMono (e : SubEmbedding M) {x : M} (hx : x ∉ e.f.domain) :
    StrictMono (ext_fun e hx) := by

  intro z y hxy
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hxy := sub_pos.mpr hxy
  obtain hxymem := (y - z).prop
  nth_rw 1 [LinearPMap.domain_supSpanSingleton] at hxymem
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxymem
  have : y - z = ⟨a + b, hab.symm ▸ (y - z).prop⟩ := by simp_rw [hab]
  rw [this] at ⊢ hxy

  have habpos : 0 < a + b := by exact hxy

  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
  simp_rw [← hc]
  rw [← hc] at habpos
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ hx _ ha]

  rw [← sub_neg_eq_add, ← neg_smul, sub_pos] at habpos ⊢
  by_cases hc0 : c = 0
  · rw [hc0] at habpos ⊢
    simp only [zero_smul, ne_eq, neg_zero] at habpos ⊢
    have : 0 = e.f 0 := by simp
    rw [this]
    apply e.strictMono
    simpa using habpos
  · have : a = (-c) • ((-c)⁻¹ • a) := by
      rw [smul_smul]
      rw [mul_inv_cancel₀ (neg_ne_zero.mpr hc0)]
      simp
    rw [this] at habpos
    have : e.f ⟨a, ha⟩ = (-c) • ((-c)⁻¹ • e.f ⟨a, ha⟩) := by
      rw [smul_smul]
      rw [mul_inv_cancel₀ (neg_ne_zero.mpr hc0)]
      simp
    rw [this, ← LinearPMap.map_smul]

    have : (-c)⁻¹ • (⟨a, ha⟩ : e.f.domain) = ⟨(-c)⁻¹ • a,
      Submodule.smul_mem e.f.domain (-c)⁻¹ ha⟩ := rfl
    rw [this]

    obtain hcneg|hcpos := lt_or_gt_of_ne hc0
    · have : 0 < -c := Left.neg_pos_iff.mpr hcneg
      refine smul_lt_smul_of_pos_left ?_ this
      obtain h := lt_of_smul_lt_smul_left habpos this.le
      apply SubEmbedding.eval_lt e hx
      exact h
    · have : -c < 0 := neg_neg_iff_pos.mpr hcpos
      refine smul_lt_smul_of_neg_left ?_ this
      obtain h := lt_of_smul_lt_smul_of_nonpos habpos this.le
      apply SubEmbedding.lt_eval e hx
      exact h


noncomputable
def SubEmbedding.extend (e : SubEmbedding M) {x : M} (hx : x ∉ e.f.domain) : SubEmbedding M where
  f := ext_fun e hx
  strictMono := ext_fun_strictMono e hx

  hdomain := by
    intro A hA a ha
    apply Submodule.mem_sup_left
    exact e.hdomain A hA a ha
  anchor := by
    intro A hA a ha
    rw [LinearPMap.supSpanSingleton_apply_mk_of_mem _ _ hx (e.hdomain A hA a ha)]
    exact e.anchor A hA a ha

  range_cut := by
    intro a ha c
    simp only [Set.mem_range] at ha
    obtain ⟨⟨a', ha'mem⟩, ha'⟩ := ha
    simp only [LinearPMap.domain_supSpanSingleton] at ha'mem
    obtain ⟨b, hbmem, hc, hcmem, hbc⟩ := Submodule.mem_sup.mp ha'mem
    obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hcmem
    rw [← hk] at hbc
    simp_rw [← hbc] at ha'
    unfold ext_fun at ha'
    rw [LinearPMap.supSpanSingleton_apply_mk e.f x _ hx b hbmem k] at ha'
    simp only [Set.mem_range]
    rw [← ha']

    rw [map_add]

    -- ehh
    have smul_change (s : HahnSeries (a⁰[M]) ℝ) : k • s = (k : ℝ) • s := by
      exact rfl
    rw [smul_change]
    rw [map_smul]
    rw [← smul_change]

    by_cases hnonempty : (e.nhds x c.val).Nonempty
    · obtain ⟨x', hx'⟩ := hnonempty

      have heq' : (HahnSeries.cut { A // A ≠ 0 } ℝ c) (e.eval_hahn x)
          = (HahnSeries.cut { A // A ≠ 0 } ℝ c) (e.f ⟨x', hx'.1⟩) := by
        ext i
        unfold eval_hahn HahnSeries.cut HahnSeries.cut_fun
        simp only [ne_eq, LinearMap.coe_mk, AddHom.coe_mk]
        split_ifs with hi
        · simp
        · apply eval_eq e x i.prop (show i.val ≤ c.val by apply le_of_lt; simpa using hi) hx'

      rw [heq']

      rw [smul_change]
      rw [← map_smul]
      rw [← smul_change]

      rw [← map_add]
      obtain h := e.range_cut (e.f ⟨b, hbmem⟩ + k • e.f ⟨x', hx'.1⟩) (by
        simp only [Set.mem_range]
        use ⟨b, hbmem⟩ + k • ⟨x', hx'.1⟩
        rw [LinearPMap.map_add, LinearPMap.map_smul]
        ) c
      simp only [Set.mem_range] at h
      obtain ⟨y, hy⟩ := h
      use ⟨y.val, Submodule.mem_sup_left y.prop⟩
      rw [LinearPMap.supSpanSingleton_apply_of_mem _ _ hx _  y.prop]
      simpa using hy
    · obtain ⟨b', hb'⟩ := e.range_cut (e.f ⟨b, hbmem⟩) (by simp) c

      have heq : (HahnSeries.cut { A // A ≠ 0 } ℝ c) (e.eval_hahn x) = e.eval_hahn x := by
        unfold HahnSeries.cut HahnSeries.cut_fun
        ext i
        simp only [ne_eq, LinearMap.coe_mk, AddHom.coe_mk, ite_eq_right_iff]
        intro hci
        have hempty : ¬ (e.nhds x i.val).Nonempty := by
          contrapose! hnonempty
          refine Set.Nonempty.mono ?_ hnonempty
          apply nhds_anti
          simpa using hci
        unfold eval_hahn eval
        simp [hempty]
      rw [heq]
      use ⟨b'.val + k • x, by
        apply Submodule.add_mem
        · apply Submodule.mem_sup_left
          simp
        · apply Submodule.smul_mem
          apply Submodule.mem_sup_right
          simp
      ⟩
      rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ hx _ b'.prop]
      simpa using hb'


variable (M) in
noncomputable
instance SubEmbedding.le : PartialOrder (SubEmbedding M) := {
  (PartialOrder.lift (fun e ↦ e.f) (by
    intro a b h
    ext1
    exact h
  )) with
}

noncomputable
abbrev grade_embed (A : (a⁰[M])) :
  M →ₗ.[ℚ] HahnSeries (a⁰[M]) ℝ where
  domain := archimedeanGrade A
  toFun := (HahnSeries.single.linearMap A).comp (archimedeanGrade.embedReal_linear A.val)

variable (M) in
theorem grade_iSupIndep :
    iSupIndep fun i ↦ (grade_embed (M := M) i).domain := by
  rw [iSupIndep_def]
  intro ⟨A, hA⟩
  unfold grade_embed
  simp only
  rw [Submodule.disjoint_def']
  intro a ha b hb hab
  by_cases hb0 : b = 0
  · exact hb0 ▸ hab
  · contrapose! hab
    suffices archimedeanClass.mk a ≠ archimedeanClass.mk b by
      exact fun x ↦ this (congrArg archimedeanClass.mk x)
    obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp _ b).mp hb
    simp only [ne_eq, DFinsupp.lsum_apply_apply] at hf
    rw [DFinsupp.sumAddHom_apply] at hf
    simp only [LinearMap.toAddMonoidHom_coe, Submodule.coe_subtype, ZeroMemClass.coe_zero,
      implies_true] at hf
    rw [DFinsupp.sum] at hf
    have hnonempty : f.support.Nonempty := by
      contrapose! hb0
      rw [← hf]
      simp only [ne_eq, Finset.not_nonempty_iff_eq_empty, DFinsupp.support_eq_empty] at hb0
      rw [hb0]
      simp
    rw [← hf]

    have hfA : f ⟨A, hA⟩ = 0 := by
      apply Submodule.coe_eq_zero.mp
      apply (Submodule.mem_bot ℚ).mp
      convert (f ⟨A, hA⟩).prop
      simp

    rw [archimedeanClass.mk_sum hnonempty (by
      apply StrictMonoOn.congr
        ((Subtype.strictMono_coe {A : archimedeanClass M | A ≠ 0}).strictMonoOn _)
      intro A' hA'
      symm
      refine archimedeanGrade.mem_class_of_nonzero A'.prop ?_ (by simpa using hA')
      convert (f A').prop
      have hne : A' ≠ ⟨A, hA⟩ := by
        contrapose! hA'
        rw [hA']
        simpa using hfA
      simp [hne]
    )]

    obtain hmem := Finset.min'_mem f.support hnonempty

    have hminne : f.support.min' hnonempty ≠ ⟨A, hA⟩ := by
      by_contra!
      rw [this] at hmem
      simp only [DFinsupp.mem_support_toFun] at hmem
      contrapose! hmem
      exact hfA

    rw [archimedeanGrade.mem_class_of_nonzero hA ha hab]
    rw [archimedeanGrade.mem_class_of_nonzero
      ((f.support.min' hnonempty).prop)
      (by
        obtain h := (f (f.support.min' _)).prop
        convert h
        simp [hminne]
      ) (by
        rw [Submodule.coe_eq_zero.ne]
        apply DFinsupp.mem_support_iff.mp
        apply Finset.min'_mem _ hnonempty
      )]

    contrapose! hmem with heq
    have heq' : ⟨A, hA⟩ = f.support.min' hnonempty := Subtype.eq heq
    rw [← heq']
    simpa using hfA

variable (M) in
noncomputable
abbrev principal_map := LinearPMap.iSup (p := grade_embed) (grade_iSupIndep M)

theorem principal_map_apply {x : (⨆ (A : (a⁰[M])), archimedeanGrade A.val : Submodule ℚ M)}
    {f : Π₀ (A : (a⁰[M])), archimedeanGrade A.val}
    (hx : x.val = ((DFinsupp.lsum ℕ) fun (A : (a⁰[M])) ↦ (archimedeanGrade A.val).subtype) f) :
    (principal_map M x).coeff = fun (A : (a⁰[M])) ↦ (archimedeanGrade.embedReal_linear A.val (f A)) := by


  rw [LinearPMap.iSup_apply (grade_iSupIndep M) hx]
  ext A
  simp only [ne_eq, DFinsupp.lsum_apply_apply]
  rw [DFinsupp.sumAddHom_apply]
  unfold DFinsupp.sum
  rw [HahnSeries.coeff_sum]

  have h : f A = 0 → 0 = (archimedeanGrade.embedReal_linear A.val) (f A ) := by
    intro h
    rw [h]
    simp

  simpa using h


theorem principal_cut_range {s : HahnSeries (a⁰[M]) ℝ}
    (hs : s ∈ Set.range (principal_map M)) (c : (a⁰[M])) :
    (HahnSeries.cut _ ℝ c) s ∈ Set.range (principal_map M) := by
  obtain ⟨a, ha⟩ := hs
  let f := (combine_equiv (grade_iSupIndep M)).symm a
  have hf : a = (combine_equiv (grade_iSupIndep M)) f := by
    unfold f
    simp

  let cf' : Π₀ (i : { A // A ≠ 0 }), ((grade_embed i).domain : Submodule ℚ M) :=
    DFinsupp.mk f.support fun A ↦ if c ≤ A then 0 else f A

  use (combine_equiv (grade_iSupIndep M)) cf'

  ext A
  rw [principal_map_apply rfl]
  unfold HahnSeries.cut HahnSeries.cut_fun cf'
  simp only [ne_eq, Finset.coe_sort_coe, DFinsupp.mk_apply, DFinsupp.mem_support_toFun, dite_not,
    LinearMap.coe_mk, AddHom.coe_mk]

  split_ifs with h1 h2
  · simp
  · rw [← ha, hf]
    rw [principal_map_apply rfl]
    simp only [map_zero, ne_eq]
    rw [h1]
    simp
  · simp
  · rw [← ha, hf]
    rw [principal_map_apply rfl]

variable (M) in
theorem principal_strictMono : StrictMono (principal_map M) := by
  intro a b h
  rw [← sub_pos] at h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  set s := b - a
  let f := (combine_equiv (grade_iSupIndep M)).symm s
  have hf : s = (combine_equiv (grade_iSupIndep M)) f := by
    unfold f
    simp
  rw [hf]
  rw [HahnSeries.lt_iff]
  use ⟨archimedeanClass.mk s.val, by
    apply archimedeanClass.eq_zero_iff.ne.mpr
    apply ne_of_gt
    simpa using h
  ⟩

  unfold combine_equiv combine at hf
  rw [Subtype.eq_iff] at hf
  simp only [ne_eq, DFinsupp.lsum_apply_apply, LinearEquiv.ofBijective_apply, LinearMap.coe_mk,
    AddHom.coe_mk] at hf
  rw [DFinsupp.sumAddHom_apply] at hf
  unfold DFinsupp.sum at hf
  simp only [LinearMap.toAddMonoidHom_coe, Submodule.subtype_apply] at hf

  have hnonempty : f.support.Nonempty := by
    contrapose! h
    simp only [ne_eq, Finset.not_nonempty_iff_eq_empty, DFinsupp.support_eq_empty] at h
    apply le_of_eq
    rw [Subtype.eq_iff]
    rw [hf, h]
    simp

  have hmono : StrictMonoOn (fun x ↦ archimedeanClass.mk (f x).val) f.support := by
    apply StrictMonoOn.congr
      ((Subtype.strictMono_coe {A : archimedeanClass M | A ≠ 0}).strictMonoOn _)
    intro A hA
    symm
    apply archimedeanGrade.mem_class_of_nonzero A.prop (f A).prop (by simpa using hA)

  have hmk : archimedeanClass.mk s.val =
      archimedeanClass.mk (f (f.support.min' hnonempty)).val := by
    rw [hf]

    exact archimedeanClass.mk_sum hnonempty hmono

  have hmkf (A : a⁰[M]) (hsupport : A ∈ f.support) : archimedeanClass.mk (f A).val = A.val := by
    apply archimedeanGrade.mem_class_of_nonzero
    · exact A.prop
    · simp
    · rw [Submodule.coe_eq_zero.ne]
      rw [← DFinsupp.mem_support_iff]
      exact hsupport

  have hmk' : archimedeanClass.mk (f (f.support.min' hnonempty)).val =
      (f.support.min' hnonempty).val := by
    apply hmkf
    apply Finset.min'_mem

  constructor
  · intro j hj
    rw [principal_map_apply rfl]
    simp only [ne_eq, HahnSeries.coeff_zero]
    symm
    convert LinearMap.map_zero _
    contrapose! hj
    simp_rw [hmk, hmk']
    simp only [Subtype.coe_eta]
    apply Finset.min'_le
    simpa using hj
  · rw [principal_map_apply rfl]
    simp only [ne_eq, HahnSeries.coeff_zero, id_eq]
    have : 0 = (archimedeanGrade.embedReal_linear (archimedeanClass.mk s.val)) 0 := by simp
    rw [this]
    rw [archimedeanGrade.embedReal_linear_eq_orderEmbedding,
      archimedeanGrade.embedReal_linear_eq_orderEmbedding]
    apply (OrderEmbedding.strictMono _)

    have hclass {h : archimedeanClass.mk s.val ≠ 0} :
        archimedeanClass.mk s.val <
        archimedeanClass.mk ((f ⟨archimedeanClass.mk s.val, h⟩).val - s.val) := by
      rw [archimedeanClass.mk_sub_comm]
      nth_rw 1 [hf]
      nth_rw 1 [hf]
      have : ∑ x ∈ f.support, (f x).val - (f ⟨archimedeanClass.mk s.val, h⟩).val
          = ∑ x ∈ (f.support.erase ⟨archimedeanClass.mk s.val, h⟩), (f x).val := by
        apply sub_eq_of_eq_add
        symm
        apply Finset.sum_erase_add
        convert f.support.min'_mem hnonempty
        rw [hmk, hmk']

      rw [this]


      by_cases h0 : ∑ x ∈ (f.support.erase ⟨archimedeanClass.mk s.val, h⟩), (f x).val = 0
      · rw [h0]
        apply lt_of_le_of_ne (archimedeanClass.nonpos _)
        rw [← hf]
        exact h
      · have hnonempty' : (f.support.erase ⟨archimedeanClass.mk s.val, h⟩).Nonempty := by
          contrapose! h0
          simp only [ne_eq, Finset.not_nonempty_iff_eq_empty] at h0
          rw [h0]
          simp

        rw [archimedeanClass.mk_sum hnonempty hmono]
        rw [archimedeanClass.mk_sum hnonempty' (hmono.mono (by simp))]
        rw [hmk']
        rw [hmkf _ (
          Finset.mem_of_subset (Finset.erase_subset _ _) (Finset.min'_mem _ _))]
        rw [Subtype.coe_lt_coe]
        apply lt_of_le_of_ne
        · apply Finset.min'_le
          exact Finset.mem_of_subset (Finset.erase_subset _ _) (Finset.min'_mem _ _)
        · obtain hmem := Finset.min'_mem _ hnonempty'
          contrapose! hmem with heq
          rw [← heq]
          convert Finset.not_mem_erase (f.support.min' hnonempty) _
          rw [hmk, hmk']

    rw [← Subtype.coe_lt_coe] at ⊢ h
    simp only [ZeroMemClass.coe_zero] at ⊢ h
    exact archimedeanClass.pos_of_pos_of_mk_lt h hclass



variable (M) in
noncomputable
def SubEmbedding.principal : SubEmbedding M where
  f := principal_map M

  strictMono := principal_strictMono M

  hdomain := by
    intro A hA a ha
    apply Set.mem_of_mem_of_subset ha
    simp only [SetLike.coe_subset_coe]
    exact LinearPMap.le_iSup (grade_iSupIndep M) ⟨A, hA⟩

  anchor := by
    intro A hA a ha
    have ha' : a ∈ (grade_embed ⟨A, hA⟩).domain := ha
    rw [LinearPMap.iSup_apply_i (grade_iSupIndep M) ha']
    rfl

  range_cut := by
    intro ⟨a, ha⟩ h c
    apply principal_cut_range h


variable (M) in
instance SubEmbedding.nonempty : Nonempty (SubEmbedding M) :=
  Nonempty.intro (SubEmbedding.principal M)

variable (M) in
theorem SubEmbedding.exists_maximal :
    ∃ (e : SubEmbedding M), IsMax e := by
  apply zorn_le_nonempty
  intro s hchain hnonempty

  have hchain' : IsChain (· ≤ ·) ((fun e ↦ e.f) '' s) := by
    refine IsChain.image _ _ _ ?_ hchain
    intro x y hxy
    exact hxy

  have hchain'' : IsChain (· ≤ ·) (LinearPMap.domain '' ((fun e ↦ e.f) '' s)) := by
    refine IsChain.image _ _ _ ?_ hchain'
    intro x y hxy
    exact hxy.1

  use {
    f := LinearPMap.sSup ((fun e ↦ e.f) '' s) hchain'.directedOn
    strictMono := by
      intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      unfold LinearPMap.sSup at ha hb
      simp only at ha hb
      rw [Submodule.mem_sSup_of_directed ((hnonempty.image _).image _)
        hchain''.directedOn] at ha hb
      obtain ⟨a', ha'mem, ha'⟩ := ha
      obtain ⟨b', hb'mem, hb'⟩ := hb
      simp only [ne_eq, Set.mem_image, exists_exists_and_eq_and] at ha'mem hb'mem
      obtain ⟨a'', ha''mem, ha''⟩ := ha'mem
      obtain ⟨b'', hb''mem, hb''⟩ := hb'mem
      rw [← ha''] at ha'
      rw [← hb''] at hb'

      rw [LinearPMap.sSup_apply hchain'.directedOn (by use a'') ⟨a, ha'⟩]
      rw [LinearPMap.sSup_apply hchain'.directedOn (by use b'') ⟨b, hb'⟩]
      obtain hle|hle := hchain.total ha''mem hb''mem
      · have hle' : a''.f.domain ≤ b''.f.domain := hle.1
        have heq : a''.f ⟨a, ha'⟩ = b''.f ⟨a, Set.mem_of_mem_of_subset ha' hle'⟩ := by
          apply hle.2
          simp
        rw [heq]
        apply b''.strictMono
        simpa using hab
      · have hle' : b''.f.domain ≤ a''.f.domain := hle.1
        have heq : b''.f ⟨b, hb'⟩ = a''.f ⟨b, Set.mem_of_mem_of_subset hb' hle'⟩ := by
          apply hle.2
          simp
        rw [heq]
        apply a''.strictMono
        simpa using hab

    hdomain := by
      obtain ⟨e, he⟩ := hnonempty
      have he' : e.f.domain ∈ (·.domain) '' ((·.f) '' s) := by
        simp only [ne_eq, Set.mem_image, exists_exists_and_eq_and]
        use e
      intro A hA a ha
      unfold LinearPMap.sSup
      simp only
      apply Submodule.mem_sSup_of_mem he'
      exact e.hdomain A hA a ha

    anchor := by
      obtain ⟨e, he⟩ := hnonempty
      have he' : e.f ∈ (·.f) '' s := by use e
      intro A hA a ha
      rw [LinearPMap.sSup_apply hchain'.directedOn he' ⟨a, e.hdomain A hA a ha⟩ ]
      exact e.anchor A hA a ha

    range_cut := by
      intro a ha c
      simp only [Set.mem_range] at ha
      obtain ⟨⟨a', ha'mem⟩, ha'⟩ := ha
      unfold LinearPMap.sSup at ha'mem
      simp only [ne_eq] at ha'mem
      rw [Submodule.mem_sSup_of_directed ((hnonempty.image _).image _)
        hchain''.directedOn] at ha'mem
      obtain ⟨a'', ha''mem, ha''⟩ := ha'mem
      simp only [Set.mem_image, exists_exists_and_eq_and] at ha''mem
      obtain ⟨e, hemem, he⟩ := ha''mem
      have he' : e.f ∈ (·.f) '' s := by use e

      have harange : a ∈ Set.range e.f := by
        rw [← he] at ha''
        use ⟨a', ha''⟩
        rw [← ha']
        symm
        apply LinearPMap.sSup_apply hchain'.directedOn he' ⟨a', ha''⟩
      obtain ⟨⟨b, hbmem⟩, hb⟩ := e.range_cut a harange c

      simp only [Set.mem_range]
      use ⟨b, Set.mem_of_mem_of_subset hbmem (by
        unfold LinearPMap.sSup
        simp only [ne_eq, SetLike.coe_subset_coe]
        apply le_sSup
        simp only [Set.mem_image, exists_exists_and_eq_and]
        use e
      )⟩
      rw [LinearPMap.sSup_apply hchain'.directedOn he' ⟨b, hbmem⟩]
      exact hb

  }
  intro t ht
  apply LinearPMap.le_sSup hchain'.directedOn (by use t)

variable (M) in
theorem SubEmbedding.exists_univ :
    ∃ (e : SubEmbedding M), e.f.domain = ⊤ := by
  obtain ⟨e, he⟩ := SubEmbedding.exists_maximal M
  use e
  suffices ∀ (x : M), x ∈ e.f.domain by
    exact Submodule.eq_top_iff'.mpr this
  contrapose! he with hx
  obtain ⟨x, hx⟩ := hx
  simp only [not_isMax_iff]
  use e.extend hx
  apply lt_of_le_of_ne
  · constructor
    · unfold extend
      simp
    · intro ⟨a, ha⟩ ⟨b, hb⟩ hab
      simp only at hab
      unfold extend ext_fun
      simp only
      symm
      simp_rw [hab]
      apply LinearPMap.supSpanSingleton_apply_mk_of_mem
  · suffices e.f.domain ≠ (e.extend hx).f.domain by
      contrapose! this
      congr
    by_contra heq
    rw [heq] at hx
    contrapose! hx
    unfold extend
    simp only [LinearPMap.domain_supSpanSingleton]
    apply Submodule.mem_sup_right
    simp

variable (M) in
noncomputable
def hahn_embedding_of_divisible : M →+o HahnSeries (a⁰[M]) ℝ where
  toFun (a) :=
    let e := (SubEmbedding.exists_univ M).choose
    let he : e.f.domain = ⊤  := (SubEmbedding.exists_univ M).choose_spec
    let a' : e.f.domain := ⟨a, by
      rw [he]
      simp
    ⟩
    e.f a'

  map_zero' := by
    simp only
    apply LinearPMap.map_zero

  map_add' := by
    intro a b
    simp only
    rw [← LinearPMap.map_add]
    simp

  monotone' := by
    intro a b h
    exact (SubEmbedding.exists_univ M).choose.strictMono.monotone h

variable (M) in
theorem hahn_embedding_of_divisible_injective: Function.Injective (hahn_embedding_of_divisible M) := by
  intro a b h
  simpa using (SubEmbedding.exists_univ M).choose.strictMono.injective h

#min_imports
