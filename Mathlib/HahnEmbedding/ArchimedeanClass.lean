import Mathlib.HahnEmbedding.Misc

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.UpperLower.Principal


variable {M: Type*}
variable [CommGroup M] [LinearOrder M] [IsOrderedMonoid M]

variable (M) in
@[to_additive archimedeanEquiv]
def mulArchimedeanEquiv : Setoid M where
  r (a b) := (∃ m, m ≠ 0 ∧ |a|ₘ ≤ |b|ₘ ^ m) ∧ (∃ n, n ≠ 0 ∧ |b|ₘ ≤ |a|ₘ ^ n)
  iseqv := {
    refl (a) := ⟨⟨1, by simp, by simp⟩, ⟨1, by simp, by simp⟩⟩
    symm (h) := h.symm
    trans := by
      intro a b c ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ ⟨⟨m', hm0', hm'⟩, ⟨n', hn0', hn'⟩⟩
      refine ⟨⟨m' * m, by simp [hm0, hm0'], ?_⟩, ⟨n * n', by simp [hn0, hn0'], ?_⟩⟩
      · refine le_trans hm ?_
        rw [pow_mul]
        exact pow_le_pow_left' hm' m
      · refine le_trans hn' ?_
        rw [pow_mul]
        exact pow_le_pow_left' hn n'
  }

variable (M) in
@[to_additive archimedeanClass]
def mulArchimedeanClass := Quotient (mulArchimedeanEquiv M)


namespace mulArchimedeanClass

@[to_additive]
def mk (a : M) : mulArchimedeanClass M := Quotient.mk'' a

@[to_additive]
theorem mk_surjective : Function.Surjective <| mk (M := M) := Quotient.mk''_surjective

@[to_additive (attr := simp)]
theorem range_mk : Set.range (mk (M := M)) = Set.univ := Set.range_eq_univ.mpr mk_surjective

@[to_additive]
noncomputable
def out (A : mulArchimedeanClass M) : M := Quotient.out A

@[to_additive (attr := simp)]
theorem out_eq (A : mulArchimedeanClass M) : mk A.out = A := Quotient.out_eq' A

@[to_additive]
theorem eq {a b : M} :
    mk a = mk b ↔ (∃ m, m ≠ 0 ∧ |a|ₘ ≤ |b|ₘ ^ m) ∧ (∃ n, n ≠ 0 ∧ |b|ₘ ≤ |a|ₘ ^ n) := Quotient.eq''

@[to_additive (attr := simp)]
theorem mk_out (a : M) :
    (∃ m, m ≠ 0 ∧ |(mk a).out|ₘ ≤ |a|ₘ ^ m) ∧ (∃ n, n ≠ 0 ∧ |a|ₘ ≤ |(mk a).out|ₘ ^ n) := eq.mp (by simp)

@[to_additive (attr := simp)]
theorem mk_inv (a : M) : mk a⁻¹ = mk a := by
  rw [eq]
  exact ⟨⟨1, by simp, by simp⟩, ⟨1, by simp, by simp⟩⟩

@[to_additive]
theorem mk_div_comm (a b : M) : mk (a / b) = mk (b / a) := by
  rw [← mk_inv, inv_div]

@[to_additive (attr := simp)]
theorem mk_mabs (a : M) : mk |a|ₘ = mk a := by
  rw [eq]
  exact ⟨⟨1, by simp, by simp⟩, ⟨1, by simp, by simp⟩⟩


variable (M) in
@[to_additive]
instance instOne : One (mulArchimedeanClass M) := ⟨mk 1⟩

variable (M) in
@[to_additive (attr := simp)]
theorem mk_one : mk (1 : M) = 1 := rfl

@[to_additive (attr := simp)]
theorem eq_one_iff {a : M} : mk a = 1 ↔ a = 1 := by
  constructor
  · intro h
    rw [← mk_one, eq] at h
    obtain ⟨⟨_, _, hm⟩, _⟩ := h
    simpa using hm
  · intro h
    rw [h, mk_one]

variable (M) in
@[to_additive (attr := simp)]
theorem one_out : (1 : mulArchimedeanClass M).out = 1 := by
  rw [← eq_one_iff, out_eq]

variable (M) in
@[to_additive]
instance instNontrivial [Nontrivial M]: Nontrivial (mulArchimedeanClass M) where
  exists_pair_ne := by
    obtain ⟨x, hx⟩ := exists_ne (1 : M)
    use mk x, 1
    apply eq_one_iff.ne.mpr hx

variable (M) in
@[to_additive]
noncomputable
instance instLinearOrder : LinearOrder (mulArchimedeanClass M) :=
  LinearOrder.lift' (fun A ↦ OrderDual.toDual |A.out|ₘ) (by
    intro A B
    simp only [EmbeddingLike.apply_eq_iff_eq]
    intro h
    simpa using congr_arg mk h
  )

@[to_additive]
theorem le (A B : mulArchimedeanClass M) : A ≤ B ↔ |B.out|ₘ ≤ |A.out|ₘ := by rfl

@[to_additive]
theorem lt (A B : mulArchimedeanClass M) : A < B ↔ |B.out|ₘ < |A.out|ₘ := by rfl

@[to_additive]
theorem le_one (A : mulArchimedeanClass M) : A ≤ 1 := by
  rw [le]
  simp

@[to_additive]
theorem ne_one_of_lt {A B : mulArchimedeanClass M} (h : A < B) : A ≠ 1 := by
  apply ne_of_lt
  exact lt_of_lt_of_le h (le_one _)

variable (M) in
@[to_additive]
noncomputable
instance instOrderTop : OrderTop (mulArchimedeanClass M) where
  top := 1
  le_top := le_one

@[to_additive]
theorem mk_lt_mk {a b : M} : mk a < mk b ↔ ∀ n, |b|ₘ ^ n < |a|ₘ := by
  obtain ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ := mk_out a
  obtain ⟨⟨m', hm0', hm'⟩, ⟨n', hn0', hn'⟩⟩ := mk_out b
  constructor
  · intro h k
    by_cases hk0 : k = 0
    · rw [hk0]
      simp only [pow_zero, one_lt_mabs, ne_eq]
      contrapose! h
      rw [h]
      simpa using le_one (mk b)
    · have hne : ¬ mk a = mk b := ne_of_lt h
      rw [eq] at hne
      simp only [not_and, not_exists, not_le, forall_exists_index] at hne
      by_contra!
      obtain hne' := hne k ⟨hk0, this⟩ (m * n') (by simp [hn0', hm0])
      rw [lt] at h
      contrapose! hne'
      apply le_of_lt
      apply lt_of_le_of_lt hn'
      rw [pow_mul]
      rw [pow_lt_pow_iff_left' hn0']
      apply lt_of_lt_of_le h
      exact hm
  · intro h
    rw [lt]
    rw [← pow_lt_pow_iff_left' hn0]
    rw [← pow_le_pow_iff_left' hn0] at hm'
    apply lt_of_le_of_lt hm'
    rw [← pow_mul]
    exact lt_of_lt_of_le (h (m' * n)) hn


variable (M) in
@[to_additive]
theorem mk_antitoneOn : AntitoneOn mk (Set.Ici (1 : M)) := by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_self.mpr ha, mabs_eq_self.mpr hb] at h
  simpa using h

variable (M) in
@[to_additive]
theorem mk_monotoneOn : MonotoneOn mk (Set.Iic (1 : M)) := by
  intro a ha b hb hab
  contrapose! hab
  rw [mk_lt_mk] at hab
  obtain h := hab 1
  rw [mabs_eq_inv_self.mpr ha, mabs_eq_inv_self.mpr hb] at h
  simpa using h

@[to_additive]
theorem mk_le_mk_self_mul_of_mk_eq {a b : M} (hab : mk a = mk b) : mk a ≤ mk (a * b) := by
  by_contra! h
  obtain h2 := hab ▸ h
  obtain h1 := mk_lt_mk.mp h  2
  obtain h2 := mk_lt_mk.mp h2  2
  rw [pow_two] at h1 h2
  have h1 := lt_of_lt_of_le h1 (mabs_mul _ _)
  have h2 := lt_of_lt_of_le h2 (mabs_mul _ _)
  simp only [mul_lt_mul_iff_left, mul_lt_mul_iff_right] at h1 h2
  have := h1.trans h2
  simp at this

@[to_additive]
theorem mk_eq_mk_self_mul_of_mk_lt {a b : M} (h : mk a < mk b) : mk a = mk (a * b) := by
  obtain h := mk_lt_mk.mp h
  apply eq.mpr
  constructor
  · use 2
    constructor
    · simp
    · apply (mabs_mul' _ b).trans
      rw [mul_comm b a, pow_two]
      simp only [mul_le_mul_iff_right]
      apply le_of_mul_le_mul_left' (a := |b|ₘ)
      rw [mul_comm a b]
      refine le_trans ?_ (mabs_mul' a b)
      obtain h := (h 2).le
      rw [pow_two] at h
      exact h
  · use 2
    constructor
    · simp
    · apply (mabs_mul _ _).trans
      rw [pow_two]
      simp only [mul_le_mul_iff_left]
      simpa using (h 1).le

@[to_additive]
theorem mk_prod {ι : Type*} [LinearOrder ι] {s : Finset ι} (hnonempty : s.Nonempty)
    {a : ι → M}  :
    StrictMonoOn (mk ∘ a) s → mk (∏ i ∈ s, (a i)) = mk (a (s.min' hnonempty)) := by
  induction hnonempty using Finset.Nonempty.cons_induction with
  | singleton i => simp
  | cons i s hi hs ih =>
    intro hmono
    obtain ih := ih (hmono.mono (by simp))
    rw [Finset.prod_cons]
    have hminmem : s.min' hs ∈ (Finset.cons i s hi) :=
      Finset.mem_cons_of_mem (by apply Finset.min'_mem)
    have hne : mk (a i) ≠ mk (a (s.min' hs)) := by
      by_contra!
      obtain eq := hmono.injOn (by simp) hminmem this
      rw [eq] at hi
      obtain hi' := Finset.min'_mem _ hs
      exact hi hi'
    rw [← ih] at hne
    obtain hlt|hlt := lt_or_gt_of_ne hne
    · rw [← mk_eq_mk_self_mul_of_mk_lt hlt]
      congr
      apply le_antisymm
      · apply Finset.le_min'
        intro y hy
        obtain heq|hmem := Finset.mem_cons.mp hy
        · rw [heq]
        · apply le_of_lt
          refine lt_of_lt_of_le ?_ (Finset.min'_le _ _ hmem)
          apply (hmono.lt_iff_lt (by simp) hminmem).mp
          rw [ih] at hlt
          exact hlt
      · apply Finset.min'_le
        simp
    · rw [mul_comm]
      rw [← mk_eq_mk_self_mul_of_mk_lt hlt]
      rw [ih]
      congr 2
      apply le_antisymm
      · apply Finset.le_min'
        intro y hy
        obtain heq|hmem := Finset.mem_cons.mp hy
        · rw [heq]
          apply le_of_lt
          apply (hmono.lt_iff_lt hminmem (by simp)).mp
          rw [ih] at hlt
          exact hlt
        · apply Finset.min'_le
          exact hmem
      · apply Finset.min'_le
        exact hminmem

@[to_additive]
theorem min_le_mk_mul (a b : M) : min (mk a) (mk b) ≤ mk (a * b) := by
  obtain hab|hab|hab := lt_trichotomy (mk a) (mk b)
  · simp only [inf_le_iff]
    left
    exact (mk_eq_mk_self_mul_of_mk_lt hab).le
  · rw [← hab]
    simpa using mk_le_mk_self_mul_of_mk_eq hab
  · simp only [inf_le_iff]
    right
    rw [mul_comm]
    exact (mk_eq_mk_self_mul_of_mk_lt hab).le

@[to_additive]
theorem lt_of_mk_lt_mk {a b : M} (h : mk a < mk b) (hpos : 1 ≤ a) : b < a := by
  obtain h := (mk_lt_mk).mp h 1
  rw [pow_one, mabs_lt, mabs_eq_self.mpr hpos] at h
  exact h.2

@[to_additive]
theorem lt_of_mk_lt_mk' {a b : M} (h : mk a < mk b) (hneg : a ≤ 1) : a < b := by
  obtain h := (mk_lt_mk).mp h 1
  rw [pow_one, mabs_lt, mabs_eq_inv_self.mpr hneg] at h
  simp only [inv_inv] at h
  exact h.1

@[to_additive]
theorem one_lt_of_one_lt_of_mk_lt {a b : M} (ha : 1 < a) (hab : mk a < mk (b / a)) :
    1 < b := by
  suffices a⁻¹ < b / a by
    simpa using this
  apply lt_of_mk_lt_mk'
  · simpa using hab
  · simpa using ha.le

@[to_additive]
theorem Ioi_nonempty {A : mulArchimedeanClass M} (hA : A ≠ 1):
    (UpperSet.Ioi A).carrier.Nonempty := by
  use 1
  simpa using lt_of_le_of_ne (le_one _) hA

@[to_additive]
theorem archimedean_of_mk_eq_mk (h : ∀ (a b : M), a ≠ 1 → b ≠ 1 → mk a = mk b) :
    MulArchimedean M where
  arch := by
    intro x y hy
    by_cases hx : x ≤ 1
    · use 0
      simpa using hx
    · have hx : 1 < x := lt_of_not_ge hx
      have hxy : mk x = mk y := by
        apply h x y hx.ne.symm hy.ne.symm
      obtain ⟨⟨m, _, hm⟩, _⟩ := (mulArchimedeanClass.eq).mp hxy
      use m
      rw [mabs_eq_self.mpr hx.le, mabs_eq_self.mpr hy.le] at hm
      exact hm


variable {N: Type*}
variable [CommGroup N] [LinearOrder N] [IsOrderedMonoid N]

@[to_additive]
noncomputable
abbrev orderHomFun {F : Type*} [FunLike F M N]
    (f : F) (a : mulArchimedeanClass M) : mulArchimedeanClass N :=
  mulArchimedeanClass.mk (f a.out)

@[to_additive]
noncomputable
def orderHom {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) : mulArchimedeanClass M →o mulArchimedeanClass N where
  toFun := orderHomFun f
  monotone' := by
    intro a b h
    contrapose! h
    unfold orderHomFun at h
    rw [mk_lt_mk] at h
    rw [← out_eq a, ← out_eq b]
    rw [mk_lt_mk]
    intro n
    obtain h := h n
    contrapose! h
    obtain h := OrderHomClass.monotone f h
    rw [map_pow, map_mabs, map_mabs] at h
    exact h

@[to_additive]
theorem map_mk {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) (a : M):
    mk (f a) = (orderHom f) (mk a) := by
  unfold orderHom orderHomFun
  simp
  apply eq.mpr
  have a_eq : mk a = mk (mk a).out := by
    rw [out_eq]
  obtain ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ := eq.mp a_eq
  constructor <;> [use m; use n]
  <;> [refine ⟨hm0, ?_⟩; refine ⟨hn0, ?_⟩]
  all_goals
    rw [← map_mabs, ← map_mabs]
    rw [← map_pow]
    apply OrderHomClass.monotone
    try exact hm
    try exact hn

@[to_additive]
theorem map_mk_eq {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) {a b : M} (h : mk a = mk b) :
    mk (f a) = mk (f b) := by
  rw [map_mk, map_mk, h]

@[to_additive]
theorem map_mk_le {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) {a b : M} (h : mk a ≤ mk b) :
    mk (f a) ≤ mk (f b) := by
  rw [map_mk, map_mk]
  apply OrderHomClass.monotone
  exact h

@[to_additive]
theorem orderHom_injective {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    {f : F} (h : Function.Injective f) : Function.Injective (mulArchimedeanClass.orderHom f) := by
  intro a b
  nth_rw 2 [← mulArchimedeanClass.out_eq a]
  nth_rw 2 [← mulArchimedeanClass.out_eq b]
  unfold orderHom orderHomFun
  simp only [OrderHom.coe_mk]
  rw [mulArchimedeanClass.eq, mulArchimedeanClass.eq]
  simp_rw [← map_mabs, ← map_pow]
  intro h
  obtain ⟨⟨m, hm0, hm⟩, ⟨n, hn0, hn⟩⟩ := h
  refine ⟨⟨m, hm0, ?_⟩, ⟨n, hn0, ?_⟩⟩
  · contrapose! hm
    apply lt_of_le_of_ne
    · apply OrderHomClass.monotone f hm.le
    · contrapose! hm
      exact (h hm).symm.le
  · contrapose! hn
    apply lt_of_le_of_ne
    · apply OrderHomClass.monotone f hn.le
    · contrapose! hn
      exact (h hn).symm.le

@[to_additive (attr := simp)]
theorem orderHom_one {F : Type*} [FunLike F M N] [OrderHomClass F M N] [MonoidHomClass F M N]
    (f : F) : (mulArchimedeanClass.orderHom f) (1 : mulArchimedeanClass M) = (1 : mulArchimedeanClass N) := by
  rw [← mk_one, ← mk_one]
  rw [← map_mk]
  simp

end mulArchimedeanClass
