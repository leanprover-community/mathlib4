import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.Finsupp.WellFounded
import Mathlib.Data.List.TFAE
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Finsupp.Lex
import Mathlib.Logic.Equiv.TransferInstance

/-! # Groebner bases 

Reference : [Becker-Weispfenning1993] -/

structure MonomialOrder (σ : Type*) where
  syn : Type*
  locacm : LinearOrderedCancelAddCommMonoid syn
  toSyn : (σ →₀ ℕ) ≃+ syn
  toSyn_monotone : Monotone toSyn
  wf : WellFoundedLT syn

structure MonomialOrder' (σ : Type*) where
  syn : Type*
  locacm : LinearOrderedCancelAddCommMonoid syn
  toSyn : (σ →₀ ℕ) →+ syn
  toSyn_injective : Function.Injective toSyn
  toSyn_monotone : Monotone toSyn
  wf : WellFoundedLT syn

instance (σ : Type*) (m : MonomialOrder σ) : LinearOrderedCancelAddCommMonoid m.syn := m.locacm

instance (σ : Type*) (m : MonomialOrder σ) : WellFoundedLT m.syn := m.wf

variable {σ : Type*} (m : MonomialOrder σ)

namespace MonomialOrder

lemma le_add_right (a b : σ →₀ ℕ) : 
    m.toSyn a ≤ m.toSyn a + m.toSyn b := by 
  rw [← map_add]
  exact m.toSyn_monotone le_self_add

/-
lemma MonomialOrder.toSyn_monotone : Monotone (m.toSyn) := by
  intro a b h
  have : b = a + (b - a) := by
    ext s
    simp only [coe_add, coe_tsub, Pi.add_apply, Pi.sub_apply]
    rw [add_tsub_cancel_of_le (h s)]
  rw [this]
  apply le_add_right -/
  
instance orderBot : OrderBot (m.syn) where
  bot := 0
  bot_le a := by 
    have := m.le_add_right 0 (m.toSyn.symm a)
    simp [map_add, zero_add] at this
    exact this

@[simp] 
theorem bot_eq_zero : (⊥ : m.syn) = 0 := rfl

theorem eq_zero_iff {a : m.syn} : a = 0 ↔ a ≤ 0 := eq_bot_iff

lemma toSyn_strictMono : StrictMono (m.toSyn) := by
  apply m.toSyn_monotone.strictMono_of_injective m.toSyn.injective

/- 
theorem MonomialOrder.isDickson {σ : Type*} [Finite σ] (m : MonomialOrder σ) :
    Preorder.isDickson m.syn  :=
  m.toSyn.isDickson_of_monotone m.toSyn_monotone (Finsupp.isDickson σ)

theorem MonomialOrder.wf {σ : Type*} [Finite σ] (m : MonomialOrder σ) :
    WellFoundedLT m.syn :=
  isDickson.wf (isDickson m)
-/

open MvPolynomial 

variable {σ : Type*} (m : MonomialOrder σ) 

scoped
notation:25 c "≺[" m:25 "]" d:25 => (MonomialOrder.toSyn m c < MonomialOrder.toSyn m d)

scoped
notation:25 c "≼[" m:25 "]" d:25 => (MonomialOrder.toSyn m c ≤ MonomialOrder.toSyn m d)

/-- the degree of a multivariate polynomial with respect to a monomial ordering -/
def degree {R : Type*} [CommRing R] (f : MvPolynomial σ R) : σ →₀ ℕ :=
  m.toSyn.symm (f.support.sup m.toSyn)

/-- the leading coefficient of a multivariate polynomial with respect to a monomial ordering -/
def lCoeff {R : Type*} [CommRing R] (f : MvPolynomial σ R) : R :=
  f.coeff (m.degree f)

variable {m : MonomialOrder σ} {R : Type*} [CommRing R]

@[simp]
theorem degree_zero : m.degree (0 : MvPolynomial σ R) = 0 := by
  simp [degree]

@[simp]
theorem lCoeff_zero : m.lCoeff (0 : MvPolynomial σ R) = 0 := by
  simp [degree, lCoeff]

theorem degree_monomial_le {d : σ →₀ ℕ} (c : R) :
    m.degree (monomial d c) ≼[m] d := by
  simp only [degree, AddEquiv.apply_symm_apply]
  apply le_trans (Finset.sup_mono support_monomial_subset)
  simp only [Finset.sup_singleton, le_refl]

theorem degree_monomial {d : σ →₀ ℕ} (c : R) [Decidable (c = 0)] :
    m.degree (monomial d c) = if c = 0 then 0 else d := by
  simp only [degree, support_monomial]
  split_ifs with hc <;> simp

@[simp]
theorem lCoeff_monomial {d : σ →₀ ℕ} (c : R) :
    m.lCoeff (monomial d c) = c := by
  classical
  simp only [lCoeff, degree_monomial]
  split_ifs with hc <;> simp [hc]

theorem degree_le_iff {f : MvPolynomial σ R} {d : σ →₀ ℕ} :
    m.degree f ≼[m] d ↔ ∀ c ∈ f.support, c ≼[m] d := by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.sup_le_iff, mem_support_iff, ne_eq]

theorem degree_lt_iff {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : 0 ≺[m] d) :
    m.degree f ≺[m] d ↔ ∀ c ∈ f.support, c ≺[m] d := by
  simp only [map_zero] at hd
  unfold degree
  simp only [AddEquiv.apply_symm_apply]
  exact Finset.sup_lt_iff hd

theorem le_degree {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : d ∈ f.support) :
    d ≼[m] m.degree f := by
  unfold degree
  simp only [AddEquiv.apply_symm_apply, Finset.le_sup hd]

theorem coeff_eq_zero_of_lt {f : MvPolynomial σ R} {d : σ →₀ ℕ} (hd : m.degree f ≺[m] d) :
    f.coeff d = 0 := by
  rw [← not_le] at hd
  by_contra hf
  apply hd (m.le_degree (mem_support_iff.mpr hf))

theorem _root_.Finset.sup_mem_of_nonempty {α β : Type*} {f : α → β}  [LinearOrder β] [OrderBot β]
    {s : Finset α} (hs : s.Nonempty) : 
    s.sup f ∈ f '' s := by 
  classical
  induction s using Finset.induction with
  | empty => exfalso; simp only [Finset.not_nonempty_empty] at hs
  | @insert a s _ h => 
    rw [Finset.sup_insert (b := a) (s := s) (f := f)]
    by_cases hs : s = ∅ 
    · simp [hs]
    · rw [← ne_eq, ← Finset.nonempty_iff_ne_empty] at hs
      simp only [Finset.coe_insert]
      rcases le_total (f a) (s.sup f) with (ha | ha)
      · rw [sup_eq_right.mpr ha]
        exact Set.image_mono (Set.subset_insert a s) (h hs)
      · rw [sup_eq_left.mpr ha]
        apply Set.mem_image_of_mem _ (Set.mem_insert a ↑s)

@[simp]
theorem lCoeff_ne_zero_iff {f : MvPolynomial σ R} :
    m.lCoeff f ≠ 0 ↔ f ≠ 0 := by
  constructor
  · rw [not_imp_not]
    intro hf
    rw [hf, lCoeff_zero]
  · intro hf
    rw [← support_nonempty] at hf
    rw [lCoeff, ← mem_support_iff, degree] 
    suffices f.support.sup m.toSyn ∈ m.toSyn '' f.support by 
      obtain ⟨d, hd, hd'⟩ := this
      rw [← hd', AddEquiv.symm_apply_apply]
      exact hd
    exact Finset.sup_mem_of_nonempty hf

@[simp]
theorem lCoeff_eq_zero_iff {f : MvPolynomial σ R} :
    lCoeff m f = 0 ↔ f = 0 := by
  simp only [← not_iff_not, lCoeff_ne_zero_iff]

@[simp]
theorem coeff_degree_ne_zero_iff {f : MvPolynomial σ R} :
    f.coeff (m.degree f) ≠ 0 ↔ f ≠ 0 :=
  m.lCoeff_ne_zero_iff

@[simp]
theorem coeff_degree_eq_zero_iff {f : MvPolynomial σ R} :
    f.coeff (m.degree f) = 0 ↔ f = 0 :=
  m.lCoeff_eq_zero_iff

theorem degree_eq_zero_iff_totalDegree_eq_zero {f : MvPolynomial σ R} :
    m.degree f = 0 ↔ f.totalDegree = 0 := by 
  rw [← m.toSyn.injective.eq_iff]
  rw [map_zero, ← m.bot_eq_zero, eq_bot_iff, m.bot_eq_zero, ← m.toSyn.map_zero]
  rw [degree_le_iff]
  rw [totalDegree_eq_zero_iff]
  apply forall_congr'
  intro d
  apply imp_congr (rfl.to_iff)
  rw [map_zero, ← m.bot_eq_zero, ← eq_bot_iff, m.bot_eq_zero]
  simp only [AddEquivClass.map_eq_zero_iff]
  exact Finsupp.ext_iff

@[simp]
theorem degree_neg {f : MvPolynomial σ R} :
    m.degree (-f) = m.degree f := by
  unfold degree
  rw [support_neg]

@[simp]
theorem degree_C (r : R) :
    m.degree (C r) = 0 := by
  rw [degree_eq_zero_iff_totalDegree_eq_zero, totalDegree_C]

theorem degree_add_le {f g : MvPolynomial σ R} :
    m.toSyn (m.degree (f + g)) ≤ m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  conv_rhs => rw [← m.toSyn.apply_symm_apply (_ ⊔ _)]
  rw [degree_le_iff]
  simp only [AddEquiv.apply_symm_apply, le_sup_iff]
  intro b hb
  by_cases hf : b ∈ f.support
  · left
    exact m.le_degree hf
  · right
    apply m.le_degree
    simp only [not_mem_support_iff] at hf
    simpa only [mem_support_iff, coeff_add, hf, zero_add] using hb

theorem degree_sub_le {f g : MvPolynomial σ R} :
    m.toSyn (m.degree (f - g)) ≤ m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  rw [sub_eq_add_neg]
  apply le_of_le_of_eq m.degree_add_le
  rw [degree_neg]

theorem degree_add_of_lt {f g : MvPolynomial σ R} (h : m.degree g ≺[m] m.degree f) :
    m.degree (f + g) = m.degree f := by
  apply m.toSyn.injective
  apply le_antisymm 
  · apply le_trans degree_add_le
    simp only [sup_le_iff, le_refl, true_and, le_of_lt h]
  · apply le_degree
    rw [mem_support_iff, coeff_add, m.coeff_eq_zero_of_lt h, add_zero, ← lCoeff, lCoeff_ne_zero_iff]
    intro hf
    rw [← not_le, hf] at h
    apply h
    simp only [degree_zero, map_zero]
    apply bot_le

theorem degree_add_of_ne {f g : MvPolynomial σ R}
    (h : m.degree f ≠ m.degree g) :
    m.toSyn (m.degree (f + g)) = m.toSyn (m.degree f) ⊔ m.toSyn (m.degree g) := by
  by_cases h' : m.degree g ≺[m] m.degree f
  · simp [degree_add_of_lt h', left_eq_sup, le_of_lt h']
  · rw [not_lt, le_iff_eq_or_lt, Classical.or_iff_not_imp_left, EmbeddingLike.apply_eq_iff_eq] at h'
    rw [add_comm, degree_add_of_lt (h' h), right_eq_sup]
    simp only [le_of_lt (h' h)]

theorem degree_mul_le {f g : MvPolynomial σ R} :
    m.degree (f * g) ≼[m] m.degree f + m.degree g := by
  classical
  rw [degree_le_iff]
  intro c 
  rw [← not_lt, mem_support_iff, not_imp_not]
  intro hc
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨d, e⟩ hde
  simp only [Finset.mem_antidiagonal] at hde
  dsimp only
  by_cases hd : m.degree f ≺[m] d
  · rw [m.coeff_eq_zero_of_lt hd, zero_mul]
  · suffices m.degree g ≺[m] e by
      rw [m.coeff_eq_zero_of_lt this, mul_zero]
    simp only [not_lt] at hd
    apply lt_of_add_lt_add_left (a := m.toSyn d)
    simp only [← map_add, hde]
    apply lt_of_le_of_lt _ hc
    simp only [map_add]
    exact add_le_add_right hd _

theorem lCoeff_mul' {f g : MvPolynomial σ R} :
    (f * g).coeff (m.degree f + m.degree g) = m.lCoeff f * m.lCoeff g := by
  classical
  rw [coeff_mul]
  rw [Finset.sum_eq_single (m.degree f, m.degree g)]
  · rfl
  · rintro ⟨c, d⟩ hcd h
    simp only [Finset.mem_antidiagonal] at hcd
    by_cases hf : m.degree f ≺[m] c
    · rw [m.coeff_eq_zero_of_lt hf, zero_mul]
    · suffices m.degree g ≺[m] d by
        rw [coeff_eq_zero_of_lt this, mul_zero]
      apply lt_of_add_lt_add_left (a := m.toSyn c)
      simp only [← map_add, hcd]
      simp only [map_add]
      rw [← not_le]
      intro h'; apply hf
      simp only [le_iff_eq_or_lt] at h'
      cases h' with
      | inl h' => 
        simp only [← map_add, EmbeddingLike.apply_eq_iff_eq, add_left_inj] at h'
        exfalso
        apply h
        simp only [h', Prod.mk.injEq, true_and]
        simpa [h'] using hcd
      | inr h' => 
        exact lt_of_add_lt_add_right h'
  · simp

theorem degree_mul_of_isRegular_left {f g : MvPolynomial σ R} 
    (hf : IsRegular (m.lCoeff f)) (hg : g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := by
  apply m.toSyn.injective
  apply le_antisymm degree_mul_le
  apply le_degree 
  rw [mem_support_iff, lCoeff_mul']
  simp only [ne_eq, hf, IsRegular.left, IsLeftRegular.mul_left_eq_zero_iff,
    lCoeff_eq_zero_iff]
  exact hg

theorem degree_mul_of_isRegular_right {f g : MvPolynomial σ R} 
    (hf : f ≠ 0) (hg : IsRegular (m.lCoeff g)) :
    m.degree (f * g) = m.degree f + m.degree g := by
  rw [mul_comm, m.degree_mul_of_isRegular_left hg hf, add_comm]

theorem degree_mul [IsDomain R] {f g : MvPolynomial σ R} 
    (hf : f ≠ 0) (hg : g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := 
  degree_mul_of_isRegular_left (isRegular_of_ne_zero (lCoeff_ne_zero_iff.mpr hf)) hg

theorem degree_mul' [IsDomain R] {f g : MvPolynomial σ R} (hfg : f * g ≠ 0) :
    m.degree (f * g) = m.degree f + m.degree g := 
  degree_mul (left_ne_zero_of_mul hfg) (right_ne_zero_of_mul hfg)

theorem lCoeff_mul [IsDomain R] {f g : MvPolynomial σ R} 
    (hf : f ≠ 0) (hg : g ≠ 0) :
    m.lCoeff (f * g) = m.lCoeff f * m.lCoeff g := by
  rw [lCoeff, degree_mul hf hg, ← lCoeff_mul']

theorem degree_smul_le {r : R} {f : MvPolynomial σ R} :
    m.degree (r • f) ≼[m] m.degree f := by
  rw [smul_eq_C_mul]
  apply le_of_le_of_eq degree_mul_le
  simp
   
theorem degree_smul {r : R} (hr : IsRegular r) {f : MvPolynomial σ R} :
    m.degree (r • f) = m.degree f := by
  by_cases hf : f = 0
  · simp [hf]
  apply m.toSyn.injective
  apply le_antisymm degree_smul_le
  apply le_degree
  simp only [mem_support_iff, smul_eq_C_mul]
  rw [← zero_add (degree m f), ← degree_C r, lCoeff_mul']
  simp [lCoeff, hr.left.mul_left_eq_zero_iff, hf]

/-- Delete the leading term in a multivariate polynomial (for some monomial order) -/
noncomputable def subLTerm (f : MvPolynomial σ R) : MvPolynomial σ R :=
  f - monomial (m.degree f) (m.lCoeff f)
 
theorem degree_sub_LTerm_le (f : MvPolynomial σ R) :
    m.degree (m.subLTerm f) ≼[m] m.degree f := by
  apply le_trans degree_sub_le
  simp only [sup_le_iff, le_refl, true_and]
  apply degree_monomial_le

theorem degree_sub_LTerm_lt {f : MvPolynomial σ R} (hf : m.degree f ≠ 0) : 
    m.degree (m.subLTerm f) ≺[m] m.degree f := by
  rw [lt_iff_le_and_ne]
  refine ⟨degree_sub_LTerm_le f, ?_⟩
  classical
  intro hf'
  simp only [EmbeddingLike.apply_eq_iff_eq] at hf'
  have : m.subLTerm f ≠ 0 := by 
    intro h
    simp only [h, degree_zero] at hf'
    exact hf hf'.symm
  rw [← coeff_degree_ne_zero_iff (m := m), hf'] at this
  apply this
  simp [subLTerm, coeff_monomial, lCoeff]

/-- Reduce a polynomial modulo a polynomial with unit leading term (for some monomial order) -/
noncomputable def reduce {b : MvPolynomial σ R} (hb : IsUnit (m.lCoeff b)) (f : MvPolynomial σ R) :
    MvPolynomial σ R :=
 f - monomial (m.degree f - m.degree b) (hb.unit⁻¹ * m.lCoeff f) * b
 
theorem degree_reduce_lt {f b : MvPolynomial σ R} (hb : IsUnit (m.lCoeff b))
    (hbf : m.degree b ≤ m.degree f) (hf : m.degree f ≠ 0) : 
    m.degree (m.reduce hb f) ≺[m] m.degree f := by
  have H : m.degree f = 
    m.degree ((monomial (m.degree f - m.degree b)) (hb.unit⁻¹ * m.lCoeff f)) + 
      m.degree b := by
    classical
    rw [degree_monomial, if_neg]
    · ext d
      rw [tsub_add_cancel_of_le hbf]
    · simp only [Units.mul_right_eq_zero, lCoeff_eq_zero_iff]
      intro hf0
      apply hf 
      simp [hf0]
  have H' : coeff (m.degree f) (m.reduce hb f) = 0 := by 
    simp only [reduce, coeff_sub, sub_eq_zero]
    nth_rewrite 2 [H]
    rw [lCoeff_mul' (m := m), lCoeff_monomial]
    rw [mul_comm, ← mul_assoc]
    simp only [IsUnit.mul_val_inv, one_mul]
    rfl
  rw [lt_iff_le_and_ne]
  constructor
  · classical
    apply le_trans degree_sub_le
    simp only [sup_le_iff, le_refl, true_and]
    apply le_of_le_of_eq degree_mul_le
    rw [m.toSyn.injective.eq_iff]
    exact H.symm
  · intro K
    simp only [EmbeddingLike.apply_eq_iff_eq] at K
    nth_rewrite 1 [← K] at H'
    change lCoeff m _ = 0 at H'
    rw [lCoeff_eq_zero_iff] at H'
    rw [H', degree_zero] at K
    exact hf K.symm
    
theorem eq_C_of_degree_eq_zero {f : MvPolynomial σ R} (hf : m.degree f = 0) :
    f = C (m.lCoeff f) := by 
  ext d
  simp only [lCoeff, hf]
  classical
  by_cases hd : d = 0
  · simp [hd]
  · rw [coeff_C, if_neg (Ne.symm hd)]
    apply coeff_eq_zero_of_lt (m := m)
    rw [hf, map_zero, lt_iff_le_and_ne, ne_eq, eq_comm, AddEquivClass.map_eq_zero_iff] 
    exact ⟨bot_le, hd⟩

theorem monomialOrderDiv [Finite σ] (B : Set (MvPolynomial σ R)) 
    (hB : ∀ b ∈ B, IsUnit (m.lCoeff b)) (f : MvPolynomial σ R) :
    ∃ (g : B →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R), 
      f = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r ∧ 
        (∀ (b : B), m.degree ((b : MvPolynomial σ R) * (g b)) ≼[m] m.degree f) ∧
        (∀ c ∈ r.support, ∀ b ∈ B, ¬ (m.degree b ≤ c)) := by
  by_cases hB' : ∃ b ∈ B, m.degree b = 0
  · obtain ⟨b, hb, hb0⟩ := hB'
    use Finsupp.single ⟨b, hb⟩ ((hB b hb).unit⁻¹ • f), 0
    constructor
    · simp only [Finsupp.linearCombination_single, smul_eq_mul, add_zero]
      simp only [smul_mul_assoc, ← smul_eq_iff_eq_inv_smul, Units.smul_isUnit]
      nth_rewrite 2 [eq_C_of_degree_eq_zero hb0]
      rw [mul_comm, smul_eq_C_mul]
    constructor
    · intro c
      by_cases hc : c = ⟨b, hb⟩
      · apply le_trans degree_mul_le
        simp only [hc, hb0, Finsupp.single_eq_same, zero_add]
        apply le_of_eq
        simp only [EmbeddingLike.apply_eq_iff_eq]
        apply degree_smul (Units.isRegular _)
      · simp only [Finsupp.single_eq_of_ne (Ne.symm hc), mul_zero, degree_zero, map_zero]
        apply bot_le
    · simp
  push_neg at hB'
  by_cases hf0 : f = 0
  · refine ⟨0, 0, by simp [hf0], ?_, by simp⟩
    intro b
    simp only [Finsupp.coe_zero, Pi.zero_apply, mul_zero, degree_zero, map_zero]
    exact bot_le
  by_cases hf : ∃ b ∈ B, m.degree b ≤ m.degree f
  · obtain ⟨b, hb, hf⟩ := hf
    have deg_reduce : m.degree (m.reduce (hB b hb) f) ≺[m] m.degree f := by
      apply degree_reduce_lt (hB b hb) hf
      intro hf0'
      apply hB' b hb
      simpa [hf0'] using hf
    obtain ⟨g', r', H'⟩ := monomialOrderDiv B hB (m.reduce (hB b hb) f)
    use g' + 
      Finsupp.single ⟨b, hb⟩ (monomial (m.degree f - m.degree b) ((hB b hb).unit⁻¹ * m.lCoeff f)) 
    use r'
    constructor
    · rw [map_add, add_assoc, add_comm _ r', ← add_assoc, ← H'.1]
      simp [reduce]
    constructor
    · rintro c
      simp
      rw [mul_add]
      apply le_trans degree_add_le
      simp only [sup_le_iff]
      constructor
      · exact le_trans (H'.2.1 _) (le_of_lt deg_reduce)
      · classical
        rw [Finsupp.single_apply]
        split_ifs with hc
        · apply le_trans degree_mul_le
          simp only [map_add]
          apply le_of_le_of_eq (add_le_add_left (degree_monomial_le _) _)
          simp only [← hc]
          rw [← map_add, m.toSyn.injective.eq_iff]
          rw [add_tsub_cancel_of_le]
          exact hf
        · simp only [mul_zero, degree_zero, map_zero]
          exact bot_le
    · exact H'.2.2
  · push_neg at hf
    suffices ∃ (g' : B →₀ MvPolynomial σ R), ∃ r', 
        (m.subLTerm f = (Finsupp.linearCombination (MvPolynomial σ R) fun b ↦ ↑b) g' + r') ∧
        (∀ (b : B), m.degree ((b : MvPolynomial σ R) * (g' b)) ≼[m] m.degree (m.subLTerm f)) ∧
        (∀ c ∈ r'.support, ∀ b ∈ B, ¬ m.degree b ≤ c) by
      obtain ⟨g', r', H'⟩ := this
      use g', r' +  monomial (m.degree f) (m.lCoeff f)
      constructor
      · simp [← add_assoc, ← H'.1, subLTerm]
      constructor
      · exact fun b ↦ le_trans (H'.2.1 b) (degree_sub_LTerm_le f)
      · intro c hc b hb
        by_cases hc' : c ∈ r'.support
        · exact H'.2.2 c hc' b hb 
        · classical
          have := MvPolynomial.support_add hc
          rw [Finset.mem_union, Classical.or_iff_not_imp_left] at this
          specialize this hc'
          simp only [mem_support_iff, coeff_monomial, ne_eq, ite_eq_right_iff,
            coeff_degree_eq_zero_iff, Classical.not_imp] at this
          rw [← this.1]
          exact hf b hb
    by_cases hf'0 : m.subLTerm f = 0
    · refine ⟨0, 0, by simp [hf'0], ?_, by simp⟩
      intro b
      simp only [Finsupp.coe_zero, Pi.zero_apply, mul_zero, degree_zero, map_zero]
      exact bot_le
    · apply monomialOrderDiv B hB 
termination_by WellFounded.wrap 
  ((isWellFounded_iff m.syn fun x x_1 ↦ x < x_1).mp m.wf) (m.toSyn (m.degree f))
decreasing_by
· exact deg_reduce
· apply degree_sub_LTerm_lt
  intro hf0
  apply hf'0
  simp only [subLTerm, sub_eq_zero]
  nth_rewrite 1 [eq_C_of_degree_eq_zero hf0, hf0]
  simp 
   
end MonomialOrder

section Lex

open Finsupp
-- The linear order on `Finsupp`s obtained by the lexicographic ordering. -/
noncomputable instance {α N : Type*} [LinearOrder α] [WellFoundedGT α]
    [OrderedCancelAddCommMonoid N] :
    OrderedCancelAddCommMonoid (Lex (α →₀ N)) where 
  le_of_add_le_add_left a b c h := by simpa only [add_le_add_iff_left] using h
  add_le_add_left a b h c := by simpa only [add_le_add_iff_left] using h

theorem _root_.Finsupp.lex_lt_iff {α N : Type*} [LinearOrder α] [LinearOrder N] [Zero N]
    {a b : Lex (α →₀ N)} :
    a < b ↔ ∃ i, (∀ j, j< i → ofLex a j = ofLex b j) ∧ ofLex a i < ofLex b i := 
    Finsupp.lex_def

theorem _root_.Finsupp.lex_le_iff {α N : Type*} [LinearOrder α] [LinearOrder N] [Zero N]
    {a b : Lex (α →₀ N)} :
    a ≤ b ↔ a = b ∨ ∃ i, (∀ j, j< i → ofLex a j = ofLex b j) ∧ ofLex a i < ofLex b i := by
    rw [le_iff_eq_or_lt, Finsupp.lex_lt_iff]

theorem toLex_monotone {σ : Type*} [LinearOrder σ] :
    Monotone (toLex (α := σ →₀ ℕ)) := by
  intro a b h
  rw [← (add_tsub_cancel_of_le h), toLex_add]
  simp only [AddEquiv.refl_symm, le_add_iff_nonneg_right, ge_iff_le]
  apply bot_le

noncomputable def MonomialOrder.lex (σ : Type*) [LinearOrder σ] [WellFoundedGT σ] :
    MonomialOrder σ where
  syn := Lex (σ →₀ ℕ)
  locacm := Lex.linearOrderedCancelAddCommMonoid
  toSyn := {
    toEquiv := toLex
    map_add' := toLex_add } -- AddEquiv.refl _ -- (AddEquiv.refl (Lex (σ →₀ ℕ))).symm
  wf := Lex.wellFoundedLT
  toSyn_monotone := Finsupp.toLex_monotone

noncomputable def MonomialOrder.revlex (σ : Type*) [LinearOrder σ] [WellFoundedLT σ] :
    MonomialOrder σ := MonomialOrder.lex σᵒᵈ 

end Lex

section degLex

/-- A type synonym to equip a type with its lexicographic order sorted by degrees. -/
def DegLex (α : Type*) := α

variable {α : Type*}
/-- `toDegLex` is the identity function to the `DegLex` of a type.  -/
@[match_pattern]
def toDegLex : α ≃ DegLex α :=
  Equiv.refl _

/-- `ofDegLex` is the identity function from the `DegLex` of a type.  -/
@[match_pattern]
def ofDegLex : DegLex α ≃ α :=
  Equiv.refl _

@[simp]
theorem toDegLex_symm_eq : (@toDegLex α).symm = ofDegLex :=
  rfl

@[simp]
theorem ofDegLex_symm_eq : (@ofDegLex α).symm = toDegLex :=
  rfl

@[simp]
theorem toDegLex_ofDegLex (a : DegLex α) : toDegLex (ofDegLex a) = a :=
  rfl

@[simp]
theorem ofDegLex_toDegLex (a : α) : ofDegLex (toDegLex a) = a :=
  rfl

theorem toDegLex_inj {a b : α} : toDegLex a = toDegLex b ↔ a = b :=
  Iff.rfl

theorem ofDegLex_inj {a b : DegLex α} : ofDegLex a = ofDegLex b ↔ a = b :=
  Iff.rfl

/-- A recursor for `DegLex`. Use as `induction x`. -/
@[elab_as_elim, induction_eliminator, cases_eliminator]
protected def DegLex.rec {β : DegLex α → Sort*} (h : ∀ a, β (toDegLex a)) :
    ∀ a, β a := fun a => h (ofDegLex a)

@[simp] lemma DegLex.forall {p : DegLex α → Prop} : (∀ a, p a) ↔ ∀ a, p (toDegLex a) := Iff.rfl
@[simp] lemma DegLex.exists {p : DegLex α → Prop} : (∃ a, p a) ↔ ∃ a, p (toDegLex a) := Iff.rfl

namespace Finsupp

variable {M N : Type*} [AddCommMonoid M] [CanonicallyOrderedAddCommMonoid N]

/-- `Finsupp.DegLex r s` is the homogeneous lexicographic order on `α →₀ M`,
where `α` is ordered by `r` and `M` is ordered by `s`.
The type synonym `DegLex (α →₀ M)` has an order given by `Finsupp.DegLex (· < ·) (· < ·)`. -/
protected def DegLex (r : α → α → Prop) (s : ℕ → ℕ → Prop) :
    (α →₀ ℕ) → (α →₀ ℕ) → Prop :=
  (Prod.Lex s (Finsupp.Lex r s)) on (fun x ↦ (x.degree, x))

theorem degLex_def {r : α → α → Prop} {s : ℕ → ℕ → Prop} {a b : α →₀ ℕ} :
    Finsupp.DegLex r s a b ↔
      Prod.Lex s (Finsupp.Lex r s) (a.degree, a) (b.degree, b) :=
  Iff.rfl

theorem DegLex.wellFounded
    {r : α → α → Prop} [IsTrichotomous α r] (hr : WellFounded (Function.swap r))
    {s : ℕ → ℕ → Prop} (hs : WellFounded s) (hs0 : ∀ ⦃n⦄, ¬ s n 0) :
    WellFounded (Finsupp.DegLex r s) := by
  have wft := WellFounded.prod_lex hs (Finsupp.Lex.wellFounded' hs0 hs hr)
  rw [← Set.wellFoundedOn_univ] at wft
  unfold Finsupp.DegLex
  rw [← Set.wellFoundedOn_range]
  exact Set.WellFoundedOn.mono wft (le_refl _) (fun _ _ ↦ trivial)

instance [LT α] : LT (DegLex (α →₀ ℕ)) :=
  ⟨fun f g ↦ Finsupp.DegLex (· < ·) (· < ·) (ofDegLex f) (ofDegLex g)⟩

theorem DegLex.lt_def [LT α] {a b : DegLex (α →₀ ℕ)} :
    a < b ↔ (toLex ((ofDegLex a).degree, toLex (ofDegLex a))) <
        (toLex ((ofDegLex b).degree, toLex (ofDegLex b))) :=
  Iff.rfl

theorem DegLex.lt_iff [LT α] {a b : DegLex (α →₀ ℕ)} :
    a < b ↔ (ofDegLex a).degree < (ofDegLex b).degree ∨
    (((ofDegLex a).degree = (ofDegLex b).degree) ∧ toLex (ofDegLex a) < toLex (ofDegLex b)) := by
  simp only [Finsupp.DegLex.lt_def, Prod.Lex.lt_iff]

noncomputable instance : AddCommMonoid (DegLex (α →₀ ℕ)) := ofDegLex.addCommMonoid

theorem toDegLex_add (a b : α →₀ ℕ) : toDegLex (a + b) = toDegLex a + toDegLex b := rfl

theorem ofDegLex_add (a b : DegLex (α →₀ ℕ)) : ofDegLex (a + b) = ofDegLex a + ofDegLex b := rfl

variable [LinearOrder α]

instance DegLex.isStrictOrder : IsStrictOrder (DegLex (α →₀ ℕ)) (· < ·) :=
  { irrefl := fun a ↦ by simp [DegLex.lt_def]
    trans := by
      intro a b c hab hbc
      simp only [DegLex.lt_iff] at hab hbc ⊢
      rcases hab with (hab | hab)
      · rcases hbc with (hbc | hbc)
        · left; exact lt_trans hab hbc
        · left; exact lt_of_lt_of_eq hab hbc.1
      · rcases hbc with (hbc | hbc)
        · left; exact lt_of_eq_of_lt hab.1 hbc
        · right; exact ⟨Eq.trans hab.1 hbc.1, lt_trans hab.2 hbc.2⟩ }

/-- The partial order on `Finsupp`s obtained by the homogeneous lexicographic ordering.
See `Finsupp.DegLex.linearOrder` for a proof that this partial order is in fact linear. -/
instance DegLex.partialOrder : PartialOrder (DegLex (α →₀ ℕ)) :=
  PartialOrder.lift
    (fun (f : DegLex (α →₀ ℕ)) ↦ toLex ((ofDegLex f).degree, toLex (ofDegLex f)))
    (fun f g ↦ by simp)

theorem DegLex.le_iff {x y : DegLex (α →₀ ℕ)} :
    x ≤ y ↔ (ofDegLex x).degree < (ofDegLex y).degree ∨
      (ofDegLex x).degree = (ofDegLex y).degree ∧ toLex (ofDegLex x) ≤ toLex (ofDegLex y) := by
  simp only [le_iff_eq_or_lt, DegLex.lt_iff, EmbeddingLike.apply_eq_iff_eq]
  by_cases h : x = y
  · simp [h]
  · by_cases k : (ofDegLex x).degree < (ofDegLex y).degree
    · simp [k]
    · simp only [h, k, false_or]

theorem _root_.Finsupp.degree_add {α : Type*} (a b : α →₀ ℕ) :
    (a + b).degree = a.degree + b.degree := 
  sum_add_index' (h := fun _ ↦ id) (congrFun rfl) fun _ _ ↦ congrFun rfl

noncomputable instance : OrderedCancelAddCommMonoid (DegLex (α →₀ ℕ)) where
  toAddCommMonoid := ofDegLex.addCommMonoid
  toPartialOrder := DegLex.partialOrder
  le_of_add_le_add_left a b c h := by
    rw [DegLex.le_iff] at h ⊢
    simpa only [ofDegLex_add, degree_add, add_lt_add_iff_left, add_right_inj, toLex_add,
      add_le_add_iff_left] using h
  add_le_add_left a b h c := by
    rw [DegLex.le_iff] at h ⊢
    simpa [ofDegLex_add, degree_add] using h

/-- The linear order on `Finsupp`s obtained by the homogeneous lexicographic ordering. -/
instance DegLex.linearOrder : LinearOrder (DegLex (α →₀ ℕ)) :=
  LinearOrder.lift'
    (fun (f : DegLex (α →₀ ℕ)) ↦ toLex ((ofDegLex f).degree, toLex (ofDegLex f)))
    (fun f g ↦ by simp)

/-- The linear order on `Finsupp`s obtained by the homogeneous lexicographic ordering. -/
noncomputable instance :
    LinearOrderedCancelAddCommMonoid (DegLex (α →₀ ℕ)) where
  toOrderedCancelAddCommMonoid := inferInstance
  le_total := DegLex.linearOrder.le_total
  decidableLE := DegLex.linearOrder.decidableLE
  min_def := DegLex.linearOrder.min_def
  max_def := DegLex.linearOrder.max_def
  compare_eq_compareOfLessAndEq := DegLex.linearOrder.compare_eq_compareOfLessAndEq

theorem DegLex.monotone_degree :
    Monotone (fun (x : DegLex (α →₀ ℕ)) ↦ (ofDegLex x).degree) := by
  intro x y
  rw [DegLex.le_iff]
  rintro (h | h)
  · apply le_of_lt h
  · apply le_of_eq h.1

instance DegLex.orderBot : OrderBot (DegLex (α →₀ ℕ)) where
  bot := toDegLex (0 : α →₀ ℕ)
  bot_le x := by
    simp only [DegLex.le_iff, ofDegLex_toDegLex, toLex_zero, degree_zero]
    rcases eq_zero_or_pos (ofDegLex x).degree with (h | h)
    · simp only [h, lt_self_iff_false, true_and, false_or, ge_iff_le]
      exact bot_le
    · simp [h]

instance DegLex.wellFoundedLT [WellFoundedGT α] :
    WellFoundedLT (DegLex (α →₀ ℕ)) :=
  ⟨DegLex.wellFounded wellFounded_gt wellFounded_lt fun n ↦ (zero_le n).not_lt⟩

/-- The RevLex order on monomials -/
noncomputable def MonomialOrder.degLex (σ : Type*) [LinearOrder σ] [WellFoundedGT σ] :
    MonomialOrder σ where
  syn := DegLex (σ →₀ ℕ)
  locacm := inferInstance
  toSyn := { toEquiv := toDegLex, map_add' := toDegLex_add }
  wf := DegLex.wellFoundedLT
  toSyn_monotone a b h := by
    change toDegLex a ≤ toDegLex b
    simp only [DegLex.le_iff, ofDegLex_toDegLex]
    by_cases ha : a.degree < b.degree
    · exact Or.inl ha
    · refine Or.inr ⟨le_antisymm ?_ (not_lt.mp ha), toLex_monotone h⟩
      rw [← add_tsub_cancel_of_le h, degree_add]
      exact Nat.le_add_right a.degree (b - a).degree

theorem MonomialOrder.degLex_lt_iff {σ : Type*} [LinearOrder σ] [WellFoundedGT σ] 
    {a b : σ →₀ ℕ} : 
    (MonomialOrder.degLex σ).toSyn a < (MonomialOrder.degLex σ).toSyn b 
      ↔ toDegLex a < toDegLex b :=
  Iff.rfl

/-- The degRevLex order on monomials -/
noncomputable def MonomialOrder.degRevLex (σ : Type*) [LinearOrder σ] [WellFoundedLT σ] :
    MonomialOrder σ :=
  MonomialOrder.degLex σᵒᵈ

end Finsupp

end degLex

section Dickson

/-- A subset `B` of a set `S` in a preordered type is a basis
if any element of `S` is larger than some element of `B`  -/
def Set.isBasis {α : Type*} [Preorder α] (S B : Set α) : Prop :=
  B ⊆ S ∧ ∀ x ∈ S, ∃ y ∈ B, y ≤ x

/-- A preordered type has the Dickson property if any set contains a finite basis -/
def Preorder.isDickson (α : Type*) [Preorder α] : Prop :=
  ∀ (S : Set α), ∃ (B : Set α), S.isBasis B ∧ Finite B

open Preorder

variable {α : Type*} [Preorder α]

theorem Equiv.isDickson_of_monotone {β : Type*} [Preorder β] (f : α ≃ β) (hf : Monotone f)
  (H : isDickson α) :
  isDickson β := fun S ↦ by
  obtain ⟨B, hB, hB'⟩ := H (S.preimage f)
  use f '' B
  refine ⟨?_, Finite.Set.finite_image B ⇑f⟩
  refine ⟨Set.image_subset_iff.mpr hB.1, ?_⟩
  intro x hx
  obtain ⟨b, hb, hbx⟩ :=
    hB.2 (f.symm x) (by simp only [Set.mem_preimage, Equiv.apply_symm_apply, hx])
  use f b
  refine ⟨Set.mem_image_of_mem (⇑f) hb, ?_⟩
  convert hf hbx
  simp only [Equiv.apply_symm_apply]

theorem exists_lt_and_le_of_isDickson (H : isDickson α) (a : ℕ → α) :
    ∃ i j, i < j ∧ a i ≤ a j := by
  obtain ⟨B, hB, hB'⟩ := H (Set.range a)
  let B' : Set ℕ := a.invFun '' B
  have hB'' : Finite B' := Finite.Set.finite_image B (Function.invFun a)
  have : ∃ n, ∀ c ∈ B', c ≤ n := Set.exists_upper_bound_image B' (fun b ↦ b) hB''
  obtain ⟨n, hn⟩ := this
  obtain ⟨b, hb, hb'⟩ := hB.2 (a (n + 1)) (Set.mem_range_self _)
  use a.invFun b, n + 1
  constructor
  · apply Nat.lt_add_one_of_le
    exact hn _ (Set.mem_image_of_mem (Function.invFun a) hb)
  · convert hb'
    apply Function.invFun_eq
    rw [← Set.mem_range]
    exact hB.1 hb

-- TODO : Generalize to `PreOrder α`
-- This means that the conclusion should take place 
-- in the quotient partial order associated with the preorder.
theorem minimal_ne_and_finite_of {α : Type*} [PartialOrder α]
    (H : ∀ a : ℕ → α, ∃ i j, i < j ∧ a i ≤ a j) (S : Set α) (hSne : S.Nonempty) :
    let M := {x ∈ S | Minimal (fun x ↦ x ∈ S) x}
    M.Nonempty ∧ M.Finite := by
  constructor
  · by_contra hM
    rw [Set.not_nonempty_iff_eq_empty] at hM
    by_cases hS : S.Finite
    · -- in a finite set, there are minimal elements
      obtain ⟨x, hx, hxm⟩ :=  Set.Finite.exists_minimal_wrt id S hS hSne
      simp only [Set.sep_eq_empty_iff_mem_false] at hM
      exact hM x hx (minimal_iff.mpr ⟨hx, hxm⟩)
    · have : ∀ x : S, ∃ y : S, (y : α) < x := by
        rintro ⟨x, hx⟩
        simp only [Set.sep_eq_empty_iff_mem_false] at hM
        by_contra hx'
        push_neg at hx'
        apply hM x hx
        unfold Minimal
        refine ⟨hx, ?_⟩
        intro y hy
        rw [le_iff_eq_or_lt]
        rintro (hyx | hyx)
        · exact le_of_eq hyx.symm
        · exfalso
          exact hx' ⟨y,hy⟩ hyx
      obtain ⟨a0, ha0⟩ := hSne
      let a : ℕ → S := Nat.rec ⟨a0, ha0⟩ fun _ x ↦ (this x).choose
      have ha : ∀ n, (a (n + 1)).val < (a n).val := fun n ↦ (this (a n)).choose_spec
      obtain ⟨i, j, H, H'⟩ := H (fun n ↦ (a n).val)
      rw [← lt_self_iff_false (a i)]
      exact lt_of_le_of_lt  H' (strictAnti_nat_of_succ_lt ha H)
  · rw [← Set.not_infinite]
    intro hM
    obtain ⟨a, ha⟩ := Set.Infinite.natEmbedding _ hM
    obtain ⟨i, j, h, H⟩ := H (fun n ↦ a n)
    simp only [Set.mem_setOf_eq, Subtype.coe_le_coe] at H
    exact ne_of_lt h <| ha <| le_antisymm H ((a j).prop.2.2 (a i).prop.1 H)

-- Unless the equivalence classes for the preorder are finite,
-- the assumption is often meaningless
-- TODO : Generalize to `PartialOrder α`
theorem isDickson_of_minimal_ne_and_finite 
    (H : ∀ (S : Set α) (_ : S.Nonempty), { x ∈ S | Minimal (fun x ↦ x ∈ S) x}.Nonempty
        ∧ {x ∈ S | Minimal (fun x ↦ x ∈ S) x}.Finite) :
    isDickson α := by
  intro S
  let B := {x ∈ S | Minimal (fun x ↦ x ∈ S) x}
  have hBS : B ⊆ S := Set.sep_subset S (Minimal fun x ↦ x ∈ S)
  use B
  by_cases hS : S.Nonempty
  · have := H S hS
    refine ⟨⟨hBS, ?_⟩, (H S hS).2⟩
    intro a ha
    let S' := {x ∈ S | x ≤ a}
    have := H S' ⟨a, by simp [S', ha]⟩
    obtain ⟨b, hb, hb'⟩ := this.1
    refine ⟨b, ?_, hb.2⟩
    simp only [B]
    refine ⟨hb.1, ?_⟩
    -- apply hb'.mono  ?_ (Set.mem_of_mem_inter_left hb)
    unfold Minimal
    refine ⟨Set.mem_of_mem_inter_left hb, ?_⟩
    intro y hy hyb
    exact hb'.2 ⟨hy, le_trans hyb hb.2⟩ hyb
  · rw [Set.not_nonempty_iff_eq_empty] at hS
    have hB : B = ∅ := Set.subset_eq_empty hBS hS
    constructor
    exact ⟨hBS, by simp [hS]⟩ 
    simp [hB, Finite.of_fintype]

-- TODO : Generalize to `Preorder α`
/-- Becker-Weispfenning, Proposition 4.42 -/
theorem isDickson_tfae (α : Type*) [PartialOrder α] : List.TFAE [
    isDickson α,
    ∀ (a : ℕ → α), ∃ i j, i < j ∧ a i ≤ a j,
    ∀ (S : Set α) (_ : S.Nonempty), { x ∈ S | Minimal (fun x ↦ x ∈ S) x}.Nonempty
        ∧ {x ∈ S | Minimal (fun x ↦ x ∈ S) x}.Finite] := by
  tfae_have 1 → 2
  · exact exists_lt_and_le_of_isDickson
  tfae_have 2 → 3
  · exact  minimal_ne_and_finite_of
  tfae_have 3 → 1
  · exact isDickson_of_minimal_ne_and_finite
  tfae_finish

/-
lemma _root_.Set.Infinite.exists_extraction
  {S : Set ℕ} (hS : S.Infinite) : ∃ n : ℕ → ℕ, StrictMono n ∧ Set.range n = S := by
  use Nat.nth (fun x ↦ x ∈ S), Nat.nth_strictMono hS, Nat.range_nth_of_infinite hS
  -/

theorem isDickson_iff_exists_monotone (α : Type*) [PartialOrder α] :
    isDickson α ↔ ∀ (a : ℕ → α), ∃ (n : ℕ → ℕ), StrictMono n ∧ Monotone (a ∘ n) := by
  constructor
  · intro H a
    have H' : ∀ (S : Set ℕ) (_ : S.Infinite), ∃ s ∈ S, ∃ T, 
        T.Infinite ∧ T ⊆ S ∧ (∀ t ∈ T, s < t ∧ a s ≤ a t):= by
      intro S hS
      obtain ⟨B, hB, hBf⟩ := H (a '' S)
      let f (b) := {n ∈ S | b ≤ a n}
      have : ⋃ b ∈ B, f b = S := by 
        ext n
        constructor
        · simp only [Set.mem_iUnion, exists_prop, forall_exists_index, and_imp]
          intro b _ hn
          exact hn.1
        · intro hnS
          obtain ⟨b, hb, hb_le⟩:= hB.2 (a n) (Set.mem_image_of_mem a hnS)
          exact Set.mem_biUnion hb ⟨hnS, hb_le⟩
      have : ∃ b ∈ B, (f b).Infinite := by
        by_contra h
        push_neg at h
        simp only [Set.not_infinite] at h
        apply hS
        rw [← this]
        exact Set.Finite.biUnion' hBf h
      obtain ⟨b, hbB, hb⟩ := this
      obtain ⟨q, hqS, hqb⟩ := (Set.mem_image _ _ _).mpr (hB.1 hbB)
      use q, hqS, {n | n ∈ S ∧ b ≤ a n ∧ q < n}
      refine ⟨?_, Set.sep_subset S _, fun x ht ↦ ⟨ht.2.2, hqb ▸ ht.2.1⟩⟩
      -- this set is infinite
      simp_rw [← and_assoc]
      change ({n | n ∈ S ∧ b ≤ a n} ∩ {n | q < n}).Infinite
      rw [← Set.diff_compl]
      apply Set.Infinite.diff hb
      rw [Set.compl_setOf]
      simp_rw [not_lt]
      exact Set.finite_le_nat q
    obtain ⟨s0, _, S0, hS0⟩ := H' Set.univ Set.infinite_univ
    let v : ℕ → {(s, S) : ℕ × Set ℕ | S.Infinite ∧ ∀ x ∈ S, s < x ∧ a s ≤ a x} := 
      Nat.rec (⟨(s0, S0), ⟨hS0.1, hS0.2.2⟩⟩) (fun _ sS ↦ by 
        let t := (H' sS.val.2 sS.prop.1).choose
        let T := (H' sS.val.2 sS.prop.1).choose_spec.2.choose
        let hT : T.Infinite ∧ T ⊆ sS.val.2 ∧ ∀ x ∈ T, t < x ∧ a t ≤ a x := 
          (H' sS.val.2 sS.prop.1).choose_spec.2.choose_spec
        exact ⟨(t, T), ⟨hT.1, hT.2.2⟩⟩)
    let n (k) := (v k).val.1
    let S (k) := (v k).val.2
    have hS (k) : (S k).Infinite := (v k).prop.1
    have hn (k) : ∀ x ∈ S k, n k < x ∧ a (n k) ≤ a x := (v k).prop.2
    have hn_mem_S (k) : n k.succ ∈ S k := (H' (S k) (hS k)).choose_spec.1 
    use n
    constructor
    · apply strictMono_nat_of_lt_succ
      exact fun k ↦ (hn k (n (k + 1)) (hn_mem_S k)).1
    · apply monotone_nat_of_le_succ
      exact fun k ↦ (hn k (n (k + 1)) (hn_mem_S k)).2
  · intro H
    simp only [List.TFAE.out (isDickson_tfae _) 0 1]
    intro a
    obtain ⟨n, hn, han⟩ := H a
    exact ⟨n 0, n 1, hn Nat.one_pos, han (Nat.zero_le 1)⟩

/-
theorem wellFounded_iff_not_exists {α : Type*} (r : α → α → Prop) :
    WellFounded r ↔ ¬ ∃ (a : ℕ → α), ∀ n, r (a (n + 1)) (a n) := by
  constructor
  · intro H 
    suffices ∀ a, ¬ ∃ (u : ℕ → α), u 0 = a ∧ ∀ n, r (u (n + 1)) (u n) by
      intro Ha
      obtain ⟨u, hu⟩ := Ha
      exact this (u 0) ⟨u, rfl, hu⟩
    intro  a
    induction a using WellFounded.induction H with
    | _ a Ha => 
    rintro ⟨u, hua, hu⟩
    apply Ha (u 1)
    simp only [← hua, hu 0]
    use fun n ↦ u (n + 1)
    simp only [zero_add, true_and]
    intro n 
    exact hu (n + 1)
  · intro H
    apply WellFounded.intro
    intro a
    by_contra ha
    apply H
    let u : ℕ → {x | ¬ Acc r x} := 
      Nat.rec ⟨a, ha⟩ (fun _ x ↦ ⟨(RelEmbedding.exists_not_acc_lt_of_not_acc x.prop).choose,
        (RelEmbedding.exists_not_acc_lt_of_not_acc x.prop).choose_spec.1⟩)
    use fun n ↦ (u n).val
    intro n
    exact (RelEmbedding.exists_not_acc_lt_of_not_acc (u n).prop).choose_spec.2
-/

theorem WellFoundedLT.isDickson {α : Type*} [LinearOrder α] [WellFoundedLT α] : 
    isDickson α := fun S ↦ by
  by_cases hS : S.Nonempty
  · obtain ⟨a, haS, ha⟩ := WellFounded.has_min wellFounded_lt S hS
    use {a}
    constructor
    · unfold Set.isBasis
      constructor
      simp [haS]
      intro x hx 
      use a
      simp_rw [not_lt] at ha
      simp [ha x hx]
    · exact Finite.of_fintype _
  · use ∅
    constructor
    unfold Set.isBasis
    constructor
    · exact Set.empty_subset S
    · simp only [Set.not_nonempty_iff_eq_empty] at hS
      simp [hS]
    exact Finite.of_fintype _

theorem isDickson.wf {α : Type*} [PartialOrder α] (H : isDickson α) : WellFoundedLT α := by
  unfold WellFoundedLT
  apply IsWellFounded.mk
  rw [RelEmbedding.wellFounded_iff_no_descending_seq]
  apply IsEmpty.mk
  rintro ⟨a, ha⟩
  have := List.TFAE.out (isDickson_tfae α) 0 1
  rw [this] at H
  obtain ⟨i, j, hij, H⟩ := H a
  exact ne_of_lt (lt_of_le_of_lt H (ha.mpr hij)) rfl
  
theorem Finsupp.isDickson_equiv {α β : Type*} (e : α ≃ β) (hα : isDickson (α →₀ ℕ)) :
    isDickson (β →₀ ℕ) := by
  apply Equiv.isDickson_of_monotone (equivCongrLeft e) _ hα
  exact fun a b h d ↦ by simp [h (e.symm d)]

theorem isDickson_prod {α β : Type*} [PartialOrder α] [PartialOrder β]
    (hα : isDickson α) (hβ : isDickson β) : 
    isDickson (α × β) := by
  simp only [List.TFAE.out (isDickson_tfae _) 0 1] 
  intro a
  simp only [isDickson_iff_exists_monotone] at hα hβ
  obtain ⟨m, hm, ha1⟩ := hα (fun k ↦ (a k).1)
  obtain ⟨n, hn, ha2⟩ := hβ (fun k ↦ (a (m k)).2)
  use m (n 0), m (n 1)
  constructor
  exact hm (hn zero_lt_one)
  simp only [Prod.le_def]
  constructor
  · apply ha1 
    exact hn.monotone zero_le_one
  · apply ha2 zero_le_one

theorem Nat.isDickson : isDickson ℕ := WellFoundedLT.isDickson

theorem Fin.isDickson_nat (n : ℕ) : isDickson (Fin n → ℕ) := by
  induction n with
  | zero => exact fun S ↦ ⟨S,⟨⟨subset_rfl, fun x hx ↦ ⟨x, hx, le_rfl⟩⟩, Subtype.finite⟩⟩
  | succ n h => 
      apply Equiv.isDickson_of_monotone (Fin.snocEquiv (fun _ ↦ ℕ))
      · intro a b h i
        rw [Prod.le_def] at h
        simp only [snocEquiv_apply]
        rcases i.eq_castSucc_or_eq_last with (hi | hi)
        · obtain ⟨j, rfl⟩ := hi
          simp only [snoc_castSucc, ge_iff_le, h.2 j]
        · simp only [hi, snoc_last, h.1]
      · exact isDickson_prod Nat.isDickson h

theorem Finsupp.isDickson_nat (n : ℕ) : isDickson (Fin n →₀ ℕ) := by
  let e : (Fin n → ℕ) ≃ (Fin n →₀ ℕ) := equivFunOnFinite.symm
  apply Equiv.isDickson_of_monotone e (fun x y h i ↦ by exact h i) (Fin.isDickson_nat n)

theorem Finsupp.isDickson (σ : Type*) [Finite σ] : isDickson (σ →₀ ℕ) := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin σ
  exact Finsupp.isDickson_equiv e.symm (Finsupp.isDickson_nat n)

end Dickson
