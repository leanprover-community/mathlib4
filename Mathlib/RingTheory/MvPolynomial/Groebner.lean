import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Lex
import Mathlib.Data.List.TFAE

/-! # Groebner bases 

Reference : [Becker-Weispfenning1993] -/


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
    have : ∀ a (_ : ¬ Acc r a), ∃ b, r b a ∧ ¬ Acc r b := fun a ha ↦ by
      revert ha
      rw [not_imp_comm]
      intro H'
      push_neg at H'
      exact Acc.intro a H'
    apply WellFounded.intro
    intro a
    by_contra ha
    apply H
    let u : ℕ → {x | ¬ Acc r x} := 
      Nat.rec ⟨a, ha⟩ (fun _ x ↦ ⟨(this x.val x.prop).choose, (this x.val x.prop).choose_spec.2⟩)
    use fun n ↦ (u n).val
    intro n
    exact (this (u n).val (u n).prop).choose_spec.1

    
theorem isDickson.wf {α : Type*} [PartialOrder α] (H : isDickson α) : WellFoundedLT α := by
  unfold WellFoundedLT
  apply IsWellFounded.mk
  rw [wellFounded_iff_not_exists]
  rintro ⟨a, ha⟩
  have := List.TFAE.out (isDickson_tfae α) 0 1
  rw [this] at H
  obtain ⟨i, j, hij, H⟩ := H a
  exact ne_of_lt (lt_of_le_of_lt H (strictAnti_nat_of_succ_lt ha hij)) rfl
  
theorem Finsupp.isDickson (σ : Type*) [Finite σ] : isDickson (σ →₀ ℕ) := sorry

end Dickson

namespace Finsupp

open Preorder

structure MonomialOrder (σ : Type*) where
  syn : Type*
  clacm : CanonicallyLinearOrderedAddCommMonoid syn
  toSyn : (σ →₀ ℕ) ≃+ syn

instance (σ : Type*) (m : MonomialOrder σ) : CanonicallyLinearOrderedAddCommMonoid m.syn := m.clacm

variable {σ : Type*} (m : MonomialOrder σ)

lemma MonomialOrder.toSyn_monotone : Monotone (m.toSyn) := by
  intro a b h
  have : b = a + (b - a) := by
    ext s
    simp only [coe_add, coe_tsub, Pi.add_apply, Pi.sub_apply]
    rw [add_tsub_cancel_of_le (h s)]
  rw [this, map_add]
  exact le_self_add

theorem MonomialOrder.bot_eq : ⊥ = m.toSyn 0 := by
  simp only [bot_eq_zero', map_zero]

lemma MonomialOrder.toSyn_strictMono : StrictMono (m.toSyn) := by
  apply m.toSyn_monotone.strictMono_of_injective m.toSyn.injective

theorem MonomialOrder.isDickson {σ : Type*} [Finite σ] (m : MonomialOrder σ) :
    Preorder.isDickson m.syn  :=
  m.toSyn.isDickson_of_monotone m.toSyn_monotone (Finsupp.isDickson σ)

theorem MonomialOrder.wf {σ : Type*} [Finite σ] (m : MonomialOrder σ) :
    WellFoundedLT m.syn :=
  isDickson.wf (isDickson m)

end Finsupp

namespace MvPolynomial

open Finsupp

variable {σ : Type*} (m : MonomialOrder σ) {R : Type*} [CommRing R]

notation:25 c "≺[" m:25 "]" d:25 => (MonomialOrder.toSyn m c < MonomialOrder.toSyn m d)

notation:25 c "≼[" m:25 "]" d:25 => (MonomialOrder.toSyn m c ≤ MonomialOrder.toSyn m d)

/-- the degree of a multivariate polynomial with respect to a monomial ordering -/
def monomialOrderDegree (m : MonomialOrder σ) (f : MvPolynomial σ R) : σ →₀ ℕ :=
  m.toSyn.symm (f.support.sup m.toSyn)

/-- the leading coefficient of a multivariate polynomial with respect to a monomial ordering -/
def monomialOrderLCoeff (m : MonomialOrder σ) (f : MvPolynomial σ R) : R :=
  f.coeff (f.monomialOrderDegree m)

variable (m : MonomialOrder σ)

@[simp]
theorem monomialOrderDegree_zero {m : MonomialOrder σ} : 
    monomialOrderDegree m (0 : MvPolynomial σ R) = 0 := by
  simp [monomialOrderDegree]

@[simp]
theorem monomialOrderLCoeff_zero {m : MonomialOrder σ} : 
    monomialOrderLCoeff m (0 : MvPolynomial σ R) = 0 := by
  simp [monomialOrderDegree, monomialOrderLCoeff]

theorem monomialOrderDegree_monomial_le {m : MonomialOrder σ} {d : σ →₀ ℕ} (c : R) :
    monomialOrderDegree m (monomial d c) ≼[m] d := by
  simp only [monomialOrderDegree, AddEquiv.apply_symm_apply]
  apply le_trans (Finset.sup_mono support_monomial_subset)
  simp only [Finset.sup_singleton, le_refl]

theorem monomialOrderDegree_monomial {m : MonomialOrder σ} {d : σ →₀ ℕ}
    (c : R) [Decidable (c = 0)] :
    monomialOrderDegree m (monomial d c) = if c = 0 then 0 else d := by
  simp only [monomialOrderDegree, support_monomial]
  split_ifs with hc <;> simp

@[simp]
theorem monomialOrderLCoeff_monomial {m : MonomialOrder σ} {d : σ →₀ ℕ} (c : R) :
    monomialOrderLCoeff m (monomial d c) = c := by
  classical
  simp only [monomialOrderLCoeff, monomialOrderDegree_monomial]
  split_ifs with hc <;> simp [hc]

theorem monomialOrderDegree_le_iff {m : MonomialOrder σ} {f : MvPolynomial σ R} {d : σ →₀ ℕ} :
    f.monomialOrderDegree m ≼[m] d ↔ ∀ c ∈ f.support, c ≼[m] d := by
  unfold monomialOrderDegree
  simp only [AddEquiv.apply_symm_apply, Finset.sup_le_iff, mem_support_iff, ne_eq]

theorem monomialOrderDegree_lt_iff {m : MonomialOrder σ} {f : MvPolynomial σ R} {d : σ →₀ ℕ} 
    (hd : 0 ≺[m] d) :
    f.monomialOrderDegree m ≺[m] d ↔ ∀ c ∈ f.support, c ≺[m] d := by
  unfold monomialOrderDegree
  simp only [AddEquiv.apply_symm_apply]
  apply Finset.sup_lt_iff
  convert hd
  rw [bot_eq_zero, map_zero]

theorem le_monomialOrderDegree {m : MonomialOrder σ} {f : MvPolynomial σ R} {d : σ →₀ ℕ}
    (hd : d ∈ f.support) : d ≼[m] f.monomialOrderDegree m := by
  unfold monomialOrderDegree
  simp only [AddEquiv.apply_symm_apply, Finset.le_sup hd]

theorem coeff_eq_zero_of_lt {m : MonomialOrder σ} {f : MvPolynomial σ R} {d : σ →₀ ℕ} 
    (hd : monomialOrderDegree m f ≺[m] d) :
    f.coeff d = 0 := by
  rw [← not_le] at hd
  by_contra hf
  apply hd (le_monomialOrderDegree (mem_support_iff.mpr hf))

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
theorem monomialOrderLCoeff_ne_zero_iff {m : MonomialOrder σ} {f : MvPolynomial σ R} :
    monomialOrderLCoeff m f ≠ 0 ↔ f ≠ 0 := by
  constructor
  · rw [not_imp_not]
    intro hf
    rw [hf, monomialOrderLCoeff_zero]
  · intro hf
    rw [← support_nonempty] at hf
    rw [monomialOrderLCoeff, ← mem_support_iff, monomialOrderDegree] 
    suffices f.support.sup m.toSyn ∈ m.toSyn '' f.support by 
      obtain ⟨d, hd, hd'⟩ := this
      rw [← hd', AddEquiv.symm_apply_apply]
      exact hd
    exact Finset.sup_mem_of_nonempty hf

@[simp]
theorem coeff_monomialOrderDegree_eq_zero_iff {m : MonomialOrder σ} {f : MvPolynomial σ R} :
    monomialOrderLCoeff m f = 0 ↔ f = 0 := by
  simp only [← not_iff_not, monomialOrderLCoeff_ne_zero_iff]

theorem monomialOrderDegree_eq_zero_iff_totalDegree_eq_zero
    {m : MonomialOrder σ} {f : MvPolynomial σ R} :
    f.monomialOrderDegree m = 0 ↔ f.totalDegree = 0 := by 
  rw [← m.toSyn.injective.eq_iff]
  rw [map_zero, ← nonpos_iff_eq_zero, ← m.toSyn.map_zero, monomialOrderDegree_le_iff]
  simp only [map_zero, nonpos_iff_eq_zero, AddEquivClass.map_eq_zero_iff]
  rw [totalDegree_eq_zero_iff]
  apply forall_congr'
  exact fun _ ↦ imp_congr (rfl.to_iff) (by simp [Finsupp.ext_iff])

theorem monomialOrderDegree_neg {f : MvPolynomial σ R} :
    (-f).monomialOrderDegree m = f.monomialOrderDegree m := by
  unfold monomialOrderDegree
  rw [support_neg]

theorem monomialOrderDegree_add_le {f g : MvPolynomial σ R} :
    m.toSyn ((f + g).monomialOrderDegree m) ≤ 
      m.toSyn (f.monomialOrderDegree m) ⊔ m.toSyn (g.monomialOrderDegree m) := by
  conv_rhs => rw [← m.toSyn.apply_symm_apply (_ ⊔ _)]
  rw [monomialOrderDegree_le_iff]
  simp only [AddEquiv.apply_symm_apply, le_sup_iff]
  intro b hb
  by_cases hf : b ∈ f.support
  · left
    exact le_monomialOrderDegree hf
  · right
    apply le_monomialOrderDegree
    simp only [not_mem_support_iff] at hf
    simpa only [mem_support_iff, coeff_add, hf, zero_add] using hb

theorem monomialOrderDegree_sub_le {f g : MvPolynomial σ R} :
    m.toSyn ((f - g).monomialOrderDegree m) ≤ 
      m.toSyn (f.monomialOrderDegree m) ⊔ m.toSyn (g.monomialOrderDegree m) := by
  rw [sub_eq_add_neg]
  apply le_of_le_of_eq (monomialOrderDegree_add_le m)
  rw [monomialOrderDegree_neg]

theorem monomialOrderDegree_add_of_lt {f g : MvPolynomial σ R}
    (h : g.monomialOrderDegree m ≺[m] f.monomialOrderDegree m) :
    (f + g).monomialOrderDegree m = f.monomialOrderDegree m := by
  apply m.toSyn.injective
  apply le_antisymm 
  · apply le_trans (monomialOrderDegree_add_le m)
    simp only [sup_le_iff, le_refl, true_and, le_of_lt h]
  · apply le_monomialOrderDegree
    rw [mem_support_iff, coeff_add, coeff_eq_zero_of_lt h, add_zero,
      ← monomialOrderLCoeff, monomialOrderLCoeff_ne_zero_iff]
    intro hf
    rw [← not_le, hf] at h
    apply h
    convert zero_le _
    simp only [monomialOrderDegree_zero, map_zero]

theorem monomialOrderDegree_add_of_ne {f g : MvPolynomial σ R}
    (h : f.monomialOrderDegree m ≠ g.monomialOrderDegree m) :
    m.toSyn ((f + g).monomialOrderDegree m) = 
      m.toSyn (f.monomialOrderDegree m) ⊔ m.toSyn (g.monomialOrderDegree m) := by
  by_cases h' : g.monomialOrderDegree m ≺[m] f.monomialOrderDegree m
  · simp only [monomialOrderDegree_add_of_lt m h', left_eq_sup, le_of_lt h']
  · rw [not_lt, le_iff_eq_or_lt, Classical.or_iff_not_imp_left, EmbeddingLike.apply_eq_iff_eq] at h'
    rw [add_comm, monomialOrderDegree_add_of_lt m (h' h), right_eq_sup]
    simp only [le_of_lt (h' h)]
    
theorem monomialOrderDegree_mul_le {f g : MvPolynomial σ R} :
    (f * g).monomialOrderDegree m ≼[m] f.monomialOrderDegree m + g.monomialOrderDegree m := by
  classical
  rw [monomialOrderDegree_le_iff]
  intro c 
  rw [← not_lt, mem_support_iff, not_imp_not]
  intro hc
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  rintro ⟨d, e⟩ hde
  simp only [Finset.mem_antidiagonal] at hde
  dsimp only
  by_cases hd : f.monomialOrderDegree m ≺[m] d
  · rw [coeff_eq_zero_of_lt hd, zero_mul]
  · suffices g.monomialOrderDegree m ≺[m] e by
      rw [coeff_eq_zero_of_lt this, mul_zero]
    simp only [not_lt] at hd
    apply lt_of_add_lt_add_left (a := m.toSyn d)
    simp only [← map_add, hde]
    apply lt_of_le_of_lt _ hc
    simp only [map_add]
    exact add_le_add_right hd _
    
theorem monomialOrderLCoeff' {f g : MvPolynomial σ R} :
    (f * g).coeff (f.monomialOrderDegree m + g.monomialOrderDegree m) 
      = f.monomialOrderLCoeff m * g.monomialOrderLCoeff m := by
  classical
  rw [coeff_mul]
  rw [Finset.sum_eq_single (f.monomialOrderDegree m, g.monomialOrderDegree m)]
  · rfl
  · rintro ⟨c, d⟩ hcd h
    simp only [Finset.mem_antidiagonal] at hcd
    by_cases hf : f.monomialOrderDegree m ≺[m] c
    · rw [coeff_eq_zero_of_lt hf, zero_mul]
    · suffices g.monomialOrderDegree m ≺[m] d by
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

theorem monomialOrderDegree_mul_eq [IsDomain R] {f g : MvPolynomial σ R} 
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).monomialOrderDegree m = f.monomialOrderDegree m + g.monomialOrderDegree m := by
  apply m.toSyn.injective
  apply le_antisymm (monomialOrderDegree_mul_le m)
  apply le_monomialOrderDegree 
  rw [mem_support_iff, monomialOrderLCoeff']
  simp [hf, hg]

theorem monomialOrderDegree_mul_eq' [IsDomain R] {f g : MvPolynomial σ R} (hfg : f * g ≠ 0) :
    (f * g).monomialOrderDegree m = f.monomialOrderDegree m + g.monomialOrderDegree m := 
  monomialOrderDegree_mul_eq _ (left_ne_zero_of_mul hfg) (right_ne_zero_of_mul hfg)

theorem monomialOrderLCoeff_mul [IsDomain R] {f g : MvPolynomial σ R} 
    (hf : f ≠ 0) (hg : g ≠ 0) :
    (f * g).monomialOrderLCoeff m = f.monomialOrderLCoeff m * g.monomialOrderLCoeff m := by
  rw [monomialOrderLCoeff, monomialOrderDegree_mul_eq m hf hg, ← monomialOrderLCoeff']

noncomputable example (B : Set (MvPolynomial σ R)) : B →₀ MvPolynomial σ R := 0

-- Maybe the statement is incorrect
theorem monomialOrderDiv [IsDomain R] (B : Set (MvPolynomial σ R)) 
    (hB : ∀ b ∈ B, IsUnit (b.monomialOrderLCoeff m)) (f : MvPolynomial σ R) :
    ∃ (g : B →₀ (MvPolynomial σ R)) (r : MvPolynomial σ R), 
      f = Finsupp.linearCombination _ (fun (b : B) ↦ (b : MvPolynomial σ R)) g + r ∧ 
        (∀ b, (b * (g b)).monomialOrderDegree m ≼[m] f.monomialOrderDegree m) ∧
        (∀ c ∈ r.support, ∀ b ∈ B, ¬ (b.monomialOrderDegree m ≤ c)) := by
  by_cases hf0 : f = 0
  · exact ⟨0, 0, by simp [hf0], fun _ ↦ by simp, by simp⟩
  by_cases hf : ∃ b ∈ B, b.monomialOrderDegree m ≤ f.monomialOrderDegree m
  · obtain ⟨b, hb, hf⟩ := hf
    let f' := f -  monomial 
      (f.monomialOrderDegree m - b.monomialOrderDegree m) 
      ((f.coeff (f.monomialOrderDegree m)) * (hB b hb).unit⁻¹) * b
    have : f'.monomialOrderDegree m ≺[m] f.monomialOrderDegree m := sorry
    obtain ⟨g', r', H'⟩ := monomialOrderDiv B hB f'
    use g' + Finsupp.single ⟨b, hb⟩ (monomial 
      (f.monomialOrderDegree m - b.monomialOrderDegree m) 
      ((f.coeff (f.monomialOrderDegree m)) * (hB b hb).unit⁻¹))
    use r'
    constructor
    · rw [map_add, add_assoc, add_comm _ r', ← add_assoc, ← H'.1]
      simp [f']
    constructor
    · rintro c
      simp
      rw [mul_add]
      apply le_trans (monomialOrderDegree_add_le m)
      simp only [sup_le_iff]
      constructor
      · apply le_trans (H'.2.1 _) (le_of_lt ?_)
        -- the monomialOrderDegree of f' is strictly smaller than that of f
        sorry
      · classical
        rw [single_apply]
        split_ifs with hc
        · apply le_trans (monomialOrderDegree_mul_le _)
          simp only [map_add]
          apply le_of_le_of_eq (add_le_add_left (monomialOrderDegree_monomial_le _) _)
          simp only [← hc]
          rw [add_tsub_cancel_of_le]
          sorry
        · simp
    · exact H'.2.2
  · push_neg at hf
    sorry
    

end MvPolynomial
