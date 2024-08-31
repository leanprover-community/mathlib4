import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Data.Finsupp.Lex

/-! # Groebner bases -/


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
 
example {α : Type*} [PartialOrder α] 
    (H : ∀ a : ℕ → α, ∃ i j, i < j ∧ a i ≤ a j) (S : Set α) (hSne : S.Nonempty) :
    let M := {x ∈ S | Minimal (fun x ↦ x ∈ S) x}
    M.Nonempty ∧ M.Finite := by
  constructor
  · by_contra hM
    rw [Set.not_nonempty_iff_eq_empty] at hM
    by_cases hS : S.Finite
    · -- in a finite set, there are minimal elements
      sorry
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
      let a : ℕ → S := sorry
      have ha : ∀ n, (a (n + 1) : α) < a n := sorry
      obtain ⟨i, j, H, H'⟩ := H (fun n ↦ a n)
      rw [← lt_self_iff_false (a i)]
      exact lt_of_le_of_lt  H' (strictAnti_nat_of_succ_lt ha H)
  · rw [← Set.not_infinite]
    intro hM
    obtain ⟨a, ha⟩ := Set.Infinite.natEmbedding _ hM
    obtain ⟨i, j, h, H⟩ := H (fun n ↦ a n)
    simp only [Set.mem_setOf_eq, Subtype.coe_le_coe] at H
    apply ne_of_lt h
    apply ha
    apply le_antisymm H
    have := (a j).prop.2
    exact this.2 (a i).prop.1 H

    
theorem isDickson_tfae (α : Type*) [PartialOrder α] : List.TFAE [
    isDickson α,
    ∀ (a : ℕ → α), ∃ i j, i < j ∧ a i ≤ a j,
    ∀ (S : Set α) (hSne : S.Nonempty), { x ∈ S | Minimal (fun x ↦ x ∈ S) x}.Nonempty 
        ∧ {x ∈ S | Minimal (fun x ↦ x ∈ S) x}.Finite] := by
  sorry

theorem isDickson.wf {α : Type*} [PartialOrder α] (H : isDickson α) : WellFoundedLT α := sorry

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

variable {σ : Type*} [Finite σ] (m : MonomialOrder σ) {R : Type*} [CommRing R]

notation:25 f "≺[" m:25 "]" g => MonomialOrder.toSyn m f < MonomialOrder.toSyn m g 

notation:25 f "≼[" m:25 "]" g => MonomialOrder.toSyn m f ≤ MonomialOrder.toSyn m g 

/-- the degree of a multivariate polynomial with respect to a monomial ordering -/
def monomialOrderDegree (m : MonomialOrder σ) (f : MvPolynomial σ R) : σ →₀ ℕ := 
    m.toSyn.symm (f.support.sup m.toSyn)

variable (m : MonomialOrder σ)

theorem monomialOrderDegree_eq_zero_iff {m : MonomialOrder σ} {f : MvPolynomial σ R} :
    f.monomialOrderDegree m = 0 ↔ f.totalDegree = 0 := by sorry

theorem monomialOrderDiv (B : Set (MvPolynomial σ R)) (f : MvPolynomial σ R) : 
    ∃ g r, f = g + r ∧ g ∈ Ideal.span B ∧ 
      (r = 0 ∨ ∀ b ∈ B, r.monomialOrderDegree m ≺[m] b.monomialOrderDegree m) :=
    sorry

end MvPolynomial
