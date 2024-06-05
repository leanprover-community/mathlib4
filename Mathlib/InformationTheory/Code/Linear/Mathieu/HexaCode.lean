import Mathlib.InformationTheory.Code.Linear.Mathieu.F4
import Mathlib.InformationTheory.Code.Linear.TacticTmp.have_goal
import Mathlib.InformationTheory.Code.HammingCode
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Matrix.Reflection

open F4 BigOperators

abbrev F_4_6 := Fin 6 → F4
namespace HexaCode



def b₁ : F_4_6 := ![ω,ω⁻¹,ω⁻¹,ω,ω⁻¹,ω]
def b₂ : F_4_6 := ![ω⁻¹,ω,ω,ω⁻¹,ω⁻¹,ω]
def b₃ : F_4_6 := ![ω⁻¹,ω,ω⁻¹,ω,ω,ω⁻¹]

example : ω • b₁ + ω⁻¹ • b₂ = ![1,0,0,1,ω⁻¹,ω] := by
  simp_rw [b₁,b₂]
  simp only [Matrix.smul_cons, Matrix.smul_empty,smul_eq_mul]
  simp only [Matrix.add_cons, Matrix.empty_add_empty]
  simp only [Matrix.head_cons, Matrix.tail_cons]

  abel

example : ω⁻¹ • b₁ + ω⁻¹ • b₂ + b₃ = ![0,1,0,1,ω,ω⁻¹] := by
  simp_rw [b₁,b₂,b₃]
  simp only [Matrix.smul_cons, Matrix.smul_empty,smul_eq_mul]
  simp only [Matrix.add_cons, Matrix.empty_add_empty]
  simp only [Matrix.head_cons, Matrix.tail_cons]

  abel

example : b₂ + b₃ = ![0,0,1,1,1,1] := by
  simp_rw [b₂,b₃]
  -- simp only [Matrix.smul_cons, Matrix.smul_empty,smul_eq_mul]
  simp only [Matrix.add_cons, Matrix.empty_add_empty]
  simp only [Matrix.head_cons, Matrix.tail_cons]
  abel

abbrev hexaCodeBasis' : Fin 3 → F_4_6 := ![b₁,b₂,b₃]

/-
h = a • b₁ + b • b₂ + c • b₃ = ![a * ω + (b + c) * ω⁻¹,
                                 (b + c) * ω + a * ω⁻¹,
                                 b * ω + (a + c) * ω⁻¹,
                                 (a + c) * ω + b * ω⁻¹,
                                 c * ω + (a + b) * ω⁻¹,
                                 (a + b) * ω + c * ω⁻¹]

h 0 = h 4 + h 5


h 3 = h 1 + h 2

-/
lemma basis_indep : LinearIndependent F4 hexaCodeBasis' := by
  rw [ Fintype.linearIndependent_iff]
  intro g
  rw [Function.funext_iff]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
  intro h
  intro i
  fin_cases i
  . calc
      g 0
        = g 0 * (ω + ω⁻¹) + g 1 * (ω + ω) + g 2 * (ω⁻¹ + ω⁻¹) := by
        simp only [omega_add_omega_inv, mul_one, CharTwo.add_self_eq_zero, mul_zero, add_zero]
      _ = (∑ i, g i • hexaCodeBasis' i) ((0: Fin 1).succ.succ.succ.succ.succ) + (∑ i, g i • hexaCodeBasis' i) 2 := by
        simp_rw [Finset.univ,Fintype.elems,List.finRange]
        simp only [Fin.isValue, omega_add_omega_inv, mul_one, CharTwo.add_self_eq_zero, mul_zero,
          add_zero, List.pmap, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Nat.succ_eq_add_one,
          Nat.reduceAdd, Fin.succ_zero_eq_one, Fin.succ_one_eq_two, Finset.sum_apply, Pi.smul_apply,
          Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, Finset.sum_mk,
          Multiset.map_coe, List.map_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_fin_const,
          List.map_nil, Multiset.sum_coe, List.sum_cons, List.sum_nil]
        simp_rw [b₁,b₂,b₃]
        simp only [Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons]
        ring_nf
        rw [← left_distrib (g 0), omega_add_omega_inv,mul_one]
        simp only [Fin.isValue, two_eq_zero, mul_zero, add_zero]
      _ = 0 := by
        rw [h ((0:Fin 1).succ.succ.succ.succ.succ), h 2,add_zero]
  . calc
      g 1 =
        g 0 * (ω + ω) + g 1 * (ω + ω⁻¹) + g 2 * (ω⁻¹ + ω⁻¹) := by
          simp only [CharTwo.add_self_eq_zero, mul_zero, omega_add_omega_inv, mul_one, zero_add,
            add_zero]
      _ = (g 0 * ω + g 1 * ω + g 2 * ω⁻¹) + (g 0 * ω + g 1 * ω⁻¹ + g 2 * ω⁻¹) := by
        ring_nf
      _ = (∑ i, g i • hexaCodeBasis' i) ((0:Fin 1).succ.succ.succ.succ.succ) +
          (∑ i, g i • hexaCodeBasis' i) 0 := by
        simp_rw [Finset.univ,Fintype.elems,List.finRange]
        simp only [Fin.isValue, List.pmap, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
          Nat.succ_eq_add_one, Nat.reduceAdd, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
          Finset.sum_apply, Pi.smul_apply, Matrix.cons_val', Matrix.empty_val',
          Matrix.cons_val_fin_one, smul_eq_mul, Finset.sum_mk, Multiset.map_coe, List.map_cons,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_fin_const, List.map_nil, Multiset.sum_coe, List.sum_cons,
          List.sum_nil, add_zero]
        simp_rw [b₁,b₂,b₃]
        simp only [Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons]
        ring_nf
      _ = 0 := by
        rw [h ((0:Fin 1).succ.succ.succ.succ.succ), h 0,add_zero]
  . calc
    g 2
      = g 0 * (ω + ω) + g 1 * (ω⁻¹ + ω⁻¹) + g 2 * (ω + ω⁻¹) := by
      simp only [CharTwo.add_self_eq_zero, mul_zero, omega_add_omega_inv, mul_one, zero_add]
    _ = (g 0 * ω + g 1 * ω⁻¹ + g 2 * ω) + (g 0 * ω + g 1 * ω⁻¹ + g 2 * ω⁻¹) := by
      ring_nf
    _ = (∑ i, g i • hexaCodeBasis' i) (2:Fin 5).succ + (∑ i, g i • hexaCodeBasis' i) 0 := by
      simp_rw [Finset.univ,Fintype.elems,List.finRange]
      simp only [Fin.isValue, List.pmap, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk,
        Finset.sum_apply, Pi.smul_apply, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one, smul_eq_mul, Finset.sum_mk, Multiset.map_coe, List.map_cons,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons, Matrix.head_fin_const, List.map_nil,
        Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
      simp_rw [b₁,b₂,b₃]
      simp only [Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons]
      ring_nf
    _ = 0 := by
      rw [h (2:Fin 5).succ, h 0,add_zero]

-- def a₁ : F_4_6 := ![ω,ω⁻¹,ω,ω⁻¹,ω,ω⁻¹]

end HexaCode

def HexaCode : Submodule F4 F_4_6 := Submodule.span (F4) (Set.range HexaCode.hexaCodeBasis')


namespace HexaCode

noncomputable def hc_basis : Basis (Fin 3) F4 HexaCode := Basis.span basis_indep

@[simp]
lemma left_distrib_omega_omega_inv (a:F4) : a * ω + a * ω⁻¹ = a := by
  rw [← left_distrib, omega_add_omega_inv, mul_one]

@[simp]
lemma right_distrib_omega_omega_inv (a:F4) : ω * a + ω⁻¹ * a = a := by
  rw [← right_distrib, omega_add_omega_inv, one_mul]

@[simp]
lemma add_mul_omega_inv (a:F4) : a + a * ω⁻¹ = a * ω := by
  nth_rw 1 [← mul_one a]
  rw [← left_distrib]
  simp only [mul_eq_mul_left_iff]
  left
  decide

@[simp]
lemma add_mul_omega (a:F4) : a + a * ω = a * ω⁻¹ := by
  nth_rw 1 [← mul_one a]
  rw [← left_distrib]
  simp only [mul_eq_mul_left_iff]
  left
  decide

lemma calc_stuff (x : F_4_6) :
    ![x 0, x 1, x 2,x 0 + x 1 + x 2, ω⁻¹ • x 0 + ω • x 1 + x 2,ω • x 0 + ω⁻¹ • x 1 + x 2] =
    (x 0 * ω + x 1 * ω⁻¹) • b₁ + (x 0 * ω⁻¹ + x 1 * ω⁻¹ + x 2) • b₂ + (x 1 + x 2) • b₃ := by
  simp_rw [b₁,b₂,b₃]
  simp only [smul_eq_mul, Matrix.smul_cons, Matrix.smul_empty, Matrix.add_cons, Matrix.head_cons,
    Matrix.tail_cons, Matrix.empty_add_empty]
  ring_nf
  simp only [square_eq_inv, inv_pow, inv_inv, two_eq_zero, mul_zero, add_zero, zero_add]
  ring_nf
  simp only [left_distrib_omega_omega_inv, two_eq_zero, mul_zero, zero_add, add_zero]
  ring_nf
  simp only [add_mul_omega_inv]
  rw [add_assoc (x 0) (x 1 * ω)]
  simp only [add_mul_omega_inv]
  ring_nf
  simp only [square_eq_inv, CharTwo.add_self_eq_zero, zero_add, left_distrib_omega_omega_inv]
  ring_nf
  simp only [two_eq_zero, mul_zero, add_zero]
  rw [mul_assoc, mul_inv_cancel omega_ne_zero, mul_one, add_assoc (x 0 + x 1)]
  simp only [left_distrib_omega_omega_inv]
  ring_nf
  rw [add_assoc (x 0 * ω⁻¹ + x 1 * ω),left_distrib_omega_omega_inv,mul_assoc (x 0), mul_comm ω ω⁻¹]
  rw [← mul_assoc,add_comm (x 0 * ω⁻¹ * ω), add_mul_omega]
  ring_nf
  simp only [inv_pow, square_eq_inv, inv_inv]
  rw [add_assoc (x 0 * ω + x 1 * ω⁻¹),left_distrib_omega_omega_inv]

@[simp]
lemma hc_basis_zero : hc_basis 0 = b₁ := by
  calc
    hc_basis 0 = hexaCodeBasis' 0 := Basis.span_apply basis_indep 0
    _ = b₁ := by decide

@[simp]
lemma b₁_mem_hc : b₁ ∈ HexaCode := hc_basis_zero ▸ (hc_basis 0).2

@[simp]
lemma hc_basis_one : hc_basis 1 = b₂ := by
  calc
    hc_basis 1 = hexaCodeBasis' 1 := Basis.span_apply basis_indep 1
    _ = b₂ := by decide

@[simp]
lemma b₂_mem_hc : b₂ ∈ HexaCode := hc_basis_one ▸ (hc_basis 1).2

@[simp]
lemma hc_basis_two : hc_basis 2 = b₃ := by
  calc
    hc_basis 2 = hexaCodeBasis' 2 := Basis.span_apply basis_indep 2
    _ = b₃ := by decide

@[simp]
lemma b₃_mem_hc : b₃ ∈ HexaCode := hc_basis_two ▸ (hc_basis 2).2


lemma mem_hc_iff (x :F_4_6): x ∈ HexaCode ↔
    x = ![x 0, x 1, x 2,x 0 + x 1 + x 2, ω⁻¹ • x 0 + ω • x 1 + x 2,ω • x 0 + ω⁻¹ • x 1 + x 2] := by
  rw [calc_stuff]
  constructor
  . intro hx
    rw [HexaCode] at hx
    refine Submodule.span_induction hx ?basis ?zero ?add ?smul
    . simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton,
      Set.union_insert, Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
      decide
    . decide
    . intro x y hx hy
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      nth_rw 1 [hx,hy]
      simp_rw [right_distrib,add_smul]
      ring_nf
    . intro r m hm
      nth_rw 1 [hm]
      simp only [smul_add, Pi.smul_apply, smul_eq_mul]
      simp_rw [← mul_smul]
      simp_rw [left_distrib r,mul_assoc]
  intro h
  rw [h]
  apply add_mem
  apply add_mem
  any_goals apply HexaCode.smul_mem
  any_goals exact b₁_mem_hc
  any_goals exact b₂_mem_hc
  any_goals exact b₃_mem_hc

instance : DecidablePred (. ∈ HexaCode) := fun h => by
  apply decidable_of_iff _ (mem_hc_iff h).symm

-- #eval b₁ ∈ HexaCode

example : b₁ ∈ HexaCode := by decide

lemma addGNorm_eq_of_size {x : F_4_6} (n : ℕ) (hn : (Finset.filter (x . ≠ 0) (Finset.univ)).card = n) :
    addGNorm hdist x = n := by
  dsimp [addGNorm]
  rw [Nat.cast_inj]
  dsimp [hammingNorm]
  exact hn

noncomputable def hexa_poly (a b c : F4) : Polynomial F4 :=
  Polynomial.C a * Polynomial.X^2 + Polynomial.C b * Polynomial.X + Polynomial.C c

lemma poly_eq_zero_iff (a b c : F4) : hexa_poly a b c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  dsimp [hexa_poly]
  rw [Polynomial.ext_iff]
  simp_rw [Polynomial.coeff_add,Polynomial.coeff_C_mul_X]
  constructor
  . intro h
    repeat' constructor
    . specialize h 2
      simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, ↓reduceIte, mul_one,
        OfNat.ofNat_ne_one, add_zero, Polynomial.coeff_C_succ, Polynomial.coeff_zero] at h
      exact h
    . specialize h 1
      simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, OfNat.one_ne_ofNat, ↓reduceIte,
        mul_zero, zero_add, Polynomial.coeff_C_succ, add_zero, Polynomial.coeff_zero] at h
      exact h
    . specialize h 0
      simp only [Polynomial.mul_coeff_zero, Polynomial.coeff_C_zero, Polynomial.coeff_X_pow,
        OfNat.zero_ne_ofNat, ↓reduceIte, mul_zero, zero_ne_one, CharTwo.add_self_eq_zero, zero_add,
        Polynomial.coeff_zero] at h
      exact h
  . intro ⟨ha,hb,hc⟩
    rw [ha,hb,hc]
    simp only [map_zero, zero_mul, Polynomial.coeff_zero, ite_self, CharTwo.add_self_eq_zero,
      implies_true]


lemma mem_hc_iff' {x : F_4_6} : x ∈ HexaCode ↔
  x = ![x 0, x 1,
    (hexa_poly (x 0) (x 1) (x 2)).eval 0,
    (hexa_poly (x 0) (x 1) (x 2)).eval 1,
    (hexa_poly (x 0) (x 1) (x 2)).eval ω,
    (hexa_poly (x 0) (x 1) (x 2)).eval ω⁻¹] := by
  rw [mem_hc_iff]
  dsimp [hexa_poly]
  constructor
  intro h
  nth_rw 1 [h]
  clear h
  have_goal suf := by
    generalize x 0 = a
    generalize x 1 = b
    generalize x 2 = c
    simp_rw [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C]
    simp only [Polynomial.eval_pow, Polynomial.eval_X, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, smul_eq_mul, mul_zero, CharTwo.add_self_eq_zero,
      Polynomial.eval_C, zero_add, one_pow, mul_one, square_eq_inv, inv_pow, inv_inv]
    rw [mul_comm ω⁻¹ a,mul_comm ω b,mul_comm ω a, mul_comm ω⁻¹ b]
  rw [suf]
  intro h
  rw [← h]

lemma norm_hc_eq {x : F_4_6} (hx : x ∈ HexaCode) (hz : x ≠ 0): hammingNorm x =
    (if x 0 ≠ 0 then 1 else 0) +
    (if x 1 ≠ 0 then 1 else 0) +
    (4 - ((hexa_poly (x 0) (x 1) (x 2)).roots.toFinset.card)) := by
  rw [Multiset.card_toFinset]
  rw [mem_hc_iff'.mp hx]
  have poly_ne_zero : hexa_poly (x 0) (x 1) (x 2) ≠ 0 := by
    rw [ne_eq, poly_eq_zero_iff]
    contrapose! hz
    rw [(mem_hc_iff x).mp hx]
    obtain ⟨h₁,h₂,h₃⟩ := hz
    rw [h₁,h₂,h₃]
    decide
  clear hx
  dsimp [hammingNorm]
  simp only [Fin.isValue, Matrix.tail_cons, Matrix.head_cons]
  dsimp [Finset.univ,Fintype.elems,List.finRange]
  simp only [Fin.isValue]
  revert poly_ne_zero
  generalize x 0 = a
  generalize x 1 = b
  generalize x 2 = c
  intro poly_ne_zero
  rw [Finset.card_filter]
  simp only [Fin.isValue, Finset.sum_mk, Multiset.map_coe, List.map_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.tail_cons, Matrix.cons_val_three,
    Matrix.cons_val_four, List.map_nil, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
  simp_rw [add_assoc]
  congr
  suffices (Finset.filter (fun z => (hexa_poly a b c).eval z ≠ 0) Finset.univ) =
      ((hexa_poly a b c).roots).toFinsetᶜ by
    have : (Finset.filter (fun z => (hexa_poly a b c).eval z ≠ 0) Finset.univ).card =
      ((hexa_poly a b c).roots).toFinsetᶜ.card := by
      rw [this]
    rw [Finset.card_compl] at this
    simp only [ne_eq, Set.toFinset_card] at this
    have four_eq : Fintype.card F4 = 4 := by decide
    rw [four_eq] at this
    rw [Multiset.card_toFinset] at this
    have c_eq : (hexa_poly a b c).eval 0 = c := by
      dsimp [hexa_poly]
      simp_rw [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
        Polynomial.eval_X]
      rw [zero_pow (by decide : 2 ≠ 0)]
      simp only [mul_zero, zero_add]
    simp_rw [c_eq]
    rw [← this]
    rw [Finset.card_filter]
    simp only [ite_not, Fin.isValue]
    dsimp [Finset.univ,Fintype.elems]
    simp only [Fin.isValue, Finset.cons_eq_insert]
    rw [Finset.sum_insert, Finset.sum_insert,Finset.sum_insert]
    skip_goal
    . decide
    . decide
    . decide
    rw [Finset.sum_mk,Multiset.map_singleton]
    simp only [Fin.isValue, Multiset.sum_singleton]
    rw [c_eq]
    rfl
  ext v
  simp only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
    Multiset.mem_toFinset, Polynomial.mem_roots', Polynomial.IsRoot.def, not_and,
    Classical.imp_iff_left_iff]
  left
  exact poly_ne_zero

lemma four_le_norm_of_nzero {x : F_4_6} (hx : x ∈HexaCode) (hz :x ≠ 0): 4 ≤ addGNorm hdist x := by
  dsimp [addGNorm]
  rw [Nat.ofNat_le_cast]
  rw [norm_hc_eq hx hz]
  generalize x 0 = a
  generalize x 1 = b
  generalize x 2 = c
  if ha : a = 0 then
    rw [ha]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, ite_not, zero_add]
    if hb : b = 0 then
      rw [hb]
      simp only [↓reduceIte, zero_add]
      dsimp [hexa_poly]
      simp only [map_zero, zero_mul, CharTwo.add_self_eq_zero, zero_add, Polynomial.roots_C,
        Multiset.toFinset_zero, Finset.card_empty, tsub_zero, le_refl]
    else
      have : (hexa_poly 0 b c).degree = 1 := by
        dsimp [hexa_poly]
        simp only [map_zero, zero_mul, zero_add]
        rw [Polynomial.degree_linear hb]
      rw [if_neg hb]
      have max_one_root : (hexa_poly 0 b c).roots.toFinset.card ≤ 1 := by
        apply le_trans
        skip_goal
        skip_goal
        . exact (Multiset.card (hexa_poly 0 b c).roots)
        . exact Multiset.toFinset_card_le (hexa_poly 0 b c).roots
        . rw [Polynomial.degree_eq_natDegree] at this
          simp only [Nat.cast_eq_one] at this
          rw [← this]
          exact Polynomial.card_roots' (hexa_poly 0 b c)
          contrapose! this
          rw [this]
          simp only [Polynomial.degree_zero, ne_eq, WithBot.bot_ne_one, not_false_eq_true]
      omega
  else
    have : (hexa_poly a b c).degree = 2 := by
      dsimp [hexa_poly]
      exact Polynomial.degree_quadratic ha
    simp only [ne_eq, ite_not, ge_iff_le]
    rw [if_neg ha]
    if hb : b = 0 then
      rw [hb]
      simp only [↓reduceIte, add_zero]
      suffices (hexa_poly a 0 c).roots.toFinset = {a * c⁻¹} by
        rw [this]
        simp only [Finset.card_singleton, Nat.reduceSub, Nat.reduceAdd, le_refl]
      ext x
      simp only [Multiset.mem_toFinset, Polynomial.mem_roots', ne_eq, Polynomial.IsRoot.def,
        Finset.mem_singleton]
      rw [poly_eq_zero_iff]
      simp only [true_and, not_and]
      dsimp [hexa_poly]
      simp only [map_zero, zero_mul, add_zero, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, square_eq_inv]
      constructor
      . intro ⟨_,h⟩
        rw [← zero_add c,← h,add_assoc,F4.add_self,add_zero]
        simp only [mul_inv_rev, inv_inv]
        rw [mul_comm x,← mul_assoc,mul_inv_cancel ha,one_mul]
      . rintro rfl
        simp only [mul_inv_rev, inv_inv]
        rw [mul_comm c a⁻¹,← mul_assoc,mul_inv_cancel ha,one_mul,F4.add_self]
        simp only [and_true]
        exact fun a _ ↦ ha a
    else
      rw [if_neg hb]
      suffices (hexa_poly a b c).roots.toFinset.card ≤ 2 by
        omega
      apply le_trans
      skip_goal
      skip_goal
      exact Multiset.card (hexa_poly a b c).roots
      . exact Multiset.toFinset_card_le (hexa_poly a b c).roots
      . rw [Polynomial.degree_eq_natDegree] at this
        rw [← Nat.cast_eq_ofNat] at this
        rw [Nat.cast_inj] at this
        rw [← Nat.cast_eq_ofNat]
        rw [← this]
        exact (hexa_poly a b c).card_roots'
        simp only [ne_eq]
        rw [poly_eq_zero_iff]
        exact fun a => ha a.1

lemma most_2_zeros {x : F_4_6} (hx : x ∈ HexaCode) :
    addGNorm hdist x = 0 ∨ 4 ≤ addGNorm hdist x := by
  if hx' : x = 0 then
    rw [hx']
    left
    dsimp[addGNorm]
    simp only [hammingNorm_zero, CharP.cast_eq_zero]
  else
    right
    exact four_le_norm_of_nzero hx hx'
