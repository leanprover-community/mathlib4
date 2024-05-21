import Mathlib.InformationTheory.Code.Linear.Mathieu.F4
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
        simp only [List.pmap, Fin.zero_eta, Fin.mk_one, Finset.sum_apply, Pi.smul_apply,
          Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, Finset.sum_mk,
          Multiset.coe_map, List.map_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.cons_val_succ', Matrix.head_fin_const, List.map_nil,
          Multiset.coe_sum, List.sum_cons, List.sum_nil, add_zero]
        simp_rw [b₁,b₂,b₃]
        simp only [Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons]
        ring_nf
        rfl
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
        simp only [List.pmap, Fin.zero_eta, Fin.mk_one, Fin.succ_zero_eq_one, Fin.succ_one_eq_two,
          Finset.sum_apply, Pi.smul_apply, Matrix.cons_val', Matrix.empty_val',
          Matrix.cons_val_fin_one, smul_eq_mul, Finset.sum_mk, Multiset.coe_map, List.map_cons,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ',
          Matrix.head_fin_const, List.map_nil, Multiset.coe_sum, List.sum_cons, List.sum_nil,
          add_zero]
        simp_rw [b₁,b₂,b₃]
        simp only [Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons]
        ring_nf
        rfl
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
      simp only [List.pmap, Fin.zero_eta, Fin.mk_one, Finset.sum_apply, Pi.smul_apply,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul, Finset.sum_mk,
        Multiset.coe_map, List.map_cons, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons, Matrix.cons_val_succ', Matrix.head_fin_const, List.map_nil,
        Multiset.coe_sum, List.sum_cons, List.sum_nil, add_zero]
      simp_rw [b₁,b₂,b₃]
      simp only [Matrix.cons_val_succ, Matrix.cons_val_zero, Matrix.cons_val_two,
          Matrix.tail_cons, Matrix.head_cons]
      ring_nf
      rfl
    _ = 0 := by
      rw [h (2:Fin 5).succ, h 0,add_zero]

def a₁ : F_4_6 := ![ω,ω⁻¹,ω,ω⁻¹,ω,ω⁻¹]

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

#eval b₁ ∈ HexaCode

example : b₁ ∈ HexaCode := by decide
