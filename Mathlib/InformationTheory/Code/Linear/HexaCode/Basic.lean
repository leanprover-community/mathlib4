import Mathlib.InformationTheory.Code.Linear.HexaCode.F4
import Mathlib.InformationTheory.Code.HammingCode
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Matrix.Reflection

open F4

abbrev F_4_6 := Fin 6 → F4



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

def hexaCodeBasis' : Fin 3 → F_4_6 := ![b₁,b₂,b₃]

def a₁ : F_4_6 := ![ω,ω⁻¹,ω,ω⁻¹,ω,ω⁻¹]

def hexaCode : Submodule F4 F_4_6 := Submodule.span (F4) (Set.range hexaCodeBasis')

/-

how to prove ![b₁,b₂,b₃] is a basis for hexaCode:

prove the forgetful projection is of type (Fin 6 → F4) →ₗ[F4] (Fin 3 → F4)

prove the matrix !![ω,ω⁻¹,0;ω⁻¹,ω⁻¹,1;0,1,1] gives a type (Fin 3 → F4) →ₗ[F4] (Fin 3 → F4)

these compose to (Fin 6 → F4) →ₗ[F4] (Fin 3 → F4)

furthermore, the opposite map given by (Matrix.of ![b₁,b₂,b₃] : (Fin 3 → F4) →ₗ (Fin 6 → F4))

prove that these are right- and left-inverse to eachother.

-/
def forgetful : (Fin 6 → F4) →ₗ[F4] (Fin 3 → F4) where
  toFun := fun f i => f i
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def matrix1 : (Fin 3 → F4) →ₗ[F4] (Fin 3 → F4) := Matrix.vecMulLinear !![ω,ω⁻¹,0;ω⁻¹,ω⁻¹,1;0,1,1]

def hexacodeBasisEquiv.tolinearMap : hexaCode →ₗ[F4] (Fin 3 → F4) :=
  (matrix1.comp (forgetful.domRestrict hexaCode))

def hexacodeBasisEquiv.tolinearMap_inv' : (Fin 3 → F4) →ₗ[F4] F_4_6 :=
  Matrix.vecMulLinear (Matrix.of ![b₁,b₂,b₃])

lemma hexacodeBasisEquiv.tolinearMap_inv_to_code : ∀ (f:Fin 3 → F4),
    hexacodeBasisEquiv.tolinearMap_inv' f ∈ hexaCode := by
  rw [hexaCode]
  simp_rw [Submodule.mem_span]
  simp_rw [hexaCodeBasis']
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton,
    Set.union_insert]
  rw [forall_comm]
  intro b
  rw [forall_comm]
  intro hb
  rw [tolinearMap_inv']
  simp only [Matrix.vecMulLinear_apply, Matrix.vecMul_cons, Matrix.empty_vecMul, add_zero]
  intro a
  let a₁ := a 0
  let a₂ := a 1
  let a₃ := a 2
  have ha : a = ![a₁,a₂,a₃] := by
    ext ⟨i,hi⟩ : 1
    rcases i
    . simp only [Nat.zero_eq, Fin.zero_eta, Matrix.cons_val_zero]
    rename_i i
    simp only [Matrix.cons_val_succ']
    rcases i
    . simp only [Nat.zero_eq, Nat.reduceSucc, Fin.mk_one, Fin.zero_eta, Matrix.cons_val_zero]
    rename_i i
    rcases i
    . simp only [Nat.zero_eq, Nat.reduceSucc, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]
      congr
    contradiction
  rw [ha]
  simp only [Matrix.mulVec_cons, Matrix.mulVec_empty, add_zero]
  apply add_mem <;> try apply add_mem <;> apply Submodule.smul_mem <;> apply hb
  . apply Submodule.smul_mem
    apply hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  . simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or, or_true]

  . simp only [Set.mem_insert_iff, Set.mem_singleton_iff, true_or]

set_option maxHeartbeats 400000
def hexaCodeBasisEquiv : hexaCode ≃ₗ[F4] (Fin 3 → F4) := {
  hexacodeBasisEquiv.tolinearMap with
  invFun := hexacodeBasisEquiv.tolinearMap_inv'.codRestrict hexaCode hexacodeBasisEquiv.tolinearMap_inv_to_code
  left_inv := by
    intro ⟨f,hf⟩
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    rw [hexacodeBasisEquiv.tolinearMap]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.domRestrict_apply]
    ext : 1
    simp only [LinearMap.codRestrict_apply]
    simp_rw [hexacodeBasisEquiv.tolinearMap_inv']
    simp only [Matrix.vecMulLinear_apply, Matrix.vecMul_cons, Matrix.empty_vecMul, add_zero]
    apply (@Submodule.span_induction F4 F_4_6 _ _ _ f (Set.range hexaCodeBasis'))
    . exact hf
    . rw [Set.range,hexaCodeBasis']
      simp only [Set.mem_setOf_eq, forall_exists_index, forall_apply_eq_imp_iff, Matrix.cons_val',
        Matrix.empty_val', Matrix.cons_val_fin_one]
      intro ⟨i,hi⟩
      rcases i
      . simp only [Nat.zero_eq, Fin.zero_eta, Matrix.cons_val_zero]
        nth_rw 1 [b₁]
        nth_rw 2 [b₁,b₁]
        simp_rw [forgetful,matrix1]
        simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulLinear_apply, Matrix.vecMul_cons,
          Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty, mul_one, Matrix.empty_vecMul,
          add_zero, Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_add_empty,
          zero_add]
        simp_rw [Matrix.vecHead,Matrix.vecTail]
        simp only [Fin.val_zero, Nat.cast_zero, Matrix.cons_val_zero, Function.comp_apply,
          Fin.succ_zero_eq_one, Fin.val_one, Nat.cast_one, Matrix.cons_val_one, Matrix.head_cons,
          Fin.succ_one_eq_two, Fin.val_two, Nat.cast_ofNat, Matrix.cons_val_two, Matrix.tail_cons]
        ring_nf
        ext j : 1
        simp only [inv_pow, Pi.add_apply, Pi.smul_apply, Function.comp_apply, Matrix.head_cons,
          smul_eq_mul, Matrix.tail_cons]
        ring_nf
        simp only [square_eq_inv, two_eq_zero, mul_zero, add_zero, inv_pow, inv_inv]
        rw [mul_inv_cancel omega_ne_zero]
        ring_nf
        rw [add_assoc (b₂ j),← left_distrib (b₂ j),omega_add_omega_inv]
        rw [add_assoc, ← right_distrib, omega_add_omega_inv]
        simp only [mul_one, add_self, one_mul, zero_add]
      rename_i i
      cases i
      . nth_rw 1 [b₂,b₂]
        nth_rw 2 [b₂]
        simp only [Matrix.cons_val_zero, Nat.zero_eq, Nat.reduceSucc, Fin.mk_one,
          Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty, Matrix.cons_add, Matrix.empty_add_empty,
          Matrix.add_cons]
        ring_nf
        rw [forgetful]
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        rw [matrix1]
        simp only [Matrix.vecMulLinear_apply, Matrix.vecMul_cons, Matrix.smul_cons, smul_eq_mul,
          mul_zero, Matrix.smul_empty, mul_one, Matrix.empty_vecMul, add_zero, Matrix.add_cons,
          Matrix.head_cons, Matrix.tail_cons, Matrix.empty_add_empty, zero_add, Matrix.mulVec_cons,
          Matrix.mulVec_empty]
        simp_rw [Matrix.vecHead,Matrix.vecTail]
        simp only [Fin.val_zero, Nat.cast_zero, Matrix.cons_val_zero, Function.comp_apply,
          Fin.succ_zero_eq_one, Fin.val_one, Nat.cast_one, Matrix.cons_val_one, Matrix.head_cons,
          Fin.succ_one_eq_two, Fin.val_two, Nat.cast_ofNat, Matrix.cons_val_two, Matrix.tail_cons,
          add_self, zero_smul, add_zero]
        ext i : 1
        simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, Matrix.head_cons, smul_eq_mul,
          Matrix.tail_cons]
        ring_nf
        simp only [two_eq_zero, mul_zero, zero_add, inv_pow, square_eq_inv, inv_inv]
        rw [mul_inv_cancel omega_ne_zero]
        simp only [one_mul]

        rw [add_assoc,← right_distrib, add_self]
        simp only [zero_mul, add_zero]
      rename_i i
      cases i
      . nth_rw 1 [b₃,b₃,b₃]
        simp only [Matrix.cons_val_zero, Nat.zero_eq, Nat.reduceSucc, Matrix.cons_val_succ',
          Fin.mk_one, Matrix.cons_val_one, Matrix.head_fin_const, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons, Matrix.smul_cons, smul_eq_mul, Matrix.smul_empty,
          Matrix.add_cons, Matrix.empty_add_empty]
        ring_nf
        rw [forgetful,matrix1]
        simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulLinear_apply, Matrix.vecMul_cons,
          Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty, mul_one, Matrix.empty_vecMul,
          add_zero, Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_add_empty,
          zero_add, Matrix.mulVec_cons, Matrix.mulVec_empty]
        ext i: 1
        simp only [Pi.add_apply, Pi.smul_apply, Function.comp_apply, Matrix.head_cons, smul_eq_mul,
          Matrix.tail_cons]
        simp_rw [Matrix.vecHead,Matrix.vecTail]
        simp only [Fin.val_zero, Nat.cast_zero, Matrix.cons_val_zero, Function.comp_apply,
          Fin.succ_zero_eq_one, Fin.val_one, Nat.cast_one, Matrix.cons_val_one, Matrix.head_cons,
          Fin.succ_one_eq_two, Fin.val_two, Nat.cast_ofNat, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.transpose_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
          omega_add_omega_inv, Matrix.head_fin_const, one_mul]
        rw [mul_inv_cancel omega_ne_zero,inv_mul_cancel omega_ne_zero,add_self,zero_mul]
        ring_nf
        simp only [inv_pow, square_eq_inv, inv_inv, add_left_eq_self]
        rw [← right_distrib,add_comm ω⁻¹ ω,omega_add_omega_inv,one_mul,add_self]
      contradiction
    . simp only [map_zero, Matrix.head_zero, zero_smul, Matrix.tail_zero, add_zero]
    . simp only [map_add, Matrix.head_add, Matrix.tail_add]
      intro x y hx hy
      nth_rw 4 [← hx, ← hy]
      simp_rw [add_smul]
      ring_nf
    . intro r m hm
      nth_rw 4 [← hm]
      simp only [smul_add,map_smul]
      simp_rw [Matrix.vecHead,Matrix.vecTail]
      simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply, Fin.succ_zero_eq_one,
        Fin.succ_one_eq_two]
      simp_rw [mul_smul]
  right_inv := by
    intro f
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
    rw [hexacodeBasisEquiv.tolinearMap]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.domRestrict_apply,
      LinearMap.codRestrict_apply]
    rw [hexacodeBasisEquiv.tolinearMap_inv']
    simp only [Matrix.vecMulLinear_apply, Matrix.vecMul_cons, Matrix.empty_vecMul, add_zero,
      map_add, map_smul]
    rw [forgetful,matrix1]
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Matrix.vecMulLinear_apply, Matrix.vecMul_cons,
      Matrix.smul_cons, smul_eq_mul, mul_zero, Matrix.smul_empty, mul_one, Matrix.empty_vecMul,
      add_zero, Matrix.add_cons, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_add_empty,
      zero_add]
    ext i : 1
    obtain ⟨i,hi⟩ := i
    rcases i
    . simp only [Nat.zero_eq, Fin.zero_eta, Matrix.cons_val_zero]
      simp_rw [Matrix.vecHead,Matrix.vecTail]
      simp only [Fin.val_zero, Nat.cast_zero, Function.comp_apply, Fin.succ_zero_eq_one,
        Fin.val_one, Nat.cast_one, Fin.succ_one_eq_two]
      simp_rw [b₁,b₂,b₃]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      ring_nf
      simp only [square_eq_inv, inv_pow, inv_inv, two_eq_zero, mul_zero, add_zero]
      rw [add_comm,← left_distrib,omega_add_omega_inv,mul_one]
    rename_i i
    rcases i
    . simp only [Nat.zero_eq, Nat.reduceSucc, Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]
      simp_rw [Matrix.vecHead,Matrix.vecTail]
      simp only [Fin.val_zero, Nat.cast_zero, Function.comp_apply, Fin.succ_zero_eq_one,
        Fin.val_one, Nat.cast_one, Fin.succ_one_eq_two, Fin.val_two, Nat.cast_ofNat]
      simp_rw [b₁,b₂,b₃]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
      ring_nf
      simp only [inv_pow, square_eq_inv, inv_inv]
      rw [mul_inv_cancel omega_ne_zero, mul_assoc (f 0), mul_inv_cancel omega_ne_zero]
      ring_nf
      simp only [two_eq_zero, mul_zero, add_zero]
      rw [add_assoc (f 0),← left_distrib,omega_add_omega_inv,mul_one,add_self,zero_add]
      rw [← right_distrib, omega_add_omega_inv,one_mul,add_comm,← add_assoc,add_self,zero_add]
    rename_i i
    rcases i
    . simp only [Nat.zero_eq, Nat.reduceSucc, Matrix.cons_val_succ', Fin.mk_one,
      Matrix.cons_val_one, Matrix.head_cons]
      simp_rw [Matrix.vecHead,Matrix.vecTail]
      simp only [Function.comp_apply, Fin.succ_zero_eq_one, Fin.val_one, Nat.cast_one,
        Fin.succ_one_eq_two, Fin.val_two, Nat.cast_ofNat]
      simp_rw [b₁,b₂,b₃]
      simp only [Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
        add_self, mul_zero, omega_add_omega_inv, mul_one, zero_add]
      rfl
    contradiction
}


noncomputable def hexaCodeBasis : Basis (Fin 3) F4 (hexaCode) := Basis.ofEquivFun hexaCodeBasisEquiv

lemma decideProc_mem_hexacode (f: F_4_6): (f ∈ hexaCode) ↔ hexaCodeBasisEquiv.symm (matrix1 (forgetful f)) = f := by
  constructor
  . intro h
    have h_inv := hexaCodeBasisEquiv.left_inv ⟨f,h⟩
    nth_rw 2 [hexaCodeBasisEquiv] at h_inv
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.invFun_eq_symm] at h_inv
    simp_rw [hexacodeBasisEquiv.tolinearMap] at h_inv
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.domRestrict_apply] at h_inv
    rw [Subtype.ext_iff] at h_inv
    exact h_inv
  . intro h
    exact h ▸ ((LinearEquiv.symm hexaCodeBasisEquiv) (matrix1 (forgetful f))).property

instance : DecidablePred (. ∈ hexaCode) := fun h => by
  simp only
  rw [decideProc_mem_hexacode]
  if h2:↑((LinearEquiv.symm hexaCodeBasisEquiv) (matrix1 (forgetful h))) = h then
    exact (isTrue h2)
  else
    exact (isFalse h2)
