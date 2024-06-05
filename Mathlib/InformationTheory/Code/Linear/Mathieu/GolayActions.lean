import Mathlib.InformationTheory.Code.Linear.Mathieu.BGolay
import Mathlib.Algebra.Ring.BooleanRing

import Mathlib.InformationTheory.Code.Linear.TacticTmp.have_goal

open BigOperators HexaCode

lemma mem_vadd_map_dist (f:F_4_6) :
    ∀ x y : golay_code_space', hdist x y = hdist (f +ᵥ x) (f +ᵥ y) := fun x y => by
  simp_rw [addDist_eq,addGNorm,hdist]
  simp only [hammingENatdist_eq_cast_hammingDist, hammingDist_zero_right, Equiv.toFun_as_coe,
    AddAction.toPerm_apply, Nat.cast_inj]
  simp_rw [hammingNorm]
  suffices hsuf : (Finset.filter (fun x_1 ↦ (x - y) x_1 ≠ 0) Finset.univ) ≃
      (Finset.filter (fun x_1 ↦ (f +ᵥ (x - y)) x_1 ≠ 0) Finset.univ) by
    exact Finset.card_eq_of_equiv hsuf
  exact {
    toFun := fun ⟨⟨i,x⟩,hx⟩ => ⟨⟨i,f i + x⟩,by
      simp_rw [HVAdd.hVAdd,VAdd.vadd]
      simp only [ne_eq, Finset.filter_congr_decidable, Finset.mem_filter, Finset.mem_univ,
        Function.uncurry_apply_pair, Pi.vadd_apply', true_and]
      simp_rw [HVAdd.hVAdd,VAdd.vadd]
      simp only [Equiv.symm_apply_apply, vadd_eq_add, Function.curry_apply]
      group
      simp only [F4.two_eq_zero, mul_zero, zero_add]
      simp only [ne_eq, Finset.mem_filter, Finset.mem_univ,
        true_and] at hx
      exact hx⟩
    invFun := fun ⟨⟨i,x⟩,hx⟩ => ⟨⟨i,f i + x⟩,by
      simp_rw [HVAdd.hVAdd,VAdd.vadd] at hx
      simp only [ne_eq, Finset.filter_congr_decidable, Finset.mem_filter, Finset.mem_univ,
        Function.uncurry_apply_pair, Pi.vadd_apply', true_and] at hx
      simp_rw [HVAdd.hVAdd,VAdd.vadd] at hx
      simp only [Equiv.symm_apply_apply, vadd_eq_add, Function.curry_apply] at hx
      group at hx
      simp only [CharTwo.sub_eq_add, ne_eq, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hx⟩

    left_inv := fun ⟨⟨i,x⟩,hx⟩ => by
      simp only [Pi.sub_apply, ne_eq, Subtype.mk.injEq, Prod.mk.injEq, true_and]
      group
      simp only [F4.two_eq_zero, mul_zero, zero_add]
    right_inv := fun ⟨⟨i,x⟩,hx⟩ => by
      simp only [ne_eq, Subtype.mk.injEq, Prod.mk.injEq, true_and]
      group
      simp only [F4.two_eq_zero, mul_zero, zero_add]
  }

-- to_hexaCode' x =    ![0,0,0,0,0,0] = 0
abbrev gc_b₁ := to_gc !![1,1,1,0,0,0;-- bad; weight = 12
                         0,0,0,1,1,1;
                         0,0,0,1,1,1;
                         0,0,0,1,1,1]

lemma gc_b₁_mem : gc_b₁ ∈ GolayCode := by decide


abbrev gc_b₁' : GolayCode := ⟨gc_b₁,gc_b₁_mem⟩

-- to_hexaCode' x =    ![1,0,0,1,ω⁻¹,ω] = ω • b₁ + ω⁻¹ • b₂
abbrev gc_b₂ := to_gc !![0,1,1,0,0,1;
                         1,0,0,1,0,1;
                         0,0,0,0,0,0;
                         0,0,0,0,1,1]


lemma gc_b₂_mem : gc_b₂ ∈ GolayCode := by decide

abbrev gc_b₂' : GolayCode := ⟨gc_b₂,gc_b₂_mem⟩


example : to_hexacode' gc_b₂ = ω • b₁ + ω⁻¹ • b₂ := by decide

-- to_hexaCode' x =    ![ω,0,0,ω,1,ω⁻¹] = ω⁻¹ • b₁ + b₂
abbrev gc_b₃ := to_gc !![0,1,1,0,0,1;
                         0,0,0,0,1,1;
                         1,0,0,1,0,1;
                         0,0,0,0,0,0]
lemma gc_b₃_mem : gc_b₃ ∈ GolayCode := by decide

abbrev gc_b₃' : GolayCode := ⟨gc_b₃,gc_b₃_mem⟩

example : to_hexacode' gc_b₃ = ω⁻¹ • b₁ + b₂ := by decide

-- to_hexaCode' x =  ![ω⁻¹,0,0,ω⁻¹,ω,1] = b₁ + ω • b₂
abbrev gc_b₄ := to_gc !![0,1,1,0,0,1;
                         0,0,0,0,0,0;
                         0,0,0,0,1,1;
                         1,0,0,1,0,1]

lemma gc_b₄_mem : gc_b₄ ∈ GolayCode := by decide

abbrev gc_b₄' : GolayCode := ⟨gc_b₄,gc_b₄_mem⟩

example : to_hexacode' gc_b₄ = b₁ + ω • b₂ := by decide

-- to_hexaCode' x =   ![0,1,0,1,ω,ω⁻¹] = ω⁻¹ • b₁ + ω⁻¹ • b₂ + b₃
abbrev gc_b₅ := to_gc !![0,1,0,0,0,1;
                         0,1,0,0,1,0;
                         0,0,0,1,0,0;
                         0,0,0,1,1,1]

set_option maxHeartbeats 400000

lemma gc_b₅_mem : gc_b₅ ∈ GolayCode := by decide

abbrev gc_b₅' : GolayCode := ⟨gc_b₅,gc_b₅_mem⟩

example : to_hexacode' gc_b₅ = ω⁻¹ • b₁ + ω⁻¹ • b₂ + b₃ := by decide

-- to_hexaCode' x =   ![0,ω,0,ω,ω⁻¹,1] = b₁ + b₂ + ω • b₃
abbrev gc_b₆ := to_gc !![0,1,0,0,0,1;
                         0,0,0,1,1,1;
                         0,1,0,0,1,0;
                         0,0,0,1,0,0]

lemma gc_b₆_mem : gc_b₆ ∈ GolayCode := by decide

abbrev gc_b₆' : GolayCode := ⟨gc_b₆,gc_b₆_mem⟩

example : to_hexacode' gc_b₆ = b₁ + b₂ + ω • b₃ := by decide

-- to_hexaCode' x =   ![0,ω⁻¹,0,ω⁻¹,1,ω] = ω • b₁ + ω • b₂ + ω⁻¹ • b₃
abbrev gc_b₇ := to_gc !![0,1,0,0,0,1;
                         0,0,0,1,0,0;
                         0,0,0,1,1,1;
                         0,1,0,0,1,0]

lemma gc_b₇_mem : gc_b₇ ∈ GolayCode := by decide

abbrev gc_b₇' : GolayCode := ⟨gc_b₇,gc_b₇_mem⟩

example : to_hexacode' gc_b₇ = ω • b₁ + ω • b₂ + ω⁻¹ • b₃ := by decide

-- to_hexaCode' x =   ![0,0,1,1,1,1] = b₂ + b₃
abbrev gc_b₈ := to_gc !![0,0,1,0,0,1;
                         0,0,1,0,0,1;
                         0,0,0,1,1,0;
                         0,0,0,1,1,0]

lemma gc_b₈_mem : gc_b₈ ∈ GolayCode := by decide

abbrev gc_b₈' : GolayCode := ⟨gc_b₈,gc_b₈_mem⟩

example : to_hexacode' gc_b₈ = b₂ + b₃ := by decide

-- to_hexaCode' x =   ![0,0,ω,ω,ω,ω] = ω • b₂ + ω • b₃
abbrev gc_b₉ := to_gc !![0,0,1,0,0,1;
                         0,0,0,1,1,0;
                         0,0,1,0,0,1;
                         0,0,0,1,1,0]

lemma gc_b₉_mem : gc_b₉ ∈ GolayCode := by decide

abbrev gc_b₉' : GolayCode := ⟨gc_b₉,gc_b₉_mem⟩

example : to_hexacode' gc_b₉ = ω • b₂ + ω • b₃ := by decide

-- to_hexaCode' x =   ![0,0,ω⁻¹,ω⁻¹,ω⁻¹,ω⁻¹] = ω⁻¹ • b₂ + ω⁻¹ • b₃
abbrev gc_b₁₀ := to_gc !![0,0,1,0,0,1;
                          0,0,0,1,1,0;
                          0,0,0,1,1,0;
                          0,0,1,0,0,1]

lemma gc_b₁₀_mem : gc_b₁₀ ∈ GolayCode := by decide

abbrev gc_b₁₀' : GolayCode := ⟨gc_b₁₀,gc_b₁₀_mem⟩

example : to_hexacode' gc_b₁₀ = ω⁻¹ • b₂ + ω⁻¹ • b₃ := by decide

-- to_hexaCode' x =   ![0,0,0,0,0,0] = 0
abbrev gc_b₁₁ := to_gc !![0,0,0,1,0,1;
                          0,0,0,1,0,1;
                          0,0,0,1,0,1;
                          0,0,0,1,0,1]

lemma gc_b₁₁_mem : gc_b₁₁ ∈ GolayCode := by decide

abbrev gc_b₁₁' : GolayCode := ⟨gc_b₁₁,gc_b₁₁_mem⟩

example : to_hexacode' gc_b₁₁ = 0 := by decide

-- to_hexaCode' x =   ![0,0,0,0,0,0] = 0
abbrev gc_b₁₂ := to_gc !![0,0,0,0,1,1;
                          0,0,0,0,1,1;
                          0,0,0,0,1,1;
                          0,0,0,0,1,1]

lemma gc_b₁₂_mem : gc_b₁₂ ∈ GolayCode := by decide

abbrev gc_b₁₂' : GolayCode := ⟨gc_b₁₂,gc_b₁₂_mem⟩

example : to_hexacode' gc_b₁₂ = 0 := by decide

abbrev gc_basis_fam :=
  ![gc_b₁,gc_b₂,gc_b₃,gc_b₄,gc_b₅,gc_b₆,gc_b₇,gc_b₈,gc_b₉,gc_b₁₀,gc_b₁₁,gc_b₁₂]

abbrev gc_basis_fam' :=
  ![gc_b₁',gc_b₂',gc_b₃',gc_b₄',gc_b₅',gc_b₆',gc_b₇',gc_b₈',gc_b₉',gc_b₁₀',gc_b₁₁',gc_b₁₂']

-- #check gc_basis_fam

abbrev gc_basis_backwards : Fin 12 → ((Fin 6) × F4) :=
  ![(0,0),(0,1),(0,ω),(0,ω⁻¹),(1,1),(1,ω),(1,ω⁻¹),(2,1),(2,ω),(2,ω⁻¹),(3,0),(4,0)]

abbrev of_basis (m: golay_code_space') := ∑ j, (m (gc_basis_backwards j)) • gc_basis_fam j

lemma of_basis_mem (m:golay_code_space') : of_basis m ∈ GolayCode := by
  suffices hsuf : of_basis m = ∑ j, (m (gc_basis_backwards j)) • gc_basis_fam' j by
    rw [hsuf]
    exact (∑ j, (m (gc_basis_backwards j)) • gc_basis_fam' j).property
  rfl

lemma of_basis_index_eq (m:golay_code_space') ⦃c: Fin 6 × F4⦄ (hc:∃ i, c = gc_basis_backwards i) :
    m c =
    (of_basis m) c := by
  obtain ⟨i,hi⟩ := hc
  rw [hi]
  simp_rw [of_basis,gc_basis_backwards,gc_basis_fam,Finset.univ,Fintype.elems,List.finRange]
  simp only [List.pmap, Fin.zero_eta, Fin.mk_one, Finset.sum_mk, Multiset.map_coe, List.map_cons,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ',
    List.map_nil, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero, AddSubmonoid.coe_add,
    Submodule.coe_toAddSubmonoid, SetLike.val_smul]
  simp_rw [gc_b₁,gc_b₂,gc_b₃,gc_b₄,gc_b₅,gc_b₆,gc_b₇,gc_b₈,gc_b₉,gc_b₁₀,gc_b₁₁,gc_b₁₂]
  simp_rw [to_gc_map_smul]
  simp_rw [to_gc_map_add]
  simp only [Matrix.smul_of, Matrix.smul_cons, smul_eq_mul, mul_one, mul_zero, Matrix.smul_empty,
    Matrix.of_add_of, Matrix.add_cons, Matrix.head_cons, CharTwo.add_self_eq_zero, Matrix.tail_cons,
    add_zero, zero_add, Matrix.empty_add_empty]
  fin_cases i <;> rfl


def unfold_g (g : Fin 12 → ZMod 2) : golay_code_space' :=
  to_gc !![g 0, 0,   0,   g 10, g 11,0;
           g 1, g 4, g 7, 0,    0,   0;
           g 2, g 5, g 8, 0,    0,   0;
           g 3, g 6, g 9, 0,    0,   0]

lemma unfold_g_basis_reverse_eq (g:Fin 12 → ZMod 2) : unfold_g g ∘ (gc_basis_backwards) = g := by
  ext i
  fin_cases i <;> rfl

lemma gc_basis_linindep : LinearIndependent (ZMod 2) gc_basis_fam := by
  rw [ Fintype.linearIndependent_iff]
  intro g
  rw [(unfold_g_basis_reverse_eq g).symm]
  simp only [Function.comp_apply]
  intro h
  rw [Function.funext_iff] at h
  intro i
  exact (of_basis_index_eq (unfold_g g) ⟨i,by rfl⟩).symm ▸ h (gc_basis_backwards i)


lemma of_basis_column_one_parity (m:golay_code_space') :
    to_binary_vert' m 0 = (to_binary_vert' (of_basis m) 0) := by
  simp_rw [to_binary_vert'_apply]
  simp_rw [of_basis]
  simp only [AddSubmonoid.coe_finset_sum, Submodule.coe_toAddSubmonoid, SetLike.val_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  obtain hz₁ := of_basis_index_eq m ⟨0,by rfl⟩
  obtain hz₂ := of_basis_index_eq m ⟨1,by rfl⟩
  obtain hz₃ := of_basis_index_eq m ⟨2,by rfl⟩
  obtain hz₄ := @of_basis_index_eq m (0,ω⁻¹) ⟨3,by rfl⟩
  simp only [Matrix.cons_val_zero, AddSubmonoid.coe_finset_sum, Submodule.coe_toAddSubmonoid,
    SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] at hz₁ hz₂ hz₃ hz₄
  rw [hz₁,hz₂,hz₃,hz₄]

lemma of_basis_parity_hori ⦃m:golay_code_space'⦄ (hm : m ∈ GolayCode):
    to_binary_hori' m = to_binary_hori' (of_basis m) := by
  obtain ⟨_,hm₂⟩ := hm
  obtain ⟨_,hb₂⟩ := (of_basis_mem m)
  rw [Property2] at hm₂ hb₂
  rw [← hm₂ 0, ← hb₂ 0]
  exact of_basis_column_one_parity m

lemma of_basis_parity_vert ⦃m:golay_code_space'⦄ (hm : m ∈ GolayCode) (i:Fin 6):
    to_binary_vert' m i = to_binary_vert' (of_basis m) i := by
  let ⟨_,hm₂⟩ := hm
  obtain ⟨_,hb₂⟩ := (of_basis_mem m)
  rw [Property2] at hm₂ hb₂
  rw [hm₂ i, hb₂ i]
  exact of_basis_parity_hori hm

lemma indep' (a b c d:ZMod 2) : a • ω + b • ω⁻¹ = c • ω + d • ω⁻¹ ↔ a = c ∧ b = d :=
  ⟨by
    simp_rw [F4.omega_inv_eq,F4.smul_mk_apply,mul_one,mul_zero,F4.add_def,zero_add,add_zero]
    exact F4.ext_iff ⟨a,b⟩ ⟨c,d⟩ |>.mp,
  by
    intro h
    rw [h.left,h.right]⟩

lemma to_hexacode_binary_inv (m:golay_code_space') (i:Fin 6) {p:ZMod 2}
    (hp : to_binary_vert' m i = p):
    m (i,1) = (to_hexacode' m i).x0 + (to_hexacode' m i).x1 + p + m (i,0) ∧
    m (i,ω) = (to_hexacode' m i).x1 + p + m (i,0) ∧
    m (i,ω⁻¹) = (to_hexacode' m i).x0 + p + m (i,0) := by
  rw [to_binary_vert'_apply] at hp
  simp_rw [to_hexacode'_apply,F4.inv_def,F4.smul_mk_apply,F4.add_def, hp.symm]
  simp only [mul_one, mul_zero, add_zero, zero_add]
  abel_nf
  simp only [zsmul_eq_mul, Int.cast_ofNat]
  have foo : (2:ZMod 2) = 0 := rfl
  have bar : (3:ZMod 2) = 1 := rfl
  simp_rw [foo, bar]
  simp only [one_mul, zero_mul, zero_add, self_eq_add_right, and_self_left]
  simp_rw [F4.inv_def]
  simp only [CharTwo.add_self_eq_zero, and_self]

lemma of_basis_zero_eq_sum (m:golay_code_space') (i:Fin 6) :
    m (i,0) = to_binary_vert' m i + m (i,1) + m (i,ω) + m (i,ω⁻¹) := by
  rw [to_binary_vert'_apply]
  group
  simp only [Int.reduceNeg, zpow_neg, zpow_one]
  have foo: (2:ZMod 2) = 0 := rfl
  simp_rw [foo]
  simp only [mul_zero, add_zero]

lemma of_basis_six_eq (m:golay_code_space') :
    m (⟨5,by linarith⟩,0) = to_binary_hori' m + m (⟨0,by linarith⟩,0) + m (⟨1,by linarith⟩,0) +
      m (⟨2,by linarith⟩,0) + m (⟨3,by linarith⟩,0) + m (⟨4,by linarith⟩,0) := by
  have foo : (2:ZMod 2) = 0 := rfl
  calc
    m (5,0) = to_binary_hori' m + m (0,0) + m (1,0) + m (2,0) + m (3,0) + m (4,0) := by
      rw [to_binary_hori'_apply]
      group
      simp_rw [foo,mul_zero,zero_add]


lemma of_basis_hexacode_left_eq (m:golay_code_space') :
    ∀ i:Fin 3, to_hexacode' m i = to_hexacode' (of_basis m) i := by
  intro i
  simp_rw [to_hexacode'_apply]
  rw [indep']
  fin_cases i
  . rw [@of_basis_index_eq m (((⟨0,by linarith⟩:Fin 3):Fin 6),1) ⟨1,rfl⟩]
    rw [@of_basis_index_eq m (((⟨0,by linarith⟩:Fin 3):Fin 6),ω) ⟨2,rfl⟩]
    rw [@of_basis_index_eq m (((⟨0,by linarith⟩:Fin 3):Fin 6),ω⁻¹) ⟨3,rfl⟩]
    simp only [Nat.cast_zero, AddSubmonoid.coe_finset_sum, Submodule.coe_toAddSubmonoid,
      SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, and_self]
  . rw [@of_basis_index_eq m (((⟨1,by linarith⟩:Fin 3):Fin 6),1) ⟨4,rfl⟩]
    rw [@of_basis_index_eq m (((⟨1,by linarith⟩:Fin 3):Fin 6),ω) ⟨5,rfl⟩]
    rw [@of_basis_index_eq m (((⟨1,by linarith⟩:Fin 3):Fin 6),ω⁻¹) ⟨6,rfl⟩]
    simp only [Nat.cast_one, AddSubmonoid.coe_finset_sum, Submodule.coe_toAddSubmonoid,
      SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, and_self]
  . rw [@of_basis_index_eq m (((⟨2,by linarith⟩:Fin 3):Fin 6),1) ⟨7,rfl⟩]
    rw [@of_basis_index_eq m (((⟨2,by linarith⟩:Fin 3):Fin 6),ω) ⟨8,rfl⟩]
    rw [@of_basis_index_eq m (((⟨2,by linarith⟩:Fin 3):Fin 6),ω⁻¹) ⟨9,rfl⟩]
    simp only [Nat.cast_ofNat, AddSubmonoid.coe_finset_sum, Submodule.coe_toAddSubmonoid,
      SetLike.val_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, and_self]

lemma of_basis_hexacode_eq ⦃m : golay_code_space'⦄ (hm : m ∈ GolayCode) :
    to_hexacode' m = to_hexacode' (of_basis m) := by
  rw [(mem_hc_iff (to_hexacode' m)).mp hm.left]
  rw [(mem_hc_iff (to_hexacode' (of_basis m))).mp (of_basis_mem m).left]
  ext i : 1
  fin_cases i <;> simp only [Fin.zero_eta,Matrix.cons_val_zero,Matrix.cons_val_succ',
    Fin.mk_one,Matrix.cons_val_one,Matrix.head_cons]
  have_goal h1 := of_basis_hexacode_left_eq m 0
  have_goal h2 := of_basis_hexacode_left_eq m 1
  have_goal h3 := of_basis_hexacode_left_eq m 2
  all_goals simp_rw [h1, h2, h3]


lemma of_basis_left ⦃m:golay_code_space'⦄ (hm:m ∈ GolayCode) (i:Fin 3) (x:F4) :
    m (i,x) = (of_basis m : golay_code_space') (i,x) := by
  fin_cases i
  . fin_cases x
    . exact @of_basis_index_eq m (((⟨0,by linarith⟩:Fin 3):Fin 6),0) ⟨0,rfl⟩
    . exact @of_basis_index_eq m (((⟨0,by linarith⟩:Fin 3):Fin 6),1) ⟨1,rfl⟩
    . exact @of_basis_index_eq m (((⟨0,by linarith⟩:Fin 3):Fin 6),ω) ⟨2,rfl⟩
    . exact @of_basis_index_eq m (((⟨0,by linarith⟩:Fin 3):Fin 6),ω⁻¹) ⟨3,rfl⟩
  . fin_cases x
    skip_goal
    have_goal h5 := @of_basis_index_eq m (((⟨1,by linarith⟩:Fin 3):Fin 6),1) ⟨4,rfl⟩
    have_goal h6 := @of_basis_index_eq m (((⟨1,by linarith⟩:Fin 3):Fin 6),ω) ⟨5,rfl⟩
    have_goal h7 := @of_basis_index_eq m (((⟨1,by linarith⟩:Fin 3):Fin 6),ω⁻¹) ⟨6,rfl⟩
    simp_rw [of_basis_zero_eq_sum]
    rw [h5,h6,h7,of_basis_parity_vert hm]
  . fin_cases x
    skip_goal
    have_goal h8 := @of_basis_index_eq m (((⟨2,by linarith⟩:Fin 3):Fin 6),1) ⟨7,rfl⟩
    have_goal h9 := @of_basis_index_eq m (((⟨2,by linarith⟩:Fin 3):Fin 6),ω) ⟨8,rfl⟩
    have_goal h10 := @of_basis_index_eq m (((⟨2,by linarith⟩:Fin 3):Fin 6),ω⁻¹) ⟨9,rfl⟩
    simp_rw [of_basis_zero_eq_sum]
    rw [h8,h9,h10,of_basis_parity_vert hm]

lemma of_basis_zero_eq ⦃m:golay_code_space'⦄ (hm:m∈ GolayCode) (i:Fin 6) :
    m (i,0) = (of_basis m : golay_code_space') (i,0) := by
  fin_cases i
  have_goal h1 := of_basis_index_eq m ⟨0,rfl⟩
  have_goal h2 := of_basis_left hm ⟨1,by linarith⟩ 0
  have_goal h3 := of_basis_left hm ⟨2,by linarith⟩ 0
  have_goal h4 := of_basis_index_eq m ⟨10,rfl⟩
  have_goal h5 := of_basis_index_eq m ⟨11,rfl⟩
  rw [of_basis_six_eq m, of_basis_six_eq (of_basis m)]
  rw [h1,h2,h3,h4,h5]
  rw [of_basis_parity_hori hm]

lemma of_basis_eq ⦃m:golay_code_space'⦄ (hm:m ∈ GolayCode): m = of_basis m := by
  ext ⟨i,x⟩
  obtain ⟨hz₁,hz₂,hz₃⟩ := to_hexacode_binary_inv m i (hm.right i)
  rw [of_basis_hexacode_eq hm,of_basis_parity_hori hm] at hz₁ hz₂ hz₃
  obtain ⟨hz₁',hz₂',hz₃'⟩ := to_hexacode_binary_inv (of_basis m) i ((of_basis_mem m).right i)
  fin_cases x
  have_goal h0 := of_basis_zero_eq hm i
  . rw [hz₁,hz₁',h0]
  . rw [hz₂,hz₂',h0]
  . rw [hz₃,hz₃',h0]

noncomputable def gc_basis' :
    Basis (Fin 12) (ZMod 2) (Submodule.span (ZMod 2) (Set.range gc_basis_fam)) :=
  Basis.span gc_basis_linindep


-- #check gc_basis'

lemma gc_span_is_gc : Submodule.span (ZMod 2) (Set.range gc_basis_fam) = GolayCode := by
  ext x
  constructor
  . intro h
    exact Submodule.span_induction h
      (by
        intro b hb
        simp_rw [Set.mem_range] at hb
        obtain ⟨i,hi⟩ := hb
        simp_rw [hi.symm]
        obtain hz := (gc_basis_fam' i).property
        fin_cases i <;> exact hz)
      (GolayCode.zero_mem)
      (fun x y => GolayCode.add_mem)
      (fun r m hm => GolayCode.smul_mem r hm)
  . intro h
    rw [of_basis_eq h,of_basis]
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton,
      Set.union_insert]
    rw [Submodule.mem_span]
    intro p hp
    rw [Set.subset_def] at hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, SetLike.mem_coe, forall_eq_or_imp,
      forall_eq] at hp
    obtain ⟨h12,h11,h10,h9,h8,h7,h6,h5,h4,h3,h2,h1⟩ := hp
    simp_rw [Finset.univ,Fintype.elems,List.finRange,gc_basis_fam]
    simp only [List.pmap, Fin.zero_eta, Fin.mk_one, Finset.sum_mk, Multiset.map_coe, List.map_cons,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_succ',
      List.map_nil, Multiset.sum_coe, List.sum_cons, List.sum_nil, add_zero]
    repeat' apply p.add_mem
    all_goals apply p.smul_mem
    exact h1; exact h2; exact h3; exact h4; exact h5; exact h6
    exact h7; exact h8; exact h9; exact h10; exact h11; exact h12

noncomputable def gc_basis : Basis (Fin 12) (ZMod 2) GolayCode := gc_span_is_gc ▸ gc_basis'

lemma card_golayCode : Fintype.card GolayCode = 4096 := by
  rw [Module.card_fintype gc_basis]
  simp only [ZMod.card, Fintype.card_fin, Nat.reducePow]

lemma vadd_map_to_binary_vert (f:F_4_6) (x:golay_code_space') :
    to_binary_vert' x = to_binary_vert' (f +ᵥ x) := by
  simp_rw [to_binary_vert',HVAdd.hVAdd,VAdd.vadd]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Function.uncurry_apply_pair, Pi.vadd_apply']
  simp_rw [HVAdd.hVAdd,VAdd.vadd]
  simp only [Equiv.symm_apply_apply, vadd_eq_add, Function.curry_apply]
  ext i
  rw [← Equiv.sum_comp (?equiv : F4 ≃ F4) (fun x_1 => x (i,x_1))]
  case equiv =>
    exact Equiv.addLeft (f i)
  rfl


lemma vadd_zero (f:F_4_6) : f +ᵥ (0:golay_code_space') = 0 := rfl


set_option maxHeartbeats 500000
lemma vadd_mem_GolayCode ⦃f:F_4_6⦄ (hf : f ∈ HexaCode) : ∀ x ∈ GolayCode, f +ᵥ x ∈ GolayCode := by
  refine Submodule.closure_induction hf ?zero ?add ?smul_mem
  . simp only [zero_vadd, imp_self, forall_const]
  . intro f g hf hg
    intro x hx
    rw [add_vadd]
    exact hf (g +ᵥ x) (hg x hx)
  intro r
  have hr : r ∈ AddSubmonoid.closure (Set.range ![ω,ω⁻¹]) := F4.top_le_closure trivial
  refine AddSubmonoid.closure_induction hr ?mem ?zero' ?add'
  case zero' => simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.union_singleton, Set.union_insert, Set.mem_insert_iff, Set.mem_singleton_iff, zero_smul,
    zero_vadd, imp_self, forall_const, implies_true]
  case add' =>
    intro r₁ r₂ hr₁ hr₂
    intro f hf x hx
    simp_rw [add_smul,add_vadd]
    apply hr₁ f hf
    apply hr₂ f hf x hx
  intro r hr
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton,
    Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  intro f hf
  intro x hx
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton,
    Set.union_insert, Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rw [gc_span_is_gc.symm] at hx
  refine Submodule.span_induction hx ?basis ?zero'' ?add'' ?smul
  case zero'' => rw [vadd_zero]; decide
  case add'' =>
    intro x y hx hy
    rw [← vadd_add_distrib]
    exact add_mem hx hy
  case smul =>
    intro a x hx
    fin_cases a <;> simp only [Fin.zero_eta, zero_smul]
    . rw [vadd_zero] ; decide
    . simp only [Fin.mk_one, one_smul]
      exact hx
  intro x hx
  simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.union_singleton,
    Set.union_insert, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  obtain rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl := hx
  all_goals obtain rfl | rfl := hr
  all_goals obtain rfl | rfl | rfl := hf
  all_goals decide

-- @[simps]
def GolayCode.lift_hexacode_mem ⦃f:F_4_6⦄ (hf : f ∈ HexaCode) :
    SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode := {
  fst := RingEquiv.refl (ZMod 2)
  snd :=
  letI inst := RingHomInvPair.of_ringEquiv (RingEquiv.refl (ZMod 2))
  letI := inst.symm
  {
  AddAction.toPerm f with
  map_dist := fun x y => by
    simp only
    exact mem_vadd_map_dist f x y
  map_code := fun x hx => by
    simp only [Equiv.toFun_as_coe, AddAction.toPerm_apply, SetLike.mem_coe]
    simp only [SetLike.mem_coe] at hx
    exact vadd_mem_GolayCode hf x hx
  invMap_code := fun x hx => by
    simp only [Equiv.toFun_as_coe, AddAction.toPerm_apply, SetLike.mem_coe] at hx ⊢
    suffices hsuf : x = f +ᵥ (f +ᵥ x) by
      rw [hsuf]
      exact vadd_mem_GolayCode hf (f +ᵥ x) hx
    rw [← add_vadd]
    have hfoo : f + f = 0 := by
      ext i : 1
      simp only [Pi.add_apply, CharTwo.add_self_eq_zero, Pi.zero_apply]
    rw [hfoo]
    rw [zero_vadd]
  map_add' := by
    simp only [Equiv.toFun_as_coe, AddAction.toPerm_apply]
    intro x y
    exact vadd_add_distrib f x y
  map_smul' := by
    simp only [Equiv.toFun_as_coe, AddAction.toPerm_apply, RingHom.id_apply]
    intro r x
    fin_cases r
    . simp only [Fin.zero_eta, zero_smul, RingEquiv.coe_ringHom_refl, map_zero]
      rw [vadd_zero]
    . simp only [Fin.mk_one, one_smul, RingEquiv.coe_ringHom_refl, map_one]
  }}



def HexaCode.toGolayAut_MulHom :
    Multiplicative HexaCode →* SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode where
      toFun := fun f => GolayCode.lift_hexacode_mem f.property
      map_one' := by
        simp_rw [GolayCode.lift_hexacode_mem]
        simp only [RingEquiv.coe_ringHom_refl, RingEquiv.symm_refl, Equiv.toFun_as_coe,
          Equiv.invFun_as_coe, SemilinearCodeAut.mk_apply']
        ext v : 1
        . rfl
        simp only [RingEquiv.coe_ringHom_refl, RingEquiv.symm_refl, Equiv.toFun_as_coe, id_eq,
          AddHom.toFun_eq_coe, RingHom.id_apply, LinearMap.coe_toAddHom, Equiv.invFun_as_coe,
          AddHom.coe_mk, hammingENatdist_eq_cast_hammingDist, LinearEquiv.coe_coe,
          SemilinearCodeAut.coe_one]
        simp_rw [DFunLike.coe,EquivLike.coe]
        simp only [Equiv.toFun_as_coe, AddAction.toPerm_apply]
        exact zero_vadd (F_4_6) v
      map_mul' := fun x y => by
        simp_rw [GolayCode.lift_hexacode_mem]
        simp only [RingEquiv.coe_ringHom_refl, RingEquiv.symm_refl, Equiv.toFun_as_coe,
          Equiv.invFun_as_coe]
        ext v : 1
        . rfl
        simp_rw [DFunLike.coe,EquivLike.coe]
        simp only [Equiv.toFun_as_coe, AddAction.toPerm_apply, RingEquiv.coe_ringHom_refl,
          RingEquiv.symm_refl, SemilinearCodeEquiv.toLinearEquiv_eq_coe, AddHom.toFun_eq_coe,
          LinearMap.coe_toAddHom, LinearEquiv.coe_coe, SemilinearCodeEquiv.coe_toLinearEquiv,
          SemilinearCodeAut.coe_mul, SemilinearCodeEquiv.coe_mk, LinearEquiv.coe_mk,
          Function.comp_apply]
        rw [← add_vadd]
        rfl


instance : DistribMulAction (SemilinearCodeAut F4 trivdist hdist HexaCode) HexaCode where
  smul := fun φ x => ⟨φ • x, φ.snd.map_code x x.property⟩
  one_smul := fun b => by
    ext : 1
    simp only [HSMul.hSMul, SMul.smul, SemilinearCodeAut.coe_one, id_eq, Subtype.coe_eta]
  mul_smul := fun x y b => by
    ext : 1
    simp only [HSMul.hSMul, SMul.smul]
    exact mul_smul x y (b : F_4_6)
  smul_zero := fun a => by
    ext : 1
    simp only [HSMul.hSMul, SMul.smul, ZeroMemClass.coe_zero, map_zero]
  smul_add := fun a x y => by
    ext : 1
    simp only [HSMul.hSMul, SMul.smul, AddSubmonoid.coe_add, Submodule.coe_toAddSubmonoid, map_add,
      AddSubmonoid.mk_add_mk]


instance : MulDistribMulAction -- really i should want this to be automatic
  (SemilinearCodeAut F4 trivdist hdist HexaCode)
  (Multiplicative HexaCode) where
    smul := fun φ x => Multiplicative.ofAdd (φ • Multiplicative.toAdd x)
    one_smul := fun b => by
      simp only [HSMul.hSMul, SMul.smul, SemilinearCodeAut.coe_one, id_eq, Subtype.coe_eta,
        ofAdd_toAdd]
    mul_smul := fun x y b => by
      simp only [HSMul.hSMul, SMul.smul, SemilinearCodeAut.coe_mul, Function.comp_apply,
        toAdd_ofAdd]
    smul_mul := fun r x y => by
      simp only [HSMul.hSMul, SMul.smul, toAdd_mul, AddSubmonoid.coe_add,
        Submodule.coe_toAddSubmonoid, map_add]
      rfl
    smul_one := fun r => by
      simp only [HSMul.hSMul, SMul.smul, toAdd_one, ZeroMemClass.coe_zero, map_zero, ofAdd_eq_one,
        Submodule.mk_eq_zero]

-- #synth MulAction (Multiplicative HexaCode) (golay_code_space')

noncomputable abbrev apply_aut :
    SemilinearCodeAut F4 trivdist hdist HexaCode →* MulAut (Multiplicative HexaCode) :=
  MulDistribMulAction.toMulAut
    (SemilinearCodeAut F4 trivdist hdist HexaCode)
    (Multiplicative HexaCode)

-- #check (Multiplicative HexaCode ⋊[apply_aut] (SemilinearCodeAut F4 trivdist hdist HexaCode))

-- #print axioms HexaCode.toGolayAut_MulHom
-- #check extract_gives_stuff_strong

lemma lift_hexacode_aut_apply_apply (φ : SemilinearCodeAut F4 trivdist hdist HexaCode) (m: golay_code_space')
    (i:Fin 6) (x : F4) : (GolayCode.lift_hexacode_aut φ) m (i,x) = m (φ⁻¹ • (i,x)) := by
  rfl

lemma f4aut_smul_index_def (φ : SemilinearCodeAut F4 trivdist hdist HexaCode) (i:Fin 6) (x:F4) :
    φ • (i,x) = (extract_perm φ i, φ.fst (extract_diag φ i * x)) := rfl

-- #synth SMul (Multiplicative HexaCode) (Fin 6 × F4)

lemma lift_hexacode_mem_apply_apply (f : HexaCode) (m:golay_code_space') (i:Fin 6) (x : F4) :
    HexaCode.toGolayAut_MulHom f m (i,x) = m ((i, (f : F_4_6) i + x)) := by rfl

lemma semiaut_fst_map_inv (φ : SemilinearCodeAut F4 trivdist hdist HexaCode) : φ⁻¹.fst = φ.fst⁻¹ := rfl

lemma aut_smul_hexacode (φ : SemilinearCodeAut F4 trivdist hdist HexaCode) (v:HexaCode):
    φ • (Multiplicative.ofAdd v) = Multiplicative.ofAdd (φ • v) := rfl

-- #synth AddCommGroup F4
abbrev hexa_gen_aut : Type
  := Multiplicative HexaCode ⋊[apply_aut] (SemilinearCodeAut F4 trivdist hdist HexaCode)


noncomputable def apply_hexacode_semi :
    (Multiplicative HexaCode ⋊[apply_aut] (SemilinearCodeAut F4 trivdist hdist HexaCode)) →*
    SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode :=
  SemidirectProduct.lift (HexaCode.toGolayAut_MulHom) (GolayCode.lift_hexacode_aut) (by
    intro φ
    simp only [MulDistribMulAction.toMulAut_apply]
    ext v : 1
    rw [← ofAdd_toAdd v]
    obtain v := Multiplicative.toAdd v
    simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Multiplicative.toAdd_symm_eq, ofAdd_toAdd,
      MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      MulDistribMulAction.toMulEquiv_apply, MulAut.conj_apply]
    ext m : 1
    . rfl
    ext ⟨i,x⟩ : 1
    simp only [SemilinearCodeAut.coe_mul, Function.comp_apply]
    rw [lift_hexacode_aut_apply_apply]
    rw [f4aut_smul_index_def]
    rw [lift_hexacode_mem_apply_apply,lift_hexacode_mem_apply_apply]
    rw [← map_inv]
    rw [lift_hexacode_aut_apply_apply]
    rw [f4aut_smul_index_def]
    congr
    . simp only [inv_inv]
      rw [extract_perm_map_inv]
      rw [Equiv.Perm.apply_inv_self]
    -- simp_rw [toGolayAut_MulHom]
    -- simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    simp_rw [inv_inv]
    rw [extract_diag_map_inv']
    simp only [semiaut_fst_map_inv, map_mul,map_add]
    have foo : φ.fst⁻¹ = φ.fst.symm := rfl
    rw [foo]
    simp only [RingEquiv.apply_symm_apply]
    rw [aut_smul_hexacode]
    simp only [smul_inv', Prod.smul_def', Pi.inv_apply, Pi.smul_apply, Units.val_inv_eq_inv_val]
    have foo2 : (Multiplicative.ofAdd v : HexaCode) = v := rfl
    rw [foo2]
    rw [left_distrib]
    rw [← Units.smul_val_eq_val_smul φ.fst]
    have foo3 : φ.fst ↑(extract_diag φ ((extract_perm φ⁻¹) i)) * φ.fst ((v : F_4_6) ((extract_perm φ⁻¹) i)) = (φ • v : F_4_6) i := by
      symm
      calc
        (φ • v : F_4_6) i
          = (φ v) i := rfl
        _ = (φ.fst • extract_perm φ • (extract_diag φ • (v : F_4_6))) i := by
            rw [extract_gives_stuff_strong]
        _ = (φ.fst ∘ (extract_diag φ • (v : F_4_6)) ∘ extract_perm φ⁻¹) i := rfl
        _ = φ.fst (extract_diag φ (extract_perm φ⁻¹ i) * (v : F_4_6) (extract_perm φ⁻¹ i)) := rfl
        _ = _ := by
          rw [map_mul]
    rw [foo3]
    suffices x = _ by
      nth_rw 1 [this]
      rfl
    symm
    calc
      φ.fst ↑(extract_diag φ ((extract_perm φ⁻¹) i)) * ((φ.fst • ↑((extract_perm φ • extract_diag φ) i))⁻¹ * x)
        = (φ.fst ↑(extract_diag φ ((extract_perm φ⁻¹) i)) * (φ.fst • ↑((extract_perm φ • extract_diag φ) i))⁻¹) * x := by
          rw [mul_assoc]
      _ = φ.fst (↑(extract_diag φ ((extract_perm φ⁻¹) i)) * (↑((extract_perm φ • extract_diag φ) i))⁻¹) * x := by
        rw [map_mul,map_inv₀]
        rfl
      _ = φ.fst (↑(extract_diag φ ((extract_perm φ⁻¹) i)) * ↑(((extract_perm φ • extract_diag φ) i)⁻¹)) * x := by
        rw [Units.val_inv_eq_inv_val]
      _ = φ.fst ↑((extract_diag φ ((extract_perm φ⁻¹) i)) * (((extract_perm φ • extract_diag φ) i)⁻¹ )) * x := by
        rw [Units.val_mul]
      _ = φ.fst ↑((extract_diag φ ((extract_perm φ⁻¹) i)) * (((extract_diag φ) (extract_perm φ⁻¹ i))⁻¹)) * x := rfl
      _ = φ.fst ↑(1 : F4ˣ) * x := by rw [mul_inv_self]
      _ = x := by rw [Units.val_one,map_one,one_mul]
  )


example : True := trivial



lemma toGolayAut_MulHom_inj : Function.Injective toGolayAut_MulHom := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  simp_rw [MonoidHom.mem_ker,DFunLike.ext_iff]
  intro v
  rw [← ofAdd_toAdd v]
  generalize Multiplicative.toAdd v = v' at *
  simp only [ofAdd_eq_one]
  simp_rw [Function.funext_iff]
  simp_rw [DFunLike.coe, EquivLike.coe]
  simp only [Equiv.toFun_as_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
    SemilinearCodeAut.coe_one, id_eq, Prod.forall]
  intro hv
  ext i : 2
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply]
  specialize hv (fun (_,x) => if x = 0 then 1 else 0) i 0
  rw [lift_hexacode_mem_apply_apply] at hv
  simp only [add_zero, ↓reduceIte, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not] at hv
  rw [← hv]
  rfl

lemma GolayCode.lift_hexacode_aut_inj : Function.Injective GolayCode.lift_hexacode_aut := by
  rw [← MonoidHom.ker_eq_bot_iff,Subgroup.eq_bot_iff_forall]
  simp_rw [MonoidHom.mem_ker, DFunLike.ext_iff,DFunLike.coe,EquivLike.coe]
  simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, SemilinearCodeAut.coe_one, id_eq]
  intro φ
  intro hφ v
  simp_rw [Function.funext_iff] at hφ
  simp only [Prod.forall] at hφ
  simp_rw [lift_hexacode_aut_apply_apply,HSMul.hSMul,SMul.smul] at hφ
  simp_rw [extract_gives_stuff_strong]
  ext i : 1
  specialize hφ (fun (j,x) => if i = j ∧ x = v i then 1 else 0) i (v i)
  simp only [RingAut.smul_def, and_self, ↓reduceIte, ite_eq_left_iff, not_and, zero_ne_one,
    imp_false, Classical.not_imp, Decidable.not_not] at hφ
  rw [extract_diag_map_inv'] at hφ
  obtain ⟨hperm,hval⟩ := hφ
  simp_rw [HSMul.hSMul,SMul.smul] at hval ⊢
  simp only [DomMulAct.mk_inv, RingAut.smul_def]
  simp_rw [HSMul.hSMul,SMul.smul] at hval ⊢
  simp_rw [HSMul.hSMul,SMul.smul] at hval
  simp only [DomMulAct.mk_inv, DomMulAct.symm_mk_inv, Equiv.symm_apply_apply, Equiv.Perm.smul_def,
    Pi.inv_apply, Units.val_inv_eq_inv_val, smul_inv'', Units.smul_val_eq_val_smul, map_mul,
    map_inv₀, smul_eq_mul] at hval ⊢
  rw [← Units.smul_val_eq_val_smul] at hval
  rw [← extract_perm_map_inv,← hperm] at hval ⊢
  nth_rw 1 [← hval]
  calc
    φ.fst ↑(extract_diag φ i) * φ.fst ((φ⁻¹.fst (φ.fst • ↑(extract_diag φ i)))⁻¹ * φ.fst⁻¹ (v i))
      = φ.fst ↑(extract_diag φ i) * φ.fst ((φ.fst⁻¹ (φ.fst • ↑(extract_diag φ i)))⁻¹ * φ.fst⁻¹ (v i)) := rfl
    _ = φ.fst ↑(extract_diag φ i) * φ.fst (φ.fst⁻¹ (φ.fst • ↑(extract_diag φ i))⁻¹ * φ.fst⁻¹ (v i)) := by
        rw [map_inv₀]
    _ = φ.fst ↑(extract_diag φ i) * φ.fst (φ.fst⁻¹ ((φ.fst • ↑(extract_diag φ i))⁻¹ * (v i))) := by
        rw [map_mul φ.fst⁻¹]
    _ = φ.fst ↑(extract_diag φ i) * φ.fst (φ.fst.symm ((φ.fst ↑(extract_diag φ i))⁻¹ * (v i))) := rfl
    _ = φ.fst ↑(extract_diag φ i) * ((φ.fst ↑(extract_diag φ i))⁻¹ * (v i)) := by
      rw [RingEquiv.apply_symm_apply]
    _ = φ.fst ↑(extract_diag φ i) * (φ.fst ↑(extract_diag φ i))⁻¹ * (v i) := by rw [mul_assoc]
    _ = v i := by simp only [isUnit_iff_ne_zero, ne_eq, AddEquivClass.map_eq_zero_iff,
      Units.ne_zero, not_false_eq_true, IsUnit.mul_inv_cancel, one_mul]

theorem lift_mem_lift_aut_indep : toGolayAut_MulHom.range ⊓ GolayCode.lift_hexacode_aut.range = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  simp only [Subgroup.mem_inf, MonoidHom.mem_range, Multiplicative.exists, Subtype.exists,
    and_imp, forall_exists_index]
  intro φ' v hv hv' φ
  intro hφ
  obtain rfl := hv'
  rw [DFunLike.ext_iff] at hφ ⊢
  intro m
  simp_rw [DFunLike.coe,EquivLike.coe] at hφ ⊢
  simp_rw [Function.funext_iff] at hφ
  simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, Equiv.toFun_as_coe, Prod.forall,
    SemilinearCodeAut.coe_one, id_eq] at hφ ⊢
  ext ⟨i,x⟩
  simp_rw [lift_hexacode_mem_apply_apply] at hφ ⊢
  simp_rw [lift_hexacode_aut_apply_apply] at hφ
  suffices m (i, v i + x) = m (i,x) by
    exact this
  suffices v i = 0 by
    rw [this]
    simp only [Pi.zero_apply, zero_add]
  specialize hφ (fun (_,y) => if y = 0 then 1 else 0) i 0
  simp only [smul_zero, ↓reduceIte, add_zero] at hφ
  have hφ': (1 : ZMod 2) = if v i = 0 then 1 else 0 := hφ
  split at hφ'
  . rename_i h
    exact h
  . contradiction

lemma apply_hexacode_semi_inj : Function.Injective apply_hexacode_semi := by
  dsimp [apply_hexacode_semi]
  apply SemidirectProduct.lift_inj
  . exact toGolayAut_MulHom_inj
  . exact GolayCode.lift_hexacode_aut_inj
  . exact lift_mem_lift_aut_indep

section
-- -- todo: figure out a way to do this without something blabla.
-- abbrev gc := gc_basis_fam

-- abbrev a₁ := gc 0 + gc 6 + gc 9 -- (0,0)
-- #eval of_gc (a₁)
-- #eval a₁.to_finset.card

-- abbrev a₂ := gc 1 + gc 6 + gc 9 -- (0,1)
-- #eval of_gc a₂
-- #eval a₂.to_finset.card

-- abbrev a₃ := gc 2 + gc 6 + gc 9 -- (0,2)
-- #eval of_gc a₃
-- #eval a₃.to_finset.card

-- abbrev a₄ := gc 3 + gc 6 + gc 9 -- (0,3)
-- #eval of_gc a₄
-- #eval a₄.to_finset.card

-- abbrev a₅ := gc 6 -- (1,0)
-- #eval of_gc a₅
-- #eval a₅.to_finset.card

-- abbrev a₆ := gc 4 + gc 6-- (1,1)
-- #eval of_gc a₆
-- #eval a₆.to_finset.card

-- abbrev a₇ := gc 5 + gc 6 -- (1,2)
-- #eval of_gc a₇
-- #eval a₇.to_finset.card

-- abbrev a₈ := gc 9 -- (2,0)
-- #eval of_gc a₈
-- #eval a₈.to_finset.card

-- abbrev a₉ := gc 7 + gc 9 -- (2,1)
-- #eval of_gc a₉
-- #eval a₉.to_finset.card

-- abbrev a₁₀ := gc 8 + gc 9
-- #eval of_gc a₁₀
-- #eval a₁₀.to_finset.card

-- abbrev a₁₁ := gc 10
-- #eval of_gc a₁₁
-- #eval a₁₁.to_finset.card

-- abbrev a₁₂ := gc 11
-- #eval of_gc a₁₂
-- #eval a₁₂.to_finset.card

-- abbrev a : Fin 12 → golay_code_space' := ![a₁,a₂,a₃,a₄,a₅,a₆,a₇,a₈,a₉,a₁₀,a₁₁,a₁₂]

-- #eval of_gc (a 0)

-- abbrev spike (c : Fin 6 × F4) : golay_code_space' := fun x => if x = c then 1 else 0
-- abbrev left : golay_code_space' := to_gc !![1,1,1,1,1,0;1,1,1,0,0,0;1,1,1,0,0,0;1,0,0,0,0,0]
-- abbrev right : golay_code_space' := 1 + left

-- abbrev count (x:golay_code_space') : ℕ := x.to_finset.card
-- #eval  count ∘ (((a₁₂ * a₁ + a₂ * a₁₀) • right • a))
-- #eval of_gc (a₂ * a₁₀ + a₁ * a₁₂)
-- /-
-- a₁ * a₁₂ => (6,1) (5,ω)
-- a₂ * a₁₀ => (6,ω) (3,ω⁻¹)
-- a₃ * a₆ => (2,ω⁻¹) (6,ω⁻¹)
-- a₄ * a₁₁ => (6,0) (4,ω⁻¹)
-- a₅ * a₉ => (4,1) (5,ω⁻¹)
-- a₇ * a₈ => (5,1) (4,ω)



-- -/
-- #eval of_gc (a₂ * a₁)
end

lemma eq_one_iff_norm (x : golay_code_space') : addGNorm hdist x = 24 ↔ x = 1 := by
  dsimp [addGNorm]
  constructor
  . intro h
    rw [← @Nat.cast_eq_ofNat ENat ] at h
    rw [Nat.cast_inj] at h
    dsimp [hammingNorm] at h
    have : Fintype.card golay_code_index = 24 := by decide
    rw [← this] at h
    have : Finset.filter (fun x_1 => ¬ x x_1 = 0) Finset.univ = Finset.univ := by
      exact Finset.eq_univ_of_card _ h
    rw [Finset.eq_univ_iff_forall] at this
    ext c
    specialize this c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    rw [Pi.one_apply]
    revert this
    generalize x c = z
    revert z
    decide
  rintro rfl
  decide

instance : BooleanRing (ZMod 2) where
  mul_self := by decide

instance : MulSemiringAction (SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode) golay_code_space' where
  smul_one := fun g => by
    rw [← eq_one_iff_norm (g • 1)]
    dsimp [SMul.smul]
    have : addGNorm hdist 1 = 24 := by
      rw [eq_one_iff_norm]
    rw [← this]
    exact g.map_addGNorm 1
  smul_mul := fun g a b => by
    dsimp [SMul.smul]
    simp_rw [extract_gives_stuff_strong]
    ext ⟨i,x⟩
    simp only [Pi.smul_apply, RingAut.smul_def, Pi.mul_apply]
    dsimp [HSMul.hSMul,SMul.smul]
    simp only [Equiv.symm_apply_apply, map_mul]
    ring_nf
    rw [pow_two,mul_self]
