import Mathlib.InformationTheory.Code.Linear.Mathieu.HexaCode
import Mathlib.Algebra.Module.Equiv
import Mathlib.Topology.GMetric.GNorm


open BigOperators
abbrev golay_code_index := Fin 6 × F4

-- this seems akin to a Semidirect Product of some sort... but not quite

-- you can interpret this as the Aut map acting on the element `r • b i`
noncomputable instance : MulAction (SemilinearCodeAut F4 trivdist hdist HexaCode) golay_code_index where
  smul := fun f ⟨i,x⟩=> ⟨(extract_perm f) i, f.fst • (extract_diag f i) • x⟩
  one_smul := fun ⟨i,x⟩ => by
    simp_rw [HSMul.hSMul,SMul.smul]
    rw [extract_perm_map_one,extract_diag_map_one]
    simp only [Equiv.Perm.coe_one, id_eq, Pi.one_apply, Units.val_one, smul_eq_mul, one_mul,
      Prod.mk.injEq, true_and]
    rfl
  mul_smul := fun x y ⟨i,a⟩ => by
    simp_rw [HSMul.hSMul,SMul.smul]
    rw [extract_perm_map_mul x y,extract_diag_map_mul x y]
    simp only [Equiv.Perm.coe_mul, Function.comp_apply, MonoidHom.coe_mk, map_inv,
      MulDistribMulAction.toMulAut_apply, OneHom.coe_mk, MulOpposite.unop_op, Pi.mul_apply,
      Units.val_mul, smul_eq_mul, map_mul, Prod.mk.injEq, true_and]
    simp only [Inv.inv, MulDistribMulAction.toMulEquiv_symm_apply, Prod.smul_def', Pi.smul_apply]
    have foo : ∀ (x y : SemilinearCodeAut F4 trivdist hdist HexaCode) v,
      (x * y).fst v = x.fst (y.fst v) := fun x y v => rfl
    simp_rw [foo]
    simp only [HSMul.hSMul, SMul.smul, DomMulAct.mk_inv, DomMulAct.symm_mk_inv,
      Equiv.symm_apply_apply, Units.val_inv_eq_inv_val, map_inv₀, RingEquiv.apply_symm_apply]
    simp only [Inv.inv, Equiv.symm_symm]
    rw [← mul_assoc,mul_comm (x.fst (y.fst (extract_diag y i)))]

-- abbrev golay_code_space := golay_code_index → ZMod 2 -- rather use ZMod 2? or bool?
-- rather use Matrix (Fin 6) F4 (ZMod 2)? for props: yes

abbrev golay_code_space' := ((Fin 6) × F4) → (ZMod 2) -- fun fact, Matrix a b c is defeq to a → b → c

-- #synth AddAction (Fin 6 → (F4)ᵈᵃᵃ) (Fin 6 → F4 → (ZMod 2))
-- #synth AddAction (F4)ᵈᵃᵃ (F4 → (ZMod 2))

example (x : F4) (y:F4 → ZMod 2): (DomAddAct.mk x) +ᵥ y = y ∘ (x + .) := rfl

instance : AddAction F_4_6 golay_code_space' where
  vadd := fun f g => ((fun i => DomAddAct.mk (f i)) +ᵥ g.curry).uncurry
  zero_vadd := fun f => by
    simp_rw [HVAdd.hVAdd, VAdd.vadd]
    ext : 1
    simp only [Pi.zero_apply, DomAddAct.mk_zero, zero_vadd]
    rfl
  add_vadd := fun f g => by
    intro b
    simp_rw [HVAdd.hVAdd,VAdd.vadd]
    ext ⟨i,j⟩ : 2
    simp only [Pi.add_apply, DomAddAct.mk_add, Matrix.of_apply]
    simp_rw [HVAdd.hVAdd,VAdd.vadd]
    simp only [DomAddAct.symm_mk_add, Equiv.symm_apply_apply, vadd_eq_add, Matrix.of_apply]
    simp only [Function.curry_apply, Function.uncurry_apply_pair]
    nth_rw 2 [add_comm]
    rw [add_assoc]

lemma vadd_add_distrib (f :F_4_6 ) (x y : golay_code_space') :
    f +ᵥ x + (f +ᵥ y) = f +ᵥ (x + y) := by
  rfl

lemma vadd_sub_distrib (f :F_4_6 ) (x y : golay_code_space') :
    f +ᵥ x - (f +ᵥ y) = f +ᵥ (x - y) := by
  rfl

def to_gc  (M:Matrix (Fin 4) (Fin 6) (ZMod 2)) : golay_code_space' :=
  Matrix.of.symm ((Matrix.reindex (Equiv.refl (Fin 6)) F4.naturalEquiv) (M.transpose)) |>.uncurry

def of_gc (m : golay_code_space') : Matrix (Fin 4) (Fin 6) (ZMod 2) :=
  (Matrix.reindex (Equiv.refl (Fin 6)) F4.naturalEquiv).symm (Matrix.of m.curry) |>.transpose

lemma of_gc_to_gc (M:Matrix (Fin 4) (Fin 6) (ZMod 2)) : of_gc (to_gc M) = M := by
  dsimp only [of_gc,to_gc]
  simp only [Matrix.reindex_symm, Equiv.refl_symm, Matrix.reindex_apply, Equiv.coe_refl,
    Function.curry_uncurry, Equiv.apply_symm_apply, Equiv.symm_symm, Matrix.submatrix_submatrix,
    CompTriple.comp_eq, Equiv.symm_comp_self, Matrix.submatrix_id_id, Matrix.transpose_transpose]

lemma to_gc_of_gc (m : golay_code_space') : to_gc (of_gc m) = m := by
  dsimp only [of_gc,to_gc]
  simp only [Matrix.reindex_symm, Equiv.refl_symm, Matrix.reindex_apply, Equiv.coe_refl,
    Equiv.symm_symm, Matrix.transpose_submatrix, Matrix.transpose_transpose,
    Matrix.submatrix_submatrix, CompTriple.comp_eq, Equiv.self_comp_symm, Matrix.submatrix_id_id,
    Equiv.symm_apply_apply, Function.uncurry_curry]

@[simp]
lemma to_gc_map_smul (M:Matrix (Fin 4) (Fin 6) (ZMod 2)) (a:ZMod 2) :
  a • to_gc M = to_gc (a • M) := rfl

@[simp]
lemma to_gc_map_add (M₁ M₂:Matrix (Fin 4) (Fin 6) (ZMod 2)) :
  to_gc M₁ + to_gc M₂ = to_gc (M₁ + M₂) := rfl


instance : One golay_code_space' where
  one := fun _ => 1

namespace golay_code_space'

def to_finset (m:golay_code_space') : Finset (golay_code_index) :=
  Finset.filter (fun x => m x = 1) Finset.univ
end golay_code_space'

lemma to_finset_inj : Function.Injective golay_code_space'.to_finset := by
  intro x y h
  rw [Finset.ext_iff] at h
  dsimp [golay_code_space'.to_finset] at h
  ext i
  specialize h i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
  revert h
  generalize x i = a
  generalize y i = b
  revert a b
  decide

instance : SetLike (golay_code_space') golay_code_index where
  coe := fun m => m.to_finset
  coe_injective' := fun f g h => by
    ext i
    simp only [golay_code_space'.to_finset, Set.mem_setOf_eq, Finset.coe_inj] at h
    simp_rw [Finset.ext_iff] at h
    specialize h i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    revert h
    generalize f i = a
    generalize g i = b
    revert a b
    decide

lemma to_finset_eq_coe (x:golay_code_space') : ∀ y, y ∈ x ↔ y ∈ x.to_finset := fun y => by rfl

def to_hexacode' : golay_code_space' →ₗ[ZMod 2] F_4_6 where
  toFun := fun M => fun i => ∑ x, M (i,x) • x
  map_add' := fun x y => by
    ext i : 1
    simp only
    simp only [Pi.add_apply]
    simp_rw [add_smul]
    exact Finset.sum_add_distrib
  map_smul' := fun r x => by
    ext i : 1
    simp only
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [MulAction.mul_smul]
    rw [Finset.smul_sum]

lemma to_hexacode'_apply (f : golay_code_space') (i:Fin 6) :
    to_hexacode' f i = (f (i,ω) + f (i,1)) • ω + (f (i,ω⁻¹) + f (i,1)) • ω⁻¹ := by
  rw [to_hexacode']
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [Finset.univ,Fintype.elems]
  simp only [Multiset.insert_eq_cons, Finset.mk_cons, Finset.cons_eq_insert, Finset.mem_insert,
    false_or, smul_zero, implies_true, Finset.sum_insert_of_eq_zero_if_not_mem]
  rw [Finset.sum_insert,Finset.sum_insert]
  simp only [Finset.sum_mk, Multiset.map_singleton, Multiset.sum_singleton]
  obtain z := f (i,1)
  fin_cases z
  . simp only [Fin.zero_eta, zero_smul, zero_add, add_zero]
  . simp only [Fin.mk_one, one_smul]
    simp_rw [Algebra.smul_def,map_add,map_one,right_distrib,one_mul]
    rw [add_assoc,add_comm ω,add_assoc,add_comm ω⁻¹,F4.omega_add_omega_inv]
    ring
  all_goals decide

def to_binary_vert' : golay_code_space' →ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun := fun M => fun i => ∑ x, M (i,x)
  map_add' := fun x y => by
    ext i : 1
    simp only [Pi.add_apply]
    exact Finset.sum_add_distrib
  map_smul' := fun r x => by
    ext i : 1
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

lemma to_binary_vert'_apply (f:golay_code_space') (i:Fin 6) :
    to_binary_vert' f i = f (i,0) + f (i,1) + f (i,ω) + f (i,ω⁻¹) := by
  simp_rw [to_binary_vert',Finset.univ,Fintype.elems]
  simp only [Multiset.insert_eq_cons, Finset.mk_cons, Finset.cons_eq_insert, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [Finset.sum_insert,Finset.sum_insert,Finset.sum_insert]
  simp only [Finset.sum_mk, Multiset.map_singleton, Multiset.sum_singleton]
  simp_rw [add_assoc]
  all_goals decide

def to_binary_hori' : golay_code_space' →ₗ[ZMod 2] ZMod 2 where
  toFun := fun M => ∑ i, M (i,0)
  map_add' := fun x y => by
    simp only [Pi.add_apply]
    exact Finset.sum_add_distrib
  map_smul' := fun r x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

lemma to_binary_hori'_apply (f:golay_code_space') :
    to_binary_hori' f = f (0,0) + f (1,0) + f (2,0) + f (3,0) + f (4,0) + f (5,0) := by
  simp_rw [to_binary_hori',Finset.univ,Fintype.elems,List.finRange]
  simp only [List.pmap, Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, Finset.sum_mk,
    Multiset.map_coe, List.map_cons, List.map_nil, Multiset.sum_coe, List.sum_cons, List.sum_nil,
    add_zero, LinearMap.coe_mk, AddHom.coe_mk]
  simp_rw [add_assoc]


abbrev Property1 : golay_code_space' → Prop := -- taking the sum of F4 by index maps to the hexaCode
  fun f => to_hexacode' f ∈ HexaCode

abbrev Property2 : golay_code_space' → Prop := fun f =>
  ∀ (i: Fin 6),to_binary_vert' f i = to_binary_hori' f

def GolayCode : Submodule (ZMod 2) golay_code_space' where
  carrier := {f | Property1 f ∧ Property2 f}
  add_mem' := by
    simp only [Set.mem_setOf_eq, and_imp]
    intro a b ha1 ha2 hb1 hb2
    simp_rw [Property1,Property2]
    constructor
    . rw [LinearMap.map_add]
      exact Submodule.add_mem HexaCode ha1 hb1
    . intro i
      simp only [map_add, Pi.add_apply]
      rw [ha2,hb2]
  zero_mem' := by
    simp only [Finset.filter_congr_decidable, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq]
    constructor
    . exact (Submodule.Quotient.mk_eq_zero HexaCode).mp rfl
    . exact congrFun rfl
  smul_mem' := fun ⟨i,hi⟩ x hx => by
    simp only [Set.mem_setOf_eq]
    rcases i
    . simp only [Nat.zero_eq, Fin.zero_eta, zero_smul]
      constructor
      . exact (Submodule.Quotient.mk_eq_zero HexaCode).mp rfl
      . exact congrFun rfl
    rename_i i
    rcases i
    . simp only [Nat.reduceAdd, zero_add, Fin.mk_one, Fin.isValue, one_smul]
      exact hx
    contradiction

lemma mem_golayCode_iff (m:golay_code_space') : m ∈ GolayCode ↔
    (to_hexacode' m ∈ HexaCode ∧ Property2 m) := by
  rw [GolayCode]
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]

instance : DecidablePred (. ∈ GolayCode) := fun x => by
  exact decidable_of_iff _ (mem_golayCode_iff x).symm

lemma GolayCode.one_mem : 1 ∈ GolayCode := by decide

-- #synth _LinearCode ℕ∞ (ZMod 2) trivdist hdist GolayCode

def golay_code_space'.compl : golay_code_space' → golay_code_space' := (1 + .)

set_option maxHeartbeats 300000

lemma GolayCode.mem_compl : ∀ f ∈ GolayCode, f.compl ∈ GolayCode :=
  fun _ hf => GolayCode.add_mem (GolayCode.one_mem) hf

lemma aut_smul_map_dist (φ: SemilinearCodeAut F4 trivdist hdist HexaCode) :
    ∀ x y : golay_code_space', hdist x y = hdist (DomMulAct.mk φ • x) (DomMulAct.mk φ • y):= fun f g => by
  simp_rw [addDist_eq]
  simp_rw [addGNorm,hdist]
  simp only [hammingENatdist_eq_cast_hammingDist, hammingDist_zero_right, Nat.cast_inj]
  simp_rw [hammingNorm]
  simp only [ne_eq, Finset.filter_congr_decidable]
  suffices h: (
        Finset.filter (fun x_1 ↦ ¬(f - g) x_1 = 0) Finset.univ) ≃
        (Finset.filter (fun x_1 ↦ ¬(DomMulAct.mk φ • (f - g)) x_1 = 0) Finset.univ) by
    rw [smul_sub] at h
    exact Finset.card_eq_of_equiv h
  simp_rw [HSMul.hSMul,SMul.smul]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
  exact {
    toFun := fun ⟨⟨i,x⟩,hz⟩ => ⟨⟨(extract_perm φ).symm i,(extract_diag φ ((extract_perm φ).symm i))⁻¹ • φ.fst⁻¹ • x⟩,by
      simp only [HSMul.hSMul, SMul.smul, Equiv.apply_symm_apply, Units.val_inv_eq_inv_val, ne_eq,
        Units.ne_zero, not_false_eq_true, mul_inv_cancel_left₀]
      simp only [Inv.inv, RingEquiv.apply_symm_apply]
      exact hz⟩
    invFun := fun z => ⟨⟨extract_perm φ z.1.1,φ.fst • extract_diag φ z.1.1 • z.1.2⟩,by
      exact z.2⟩
    left_inv := fun z => by
      simp only [Pi.sub_apply, Equiv.apply_symm_apply, smul_inv_smul, Prod.mk.eta,
        Subtype.coe_eta]
    right_inv := fun z => by
      simp only [Pi.sub_apply, Equiv.symm_apply_apply, inv_smul_smul, Prod.mk.eta,
        Subtype.coe_eta]
  }


instance : SMulCommClass (RingAut F4) (ZMod 2) F4 where
  smul_comm := fun m b x => by
    fin_cases b <;> simp

lemma aut_smul_map_property1 (φ: SemilinearCodeAut F4 trivdist hdist HexaCode) :
    ∀ (x : golay_code_space'), Property1 x → Property1 (DomMulAct.mk φ • x) := fun x hx => by
  simp_rw [Property1] at hx ⊢
  suffices hsuf : φ (to_hexacode' (DomMulAct.mk φ • x)) = (to_hexacode' x) by
    rw [← hsuf] at hx
    apply φ.snd.invMap_code
    exact hx
  simp_rw [to_hexacode']
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  ext i : 1
  rw [extract_gives_stuff_strong]
  simp only [Pi.smul_apply, RingAut.smul_def]
  calc
    φ.fst ((extract_perm φ • extract_diag φ • fun i ↦ ∑ x_1 : F4, (DomMulAct.mk φ • x) (i,x_1) • x_1) i)
      = φ.fst ((extract_diag φ •
        fun i ↦ ∑ x_1 : F4, (DomMulAct.mk φ • x) (i,x_1) • x_1) ((extract_perm φ)⁻¹ i)) := by
          nth_rw 1 [HSMul.hSMul,instHSMul]
          simp_rw [SMul.smul]
          nth_rw 1 [HSMul.hSMul,instHSMul]
          simp_rw [SMul.smul]
          simp only [DomMulAct.mk_inv, DomMulAct.symm_mk_inv, Equiv.symm_apply_apply,
            Equiv.Perm.smul_def, EmbeddingLike.apply_eq_iff_eq]
    _ = φ.fst (extract_diag φ ((extract_perm φ)⁻¹ i) •
        ∑ x_1 : F4, (DomMulAct.mk φ • x) ((extract_perm φ)⁻¹ i, x_1) • x_1) := by
      rw [Pi.smul_apply']
    _ = φ.fst (∑ x_1 : F4, extract_diag φ ((extract_perm φ)⁻¹ i) •
      (DomMulAct.mk φ • x) ((extract_perm φ)⁻¹ i, x_1) • x_1) := by
        rw [Finset.smul_sum]
    _ = ∑ x_1 : F4, φ.fst (extract_diag φ ((extract_perm φ)⁻¹ i) •
      (DomMulAct.mk φ • x) ((extract_perm φ)⁻¹ i,x_1) • x_1) := by
        rw [RingEquiv.map_sum]
    _ = ∑ x_1 : F4, φ.fst • (extract_diag φ ((extract_perm φ)⁻¹ i) •
      (DomMulAct.mk φ • x) ((extract_perm φ)⁻¹ i,x_1) • x_1) := rfl
    _ = ∑ x_1 : F4, φ.fst • (DomMulAct.mk φ • x) ((extract_perm φ)⁻¹ i,x_1) •
      (extract_diag φ ((extract_perm φ)⁻¹ i) •x_1) := by
        conv =>
          enter [1, 2, x_1, 2]
          rw [smul_comm]
    _ = ∑ x_1 : F4, (DomMulAct.mk φ • x) ((extract_perm φ)⁻¹ i,x_1) •
      φ.fst • (extract_diag φ ((extract_perm φ)⁻¹ i) •x_1) := by
        conv =>
          enter [1, 2, x_1]
          rw [smul_comm]
    _ = ∑ x_1 : F4, (DomMulAct.mk φ • x) ((extract_perm φ)⁻¹ i,
        (extract_diag φ ((extract_perm φ)⁻¹ i))⁻¹ • x_1) • φ.fst • x_1 := by
      rw [← (?equiv:F4 ≃ F4).sum_comp]
      case equiv =>
        exact MulAction.toPerm (extract_diag φ ((extract_perm φ)⁻¹ i))⁻¹
      simp_rw [MulAction.toPerm_apply,smul_inv_smul]
    _ = ∑ x_1 : F4, (DomMulAct.mk φ • x) ((extract_perm φ)⁻¹ i,
        (extract_diag φ ((extract_perm φ)⁻¹ i))⁻¹ • φ.fst⁻¹ • x_1) • x_1 := by
      rw [← (?equiv : F4 ≃ F4).sum_comp]
      case equiv => exact MulAction.toPerm φ.fst⁻¹
      simp_rw [MulAction.toPerm_apply,smul_inv_smul]
    -- _ = ∑ x_1 : F4,
    _ = ∑ x_1 : F4, x (i,φ.fst (φ.fst⁻¹ x_1)) • x_1 := by
      nth_rw 2 [HSMul.hSMul,instHSMul]
      simp_rw [SMul.smul]
      simp only [Equiv.symm_apply_apply, RingAut.smul_def]
      nth_rw 2 [HSMul.hSMul,instHSMul]
      simp only [SMul.smul, RingAut.smul_def, Equiv.Perm.apply_inv_self, smul_inv_smul]

    _ = ∑ x_1 : F4, x (i,φ.fst (φ.fst.symm x_1)) • x_1 := rfl
    _ = ∑ x_1 : F4, x (i, x_1) • x_1 := by simp_rw [RingEquiv.apply_symm_apply]


lemma aut_smul_map_property2 (φ: SemilinearCodeAut F4 trivdist hdist HexaCode) :
    ∀ (x : golay_code_space'), Property2 x → Property2 (DomMulAct.mk φ • x) := fun x hx => by
  simp_rw [Property2, to_binary_vert',to_binary_hori'] at hx ⊢
  simp_all only [LinearMap.coe_mk, AddHom.coe_mk]
  intro i
  calc
    ∑ x_1 : F4, (DomMulAct.mk φ • x) (i,x_1)
      = ∑ x_1 : F4, x (φ • (i,x_1)) := rfl
    _ = ∑ x_1 : F4, x (extract_perm φ i, φ.fst • extract_diag φ i • x_1) := rfl
    _ = ∑ x_1 : F4, x (extract_perm φ i, φ.fst • x_1) := by
      rw [← (?equiv : F4 ≃ F4).sum_comp]
      case equiv => exact MulAction.toPerm (extract_diag φ i)⁻¹
      simp_rw [MulAction.toPerm_apply, smul_inv_smul]
    _ = ∑ x_1 : F4, x (extract_perm φ i, x_1) := by
      rw [← (?equiv' : F4 ≃ F4).sum_comp]
      case equiv' => exact MulAction.toPerm φ.fst⁻¹
      simp_rw [MulAction.toPerm_apply, smul_inv_smul]
    _ = ∑ i : Fin 6, x (i, 0) := by
      rw [hx (extract_perm φ i)]
    _ = ∑ i : Fin 6, x (extract_perm φ i, 0) := by
      rw [← (?equiv'' : Fin 6 ≃ Fin 6).sum_comp]
      case equiv'' => exact extract_perm φ
      rfl
    _ = ∑ i : Fin 6, x (extract_perm φ i, φ.fst • extract_diag φ i • 0) := by
      simp_rw [smul_zero]
    _ = ∑ i : Fin 6, x (φ • (i, 0)) := by rfl
    _ = ∑ i : Fin 6, (DomMulAct.mk φ • x) (i, 0) := rfl

-- with a little luck this is a mulhom
noncomputable def GolayCode.lift_hexacode_aut' (φ: SemilinearCodeAut F4 trivdist hdist HexaCode):
    SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode := ⟨RingEquiv.refl (ZMod 2),
  letI inst := RingHomInvPair.of_ringEquiv (RingEquiv.refl (ZMod 2))
  letI := inst.symm
  {
  (DistribMulAction.toLinearEquiv (ZMod 2) golay_code_space' (DomMulAct.mk φ⁻¹):
  golay_code_space' ≃ₗ[ZMod 2] golay_code_space') with
  map_dist := fun f g => aut_smul_map_dist φ⁻¹ f g
  map_code := fun x ⟨hx₁,hx₂⟩ => by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      DistribMulAction.toLinearEquiv_apply, SetLike.mem_coe]
    constructor
    . exact aut_smul_map_property1 φ⁻¹ x hx₁
    . exact aut_smul_map_property2 φ⁻¹ x hx₂
  invMap_code := fun y ⟨hy₁,hy₂⟩ => by
    simp_all only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
      DistribMulAction.toLinearEquiv_apply, SetLike.mem_coe]
    rw [← smul_inv_smul (DomMulAct.mk φ) y]
    rw [← DomMulAct.mk_inv]
    constructor
    . exact aut_smul_map_property1 φ (DomMulAct.mk φ⁻¹ • y) hy₁
    . exact aut_smul_map_property2 φ (DomMulAct.mk φ⁻¹ • y) hy₂}⟩

#check LinearCodeAut (ZMod 2) trivdist hdist GolayCode

-- #synth Add (LinearCodeAut (ZMod 2) trivdist hdist GolayCode)

noncomputable def GolayCode.lift_hexacode_aut :
    SemilinearCodeAut F4 trivdist hdist HexaCode →* SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode where
      toFun := GolayCode.lift_hexacode_aut'
      map_one' := by
        rw [GolayCode.lift_hexacode_aut']
        simp only [RingEquiv.coe_ringHom_refl, RingEquiv.symm_refl, inv_one, DomMulAct.mk_one]
        ext f : 1
        . rfl
        simp only [SemilinearCodeEquiv.coe_mk, CodeEquiv.coe_mk, GIsometryEquiv.coe_mk, Equiv.coe_fn_mk,
          DistribMulAction.toLinearEquiv_apply, one_smul]
        simp only [RingEquiv.coe_ringHom_refl, RingEquiv.symm_refl, SemilinearCodeAut.coe_one,
          id_eq]
        suffices hsuf : DistribMulAction.toLinearEquiv (ZMod 2) golay_code_space'
              (1 : (SemilinearCodeAut F4 trivdist hdist HexaCode)ᵈᵐᵃ) f = f by
          exact hsuf
        simp only [DistribMulAction.toLinearEquiv_apply, one_smul]
      map_mul' := fun x y => by
        ext f : 1
        . rfl
        simp only [DomMulAct.mk_inv, DomMulAct.mk_one, RingEquiv.coe_ringHom_refl,
          RingEquiv.symm_refl, id_eq, hammingENatdist_eq_cast_hammingDist, AddHom.toFun_eq_coe,
          LinearMap.coe_toAddHom, LinearEquiv.coe_coe, RingEquiv.refl_apply,
          SemilinearCodeEquiv.coe_mk, DistribMulAction.toLinearEquiv_apply,
          SemilinearCodeAut.coe_one, eq_mpr_eq_cast, cast_eq, OneHom.toFun_eq_coe, OneHom.coe_mk,
          SemilinearCodeAut.coe_mul, Function.comp_apply]
        simp_rw [lift_hexacode_aut']
        simp only [_root_.mul_inv_rev, DomMulAct.mk_mul, DomMulAct.mk_inv, AddHom.toFun_eq_coe,
          LinearMap.coe_toAddHom, LinearEquiv.coe_coe, LinearEquiv.invFun_eq_symm,
          SemilinearCodeEquiv.coe_mk, CodeEquiv.coe_mk, GIsometryEquiv.coe_mk, Equiv.coe_fn_mk,
          DistribMulAction.toLinearEquiv_apply]
        simp only [RingEquiv.coe_ringHom_refl, RingEquiv.symm_refl]
        suffices hsuf :
          DistribMulAction.toLinearEquiv (ZMod 2) golay_code_space'
            ((DomMulAct.mk x)⁻¹ * (DomMulAct.mk y⁻¹)) f
              = DistribMulAction.toLinearEquiv (ZMod 2) golay_code_space' (DomMulAct.mk x)⁻¹
                (DistribMulAction.toLinearEquiv (ZMod 2) golay_code_space' (DomMulAct.mk y)⁻¹ f) by
            exact hsuf
        simp only [DomMulAct.mk_inv, DistribMulAction.toLinearEquiv_apply]
        simp_rw [mul_smul]

example (φ : SemilinearCodeAut F4 trivdist hdist HexaCode)
    (f : golay_code_space') (x: golay_code_index) :
    f x = (GolayCode.lift_hexacode_aut φ f) (φ • x):= by
  simp_rw [GolayCode.lift_hexacode_aut]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  simp_rw [GolayCode.lift_hexacode_aut']
  simp only [DomMulAct.mk_inv, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearEquiv.invFun_eq_symm, SemilinearCodeEquiv.coe_mk, CodeEquiv.coe_mk, GIsometryEquiv.coe_mk,
    Equiv.coe_fn_mk, DistribMulAction.toLinearEquiv_apply]
  nth_rw 1 [HSMul.hSMul,instHSMul]
  simp_rw [SMul.smul]
  suffices hsuf : f x =
    DistribMulAction.toLinearEquiv (ZMod 2) golay_code_space' (DomMulAct.mk φ)⁻¹ f
      ((extract_perm φ) x.1,φ.fst • extract_diag φ x.1 • x.2) by exact hsuf
  simp only [RingAut.smul_def, DistribMulAction.toLinearEquiv_apply]
  symm
  calc
    ((DomMulAct.mk φ)⁻¹ • f) ((extract_perm φ) x.1, φ.fst • extract_diag φ x.1 • x.2)
      = f (φ⁻¹ • ((extract_perm φ) x.1, φ.fst • extract_diag φ x.1 • x.2)) := rfl
    _ = f (φ⁻¹ • φ • x) := rfl
    _ = f x := by rw [inv_smul_smul]

-- #synth SMul (SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode) (Set golay_code_index)
example : Unit := ()

noncomputable instance : MulAction (SemilinearCodeAut (ZMod 2) trivdist hdist GolayCode) golay_code_index where
  smul := fun φ => extract_perm φ
  one_smul := fun b => by
    suffices hsuf : extract_perm 1 b = b by
      exact hsuf
    rw [extract_perm_map_one]
    rfl
  mul_smul := fun x y b => by
    suffices hsuf : extract_perm (x * y) b = extract_perm x (extract_perm y b) by
      exact hsuf
    rw [extract_perm_map_mul x y]
    rfl


-- #synth AddAction F_4_6 golay_code_space'
