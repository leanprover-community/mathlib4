import Mathlib.InformationTheory.Code.Linear.HexaCode.Basic
import Mathlib.Algebra.Module.Equiv
import Mathlib.Topology.GMetric.GNorm


open BigOperators Matrix
abbrev golay_code_index := Fin 6 × F4

-- this seems akin to a Semidirect Product of some sort... but not quite

-- you can interpret this as the Aut map acting on the element `r • b i`
noncomputable instance : MulAction (LinearCodeAut F4 trivdist hdist hexaCode) golay_code_index where
  smul := fun f ⟨i,x⟩=> ⟨extract_perm f i, extract_diag f i • x⟩
  one_smul := fun ⟨i,x⟩ => by
    simp_rw [HSMul.hSMul,SMul.smul]
    ext : 1
    . simp only [_root_.map_one, SemidirectProduct.one_right]
      rw [extract_perm]
      simp only [Equiv.coe_fn_mk]
      apply (extract_gives_unique_perm' 1 i i 1 _).symm
      simp only [LinearCodeAut.one_apply, one_smul]
    . simp only
      suffices hsuf : (extract_diag 1 i) = 1 by
        rw [hsuf]
        simp only [Units.val_one, smul_eq_mul, one_mul]
      apply (extract_gives_unique_diag 1 i i 1 _).symm
      simp only [LinearCodeAut.one_apply, one_smul]
  mul_smul := fun x y ⟨i,a⟩ => by
    simp_rw [HSMul.hSMul,SMul.smul]
    ext : 1
    . simp only
      rw [extract_perm]
      simp only [Equiv.coe_fn_mk]
      apply (extract_gives_unique_perm' (x * y) i _ _ _).symm
      . exact extract_diag y i * (extract_diag x (extract_perm y i))
      simp_rw [HMul.hMul,Mul.mul]
      simp only [LinearCodeEquiv.trans_apply]
      rw [extract_gives_stuff']
      simp_rw [HSMul.hSMul,SMul.smul]
      simp only [SMulHomClass.map_smul]
      rw [extract_gives_stuff']
      ext j : 1
      simp_rw [extract_perm_is_perm',HSMul.hSMul,SMul.smul]
      simp only [smul_eq_mul]
      simp_rw [HSMul.hSMul,SMul.smul]
      simp_rw [HSMul.hSMul,SMul.smul]
      ring_nf
    . simp only [smul_eq_mul]
      suffices hsuf : extract_diag (x * y) i = extract_diag x ((extract_perm y) i) * extract_diag y i by
        rw [hsuf]
        simp only [Units.val_mul]
        ring_nf
      obtain hz :toSemidirectProd (x * y) = toSemidirectProd x * toSemidirectProd y := toSemidirectProd.map_mul x y
      simp_rw [toSemidirectProd] at hz
      simp only [MonoidHom.coe_mk, OneHom.coe_mk] at hz
      simp_rw [toSemidirectProd'] at hz
      rw [← MulOpposite.op_mul, MulOpposite.op_inj] at hz
      nth_rw 3 [HMul.hMul,instHMul] at hz
      simp only at hz
      simp_rw [Mul.mul] at hz
      rw [SemidirectProduct.ext_iff] at hz
      simp only at hz
      rw [hz.left]
      simp_rw [apply_perm,MulDistribMulAction.toMulAut]
      simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulDistribMulAction.toMulEquiv_apply,
        Pi.mul_apply]
      simp_rw [HSMul.hSMul,SMul.smul]
      simp only [Equiv.symm_apply_apply, Equiv.Perm.smul_def]
      rw [mul_comm]


-- abbrev golay_code_space := golay_code_index → ZMod 2 -- rather use ZMod 2? or bool?
-- rather use Matrix (Fin 6) F4 (ZMod 2)?
@[reducible]
abbrev golay_code_space' := Matrix (Fin 6) F4 (ZMod 2) -- fun fact, Matrix a b c is defeq to a → b → c

#synth AddAction (Fin 6 → F4ᵈᵃᵃ) ((Fin 6) → F4 → (ZMod 2))

-- remind matrix of the instance above, and use the fact that F4 has commutative addition to simp.
instance : AddAction F_4_6 golay_code_space' where
  vadd := fun f g => by
    obtain g' := g
    obtain y := Matrix.of ((VAdd.vadd (fun i => DomAddAct.mk (f i))) (g))
    exact y
  zero_vadd := fun f => by
    simp_rw [HVAdd.hVAdd, VAdd.vadd]
    ext : 1
    simp only [Pi.zero_apply, DomAddAct.mk_zero, zero_vadd]
    rfl
  add_vadd := fun f g => by
    intro b
    simp_rw [HVAdd.hVAdd,VAdd.vadd]
    ext i j : 2
    simp only [Pi.add_apply, DomAddAct.mk_add, of_apply]
    simp_rw [HVAdd.hVAdd,VAdd.vadd]
    simp only [DomAddAct.symm_mk_add, Equiv.symm_apply_apply, vadd_eq_add, of_apply]
    nth_rw 2 [add_comm]
    rw [add_assoc]

def to_gc  (M:Matrix (Fin 4) (Fin 6) (ZMod 2)) : Matrix (Fin 6) F4 (ZMod 2) :=
  (Matrix.reindex (Equiv.refl (Fin 6)) F4.naturalEquiv) M.transpose

instance : One golay_code_space' where
  one := to_gc !![1,1,1,1,1,1;
                  1,1,1,1,1,1;
                  1,1,1,1,1,1;
                  1,1,1,1,1,1]


instance : SetLike (golay_code_space') golay_code_index where
  coe := fun m => {x | Function.uncurry m x = (1:ZMod 2)}
  coe_injective' := fun f g h => by
    ext i x'
    simp only at h
    rw [Set.ext_iff] at h
    simp only [Set.mem_setOf_eq, Prod.forall, Function.uncurry_apply_pair] at h
    let y := f i x'
    let z := g i x'
    if h2: y = 1 then
      dsimp at h2
      exact h2 ▸ ((h i x').mp h2).symm
    else
      suffices y = z by
        dsimp at this
        exact this
      have h3 : z ≠ 1 := (h i x').mpr.mt h2
      have h4 : y = 0 := by
        obtain ⟨y,hy⟩ := y
        rcases y
        . simp only [Nat.zero_eq, Fin.zero_eta]
        rename_i y
        rcases y
        . contradiction
        contradiction
      rw [h4]
      obtain ⟨z,hz⟩ := z
      rcases z
      . simp only [Nat.zero_eq, Fin.zero_eta]
      rename_i z
      rcases z
      . contradiction
      contradiction

-- instance : SetLike (golay_code_space) golay_code_index where
--   coe := fun f => {z | f z = 1}
--   coe_injective' := fun f g h => by
--     ext x
--     simp only at h
--     rw [Set.ext_iff] at h
--     simp only [Set.mem_setOf_eq, Prod.forall] at h
--     let y := f x
--     let z := g x
--     if h2: y = 1 then
--       dsimp at h2
--       exact h2 ▸ ((h x.1 x.2).mp h2).symm
--     else
--       suffices y = z by
--         dsimp at this
--         exact this
--       have h3 : z ≠ 1 := (h x.1 x.2).mpr.mt h2
--       have h4 : y = 0 := by
--         obtain ⟨y,hy⟩ := y
--         rcases y
--         . simp only [Nat.zero_eq, Fin.zero_eta]
--         rename_i y
--         rcases y
--         . contradiction
--         contradiction
--       rw [h4]
--       obtain ⟨z,hz⟩ := z
--       rcases z
--       . simp only [Nat.zero_eq, Fin.zero_eta]
--       rename_i z
--       rcases z
--       . contradiction
--       contradiction

def to_hexacode' : golay_code_space' →ₗ[ZMod 2] F_4_6 where
  toFun := fun M => (Algebra.linearMap (ZMod 2) F4).mapMatrix M *ᵥ id
  map_add' := fun x y => by
    simp only
    simp only [map_add, LinearMap.mapMatrix_apply]
    rw [Matrix.add_mulVec]
  map_smul' := fun r x => by
    simp only [SMulHomClass.map_smul, LinearMap.mapMatrix_apply, RingHom.id_apply]
    rw [Matrix.smul_mulVec_assoc]

  -- use f as weights on the identity map as vector
-- def to_hexacode : golay_code_space →ₗ[ZMod 2]  F_4_6 where
--   toFun := fun f i => Fintype.total (ZMod 2) F4 id (f ∘ (i,.))
--   map_add' := fun x y => by
--     simp only
--     ext i : 1
--     simp only [Pi.add_apply,Fintype.total_apply]
--     simp only [Function.comp_apply, Pi.add_apply, id_eq]
--     simp_rw [Finset.univ]
--     simp_rw [add_smul]
--     exact Finset.sum_add_distrib
--   map_smul' := fun ⟨r,hr⟩ x => by
--     simp only [RingHom.id_apply]
--     ext i : 1
--     simp only [Pi.smul_apply,Fintype.total_apply]
--     simp only [Function.comp_apply, Pi.smul_apply, id_eq]
--     rw [Finset.smul_sum]
--     simp only [smul_eq_mul]
--     rcases r
--     . simp only [Nat.zero_eq, Fin.zero_eta, zero_mul, zero_smul, Finset.sum_const_zero]
--     rename_i r
--     rcases r
--     . simp only [Nat.zero_eq, Nat.reduceSucc, Fin.mk_one, one_mul, one_smul]
--     contradiction


def to_binary_vert' : golay_code_space' →ₗ[ZMod 2] (Fin 6 → ZMod 2) where
  toFun := fun M => M *ᵥ 1
  map_add' := fun x y => by
    simp only
    rw [Matrix.add_mulVec]
  map_smul' := fun r x => by
    simp only [RingHom.id_apply]
    rw [Matrix.smul_mulVec_assoc]

-- def to_binary_vert : golay_code_space →ₗ[ZMod 2] (Fin 6 → ZMod 2) where
--   toFun := fun f i => ∑ x, f (i,x)
--   map_add' := fun x y => by
--     simp only [Pi.add_apply]
--     ext i : 1
--     exact Finset.sum_add_distrib
--   map_smul' := fun ⟨r,hr⟩ x => by
--     simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
--     ext i : 1
--     simp only [Pi.smul_apply, smul_eq_mul]
--     rcases r
--     . simp only [Nat.zero_eq, Fin.zero_eta, zero_mul, Finset.sum_const_zero]
--     rename_i r
--     rcases r
--     . simp only [Nat.zero_eq, Nat.reduceSucc, Fin.mk_one, one_mul]
--     contradiction

def to_binary_hori' : golay_code_space' →ₗ[ZMod 2] ZMod 2 where
  toFun := fun M => M.transpose 0 ⬝ᵥ 1
  map_add' := fun x y => by
    simp only [transpose_add, Nat.rec_add_one]
    rw [← Matrix.add_dotProduct]
    rfl
  map_smul' := fun r x => by
    simp only [transpose_smul, RingHom.id_apply]
    rw [← Matrix.smul_dotProduct]
    rfl


-- def to_binary_hori : golay_code_space →ₗ[ZMod 2] ZMod 2 where
--   toFun := fun f => ∑ i, f (i,0)
--   map_add' := fun x y => by
--     exact Finset.sum_add_distrib
--   map_smul' := fun ⟨r,hr⟩ x => by
--     simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
--     rcases r
--     . simp only [Nat.zero_eq, Fin.zero_eta, zero_mul, Finset.sum_const_zero]
--     rename_i r
--     rcases r
--     . simp only [Nat.zero_eq, Nat.reduceSucc, Fin.mk_one, one_mul]
--     contradiction

abbrev Property1 : golay_code_space' → Prop := -- taking the sum of F4 by index maps to the hexaCode
  fun f => to_hexacode' f ∈ hexaCode

abbrev Property2 : golay_code_space' → Prop := fun f => -- all projections along F4 have the same parity
  ∀ i, to_binary_vert' f i = to_binary_vert' f 0

abbrev Property3 : golay_code_space' → Prop := fun f =>
  to_binary_vert' f 0 = to_binary_hori' f

def GolayCode : Submodule (ZMod 2) golay_code_space' where
  carrier := {f | Property1 f ∧ Property2 f ∧ Property3 f}
  add_mem' := by
    simp only [Set.mem_setOf_eq, and_imp]
    intro a b ha1 ha2 ha3 hb1 hb2 hb3
    simp_rw [Property1,Property2,Property3]
    constructor
    . rw [LinearMap.map_add]
      exact Submodule.add_mem hexaCode ha1 hb1
    constructor
    . intro i
      simp only [map_add, Pi.add_apply]
      rw [ha2,hb2]
    . simp only [map_add, Pi.add_apply]
      rw [ha3,hb3]
  zero_mem' := by
    simp only [Finset.filter_congr_decidable, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq]
    constructor
    . exact (Submodule.Quotient.mk_eq_zero hexaCode).mp rfl
    constructor
    . exact congrFun rfl
    . exact rfl
  smul_mem' := fun ⟨i,hi⟩ x hx => by
    simp only [Set.mem_setOf_eq]
    rcases i
    . simp only [Nat.zero_eq, Fin.zero_eta, zero_smul]
      constructor
      . exact (Submodule.Quotient.mk_eq_zero hexaCode).mp rfl
      constructor
      . exact congrFun rfl
      . exact rfl
    rename_i i
    rcases i
    . simp only [Nat.zero_eq, Nat.reduceSucc, Fin.mk_one, one_smul]
      exact hx
    contradiction

lemma GolayCode.one_mem : 1 ∈ GolayCode := by
  rw [GolayCode]
  simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  constructor
  . rw [Property1]
    suffices h: to_hexacode' 1 = 0 by
      rw [h]
      simp only [Submodule.zero_mem]
    decide
  . decide

#synth _LinearCode ℕ∞ (ZMod 2) trivdist hmdist GolayCode

def golay_code_space'.compl : golay_code_space' → golay_code_space' := (1 - .)

set_option maxHeartbeats 300000

lemma GolayCode.mem_compl : ∀ f ∈ GolayCode, f.compl ∈ GolayCode :=
  fun _ hf => GolayCode.sub_mem (GolayCode.one_mem) hf

#synth DistribMulAction (LinearCodeAut F4 trivdist hdist hexaCode)ᵈᵐᵃ (((Fin 6) × F4) → ZMod 2)

def GolayCode.lift_hexacode_aut (φ: LinearCodeAut F4 trivdist hdist hexaCode):
    LinearCodeAut (ZMod 2) trivdist hmdist GolayCode := {
      (DistribMulAction.toLinearEquiv (ZMod 2) golay_code_space' (DomMulAct.mk φ):
      golay_code_space ≃ₗ[ZMod 2] golay_code_space) with
      map_dist := fun f g => by
        simp_rw [addDist_eq]
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
          DistribMulAction.toLinearEquiv_apply]
        rw [← smul_sub]
        simp_rw [addGNorm,hdist]
        simp only [hammingENatdist_eq_cast_hammingDist, hammingDist_zero_right, Nat.cast_inj]
        simp_rw [hammingNorm]
        simp only [ne_eq, Finset.filter_congr_decidable]
        suffices h: (Finset.filter (fun x_1 ↦ ¬(f - g) x_1 = 0) Finset.univ) ≃ (Finset.filter (fun x_1 ↦ ¬(DomMulAct.mk φ • (f - g)) x_1 = 0) Finset.univ) by
          exact Finset.card_eq_of_equiv h
        simp_rw [HSMul.hSMul,SMul.smul]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply]
        simp_rw [HSMul.hSMul,SMul.smul]
        exact {
          toFun := fun z => ⟨⟨(extract_perm φ).symm z.1.1,(extract_diag φ ((extract_perm φ).symm z.1.1))⁻¹ • z.1.2⟩,by
            simp only [Equiv.apply_symm_apply,smul_inv_smul]
            exact z.2⟩
          invFun := fun z => ⟨⟨extract_perm φ z.1.1,extract_diag φ z.1.1 • z.1.2⟩,by
            exact z.2⟩
          left_inv := fun z => by
            simp only [Pi.sub_apply, Equiv.apply_symm_apply, smul_inv_smul, Prod.mk.eta,
              Subtype.coe_eta]
          right_inv := fun z => by
            simp only [Pi.sub_apply, Equiv.symm_apply_apply, inv_smul_smul, Prod.mk.eta,
              Subtype.coe_eta]
        }
      map_code := fun x hx => by
        simp only [SetLike.mem_coe, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          LinearEquiv.coe_coe, DistribMulAction.toLinearEquiv_apply] at hx ⊢
        simp_rw [GolayCode, Property1,Property2,Property3] at hx ⊢
        simp only [Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
          Set.mem_setOf_eq] at hx ⊢
        constructor
        . suffices h: to_hexacode (DomMulAct.mk φ • x) = φ (to_hexacode x) by
            rw [h]
            apply φ.map_code
            exact hx.left
          ext i : 1
          rw [← coe_toSemidirectProd',toSemidirectProd']
          simp_rw [HSMul.hSMul,SMul.smul]
          simp only [Equiv.symm_apply_apply, SemidirectProduct.mk_eq_inl_mul_inr,
            MulOpposite.op_mul, MulOpposite.unop_mul, MulOpposite.unop_op,
            SemidirectProduct.mul_right, SemidirectProduct.right_inl, SemidirectProduct.right_inr,
            one_mul, SemidirectProduct.mul_left, SemidirectProduct.left_inl, map_one,
            SemidirectProduct.left_inr, mul_one]
          simp_rw [to_hexacode]
          simp only [LinearMap.coe_mk, AddHom.coe_mk]
          simp_rw [HSMul.hSMul,SMul.smul]
          simp only [Function.comp_apply]
          rw [Fintype.total_apply]
          simp only [Function.comp_apply, id_eq]

          rw [Finset.smul_sum]
          nth_rw 3 [HSMul.hSMul,instHSMul]
          simp only
          simp_rw [SMul.smul]
          sorry
        sorry
      invMap_code := _
    }



-- #synth Module (ZMod 2) golay_code_space
-- #synth Group (LinearCodeAut F4 trivdist hdist hexaCode)ᵈᵐᵃ
#synth AddAction (F_4_6ᵈᵃᵃ) (golay_code_space') -- equivalent
#synth DistribMulAction ((LinearCodeAut F4 trivdist hdist hexaCode)ᵈᵐᵃ) golay_code_space'
-- #synth _LinearCode ℕ∞ (ZMod 2) trivdist hdist GolayCode
