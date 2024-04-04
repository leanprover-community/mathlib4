import Mathlib.InformationTheory.Code.Linear.HexaCode.Basic
import Mathlib.Algebra.Module.Equiv
import Mathlib.Topology.GMetric.GNorm


open BigOperators
abbrev golay_code_index := Fin 6 × F4

-- this seems akin to a Semidirect Product of some sort... but not quite

-- you can interpret this as the Aut map acting on the element `r • b i`
noncomputable instance : MulAction (LinearCodeAut F4 trivdist hdist hexaCode) golay_code_index where
  smul := fun f ⟨i,x⟩=> ⟨(extract_perm f) i, (extract_diag f i) • x⟩
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
-- rather use Matrix (Fin 6) F4 (ZMod 2)? for props: yes

abbrev golay_code_space' := ((Fin 6) × F4) → (ZMod 2) -- fun fact, Matrix a b c is defeq to a → b → c

#synth AddAction (Fin 6 → (F4)ᵈᵃᵃ) (Fin 6 → F4 → (ZMod 2))
#synth AddAction (F4)ᵈᵃᵃ (F4 → (ZMod 2))

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
  (Matrix.reindex (Equiv.refl (Fin 6)) F4.naturalEquiv) M.transpose |>.uncurry


instance : One golay_code_space' where
  one := to_gc !![1,1,1,1,1,1;
                  1,1,1,1,1,1;
                  1,1,1,1,1,1;
                  1,1,1,1,1,1]

instance : SetLike (golay_code_space') golay_code_index where
  coe := fun m => {x | m x = (1:ZMod 2)}
  coe_injective' := fun f g h => by
    ext i
    rw [Set.ext_iff] at h
    simp only [Set.mem_setOf_eq, Prod.forall] at h
    let y := f i
    let z := g i
    obtain ⟨j,x'⟩ := i
    if h2: y = 1 then
      dsimp at h2
      exact h2 ▸ ((h j x').mp h2).symm
    else
      suffices y = z by
        dsimp at this
        exact this
      have h3 : z ≠ 1 := (h j x').mpr.mt h2
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


def to_binary_hori' : golay_code_space' →ₗ[ZMod 2] ZMod 2 where
  toFun := fun M => ∑ i, M (i,0)
  map_add' := fun x y => by
    simp only [Pi.add_apply]
    exact Finset.sum_add_distrib
  map_smul' := fun r x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]

abbrev Property1 : golay_code_space' → Prop := -- taking the sum of F4 by index maps to the hexaCode
  fun f => to_hexacode' f ∈ hexaCode

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
      exact Submodule.add_mem hexaCode ha1 hb1
    . intro i
      simp only [map_add, Pi.add_apply]
      rw [ha2,hb2]
  zero_mem' := by
    simp only [Finset.filter_congr_decidable, Finset.coe_filter, Finset.mem_univ, true_and,
      Set.mem_setOf_eq]
    constructor
    . exact (Submodule.Quotient.mk_eq_zero hexaCode).mp rfl
    . exact congrFun rfl
  smul_mem' := fun ⟨i,hi⟩ x hx => by
    simp only [Set.mem_setOf_eq]
    rcases i
    . simp only [Nat.zero_eq, Fin.zero_eta, zero_smul]
      constructor
      . exact (Submodule.Quotient.mk_eq_zero hexaCode).mp rfl
      . exact congrFun rfl
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

#synth _LinearCode ℕ∞ (ZMod 2) trivdist hdist GolayCode

def golay_code_space'.compl : golay_code_space' → golay_code_space' := (1 - .)

set_option maxHeartbeats 300000

lemma GolayCode.mem_compl : ∀ f ∈ GolayCode, f.compl ∈ GolayCode :=
  fun _ hf => GolayCode.sub_mem (GolayCode.one_mem) hf

lemma aut_smul_map_dist (φ: LinearCodeAut F4 trivdist hdist hexaCode) :
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
    toFun := fun ⟨⟨i,x⟩,hz⟩ => ⟨⟨(extract_perm φ).symm i,(extract_diag φ ((extract_perm φ).symm i))⁻¹ • x⟩,by
      nth_rw 1 [HSMul.hSMul,instHSMul]
      simp_rw [SMul.smul]
      simp only [Equiv.apply_symm_apply, smul_inv_smul]
      exact hz⟩
    invFun := fun z => ⟨⟨extract_perm φ z.1.1,extract_diag φ z.1.1 • z.1.2⟩,by
      exact z.2⟩
    left_inv := fun z => by
      simp only [Pi.sub_apply, Equiv.apply_symm_apply, smul_inv_smul, Prod.mk.eta,
        Subtype.coe_eta]
    right_inv := fun z => by
      simp only [Pi.sub_apply, Equiv.symm_apply_apply, inv_smul_smul, Prod.mk.eta,
        Subtype.coe_eta]
  }

lemma aut_smul_map_property1 (φ: LinearCodeAut F4 trivdist hdist hexaCode) :
    ∀ (x : golay_code_space'), Property1 x → Property1 (DomMulAct.mk φ • x) := fun x hx => by
  simp_rw [Property1] at hx ⊢
  suffices hsuf : φ (to_hexacode' (DomMulAct.mk φ • x)) = (to_hexacode' x) by
    rw [← hsuf] at hx
    apply φ.invMap_code
    exact hx
  simp_rw [to_hexacode']
  ext i : 1
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [extract_gives_stuff_strong]
  nth_rw 1 [HSMul.hSMul,instHSMul]
  nth_rw 1 [HSMul.hSMul,instHSMul]
  nth_rw 2 [HSMul.hSMul,instHSMul]
  simp_rw [SMul.smul]
  simp only [Equiv.symm_apply_apply, Function.comp_apply]
  nth_rw 3 [HSMul.hSMul,instHSMul]
  simp_rw [SMul.smul]
  simp only [Equiv.apply_symm_apply]
  calc
    extract_diag φ ((extract_perm φ).symm i) •
        (∑ x_1 : F4, x (i, extract_diag φ ((extract_perm φ).symm i) • x_1) • x_1)
      = ∑ x_1 : F4, extract_diag φ ((extract_perm φ).symm i) •
        (x (i, extract_diag φ ((extract_perm φ).symm i) • x_1) • x_1) := by
      exact Finset.smul_sum
    _ = ∑ x_1 : F4, x (i, extract_diag φ ((extract_perm φ).symm i) • x_1) •
        (extract_diag φ ((extract_perm φ).symm i) • x_1) := by
      conv =>
        left
        right
        intro x1
        rw [smul_comm]
    _ = ∑ x_1 : F4, x (i, x_1) • x_1 := by
      rw [← (?equiv:F4 ≃ F4).sum_comp]
      case equiv =>
        exact MulAction.toPerm (extract_diag φ ((extract_perm φ).symm i))⁻¹
      simp only [MulAction.toPerm_apply, smul_inv_smul]

lemma aut_smul_map_property2 (φ: LinearCodeAut F4 trivdist hdist hexaCode) :
    ∀ (x : golay_code_space'), Property2 x → Property2 (DomMulAct.mk φ • x) := fun x hx => by
  simp_rw [Property2, to_binary_vert',to_binary_hori'] at hx ⊢
  simp_all only [LinearMap.coe_mk, AddHom.coe_mk]
  intro i
  simp_rw [HSMul.hSMul,instHSMul,SMul.smul]
  simp only [Equiv.symm_apply_apply]
  simp_rw [HSMul.hSMul,instHSMul,SMul.smul]
  simp only [smul_zero]
  nth_rw 1 [← (?equiv:F4 ≃ F4).sum_comp]
  case equiv => exact MulAction.toPerm (extract_diag φ i)⁻¹
  simp only [MulAction.toPerm_apply, smul_inv_smul]
  rw [(extract_perm φ).sum_comp (fun i => x (i,0))]
  exact hx (extract_perm φ i)

-- with a little luck this is a mulhom
noncomputable def GolayCode.lift_hexacode_aut' (φ: LinearCodeAut F4 trivdist hdist hexaCode):
    LinearCodeAut (ZMod 2) trivdist hdist GolayCode := {
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
    . exact aut_smul_map_property2 φ (DomMulAct.mk φ⁻¹ • y) hy₂}

noncomputable def GolayCode.lift_hexacode_aut :
    LinearCodeAut F4 trivdist hdist hexaCode →* LinearCodeAut (ZMod 2) trivdist hdist GolayCode where
      toFun := GolayCode.lift_hexacode_aut'
      map_one' := by
        rw [GolayCode.lift_hexacode_aut']
        simp only [inv_one, DomMulAct.mk_one, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
          LinearEquiv.coe_coe, LinearEquiv.invFun_eq_symm]
        ext f : 1
        simp only [LinearCodeEquiv.coe_mk, CodeEquiv.coe_mk, GIsometryEquiv.coe_mk, Equiv.coe_fn_mk,
          DistribMulAction.toLinearEquiv_apply, one_smul, LinearCodeAut.one_apply]
      map_mul' := fun x y => by
        ext f : 1
        simp only [LinearCodeAut.mul_apply]
        simp_rw [lift_hexacode_aut']
        simp only [_root_.mul_inv_rev, DomMulAct.mk_mul, DomMulAct.mk_inv, AddHom.toFun_eq_coe,
          LinearMap.coe_toAddHom, LinearEquiv.coe_coe, LinearEquiv.invFun_eq_symm,
          LinearCodeEquiv.coe_mk, CodeEquiv.coe_mk, GIsometryEquiv.coe_mk, Equiv.coe_fn_mk,
          DistribMulAction.toLinearEquiv_apply]
        simp_rw [mul_smul]

example (φ : LinearCodeAut F4 trivdist hdist hexaCode)
    (f : golay_code_space') (x: golay_code_index) :
    f x = (GolayCode.lift_hexacode_aut φ f) (φ • x):= by
  simp_rw [GolayCode.lift_hexacode_aut]
  simp only [MonoidHom.coe_mk, OneHom.coe_mk]
  simp_rw [GolayCode.lift_hexacode_aut']
  simp only [DomMulAct.mk_inv, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe,
    LinearEquiv.invFun_eq_symm, LinearCodeEquiv.coe_mk, CodeEquiv.coe_mk, GIsometryEquiv.coe_mk,
    Equiv.coe_fn_mk, DistribMulAction.toLinearEquiv_apply]
  nth_rw 1 [HSMul.hSMul,instHSMul]
  simp_rw [SMul.smul]
  simp only [DomMulAct.symm_mk_inv, Equiv.symm_apply_apply, inv_smul_smul]

#synth AddAction F_4_6 golay_code_space'

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

lemma mem_vadd_map_property1 ⦃f: F_4_6⦄ (hf: f ∈ hexaCode) :
    ∀ (x:golay_code_space'), Property1 x → Property1 (f +ᵥ x) := fun x hx => by
  simp_rw [Property1,to_hexacode'] at hx ⊢
  simp_all only [LinearMap.coe_mk, AddHom.coe_mk]
  suffices hsuf : ((fun i ↦ ∑ x_1 : F4, (f +ᵥ x) (i, x_1) • x_1)) = f + to_hexacode' x by
    rw [hsuf,to_hexacode']
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    apply hexaCode.add_mem hf hx
  ext i : 1
  simp_rw [to_hexacode']
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]


def GolayCode.lift_hexacode_mem ⦃f:F_4_6⦄ (hf : f ∈ hexaCode) :
    LinearCodeAut (ZMod 2) trivdist hdist GolayCode := {
  AddAction.toPerm f with
  map_dist := fun x y => by
    simp only
    exact mem_vadd_map_dist f x y
  map_code := fun x ⟨hx₁,hx₂⟩ => by
    constructor
    . simp only [Equiv.toFun_as_coe, AddAction.toPerm_apply]
      sorry
    . sorry
  invMap_code := sorry
  map_add' := sorry
  map_smul' := sorry

  }

-- #synth Module (ZMod 2) golay_code_space'
-- #synth Group (LinearCodeAut F4 trivdist hdist hexaCode)ᵈᵐᵃ
-- -- #synth AddAction (F_4_6ᵈᵃᵃ) (golay_code_space') -- equivalent
-- #synth DistribMulAction ((LinearCodeAut F4 trivdist hdist hexaCode)ᵈᵐᵃ) golay_code_space'
-- #synth _LinearCode ℕ∞ (ZMod 2) trivdist hdist GolayCode
