import Mathlib.Topology.GMetric.WellSpaced
import Mathlib.Topology.GMetric.Isometry
import Mathlib.Topology.GMetric.GNorm
import Mathlib.InformationTheory.Hamming
import Mathlib.InformationTheory.Code.Linear.Aut
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.GroupAction.DomAct.Basic
import Mathlib.GroupTheory.SemidirectProduct

open Set
open GMetric
open Code

section hamming
variable {ι K:Type*} [Fintype ι] [DecidableEq K]

abbrev hdist :GMetric (ι → K) ℕ∞ := hammingENatDist
variable (s:Set (ι → K)) [IsDelone hdist s]
-- maybe sensitive to universe problems? because the choice of ι is *very* unimportant
def trivdist : GMetric K ℕ∞ where
  toFun := fun x y => hammingENatDist (Function.const (Fin 1) x) (Function.const (Fin 1) y)
  gdist_self := fun x => by simp
  comm' := fun x y => by
    apply hammingENatDist.comm'
  triangle' := fun x y z => by apply hammingENatDist.triangle'
  eq_of_dist_eq_zero := by simp

@[simp, push_cast]
theorem trivdist_eq_cast_hammingDist (x y : K) :
    trivdist x y = hammingENatDist (Function.const (Fin 1) x) (Function.const (Fin 1) y) :=
  rfl

instance Hamming.instAddGNorm [AddMonoid K] [IsCancelAdd K]: AddGNorm (∀ _:ι,K) ℕ∞ hdist where
  gdist_absorb_add := fun z => by
    ext x y
    rw [Function.onFun]
    simp only [hammingENatdist_eq_cast_hammingDist, Nat.cast_inj]
    rw[hammingDist,hammingDist]
    simp

-- prefer [AddMonoid K] [IsCancelAdd K] over [CancelAddMonoid],
-- because i want [Semiring K] and [IsCancelAdd K]
instance trivdist.instAddGNorm [AddMonoid K] [IsCancelAdd K]: AddGNorm K ℕ∞ trivdist where
  gdist_absorb_add := fun z => by
    ext x y
    rw [Function.onFun]
    simp only [trivdist_eq_cast_hammingDist, hammingENatdist_eq_cast_hammingDist, Nat.cast_inj]
    rw [hammingDist,hammingDist]
    simp

lemma trivdist_eq (x y:K): trivdist x y = if x = y then 0 else 1 := by
  if h:x=y then
    rw [h]
    simp
  else
    simp only [trivdist_eq_cast_hammingDist, hammingENatdist_eq_cast_hammingDist]
    rw [hammingDist]
    simp_all

-- noncomputable because we depend on CompleteLinearOrder ENat
-- i'm not sure this is how this should be, but who knows
noncomputable instance Hamming.instStrictModuleGNorm_SemiRing_Domain
    [Semiring K] [IsDomain K] [IsCancelAdd K]: StrictModuleGNorm K K trivdist trivdist where
  norm_smul_le' := fun a b => by
    apply Eq.le
    rw [addGNorm,addGNorm,addGNorm]
    rw [trivdist_eq,trivdist_eq,trivdist_eq]
    simp only [smul_eq_mul, mul_eq_zero, mul_ite, mul_zero, mul_one]
    if ha:a=0 then
      rw [ha]
      simp only [true_or, ↓reduceIte, ite_self]
    else if hb:b=0 then
      rw [hb]
      simp only [or_true, ↓reduceIte]
    else
      simp_all only [or_self, ite_false]
  smul_norm_le' := fun a b => by
    apply Eq.le
    rw [addGNorm,addGNorm,addGNorm]
    rw [trivdist_eq,trivdist_eq,trivdist_eq]
    simp only [smul_eq_mul, mul_eq_zero, mul_ite, mul_zero, mul_one]
    if ha:a=0 then
      rw [ha]
      simp only [true_or, ↓reduceIte, ite_self]
    else if hb:b=0 then
      rw [hb]
      simp only [or_true, ↓reduceIte]
    else
      simp_all only [or_self, ite_false]

-- look into: hamming distance as measure on the set of indices where the things differ
-- look into: hamming distance as the sum of trivial distances in each of the dimensions

lemma norm_eq_smul
    [Semiring K] [IsCancelAdd K] [IsDomain K] (a : K) (b : ι → K) :
    addGNorm hdist (a • b) = addGNorm trivdist a * addGNorm hdist b := by
  rw [addGNorm,addGNorm,addGNorm]
  if ha:a=0 then
    rw [ha]
    simp_all
  else if hb:b=0 then
    rw [hb]
    simp_all
  else
    simp_all
    rw [hammingNorm,hammingNorm,hammingNorm]
    simp_all

noncomputable instance Hamming.instStrictModuleGNorm_Module
    [Semiring K] [IsCancelAdd K] [IsDomain K]: StrictModuleGNorm K (ι → K) trivdist hdist where
  norm_smul_le' := fun a b => (norm_eq_smul a b).le
  smul_norm_le' := fun a b => (norm_eq_smul a b).ge

instance instIsDelone (s:Set (ι → K)) [hs: Inhabited s]: IsDelone hdist s where
  isDeloneWith := ⟨1, (Fintype.card ι), {
    isOpenPacking := by
      obtain h := (s.exists_ne_mem_inter_of_not_pairwiseDisjoint).mt; push_neg at h ; apply h
      intro x _ y _ hne z;
      simp only [mem_inter_iff, not_and]
      intro hz
      rw [mem_ball] at hz ⊢
      simp_all,
    isClosedCoveringWith := by
      ext y
      simp only [mem_iUnion, exists_prop, mem_univ, iff_true]
      obtain ⟨x,hx⟩ := hs
      use x
      use hx
      rw [mem_closedBall]
      simp only [hammingENatdist_eq_cast_hammingDist, Nat.cast_le]
      exact hammingDist_le_card_fintype
  }⟩
end hamming

section linear
variable {ι K:Type*} [Fintype ι]
variable [Field K]
variable {s : Submodule K (ι → K)} [Inhabited s]


instance {G α β : Type*} [Monoid G] [Monoid β] [MulAction G α] :
    MulDistribMulAction (Gᵈᵐᵃ) (α → β) where
  smul_mul _ _ _ := funext fun _ => rfl
  smul_one _ := funext fun _ => rfl

def f : (ι ≃ ι)ᵈᵐᵃ →* MulAut (ι → Kˣ) := MulDistribMulAction.toMulAut (ι ≃ ι)ᵈᵐᵃ (ι → Kˣ)


-- now LinearAut (ι → K) has a subgroup

-- #synth MulAction (((ι → Kˣ) ⋊[f] (ι ≃ ι)ᵈᵐᵃ))ᵈᵐᵃ ((ι → K) ≃ₗ[K] (ι → K))
--(ι → K ≃ₗ[K] ι → K)

private abbrev g_toFun : ((ι → Kˣ) ⋊[f] (ι ≃ ι)ᵈᵐᵃ) → ((ι → K) ≃ₗ[K] (ι → K)) := fun ⟨d,σ⟩ => {
    toFun := fun φ => d • (σ • φ)
    map_add' := fun x y => by simp only [smul_add]
    map_smul' := fun k x => by
      simp only [RingHom.id_apply]; ext i
      simp only [Pi.smul_apply', Pi.smul_apply, smul_eq_mul,HSMul.hSMul,SMul.smul]
      ring_nf
    invFun := fun φ => σ⁻¹ • (d⁻¹ • φ)
    left_inv := fun x => by simp only [inv_smul_smul]
    right_inv := fun y => by simp
  }

private lemma g_map_one' : g_toFun (1: ((ι → Kˣ) ⋊[f] (ι ≃ ι)ᵈᵐᵃ)) = 1 := by
    rw [g_toFun]
    ring_nf; ext f i
    simp only [LinearEquiv.coe_one, id_eq, OfNat.ofNat, One.one,MulOpposite.op]
    simp only [LinearEquiv.coe_mk, Pi.smul_apply', Units.smul_mk_apply, smul_eq_mul,
      LinearEquiv.refl_apply]
    ring_nf
    rfl

-- this probably could use some golfing
private lemma g_map_mul' (x y:((ι → Kˣ) ⋊[f] (ι ≃ ι)ᵈᵐᵃ)): g_toFun (x * y) = g_toFun x * g_toFun y := by
  obtain ⟨d₁,σ₁⟩ := x; obtain ⟨d₂,σ₂⟩ := y; simp_rw [g_toFun]; ext f i
  simp only [mul_inv_rev, LinearEquiv.coe_mk, Pi.smul_apply', Pi.mul_apply]
  nth_rw 3 [HMul.hMul,instHMul]
  simp only
  simp_rw [Mul.mul,LinearEquiv.trans]
  simp only [Equiv.invFun_as_coe]
  have h₁ (z:(ι → K) ≃ₗ[K] (ι → K)) : z f = z.toLinearMap f:= rfl
  rw [h₁]
  simp only
  rw [LinearMap.comp]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Function.comp_apply, Pi.smul_apply']
  simp only [HSMul.hSMul,SMul.smul]
  ring_nf
  rfl

def g : ((ι → Kˣ) ⋊[f] (ι ≃ ι)ᵈᵐᵃ) →* ((ι → K) ≃ₗ[K] (ι → K)) where
  toFun := g_toFun
  map_one' := g_map_one'
  map_mul' := g_map_mul'

lemma g_def (d:(ι → Kˣ)) (σ :(ι ≃ ι)) (x: ι → K) :
  g ⟨d,⟨σ⟩⟩ x = d • (x ∘ σ) := rfl

lemma g_def_symm (d:(ι → Kˣ)) (σ :(ι ≃ ι)) (x: ι → K) :
  (g ⟨d,⟨σ⟩⟩).symm x = (d⁻¹ • x) ∘ σ.symm := rfl

def basis_vec (i:ι) [DecidableEq ι]: ι → K := fun j => if j = i then 1 else 0
lemma basis_vec_def [DecidableEq ι] : ∀ i, (basis_vec i:ι→K) = fun j => if j = i then 1 else 0 := by
  intro i;rfl

lemma g.inj [DecidableEq ι]: Function.Injective (@g ι K _) := fun x y => by
  obtain ⟨d₁,⟨σ₁⟩⟩ := x
  obtain ⟨d₂,⟨σ₂⟩⟩ := y
  rw [LinearEquiv.ext_iff]
  simp_rw [g_def]
  intro h
  have hd : d₁ = d₂ := by
    ext i
    obtain hz := h (Function.const ι 1)
    simp only [Function.const_one, Pi.one_comp] at hz
    simp only [HSMul.hSMul,SMul.smul,Pi.one_apply,funext] at hz
    ring_nf at hz
    have hsimp : (↑(d₁ i) = (fun i ↦ ((d₁ i):K)) i) := rfl
    rw [hsimp,hz]
  rw [hd] at h ⊢
  simp only [SemidirectProduct.mk_eq_inl_mul_inr, mul_right_inj, SemidirectProduct.inr_inj]
  suffices hsuf : (σ₁=σ₂) by rw [hsuf]
  ext i
  obtain hz := h (basis_vec (σ₂ i))
  simp only [dite_eq_ite, smul_left_cancel_iff] at hz
  have hyp : (basis_vec (σ₂ i) ∘ σ₁) i = (1:K) := by
    rw [hz]
    simp only [Function.comp_apply]
    rw [basis_vec]
    simp
  simp only [Function.comp_apply] at hyp
  rw [basis_vec] at hyp
  simp at hyp
  exact hyp

variable [Fintype K] [DecidableEq K] [DecidableEq ι] (f:LinearCodeAut K trivdist hdist s)

lemma basis_vec_norm_one (i:ι): addGNorm hdist ((@basis_vec ι K) i) = 1 := by
  rw [addGNorm]
  simp only [hammingENatdist_eq_cast_hammingDist, hammingDist_zero_right, Nat.cast_eq_one]
  rw [basis_vec_def]
  rw [hammingNorm]
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
  suffices (Finset.filter (fun x ↦ x = i) Finset.univ) = ({i}:Finset ι) by
    exact Finset.card_eq_one.mpr (Exists.intro i this)
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]

lemma norm_one_basis_mul {x: ι → K} : addGNorm hdist x = 1 ↔ ∃! (i:ι), x i ≠ 0 := by
  rw [addGNorm]
  simp only [hammingENatdist_eq_cast_hammingDist, hammingDist_zero_right, Nat.cast_eq_one]
  exact Iff.symm (Fintype.exists_unique_iff_card_one fun a ↦ ¬x a = 0)


noncomputable def extract_perm_toFun' (i:ι) : ι := by
  have hz₂ : addGNorm hdist (f ((@basis_vec ι K) i)) = 1 := by
    rw [GIsometry.map_norm]
    exact basis_vec_norm_one i
  obtain hz' : ∃! (j:ι), (f ((@basis_vec ι K) i)) j ≠ 0 := norm_one_basis_mul.mp hz₂
  exact hz'.exists.choose


noncomputable def extract_diag_toFun' (i:ι) : K :=
  (f ((@basis_vec ι K) i)) (extract_perm_toFun' f i)

lemma map_basis_unique_nzero (i:ι): ∃! (j:ι), (f ((@basis_vec ι K) i)) j ≠ 0 := by
  have foo : addGNorm hdist (f ((@basis_vec ι K) i)) = 1 := by
    rw [GIsometry.map_norm]
    exact basis_vec_norm_one i
  exact norm_one_basis_mul.mp foo

lemma extract_diag_nzero (i:ι): (f ((@basis_vec ι K) i)) (extract_perm_toFun' f i) ≠ 0 := by
  exact (map_basis_unique_nzero f i).exists.choose_spec

lemma map_basis_nzero_is_extracted_perm' (i:ι) (j:ι):
    (f ((@basis_vec ι K) i)) j ≠ 0 ↔ j = extract_perm_toFun' f i := by
  constructor
  . intro h
    apply (map_basis_unique_nzero f i).unique h
    exact extract_diag_nzero f i
  . intro h
    rw [h]
    exact extract_diag_nzero f i

lemma map_basis_nzero_is_extracted_diag' (i:ι) (j:ι):
    (f ((@basis_vec ι K) i)) j ≠ 0 ↔ (f ((@basis_vec ι K) i)) j = extract_diag_toFun' f i := by
  rw [extract_diag_toFun']
  constructor
  . intro h
    rw [(map_basis_nzero_is_extracted_perm' f i j).mp h]
  . intro h
    rw [h]
    exact extract_diag_nzero f i

noncomputable def extract_diag_toFun [DecidableEq ι] (f:LinearCodeAut K trivdist hdist s) (i:ι) : Kˣ :=⟨
  extract_diag_toFun' f i,
  (extract_diag_toFun' f i)⁻¹,
  by
    apply mul_inv_cancel
    exact extract_diag_nzero f i,
  by
    apply inv_mul_cancel
    exact extract_diag_nzero f i⟩


def extract_perm_invFun' :

-- def extract_perm [DecidableEq ι] (f:LinearCodeAut K trivdist hdist s) : ι ≃ ι where
--   toFun := extract_perm_toFun f
--   invFun := _
--   left_inv := _
--   right_inv := _





def map_lcodeaut_sprod : LinearCodeAut K trivdist hdist s →* ((ι → Kˣ) ⋊[f] (ι ≃ ι)ᵈᵐᵃ) where
  toFun := fun f => {
    right := DomMulAct.mk {
      toFun := _
      invFun := _
      left_inv := _
      right_inv := _
    }
    left := _
  }
  map_one' := _
  map_mul' := _

end linear
