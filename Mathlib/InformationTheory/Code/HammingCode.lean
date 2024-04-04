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
-- variable (s:Set (ι → K)) [IsDelone hdist s]
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
  gdist_absorb_add := fun z x y=> by
    simp only [hammingENatdist_eq_cast_hammingDist, Nat.cast_inj]
    rw[hammingDist,hammingDist]
    simp

-- prefer [AddMonoid K] [IsCancelAdd K] over [CancelAddMonoid],
-- because i want [Semiring K] and [IsCancelAdd K]
instance trivdist.instAddGNorm [AddMonoid K] [IsCancelAdd K]: AddGNorm K ℕ∞ trivdist where
  gdist_absorb_add := fun z x y=> by
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

def apply_perm : (ι ≃ ι)ᵈᵐᵃ →* MulAut (ι → Kˣ) := MulDistribMulAction.toMulAut (ι ≃ ι)ᵈᵐᵃ (ι → Kˣ)

instance : MulDistribMulAction (ι ≃ ι) (ι → K) where
  smul := fun σ f => f ∘ σ.symm
  one_smul := fun x => by
    simp_rw [HSMul.hSMul]
    simp only [Equiv.Perm.one_symm, Equiv.Perm.coe_one, Function.comp_id]
  mul_smul := fun x y f => by
    simp_rw [HSMul.hSMul]
    ext i
    simp only [Function.comp_apply]
    simp_rw [HMul.hMul,Mul.mul]
    simp only [Equiv.symm_trans_apply]
  smul_mul := fun _ _ _ => rfl
  smul_one := fun _ => rfl

instance : DistribMulAction (ι ≃ ι) (ι → K) where
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl



instance : DistribMulAction ((ι → Kˣ) ⋊[apply_perm] (ι ≃ ι)ᵈᵐᵃ)ᵐᵒᵖ (ι → K) where
  smul := fun z f => DomMulAct.mk.symm (MulOpposite.unop z).right • ((MulOpposite.unop z).left • f)
  one_smul := fun x => by
    simp_rw [HSMul.hSMul,SMul.smul]
    simp only [MulOpposite.unop_one, SemidirectProduct.one_left, Pi.one_apply, one_smul,
      SemidirectProduct.one_right, DomMulAct.symm_mk_one, Equiv.Perm.one_symm, Equiv.Perm.coe_one,
      Function.comp_id]
  mul_smul := fun z₁' z₂' f => by
    ext i
    simp_rw [HMul.hMul,Mul.mul]
    simp_rw [HSMul.hSMul,SMul.smul]
    obtain ⟨d₁,σ₁'⟩ := MulOpposite.unop z₁' -- surely there should be a better way to do this.
    obtain ⟨d₂,σ₂'⟩ := MulOpposite.unop z₂'
    simp only [SemidirectProduct.mk_eq_inl_mul_inr, MulOpposite.op_mul, MulOpposite.unop_mul,
      MulOpposite.unop_op, SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, map_one, SemidirectProduct.left_inr, mul_one,
      SemidirectProduct.mul_right, SemidirectProduct.right_inr, one_mul, Pi.mul_apply,
      DomMulAct.symm_mk_mul, Function.comp_apply]
    simp_rw [apply_perm,MulDistribMulAction.toMulAut]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, MulDistribMulAction.toMulEquiv_apply]
    simp_rw [HSMul.hSMul,SMul.smul]
    simp only [Equiv.Perm.smul_def, Units.val_mul, smul_eq_mul]
    obtain σ₁ := DomMulAct.mk.symm σ₁'
    obtain σ₂ := DomMulAct.mk.symm σ₂'
    nth_rewrite 3 [HMul.hMul,instHMul]
    nth_rewrite 3 [HMul.hMul,instHMul]
    nth_rewrite 3 [HMul.hMul,instHMul]
    simp_rw [Mul.mul]
    simp only [Equiv.symm_trans_apply, Equiv.apply_symm_apply]
    ring_nf
  smul_zero := fun z => by
    ext i
    simp_rw [HSMul.hSMul,SMul.smul]
    simp only [Pi.zero_apply, smul_zero, Function.comp_apply]
  smul_add := fun z f g => by
    ext i
    simp_rw [HSMul.hSMul,SMul.smul]
    simp only [Pi.add_apply, smul_add, Function.comp_apply]

-- now LinearAut (ι → K) has a subgroup

-- #synth MulAction ((ι → Kˣ) ⋊[apply_perm] (ι ≃ ι)ᵈᵐᵃ)ᵐᵒᵖ (ι → K)
--(ι → K ≃ₗ[K] ι → K)

/-
It is important to note that here, `(σ:(ι≃ι)ᵈᵐᵃ) • (d:(ι → Kˣ))` means something different from
`(σ : ι ≃ ι) • (x:ι → K)`.

More precisely, in the first case we have `σ • d = d ∘ σ`,
while in the second case we have `σ • x = x ∘ σ.symm`

this is all needed to have the proper DistribMulActions and accompanying properties, *and*
to be able to more easily and directly characterise arbitrary LinearCodeAuts in terms of this group.

all of these definitions hinge on the choice of how we want (d,σ) to act on an element (x:ι → K).
there are several possibilities, among which:
- `fun (d,σ) x => (d • (x ∘ σ))`
- `fun (d,σ) x => ((d • x) ∘ σ)`
- `fun (d,σ) x => (d • (x ∘ σ.symm))`
- `fun (d,σ) x => ((d • x) ∘ σ.symm)` -- this is the one used in this file.
by using the chosen definition,
you can derive the appropriate definitions of (σ • d) and (σ • x) by looking at
the property for DistribMulAction mul_smul, which says that you want the following to hold:
  `((d₁,σ₁) * (d₂,σ₂)) • x = (d₁,σ₁) • ((d₂,σ₂) • x)`
rewrite the right hand side using the chosen definition, then pick the left hand side multiplication
to match. in our case, this results in the group `(ι → Kˣ) ⋊[apply_perm] (ι ≃ ι)ᵈᵐᵃ)ᵐᵒᵖ` with
an instance `DistribMulAction ((ι → Kˣ) ⋊[apply_perm] (ι ≃ ι)ᵈᵐᵃ)ᵐᵒᵖ (ι → K)`, such that
`(⟨⟨d,⟨σ⟩⟩⟩ • x) i = (d (σ.symm i) * x (σ.symm i)), which means in particular that
the `i`th basis vector gets mapped to the `σ i`th one, and multiplied with `d i`.
this characterisation allows for an easy recovery of `σ` and `d` from the action.
-/
lemma SMul_def (d:(ι → Kˣ)) (σ :(ι ≃ ι)) (x: ι → K) :
  (MulOpposite.op ⟨d,DomMulAct.mk σ⟩:((ι → Kˣ) ⋊[apply_perm] (ι ≃ ι)ᵈᵐᵃ)ᵐᵒᵖ) • x = σ • d • x  := rfl

instance : SMulCommClass ((ι → Kˣ) ⋊[apply_perm] (ι ≃ ι)ᵈᵐᵃ)ᵐᵒᵖ K (ι → K) where
  smul_comm := fun m n a => by
    ext i
    simp_rw [HSMul.hSMul,SMul.smul]
    simp only [smul_eq_mul]
    simp_rw [HSMul.hSMul,SMul.smul]
    simp only [Function.comp_apply]
    obtain ⟨d,σ'⟩ := MulOpposite.unop m
    simp only
    obtain σ := DomMulAct.mk.symm σ'
    simp_rw [HSMul.hSMul,SMul.smul]
    simp only [smul_eq_mul]
    ring_nf

def toModuleAut : ((ι → Kˣ) ⋊[apply_perm] (ι ≃ ι)ᵈᵐᵃ)ᵐᵒᵖ →* ((ι → K) ≃ₗ[K] (ι → K)) :=
  DistribMulAction.toModuleAut K (ι → K)

lemma toModuleAut_def (d:(ι → Kˣ)) (σ :(ι ≃ ι)) (x: ι → K) : toModuleAut ⟨⟨d,⟨σ⟩⟩⟩ x = σ • (d • x) := rfl

noncomputable abbrev b : Basis ι K (ι → K) := Pi.basisFun K ι


lemma toModuleAut.inj [DecidableEq ι] [DecidableEq K]: Function.Injective (@toModuleAut ι K _) := fun x y => by
  obtain ⟨d₁,⟨σ₁⟩⟩ := x
  obtain ⟨d₂,⟨σ₂⟩⟩ := y
  rw [LinearEquiv.ext_iff]
  simp_rw [toModuleAut_def]
  intro h
  have hd :∀ i, σ₁ i = σ₂ i ∧ d₁ i = d₂ i:= by
    intro i
    obtain hz := h (b i)
    have hz₁ : ∀ j, (σ₁ • d₁ • (b i:ι → K)) j = (σ₂ • d₂ • (b i:ι → K)) j := by
      simp_rw [hz,implies_true]
    simp_rw [HSMul.hSMul, SMul.smul] at hz₁
    simp only [Function.comp_apply] at hz₁
    obtain hz₂ := hz₁ (σ₁ i)
    simp only [Equiv.symm_apply_apply] at hz₂
    rw [b] at hz₂
    simp only [Pi.basisFun_apply, LinearMap.stdBasis_apply', ↓reduceIte, smul_ite, smul_zero] at hz₂
    simp_rw [HSMul.hSMul,SMul.smul] at hz₂
    simp only [smul_eq_mul, mul_one] at hz₂
    split at hz₂
    . rename_i h
      rw [h.symm] at hz₂
      rw [Units.ext_iff]
      rw [hz₂]
      simp only [and_true]
      nth_rw 2 [h]
      simp only [Equiv.apply_symm_apply]
    . simp only [Units.ne_zero] at hz₂
  simp only at hd
  have hσ : σ₁ = σ₂ := by
    ext i
    exact (hd i).left
  have hd' : d₁ = d₂ := by
    ext i : 1
    exact (hd i).right
  rw [hσ,hd']

variable [Fintype K] [DecidableEq K] [DecidableEq ι] (f:LinearCodeAut K trivdist hdist s)

lemma basis_vec_norm_one (i:ι): addGNorm (hdist: GMetric (ι → K) ℕ∞) (b i) = 1 := by
  rw [addGNorm]
  simp only [hammingENatdist_eq_cast_hammingDist, hammingDist_zero_right, Nat.cast_eq_one]
  rw [b,hammingNorm]
  simp only [ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not]
  simp only [Pi.basisFun_apply, LinearMap.stdBasis_apply', ite_eq_right_iff, one_ne_zero, imp_false,
    not_not]
  suffices (Finset.filter (fun x ↦ i = x) Finset.univ) = ({i}:Finset ι) by
    exact Finset.card_eq_one.mpr (Exists.intro i this)
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  exact eq_comm

lemma norm_one_basis_like {x: ι → K} : addGNorm hdist x = 1 ↔ ∃! (i:ι), x i ≠ 0 := by
  rw [addGNorm]
  simp only [hammingENatdist_eq_cast_hammingDist, hammingDist_zero_right, Nat.cast_eq_one]
  exact Iff.symm (Fintype.exists_unique_iff_card_one fun a ↦ ¬x a = 0)

-- it's nice that it's true, but i'm not sure it's the most useful of lemmas.
theorem norm_one_basis_mul {x:ι → K} : addGNorm hdist x = 1 ↔ ∃! (c:ι × Kˣ), x = c.2 • b c.1 := by
  constructor
  . rw [norm_one_basis_like]
    intro h
    obtain ⟨i,hi⟩ := h
    use ⟨i,{
      val := x i
      inv := (x i)⁻¹
      val_inv := by apply mul_inv_cancel hi.left
      inv_val := by apply inv_mul_cancel hi.left
    }⟩
    simp only [Units.smul_mk_apply, Prod.forall, Prod.mk.injEq]
    constructor
    . simp at hi
      ext j
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [b]
      simp only [Pi.basisFun_apply, LinearMap.stdBasis_apply', mul_ite, mul_one, mul_zero]
      split
      . rename_i h
        rw [h]
      . rename_i h
        obtain z := (hi.right j)
        contrapose! z
        exact ⟨z,Ne.symm h⟩
    simp at hi
    intro i₂ c₂ h
    obtain ⟨hi₁,hi₂⟩ := hi
    simp_all
    have h₂: i₂ = i := by
      apply hi₂
      rw [h]
      simp only [Pi.smul_apply]
      simp only [LinearMap.stdBasis_apply', ↓reduceIte]
      simp_rw [HSMul.hSMul,SMul.smul]
      simp only [smul_eq_mul, mul_one, Units.ne_zero, not_false_eq_true]
    use h₂
    ext
    simp only
    rw [← h₂]
    simp only [↓reduceIte]
    simp_rw [HSMul.hSMul,SMul.smul]
    simp only [smul_eq_mul, mul_one]
  . intro ⟨⟨i,k⟩,⟨hi₁,hi₂⟩⟩
    rw [addGNorm]
    simp only [hammingENatdist_eq_cast_hammingDist, hammingDist_zero_right, Nat.cast_eq_one]
    simp at hi₁
    rw [hi₁]
    rw [hammingNorm]
    simp only [Pi.smul_apply, ne_eq, Finset.filter_congr_decidable]
    suffices h: (Finset.filter (fun i => x i ≠ 0) Finset.univ) = {i} by
      rw [hi₁] at hi₂
      simp_all only [Prod.forall, Prod.mk.injEq, Pi.smul_apply, ne_eq, Finset.filter_congr_decidable,
        Finset.card_singleton]
    ext j
    rw [hi₁]
    simp only [Pi.smul_apply, Finset.filter_congr_decidable, Finset.mem_filter,
      Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    . simp only [LinearMap.stdBasis_apply', smul_ite, smul_zero, ne_eq, ite_eq_right_iff,
      not_forall, exists_prop, and_imp]
      intro h
      contrapose! h
      exact Ne.symm (h.right)
    . intro h
      rw [h]
      simp only [LinearMap.stdBasis_apply', ↓reduceIte, ne_eq]
      simp_rw [HSMul.hSMul,SMul.smul]
      simp only [smul_eq_mul, mul_one, ne_eq, Units.ne_zero, not_false_eq_true]


lemma map_index_to_stuff (i:ι): ∃! (c:ι × Kˣ), (f (b i)) = (c.2 • b c.1) := by
  have hz₂ : addGNorm hdist (f (b i)) = 1 := by
    rw [GIsometry.map_norm]
    exact basis_vec_norm_one i
  exact norm_one_basis_mul.mp hz₂


noncomputable def extract_perm' (i:ι) : ι := (map_index_to_stuff f i).exists.choose.1

noncomputable def extract_diag (i:ι) : Kˣ := (map_index_to_stuff f i).exists.choose.2

lemma extract_gives_stuff' (i:ι) : f (b i) = (extract_diag f i • b (extract_perm' f i)) := by
  exact (map_index_to_stuff f i).exists.choose_spec

lemma extract_gives_unique {i:ι} (j:ι) (k:Kˣ) :
  f (b i) = k • b j → (j,k) = (extract_perm' f i, extract_diag f i) := by
  intro h
  apply (map_index_to_stuff f i).unique
  . exact h
  . exact extract_gives_stuff' f i


lemma extract_gives_unique_perm' (i:ι) (j:ι) (k:Kˣ) : f (b i) = k • b j → (j = extract_perm' f i) := by
  intro h
  have hz := (extract_gives_unique f j k h)
  simp only [Prod.mk.injEq] at hz
  exact hz.left


lemma extract_gives_unique_diag (i:ι) (j:ι) (k:Kˣ) : f (b i) = k • b j → (k = extract_diag f i) := by
  intro h
  have hz := (extract_gives_unique f j k h)
  simp only [Prod.mk.injEq] at hz
  exact hz.right

noncomputable def extract_perm : ι ≃ ι where
  toFun := extract_perm' f
  invFun := extract_perm' f.symm
  left_inv := by
    intro i
    apply (extract_gives_unique_perm' f.symm _ i (extract_diag f i)⁻¹ _).symm
    rw [← f.left_inv (b i)]
    simp only [LinearCodeEquiv.toCodeEquiv_eq_coe, CodeEquiv.toGIsometryEquiv_eq_coe,
      GIsometryEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe,
      CodeEquiv.coe_toGIsometryEquiv, LinearCodeEquiv.coe_toCodeEquiv, Equiv.invFun_as_coe,
      GIsometryEquiv.coe_toEquiv_symm, CodeEquiv.coe_toGIsometryEquiv_symm,
      LinearCodeEquiv.coe_toCodeEquiv_symm]
    rw [extract_gives_stuff' f i]
    simp_rw [HSMul.hSMul, SMul.smul]
    rw [SemilinearMapClass.map_smulₛₗ f.symm]
    simp only [Units.val_inv_eq_inv_val, RingHom.id_apply, ne_eq, Units.ne_zero,
      not_false_eq_true, inv_smul_smul₀]
  right_inv := by
    intro i
    apply (extract_gives_unique_perm' f _ i (extract_diag (LinearCodeEquiv.symm f) i)⁻¹ _).symm
    rw [← f.right_inv (b i)]
    simp only [LinearCodeEquiv.toCodeEquiv_eq_coe, CodeEquiv.toGIsometryEquiv_eq_coe,
      GIsometryEquiv.toEquiv_eq_coe, Equiv.invFun_as_coe, GIsometryEquiv.coe_toEquiv_symm,
      CodeEquiv.coe_toGIsometryEquiv_symm, LinearCodeEquiv.coe_toCodeEquiv_symm,
      Equiv.toFun_as_coe, EquivLike.coe_coe, CodeEquiv.coe_toGIsometryEquiv,
      LinearCodeEquiv.coe_toCodeEquiv]
    rw [extract_gives_stuff' f.symm i]
    simp_rw [HSMul.hSMul, SMul.smul]
    rw [SemilinearMapClass.map_smulₛₗ f]
    simp only [Units.val_inv_eq_inv_val, RingHom.id_apply, ne_eq, Units.ne_zero,
      not_false_eq_true, inv_smul_smul₀]

lemma extract_perm_is_perm': extract_perm' f = (extract_perm f) := by rfl

lemma extract_gives_stuff (i:ι) :
    f (b i) = extract_perm f • (extract_diag f • (b i:ι → K)) := by
  ext j
  calc
    f (b i) j = ((extract_diag f i) • (b (extract_perm f i): ι → K)) j:= by
      rw [extract_gives_stuff' f i, extract_perm_is_perm']
    _ = extract_diag f ((extract_perm f).symm j) • b i ((extract_perm f).symm j) := by
      simp only [Pi.smul_apply]
      simp_rw [b]
      simp only [Pi.basisFun_apply, LinearMap.stdBasis_apply', smul_ite, smul_zero]
      split
      . rename_i h
        rw [h.symm]
        simp only [Equiv.symm_apply_apply, ↓reduceIte]
      . rename_i h
        split
        . rename_i h₂
          rw [h₂] at h
          simp only [Equiv.apply_symm_apply, not_true_eq_false] at h
        . rfl
    _ = (extract_diag f • (b i:ι → K)) ((extract_perm f).symm j) := by rw [Pi.smul_apply']
    _ = (extract_perm f • (extract_diag f • (b i:ι → K))) j := by rfl

instance : SMulCommClass (ι ≃ ι) K (ι → K) where
  smul_comm := fun _ _ _ ↦ rfl

instance : SMulCommClass (ι → Kˣ) K (ι → K) where
  smul_comm := by exact fun m n a ↦ (smul_comm n m a).symm

lemma extract_gives_stuff_strong (x:ι → K) : f x = extract_perm f • (extract_diag f • x) := by
  suffices hsuf :
      ((DistribMulAction.toLinearEquiv K (ι → K) (extract_diag f)).trans
      (DistribMulAction.toLinearEquiv K (ι → K) (extract_perm f))) = f by
    rw [LinearEquiv.ext_iff] at hsuf
    simp only [LinearEquiv.trans_apply, DistribMulAction.toLinearEquiv_apply,
      LinearCodeEquiv.coe_toLinearEquiv] at hsuf
    rw [hsuf]
  apply b.ext'
  simp only [LinearEquiv.trans_apply, DistribMulAction.toLinearEquiv_apply,
    LinearCodeEquiv.coe_toLinearEquiv]
  exact fun i ↦ (extract_gives_stuff f i).symm

noncomputable def toSemidirectProd' (f:LinearCodeAut K trivdist hdist s) :
    ((ι → Kˣ) ⋊[apply_perm] (ι ≃ ι)ᵈᵐᵃ)ᵐᵒᵖ :=
  MulOpposite.op ⟨extract_diag f,DomMulAct.mk (extract_perm f)⟩

@[simp]
lemma toModuleAut_apply_eq_smul
    (f:LinearCodeAut K trivdist hdist s) (x: ι → K):
    toModuleAut (toSemidirectProd' f) x = toSemidirectProd' f • x := by rfl

@[simp]
lemma toModuleAut_toSemiProd_eq_coe (f:LinearCodeAut K trivdist hdist s) :
    toModuleAut (toSemidirectProd' f) = f := by
  apply b.ext'
  intro i
  simp only [LinearCodeEquiv.coe_toLinearEquiv]
  rw [extract_gives_stuff]
  rw [toSemidirectProd',toModuleAut]
  simp only [map_mul, DistribMulAction.toModuleAut_apply]
  rw [DistribMulAction.toLinearEquiv]
  simp only [AddEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, Equiv.invFun_as_coe,
    AddEquiv.coe_toEquiv_symm, LinearEquiv.coe_mk, DistribMulAction.toAddEquiv_apply]
  rw [SMul_def]

@[simp]
lemma coe_toSemidirectProd'
    (f:LinearCodeAut K trivdist hdist s) :
    ∀ (x:ι → K), (toSemidirectProd' f) • x = f x := by
  intro x
  rw [← toModuleAut_apply_eq_smul]
  rw [toModuleAut_toSemiProd_eq_coe]
  rfl

lemma toSemidirectProd'_inj : Function.Injective (toSemidirectProd': LinearCodeAut K trivdist hdist s →
    ((ι → Kˣ) ⋊[apply_perm] (ι ≃ ι)ᵈᵐᵃ)ᵐᵒᵖ) := fun x y h => by
  ext f i
  suffices hsuf1 :(x:(ι → K) ≃ₗ[K] (ι → K)) = (y: (ι → K) ≃ₗ[K] (ι → K)) by
    rw [← LinearCodeEquiv.coe_toLinearEquiv x, ← LinearCodeEquiv.coe_toLinearEquiv y]
    rw [hsuf1]
  apply b.ext'
  intro i
  rw [← toModuleAut_toSemiProd_eq_coe,← toModuleAut_toSemiProd_eq_coe]
  rw [h]

noncomputable def toSemidirectProd : (LinearCodeAut K trivdist hdist s) →* ((ι → Kˣ) ⋊[apply_perm] (ι ≃ ι)ᵈᵐᵃ)ᵐᵒᵖ where
  toFun := toSemidirectProd'
  map_one' := by
    apply toModuleAut.inj
    simp only [toModuleAut_toSemiProd_eq_coe, map_one]
    ext i
    simp only [LinearCodeEquiv.coe_toLinearEquiv, LinearCodeAut.one_apply, LinearEquiv.coe_one,
      id_eq]
  map_mul' := fun x y => by
    simp only [SemidirectProduct.mk_eq_inl_mul_inr]
    apply toModuleAut.inj
    simp only [map_mul]
    apply b.ext'
    intro i
    ext j
    simp only [toModuleAut_toSemiProd_eq_coe, LinearCodeEquiv.coe_toLinearEquiv,
      LinearCodeAut.mul_apply]
    simp_rw [HMul.hMul,instHMul,Mul.mul]
    simp only [LinearEquiv.trans_apply, LinearCodeEquiv.coe_toLinearEquiv]


def lift_toLinearCodeAut
    (c:((ι → Kˣ) ⋊[apply_perm] (ι ≃ ι)ᵈᵐᵃ)ᵐᵒᵖ) (hc: ∀ x, x ∈ s ↔ c • x ∈ s) :
    LinearCodeAut K trivdist hdist s := {
      toModuleAut c with
      map_code := fun x => (hc x).mp
      invMap_code := fun x => (hc x).mpr
      map_dist := fun x y => by
        rw [addDist_eq,addDist_eq]
        simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
        simp_rw [addGNorm,hdist]
        simp only [hammingENatdist_eq_cast_hammingDist, hammingDist_zero_right, Nat.cast_inj]
        rw [← (toModuleAut c).map_sub]
        simp_rw [hammingNorm]
        simp only [Pi.sub_apply, Finset.filter_congr_decidable]
        suffices hsuf :
            Finset.filter (fun x_1 ↦ (x - y) x_1 ≠ 0) Finset.univ ≃
            Finset.filter (fun x_1 ↦ (toModuleAut c) (x - y) x_1 ≠ 0) Finset.univ by
          exact Finset.card_eq_of_equiv hsuf
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        obtain ⟨d,⟨σ⟩⟩ := c
        exact {
          toFun := fun ⟨i,hi⟩ => ⟨σ i, by
            rw [toModuleAut]
            simp_rw [DistribMulAction.toModuleAut]
            simp only [MonoidHom.coe_mk, OneHom.coe_mk, DistribMulAction.toLinearEquiv_apply]
            simp_rw [HSMul.hSMul,SMul.smul,MulOpposite.unop]
            simp_rw [HSMul.hSMul,SMul.smul]
            simp only [Function.comp_apply]
            simp_rw [DomMulAct.mk,MulOpposite.opEquiv]
            simp only [Equiv.coe_fn_symm_mk]
            simp_rw [MulOpposite.unop]
            simp only [Equiv.symm_apply_apply]
            simp_rw [HSMul.hSMul,SMul.smul]
            simp_all only [SemidirectProduct.mk_eq_inl_mul_inr, Pi.sub_apply, ne_eq, smul_eq_mul,
              mul_eq_zero, Units.ne_zero, or_self, not_false_eq_true]
            ⟩
          invFun := fun ⟨i,hi⟩ => ⟨σ.symm i, by
            simp_rw [toModuleAut,DistribMulAction.toModuleAut] at hi
            simp only [MonoidHom.coe_mk, OneHom.coe_mk,DistribMulAction.toLinearEquiv_apply] at hi
            simp_rw [HSMul.hSMul,SMul.smul] at hi
            simp_rw [DomMulAct.mk,MulOpposite.opEquiv] at hi
            simp only [Equiv.coe_fn_symm_mk] at hi
            simp_rw [MulOpposite.unop] at hi
            simp_rw [HSMul.hSMul,SMul.smul] at hi
            simp only [Function.comp_apply] at hi
            simp_rw [HSMul.hSMul,SMul.smul] at hi
            simp_all⟩
          left_inv := fun x => by
            simp only [Pi.sub_apply, ne_eq, Equiv.symm_apply_apply, Subtype.coe_eta]
          right_inv := fun x => by
            simp only [ne_eq, Equiv.apply_symm_apply, Subtype.coe_eta]
        }
    }
end linear
