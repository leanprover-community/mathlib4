import Mathlib.Topology.GMetric.WellSpaced
import Mathlib.Topology.GMetric.Isometry
import Mathlib.Topology.GMetric.GNorm
import Mathlib.InformationTheory.Hamming
import Mathlib.InformationTheory.Code.Linear.SemiAut
import Mathlib.InformationTheory.Code.Faithful
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


instance : SMulDistribSMulClass (RingAut K) (ι → Kˣ) (ι → K) where
  smul_distrib := fun φ d v => by
    ext i
    simp only [HSMul.hSMul, SMul.smul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]

instance : MulDistribMulAction (ι ≃ ι) (ι → Kˣ) where
  smul := fun σ v => DomMulAct.mk σ⁻¹ • v
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_mul := fun _ _ _ => rfl
  smul_one := fun _ => rfl

instance : DistribMulAction (ι ≃ ι) (ι → K) where
  smul := fun σ v => DomMulAct.mk σ⁻¹ • v
  one_smul := fun _ => rfl
  mul_smul := fun _ _ _ => rfl
  smul_zero := fun _ => rfl
  smul_add := fun _ _ _ => rfl

instance : SMulCommClass (RingAut K) (ι ≃ ι) (ι → Kˣ) where
  smul_comm := fun a b c => by ext i; rfl

instance : SMulCommClass (RingAut K) (ι ≃ ι) (ι → K) where
  smul_comm := fun a b c => by ext i; rfl


example (φ : RingAut K) (σ : ι ≃ ι) (v: ι → K) (i:ι) : ((φ,σ) • v ) i = φ (v (σ⁻¹ i)) := rfl

instance : SMulDistribSMulClass (RingAut K) (Kˣ) K where
  smul_distrib := fun φ u x => by
    simp only [HSMul.hSMul, SMul.smul, map_mul, Units.val_inv_eq_inv_val, map_inv₀]

instance : SMulDistribSMulClass (ι ≃ ι) (ι → Kˣ) (ι → K) where
  smul_distrib := fun σ d v => by
    ext i; rfl

-- example (x) (v:ι → K): proxy_distribmulaction.smul x v = (x.unop.right.unop,x.unop.left) • v := rfl

-- #check @semiproductmulaction (RingAut K × (ι ≃ ι)) (ι → Kˣ) (ι → K) _ _ _ _ _ _ _

-- #synth MulAction (B ⋊[invsmulMulHom] Aᵐᵒᵖ)ᵐᵒᵖ C

-- #synth MulAction ((ι → Kˣ) ⋊[invsmulMulHom] (RingAut K × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ (ι → K)


instance : DistribMulAction ((ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ (ι → K) where
  smul_zero := fun x => by ext i; simp only [HSMul.hSMul, SMul.smul, DomMulAct.mk_inv,
    DomMulAct.symm_mk_inv, Equiv.symm_apply_apply, Pi.zero_apply, mul_zero, map_zero]
  smul_add := fun a x y => by
    ext i;
    simp only [semiprod_mulact_apply, smul_add, Prod.smul_def', Pi.add_apply, Pi.smul_apply,
      RingAut.smul_def]


-- now LinearAut (ι → K) has a subgroup

/-
all of these definitions hinge on the choice of how we want (d,φ,σ) : (ι → Kˣ) × (RingAut K) × (ι ≃ ι)
to act on an element (x:ι → K).
there are several possibilities, among which:
- `fun (d,φ,σ) x => (d • (φ ∘ x ∘ σ))`
- `fun (d,φ,σ) x => ((d • (φ ∘ x)) ∘ σ)`
- `fun (d,σ) x => (d • (φ ∘ x ∘ σ.symm))`
- `fun (d,σ) x => (φ ∘ (d • x) ∘ σ.symm)` -- this is the one used in this file.
by using the chosen definition,
you can derive the appropriate definitions of (σ • d) and (σ • x) by looking at
the property for DistribMulAction mul_smul, which says that you want the following to hold:
  `((d₁,φ₁,σ₁) * (d₂,φ₂,σ₂)) • x = (d₁,φ₁,σ₁) • ((d₂,φ₂,σ₂) • x)`
rewrite the right hand side using the chosen definition, then pick the left hand side multiplication
to match. in our case, this results in the group
  `(ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ` with an instance
  `DistribMulAction ((ι → Kˣ) ⋊[apply_perm] (ι ≃ ι)ᵈᵐᵃ)ᵐᵒᵖ (ι → K)`, such that
`(⟨⟨d,⟨σ⟩⟩⟩ • x) i = (d (σ.symm i) * x (σ.symm i))`, which means in particular that
the `i`th basis vector gets mapped to the `σ i`th one, and multiplied with `d i`.
this characterisation allows for an easy recovery of `σ` and `d` from the action.
-/
lemma SemidirectProd.smul_def (d:(ι → Kˣ)) (φ:RingAut K) (σ :(ι ≃ ι)) (x: ι → K) :
  (MulOpposite.op ⟨d,MulOpposite.op (φ,σ)⟩:((ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ) • x = (φ,σ) • d • x := rfl


instance : SMulCommClass (ι ≃ ι) K (ι → K) where
  smul_comm := fun a b c => by ext i; rfl


lemma map_smul_somethin (z : ((ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ) (x : K) (v:ι → K) :
    z • x • v = (z.unop.right.unop.fst x) • z • v := by
  calc
    z • x • v = z.unop.right.unop • z.unop.left • x • v := rfl
    _ = z.unop.right.unop • x • z.unop.left • v := by rw [smul_comm x]
    _ = z.unop.right.unop.fst • z.unop.right.unop.snd • x • z.unop.left • v := by
      rw [Prod.smul_def']
    _ = z.unop.right.unop.fst • x • z.unop.right.unop.snd • z.unop.left • v := by
      rw [smul_comm z.unop.right.unop.snd]
    _ = (z.unop.right.unop.fst • x) • z.unop.right.unop.fst •
      z.unop.right.unop.snd • z.unop.left • v := by
        rw [SMulDistribSMulClass.smul_distrib]
    _ = (z.unop.right.unop.fst • x) • z.unop.right.unop • z.unop.left • v := by
      rw [Prod.smul_def']
    _ = (z.unop.right.unop.fst • x) • z • v := by
      rw [semiprod_mulact_apply]
    _ = z.unop.right.unop.fst x • z • v := by
      rw [RingAut.smul_def]

def fooooooooo1 (z:((ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ) :
  SemilinearAut K (ι → K) := {
    fst := z.unop.right.unop.fst
    snd :=
      letI inst := RingHomInvPair.of_ringEquiv z.unop.right.unop.fst;
      letI := inst.symm;
      { toFun := (z • .)
        map_add' := fun a b => by exact smul_add z a b
        map_smul' := map_smul_somethin z
        invFun := (z⁻¹ • .)
        left_inv := fun x => inv_smul_smul z x
        right_inv := fun x => smul_inv_smul z x}}

lemma fooooooooo1_map_one : (fooooooooo1 1 : SemilinearAut K (ι → K)) = 1 := by
  ext v : 1
  . rfl
  . calc
      (fooooooooo1 1 : SemilinearAut K (ι → K)).snd v
        = (1 : ((ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ) • v := rfl
      _ = v := by rw [one_smul]

lemma fooooooooo1_map_mul (a b : ((ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ):
    fooooooooo1 (a * b) = fooooooooo1 a * fooooooooo1 b := by
  ext v : 1
  . rfl
  . calc
      (fooooooooo1 (a * b)).snd v
        = (a * b) • v := rfl
      _ = a • b • v := by rw [mul_smul]
      _ = (fooooooooo1 a * fooooooooo1 b).snd v := rfl

def toSemilinearAut : ((ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ →* SemilinearAut K (ι → K) where
  toFun := fooooooooo1
  map_one' := fooooooooo1_map_one
  map_mul' := fooooooooo1_map_mul

lemma toSemilinearAut_def (z:((ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ) (v:ι → K) :
    toSemilinearAut z v = z • v := rfl

noncomputable abbrev b : Basis ι K (ι → K) := Pi.basisFun K ι


section

variable [Nonempty ι] [DecidableEq ι]
instance : FaithfulSMul (ι ≃ ι) (ι → K) where
  eq_of_smul_eq_smul{σ₁ σ₂} := fun heq => by
    ext i
    obtain heq := heq (b i)
    simp only [HSMul.hSMul, SMul.smul, DomMulAct.mk_inv, DomMulAct.symm_mk_inv,
      Equiv.symm_apply_apply] at heq
    rw [Function.funext_iff] at heq
    obtain heq := heq (σ₁ i)
    simp only [Equiv.Perm.inv_apply_self, Pi.basisFun_apply, LinearMap.stdBasis_apply',
      ↓reduceIte] at heq
    split at heq
    . rename_i h
      nth_rw 2 [h]
      simp only [Equiv.Perm.apply_inv_self]
    . simp only [one_ne_zero] at heq



instance : FaithfulSMul ((RingAut K) × (ι ≃ ι)) (ι → K) where
  eq_of_smul_eq_smul := by
    intro ⟨φ₁,σ₁⟩ ⟨φ₂,σ₂⟩ heq
    have : σ₁ = σ₂ := by
      ext i
      specialize heq (b i)
      simp only [Prod.smul_def'] at heq
      rw [Function.funext_iff] at heq
      specialize heq (σ₁ i)
      simp only [HSMul.hSMul, SMul.smul, DomMulAct.mk_inv, DomMulAct.symm_mk_inv,
        Equiv.symm_apply_apply, Equiv.Perm.inv_apply_self, Pi.basisFun_apply,
        LinearMap.stdBasis_apply', ↓reduceIte, map_one, RingHom.map_ite_one_zero] at heq
      split at heq
      . rename_i h
        nth_rw 2 [h]
        simp only [Equiv.Perm.apply_inv_self]
      . simp only [one_ne_zero] at heq
    rw [this] at heq ⊢
    simp only [Prod.mk.injEq, and_true]
    simp only [Prod.smul_def'] at heq
    exact eq_of_smul_eq_smul (fun (v:ι → K) => smul_inv_smul σ₂ v ▸ heq (σ₂⁻¹ • v))

instance : FaithfulSMul (((ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ) (ι → K) where
  eq_of_smul_eq_smul := by
    intro x y h
    simp only [semiprod_mulact_apply, Prod.smul_def'] at h
    apply MulOpposite.unop_injective
    generalize x.unop = x' at *
    generalize y.unop = y' at *
    obtain ⟨d₁,xr'⟩ := x'
    obtain ⟨d₂,yr'⟩ := y'
    rw [← MulOpposite.op_unop xr',← MulOpposite.op_unop yr']
    generalize xr'.unop = xr at *
    generalize yr'.unop = yr at *
    obtain ⟨φ₁,σ₁⟩ := xr
    obtain ⟨φ₂,σ₂⟩ := yr
    simp only [] at h ⊢

    have hσ : σ₁ = σ₂ := by
      ext i : 1
      specialize h (b i)
      simp only [HSMul.hSMul, SMul.smul, DomMulAct.mk_inv, DomMulAct.symm_mk_inv,
        Equiv.symm_apply_apply, Pi.basisFun_apply, LinearMap.stdBasis_apply', mul_ite, mul_one,
        mul_zero] at h
      rw [Function.funext_iff] at h
      specialize h (σ₁ i)
      simp only [Equiv.Perm.inv_apply_self, ↓reduceIte] at h
      split at h
      . rename_i hperm
        nth_rw 2 [hperm]
        simp only [Equiv.Perm.apply_inv_self]
      . simp only [map_zero, AddEquivClass.map_eq_zero_iff, Units.ne_zero] at h
    simp_rw [hσ] at h ⊢
    have hd : d₁ = d₂ := by
      ext i : 1
      specialize h (d₁⁻¹ • b i)
      simp only [smul_inv_smul] at h
      rw [Function.funext_iff] at h
      specialize h (σ₂ i)
      simp only [Pi.basisFun_apply, Pi.smul_apply, RingAut.smul_def] at h
      simp only [HSMul.hSMul, SMul.smul, DomMulAct.mk_inv, DomMulAct.symm_mk_inv,
        Equiv.symm_apply_apply, Equiv.Perm.inv_apply_self, LinearMap.stdBasis_apply', ↓reduceIte,
        map_one, Pi.inv_apply, Units.val_inv_eq_inv_val, mul_one, map_mul, map_inv₀] at h
      suffices hsuf : φ₂ (d₁ i) = φ₂ (d₂ i) by
        simp only [EmbeddingLike.apply_eq_iff_eq] at hsuf
        ext ; exact hsuf
      rw [← one_mul (φ₂ (d₁ i))]
      rw [h]
      simp only [ne_eq, AddEquivClass.map_eq_zero_iff, Units.ne_zero, not_false_eq_true,
        inv_mul_cancel_right₀]
    rw [hd] at h ⊢
    congr
    suffices hsuf : ∀ (a : ι → K), φ₁ • a = φ₂ • a from
      FaithfulSMul.eq_of_smul_eq_smul hsuf
    intro v
    specialize h ( d₂⁻¹ • σ₂⁻¹ • v)
    simp only [smul_inv_smul] at h
    exact h

end

lemma toSemilinearAut.inj [Nonempty ι] [DecidableEq ι] :
    Function.Injective (@toSemilinearAut ι K _) := by
  intro x y heq
  rw [SemilinearAut.ext_iff'] at heq
  obtain heq' : ∀ m, x • m = y • m := heq
  apply eq_of_smul_eq_smul heq


variable [Fintype K] [DecidableEq K] [DecidableEq ι] (f:SemilinearCodeAut K trivdist hdist s)

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

lemma ringaut_map_hdist {x:ι → K} (φ : RingAut K) : addGNorm hdist x = addGNorm hdist (φ • x) := by
  simp_rw [addGNorm]
  simp only [hammingENatdist_eq_cast_hammingDist, hammingDist_zero_right, Nat.cast_inj]
  simp_rw [hammingNorm]
  congr
  simp only [ne_eq, Pi.smul_apply, RingAut.smul_def, AddEquivClass.map_eq_zero_iff]


abbrev typeof {α:Type*} (_:α) := α

lemma map_index_to_stuff (i:ι): ∃! (c:ι × Kˣ), (f (b i)) = f.fst • (c.2 • b c.1) := by
  have hz₂ : addGNorm hdist (f (b i)) = 1 := by
    letI nempty: Nonempty ι := ⟨i⟩
    rw [← (@basis_vec_norm_one ι K) i]
    letI cls : SemilinearCodeEquivClass (typeof f.snd) (f.fst : K →+* K) trivdist hdist s hdist s :=
      inferInstance
    letI := cls.toCodeEquivClass.toGIsometryEquivClass
    exact GIsometry.map_norm _ _

  obtain hz := norm_one_basis_mul.mp (((@ringaut_map_hdist ι) f.fst⁻¹) ▸  hz₂)
  refine (exists_unique_congr ?_).mp hz
  simp only [Prod.forall]
  intro j x
  exact inv_smul_eq_iff

noncomputable def extract_perm' (i:ι) : ι := (map_index_to_stuff f i).exists.choose.1

noncomputable def extract_diag (i:ι) : Kˣ := (map_index_to_stuff f i).exists.choose.2

lemma extract_gives_stuff' (i:ι) : f (b i) = f.fst • (extract_diag f i • b (extract_perm' f i)) := by
  exact (map_index_to_stuff f i).exists.choose_spec

lemma extract_gives_stuff'' (i:ι) : f (b i) = (f.fst • extract_diag f i) • b (extract_perm' f i) := by
  rw [extract_gives_stuff' f i]
  ext j
  simp_rw [HSMul.hSMul,SMul.smul]
  simp only [Pi.basisFun_apply, Pi.smul_apply, LinearMap.stdBasis_apply', smul_eq_mul, mul_ite,
    mul_one, mul_zero, smul_ite, RingAut.smul_def, smul_zero]

lemma extract_gives_unique {i:ι} (j:ι) (k:Kˣ) :
  f (b i) = f.fst • k • b j → (j,k) = (extract_perm' f i, extract_diag f i) := by
  intro h
  apply (map_index_to_stuff f i).unique
  . exact h
  . exact extract_gives_stuff' f i


lemma extract_gives_unique_perm' (i:ι) (j:ι) (k:Kˣ) :
    f (b i) = f.fst • k • b j → (j = extract_perm' f i) := by
  intro h
  have hz := (extract_gives_unique f j k h)
  simp only [Prod.mk.injEq] at hz
  exact hz.left

lemma extract_gives_unique_diag (i:ι) (j:ι) (k:Kˣ) : f (b i) = f.fst • k • b j → (k = extract_diag f i) := by
  intro h
  have hz := (extract_gives_unique f j k h)
  simp only [Prod.mk.injEq] at hz
  exact hz.right


@[simp]
lemma ringaut_basis_eq_self (φ : RingAut K) (i:ι) : φ • (b i : ι → K) = b i := by
  ext j
  simp only [Pi.basisFun_apply, Pi.smul_apply, LinearMap.stdBasis_apply', smul_ite, smul_one,
    smul_zero]




lemma ringaut_smul_unit_distrib (σ : RingAut K) (d:Kˣ) (f:ι → K) :
    σ • (d • f) = (σ • d) • (σ • f) := by
  ext i
  simp only [Pi.smul_apply, RingAut.smul_def]
  calc
    σ (d • f i)
      = σ (d * f i) := by rfl
    _ = σ d * σ (f i) := by rw [σ.map_mul]


lemma ringaut_smul_unit_diag_distrib (σ : RingAut K) (d:ι → Kˣ) (f: ι → K) :
  σ • (d • f) = (σ • d) • (σ • f) := by
  ext i
  simp only [Pi.smul_apply, Pi.smul_apply', RingAut.smul_def]
  calc
    σ (d i * f i)
      = σ (d i) * σ (f i) := by rw [σ.map_mul]

lemma extract_perm_left_inv (i:ι): extract_perm' f⁻¹ (extract_perm' f i) = i := by
  apply (extract_gives_unique_perm' f⁻¹ _ i (f.fst • (extract_diag f i)⁻¹) _).symm
  symm
  calc
    f⁻¹.fst • (f.fst • (extract_diag f i)⁻¹) • b i
      = (f⁻¹.fst • (f.fst • (extract_diag f i)⁻¹)) • b i := by
        rw [ringaut_smul_unit_distrib,ringaut_basis_eq_self]
    _ = f.fst.symm (f.fst (extract_diag f i)⁻¹) • b i := by
      simp_rw [HSMul.hSMul,SMul.smul]
      rw [Units.val_inv_eq_inv_val, RingAut.smul_def,RingAut.smul_def]
      rfl
    _ = (extract_diag f i)⁻¹ • b i := by
      rw [RingEquiv.symm_apply_apply]
      rw [← Units.val_inv_eq_inv_val]
      rfl
    _ = (extract_diag f i)⁻¹ • (f.snd.symm (f.snd (b i))):= by
      nth_rw 1 [← f.snd.left_inv (b i)]
      rfl
    _ = (extract_diag f i)⁻¹ •
      (f.snd.symm ((f.fst • (extract_diag f i)) • (b (extract_perm' f i)))) := by
        rw [extract_gives_stuff'' f i]
    _ = (extract_diag f i)⁻¹ •
      (f.snd.symm ((f.fst • (extract_diag f i) : K) • (b (extract_perm' f i)))) := by rfl
    _ = (extract_diag f i)⁻¹ •
      (f.fst.symm (f.fst • (extract_diag f i) : K) • f.snd.symm (b (extract_perm' f i))) := by
        rw [map_smulₛₗ f.snd.symm]
        rfl
    _ = (extract_diag f i)⁻¹ •
      (f.fst.symm (f.fst (extract_diag f i)) • f.snd.symm (b (extract_perm' f i))) := by
        rfl
    _ = (extract_diag f i)⁻¹ •
      ((extract_diag f i) • f.snd.symm (b (extract_perm' f i))) := by
        rw [RingEquiv.symm_apply_apply]
        rfl
    _ = (extract_diag f i)⁻¹ •
      ((extract_diag f i) • (f⁻¹.snd (b (extract_perm' f i)))) := by
        rfl
    _ = f⁻¹.snd (b (extract_perm' f i)) := by
      rw [inv_smul_smul]

noncomputable def extract_perm : ι ≃ ι where
  toFun := extract_perm' f
  invFun := extract_perm' f⁻¹
  left_inv := by
    exact extract_perm_left_inv f
  right_inv := by
    intro i
    calc
      extract_perm' f (extract_perm' f⁻¹ i)
        = extract_perm' (f⁻¹)⁻¹ (extract_perm' f⁻¹ i) := by rw [inv_inv]
      _ = i := extract_perm_left_inv f⁻¹ i

lemma extract_perm_is_perm': extract_perm' f = (extract_perm f) := by rfl

lemma help_proof_1 (x y : SemilinearCodeAut K trivdist hdist s) (i:ι):
  (x * y).snd (b i) = (x.fst * y.fst) •
    (extract_diag y i * (y.fst⁻¹ • extract_diag x ((extract_perm y) i))) •
    b ((extract_perm x) ((extract_perm y) i)) := by
  calc
    x.snd (y.snd (b i))
      = x.snd ((y.fst • extract_diag y i) • b ((extract_perm y) i)) := by
        rw [extract_gives_stuff'',extract_perm_is_perm']
    _ = x.snd ((y.fst • extract_diag y i : K) • b ((extract_perm y) i)) := by rfl
    _ = x.fst (y.fst • extract_diag y i : K) • x.snd (b ((extract_perm y) i)) := by
        exact x.snd.map_smulₛₗ (y.fst • extract_diag y i) (b ((extract_perm y) i))
    _ = (x.fst • y.fst • extract_diag y i) • x.snd (b ((extract_perm y) i)) := by rfl
    _ = (x.fst • y.fst • extract_diag y i) • (x.fst • extract_diag x ((extract_perm y) i)) •
      b ((extract_perm x) ((extract_perm y) i)) := by
        rw [extract_gives_stuff'',extract_perm_is_perm']
    _ = ((x.fst • y.fst • extract_diag y i) * (x.fst • extract_diag x ((extract_perm y) i))) •
      b ((extract_perm x) ((extract_perm y) i)) := by
        rw [mul_smul]
    _ = (x.fst • ((y.fst • extract_diag y i) * (extract_diag x ((extract_perm y) i)))) •
      b ((extract_perm x) ((extract_perm y) i)) := by
        rw [smul_mul']
    _ = (x.fst • y.fst • (extract_diag y i * (y.fst⁻¹ • extract_diag x ((extract_perm y) i)))) •
      b ((extract_perm x) ((extract_perm y) i)) := by
        rw [smul_mul' y.fst,smul_inv_smul]
    _ = ((x.fst * y.fst) • (extract_diag y i * (y.fst⁻¹ • extract_diag x ((extract_perm y) i)))) •
      b ((extract_perm x) ((extract_perm y) i)) := by
        rw [mul_smul]
    _ = (x.fst * y.fst) • (extract_diag y i * (y.fst⁻¹ • extract_diag x ((extract_perm y) i))) •
      b ((extract_perm x) ((extract_perm y) i)) := by
        rw [SMulDistribSMulClass.smul_distrib,ringaut_basis_eq_self]


lemma extract_perm_map_one : extract_perm (1:SemilinearCodeAut K trivdist hdist s) = 1 := by
  ext i
  simp only [Equiv.Perm.coe_one, id_eq]
  symm
  apply extract_gives_unique_perm' (1 : SemilinearCodeAut K trivdist hdist s) i i 1
  simp only [Pi.basisFun_apply, SemilinearCodeAut.coe_one, id_eq, one_smul]
  rfl

lemma extract_perm_map_mul (g:SemilinearCodeAut K trivdist hdist s) :
    extract_perm (f * g) = extract_perm f * extract_perm g := by
  ext i
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  symm
  apply extract_gives_unique_perm'
  exact help_proof_1 f g i

-- i didn't realise immediately, but it's nice that this is reflexively true ;)
lemma extract_perm_map_inv : extract_perm f⁻¹ = (extract_perm f)⁻¹ := by
  rfl

lemma extract_diag_map_one : extract_diag (1:SemilinearCodeAut K trivdist hdist s) = 1 := by
  ext i
  simp only [Pi.one_apply, Units.val_one, Units.val_eq_one]
  symm
  apply extract_gives_unique_diag (1:SemilinearCodeAut K trivdist hdist s) i i
  simp only [Pi.basisFun_apply, SemilinearCodeAut.coe_one, id_eq, one_smul]
  rfl

lemma extract_diag_map_mul (g:SemilinearCodeAut K trivdist hdist s):
    extract_diag (f * g) = extract_diag g *
    (invsmulMulHom (MulOpposite.op (g.fst, extract_perm g))) (extract_diag f) := by
  ext i : 1
  symm
  apply extract_gives_unique_diag (f * g) i
  exact help_proof_1 f g i


lemma extract_diag_map_inv : extract_diag f⁻¹ = ((invsmulMulHom (MulOpposite.op (f⁻¹.fst, extract_perm f⁻¹))) (extract_diag f))⁻¹:= by
  symm
  calc
    ((invsmulMulHom (MulOpposite.op (f⁻¹.fst, extract_perm f⁻¹))) (extract_diag f))⁻¹
      = 1 * ((invsmulMulHom (MulOpposite.op (f⁻¹.fst, extract_perm f⁻¹))) (extract_diag f))⁻¹ := by
        rw [one_mul]
    _ = extract_diag 1 * ((invsmulMulHom (MulOpposite.op (f⁻¹.fst, extract_perm f⁻¹))) (extract_diag f))⁻¹ := by
        rw [(@extract_diag_map_one ι K _ _ s)]
    _ = extract_diag (f * f⁻¹) * ((invsmulMulHom (MulOpposite.op (f⁻¹.fst, extract_perm f⁻¹))) (extract_diag f))⁻¹ := by
        rw [mul_inv_self f]
    _ = extract_diag f⁻¹ * (invsmulMulHom (MulOpposite.op (f⁻¹.fst, extract_perm f⁻¹))) (extract_diag f)
      * ((invsmulMulHom (MulOpposite.op (f⁻¹.fst, extract_perm f⁻¹))) (extract_diag f))⁻¹ := by
        rw [extract_diag_map_mul]
    _ = extract_diag f⁻¹ * 1 := by
        rw [mul_assoc,mul_inv_self]
    _ = extract_diag f⁻¹ := by rw [mul_one]

lemma extract_diag_map_inv' : extract_diag f⁻¹ = (f.fst,extract_perm f) • (extract_diag f)⁻¹ := calc
  extract_diag f⁻¹
    = ((invsmulMulHom (MulOpposite.op (f⁻¹.fst, extract_perm f⁻¹))) (extract_diag f))⁻¹ := by
      rw [extract_diag_map_inv]
  _ = ((invsmulMulHom (MulOpposite.op (f⁻¹.fst,extract_perm f⁻¹))) (extract_diag f)⁻¹) := by
      rw [map_inv]
  _ = (f⁻¹.fst,extract_perm f⁻¹)⁻¹ • (extract_diag f)⁻¹ := by rfl
  _ = (f.fst,extract_perm f) • (extract_diag f)⁻¹ := by
    rw [extract_perm_map_inv]
    rfl


lemma extract_gives_stuff (i:ι) :
    f (b i) = f.fst • (extract_perm f • (extract_diag f • (b i:ι → K))) := by
  ext j
  calc
    f (b i) j = (f.fst • (extract_diag f i) • (b (extract_perm f i): ι → K)) j:= by
      rw [extract_gives_stuff' f i, extract_perm_is_perm']
    _ = ((f.fst • (extract_diag f i)) • (b (extract_perm f i)) : ι → K) j := by
      rw [ringaut_smul_unit_distrib, ringaut_basis_eq_self]
    _ = (f.fst • extract_diag f ((extract_perm f).symm j)) • b i ((extract_perm f).symm j) := by
      simp only [Pi.smul_apply]
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
    _ = (f.fst • (extract_diag f) • (b i:ι → K)) ((extract_perm f).symm j) := by
      rw [ringaut_smul_unit_diag_distrib, ringaut_basis_eq_self]
      rw [Pi.smul_apply']
      rfl
    _ = (f.fst • (extract_perm f • (extract_diag f • (b i:ι → K)))) j := by rfl

instance : SMulCommClass (ι ≃ ι) K (ι → K) where
  smul_comm := fun _ _ _ ↦ rfl

instance : SMulCommClass (ι → Kˣ) K (ι → K) where
  smul_comm := by exact fun m n a ↦ (smul_comm n m a).symm


lemma mulsemiring_apply_eq_apply :
  (MulSemiringAction.toRingEquiv (RingAut K) K f.fst) = f.fst := by
  ext m
  simp only [MulSemiringAction.toRingEquiv_apply, RingAut.smul_def]

lemma extract_gives_stuff_strong (x:ι → K) : f x = f.fst • (extract_perm f • (extract_diag f • x)) := by
  letI inst := RingHomInvPair.of_ringEquiv (MulSemiringAction.toRingEquiv (RingAut K) K f.fst)
  letI := inst.symm
  suffices hsuf :
      ((DistribMulAction.toLinearEquiv K (ι → K) (extract_diag f)).trans
      (DistribMulAction.toLinearEquiv K (ι → K) (extract_perm f))).trans
      (mulsemiring_apply_eq_apply f ▸ DistribMulAction.toSemilinearAut K (ι → K) (f.fst)) = ↑f.snd by
    rw [LinearEquiv.ext_iff] at hsuf
    simp only [LinearEquiv.trans_apply, DistribMulAction.toLinearEquiv_apply,
      SemilinearCodeEquiv.coe_toLinearEquiv] at hsuf
    specialize hsuf x
    rw [← hsuf]
    rfl
  apply b.ext'
  simp only [LinearEquiv.trans_apply, DistribMulAction.toLinearEquiv_apply,
    SemilinearCodeEquiv.coe_toLinearEquiv]
  exact fun i ↦ (extract_gives_stuff f i).symm

noncomputable def toSemidirectProd' (f:SemilinearCodeAut K trivdist hdist s) :
    ((ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ :=
  MulOpposite.op ⟨extract_diag f,MulOpposite.op (f.fst,extract_perm f)⟩

@[simp]
lemma toModuleAut_apply_eq_smul
    (f:SemilinearCodeAut K trivdist hdist s) (x: ι → K):
    toSemilinearAut (toSemidirectProd' f) x = toSemidirectProd' f • x := by rfl

@[simp]
lemma toModuleAut_toSemiProd_eq_coe (f:SemilinearCodeAut K trivdist hdist s) :
    toSemilinearAut (toSemidirectProd' f) = ⟨f.fst,f.snd⟩ := by
  ext v : 1
  . rfl
  simp only [--toModuleAut_apply_eq_smul, semiprod_mulact_apply, Prod.smul_def',
    SemilinearCodeEquiv.coe_toLinearEquiv]
  suffices hsuf :
      (toSemilinearAut (toSemidirectProd' f)).snd = (f.snd:(ι → K) ≃ₛₗ[(f.fst : K →+* K)] (ι → K)) by
    rw [hsuf,SemilinearCodeEquiv.coe_toLinearEquiv]
  apply b.ext'
  intro i
  rw [SemilinearCodeEquiv.coe_toLinearEquiv]
  rw [extract_gives_stuff]
  rfl


@[simp]
lemma coe_toSemidirectProd'
    (f:SemilinearCodeAut K trivdist hdist s) :
    ∀ (x:ι → K), (toSemidirectProd' f) • x = f x := by
  intro x
  rw [← toModuleAut_apply_eq_smul]
  rw [toModuleAut_toSemiProd_eq_coe]
  rfl

set_option maxHeartbeats 400000
lemma toSemidirectProd'_inj : Function.Injective (toSemidirectProd': SemilinearCodeAut K trivdist hdist s →
    ((ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ) := fun x y heq => by
  rw [toSemidirectProd',toSemidirectProd',MulOpposite.op_inj] at heq
  rw [SemidirectProduct.ext_iff] at heq
  simp only [MulOpposite.op_inj, Prod.mk.injEq] at heq
  obtain ⟨hdiag,hfst,hperm⟩ := heq
  ext v : 1
  . rw [hfst]
  suffices hsuf : (x.snd : (ι → K) ≃ₛₗ[(x.fst : K →+* K)] (ι → K)) v = (y.snd : (ι → K) ≃ₛₗ[(y.fst : K →+* K)] (ι → K)) v by
    simp only [SemilinearCodeEquiv.coe_toLinearEquiv] at hsuf
    exact hsuf
  refine Submodule.span_induction (b.mem_span v) ?base ?zero ?add ?smul
  -- i would rather use b.ext', but for that i need `stubst hfst` to work here, which it doesn't.
  case base =>
    simp only [mem_range,
    forall_exists_index, forall_apply_eq_imp_iff]
    intro i
    simp only [SemilinearCodeEquiv.coe_toLinearEquiv]
    rw [extract_gives_stuff, extract_gives_stuff]
    rw [hdiag,hfst,hperm]
  case zero => rw [map_zero,map_zero]
  case add =>
    intro a b ha hb
    rw [map_add,map_add,ha,hb]
  case smul =>
    intro k v hv
    rw [map_smulₛₗ,map_smulₛₗ,hv]
    rw [RingEquiv.coe_toRingHom,RingEquiv.coe_toRingHom,hfst]

lemma toSemidirectProd'_map_one :
    toSemidirectProd' (1:SemilinearCodeAut K trivdist hdist s) = 1 := by
  apply MulOpposite.unop_injective
  simp_rw [toSemidirectProd']
  simp only [MulOpposite.op_mul, MulOpposite.unop_mul,
    MulOpposite.unop_op, MulOpposite.unop_one]
  rw [extract_diag_map_one,extract_perm_map_one]
  rfl


lemma toSemidirectProd'_map_mul (x y : SemilinearCodeAut K trivdist hdist s) :
    toSemidirectProd' (x * y) = toSemidirectProd' x * toSemidirectProd' y := by
  apply MulOpposite.unop_injective
  simp_rw [toSemidirectProd']
  simp only [MulOpposite.op_mul, MulOpposite.unop_mul,
    MulOpposite.unop_op]
  nth_rw 4 [HMul.hMul,instHMul]
  simp_rw [Mul.mul]
  ext : 1
  . simp only
    exact extract_diag_map_mul x y
  . simp only
    congr
    simp only [RingEquiv.coe_ringHom_trans, MulOpposite.unop_op]
    exact extract_perm_map_mul x y

noncomputable def toSemidirectProd :
    (SemilinearCodeAut K trivdist hdist s) →* ((ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ where
  toFun := toSemidirectProd'
  map_one' := toSemidirectProd'_map_one
  map_mul' := toSemidirectProd'_map_mul


def lift_toLinearCodeAut
    (c:((ι → Kˣ) ⋊[invsmulMulHom] ((RingAut K) × (ι ≃ ι))ᵐᵒᵖ)ᵐᵒᵖ) (hc: ∀ x, x ∈ s ↔ c • x ∈ s) :
    SemilinearCodeAut K trivdist hdist s :=
    {
      fst := c.unop.right.unop.fst
      snd :=(
        letI inst := RingHomInvPair.of_ringEquiv c.unop.right.unop.fst;
        letI := inst.symm;
        {
          (toSemilinearAut c).snd with
          map_code := fun x => (hc x).mp
          invMap_code := fun x => (hc x).mpr
          map_dist := fun x y => by
            rw [addDist_eq,addDist_eq]
            simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
            simp_rw [addGNorm,hdist]
            simp only [hammingENatdist_eq_cast_hammingDist, hammingDist_zero_right, Nat.cast_inj]
            obtain hsub :=(toSemilinearAut c).snd.map_sub x y
            simp only [LinearEquiv.coe_coe] at hsub
            rw [← hsub]
            simp_rw [hammingNorm]
            simp only [Pi.sub_apply, Finset.filter_congr_decidable]
            suffices hsuf :
                Finset.filter (fun x_1 ↦ (x - y) x_1 ≠ 0) Finset.univ ≃
                Finset.filter (fun x_1 ↦ (c • (x - y)) x_1 ≠ 0) Finset.univ by
              exact Finset.card_eq_of_equiv hsuf
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            refine ⟨
              fun ⟨i,hi⟩ => ⟨c.unop.right.unop.snd i,?tofunProp⟩,
              fun ⟨i,hi⟩ => ⟨c.unop.right.unop.snd⁻¹ i,?invfunProp⟩,
              ?leftinv,
              ?rightinv⟩
            case tofunProp =>
              simp only [HSMul.hSMul, SMul.smul, DomMulAct.mk_inv, DomMulAct.symm_mk_inv,
                Equiv.symm_apply_apply, Equiv.Perm.inv_apply_self, map_mul,
                ne_eq, mul_eq_zero, AddEquivClass.map_eq_zero_iff, Units.ne_zero, false_or]
              exact hi
            case invfunProp =>
              simp only [HSMul.hSMul, SMul.smul, Inv.inv, Equiv.symm_apply_apply,
                map_mul, ne_eq, mul_eq_zero, AddEquivClass.map_eq_zero_iff, Units.ne_zero,
                false_or] at hi ⊢
              exact hi
            all_goals (intro i; simp)
      })
    }
-- #synth CommGroup (ι → Kˣ)
end linear
