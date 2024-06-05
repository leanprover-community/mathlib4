import Mathlib.InformationTheory.Code.Basic
import Mathlib.InformationTheory.Code.Aut

import Mathlib.InformationTheory.Code.Linear.SemiEquiv
import Mathlib.InformationTheory.Code.Linear.SemilinearAut
import Mathlib.InformationTheory.Code.Faithful


open Code
open LinearCode
open CodeAut
variable {γ K:Type*}[Field K] {σ: RingAut K} {Tₖ M Tₘ:Type*} {gdistₖ: Tₖ} {gdistₘ:Tₘ}
variable [Semiring γ] [CompleteLinearOrder γ]
  [CovariantClass γ γ (.+.) (.≤.)] [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ]


variable  [AddCommMonoid M]
variable? [AddGNorm K γ gdistₖ] => [AddGNorm K γ gdistₖ]
variable? [AddGNorm M γ gdistₘ] => [FunLike Tₘ M (M → γ)] [GPseudoMetricClass Tₘ M γ]
  [AddGNorm M γ gdistₘ]

variable--? {s : Submodule K M} =>
  [Module K M] {s : Submodule K M}

variable--? [_LinearCode γ K gdistₖ gdistₘ sₘ] =>
  [Set.GMetric.IsDelone gdistₘ ↑s] [Nontrivial γ]
  [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ] [StrictModuleGNorm K K gdistₖ gdistₖ]
  [StrictModuleGNorm K M gdistₖ gdistₘ]

section
variable (K gdistₖ gdistₘ s)

def SemilinearCodeAut [_LinearCode γ K gdistₖ gdistₘ s] : Type _ :=
  (σ : RingAut K) × (
    letI inst := RingHomInvPair.of_ringEquiv σ;
    letI := inst.symm;
    SemilinearCodeEquiv σ gdistₖ gdistₘ s gdistₘ s)

abbrev LinearCodeAut [_LinearCode γ K gdistₖ gdistₘ s] : Type _ :=
  LinearCodeEquiv K gdistₖ gdistₘ s gdistₘ s
end

namespace SemilinearCodeAut

@[ext]
protected lemma ext ⦃x y : SemilinearCodeAut K gdistₖ gdistₘ s⦄
    (h₁ : ∀ r, x.fst r = y.fst r) (h₂ : ∀ m, x.snd m = y.snd m) : x = y := by
  cases x; cases y
  rw [← DFunLike.ext_iff] at h₁
  subst h₁
  simp_all only [← DFunLike.ext_iff]



def toSemilinearAut : SemilinearCodeAut K gdistₖ gdistₘ s → SemilinearAut K M := fun x => ⟨x.fst,
  letI inst := RingHomInvPair.of_ringEquiv x.fst;
  letI := inst.symm
  x.snd.toLinearEquiv⟩

instance : CoeFun (SemilinearCodeAut K gdistₖ gdistₘ s)
    (fun _ => M → M) where
  coe := fun f => f.snd

instance instRingHomInvPair (e : SemilinearCodeAut K gdistₖ gdistₘ s) :
  RingHomInvPair (e.fst: K →+* K) e.fst.symm := RingHomInvPair.of_ringEquiv e.fst

instance (e: SemilinearCodeAut K gdistₖ gdistₘ s) : RingHomInvPair (e.fst.symm : K →+* K) e.fst :=
  instRingHomInvPair e |>.symm

instance trip1 (e₁ e₂ : SemilinearCodeAut K gdistₖ gdistₘ s) :
  RingHomCompTriple (e₁.fst : K →+* K) (e₂.fst : K →+* K) (e₁.fst.trans e₂.fst) :=
  ⟨by rfl⟩

instance trip2 (e₁ e₂ : SemilinearCodeAut K gdistₖ gdistₘ s) :
  RingHomCompTriple (e₁.fst.symm : K →+* K) (e₂.fst.symm : K →+* K) (e₂.fst.trans e₁.fst).symm :=
  ⟨by rfl⟩

instance invpair' (e₁ e₂ : SemilinearCodeAut K gdistₖ gdistₘ s) :
    RingHomInvPair (e₁.fst.trans e₂.fst : K →+* K) (e₁.fst.trans e₂.fst).symm :=
  RingHomInvPair.of_ringEquiv (e₁.fst.trans e₂.fst)

instance (e₁ e₂ : SemilinearCodeAut K gdistₖ gdistₘ s) :
    RingHomInvPair ((e₁.fst.trans e₂.fst).symm : K →+* K) (e₁.fst.trans e₂.fst) :=
  invpair' e₁ e₂ |>.symm

protected def mk {σ σ' : K →+* K}
    [i1:RingHomInvPair σ σ'] [i2:RingHomInvPair σ' σ]
    (e : SemilinearCodeEquiv σ gdistₖ gdistₘ s gdistₘ s) :
    SemilinearCodeAut K gdistₖ gdistₘ s :=
  ⟨RingEquiv.ofHomInv σ σ' i2.comp_eq₂ i1.comp_eq₂,e⟩

lemma toSemilinearAut.inj : Function.Injective
    (toSemilinearAut : SemilinearCodeAut K gdistₖ gdistₘ s → SemilinearAut K M) :=
  fun x y h => by
    obtain ⟨h₁,h₂⟩ := SemilinearAut.ext_iff.mp h
    simp_rw [toSemilinearAut] at h₁ h₂
    ext m
    . rw [h₁]
    . simp_rw [SemilinearCodeEquiv.toLinearEquiv_eq_coe,SemilinearCodeEquiv.coe_toLinearEquiv] at h₂
      rw [h₂]

-- #check SemilinearAut.ext'

lemma ringaut_eq_of_faithful [FaithfulSMul K M] ⦃f g : SemilinearCodeAut K gdistₖ gdistₘ s⦄
    (h:∀ x, f.snd x = g.snd x) : f.fst = g.fst := by
  suffices hsuf : f.toSemilinearAut = g.toSemilinearAut by
    rw [SemilinearAut.ext_iff] at hsuf
    rw [RingEquiv.ext_iff]
    exact hsuf.left
  apply SemilinearAut.ext'
  simp_rw [toSemilinearAut]
  simp only [SemilinearCodeEquiv.toLinearEquiv_eq_coe, SemilinearCodeEquiv.coe_toLinearEquiv]
  exact h

lemma ext' [FaithfulSMul K M] ⦃f g : SemilinearCodeAut K gdistₖ gdistₘ s⦄
    (h:∀ x, f.snd x = g.snd x) : f = g := by
  apply toSemilinearAut.inj
  apply SemilinearAut.ext'
  simp_rw [toSemilinearAut]
  simp only [SemilinearCodeEquiv.toLinearEquiv_eq_coe, SemilinearCodeEquiv.coe_toLinearEquiv]
  exact h

-- section

-- variable [Nontrivial M]
-- #synth Field K
-- #check (@instFaithfulVectorspace K M)
-- #synth FaithfulSMul K M

-- end


instance [FaithfulSMul K M] : EquivLike (SemilinearCodeAut K gdistₖ gdistₘ s) M M where
  coe := fun x => x.snd
  inv := fun x => x.snd.symm
  left_inv := fun x => x.snd.left_inv
  right_inv := fun x => x.snd.right_inv
  coe_injective' := fun x y h1 _ => by
    simp_all only
    apply ext'
    rw [h1]
    simp only [forall_const]

instance instMonoid [_LinearCode γ K gdistₖ gdistₘ s] : Monoid (SemilinearCodeAut K gdistₖ gdistₘ s) where
  mul := fun x y => ⟨y.fst.trans x.fst,
    letI trip1 : RingHomCompTriple (y.fst : K →+* K) (x.fst : K →+* K) (y.fst.trans x.fst : K →+* K) :=
      ⟨by simp only [RingEquiv.coe_ringHom_trans]⟩
    letI trip2 : RingHomCompTriple (x.fst.symm : K →+* K) (y.fst.symm : K →+* K)
        ((y.fst.trans x.fst).symm : K →+* K) := ⟨by rfl⟩
    letI pair3 := RingHomInvPair.of_ringEquiv (y.fst.trans x.fst)
    letI pair3' := pair3.symm;
    y.snd.trans x.snd⟩
  mul_assoc := fun a b c => rfl
  one := ⟨RingEquiv.refl K, SemilinearCodeEquiv.refl K gdistₖ gdistₘ s⟩
  one_mul := fun x => by
    simp_rw [HMul.hMul,OfNat.ofNat]
    ext : 1 <;> rfl
  mul_one := fun x => by
    simp_rw [HMul.hMul,OfNat.ofNat]
    ext : 1 <;> rfl

instance : Inv (SemilinearCodeAut K gdistₖ gdistₘ s) where
  inv := fun x => ⟨x.fst.symm,x.snd.symm⟩

instance instGroup [_LinearCode γ K gdistₖ gdistₘ s] : Group (SemilinearCodeAut K gdistₖ gdistₘ s) where
  mul_left_inv := by
    intro x
    simp_rw [HMul.hMul,Mul.mul,OfNat.ofNat,One.one]
    ext r
    . simp_rw [Inv.inv]
      simp only [RingEquiv.self_trans_symm, RingEquiv.refl_apply]
    . simp only [RingEquiv.coe_ringHom_trans, RingEquiv.coe_ringHom_refl, RingEquiv.symm_refl]
      rw [SemilinearCodeEquiv.trans_apply]
      simp_rw [Inv.inv]
      simp only [SemilinearCodeEquiv.symm_apply_apply, SemilinearCodeEquiv.refl_apply]

-- #synth Field K

instance instAddEquivClass [FaithfulSMul K M] [_LinearCode γ K gdistₖ gdistₘ s] :
  AddEquivClass (SemilinearCodeAut K gdistₖ gdistₘ s) M M where
    map_add := fun f => f.snd.map_add

@[simp]
theorem coe_mul (e₁ e₂ : SemilinearCodeAut K gdistₖ gdistₘ s) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : SemilinearCodeAut K gdistₖ gdistₘ s) = id :=
  rfl


@[simp]
lemma mk_apply {σ σ' : K →+* K}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : SemilinearCodeEquiv σ gdistₖ gdistₘ s gdistₘ s) (m:M) :
    SemilinearCodeAut.mk e m = e m := rfl


@[simp]
lemma mk_tosemilinear {σ σ' : K →+* K}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : SemilinearCodeEquiv σ gdistₖ gdistₘ s gdistₘ s) :
    toSemilinearAut (SemilinearCodeAut.mk e)  = (@SemilinearAut.mk K M _ _ _ σ σ') e := rfl

@[simp]
theorem mul_mk
    {σ₁₂ σ₂₁: K →+* K} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (f: SemilinearCodeEquiv σ₁₂ gdistₖ gdistₘ s gdistₘ s)
    {σ₂₃ σ₃₂: K →+* K} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
    (g: SemilinearCodeEquiv σ₂₃ gdistₖ gdistₘ s gdistₘ s)
    {σ₁₃ σ₃₁ : K →+* K} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
    [t1:RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]:
    SemilinearCodeAut.mk g * SemilinearCodeAut.mk f = SemilinearCodeAut.mk (f.trans g) := by
  ext x
  . exact t1.comp_apply
  . exact rfl

@[simp]
theorem inv_mk {σ σ' : K →+* K}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ]
    (e : SemilinearCodeEquiv σ gdistₖ gdistₘ s gdistₘ s):
    (SemilinearCodeAut.mk e)⁻¹ = SemilinearCodeAut.mk e.symm := rfl

@[simp]
theorem div_mk {σ₁₂ σ₂₁: K →+* K} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂]
    (f: SemilinearCodeEquiv σ₂₁ gdistₖ gdistₘ s gdistₘ s)
    {σ₂₃ σ₃₂: K →+* K} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃]
    (g: SemilinearCodeEquiv σ₂₃ gdistₖ gdistₘ s gdistₘ s)
    {σ₁₃ σ₃₁ : K →+* K} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
    [t1:RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁] :
    SemilinearCodeAut.mk g / SemilinearCodeAut.mk f = SemilinearCodeAut.mk (f.symm.trans g) := by
  ext x
  . simp_rw [HDiv.hDiv,Div.div, SemilinearCodeAut.mk]
    simp only [RingEquiv.coe_trans, Function.comp_apply, RingEquiv.ofHomInv_symm_apply,
      RingEquiv.ofHomInv_apply]
    exact t1.comp_apply
  . exact rfl

instance applyDistribMulAction :
    DistribMulAction (SemilinearCodeAut K gdistₖ gdistₘ s) M where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := fun f => (f.snd : M →+ M).map_zero'
  smul_add := fun f => (f.snd : M →+ M).map_add'

@[simp]
protected theorem smul_def (f : SemilinearCodeAut K gdistₖ gdistₘ s) (a : M) :
  f • a = f a := rfl

instance apply_faithfulSMul [FaithfulSMul K M] : FaithfulSMul (SemilinearCodeAut K gdistₖ gdistₘ s) M :=
  ⟨fun h => by
    simp only [SemilinearCodeAut.smul_def] at h
    exact ext' h⟩

@[simp]
theorem tmp (e:SemilinearCodeAut K gdistₖ gdistₘ s) (m: M): e.snd.symm m = e⁻¹.snd m := rfl



@[simp]
lemma mk_apply' (σ : RingAut K) (e :
    letI inst := RingHomInvPair.of_ringEquiv σ;
    letI := inst.symm;
    SemilinearCodeEquiv σ gdistₖ gdistₘ s gdistₘ s) (m:M):
  (⟨σ,e⟩ : SemilinearCodeAut K gdistₖ gdistₘ s).snd m = ⇑e m := rfl


protected lemma map_dist (f : SemilinearCodeAut K gdistₖ gdistₘ s) (a b: M) :
    gdistₘ (f a) (f b) = gdistₘ a b := by
  exact (f.snd.map_dist a b).symm

protected lemma map_add (f : SemilinearCodeAut K gdistₖ gdistₘ s) (a b : M) :
    f (a + b) = f a + f b := (f.snd.map_add a b)

protected lemma map_zero (f : SemilinearCodeAut K gdistₖ gdistₘ s) :
  f 0 = 0 := f.snd.map_zero

protected lemma map_smulₛₗ (f : SemilinearCodeAut K gdistₖ gdistₘ s) (k:K) (m : M) :
    f (k • m) = f.fst k • f m := f.snd.map_smul' k m

protected lemma map_addGNorm (f : SemilinearCodeAut K gdistₖ gdistₘ s) (a: M) :
    addGNorm gdistₘ (f a) = addGNorm gdistₘ a := by
  dsimp [addGNorm]
  nth_rw 1 [← map_zero f.snd]
  exact f.map_dist a 0

protected lemma map_code (f : SemilinearCodeAut K gdistₖ gdistₘ s) {a : M} (ha : a ∈ s):
  f a ∈ s := f.snd.map_code a ha

protected lemma invMap_code (f : SemilinearCodeAut K gdistₖ gdistₘ s) {a : M} (ha : f a ∈ s) :
  a ∈ s := f.snd.invMap_code a ha

end SemilinearCodeAut
namespace LinearCodeAut


end LinearCodeAut
