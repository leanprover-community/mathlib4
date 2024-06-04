import Mathlib.Algebra.Module.Equiv
import Mathlib.GroupTheory.QuotientGroup



def SemilinearAut (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]: Type _ :=
    (σ:RingAut R) × (
      letI inst := RingHomInvPair.of_ringEquiv σ;
      letI := inst.symm;
      M ≃ₛₗ[(σ : R →+* R)] M)

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

namespace SemilinearAut

instance : CoeFun (SemilinearAut R M)
    (fun _ => M → M) where
  coe := fun f => f.snd

@[ext]
protected lemma ext
  ⦃f g: SemilinearAut R M⦄ (h₁: ∀ r, f.fst r = g.fst r) (h₂: ∀ x, f.snd x= g.snd x): f = g := by
  cases f; cases g;
  rw [← DFunLike.ext_iff] at h₁
  subst h₁
  simp_all only [← DFunLike.ext_iff]

lemma ringaut_eq_of_faithful [hfaith:FaithfulSMul R M] ⦃f g : SemilinearAut R M⦄
    (h:∀ x, f.snd x = g.snd x) : f.fst = g.fst := by
  letI inst₁ := RingHomInvPair.of_ringEquiv f.fst
  letI := inst₁.symm
  letI inst₂ := RingHomInvPair.of_ringEquiv g.fst
  letI := inst₂.symm
  ext r
  apply hfaith.eq_of_smul_eq_smul
  intro m
  rw [← f.snd.right_inv m]
  simp only [LinearEquiv.invFun_eq_symm, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom,
    LinearEquiv.coe_coe]
  nth_rw 2 [h]
  obtain hf := f.snd.map_smulₛₗ
  obtain hg := g.snd.map_smulₛₗ
  simp only [RingHom.coe_coe] at hf hg
  rw [← hf, ← hg]
  rw [h]

protected lemma ext' [FaithfulSMul R M]
    ⦃f g: SemilinearAut R M⦄ (h : ∀ x, f.snd x = g.snd x) : f = g := by
  ext x
  . rw [ringaut_eq_of_faithful h]
  exact h x

instance [FaithfulSMul R M] : EquivLike (SemilinearAut R M) M M where
  coe := fun f => f.snd
  inv := fun f => f.snd.symm
  left_inv := fun f x => by simp only [LinearEquiv.symm_apply_apply]
  right_inv := fun f x => by simp only [LinearEquiv.apply_symm_apply]
  coe_injective' := fun e g h1 _ => by
    simp_all only
    apply SemilinearAut.ext'
    rw [h1]
    simp only [forall_const]

def mk {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {σ σ': R →+* R} [i1:RingHomInvPair σ σ'] [i2:RingHomInvPair σ' σ] (f: M ≃ₛₗ[σ] M) :
    SemilinearAut R M :=
  ⟨RingEquiv.ofHomInv σ σ' i2.comp_eq₂ i1.comp_eq₂, f⟩

lemma ext_iff ⦃f g: SemilinearAut R M⦄ :
    f = g ↔ (∀ r, f.fst r = g.fst r) ∧ ∀ m, f.snd m = g.snd m :=
  ⟨fun h => by rw [h]; simp only [forall_const, and_self], fun ⟨h₁,h₂⟩ => SemilinearAut.ext h₁ h₂⟩

lemma ext_iff' [FaithfulSMul R M] ⦃f g : SemilinearAut R M⦄ :
    f = g ↔ (∀ m, f.snd m = g.snd m) :=
  ⟨fun h => by rw [h]; simp only [forall_const], fun h => SemilinearAut.ext' h⟩

def to_ringaut_addaut (f:SemilinearAut R M): (RingAut R) × (AddAut M) :=
  ⟨f.fst,f.snd⟩

@[simp]
lemma toAddEquiv_coe {σ₁ σ₂ : R →+* R} [RingHomInvPair σ₁ σ₂] [RingHomInvPair σ₂ σ₁] (f: M ≃ₛₗ[σ₁] M) :
  f.toAddEquiv = f := rfl

@[simp]
lemma coe_somethin {σ₁ σ₂ : R →+* R} [RingHomInvPair σ₁ σ₂] [RingHomInvPair σ₂ σ₁] (f: M ≃ₛₗ[σ₁] M) :
  ⇑(f.toAddEquiv) = f := rfl

@[simp]
lemma coe_somethinf {σ₁ σ₂ : R →+* R} [RingHomInvPair σ₁ σ₂] [RingHomInvPair σ₂ σ₁]
    (f: M ≃ₛₗ[σ₁] M) (m:M) : (f:AddEquiv M M) m = f m := rfl

lemma to_ringaut_addaut_inj :
    Function.Injective (@to_ringaut_addaut R M _ _ _) := by
  intro x y h
  simp_rw [to_ringaut_addaut] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨h₁,h₂⟩ := h
  rw [AddEquiv.ext_iff] at h₂
  ext x
  . rw [h₁]
  . rename_i x'
    obtain ⟨σ₁,x₁⟩ := x'
    obtain ⟨σ₂,x₂⟩ := y
    simp_all only
    subst h₁
    exact h₂ x

instance : One (SemilinearAut R M) where
  one := ⟨RingEquiv.refl R, LinearEquiv.refl R M⟩

lemma to_ringaut_addaut_map_one : (to_ringaut_addaut (1:SemilinearAut R M)) = 1 := rfl

instance : Mul (SemilinearAut R M) where
  mul := fun x y => ⟨y.fst.trans x.fst,
    letI trip1 :RingHomCompTriple (y.fst: R →+* R) (x.fst: R →+* R)
      ((y.fst.trans x.fst):R →+* R) := ⟨by rfl⟩;
    letI trip2 :RingHomCompTriple (x.fst.symm: R →+* R) (y.fst.symm: R →+* R)
      ((y.fst.trans x.fst).symm : R →+* R) := ⟨by rfl⟩
    letI pair1 := RingHomInvPair.of_ringEquiv x.fst;
    letI pair2 := RingHomInvPair.of_ringEquiv y.fst;
    letI pair3 := RingHomInvPair.of_ringEquiv (y.fst.trans x.fst)
    letI pair1' := pair1.symm;
    letI pair2' := pair2.symm;
    letI pair3' := pair3.symm;
    y.snd.trans x.snd⟩

lemma to_ringaut_addaut_map_mul  (x y : SemilinearAut R M) :
    to_ringaut_addaut (x * y) = to_ringaut_addaut x * to_ringaut_addaut y :=
  rfl

instance : Inv (SemilinearAut R M) where
  inv := fun x => ⟨x.fst.symm,x.snd.symm⟩

lemma to_ringaut_addaut_map_inv (x:SemilinearAut R M) : to_ringaut_addaut (x⁻¹) = (to_ringaut_addaut x)⁻¹ := rfl

instance : Div (SemilinearAut R M) where
  div := fun a b => a * b⁻¹

lemma to_ringaut_addaut_map_div (x y:SemilinearAut R M) :
  to_ringaut_addaut (x / y) = to_ringaut_addaut x / to_ringaut_addaut y := rfl

instance : Monoid (SemilinearAut R M) where
  mul_assoc := fun a b c => rfl
  one_mul := fun a => rfl
  mul_one := fun a => rfl

lemma to_ringaut_addaut_map_npow (x : SemilinearAut R M) (n : ℕ) :
    to_ringaut_addaut (x ^ n) = (to_ringaut_addaut x) ^ n := by
  induction n
  . simp only [Nat.zero_eq, pow_zero]
    exact to_ringaut_addaut_map_one
  . rename_i n hind
    rw [pow_succ,pow_succ,to_ringaut_addaut_map_mul,hind]

instance : Pow (SemilinearAut R M) ℤ where
  pow := fun a b => zpowRec (npowRec) b a

private lemma npow_eq_zpow (x : SemilinearAut R M) (n : ℕ) : x ^ (n : ℤ) = x ^ n := rfl

private lemma inv_npow_eq_zpow (x : SemilinearAut R M) (n : ℕ) :
  (x ^ Int.negSucc n) = (x ^ n.succ)⁻¹ := rfl

lemma to_ringaut_addaut_map_zpow (x : SemilinearAut R M) (n : ℤ) :
    to_ringaut_addaut (x ^ n) = (to_ringaut_addaut x) ^ n := by
  induction n
  . rename_i n
    simp only [Int.ofNat_eq_coe, zpow_natCast]
    induction n
    . rfl
    . rename_i n hind
      rw [pow_succ,npow_eq_zpow,pow_succ,to_ringaut_addaut_map_mul,← npow_eq_zpow,hind]
  . simp only [zpow_negSucc]
    rw [inv_npow_eq_zpow,pow_succ,pow_succ,to_ringaut_addaut_map_inv,to_ringaut_addaut_map_mul]
    rw [to_ringaut_addaut_map_npow]

instance : Group (SemilinearAut R M) :=
  Function.Injective.group
    to_ringaut_addaut
    to_ringaut_addaut_inj
    to_ringaut_addaut_map_one
    to_ringaut_addaut_map_mul
    to_ringaut_addaut_map_inv
    to_ringaut_addaut_map_div
    to_ringaut_addaut_map_npow
    to_ringaut_addaut_map_zpow

instance instRingHomInvPair (e : SemilinearAut R M) :
    RingHomInvPair (e.fst : R →+* R) (e.fst.symm) :=
  RingHomInvPair.of_ringEquiv e.fst

-- instance instRingHomInvPair' (e : SemilinearAut R M) : RingHomInvPair (e.fst : R →+* R) ((e⁻¹).fst) :=
--   RingHomInvPair.of_ringEquiv e.fst

instance (e:SemilinearAut R M) :
    RingHomInvPair (e.fst.symm : R →+* R) e.fst :=
  instRingHomInvPair e |>.symm


@[simp]
theorem coe_mul (e₁ e₂ : SemilinearAut R M) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : SemilinearAut R M) = id :=
  rfl


@[simp]
theorem mk_apply {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {σ σ': R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f: M ≃ₛₗ[σ] M) (m:M):
    mk f m = f m := rfl

@[simp]
theorem mul_mk {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {σ₁₂ σ₂₁: R →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (f: M ≃ₛₗ[σ₁₂] M)
    {σ₂₃ σ₃₂: R →+* R} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃] (g : M ≃ₛₗ[σ₂₃] M)
    {σ₁₃ σ₃₁ : R →+* R} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
    [t1:RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [t2:RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]:
    mk g * mk f = mk (f.trans g) := by
  ext x
  . exact t1.comp_apply
  . exact rfl

@[simp]
theorem inv_mk {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {σ σ': R →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (f: M ≃ₛₗ[σ] M):
    (mk f)⁻¹ = mk f.symm := rfl

@[simp]
theorem div_mk {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {σ₁₂ σ₂₁: R →+* R} [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (f: M ≃ₛₗ[σ₂₁] M)
    {σ₂₃ σ₃₂: R →+* R} [RingHomInvPair σ₂₃ σ₃₂] [RingHomInvPair σ₃₂ σ₂₃] (g : M ≃ₛₗ[σ₂₃] M)
    {σ₁₃ σ₃₁ : R →+* R} [RingHomInvPair σ₁₃ σ₃₁] [RingHomInvPair σ₃₁ σ₁₃]
    [t1:RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [t2:RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]:
    mk g / mk f = mk (f.symm.trans g) := by
  ext x
  . simp_rw [HDiv.hDiv,Div.div,Inv.inv,HMul.hMul,Mul.mul,mk]
    simp only [RingEquiv.coe_trans, Function.comp_apply, RingEquiv.ofHomInv_symm_apply,
      RingEquiv.ofHomInv_apply]
    exact t1.comp_apply
  . exact rfl


end SemilinearAut
