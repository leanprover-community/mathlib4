import Mathlib.Algebra.Module.Equiv
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.GroupTheory.QuotientGroup



def SemilinearAut (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]: Type _ :=
    (σ:RingAut R) × (
      letI inst := RingHomInvPair.of_ringEquiv σ;
      letI := inst.symm;
      M ≃ₛₗ[(σ : R →+* R)] M)

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

namespace SemilinearAut

instance : CoeFun (SemilinearAut R M)
    (fun ⟨σ,_⟩ => (
      letI inst := RingHomInvPair.of_ringEquiv σ;
      letI := inst.symm;
      M ≃ₛₗ[(σ : R →+* R)] M)) where
  coe := fun ⟨_,f⟩ => f

@[ext]
protected lemma SemilinearAut.ext
  ⦃f g: SemilinearAut R M⦄ (h₁: f.fst = g.fst) (h₂: ⇑f.snd = ⇑g.snd ): f = g := by
  cases f; cases g;
  subst h₁
  simp_all only [DFunLike.coe_fn_eq]

def SemilinearAut.mk {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {σ σ': R →+* R} [i1:RingHomInvPair σ σ'] [i2:RingHomInvPair σ' σ] (f: M ≃ₛₗ[σ] M) :
    SemilinearAut R M :=
  ⟨RingEquiv.ofHomInv σ σ' i2.comp_eq₂ i1.comp_eq₂, f⟩


lemma SemilinearAut.ext_iff ⦃f g: SemilinearAut R M⦄ : f = g ↔ f.fst = g.fst ∧ ⇑f.snd = ⇑g.snd :=
  ⟨fun h => by rw [h]; simp only [and_self], fun ⟨h₁,h₂⟩ => SemilinearAut.ext h₁ h₂⟩

def to_somethin (f:SemilinearAut R M): (RingAut R) × (AddAut M) :=
  ⟨f.fst,f.snd⟩

@[simp]
lemma somethin_coe {σ₁ σ₂ : R →+* R} [RingHomInvPair σ₁ σ₂] [RingHomInvPair σ₂ σ₁] (f: M ≃ₛₗ[σ₁] M) :
  f.toAddEquiv = f := rfl

@[simp]
lemma coe_somethin {σ₁ σ₂ : R →+* R} [RingHomInvPair σ₁ σ₂] [RingHomInvPair σ₂ σ₁] (f: M ≃ₛₗ[σ₁] M) :
  ⇑(f.toAddEquiv) = f := rfl

@[simp]
lemma coe_somethinf {σ₁ σ₂ : R →+* R} [RingHomInvPair σ₁ σ₂] [RingHomInvPair σ₂ σ₁]
    (f: M ≃ₛₗ[σ₁] M) (m:M) : (f:AddEquiv M M) m = f m := rfl

lemma to_somethin_inj :
    Function.Injective (@to_somethin R M _ _ _) := by
  intro x y h
  simp_rw [to_somethin] at h
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

lemma to_somethin_map_one : (to_somethin (1:SemilinearAut R M)) = 1 := rfl

instance : Mul (SemilinearAut R M) where
  mul := fun ⟨σ₁,f⟩ ⟨σ₂,g⟩ => ⟨σ₂.trans σ₁,
    letI trip1 :RingHomCompTriple (σ₂: R →+* R) (σ₁: R →+* R) ((σ₂.trans σ₁):R →+* R) := ⟨by rfl⟩;
    letI trip2 :RingHomCompTriple (σ₁.symm: R →+* R) (σ₂.symm: R →+* R)
      ((σ₂.trans σ₁).symm : R →+* R) := ⟨by rfl⟩
    letI pair1 := RingHomInvPair.of_ringEquiv σ₁;
    letI pair2 := RingHomInvPair.of_ringEquiv σ₂;
    letI pair3 := RingHomInvPair.of_ringEquiv (σ₂.trans σ₁)
    letI pair1' := pair1.symm;
    letI pair2' := pair2.symm;
    letI pair3' := pair3.symm;
    g.trans f⟩

lemma to_somethin_map_mul  (x y : SemilinearAut R M) :
    to_somethin (x * y) = to_somethin x * to_somethin y :=
  rfl

instance : Inv (SemilinearAut R M) where
  inv := fun ⟨σ,f⟩ => ⟨σ.symm,f.symm⟩

lemma to_somethin_map_inv (x:SemilinearAut R M) : to_somethin (x⁻¹) = (to_somethin x)⁻¹ := rfl

instance : Div (SemilinearAut R M) where
  div := fun a b => a * b⁻¹

lemma to_somethin_map_div (x y:SemilinearAut R M) :
  to_somethin (x / y) = to_somethin x / to_somethin y := rfl

instance : Monoid (SemilinearAut R M) where
  mul_assoc := fun a b c => rfl
  one_mul := fun a => rfl
  mul_one := fun a => rfl

lemma to_somethin_map_npow (x : SemilinearAut R M) (n : ℕ) :
    to_somethin (x ^ n) = (to_somethin x) ^ n := by
  induction n
  . simp only [Nat.zero_eq, pow_zero]
    exact to_somethin_map_one
  . rename_i n hind
    rw [pow_succ,pow_succ,to_somethin_map_mul,hind]

instance : Pow (SemilinearAut R M) ℤ where
  pow := fun a b => zpowRec b a

private lemma npow_eq_zpow (x : SemilinearAut R M) (n : ℕ) : x ^ (n : ℤ) = x ^ n := rfl

private lemma inv_npow_eq_zpow (x : SemilinearAut R M) (n : ℕ) :
  (x ^ Int.negSucc n) = (x ^ n.succ)⁻¹ := rfl

lemma to_somethin_map_zpow (x : SemilinearAut R M) (n : ℤ) :
    to_somethin (x ^ n) = (to_somethin x) ^ n := by
  induction n
  . rename_i n
    simp only [Int.ofNat_eq_coe, zpow_coe_nat]
    induction n
    . rfl
    . rename_i n hind
      rw [pow_succ,npow_eq_zpow,pow_succ,to_somethin_map_mul,← npow_eq_zpow,hind]
  . simp only [zpow_negSucc]
    rw [inv_npow_eq_zpow,pow_succ,pow_succ,to_somethin_map_inv,to_somethin_map_mul]
    rw [to_somethin_map_npow]

instance : Group (SemilinearAut R M) :=
  Function.Injective.group
    to_somethin
    to_somethin_inj
    to_somethin_map_one
    to_somethin_map_mul
    to_somethin_map_inv
    to_somethin_map_div
    to_somethin_map_npow
    to_somethin_map_zpow

def toAddAut_mulHom : SemilinearAut R M →* AddAut M where
  toFun := fun f => f.snd
  map_one' := rfl
  map_mul' := fun _ _ => rfl

end SemilinearAut
section

variable (R M)

abbrev GSL := (SemilinearAut R M) ⧸ (MonoidHom.ker SemilinearAut.toAddAut_mulHom : Subgroup (SemilinearAut R M))

end
namespace GSL
abbrev toAddAut : GSL R M →* AddAut M := QuotientGroup.kerLift SemilinearAut.toAddAut_mulHom

instance : FunLike (GSL R M) M M where
  coe := fun f => toAddAut f
  coe_injective' := fun x y => by
    simp only
    simp only [DFunLike.coe_fn_eq]
    apply QuotientGroup.kerLift_injective
