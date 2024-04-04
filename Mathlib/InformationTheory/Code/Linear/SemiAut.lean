import Mathlib.InformationTheory.Code.Basic
import Mathlib.InformationTheory.Code.Aut

import Mathlib.InformationTheory.Code.Linear.SemiEquiv
import Mathlib.InformationTheory.Code.Linear.tmp



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
  [Set.IsDelone gdistₘ ↑s] [Nontrivial γ]
  [PosMulMono γ] [MulPosMono γ] [ZeroLEOneClass γ] [StrictModuleGNorm K K gdistₖ gdistₖ]
  [StrictModuleGNorm K M gdistₖ gdistₘ]

section
variable (K gdistₖ gdistₘ s)

abbrev SemilinearCodeAut [_LinearCode γ K gdistₖ gdistₘ s] : Type _ :=
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
  (h₁ : x.fst = y.fst) (h₂ : ⇑x.snd = ⇑y.snd) : x = y := by
  cases x; cases y;
  subst h₁
  simp_all only [DFunLike.coe_fn_eq]

lemma ext_iff ⦃x y : SemilinearCodeAut K gdistₖ gdistₘ s⦄ : x = y ↔ x.fst = y.fst ∧ ⇑x.snd = ⇑y.snd :=
  ⟨fun h => by rw [h]; simp only [and_self],fun ⟨h₁,h₂⟩ => SemilinearCodeAut.ext h₁ h₂⟩


def toSemilinearAut : SemilinearCodeAut K gdistₖ gdistₘ s → SemilinearAut K M := fun ⟨σ,f⟩ => ⟨σ,
  letI inst := RingHomInvPair.of_ringEquiv σ;
  letI := inst.symm
  f.toLinearEquiv⟩

lemma toSemilinearAut.inj : Function.Injective (toSemilinearAut : SemilinearCodeAut K gdistₖ gdistₘ s → SemilinearAut K M) :=
  fun x y h => by
    rw [SemilinearAut.ext_iff] at h
    simp_rw [toSemilinearAut] at h

    ext m
    . rw [h.left]
    . obtain h₂ := h.right
      obtain h₃  := (
        letI inst := RingHomInvPair.of_ringEquiv x.fst;
        letI := inst.symm;
        SemilinearCodeEquiv.toLinearEquiv_eq_coe x.snd)
      obtain h₄ := (
        letI inst := RingHomInvPair.of_ringEquiv y.fst;
        letI := inst.symm;
        SemilinearCodeEquiv.toLinearEquiv_eq_coe y.snd)
      obtain h₅ := (
        letI inst := RingHomInvPair.of_ringEquiv x.fst;
        letI := inst.symm;
        SemilinearCodeEquiv.coe_toLinearEquiv x.snd
      )
      obtain h₆ := (
        letI inst := RingHomInvPair.of_ringEquiv y.fst;
        letI := inst.symm;
        SemilinearCodeEquiv.coe_toLinearEquiv y.snd
      )
      rw [h₃,h₄,h₅,h₆] at h₂
      rw [h₂]


instance instMonoid [_LinearCode γ K gdistₖ gdistₘ s] : Monoid (SemilinearCodeAut K gdistₖ gdistₘ s) where
  mul := fun ⟨σ₁,x⟩ ⟨σ₂,y⟩ => ⟨σ₂.trans σ₁,
    letI trip1 : RingHomCompTriple (σ₂ : K →+* K) (σ₁ : K →+* K) (σ₂.trans σ₁ : K →+* K) :=
      ⟨by simp only [RingEquiv.coe_ringHom_trans]⟩
    letI trip2 : RingHomCompTriple (σ₁.symm : K →+* K) (σ₂.symm : K →+* K)
        ((σ₂.trans σ₁).symm : K →+* K) := ⟨by rfl⟩
    letI pair1 := RingHomInvPair.of_ringEquiv σ₁;
    letI pair2 := RingHomInvPair.of_ringEquiv σ₂;
    letI pair3 := RingHomInvPair.of_ringEquiv (σ₂.trans σ₁)
    letI pair1' := pair1.symm;
    letI pair2' := pair2.symm;
    letI pair3' := pair3.symm;
    y.trans x⟩
  mul_assoc := fun a b c => rfl
  one := ⟨RingEquiv.refl K, SemilinearCodeEquiv.refl K gdistₖ gdistₘ s⟩
  one_mul := fun x => by
    simp_rw [HMul.hMul,OfNat.ofNat]
    ext : 1 <;> rfl
  mul_one := fun x => by
    simp_rw [HMul.hMul,OfNat.ofNat]
    ext : 1 <;> rfl

instance : Inv (SemilinearCodeAut K gdistₖ gdistₘ s) where
  inv := fun ⟨σ,x⟩ => ⟨σ.symm,
    letI inst := RingHomInvPair.of_ringEquiv σ;
    letI := inst.symm;
    x.symm⟩



end SemilinearCodeAut

namespace LinearCodeAut

instance instGroup [_LinearCode γ K gdistₖ gdistₘ s] : Group (LinearCodeAut K gdistₖ gdistₘ s) := {
    mul := fun f g => g.trans f
    mul_assoc := fun a b c ↦ rfl
    one := SemilinearCodeEquiv.refl K gdistₖ gdistₘ s
    one_mul := fun a ↦ rfl
    mul_one := fun a ↦ rfl
    inv := SemilinearCodeEquiv.symm
    mul_left_inv := SemilinearCodeEquiv.self_trans_symm
    }

@[simp]
theorem coe_mul (e₁ e₂ : LinearCodeAut K gdistₖ gdistₘ s) : ⇑(e₁ * e₂) = e₁ ∘ e₂ :=
  rfl

@[simp]
theorem coe_one : ⇑(1 : LinearCodeAut K gdistₖ gdistₘ s) = id :=
  rfl

theorem mul_def (e₁ e₂ : LinearCodeAut K gdistₖ gdistₘ s) : e₁ * e₂ = e₂.trans e₁ :=
  rfl

theorem one_def : (1 : LinearCodeAut K gdistₖ gdistₘ s) = SemilinearCodeEquiv.refl _ _ _ _ :=
  rfl

theorem inv_def (e₁ : LinearCodeAut K gdistₖ gdistₘ s) : e₁⁻¹ = e₁.symm :=
  rfl


@[simp]
theorem mul_apply (e₁ e₂ : LinearCodeAut K gdistₖ gdistₘ s) (m : M) : (e₁ * e₂) m = e₁ (e₂ m) :=
  rfl

@[simp]
theorem one_apply (m : M) : (1 : LinearCodeAut K gdistₖ gdistₘ s) m = m :=
  rfl

@[simp]
theorem apply_inv_self (e : LinearCodeAut K gdistₖ gdistₘ s) (m : M) : e (e⁻¹ m) = m :=
  SemilinearCodeEquiv.apply_symm_apply _ _

@[simp]
theorem inv_apply_self (e : LinearCodeAut K gdistₖ gdistₘ s) (m : M) : e⁻¹ (e m) = m :=
  SemilinearCodeEquiv.apply_symm_apply _ _


def toCodeAut : (LinearCodeAut K gdistₖ gdistₘ s) →* (CodeAut gdistₘ s) where
  toFun := SemilinearCodeEquiv.toCodeEquiv
  map_one' := by simp_all only [SemilinearCodeEquiv.toCodeEquiv_eq_coe]; rfl
  map_mul' := fun x y => by simp_all only [SemilinearCodeEquiv.toCodeEquiv_eq_coe]; rfl

def toLinearAut : (LinearCodeAut K gdistₖ gdistₘ s) →* (M ≃ₗ[K] M) where
  toFun := SemilinearCodeEquiv.toLinearEquiv
  map_one':= by simp_all only [SemilinearCodeEquiv.toLinearEquiv_eq_coe]; rfl
  map_mul' := fun x y => by simp_all only [SemilinearCodeEquiv.toLinearEquiv_eq_coe]; rfl


instance applyDistribMulAction :
    DistribMulAction (LinearCodeAut K gdistₖ gdistₘ s) M where
  smul := (· <| ·)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero := fun f => (f: M →+ M).map_zero'
  smul_add := fun f => (f: M →+ M).map_add'

@[simp]
protected theorem smul_def (f : LinearCodeAut K gdistₖ gdistₘ s) (a : M) :
  f • a = f a := rfl

instance apply_faithfulSMul : FaithfulSMul (LinearCodeAut K gdistₖ gdistₘ s) M :=
  ⟨fun h => SemilinearCodeEquiv.ext h⟩

end LinearCodeAut
