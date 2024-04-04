import Mathlib.InformationTheory.Code.Linear.Basic
import Mathlib.InformationTheory.Code.Hom

open Set

variable (T:Type*)

variable {γ : Type*} [Semiring γ] [CompleteLinearOrder γ] [Nontrivial γ]
variable {K : Type*} [Field K] (σ₁₂ : K →+* K) {Tₖ : Type*} (gdistₖ:Tₖ)
variable {M : Type*} {Tₘ : Type*} (gdistₘ:Tₘ) [AddCommMonoid M] [Module K M]
variable (sₘ : Submodule K M)
variable--? [_LinearCode γ K gdistₖ gdistₘ sₘ] =>
  [CovariantClass γ γ (fun x x_1 ↦ x + x_1) fun x x_1 ↦ x ≤ x_1] [FunLike Tₖ K (K → γ)]
  [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdistₖ] [FunLike Tₘ M (M → γ)]
  [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdistₘ] [IsDelone gdistₘ ↑sₘ] [PosMulMono γ]
  [MulPosMono γ] [ZeroLEOneClass γ] [StrictModuleGNorm K K gdistₖ gdistₖ]
  [StrictModuleGNorm K M gdistₖ gdistₘ]
variable {M₂ : Type*} {Tₘ₂ : Type*} (gdistₘ₂:Tₘ₂) [AddCommMonoid M₂] [Module K M₂]
variable (sₘ₂ : Submodule K M₂)
variable--? [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂] =>
  [FunLike Tₘ₂ M₂ (M₂ → γ)] [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdistₘ₂]
  [IsDelone gdistₘ₂ ↑sₘ₂] [StrictModuleGNorm K M₂ gdistₖ gdistₘ₂]
variable--? [CodeHomClass T gdistₘ sₘ gdistₘ₂ sₘ₂] =>
  [FunLike T M M₂] [CodeHomClass T gdistₘ sₘ gdistₘ₂ sₘ₂]

structure SemilinearCodeHom [_LinearCode γ K gdistₖ gdistₘ sₘ] [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂]
  extends CodeHom gdistₘ sₘ gdistₘ₂ sₘ₂,LinearMap σ₁₂ M M₂ where

section
variable (K)

abbrev LinearCodeHom [_LinearCode γ K gdistₖ gdistₘ sₘ] [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂] :=
  SemilinearCodeHom (RingHom.id K) gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂

end

class SemilinearCodeHomClass (T:Type*) {γ :outParam Type*} [Semiring γ] [CompleteLinearOrder γ]
    [Nontrivial γ] [CovariantClass γ γ (.+.) (.≤.)] [PosMulMono γ] [MulPosMono γ]
    [ZeroLEOneClass γ] {K : outParam Type*} [Field K] (σ₁₂ : outParam (K →+* K)) {Tₖ:outParam Type*}
    (gdistₖ:outParam Tₖ) [FunLike Tₖ K (K → γ)] [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdistₖ]
    [StrictModuleGNorm K K gdistₖ gdistₖ] {M: outParam Type*} {Tₘ:outParam Type*}
    (gdistₘ: outParam Tₘ) [AddCommMonoid M] [Module K M] (sₘ: outParam (Submodule K M))
    [FunLike Tₘ M (M → γ)] [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdistₘ] [IsDelone gdistₘ sₘ]
    [StrictModuleGNorm K M gdistₖ gdistₘ] -- [_LinearCode γ K gdistₖ gdistₘ sₘ]
    {M₂: outParam Type*} {Tₘ₂:outParam Type*} (gdistₘ₂: outParam Tₘ₂) [AddCommMonoid M₂]
    [Module K M₂] (sₘ₂:outParam (Submodule K M₂)) [FunLike Tₘ₂ M₂ (M₂ → γ)]
    [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdistₘ₂] [IsDelone gdistₘ₂ sₘ₂]
    [StrictModuleGNorm K M₂ gdistₖ gdistₘ₂] -- [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂]
    [FunLike T M M₂]
    extends CodeHomClass T gdistₘ sₘ gdistₘ₂ sₘ₂, SemilinearMapClass T σ₁₂ M M₂ : Prop
    where

abbrev LinearCodeHomClass (T:Type*) {γ :outParam Type*} [Semiring γ] [CompleteLinearOrder γ]
    [Nontrivial γ] [CovariantClass γ γ (.+.) (.≤.)] [PosMulMono γ] [MulPosMono γ]
    [ZeroLEOneClass γ] (K : outParam Type*) [Field K] {Tₖ:outParam Type*} (gdistₖ:outParam Tₖ)
    [FunLike Tₖ K (K → γ)] [GPseudoMetricClass Tₖ K γ] [AddGNorm K γ gdistₖ]
    [StrictModuleGNorm K K gdistₖ gdistₖ] {M: outParam Type*} {Tₘ:outParam Type*}
    (gdistₘ: outParam Tₘ) [AddCommMonoid M] [Module K M] (sₘ: outParam (Submodule K M))
    [FunLike Tₘ M (M → γ)] [GPseudoMetricClass Tₘ M γ] [AddGNorm M γ gdistₘ] [IsDelone gdistₘ sₘ]
    [StrictModuleGNorm K M gdistₖ gdistₘ] -- [_LinearCode γ K gdistₖ gdistₘ sₘ]
    {M₂: outParam Type*} {Tₘ₂:outParam Type*} (gdistₘ₂: outParam Tₘ₂) [AddCommMonoid M₂]
    [Module K M₂] (sₘ₂:outParam (Submodule K M₂)) [FunLike Tₘ₂ M₂ (M₂ → γ)]
    [GPseudoMetricClass Tₘ₂ M₂ γ] [AddGNorm M₂ γ gdistₘ₂] [IsDelone gdistₘ₂ sₘ₂]
    [StrictModuleGNorm K M₂ gdistₖ gdistₘ₂] -- [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂]
    [FunLike T M M₂] := SemilinearCodeHomClass T (RingHom.id K) gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂

namespace SemilinearCodeHom

instance instFunLike :
    FunLike (SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) M M₂ where
  coe := fun φ => ⇑φ.toCodeHom
  coe_injective' := fun φ₁ φ₂ h => by
    cases φ₁; cases φ₂; simp_all only [DFunLike.coe_fn_eq]
section

variable {σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂}

@[ext]
lemma ext
    ⦃φ φ₂: SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂⦄
    (h:∀ x,φ x = φ₂ x) : φ = φ₂ := DFunLike.ext _ _ h
end

instance instLinearCodeHomClass
    [_LinearCode γ K gdistₖ gdistₘ sₘ] [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂]:
    SemilinearCodeHomClass
      (SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂)
      σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ where
      map_dist' := fun f => f.map_dist
      map_code' := fun f => f.map_code
      map_add := fun f => f.toLinearMap.map_add
      map_smulₛₗ := fun f => f.toLinearMap.map_smulₛₗ

end SemilinearCodeHom

variable {T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂}
variable [SemilinearCodeHomClass T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂]

@[coe]
def SemilinearCodeHomClass.toSemilinearCodeHom
    [SemilinearCodeHomClass T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂] (φ:T):
  SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ := {
    CodeHomClass.toCodeHom φ, SemilinearMapClass.semilinearMap φ with
  }

instance
    [SemilinearCodeHomClass T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂] :
    CoeTC T (SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :=
  ⟨SemilinearCodeHomClass.toSemilinearCodeHom⟩

namespace SemilinearCodeHom
@[simp]
theorem coe_coe
    [SemilinearCodeHomClass T σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂] (f : T) :
    ((f : SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) : M → M₂) = f := rfl

@[simp]
theorem coe_mk
    [_LinearCode γ K gdistₖ gdistₘ sₘ]
    [_LinearCode γ K gdistₖ gdistₘ₂ sₘ₂]
    (f : CodeHom gdistₘ sₘ gdistₘ₂ sₘ₂)
    (map_add : ∀ (x y : M), f (x + y) = f x + f y)
    (map_smul : ∀ (r : K) (x : M), f (r • x) = σ₁₂ r • f x):
    ((@SemilinearCodeHom.mk γ _ _ _ _ _ σ₁₂ Tₖ gdistₖ) f map_add map_smul : M → M₂) = f := rfl

protected def copy
    (f : SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f' : M → M₂) (h : f' = f) :
    SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂ := {
  f.toCodeHom.copy f' h, f.toLinearMap.copy f' h with}

@[simp]
theorem coe_copy
    (f : SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f' : M → M₂) (h : f' = f) :
    (f.copy f' h) = f' := rfl

theorem coe_copy_eq (f :SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (f' : M → M₂)
  (h : f' = f) : f.copy f' h = f := DFunLike.ext' h

variable {σ₂₃ : K →+* K} {σ₁₃ : K →+* K} [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] {Tₘ₃ M₃:Type*}
  {gdistₘ₃:Tₘ₃} [AddCommMonoid M₃]
variable [Module K M₃] {sₘ₃ : Submodule K M₃}
variable--? [_LinearCode γ K gdistₖ gdistₘ₃ sₘ₃] =>
  [FunLike Tₘ₃ M₃ (M₃ → γ)] [GPseudoMetricClass Tₘ₃ M₃ γ] [AddGNorm M₃ γ gdistₘ₃]
  [IsDelone gdistₘ₃ ↑sₘ₃] [StrictModuleGNorm K M₃ gdistₖ gdistₘ₃]


section
variable (K gdistₖ gdistₘ sₘ)

@[simps!] -- not sure if this should or shouldn't be simps
def id [_LinearCode γ K gdistₖ gdistₘ sₘ] :
    SemilinearCodeHom (RingHom.id K) gdistₖ gdistₘ sₘ gdistₘ sₘ :=
  {CodeHom.id gdistₘ sₘ, LinearMap.id with}
end

def comp
    (φ: SemilinearCodeHom σ₂₃ gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃)
    (φ₂ : SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
    SemilinearCodeHom σ₁₃ gdistₖ gdistₘ sₘ gdistₘ₃ sₘ₃ := {
      φ.toCodeHom.comp φ₂.toCodeHom, φ.toLinearMap.comp φ₂.toLinearMap with}


@[simp]
theorem coe_comp (g : SemilinearCodeHom σ₂₃ gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃)
    (f : SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
    ↑(g.comp f) = g ∘ f := rfl

theorem comp_apply (g : SemilinearCodeHom σ₂₃ gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃)
    (f : SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) (x : M) :
    g.comp f x = g (f x) := rfl

variable {σ₃₄ : K →+* K} {σ₂₄ : K →+* K} {σ₁₄ : K →+* K} [RingHomCompTriple σ₂₃ σ₃₄ σ₂₄]
  [RingHomCompTriple σ₁₃ σ₃₄ σ₁₄] [RingHomCompTriple σ₁₂ σ₂₄ σ₁₄]
  {M₄:Type*} {Tₘ₄:Type*} {gdistₘ₄:Tₘ₄} [AddCommMonoid M₄] [Module K M₄] {sₘ₄:Submodule K M₄}
variable--? [_LinearCode γ K gdistₖ gdist_m₄ s₄] =>
  [FunLike Tₘ₄ M₄ (M₄ → γ)] [GPseudoMetricClass Tₘ₄ M₄ γ] [AddGNorm M₄ γ gdistₘ₄]
  [IsDelone gdistₘ₄ ↑sₘ₄] [StrictModuleGNorm K M₄ gdistₖ gdistₘ₄]

theorem comp_assoc
    (f : SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂)
    (g : SemilinearCodeHom σ₂₃ gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃)
    (h : SemilinearCodeHom σ₃₄ gdistₖ gdistₘ₃ sₘ₃ gdistₘ₄ sₘ₄) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

theorem cancel_right
    {g₁ g₂ : SemilinearCodeHom σ₂₃ gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃}
    {f : SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂}
    (hf : Function.Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 (DFunLike.ext_iff.1 h), fun h => h ▸ rfl⟩


theorem cancel_left
    {g : SemilinearCodeHom σ₂₃ gdistₖ gdistₘ₂ sₘ₂ gdistₘ₃ sₘ₃}
    {f₁ f₂ : SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂}
    (hg : Function.Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h => ext fun x => hg <| by rw [← comp_apply, h,
    comp_apply],fun h => h ▸ rfl⟩

@[simp]
theorem comp_id (f : SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
    f.comp (id K gdistₖ gdistₘ sₘ) = f :=
  ext fun _ => rfl

@[simp]
theorem id_comp (f : SemilinearCodeHom σ₁₂ gdistₖ gdistₘ sₘ gdistₘ₂ sₘ₂) :
    (id K gdistₖ gdistₘ₂ sₘ₂).comp f = f :=
  ext fun _ => rfl

end SemilinearCodeHom
