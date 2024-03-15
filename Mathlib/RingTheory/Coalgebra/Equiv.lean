import Mathlib.RingTheory.Coalgebra.Hom

set_option autoImplicit true

open BigOperators TensorProduct

universe u v w u₁ v₁

variable {R : Type*} {R₁ : Type*} {R₂ : Type*} {R₃ : Type*}
variable {k : Type*} {S : Type*} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
variable {N₁ : Type*} {N₂ : Type*} {N₃ : Type*} {N₄ : Type*} {ι : Type*}

open Coalgebra
/-- An equivalence of algebras is an equivalence of rings commuting with the actions of scalars. -/
structure CoalgEquiv (R : Type u) [CommSemiring R] (A : Type v) (B : Type w)
  [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]
  [CoalgebraStruct R A] [CoalgebraStruct R B] extends A →c[R] B, A ≃ₗ[R] B where

attribute [coe] CoalgEquiv.toCoalgHom

/-- The notation `M ≃ₗ [R] M₂` denotes the type of linear equivalences between `M` and `M₂` over
a plain linear map `M →ₗ M₂`. -/
notation:50 M " ≃c[" R "] " M₂ => CoalgEquiv R M M₂

class CoalgEquivClass (F : Type*) (R M M₂ : outParam (Type*)) [CommSemiring R] [AddCommMonoid M]
    [AddCommMonoid M₂] [Module R M] [Module R M₂]
    [CoalgebraStruct R M] [CoalgebraStruct R M₂]
    [EquivLike F M M₂] extends CoalgHomClass F R M M₂, SemilinearEquivClass F (RingHom.id R) M M₂

namespace CoalgEquivClass

variable (F : Type*) [CommSemiring R]

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M] [Module R M₂] [CoalgebraStruct R M] [CoalgebraStruct R M₂]

instance (priority := 100)
  [EquivLike F M M₂] [s : CoalgEquivClass F R M M₂] : CoalgHomClass F R M M₂ :=
  { s with }

end CoalgEquivClass

namespace CoalgEquiv

section AddCommMonoid

variable {M₄ : Type*}

variable [CommSemiring R]

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [Module R M] [Module R M₂] [CoalgebraStruct R M] [CoalgebraStruct R M₂]

instance : Coe (M ≃c[R] M₂) (M →c[R] M₂) :=
  ⟨toCoalgHom⟩

-- This exists for compatibility, previously `≃ₗ[R]` extended `≃` instead of `≃+`.
/-- The equivalence of types underlying a linear equivalence. -/
def toEquiv : (M ≃c[R] M₂) → M ≃ M₂ := fun f => f.toLinearEquiv.toEquiv

theorem toEquiv_injective : Function.Injective (toEquiv : (M ≃c[R] M₂) → M ≃ M₂) :=
  sorry

@[simp]
theorem toEquiv_inj {e₁ e₂ : M ≃c[R] M₂} : e₁.toEquiv = e₂.toEquiv ↔ e₁ = e₂ :=
  toEquiv_injective.eq_iff

theorem toCoalgHom_injective : Function.Injective (toCoalgHom : (M ≃c[R] M₂) → M →c[R] M₂) :=
  fun _ _ H => toEquiv_injective <| Equiv.ext <| CoalgHom.congr_fun H

@[simp, norm_cast]
theorem toCoalgHom_inj {e₁ e₂ : M ≃c[R] M₂} : (↑e₁ : M →c[R] M₂) = e₂ ↔ e₁ = e₂ :=
  toCoalgHom_injective.eq_iff

instance : EquivLike (M ≃c[R] M₂) M M₂ where
  inv := CoalgEquiv.invFun
  coe_injective' _ _ h _ := toCoalgHom_injective (DFunLike.coe_injective h)
  left_inv := CoalgEquiv.left_inv
  right_inv := CoalgEquiv.right_inv

instance : FunLike (M ≃c[R] M₂) M M₂ where
  coe := DFunLike.coe
  coe_injective' := DFunLike.coe_injective

instance : CoalgEquivClass (M ≃c[R] M₂) R M M₂ where
  map_add := (·.map_add') --map_add' Porting note: TODO why did I need to change this?
  map_smulₛₗ := (·.map_smul') --map_smul' Porting note: TODO why did I need to change this?
  counit_comp := sorry
  map_comp_comul := sorry

-- Porting note: moved to a lower line since there is no shortcut `CoeFun` instance any more
@[simp]
theorem coe_mk {to_fun inv_fun map_add map_smul ugh ugh2 left_inv right_inv} :
    (⟨⟨⟨⟨to_fun, map_add⟩, map_smul⟩, ugh, ugh2⟩, inv_fun, left_inv, right_inv⟩ : M ≃c[R] M₂) = to_fun := rfl

theorem coe_injective : @Function.Injective (M ≃c[R] M₂) (M → M₂) CoeFun.coe :=
  DFunLike.coe_injective

end

section

variable [AddCommMonoid M] [AddCommMonoid M₁] [AddCommMonoid M₂]

variable [AddCommMonoid M₃] [AddCommMonoid M₄]

variable [AddCommMonoid N₁] [AddCommMonoid N₂]

variable [module_M : Module R M] [module_R_M₂ : Module R M₂] {wtf : CoalgebraStruct R M} {wtf2 : CoalgebraStruct R M₂}

variable (e e' : M ≃c[R] M₂)

@[simp, norm_cast]
theorem coe_coe : ⇑(e : M →c[R] M₂) = e :=
  rfl

@[simp]
theorem coe_toEquiv : ⇑(e.toEquiv) = e :=
  rfl

@[simp]
theorem coe_toCoalgHom : ⇑e.toCoalgHom = e :=
  rfl

@[simp]
theorem toLinearEquiv_toLinearMap :
    e.toLinearEquiv.toLinearMap = e.toLinearMap := rfl

@[simp]
theorem toCoalgHom_toLinearMap :
    e.toCoalgHom.toLinearMap = e.toLinearMap := rfl

-- porting note: no longer a `simp`
theorem toFun_eq_coe : e.toFun = e := rfl

section

variable {e e'}

@[ext]
theorem ext (h : ∀ x, e x = e' x) : e = e' :=
  DFunLike.ext _ _ h

theorem ext_iff : e = e' ↔ ∀ x, e x = e' x :=
  DFunLike.ext_iff

protected theorem congr_arg {x x'} : x = x' → e x = e x' :=
  DFunLike.congr_arg e

protected theorem congr_fun (h : e = e') (x : M) : e x = e' x :=
  DFunLike.congr_fun h x

end

section

variable (M R)

/-- The identity map is a linear equivalence. -/
@[refl]
def refl [Module R M] [CoalgebraStruct R M] : M ≃c[R] M :=
  { CoalgHom.id R M, LinearEquiv.refl R M with }

end


@[simp]
theorem refl_toCoalgHom : ↑(refl R M : M ≃c[R] M) = CoalgHom.id R M :=
  rfl

@[simp]
theorem coe_refl : ⇑(refl R M : M ≃c[R] M) = id :=
  rfl

/-@[simp]
theorem refl_toLinearMap [Module R M] [CoalgebraStruct R M] :
    (refl R M).toLinearMap = LinearMap.id := rfl

@[simp]
theorem refl_toLinearEquiv [Module R M] [CoalgebraStruct R M] :
    (refl R M).toLinearEquiv = LinearEquiv.refl R M := rfl

@[simp]
theorem refl_toCoalgHom [Module R M] [CoalgebraStruct R M] :
    (refl R M).toCoalgHom = CoalgHom.id R M := rfl
-/
@[simp]
theorem refl_apply [Module R M] [CoalgebraStruct R M] (x : M) : refl R M x = x :=
  rfl

/-- Linear equivalences are symmetric. -/
@[symm]
def symm (e : M ≃c[R] M₂) : M₂ ≃c[R] M :=
  { e.toLinearEquiv.symm with
    counit_comp := sorry
    map_comp_comul := sorry }

@[simp] lemma symm_toLinearEquiv (e : M ≃c[R] M₂) :
    e.symm.toLinearEquiv = e.toLinearEquiv.symm := rfl

def Simps.apply {R : Type*} [CommSemiring R]
    {M : Type*} {M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]
    [CoalgebraStruct R M] [CoalgebraStruct R M₂]
    (e : M ≃c[R] M₂) : M → M₂ :=
  e

def Simps.symm_apply {R : Type*} [CommSemiring R]
    {M : Type*} {M₂ : Type*} [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R M₂]
    [CoalgebraStruct R M] [CoalgebraStruct R M₂]
    (e : M ≃c[R] M₂) : M₂ → M :=
  e.symm

-- can't get it to work idk why
--initialize_simps_projections CoalgEquiv (toFun → apply, invFun → symm_apply)

@[simp]
theorem invFun_eq_symm : e.invFun = e.symm :=
  rfl

@[simp]
theorem coe_toEquiv_symm : e.toEquiv.symm = e.symm :=
  rfl


variable [module_saM : Module R M₁] {wtf : CoalgebraStruct R M₁}

variable [module_M₃ : Module R M₃] {ffs3 : CoalgebraStruct R M₃}

variable [module_N₁ : Module R N₁] [module_N₂ : Module R N₂] {ffs : CoalgebraStruct R N₁} {ffs2 : CoalgebraStruct R N₂}

variable (e₁₂ : M₁ ≃c[R] M₂) (e₂₃ : M₂ ≃c[R] M₃)

-- Porting note: Lean 4 aggressively removes unused variables declared using `variables`, so
-- we have to list all the variables explicitly here in order to match the Lean 3 signature.
set_option linter.unusedVariables false in
/-- Linear equivalences are transitive. -/
-- Note: the `RingHomCompTriple σ₃₂ σ₂₁ σ₃₁` is unused, but is convenient to carry around
-- implicitly for lemmas like `CoalgEquiv.self_trans_symm`.
@[trans]
def trans
    (e₁₂ : M₁ ≃c[R] M₂) (e₂₃ : M₂ ≃c[R] M₃) : M₁ ≃c[R] M₃ :=
  { e₂₃.toCoalgHom.comp e₁₂.toCoalgHom, e₁₂.toLinearEquiv.trans e₂₃.toLinearEquiv with }

@[simp]
lemma trans_toCoalgHom (e₁₂ : M₁ ≃c[R] M₂) (e₂₃ : M₂ ≃c[R] M₃) :
    e₁₂.trans e₂₃ = e₂₃.toCoalgHom.comp e₁₂.toCoalgHom := rfl

@[simp]
theorem apply_symm_apply (e : M₁ ≃c[R] M₂) : ∀ x, e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply

@[simp]
theorem symm_apply_apply (e : M₁ ≃c[R] M₂) : ∀ x, e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply

@[simp]
theorem symm_trans_apply (e₁ : M₁ ≃c[R] M₂) (e₂ : M₂ ≃c[R] M₃) (x : M₃) :
    (e₁.trans e₂).symm x = e₁.symm (e₂.symm x) :=
  rfl

@[simp]
theorem coe_trans (e₁ : M₁ ≃c[R] M₂) (e₂ : M₂ ≃c[R] M₃) : ⇑(e₁.trans e₂) = e₂ ∘ e₁ :=
  rfl

@[simp]
theorem trans_apply (e₁ : M₁ ≃c[R] M₂) (e₂ : M₂ ≃c[R] M₃) (x : M₁) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

theorem comp_coe (e₁ : M₁ ≃c[R] M₂) (e₂ : M₂ ≃c[R] M₃) :
    CoalgHom.comp e₂.toCoalgHom e₁.toCoalgHom = e₁.trans e₂ := rfl

@[simp]
theorem comp_symm (e : M₁ ≃c[R] M₂) :
    CoalgHom.comp (e : M₁ →c[R] M₂) ↑e.symm = CoalgHom.id R M₂ := by
  ext
  simp

@[simp]
theorem symm_comp (e : M₁ ≃c[R] M₂) :
    CoalgHom.comp ↑e.symm (e : M₁ →c[R] M₂) = CoalgHom.id R M₁ := by
  ext
  simp

@[simp]
theorem self_trans_symm (e : M₁ ≃c[R] M₂) :
    e.trans e.symm = refl _ _ := by
  ext
  simp only [trans_apply, symm_apply_apply, refl_apply]

@[simp]
theorem self_symm_trans (e : M₁ ≃c[R] M₂) :
    e.symm.trans e = refl _ _ := by
  ext
  simp only [trans_apply, apply_symm_apply, refl_apply]

variable {e₁₂} {e₂₃}

end
end AddCommMonoid

/-- Let `A` be an `R`-coalgebra and let `B` be an `R`-module with a `CoalgebraStruct`.
A linear equivalence `A ≃ₗ[R] B` that respects the `CoalgebraStruct`s defines an `R`-coalgebra
structure on `B`. -/
def toCoalgebra [CommSemiring R] {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    [Module R A] [Module R B] [Coalgebra R A] [CoalgebraStruct R B]
    (f : A ≃c[R] B) :
    Coalgebra R B where
  comul := comul
  counit := counit
  coassoc := by
    simp_rw [← (f.toLinearEquiv.comp_toLinearMap_symm_eq _ _).2 f.map_comp_comul,
      ← LinearMap.comp_assoc, LinearMap.lTensor_comp_map, LinearMap.comp_assoc,
      ← symm_toLinearEquiv, ← CoalgHom.comp_toLinearMap, comp_coe, self_trans_symm,
      refl_toCoalgHom, CoalgHom.id_toLinearMap, LinearMap.comp_id,
      ← LinearMap.lTensor_comp_map, ← LinearMap.rTensor_comp_lTensor A f.toLinearMap
      Coalgebra.comul, ← LinearMap.comp_assoc]
    congr 1
    simp_rw [LinearMap.comp_assoc, ← Coalgebra.coassoc]
    simp_rw [← LinearMap.comp_assoc, LinearMap.lTensor_comp_rTensor,
      TensorProduct.map_map_comp_assoc_eq]
    simp_rw [LinearMap.comp_assoc _ (map _ _), LinearMap.map_comp_rTensor, f.map_comp_comul]
    sorry
  rTensor_counit_comp_comul := by sorry
    --have := (f.toLinearEquiv.eq_comp_toLinearMap_symm _ _).2 f.counit_comp
    /-rw [(f.toLinearEquiv.eq_comp_toLinearMap_symm _ _).2 f.counit_comp,
      ← (f.toLinearEquiv.comp_toLinearMap_symm_eq _ _).2 f.map_comp_comul]
    simp only [← LinearMap.comp_assoc, LinearMap.rTensor_comp_map]
    simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.comp_id, ← LinearMap.lTensor_comp_rTensor]
    simp only [← LinearMap.comp_assoc _ Coalgebra.comul, Coalgebra.rTensor_counit_comp_comul]
    ext
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      TensorProduct.mk_apply, LinearMap.lTensor_tmul, LinearEquiv.apply_symm_apply]-/
  lTensor_counit_comp_comul := sorry /-by
      rw [(f.toLinearEquiv.eq_comp_toLinearMap_symm _ _).2 f.counit_comp,
        ← (f.toLinearEquiv.comp_toLinearMap_symm_eq _ _).2 f.map_comp_comul]
      simp only [← LinearMap.comp_assoc, LinearMap.lTensor_comp_map]
      simp only [LinearMap.comp_assoc, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
        LinearEquiv.refl_toLinearMap, LinearMap.comp_id, ← LinearMap.rTensor_comp_lTensor]
      simp only [← LinearMap.comp_assoc _ Coalgebra.comul, Coalgebra.lTensor_counit_comp_comul]
      ext
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.flip_apply,
        TensorProduct.mk_apply, LinearMap.rTensor_tmul, LinearEquiv.apply_symm_apply]
-/
end CoalgEquiv
