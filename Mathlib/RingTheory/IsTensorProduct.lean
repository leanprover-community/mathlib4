/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Module.ULift

#align_import ring_theory.is_tensor_product from "leanprover-community/mathlib"@"c4926d76bb9c5a4a62ed2f03d998081786132105"

/-!
# The characteristic predicate of tensor product

## Main definitions

- `IsTensorProduct`: A predicate on `f : M₁ →ₗ[R] M₂ →ₗ[R] M` expressing that `f` realizes `M` as
  the tensor product of `M₁ ⊗[R] M₂`. This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be
  bijective.
- `IsBaseChange`: A predicate on an `R`-algebra `S` and a map `f : M →ₗ[R] N` with `N` being an
  `S`-module, expressing that `f` realizes `N` as the base change of `M` along `R → S`.
- `Algebra.IsPushout`: A predicate on the following diagram of scalar towers
  ```
    R  →  S
    ↓     ↓
    R' →  S'
  ```
    asserting that is a pushout diagram (i.e. `S' = S ⊗[R] R'`)

## Main results
- `TensorProduct.isBaseChange`: `S ⊗[R] M` is the base change of `M` along `R → S`.

-/


universe u v₁ v₂ v₃ v₄

open TensorProduct

section IsTensorProduct

variable {R : Type*} [CommSemiring R]
variable {M₁ M₂ M M' : Type*}
variable [AddCommMonoid M₁] [AddCommMonoid M₂] [AddCommMonoid M] [AddCommMonoid M']
variable [Module R M₁] [Module R M₂] [Module R M] [Module R M']
variable (f : M₁ →ₗ[R] M₂ →ₗ[R] M)
variable {N₁ N₂ N : Type*} [AddCommMonoid N₁] [AddCommMonoid N₂] [AddCommMonoid N]
variable [Module R N₁] [Module R N₂] [Module R N]
variable {g : N₁ →ₗ[R] N₂ →ₗ[R] N}

/-- Given a bilinear map `f : M₁ →ₗ[R] M₂ →ₗ[R] M`, `IsTensorProduct f` means that
`M` is the tensor product of `M₁` and `M₂` via `f`.
This is defined by requiring the lift `M₁ ⊗[R] M₂ → M` to be bijective.
-/
def IsTensorProduct : Prop :=
  Function.Bijective (TensorProduct.lift f)
#align is_tensor_product IsTensorProduct

variable (R M N) {f}

theorem TensorProduct.isTensorProduct : IsTensorProduct (TensorProduct.mk R M N) := by
  delta IsTensorProduct
  convert_to Function.Bijective (LinearMap.id : M ⊗[R] N →ₗ[R] M ⊗[R] N) using 2
  · apply TensorProduct.ext'
    simp
  · exact Function.bijective_id
#align tensor_product.is_tensor_product TensorProduct.isTensorProduct

variable {R M N}

/-- If `M` is the tensor product of `M₁` and `M₂`, it is linearly equivalent to `M₁ ⊗[R] M₂`. -/
@[simps! apply]
noncomputable def IsTensorProduct.equiv (h : IsTensorProduct f) : M₁ ⊗[R] M₂ ≃ₗ[R] M :=
  LinearEquiv.ofBijective _ h
#align is_tensor_product.equiv IsTensorProduct.equiv

@[simp]
theorem IsTensorProduct.equiv_toLinearMap (h : IsTensorProduct f) :
    h.equiv.toLinearMap = TensorProduct.lift f :=
  rfl
#align is_tensor_product.equiv_to_linear_map IsTensorProduct.equiv_toLinearMap

@[simp]
theorem IsTensorProduct.equiv_symm_apply (h : IsTensorProduct f) (x₁ : M₁) (x₂ : M₂) :
    h.equiv.symm (f x₁ x₂) = x₁ ⊗ₜ x₂ := by
  apply h.equiv.injective
  refine (h.equiv.apply_symm_apply _).trans ?_
  simp
#align is_tensor_product.equiv_symm_apply IsTensorProduct.equiv_symm_apply

/-- If `M` is the tensor product of `M₁` and `M₂`, we may lift a bilinear map `M₁ →ₗ[R] M₂ →ₗ[R] M'`
to a `M →ₗ[R] M'`. -/
noncomputable def IsTensorProduct.lift (h : IsTensorProduct f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M') :
    M →ₗ[R] M' :=
  (TensorProduct.lift f').comp h.equiv.symm.toLinearMap
#align is_tensor_product.lift IsTensorProduct.lift

theorem IsTensorProduct.lift_eq (h : IsTensorProduct f) (f' : M₁ →ₗ[R] M₂ →ₗ[R] M') (x₁ : M₁)
    (x₂ : M₂) : h.lift f' (f x₁ x₂) = f' x₁ x₂ := by
  delta IsTensorProduct.lift
  simp
#align is_tensor_product.lift_eq IsTensorProduct.lift_eq

/-- The tensor product of a pair of linear maps between modules. -/
noncomputable def IsTensorProduct.map (hf : IsTensorProduct f) (hg : IsTensorProduct g)
    (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂) : M →ₗ[R] N :=
  hg.equiv.toLinearMap.comp ((TensorProduct.map i₁ i₂).comp hf.equiv.symm.toLinearMap)
#align is_tensor_product.map IsTensorProduct.map

theorem IsTensorProduct.map_eq (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ →ₗ[R] N₁)
    (i₂ : M₂ →ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) : hf.map hg i₁ i₂ (f x₁ x₂) = g (i₁ x₁) (i₂ x₂) := by
  delta IsTensorProduct.map
  simp
#align is_tensor_product.map_eq IsTensorProduct.map_eq

theorem IsTensorProduct.inductionOn (h : IsTensorProduct f) {C : M → Prop} (m : M) (h0 : C 0)
    (htmul : ∀ x y, C (f x y)) (hadd : ∀ x y, C x → C y → C (x + y)) : C m := by
  rw [← h.equiv.right_inv m]
  generalize h.equiv.invFun m = y
  change C (TensorProduct.lift f y)
  induction y using TensorProduct.induction_on with
  | zero => rwa [map_zero]
  | tmul _ _ =>
    rw [TensorProduct.lift.tmul]
    apply htmul
  | add _ _ _ _ =>
    rw [map_add]
    apply hadd <;> assumption
#align is_tensor_product.induction_on IsTensorProduct.inductionOn

end IsTensorProduct

section IsBaseChange

variable {R : Type*} {M : Type v₁} {N : Type v₂} (S : Type v₃)
variable [AddCommMonoid M] [AddCommMonoid N] [CommSemiring R]
variable [CommSemiring S] [Algebra R S] [Module R M] [Module R N] [Module S N] [IsScalarTower R S N]
variable (f : M →ₗ[R] N)

/-- Given an `R`-algebra `S` and an `R`-module `M`, an `S`-module `N` together with a map
`f : M →ₗ[R] N` is the base change of `M` to `S` if the map `S × M → N, (s, m) ↦ s • f m` is the
tensor product. -/
def IsBaseChange : Prop :=
  IsTensorProduct
    (((Algebra.linearMap S <| Module.End S (M →ₗ[R] N)).flip f).restrictScalars R)
#align is_base_change IsBaseChange

-- Porting note: split `variable`
variable {S f}
variable (h : IsBaseChange S f)
variable {P Q : Type*} [AddCommMonoid P] [Module R P]
variable [AddCommMonoid Q] [Module S Q]

section

variable [Module R Q] [IsScalarTower R S Q]

/-- Suppose `f : M →ₗ[R] N` is the base change of `M` along `R → S`. Then any `R`-linear map from
`M` to an `S`-module factors through `f`. -/
noncomputable nonrec def IsBaseChange.lift (g : M →ₗ[R] Q) : N →ₗ[S] Q :=
  { h.lift
      (((Algebra.linearMap S <| Module.End S (M →ₗ[R] Q)).flip g).restrictScalars R) with
    map_smul' := fun r x => by
      let F := ((Algebra.linearMap S <| Module.End S (M →ₗ[R] Q)).flip g).restrictScalars R
      have hF : ∀ (s : S) (m : M), h.lift F (s • f m) = s • g m := h.lift_eq F
      change h.lift F (r • x) = r • h.lift F x
      apply h.inductionOn x
      · rw [smul_zero, map_zero, smul_zero]
      · intro s m
        change h.lift F (r • s • f m) = r • h.lift F (s • f m)
        rw [← mul_smul, hF, hF, mul_smul]
      · intro x₁ x₂ e₁ e₂
        rw [map_add, smul_add, map_add, smul_add, e₁, e₂] }
#align is_base_change.lift IsBaseChange.lift

nonrec theorem IsBaseChange.lift_eq (g : M →ₗ[R] Q) (x : M) : h.lift g (f x) = g x := by
  have hF : ∀ (s : S) (m : M), h.lift g (s • f m) = s • g m := h.lift_eq _
  convert hF 1 x <;> rw [one_smul]
#align is_base_change.lift_eq IsBaseChange.lift_eq

theorem IsBaseChange.lift_comp (g : M →ₗ[R] Q) : ((h.lift g).restrictScalars R).comp f = g :=
  LinearMap.ext (h.lift_eq g)
#align is_base_change.lift_comp IsBaseChange.lift_comp

end

@[elab_as_elim]
nonrec theorem IsBaseChange.inductionOn (x : N) (P : N → Prop) (h₁ : P 0) (h₂ : ∀ m : M, P (f m))
    (h₃ : ∀ (s : S) (n), P n → P (s • n)) (h₄ : ∀ n₁ n₂, P n₁ → P n₂ → P (n₁ + n₂)) : P x :=
  h.inductionOn x h₁ (fun _ _ => h₃ _ _ (h₂ _)) h₄
#align is_base_change.induction_on IsBaseChange.inductionOn

theorem IsBaseChange.algHom_ext (g₁ g₂ : N →ₗ[S] Q) (e : ∀ x, g₁ (f x) = g₂ (f x)) : g₁ = g₂ := by
  ext x
  refine h.inductionOn x ?_ ?_ ?_ ?_
  · rw [map_zero, map_zero]
  · assumption
  · intro s n e'
    rw [g₁.map_smul, g₂.map_smul, e']
  · intro x y e₁ e₂
    rw [map_add, map_add, e₁, e₂]
#align is_base_change.alg_hom_ext IsBaseChange.algHom_ext

theorem IsBaseChange.algHom_ext' [Module R Q] [IsScalarTower R S Q] (g₁ g₂ : N →ₗ[S] Q)
    (e : (g₁.restrictScalars R).comp f = (g₂.restrictScalars R).comp f) : g₁ = g₂ :=
  h.algHom_ext g₁ g₂ (LinearMap.congr_fun e)
#align is_base_change.alg_hom_ext' IsBaseChange.algHom_ext'

variable (R M N S)

theorem TensorProduct.isBaseChange : IsBaseChange S (TensorProduct.mk R S M 1) := by
  delta IsBaseChange
  convert TensorProduct.isTensorProduct R S M using 1
  ext s x
  change s • (1 : S) ⊗ₜ[R] x = s ⊗ₜ[R] x
  rw [TensorProduct.smul_tmul']
  congr 1
  exact mul_one _
#align tensor_product.is_base_change TensorProduct.isBaseChange

variable {R M N S}

/-- The base change of `M` along `R → S` is linearly equivalent to `S ⊗[R] M`. -/
noncomputable nonrec def IsBaseChange.equiv : S ⊗[R] M ≃ₗ[S] N :=
  { h.equiv with
    map_smul' := fun r x => by
      change h.equiv (r • x) = r • h.equiv x
      refine TensorProduct.induction_on x ?_ ?_ ?_
      · rw [smul_zero, map_zero, smul_zero]
      · intro x y
        -- porting note (#10745): was simp [smul_tmul', Algebra.ofId_apply]
        simp only [Algebra.linearMap_apply, lift.tmul, smul_eq_mul,
          LinearMap.mul_apply, LinearMap.smul_apply, IsTensorProduct.equiv_apply,
          Module.algebraMap_end_apply, _root_.map_mul, smul_tmul', eq_self_iff_true,
          LinearMap.coe_restrictScalars, LinearMap.flip_apply]
      · intro x y hx hy
        rw [map_add, smul_add, map_add, smul_add, hx, hy] }
#align is_base_change.equiv IsBaseChange.equiv

theorem IsBaseChange.equiv_tmul (s : S) (m : M) : h.equiv (s ⊗ₜ m) = s • f m :=
  TensorProduct.lift.tmul s m
#align is_base_change.equiv_tmul IsBaseChange.equiv_tmul

theorem IsBaseChange.equiv_symm_apply (m : M) : h.equiv.symm (f m) = 1 ⊗ₜ m := by
  rw [h.equiv.symm_apply_eq, h.equiv_tmul, one_smul]
#align is_base_change.equiv_symm_apply IsBaseChange.equiv_symm_apply

variable (f)

theorem IsBaseChange.of_lift_unique
    (h : ∀ (Q : Type max v₁ v₂ v₃) [AddCommMonoid Q],
      ∀ [Module R Q] [Module S Q], ∀ [IsScalarTower R S Q],
        ∀ g : M →ₗ[R] Q, ∃! g' : N →ₗ[S] Q, (g'.restrictScalars R).comp f = g) :
    IsBaseChange S f := by
  obtain ⟨g, hg, -⟩ :=
    h (ULift.{v₂} <| S ⊗[R] M)
      (ULift.moduleEquiv.symm.toLinearMap.comp <| TensorProduct.mk R S M 1)
  let f' : S ⊗[R] M →ₗ[R] N :=
    TensorProduct.lift (((LinearMap.flip (AlgHom.toLinearMap (Algebra.ofId S
      (Module.End S (M →ₗ[R] N))))) f).restrictScalars R)
  change Function.Bijective f'
  let f'' : S ⊗[R] M →ₗ[S] N := by
    refine
      { f' with
        map_smul' := fun s x =>
          TensorProduct.induction_on x ?_ (fun s' y => smul_assoc s s' _) fun x y hx hy => ?_ }
    · dsimp; rw [map_zero, smul_zero, map_zero, smul_zero]
    · dsimp at *; rw [smul_add, map_add, map_add, smul_add, hx, hy]
  simp_rw [DFunLike.ext_iff, LinearMap.comp_apply, LinearMap.restrictScalars_apply] at hg
  let fe : S ⊗[R] M ≃ₗ[S] N :=
    LinearEquiv.ofLinear f'' (ULift.moduleEquiv.toLinearMap.comp g) ?_ ?_
  · exact fe.bijective
  · rw [← LinearMap.cancel_left (ULift.moduleEquiv : ULift.{max v₁ v₃} N ≃ₗ[S] N).symm.injective]
    refine (h (ULift.{max v₁ v₃} N) <| ULift.moduleEquiv.symm.toLinearMap.comp f).unique ?_ rfl
    ext x
    simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, hg]
    apply one_smul
  · ext x
    change (g <| (1 : S) • f x).down = _
    rw [one_smul, hg]
    rfl
#align is_base_change.of_lift_unique IsBaseChange.of_lift_unique

variable {f}

theorem IsBaseChange.iff_lift_unique :
    IsBaseChange S f ↔
      ∀ (Q : Type max v₁ v₂ v₃) [AddCommMonoid Q],
        ∀ [Module R Q] [Module S Q],
          ∀ [IsScalarTower R S Q],
            ∀ g : M →ₗ[R] Q, ∃! g' : N →ₗ[S] Q, (g'.restrictScalars R).comp f = g :=
  ⟨fun h => by
    intros Q _ _ _ _ g
    exact ⟨h.lift g, h.lift_comp g, fun g' e => h.algHom_ext' _ _ (e.trans (h.lift_comp g).symm)⟩,
    IsBaseChange.of_lift_unique f⟩
#align is_base_change.iff_lift_unique IsBaseChange.iff_lift_unique

theorem IsBaseChange.ofEquiv (e : M ≃ₗ[R] N) : IsBaseChange R e.toLinearMap := by
  apply IsBaseChange.of_lift_unique
  intro Q I₁ I₂ I₃ I₄ g
  have : I₂ = I₃ := by
    ext r q
    show (by let _ := I₂; exact r • q) = (by let _ := I₃; exact r • q)
    dsimp
    rw [← one_smul R q, smul_smul, ← @smul_assoc _ _ _ (id _) (id _) (id _) I₄, smul_eq_mul]
  cases this
  refine
    ⟨g.comp e.symm.toLinearMap, by
      ext
      simp, ?_⟩
  rintro y (rfl : _ = _)
  ext
  simp
#align is_base_change.of_equiv IsBaseChange.ofEquiv

variable {T O : Type*} [CommSemiring T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable [AddCommMonoid O] [Module R O] [Module S O] [Module T O] [IsScalarTower S T O]
variable [IsScalarTower R S O] [IsScalarTower R T O]

theorem IsBaseChange.comp {f : M →ₗ[R] N} (hf : IsBaseChange S f) {g : N →ₗ[S] O}
    (hg : IsBaseChange T g) : IsBaseChange T ((g.restrictScalars R).comp f) := by
  apply IsBaseChange.of_lift_unique
  intro Q _ _ _ _ i
  letI := Module.compHom Q (algebraMap S T)
  haveI : IsScalarTower S T Q :=
    ⟨fun x y z => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  have : IsScalarTower R S Q := by
    refine ⟨fun x y z => ?_⟩
    change (IsScalarTower.toAlgHom R S T) (x • y) • z = x • algebraMap S T y • z
    rw [AlgHom.map_smul, smul_assoc]
    rfl
  refine
    ⟨hg.lift (hf.lift i), by
      ext
      simp [IsBaseChange.lift_eq], ?_⟩
  rintro g' (e : _ = _)
  refine hg.algHom_ext' _ _ (hf.algHom_ext' _ _ ?_)
  rw [IsBaseChange.lift_comp, IsBaseChange.lift_comp, ← e]
  ext
  rfl
#align is_base_change.comp IsBaseChange.comp

variable {R' S' : Type*} [CommSemiring R'] [CommSemiring S']
variable [Algebra R R'] [Algebra S S'] [Algebra R' S'] [Algebra R S']
variable [IsScalarTower R R' S'] [IsScalarTower R S S']

open IsScalarTower (toAlgHom)

variable (R S R' S')

/-- A type-class stating that the following diagram of scalar towers
R  →  S
↓     ↓
R' →  S'
is a pushout diagram (i.e. `S' = S ⊗[R] R'`)
-/
@[mk_iff]
class Algebra.IsPushout : Prop where
  out : IsBaseChange S (toAlgHom R R' S').toLinearMap
#align algebra.is_pushout Algebra.IsPushout

variable {R S R' S'}

@[symm]
theorem Algebra.IsPushout.symm (h : Algebra.IsPushout R S R' S') : Algebra.IsPushout R R' S S' := by
  let _ := (Algebra.TensorProduct.includeRight : R' →ₐ[R] S ⊗ R').toRingHom.toAlgebra
  let e : R' ⊗[R] S ≃ₗ[R'] S' := by
    refine { (_root_.TensorProduct.comm R R' S).trans <|
      h.1.equiv.restrictScalars R with map_smul' := ?_ }
    intro r x
    change
      h.1.equiv (TensorProduct.comm R R' S (r • x)) = r • h.1.equiv (TensorProduct.comm R R' S x)
    refine TensorProduct.induction_on x ?_ ?_ ?_
    · simp only [smul_zero, map_zero]
    · intro x y
      simp only [smul_tmul', smul_eq_mul, TensorProduct.comm_tmul, smul_def,
        TensorProduct.algebraMap_apply, id.map_eq_id, RingHom.id_apply, TensorProduct.tmul_mul_tmul,
        one_mul, h.1.equiv_tmul, AlgHom.toLinearMap_apply, _root_.map_mul,
        IsScalarTower.coe_toAlgHom']
      ring
    · intro x y hx hy
      rw [map_add, map_add, smul_add, map_add, map_add, hx, hy, smul_add]
  have :
    (toAlgHom R S S').toLinearMap =
      (e.toLinearMap.restrictScalars R).comp (TensorProduct.mk R R' S 1) := by
    ext
    simp [h.1.equiv_tmul, Algebra.smul_def]
  constructor
  rw [this]
  exact (TensorProduct.isBaseChange R S R').comp (IsBaseChange.ofEquiv e)
#align algebra.is_pushout.symm Algebra.IsPushout.symm

variable (R S R' S')

theorem Algebra.IsPushout.comm : Algebra.IsPushout R S R' S' ↔ Algebra.IsPushout R R' S S' :=
  ⟨Algebra.IsPushout.symm, Algebra.IsPushout.symm⟩
#align algebra.is_pushout.comm Algebra.IsPushout.comm

variable {R S R'}

attribute [local instance] Algebra.TensorProduct.rightAlgebra

instance TensorProduct.isPushout {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] : Algebra.IsPushout R S T (TensorProduct R S T) :=
  ⟨TensorProduct.isBaseChange R T S⟩
#align tensor_product.is_pushout TensorProduct.isPushout

instance TensorProduct.isPushout' {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] : Algebra.IsPushout R T S (TensorProduct R S T) :=
  Algebra.IsPushout.symm inferInstance
#align tensor_product.is_pushout' TensorProduct.isPushout'

/-- If `S' = S ⊗[R] R'`, then any pair of `R`-algebra homomorphisms `f : S → A` and `g : R' → A`
such that `f x` and `g y` commutes for all `x, y` descends to a (unique) homomorphism `S' → A`.
-/
@[simps! (config := .lemmasOnly) apply]
noncomputable def Algebra.pushoutDesc [H : Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (hf : ∀ x y, f x * g y = g y * f x) :
    S' →ₐ[R] A := by
  letI := Module.compHom A f.toRingHom
  haveI : IsScalarTower R S A :=
    { smul_assoc := fun r s a =>
        show f (r • s) * a = r • (f s * a) by rw [f.map_smul, smul_mul_assoc] }
  haveI : IsScalarTower S A A := { smul_assoc := fun r a b => mul_assoc _ _ _ }
  have : ∀ x, H.out.lift g.toLinearMap (algebraMap R' S' x) = g x := H.out.lift_eq _
  refine AlgHom.ofLinearMap ((H.out.lift g.toLinearMap).restrictScalars R) ?_ ?_
  · dsimp only [LinearMap.restrictScalars_apply]
    rw [← (algebraMap R' S').map_one, this, g.map_one]
  · intro x y
    refine H.out.inductionOn x ?_ ?_ ?_ ?_
    · rw [zero_mul, map_zero, zero_mul]
    rotate_left
    · intro s s' e
      dsimp only [LinearMap.restrictScalars_apply] at e ⊢
      rw [LinearMap.map_smul, smul_mul_assoc, LinearMap.map_smul, e, smul_mul_assoc]
    · intro s s' e₁ e₂
      dsimp only [LinearMap.restrictScalars_apply] at e₁ e₂ ⊢
      rw [add_mul, map_add, map_add, add_mul, e₁, e₂]
    intro x
    dsimp
    rw [this]
    refine H.out.inductionOn y ?_ ?_ ?_ ?_
    · rw [mul_zero, map_zero, mul_zero]
    · intro y
      dsimp
      rw [← _root_.map_mul, this, this, _root_.map_mul]
    · intro s s' e
      rw [mul_comm, smul_mul_assoc, LinearMap.map_smul, LinearMap.map_smul, mul_comm, e]
      change f s * (g x * _) = g x * (f s * _)
      rw [← mul_assoc, ← mul_assoc, hf]
    · intro s s' e₁ e₂
      rw [mul_add, map_add, map_add, mul_add, e₁, e₂]
#align algebra.pushout_desc Algebra.pushoutDesc

@[simp]
theorem Algebra.pushoutDesc_left [H : Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) (x : S) :
    Algebra.pushoutDesc S' f g H (algebraMap S S' x) = f x := by
  letI := Module.compHom A f.toRingHom
  haveI : IsScalarTower R S A :=
    { smul_assoc := fun r s a =>
        show f (r • s) * a = r • (f s * a) by rw [f.map_smul, smul_mul_assoc] }
  haveI : IsScalarTower S A A := { smul_assoc := fun r a b => mul_assoc _ _ _ }
  rw [Algebra.algebraMap_eq_smul_one, pushoutDesc_apply, map_smul, ←
    Algebra.pushoutDesc_apply S' f g H, _root_.map_one]
  exact mul_one (f x)
#align algebra.pushout_desc_left Algebra.pushoutDesc_left

theorem Algebra.lift_algHom_comp_left [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) :
    (Algebra.pushoutDesc S' f g H).comp (toAlgHom R S S') = f :=
  AlgHom.ext fun x => (Algebra.pushoutDesc_left S' f g H x : _)
#align algebra.lift_alg_hom_comp_left Algebra.lift_algHom_comp_left

@[simp]
theorem Algebra.pushoutDesc_right [H : Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) (x : R') :
    Algebra.pushoutDesc S' f g H (algebraMap R' S' x) = g x :=
  letI := Module.compHom A f.toRingHom
  haveI : IsScalarTower R S A :=
    { smul_assoc := fun r s a =>
        show f (r • s) * a = r • (f s * a) by rw [f.map_smul, smul_mul_assoc] }
  IsBaseChange.lift_eq _ _ _
#align algebra.pushout_desc_right Algebra.pushoutDesc_right

theorem Algebra.lift_algHom_comp_right [Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] (f : S →ₐ[R] A) (g : R' →ₐ[R] A) (H) :
    (Algebra.pushoutDesc S' f g H).comp (toAlgHom R R' S') = g :=
  AlgHom.ext fun x => (Algebra.pushoutDesc_right S' f g H x : _)
#align algebra.lift_alg_hom_comp_right Algebra.lift_algHom_comp_right

@[ext]
theorem Algebra.IsPushout.algHom_ext [H : Algebra.IsPushout R S R' S'] {A : Type*} [Semiring A]
    [Algebra R A] {f g : S' →ₐ[R] A} (h₁ : f.comp (toAlgHom R R' S') = g.comp (toAlgHom R R' S'))
    (h₂ : f.comp (toAlgHom R S S') = g.comp (toAlgHom R S S')) : f = g := by
  ext x
  refine H.1.inductionOn x ?_ ?_ ?_ ?_
  · simp only [map_zero]
  · exact AlgHom.congr_fun h₁
  · intro s s' e
    rw [Algebra.smul_def, f.map_mul, g.map_mul, e]
    congr 1
    exact (AlgHom.congr_fun h₂ s : _)
  · intro s₁ s₂ e₁ e₂
    rw [map_add, map_add, e₁, e₂]
#align algebra.is_pushout.alg_hom_ext Algebra.IsPushout.algHom_ext

end IsBaseChange
