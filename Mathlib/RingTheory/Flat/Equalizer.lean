/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.SnakeLemma

/-!
# Base change along flat modules preserves equalizers

We show that base change along flat modules (resp. algebras)
preserves kernels and equalizers.

-/

@[expose] public section

universe t u

noncomputable section

open TensorProduct

variable {R : Type*} (S : Type*) [CommRing R] [CommRing S] [Algebra R S]

section Module

variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable {N P : Type*} [AddCommGroup N] [AddCommGroup P] [Module R N] [Module R P]
  (f g : N →ₗ[R] P)

lemma Module.Flat.ker_lTensor_eq [Module.Flat R M] :
    LinearMap.ker (AlgebraTensorModule.lTensor S M f) =
      LinearMap.range (AlgebraTensorModule.lTensor S M (LinearMap.ker f).subtype) := by
  rw [← LinearMap.exact_iff]
  exact Module.Flat.lTensor_exact M (LinearMap.exact_subtype_ker_map f)

lemma Module.Flat.eqLocus_lTensor_eq [Module.Flat R M] :
    LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f)
      (AlgebraTensorModule.lTensor S M g) =
      LinearMap.range (AlgebraTensorModule.lTensor S M (LinearMap.eqLocus f g).subtype) := by
  rw [LinearMap.eqLocus_eq_ker_sub, LinearMap.eqLocus_eq_ker_sub]
  rw [← map_sub, ker_lTensor_eq]

/-- The bilinear map corresponding to `LinearMap.tensorEqLocus`. -/
def LinearMap.tensorEqLocusBil :
    M →ₗ[S] LinearMap.eqLocus f g →ₗ[R]
      LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f)
        (AlgebraTensorModule.lTensor S M g) where
  toFun m :=
    { toFun := fun a ↦ ⟨m ⊗ₜ a, by simp [show f a = g a from a.property]⟩
      map_add' := fun x y ↦ by simp [tmul_add]
      map_smul' := fun r x ↦ by simp }
  map_add' x y := by
    ext
    simp [add_tmul]
  map_smul' r x := by
    ext
    simp [smul_tmul']

/-- The bilinear map corresponding to `LinearMap.tensorKer`. -/
def LinearMap.tensorKerBil :
    M →ₗ[S] LinearMap.ker f →ₗ[R] LinearMap.ker (AlgebraTensorModule.lTensor S M f) where
  toFun m :=
    { toFun := fun a ↦ ⟨m ⊗ₜ a, by simp⟩
      map_add' := fun x y ↦ by simp [tmul_add]
      map_smul' := fun r x ↦ by simp }
  map_add' x y := by ext; simp [add_tmul]
  map_smul' r x := by ext y; simp [smul_tmul']

/-- The canonical map `M ⊗[R] eq(f, g) →ₗ[R] eq(𝟙 ⊗ f, 𝟙 ⊗ g)`. -/
def LinearMap.tensorEqLocus : M ⊗[R] (LinearMap.eqLocus f g) →ₗ[S]
    LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M g) :=
  AlgebraTensorModule.lift (tensorEqLocusBil S M f g)

/-- The canonical map `M ⊗[R] ker f →ₗ[R] ker (𝟙 ⊗ f)`. -/
def LinearMap.tensorKer : M ⊗[R] (LinearMap.ker f) →ₗ[S]
    LinearMap.ker (AlgebraTensorModule.lTensor S M f) :=
  AlgebraTensorModule.lift (f.tensorKerBil S M)

@[simp]
lemma LinearMap.tensorKer_tmul (m : M) (x : LinearMap.ker f) :
    (tensorKer S M f (m ⊗ₜ[R] x) : M ⊗[R] N) = m ⊗ₜ[R] (x : N) :=
  rfl

@[simp]
lemma LinearMap.tensorKer_coe (x : M ⊗[R] (LinearMap.ker f)) :
    (tensorKer S M f x : M ⊗[R] N) = (ker f).subtype.lTensor M x := by
  induction x <;> simp_all

@[simp]
lemma LinearMap.tensorEqLocus_tmul (m : M) (x : LinearMap.eqLocus f g) :
    (tensorEqLocus S M f g (m ⊗ₜ[R] x) : M ⊗[R] N) = m ⊗ₜ[R] (x : N) :=
  rfl

@[simp]
lemma LinearMap.tensorEqLocus_coe (x : M ⊗[R] (LinearMap.eqLocus f g)) :
    (tensorEqLocus S M f g x : M ⊗[R] N) = (eqLocus f g).subtype.lTensor M x := by
  induction x <;> simp_all

set_option backward.privateInPublic true in
private def LinearMap.tensorKerInv [Module.Flat R M] :
    ker (AlgebraTensorModule.lTensor S M f) →ₗ[S] M ⊗[R] (ker f) :=
  LinearMap.codRestrictOfInjective (LinearMap.ker (AlgebraTensorModule.lTensor S M f)).subtype
    (AlgebraTensorModule.lTensor S M (ker f).subtype)
    (Module.Flat.lTensor_preserves_injective_linearMap (ker f).subtype
      (ker f).injective_subtype) (by simp [Module.Flat.ker_lTensor_eq])

@[simp]
private lemma LinearMap.lTensor_ker_subtype_tensorKerInv [Module.Flat R M]
    (x : ker (AlgebraTensorModule.lTensor S M f)) :
    (lTensor M (ker f).subtype) ((tensorKerInv S M f) x) = x := by
  rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  simp [LinearMap.tensorKerInv]

set_option backward.privateInPublic true in
private def LinearMap.tensorEqLocusInv [Module.Flat R M] :
    eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M g) →ₗ[S]
      M ⊗[R] (eqLocus f g) :=
  LinearMap.codRestrictOfInjective
    (LinearMap.eqLocus (AlgebraTensorModule.lTensor S M f)
      (AlgebraTensorModule.lTensor S M g)).subtype
    (AlgebraTensorModule.lTensor S M (eqLocus f g).subtype)
    (Module.Flat.lTensor_preserves_injective_linearMap (eqLocus f g).subtype
      (eqLocus f g).injective_subtype) (by simp [Module.Flat.eqLocus_lTensor_eq])

@[simp]
private lemma LinearMap.lTensor_eqLocus_subtype_tensorEqLocusInv [Module.Flat R M]
    (x : eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M g)) :
    (lTensor M (eqLocus f g).subtype) (tensorEqLocusInv S M f g x) = x := by
  rw [← AlgebraTensorModule.coe_lTensor (A := S)]
  simp [LinearMap.tensorEqLocusInv]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `M` is `R`-flat, the canonical map `M ⊗[R] ker f →ₗ[R] ker (𝟙 ⊗ f)` is an isomorphism. -/
def LinearMap.tensorKerEquiv [Module.Flat R M] :
    M ⊗[R] LinearMap.ker f ≃ₗ[S] LinearMap.ker (AlgebraTensorModule.lTensor S M f) :=
  LinearEquiv.ofLinear (LinearMap.tensorKer S M f) (LinearMap.tensorKerInv S M f)
    (by ext x; simp)
    (by
      ext m x
      apply (Module.Flat.lTensor_preserves_injective_linearMap (ker f).subtype
        (ker f).injective_subtype)
      simp)

@[simp]
lemma LinearMap.tensorKerEquiv_apply [Module.Flat R M] (x : M ⊗[R] ker f) :
    tensorKerEquiv S M f x = tensorKer S M f x :=
  rfl

@[simp]
lemma LinearMap.lTensor_ker_subtype_tensorKerEquiv_symm [Module.Flat R M]
    (x : ker (AlgebraTensorModule.lTensor S M f)) :
    (lTensor M (ker f).subtype) ((tensorKerEquiv S M f).symm x) = x :=
  lTensor_ker_subtype_tensorKerInv S M f x

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `M` is `R`-flat, the canonical map `M ⊗[R] eq(f, g) →ₗ[S] eq (𝟙 ⊗ f, 𝟙 ⊗ g)` is an
isomorphism. -/
def LinearMap.tensorEqLocusEquiv [Module.Flat R M] :
    M ⊗[R] eqLocus f g ≃ₗ[S]
      eqLocus (AlgebraTensorModule.lTensor S M f)
        (AlgebraTensorModule.lTensor S M g) :=
  LinearEquiv.ofLinear (LinearMap.tensorEqLocus S M f g) (LinearMap.tensorEqLocusInv S M f g)
    (by ext; simp)
    (by
      ext m x
      apply (Module.Flat.lTensor_preserves_injective_linearMap (eqLocus f g).subtype
        (eqLocus f g).injective_subtype)
      simp)

@[simp]
lemma LinearMap.tensorEqLocusEquiv_apply [Module.Flat R M] (x : M ⊗[R] LinearMap.eqLocus f g) :
    LinearMap.tensorEqLocusEquiv S M f g x = LinearMap.tensorEqLocus S M f g x :=
  rfl

@[simp]
lemma LinearMap.lTensor_eqLocus_subtype_tensoreqLocusEquiv_symm [Module.Flat R M]
    (x : eqLocus (AlgebraTensorModule.lTensor S M f) (AlgebraTensorModule.lTensor S M g)) :
    (lTensor M (eqLocus f g).subtype) ((tensorEqLocusEquiv S M f g).symm x) = x :=
  lTensor_eqLocus_subtype_tensorEqLocusInv S M f g x

variable {M}

/--
Given a short exact sequence `0 → M → N → P → 0` with `P` flat,
then any `A ⊗ M → A ⊗ N` is injective.
-/
lemma LinearMap.lTensor_injective_of_exact_of_flat [Module.Flat R P]
    (f : N →ₗ[R] P) (hf : Function.Surjective f) (g : M →ₗ[R] N) (hg : Function.Injective g)
    (H : Function.Exact g f) (A : Type*) [AddCommGroup A] [Module R A] :
    Function.Injective (g.lTensor A) := by
/-
The proof is taking a resolution `0 → K → Q → A → 0` with `Q` flat,
and applying snake lemma on the following diagram to
```
                      0
                      ↓
    K ⊗ M → K ⊗ N → K ⊗ P → 0
      ↓       ↓       ↓
0 → Q ⊗ M → Q ⊗ N → Q ⊗ P
      ↓       ↓
    A ⊗ M → A ⊗ N
      ↓       ↓
      0       0
```
to get `0 → A ⊗ K → A ⊗ M` exact.
-/
  let Q := A →₀ R
  let π : Q →ₗ[R] A := Finsupp.linearCombination R fun a ↦ a
  have hπ : Function.Surjective π := Finsupp.linearCombination_surjective _ Function.surjective_id
  let K := LinearMap.ker π
  have := SnakeLemma.exact_δ'_left (K.subtype.rTensor M) (K.subtype.rTensor N) (K.subtype.rTensor P)
    (g.lTensor K) (f.lTensor K) (lTensor_exact K H hf) (g.lTensor Q) (f.lTensor Q)
    (lTensor_exact Q H hf) (by simp) (by simp) (K₃ := Unit) 0
    (by simpa using Module.Flat.rTensor_preserves_injective_linearMap _ K.subtype_injective)
    (π.rTensor M) (rTensor_exact _ (exact_subtype_ker_map π) hπ) (π.rTensor N)
    (rTensor_exact _ (exact_subtype_ker_map π) hπ) (lTensor_surjective K hf)
    (Module.Flat.lTensor_preserves_injective_linearMap _ hg) (g.lTensor A)
    (by simp) (rTensor_surjective _ hπ)
  rw [Subsingleton.elim (SnakeLemma.δ' ..) 0] at this
  simpa using this

/-- Given surjection `f : N → P` with `P` flat, then `A ⊗ ker f ≃ ker (A ⊗ f)`.
Also see `LinearMap.tensorKerEquiv` for the version with `A` flat instead. -/
def LinearMap.kerLTensorEquivOfSurjective [Module.Flat R P]
    (f : N →ₗ[R] P) (hf : Function.Surjective f) (A : Type*) [AddCommGroup A] [Module R A] :
    LinearMap.ker (f.lTensor A) ≃ₗ[R] A ⊗[R] LinearMap.ker f := by
  refine .ofEq _ _ ?_ ≪≫ₗ (LinearEquiv.ofInjective _ (LinearMap.lTensor_injective_of_exact_of_flat
    f hf _ (LinearMap.ker f).subtype_injective (LinearMap.exact_subtype_ker_map _) _)).symm
  rw [LinearMap.exact_iff.mp (lTensor_exact _ (LinearMap.exact_subtype_ker_map _) hf)]

@[simp]
lemma LinearMap.tensorKerEquivOfSurjective_symm_tmul [Module.Flat R P]
    (f : N →ₗ[R] P) (hf : Function.Surjective f) (A : Type*) [AddCommGroup A] [Module R A] (a y) :
    ((f.kerLTensorEquivOfSurjective hf A).symm (a ⊗ₜ y)).1 = a ⊗ₜ y.1 := rfl

end Module

section Algebra

variable (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (f g : A →ₐ[R] B)

set_option backward.privateInPublic true in
private def AlgHom.tensorEqualizerAux :
    T ⊗[R] AlgHom.equalizer f g →ₗ[S]
      AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f)
        (Algebra.TensorProduct.map (AlgHom.id S T) g) :=
  LinearMap.tensorEqLocus S T (f : A →ₗ[R] B) (g : A →ₗ[R] B)

private local instance : AddHomClass (A →ₐ[R] B) A B := inferInstance

@[simp]
private lemma AlgHom.coe_tensorEqualizerAux (x : T ⊗[R] AlgHom.equalizer f g) :
    (AlgHom.tensorEqualizerAux S T f g x : T ⊗[R] A) =
      Algebra.TensorProduct.map (AlgHom.id S T) (AlgHom.equalizer f g).val x := by
  induction x with
  | zero => rfl
  | tmul => rfl
  | add x y hx hy => simp [hx, hy]

set_option backward.privateInPublic true in
private lemma AlgHom.tensorEqualizerAux_mul (x y : T ⊗[R] AlgHom.equalizer f g) :
    AlgHom.tensorEqualizerAux S T f g (x * y) =
      AlgHom.tensorEqualizerAux S T f g x *
        AlgHom.tensorEqualizerAux S T f g y := by
  apply Subtype.ext
  rw [AlgHom.coe_tensorEqualizerAux]
  simp

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The canonical map `T ⊗[R] eq(f, g) →ₐ[S] eq (𝟙 ⊗ f, 𝟙 ⊗ g)`. -/
def AlgHom.tensorEqualizer :
    T ⊗[R] AlgHom.equalizer f g →ₐ[S]
      AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f)
        (Algebra.TensorProduct.map (AlgHom.id S T) g) :=
  AlgHom.ofLinearMap (AlgHom.tensorEqualizerAux S T f g)
    rfl (AlgHom.tensorEqualizerAux_mul S T f g)

@[simp]
lemma AlgHom.coe_tensorEqualizer (x : T ⊗[R] AlgHom.equalizer f g) :
    (AlgHom.tensorEqualizer S T f g x : T ⊗[R] A) =
      Algebra.TensorProduct.map (AlgHom.id S T) (AlgHom.equalizer f g).val x :=
  AlgHom.coe_tensorEqualizerAux S T f g x

#adaptation_note /-- After nightly-2026-02-23 we need this to avoid timeouts. -/
set_option backward.whnf.reducibleClassField false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- If `T` is `R`-flat, the canonical map
`T ⊗[R] eq(f, g) →ₐ[S] eq (𝟙 ⊗ f, 𝟙 ⊗ g)` is an isomorphism. -/
def AlgHom.tensorEqualizerEquiv [Module.Flat R T] :
    T ⊗[R] AlgHom.equalizer f g ≃ₐ[S]
      AlgHom.equalizer (Algebra.TensorProduct.map (AlgHom.id S T) f)
        (Algebra.TensorProduct.map (AlgHom.id S T) g) :=
  AlgEquiv.ofLinearEquiv (LinearMap.tensorEqLocusEquiv S T f.toLinearMap g.toLinearMap)
    rfl (AlgHom.tensorEqualizerAux_mul S T f g)

@[simp]
lemma AlgHom.tensorEqualizerEquiv_apply [Module.Flat R T]
    (x : T ⊗[R] AlgHom.equalizer f g) :
    AlgHom.tensorEqualizerEquiv S T f g x = AlgHom.tensorEqualizer S T f g x :=
  rfl

#adaptation_note /-- After nightly-2026-02-23 this requires more heartbeats. -/
set_option maxHeartbeats 400000 in -- see note
variable (R A) in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
Given a surjection of `R`-algebras `S → T` with kernel `I`, such that `T` is flat,
the kernel of the map `A ⊗ S → A ⊗ T` is the base change of `I` along `S → A ⊗ S`.
-/
def Algebra.kerTensorProductMapIdToAlgHomEquiv
    [Module.Flat R T] (h₁ : Function.Surjective (algebraMap S T)) :
    RingHom.ker (Algebra.TensorProduct.map (.id A A) (IsScalarTower.toAlgHom R S T)) ≃ₗ[A ⊗[R] S]
      (A ⊗[R] S) ⊗[S] (RingHom.ker (algebraMap S T)) := by
  let φ : A ⊗[R] S →ₐ[A] A ⊗[R] T :=
    Algebra.TensorProduct.map (.id _ _) (IsScalarTower.toAlgHom _ _ _)
  let ePp : A ⊗[R] S ≃ₐ[S] S ⊗[R] A :=
    { __ := Algebra.TensorProduct.comm _ _ _, commutes' _ := rfl }
  let e₃ : (RingHom.ker φ) ≃ₗ[R] A ⊗[R] (RingHom.ker (algebraMap S T)) :=
    (LinearMap.kerLTensorEquivOfSurjective (IsScalarTower.toAlgHom R S T).toLinearMap
      h₁ A).restrictScalars R
  let e₄' : (RingHom.ker φ) ≃ₗ[R] (A ⊗[R] S) ⊗[S] (RingHom.ker (algebraMap S T)) :=
    e₃ ≪≫ₗ _root_.TensorProduct.comm _ _ _ ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange _ _ S _ _).symm.restrictScalars R ≪≫ₗ
      (AlgebraTensorModule.congr (.refl S _) ePp.symm.toLinearEquiv).restrictScalars R ≪≫ₗ
      (_root_.TensorProduct.comm _ _ _).restrictScalars R
  let e₄ : (A ⊗[R] S) ⊗[S] (RingHom.ker (algebraMap S T)) ≃ₗ[A ⊗[R] S] (RingHom.ker φ) :=
    { __ := e₄'.symm, map_smul' r' x := by
        dsimp
        induction x with
        | zero => simp only [smul_zero, LinearEquiv.map_zero]
        | add x y _ _ => simp only [smul_add, LinearEquiv.map_add, *]
        | tmul x y =>
        induction x with
        | zero => simp only [zero_tmul, smul_zero, LinearEquiv.map_zero]
        | add x y _ _ => simp only [smul_add, add_tmul, LinearEquiv.map_add, *]
        | tmul x z =>
        induction r' with
        | zero => simp only [zero_smul, LinearEquiv.map_zero]
        | add x y _ _ => simp only [add_smul, LinearEquiv.map_add, *]
        | tmul r s =>
        rw [smul_tmul']
        ext1
        dsimp [e₄', ePp, φ]
        change ((r * x) ⊗ₜ[R] ((s * z) * y.1)) = (r ⊗ₜ[R] s) * (x ⊗ₜ[R] (z * y.1))
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_assoc] }
  exact e₄.symm

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
@[simp]
lemma Algebra.kerTensorProductMapIdToAlgHomEquiv_symm_apply [Module.Flat R T]
    (h₁ : Function.Surjective (algebraMap S T)) (x y z) :
    ((kerTensorProductMapIdToAlgHomEquiv R S T A h₁).symm ((x ⊗ₜ y) ⊗ₜ z)).1 =
      x ⊗ₜ (y * z.1) := rfl

end Algebra
