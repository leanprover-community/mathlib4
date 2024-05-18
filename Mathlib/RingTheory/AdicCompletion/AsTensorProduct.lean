/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Mathlib.RingTheory.Flat.Algebra

/-!

# Adic completion as tensor product

In this file we examine properties of the natural map

`AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M`.

We show

- it is an isomorphism if `M = R^n`.
- it is surjective, if `M` is a finite `R`-module.
- it is an isomorphism if `M` is a finite `R`-module and `R` is Noetherian.

As a corollary we obtain

- if `R` is Noetherian, `AdicCompletion I R` is a flat `R`-algebra.

-/

section

variable (R : Type*) [CommRing R]

section

variable (ι : Type*) [Fintype ι] (M : ι → Type*) [∀ i, AddCommMonoid (M i)]
  [∀ i, Module R (M i)]
variable (N : Type*) [AddCommMonoid N] [Module R N]

/-- The product over a finite type satisfies the universal property of the sum. -/
def Pi.toModule (φ : ∀ (i : ι), M i →ₗ[R] N) : ((i : ι) → M i) →ₗ[R] N where
  toFun x := Finset.sum (Finset.univ) (fun i ↦ φ i (x i))
  map_add' x y := by
    simp only [add_apply, map_add, Finset.sum_add_distrib]
  map_smul' r x := by
    simp only [smul_apply, LinearMapClass.map_smul, RingHom.id_apply, Finset.smul_sum]

open TensorProduct

--def TensorProduct.finRightScalarHom (n : ℕ) :
--    A ⊗[R] ((i : ι) → M i) →ₗ[A] (i : ι) → M i where

end

open TensorProduct

variable (A : Type*) [CommRing A] [Algebra R A]

private noncomputable def TensorProduct.finRightScalarHom (n : ℕ) :
    A ⊗[R] (Fin n → R) →ₗ[A] (Fin n → A) :=
  AlgHom.toLinearMap <| Algebra.TensorProduct.lift
    (Algebra.ofId A (Fin n → A))
    (AlgHom.compLeft (Algebra.ofId R A) (Fin n))
    (by intro x y; rw [commute_iff_eq, mul_comm])

@[simp]
lemma TensorProduct.finRightScalarHom_tmul (n : ℕ) (a : A) (x : Fin n → R) :
    (finRightScalarHom R A n) (a ⊗ₜ[R] x) = (fun i ↦ x i • a) := by
  ext i
  simp [finRightScalarHom]
  rw [mul_comm]
  change algebraMap R A (x i) * a = x i • a
  rw [← _root_.Algebra.smul_def]

--private noncomputable def TensorProduct.finRightScalarInv (n : ℕ) :
--    (Fin n → A) →ₐ[A] A ⊗[R] (Fin n → R) where
--  toFun x := Finset.sum Finset.univ (fun i ↦ x i ⊗ₜ Pi.single i 1)
--  map_one' := by
--    simp only [Pi.one_apply]
--    rw [← TensorProduct.tmul_sum 1, Finset.univ_sum_single]
--    rfl

private noncomputable def TensorProduct.finRightScalarInv (n : ℕ) :
    (Fin n → A) →ₗ[A] A ⊗[R] (Fin n → R) where
  toFun x := Finset.sum Finset.univ (fun i ↦ x i ⊗ₜ Pi.single i 1)
  map_add' x y := by
    simp only [Pi.add_apply, ← Finset.sum_add_distrib, TensorProduct.add_tmul]
  map_smul' r x := by
    rw [Finset.smul_sum]
    simp
    rfl

@[simp]
lemma finRightScalarInv_single (n : ℕ) (a : A) (i : Fin n) :
    finRightScalarInv R A n (Pi.single i a) = a ⊗ₜ Pi.single i 1 := by
  dsimp [finRightScalarInv]
  let f (j : Fin n) : A ⊗[R] (Fin n → R) := a ⊗ₜ[R] Pi.single j 1
  have h (j : Fin n) :
      (if j = i then a else 0) ⊗ₜ[R] (Pi.single j 1) = (if j = i then f j else 0) := by
    split <;> simp
  simp only [Pi.single_apply, h, Fintype.sum_ite_eq']

set_option synthInstance.maxHeartbeats 50000

noncomputable def TensorProduct.finRightScalar (n : ℕ) : A ⊗[R] (Fin n → R) ≃ₗ[A] Fin n → A :=
  LinearEquiv.ofLinear
    (finRightScalarHom R A n)
    (finRightScalarInv R A n)
    (by
      ext i j
      simp
      rw [Pi.single_apply, Pi.single_apply]
      split <;> simp
      )
    (by
      ext i
      simp
      have h : (fun j ↦ ((Pi.single i (1 : R) : Fin n → R) j) • (1 : A)) = Pi.single i (1 : A) := by
        ext j
        rw [Pi.single_apply, Pi.single_apply]
        split <;> simp
      rw [h]
      simp)

@[simp]
theorem TensorProduct.finRightScalar_tmul (n : ℕ) (a : A) (x : Fin n → R) :
    (finRightScalar R A n) (a ⊗ₜ[R] x) = (fun i ↦ x i • a) := by
  simp [TensorProduct.finRightScalar]

end

variable {R : Type*} [CommRing R] (I : Ideal R)
variable (M : Type*) [AddCommGroup M] [Module R M]
variable {N : Type*} [AddCommGroup N] [Module R N]

namespace AdicCompletion

private def ofTensorProductBil : AdicCompletion I R →ₗ[AdicCompletion I R] M →ₗ[R] AdicCompletion I M where
  toFun r := LinearMap.lsmul (AdicCompletion I R) (AdicCompletion I M) r ∘ₗ of I M
  map_add' x y := by
    apply LinearMap.ext
    simp
  map_smul' r x := by
    apply LinearMap.ext
    intro y
    simp only [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      LinearMap.lsmul_apply, RingHom.id_apply, LinearMap.smul_apply]
    rw [smul_eq_mul, mul_smul]

@[simp]
private theorem ofTensorProductBil_apply_apply (r : AdicCompletion I R) (x : M) :
    ((AdicCompletion.ofTensorProductBil I M) r) x = r • (of I M) x :=
  rfl

open TensorProduct

noncomputable def ofTensorProduct :
    AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] AdicCompletion I M :=
  TensorProduct.AlgebraTensorModule.lift (ofTensorProductBil I M)

@[simp]
theorem ofTensorProduct_tmul (r : AdicCompletion I R) (x : M) :
    ofTensorProduct I M (r ⊗ₜ x) = r • of I M x := by
  simp [ofTensorProduct]

attribute [-simp] _root_.smul_eq_mul Algebra.id.smul_eq_mul

theorem diag_comm (n : ℕ) :
    piEquivFin I n ∘ₗ ofTensorProduct I (Fin n → R) =
    (TensorProduct.finRightScalar R (AdicCompletion I R) n).toLinearMap := by
  ext i j k
  simp only [AlgebraTensorModule.curry_apply, LinearMap.coe_comp, LinearMap.coe_single,
    Function.comp_apply, curry_apply, LinearMap.coe_restrictScalars, LinearEquiv.coe_coe,
    ofTensorProduct_tmul, one_smul, piEquivFin_apply, pi_apply_coe, of_apply,
    Submodule.mkQ_apply, finRightScalar_tmul]
  rw [Pi.single_apply]
  erw [LinearMap.reduceModIdeal_apply]
  split
  · next h =>
      subst h
      simp
  · next h =>
    simp
    rw [Pi.single_eq_of_ne h]
    simp

theorem diag_comm' (n : ℕ) :
    ofTensorProduct I (Fin n → R) = (piEquivFin I n).symm.toLinearMap
      ∘ₗ (TensorProduct.finRightScalar R (AdicCompletion I R) n).toLinearMap := by
  rw [← diag_comm, ← LinearMap.comp_assoc]
  simp

noncomputable def ofTensorProductInvOfFin (n : ℕ) :
    AdicCompletion I (Fin n → R) ≃ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] (Fin n → R) :=
  let f := piEquivFin I n
  let g : (Fin n → AdicCompletion I R) ≃ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] (Fin n → R)
    := (TensorProduct.finRightScalar R (AdicCompletion I R) n).symm
  f.trans g

theorem ofTensorProductInvOfFin_comp_ofTensorProduct (n : ℕ) :
    ofTensorProductInvOfFin I n ∘ₗ ofTensorProduct I (Fin n → R) = LinearMap.id := by
  dsimp [ofTensorProductInvOfFin]
  change (finRightScalar R (AdicCompletion I R) n).symm.toLinearMap
    ∘ₗ (piEquivFin I n ∘ₗ ofTensorProduct I (Fin n → R)) = LinearMap.id
  rw [diag_comm]
  simp

theorem ofTensorProduct_comp_ofTensorProductInvOfFin (n : ℕ) :
    ofTensorProduct I (Fin n → R) ∘ₗ ofTensorProductInvOfFin I n = LinearMap.id := by
  dsimp [ofTensorProductInvOfFin]
  change ofTensorProduct I (Fin n → R)
    ∘ₗ (finRightScalar R (AdicCompletion I R) n).symm.toLinearMap
    ∘ₗ piEquivFin I n = LinearMap.id
  rw [diag_comm', LinearMap.comp_assoc]
  nth_rw 2 [← LinearMap.comp_assoc]
  simp

noncomputable def ofTensorProductEquivOfFin (n : ℕ) :
    AdicCompletion I R ⊗[R] (Fin n → R) ≃ₗ[AdicCompletion I R] AdicCompletion I (Fin n → R) :=
  LinearEquiv.ofLinear
    (ofTensorProduct I (Fin n → R))
    (ofTensorProductInvOfFin I n)
    (ofTensorProduct_comp_ofTensorProductInvOfFin I n)
    (ofTensorProductInvOfFin_comp_ofTensorProduct I n)

theorem ofTensorProduct_bijective_of_fin (n : ℕ) :
    Function.Bijective (ofTensorProduct I (Fin n → R)) :=
  EquivLike.bijective (ofTensorProductEquivOfFin I n)

theorem ofTensorProduct_surjective_of_fg [Module.Finite R M] :
    Function.Surjective (ofTensorProduct I M) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R M
  let f := ofTensorProduct I M ∘ₗ p.baseChange (AdicCompletion I R)
  let g := p.adicCompletion I ∘ₗ ofTensorProduct I (Fin n → R)
  have hfg : f = g := by
    ext
    simp [f, g]
  have hg : Function.Surjective g := by
    dsimp [g]
    apply Function.Surjective.comp
    exact LinearMap.adicCompletion_surjective I hp
    exact (ofTensorProduct_bijective_of_fin I n).surjective
  apply Function.Surjective.of_comp
  show Function.Surjective f
  rw [hfg]
  exact hg

section

variable {M}
variable (f : M →ₗ[R] N)

theorem ofTensorProduct_naturality :
    f.adicCompletion I ∘ₗ ofTensorProduct I M
      = ofTensorProduct I N ∘ₗ AlgebraTensorModule.map LinearMap.id f := by
  ext
  simp

end

universe u v

variable {R : Type u} [CommRing R] (I : Ideal R)
variable (M : Type u) [AddCommGroup M] [Module R M]

section

open CategoryTheory

variable [IsNoetherianRing R]

variable {n : ℕ} (f : (Fin n → R) →ₗ[R] M) (hf : Function.Surjective f)

local notation "K" => LinearMap.ker f
local notation "i" => Submodule.subtype K

noncomputable def tensorRep1 :
    AdicCompletion I R ⊗[R] LinearMap.ker f
      →ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] (Fin n → R) :=
  AlgebraTensorModule.map LinearMap.id i

noncomputable def tensorRep2 :
    AdicCompletion I R ⊗[R] (Fin n → R)
      →ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] M :=
  AlgebraTensorModule.map LinearMap.id f

theorem if_exact : Function.Exact i f := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.property

theorem tens_exact : Function.Exact (tensorRep1 I M f) (tensorRep2 I M f) :=
  lTensor_exact (AdicCompletion I R) (if_exact M f) hf

theorem tens_surj : Function.Surjective (tensorRep2 I M f) :=
  LinearMap.lTensor_surjective (AdicCompletion I R) hf

theorem adic_exact : Function.Exact (LinearMap.adicCompletion I i) (f.adicCompletion I) := by
  refine LinearMap.adicCompletion_exact I (Submodule.injective_subtype _) ?_ hf
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.property

theorem adic_surj : Function.Surjective (f.adicCompletion I) :=
  LinearMap.adicCompletion_surjective I hf

def secondRow : ComposableArrows (ModuleCat (AdicCompletion I R)) 4 :=
  ComposableArrows.mk₄
    (ModuleCat.ofHom (LinearMap.adicCompletion I i))
    (ModuleCat.ofHom (f.adicCompletion I))
    (ModuleCat.ofHom (0 : _ →ₗ[AdicCompletion I R] PUnit))
    (ModuleCat.ofHom (0 : _ →ₗ[AdicCompletion I R] PUnit))

noncomputable instance : AddCommGroup (AdicCompletion I R ⊗[R] K) :=
  inferInstance

noncomputable def firstRow : ComposableArrows (ModuleCat (AdicCompletion I R)) 4 :=
  ComposableArrows.mk₄
    (ModuleCat.ofHom (tensorRep1 I M f))
    (ModuleCat.ofHom (tensorRep2 I M f))
    (ModuleCat.ofHom (0 : AdicCompletion I R ⊗[R] M →ₗ[AdicCompletion I R] PUnit))
    (ModuleCat.ofHom (0 : _ →ₗ[AdicCompletion I R] PUnit))

theorem firstRow_exact : (firstRow I M f).Exact where
  zero k _ := match k with
    | 0 => (tens_exact I M f hf).linearMap_comp_eq_zero
    | 1 => LinearMap.zero_comp (tensorRep2 I M f) 
    | 2 => LinearMap.zero_comp 0
  exact k _ := by
    match k with
    | 0 =>
        rw [ShortComplex.moduleCat_exact_iff]
        intro (x : AdicCompletion I R ⊗[R] (Fin n → R)) (hx : tensorRep2 I M f x = 0)
        exact (tens_exact I M f hf x).mp hx
    | 1 =>
        rw [ShortComplex.moduleCat_exact_iff]
        intro (x : AdicCompletion I R ⊗[R] M) _
        exact (tens_surj I M f hf) x
    | 2 => 
        rw [ShortComplex.moduleCat_exact_iff]
        intro (x : PUnit) _
        exact ⟨0, rfl⟩

theorem secondRow_exact : (secondRow I M f).Exact where
  zero k _ := match k with
    | 0 => (adic_exact I M f hf).linearMap_comp_eq_zero
    | 1 => LinearMap.zero_comp (f.adicCompletion I) 
    | 2 => LinearMap.zero_comp 0
  exact k _ := by
    match k with
    | 0 =>
        rw [ShortComplex.moduleCat_exact_iff]
        intro (x : AdicCompletion I (Fin n → R)) (hx : f.adicCompletion I x = 0)
        exact (adic_exact I M f hf x).mp hx
    | 1 =>
        rw [ShortComplex.moduleCat_exact_iff]
        intro (x : AdicCompletion I M) _
        exact (adic_surj I M f hf) x
    | 2 => 
        rw [ShortComplex.moduleCat_exact_iff]
        intro (x : PUnit) _
        exact ⟨0, rfl⟩

noncomputable def φ : firstRow I M f ⟶ secondRow I M f :=
  ComposableArrows.homMk₄
    (ModuleCat.ofHom (ofTensorProduct I K))
    (ModuleCat.ofHom (ofTensorProduct I (Fin n → R)))
    (ModuleCat.ofHom (ofTensorProduct I M))
    (ModuleCat.ofHom 0)
    (ModuleCat.ofHom 0)
    (ofTensorProduct_naturality I i).symm
    (ofTensorProduct_naturality I f).symm
    rfl
    rfl

theorem ofTensorProduct_iso : IsIso (ModuleCat.ofHom (ofTensorProduct I M)) := by
  refine Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono
    (firstRow_exact I M f hf) (secondRow_exact I M f hf) (φ I M f) ?_ ?_ ?_ ?_
  · apply ConcreteCategory.epi_of_surjective
    exact ofTensorProduct_surjective_of_fg I K
  · apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ofTensorProduct_bijective_of_fin I n
  · show IsIso (ModuleCat.ofHom 0)
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    show Function.Bijective (0 : _ →ₗ[AdicCompletion I R] _)
    constructor
    · intro x y _
      rfl
    · intro y
      exact ⟨0, rfl⟩
  · apply ConcreteCategory.mono_of_injective
    intro x y _
    rfl

theorem ofTensorProduct_bijective_of_map_from_fin : Function.Bijective (ofTensorProduct I M) := by
  change Function.Bijective ((forget _).map (ModuleCat.ofHom (ofTensorProduct I M)))
  have : IsIso (ModuleCat.ofHom (ofTensorProduct I M)) :=
    ofTensorProduct_iso I M f hf
  apply ConcreteCategory.bijective_of_isIso

end

theorem ofTensorProduct_bijective_of_fg [IsNoetherianRing R] [Module.Finite R M] :
    Function.Bijective (ofTensorProduct I M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  exact ofTensorProduct_bijective_of_map_from_fin I M f hf

section

variable (J : Ideal R) (hfg : J.FG) [IsNoetherianRing R]

theorem foo : (AlgebraTensorModule.map LinearMap.id (Submodule.subtype J))
    = (LinearEquiv.ofBijective (ofTensorProduct I R) (ofTensorProduct_bijective_of_fg I R)).symm.toLinearMap
    ∘ₗ LinearMap.adicCompletion I (Submodule.subtype J)
    ∘ₗ LinearEquiv.ofBijective (ofTensorProduct I J) (ofTensorProduct_bijective_of_fg I J) := by
  erw [ofTensorProduct_naturality I (Submodule.subtype J)]
  rw [← LinearMap.comp_assoc]
  ext x
  simp only [AlgebraTensorModule.curry_apply, curry_apply, LinearMap.coe_restrictScalars,
    AlgebraTensorModule.map_tmul, LinearMap.id_coe, id_eq, Submodule.coeSubtype, LinearMap.coe_comp,
    LinearEquiv.coe_coe, Function.comp_apply]
  rw [LinearEquiv.ofBijective_symm_apply_apply]

theorem bar : Function.Injective
    (AlgebraTensorModule.map LinearMap.id (Submodule.subtype J)
      : AdicCompletion I R ⊗[R] J →ₗ[AdicCompletion I R] AdicCompletion I R ⊗[R] R) := by
  rw [foo I J]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EmbeddingLike.comp_injective,
    EquivLike.injective_comp]
  exact LinearMap.adicCompletion_injective I
    (Submodule.subtype J) (Submodule.injective_subtype J)

end

/-- Adic completion of a Noetherian ring `R` is flat over `R`. -/
instance flat [IsNoetherianRing R] : Algebra.Flat R (AdicCompletion I R) where
  out := by
    apply (Module.Flat.iff_lTensor_injective' R (AdicCompletion I R)).mpr
    intro J
    exact bar I J
