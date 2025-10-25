/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

-- AlgebraHomogeneousLocalization
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization

-- ProjMap
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

-- TensorProduct/GradedAlgebra
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Basic

-- TensorProduct/Proj
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.RingTheory.GradedAlgebra.Basic

-- Scheme
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.TensorProduct.Basic

-- to be deleted
open scoped SpecOfNotation

/-! # Algebra Structure on Homogeneous Localization

In this file we show that if `A` is a graded `R`-algebra then `HomogeneousLocalization 𝒜 S` is
an `R`-algebra.
-/

variable {ι R₀ R A : Type*}

section Semiring

variable [CommSemiring R₀] [CommSemiring R] [Semiring A]
  [Algebra R₀ R] [Algebra R A] [Algebra R₀ A] [IsScalarTower R₀ R A]
  [DecidableEq ι] [AddMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]

instance : Algebra R₀ (𝒜 0) where
  algebraMap := (algebraMap R (𝒜 0)).comp (algebraMap R₀ R)
  commutes' r x := Algebra.commutes' (algebraMap R₀ R r) x
  smul_def' r x := Subtype.ext <| by
    rw [← IsScalarTower.algebraMap_smul R, Algebra.smul_def]
    rfl

@[simp] lemma algebraMap_to_zero (r : R₀) : (algebraMap R₀ (𝒜 0) r : A) = algebraMap R₀ A r :=
  (IsScalarTower.algebraMap_apply R₀ R A r).symm

end Semiring

section Ring

namespace HomogeneousLocalization

variable [CommRing R₀] [CommRing R] [CommRing A]
  [Algebra R₀ R] [Algebra R A] [Algebra R₀ A] [IsScalarTower R₀ R A]
  [DecidableEq ι] [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
  (S : Submonoid A)

@[simp]
lemma val_fromZeroRingHom (r : R) :
    (fromZeroRingHom 𝒜 S (algebraMap _ _ r)).val = algebraMap _ _ r :=
  rfl

instance : Algebra R₀ (HomogeneousLocalization 𝒜 S) where
  algebraMap := (fromZeroRingHom 𝒜 S).comp (algebraMap R₀ (𝒜 0))
  commutes' r x := mul_comm ..
  smul_def' r x := by ext; rw [val_smul, val_mul, Algebra.smul_def, RingHom.comp_apply,
    IsScalarTower.algebraMap_apply R₀ R (𝒜 0), val_fromZeroRingHom,
    ← IsScalarTower.algebraMap_apply]

instance : IsScalarTower R₀ (𝒜 0) (HomogeneousLocalization 𝒜 S) :=
  .of_algebraMap_eq' rfl

instance : IsScalarTower R₀ R (HomogeneousLocalization 𝒜 S) :=
  .of_algebraMap_eq' rfl

instance : IsScalarTower R (𝒜 0) (Localization S) :=
  .of_algebraMap_eq' rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    IsScalarTower R (HomogeneousLocalization 𝒜 S) (Localization S) :=
  .of_algebraMap_eq' rfl

instance {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι] [AddCommMonoid ι]
      (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) :
    IsScalarTower (𝒜 0) (HomogeneousLocalization 𝒜 S) (Localization S) :=
  .of_algebraMap_eq' rfl

@[simp] lemma algebraMap_eq' :
    algebraMap R₀ (HomogeneousLocalization 𝒜 S) = (fromZeroRingHom 𝒜 S).comp (algebraMap _ _) := rfl

theorem algebraMap_apply' {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (S : Submonoid A) (f : R) :
    algebraMap R (HomogeneousLocalization 𝒜 S) f = mk ⟨0, algebraMap _ _ f, 1, one_mem _⟩ := rfl

theorem val_sum {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {𝒜 : ι → Submodule R A}
      {x : Submonoid A} [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜]
      {σ : Type*} {S : Finset σ} {f : σ → HomogeneousLocalization 𝒜 x} :
    (∑ s ∈ S, f s).val = ∑ s ∈ S, (f s).val :=
  map_sum (algebraMap (HomogeneousLocalization 𝒜 x) _) _ _

theorem val_prod {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {𝒜 : ι → Submodule R A}
      {x : Submonoid A} [AddCommMonoid ι] [DecidableEq ι] [GradedAlgebra 𝒜]
      {σ : Type*} {S : Finset σ} {f : σ → HomogeneousLocalization 𝒜 x} :
    (∏ s ∈ S, f s).val = ∏ s ∈ S, (f s).val :=
  map_prod (algebraMap (HomogeneousLocalization 𝒜 x) _) _ _

namespace Away

theorem mk_smul {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] {f d hf n x} (hx) {r : R} :
    r • Away.mk 𝒜 (f:=f) hf (d:=d) n x hx = .mk 𝒜 hf n (r • x) (Submodule.smul_mem _ _ hx) := rfl

theorem algebraMap_apply {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f : A) (d hf) (r : R) :
    algebraMap R (Away 𝒜 f) r = .mk 𝒜 (d:=d) hf 0 (algebraMap R A r)
      (by rw [zero_nsmul]; exact SetLike.algebraMap_mem_graded ..) := by
  ext; simp [fromZeroRingHom]

/-- If `f = g`, then `Away 𝒜 f ≅ Away 𝒜 g`. -/
@[simps! apply] noncomputable
def congr {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f g : A)
      {d : ι} (hf : f ∈ 𝒜 d) (h : f = g) :
    Away 𝒜 f ≃ₐ[R] Away 𝒜 g := by
  refine .ofRingEquiv (f := .ofRingHom (awayMap 𝒜 (SetLike.one_mem_graded ..) (by simp [h]))
    (awayMap 𝒜 (SetLike.one_mem_graded ..) (by simp [h]))
    (RingHom.ext fun x ↦ ?_) (RingHom.ext fun x ↦ ?_)) (fun x ↦ ?_)
  · subst h; rcases Away.mk_surjective 𝒜 hf x with ⟨n, a, ha, rfl⟩; simp
  · subst h; rcases Away.mk_surjective 𝒜 hf x with ⟨n, a, ha, rfl⟩; simp
  · subst h; ext; simp [awayMap_fromZeroRingHom]

lemma congr_mk {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f g : A)
      {d : ι} (hf : f ∈ 𝒜 d) (h : f = g) (n x hx) :
    congr 𝒜 f g hf h (.mk 𝒜 hf n x hx) = .mk 𝒜 (by rwa [← h]) n x hx := by
  simp_rw [congr_apply, awayMap_mk, one_pow, mul_one, add_zero]

@[simp] lemma congr_symm {ι R A : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq ι]
      [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (f g : A)
      {d : ι} (hf : f ∈ 𝒜 d) (h : f = g) :
    (congr 𝒜 f g hf h).symm = congr 𝒜 g f (by rwa [← h]) h.symm :=
  rfl

end Away

end HomogeneousLocalization

end Ring

/-! # Functoriality of Proj
-/

universe u₁ u₂ u v

-- not `@[ext]` because `A` cannot be inferred.
theorem IsLocalization.algHom_ext {R A L B : Type*}
    [CommSemiring R] [CommSemiring A] [CommSemiring L] [CommSemiring B]
    (W : Submonoid A) [Algebra A L] [IsLocalization W L]
    [Algebra R A] [Algebra R L] [IsScalarTower R A L] [Algebra R B]
    {f g : L →ₐ[R] B} (h : f.comp (Algebra.algHom R A L) = g.comp (Algebra.algHom R A L)) :
    f = g :=
  AlgHom.coe_ringHom_injective <| IsLocalization.ringHom_ext W <| RingHom.ext <| AlgHom.ext_iff.mp h

@[ext high] theorem Localization.algHom_ext {R A B : Type*}
    [CommSemiring R] [CommSemiring A] [CommSemiring B] [Algebra R A] [Algebra R B] (W : Submonoid A)
    {f g : Localization W →ₐ[R] B}
    (h : f.comp (Algebra.algHom R A _) = g.comp (Algebra.algHom R A _)) :
    f = g :=
  IsLocalization.algHom_ext W h

@[simp] lemma Localization.localRingHom_mk {R P : Type*} [CommSemiring R] [CommSemiring P]
    (I : Ideal R) [I.IsPrime] (J : Ideal P) [J.IsPrime] (f : R →+* P) (hIJ : I = Ideal.comap f J)
    (x : R) (y : I.primeCompl) :
    Localization.localRingHom I J f hIJ (Localization.mk x y) =
      Localization.mk (f x) ⟨f y, by aesop⟩ := by
  simp [mk_eq_mk', localRingHom_mk']

namespace HomogeneousIdeal

lemma toIdeal_le_toIdeal_iff {ι σ A : Type*} [Semiring A] [SetLike σ A]
    [AddSubmonoidClass σ A] (𝒜 : ι → σ) [DecidableEq ι] [AddMonoid ι] [GradedRing 𝒜]
    {I J : HomogeneousIdeal 𝒜} : I.toIdeal ≤ J.toIdeal ↔ I ≤ J := Iff.rfl

variable {ι σ A : Type*} [Semiring A]
  [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
  [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

lemma mem_irrelevant_of_mem {x : A} {i : ι} (hi : 0 < i) (hx : x ∈ 𝒜 i) :
    x ∈ irrelevant 𝒜 := by
  rw [mem_irrelevant_iff, GradedRing.proj_apply, DirectSum.decompose_of_mem _ hx,
    DirectSum.of_eq_of_ne _ _ _ (by aesop), ZeroMemClass.coe_zero]

/-- `irrelevant 𝒜 = ⨁_{i>0} 𝒜ᵢ` -/
lemma irrelevant_eq_iSup : (irrelevant 𝒜).toAddSubmonoid = ⨆ i > 0, .ofClass (𝒜 i) := by
  refine le_antisymm (fun x hx ↦ ?_) <| iSup₂_le fun i hi x hx ↦ mem_irrelevant_of_mem _ hi hx
  classical rw [← DirectSum.sum_support_decompose 𝒜 x]
  refine sum_mem fun j hj ↦ ?_
  by_cases hj₀ : j = 0
  · classical exact (DFinsupp.mem_support_iff.mp hj <| hj₀ ▸ (by simpa using hx)).elim
  · exact AddSubmonoid.mem_iSup_of_mem j <| AddSubmonoid.mem_iSup_of_mem (pos_of_ne_zero hj₀) <|
      Subtype.prop _

lemma irrelevant_toAddSubmonoid_le {P : AddSubmonoid A} :
    (irrelevant 𝒜).toAddSubmonoid ≤ P ↔ ∀ i > 0, .ofClass (𝒜 i) ≤ P := by
  rw [irrelevant_eq_iSup, iSup₂_le_iff]

lemma irrelevant_toIdeal_le {I : Ideal A} :
    (irrelevant 𝒜).toIdeal ≤ I ↔ ∀ i > 0, .ofClass (𝒜 i) ≤ I.toAddSubmonoid :=
  irrelevant_toAddSubmonoid_le _

lemma irrelevant_le {P : HomogeneousIdeal 𝒜} :
    irrelevant 𝒜 ≤ P ↔ ∀ i > 0, .ofClass (𝒜 i) ≤ P.toAddSubmonoid :=
  irrelevant_toIdeal_le _

end HomogeneousIdeal


section gradedalghom

variable {R R₁ R₂ A₁ A₂ ι : Type*}
  [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
  [Algebra R₁ A₁] [Algebra R₂ A₂]
  (𝒜₁ : ι → Submodule R₁ A₁) (𝒜₂ : ι → Submodule R₂ A₂)

/-- Here we will completely ignore the algebra structure. In the Mathlib PR's this will say
`GradedRingHom`. -/
structure GradedAlgHom extends A₁ →+* A₂ where
  map_mem' : ∀ ⦃n a⦄, a ∈ 𝒜₁ n → toRingHom a ∈ 𝒜₂ n

@[inherit_doc]
notation:25 𝒜₁ " →ᵍᵃ " 𝒜₂ => GradedAlgHom 𝒜₁ 𝒜₂

namespace GradedAlgHom

variable {𝒜₁ 𝒜₂}

theorem toRingHom_injective : Function.Injective (toRingHom : (𝒜₁ →ᵍᵃ 𝒜₂) → (A₁ →+* A₂)) := by
  rintro ⟨_⟩ _ h
  congr

instance funLike : FunLike (𝒜₁ →ᵍᵃ 𝒜₂) A₁ A₂ where
  coe f := f.toFun
  coe_injective' _ _ h := toRingHom_injective <| RingHom.ext (congr($h ·))

instance ringHomClass : RingHomClass (𝒜₁ →ᵍᵃ 𝒜₂) A₁ A₂ where
  map_mul f := f.map_mul
  map_add f := f.map_add
  map_one f := f.map_one
  map_zero f := f.map_zero

variable (f : 𝒜₁ →ᵍᵃ 𝒜₂)

@[simp] lemma coe_toRingHom : (f.toRingHom : A₁ → A₂) = f := rfl

lemma map_mem {n : ι} {a : A₁} (ha : a ∈ 𝒜₁ n) : f a ∈ 𝒜₂ n :=
  f.map_mem' ha

@[simps] def addHom (n : ι) : 𝒜₁ n →+ 𝒜₂ n where
  toFun a := ⟨f a, f.map_mem a.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂]

@[simp] lemma decompose_map {x : A₁} :
    DirectSum.decompose 𝒜₂ (f x) = .map f.addHom (.decompose 𝒜₁ x) := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜₁ x, map_sum, DirectSum.decompose_sum,
    DirectSum.decompose_sum, map_sum]
  congr 1
  ext n : 1
  rw [DirectSum.decompose_of_mem _ (f.map_mem (Subtype.prop _)),
    DirectSum.decompose_of_mem _ (Subtype.prop _), DirectSum.map_of]
  rfl

lemma map_coe_decompose {x : A₁} {n : ι} :
    f (DirectSum.decompose 𝒜₁ x n) = DirectSum.decompose 𝒜₂ (f x) n := by
  simp

end GradedAlgHom

variable [DecidableEq ι] [AddCommMonoid ι] [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂]
variable {𝒜₁ 𝒜₂} (f : 𝒜₁ →ᵍᵃ 𝒜₂)

namespace HomogeneousIdeal

@[simp] lemma coe_toIdeal (I : HomogeneousIdeal 𝒜₁) : (I.toIdeal : Set A₁) = I := rfl

def map (I : HomogeneousIdeal 𝒜₁) : HomogeneousIdeal 𝒜₂ where
  __ := I.toIdeal.map f
  is_homogeneous' n a ha := by
    rw [Ideal.map] at ha
    induction ha using Submodule.span_induction generalizing n with
    | mem a ha =>
      obtain ⟨a, ha, rfl⟩ := ha
      rw [← f.map_coe_decompose]
      exact Ideal.mem_map_of_mem _ (I.2 _ ha)
    | zero => simp
    | add => simp [*, Ideal.add_mem]
    | smul a₁ a₂ ha₂ ih =>
      classical rw [smul_eq_mul, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
      exact sum_mem fun ij hij ↦ Ideal.mul_mem_left _ _ <| ih _

def comap (I : HomogeneousIdeal 𝒜₂) : HomogeneousIdeal 𝒜₁ where
  __ := I.toIdeal.comap f
  is_homogeneous' n a ha := by
    rw [Ideal.mem_comap, HomogeneousIdeal.mem_iff, f.map_coe_decompose]
    exact I.2 _ ha

variable {f}

lemma coe_comap (I : HomogeneousIdeal 𝒜₂) : (I.comap f : Set A₁) = f ⁻¹' I := rfl

lemma map_le_iff_le_comap {I : HomogeneousIdeal 𝒜₁} {J : HomogeneousIdeal 𝒜₂} :
    I.map f ≤ J ↔ I ≤ J.comap f :=
  Ideal.map_le_iff_le_comap
alias ⟨le_comap_of_map_le, map_le_of_le_comap⟩ := map_le_iff_le_comap

theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦
  map_le_iff_le_comap

end HomogeneousIdeal

namespace HomogeneousLocalization

open NumDenSameDeg in
/-- We fix `map` which needed same base ring. -/
def map' {P : Submonoid A₁} {Q : Submonoid A₂} (comap_le : P ≤ Q.comap f) :
  HomogeneousLocalization 𝒜₁ P →+* HomogeneousLocalization 𝒜₂ Q where
  toFun := Quotient.map'
    (fun x ↦ ⟨x.deg, ⟨_, f.2 x.num.2⟩, ⟨_, f.2 x.den.2⟩, comap_le x.den_mem⟩)
    fun x y (e : x.embedding = y.embedding) ↦ by
      apply_fun IsLocalization.map (Localization Q) (f : A₁ →+* A₂) comap_le at e
      simp_rw [HomogeneousLocalization.NumDenSameDeg.embedding, Localization.mk_eq_mk',
        IsLocalization.map_mk', ← Localization.mk_eq_mk'] at e
      exact e
  map_add' := Quotient.ind₂' fun x y ↦ by
    simp only [← mk_add, Quotient.map'_mk'', num_add, map_add, map_mul, den_add]; rfl
  map_mul' := Quotient.ind₂' fun x y ↦ by
    simp only [← mk_mul, Quotient.map'_mk'', num_mul, map_mul, den_mul]; rfl
  map_zero' := by simp only [← mk_zero (𝒜 := 𝒜₁), Quotient.map'_mk'', deg_zero,
    num_zero, ZeroMemClass.coe_zero, map_zero, den_zero, map_one]; rfl
  map_one' := by simp only [← mk_one (𝒜 := 𝒜₁), Quotient.map'_mk'',
    num_one, den_one, map_one]; rfl

lemma map'_mk {P : Submonoid A₁} {Q : Submonoid A₂} (comap_le : P ≤ Q.comap f)
    (c : NumDenSameDeg 𝒜₁ P) :
    map' f comap_le (mk c) = mk ⟨c.deg, ⟨_, f.2 c.num.2⟩, ⟨_, f.2 c.den.2⟩, comap_le c.den_mem⟩ :=
  rfl

noncomputable def localRingHom (I : Ideal A₁) [I.IsPrime] (J : Ideal A₂) [J.IsPrime]
    (hIJ : I = J.comap f) :
    AtPrime 𝒜₁ I →+* AtPrime 𝒜₂ J :=
  map' f <| Localization.le_comap_primeCompl_iff.mpr <| hIJ ▸ le_rfl

variable (I : Ideal A₁) [I.IsPrime] (J : Ideal A₂) [J.IsPrime] (hIJ : I = J.comap f)

@[simp] lemma val_localRingHom (x : AtPrime 𝒜₁ I) :
    (localRingHom f I J hIJ x).val = Localization.localRingHom _ _ f hIJ x.val := by
  obtain ⟨⟨i, x, s, hs⟩, rfl⟩ := x.mk_surjective
  simp [localRingHom, map'_mk]

instance isLocalHom_localRingHom : IsLocalHom (localRingHom f I J hIJ) where
  map_nonunit x hx := by
    rw [← isUnit_iff_isUnit_val] at hx ⊢
    rw [val_localRingHom] at hx
    exact IsLocalHom.map_nonunit _ hx

@[simps] def NumDenSameDeg.map {W₁ : Submonoid A₁} {W₂ : Submonoid A₂}
    (hw : W₁ ≤ W₂.comap f) (c : NumDenSameDeg 𝒜₁ W₁) : NumDenSameDeg 𝒜₂ W₂ where
  deg := c.deg
  den := f.addHom _ c.den
  num := f.addHom _ c.num
  den_mem := hw c.den_mem

lemma localRingHom_mk (c : NumDenSameDeg 𝒜₁ I.primeCompl) :
    localRingHom f I J hIJ (.mk c) =
      .mk (c.map f <| hIJ ▸ by rfl) := by
  rfl

def lof {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (S : Submonoid A) {i : ι} (d : 𝒜 i) (hd : ↑d ∈ S) :
    𝒜 i →ₗ[R] HomogeneousLocalization 𝒜 S where
  toFun x := mk ⟨i, x, d, hd⟩
  map_add' x y := by ext; simp [Localization.add_mk_self]
  map_smul' c x := by ext; simp [Localization.smul_mk]

nonrec def Away.lof {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i : ι} {f : A} (hf : f ∈ 𝒜 i) (n : ℕ) :
    𝒜 (n • i) →ₗ[R] HomogeneousLocalization.Away 𝒜 f :=
  lof _ _ ⟨f ^ n, SetLike.pow_mem_graded _ hf⟩ ⟨n, rfl⟩

@[simp] lemma Away.val_lof
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i : ι} {f : A} (hf : f ∈ 𝒜 i) (n : ℕ) (a : 𝒜 (n • i)) :
    (lof _ hf n a).val = .mk a ⟨f ^ n, n, rfl⟩ := rfl

lemma Away.lof_surjective
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι] (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i : ι} {f : A} (hf : f ∈ 𝒜 i) (x : Away 𝒜 f) :
    ∃ (n : ℕ) (a : 𝒜 (n • i)), lof _ hf n a = x := by
  obtain ⟨n, a, ha, rfl⟩ := x.mk_surjective _ hf
  exact ⟨n, ⟨a, ha⟩, rfl⟩

open NumDenSameDeg in
def mapₐ {R R₁ R₂ A₁ A₂ : Type*}
    [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [Algebra R R₁] [Algebra R₁ A₁] [Algebra R A₁] [IsScalarTower R R₁ A₁]
    [Algebra R R₂] [Algebra R₂ A₂] [Algebra R A₂] [IsScalarTower R R₂ A₂]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
    {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
    {𝒮₁ : Submonoid A₁} {𝒮₂ : Submonoid A₂}
    (g : A₁ →ₐ[R] A₂) (comap_le : 𝒮₁ ≤ Submonoid.comap g 𝒮₂)
    (hg : ∀ ⦃i a⦄, a ∈ 𝒜₁ i → g a ∈ 𝒜₂ i) :
    HomogeneousLocalization 𝒜₁ 𝒮₁ →ₐ[R] HomogeneousLocalization 𝒜₂ 𝒮₂ where
  __ := map' ⟨g, hg⟩ comap_le
  commutes' r := by ext; simp [fromZeroRingHom, map'_mk]

@[simp] lemma mapₐ_mk {R R₁ R₂ A₁ A₂ : Type*}
    [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [Algebra R R₁] [Algebra R₁ A₁] [Algebra R A₁] [IsScalarTower R R₁ A₁]
    [Algebra R R₂] [Algebra R₂ A₂] [Algebra R A₂] [IsScalarTower R R₂ A₂]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
    {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
    {𝒮₁ : Submonoid A₁} {𝒮₂ : Submonoid A₂}
    (g : A₁ →ₐ[R] A₂) (comap_le : 𝒮₁ ≤ Submonoid.comap g 𝒮₂)
    (hg : ∀ ⦃i⦄, ∀ a ∈ 𝒜₁ i, g a ∈ 𝒜₂ i)
    (c : NumDenSameDeg 𝒜₁ 𝒮₁) :
    HomogeneousLocalization.mapₐ g comap_le hg (mk c) =
    mk ⟨c.deg, ⟨_, hg _ c.num.2⟩, ⟨_, hg _ c.den.2⟩, comap_le c.den_mem⟩ := rfl

def Away.map {R₁ R₂ A₁ A₂ : Type*}
    [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂] [Algebra R₁ A₁] [Algebra R₂ A₂]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
    {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
    {f₁ : A₁} {f₂ : A₂} (g : 𝒜₁ →ᵍᵃ 𝒜₂) (hgf : g f₁ = f₂) :
    HomogeneousLocalization.Away 𝒜₁ f₁ →+* HomogeneousLocalization.Away 𝒜₂ f₂ :=
  HomogeneousLocalization.map' g (Submonoid.powers_le.mpr ⟨1, by simp [hgf]⟩)

@[simp] lemma Away.map_mk {R₁ R₂ A₁ A₂ : Type*}
    [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂] [Algebra R₁ A₁] [Algebra R₂ A₂]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
    {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
    {f₁ : A₁} {f₂ : A₂} (g : 𝒜₁ →ᵍᵃ 𝒜₂) (hgf : g f₁ = f₂)
    {d : ι} (hf : f₁ ∈ 𝒜₁ d) (n : ℕ) (a : A₁) (ha : a ∈ 𝒜₁ (n • d)) :
    map g hgf (.mk _ hf n a ha) = .mk _ (hgf ▸ g.2 hf) n (g a) (g.2 ha) := by
  simp [map, Away.mk, map'_mk, hgf]

@[simp] lemma Away.map_lof {R₁ R₂ A₁ A₂ : Type*}
    [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂] [Algebra R₁ A₁] [Algebra R₂ A₂]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
    {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
    {f₁ : A₁} {f₂ : A₂} (g : 𝒜₁ →ᵍᵃ 𝒜₂) (hgf : g f₁ = f₂)
    {d : ι} (hf : f₁ ∈ 𝒜₁ d) (n : ℕ) (a : 𝒜₁ (n • d)) :
    map g hgf (lof _ hf n a) = lof _ (hgf ▸ g.2 hf) n ⟨g a, g.2 a.2⟩ :=
  map_mk _ _ hf _ _ _

-- @[simp] lemma Away.val_map {R₁ R₂ A₁ A₂ : Type*}
--     [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂] [Algebra R₁ A₁] [Algebra R₂ A₂]
--     {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
--     {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
--     {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
--     {f₁ : A₁} {f₂ : A₂} (g : 𝒜₁ →ᵍᵃ 𝒜₂) (hgf : g f₁ = f₂) (x : Away 𝒜₁ f₁)
--     {d : ι} (hf : f₁ ∈ 𝒜₁ d) :
--     (map g hgf x).val = Localization.awayLift ((algebraMap _ _).comp g.toRingHom) _
--       (IsLocalization.map_units (M := .powers f₂) _ ⟨g f₁, 1, hgf ▸ pow_one _⟩) x.val := by
--   obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hf
--   simp [Localization.awayLift_mk]

def Away.mapₐ {R R₁ R₂ A₁ A₂ : Type*}
    [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [Algebra R R₁] [Algebra R₁ A₁] [Algebra R A₁] [IsScalarTower R R₁ A₁]
    [Algebra R R₂] [Algebra R₂ A₂] [Algebra R A₂] [IsScalarTower R R₂ A₂]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
    {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
    {f₁ : A₁} {f₂ : A₂} (g : A₁ →ₐ[R] A₂) (hg : ∀ ⦃i⦄, ∀ a ∈ 𝒜₁ i, g a ∈ 𝒜₂ i)
    (hgf : g f₁ = f₂) :
    HomogeneousLocalization.Away 𝒜₁ f₁ →ₐ[R] HomogeneousLocalization.Away 𝒜₂ f₂ :=
  HomogeneousLocalization.mapₐ g (Submonoid.powers_le.mpr ⟨1, by simp [hgf]⟩) hg

@[simp] lemma Away.mapₐ_mk {R R₁ R₂ A₁ A₂ : Type*}
    [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [Algebra R R₁] [Algebra R₁ A₁] [Algebra R A₁] [IsScalarTower R R₁ A₁]
    [Algebra R R₂] [Algebra R₂ A₂] [Algebra R A₂] [IsScalarTower R R₂ A₂]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
    {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
    {f₁ : A₁} {f₂ : A₂} (g : A₁ →ₐ[R] A₂) (hg : ∀ ⦃i⦄, ∀ a ∈ 𝒜₁ i, g a ∈ 𝒜₂ i)
    (hgf : g f₁ = f₂) {d : ι} (hf : f₁ ∈ 𝒜₁ d) (n : ℕ) (a : A₁) (ha : a ∈ 𝒜₁ (n • d)) :
    mapₐ g hg hgf (.mk _ hf n a ha) = .mk _ (hgf ▸ hg _ hf) n (g a) (hg _ ha) := by
  simp [mapₐ, Away.mk, hgf]

@[simp] lemma Away.mapₐ_lof {R R₁ R₂ A₁ A₂ : Type*}
    [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
    [Algebra R R₁] [Algebra R₁ A₁] [Algebra R A₁] [IsScalarTower R R₁ A₁]
    [Algebra R R₂] [Algebra R₂ A₂] [Algebra R A₂] [IsScalarTower R R₂ A₂]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {𝒜₁ : ι → Submodule R₁ A₁} [GradedAlgebra 𝒜₁]
    {𝒜₂ : ι → Submodule R₂ A₂} [GradedAlgebra 𝒜₂]
    {d : ι} {f₁ : A₁} (hf : f₁ ∈ 𝒜₁ d) {f₂ : A₂}
    (g : A₁ →ₐ[R] A₂) (hg : ∀ ⦃i⦄, ∀ a ∈ 𝒜₁ i, g a ∈ 𝒜₂ i)
    (hgf : g f₁ = f₂) (n : ℕ) (a : 𝒜₁ (n • d)) :
    mapₐ g hg hgf (lof _ hf n a) = lof _ (hgf ▸ hg _ hf) n ⟨g a, hg _ a.2⟩ :=
  mapₐ_mk _ _ _ hf _ _ _

end HomogeneousLocalization

end gradedalghom


section nat

variable {R₁ : Type u₁} {R₂ : Type u₂} {A₁ A₂ : Type v}
  [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂]
  [Algebra R₁ A₁] [Algebra R₂ A₂]
  (𝒜₁ : ℕ → Submodule R₁ A₁) (𝒜₂ : ℕ → Submodule R₂ A₂)
variable {𝒜₁ 𝒜₂} [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂] (f : 𝒜₁ →ᵍᵃ 𝒜₂)
  (hf : HomogeneousIdeal.irrelevant 𝒜₂ ≤ (HomogeneousIdeal.irrelevant 𝒜₁).map f)

@[simps!] def GradedAlgHom.zero : 𝒜₁ 0 →+* 𝒜₂ 0 where
  __ := f.addHom 0
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

namespace ProjectiveSpectrum

@[simps] def comap.toFun (p : ProjectiveSpectrum 𝒜₂) : ProjectiveSpectrum 𝒜₁ where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
  not_irrelevant_le le := p.3 <| hf.trans <| HomogeneousIdeal.map_le_of_le_comap le

def comap : C(ProjectiveSpectrum 𝒜₂, ProjectiveSpectrum 𝒜₁) where
  toFun := comap.toFun f hf
  continuous_toFun := by
    simp only [continuous_iff_isClosed, isClosed_iff_zeroLocus]
    rintro _ ⟨s, rfl⟩
    refine ⟨f '' s, ?_⟩
    ext x
    simp only [mem_zeroLocus, Set.image_subset_iff, Set.mem_preimage, mem_zeroLocus,
      comap.toFun_asHomogeneousIdeal, HomogeneousIdeal.coe_comap]

end ProjectiveSpectrum

namespace AlgebraicGeometry.Proj

open TopologicalSpace ProjectiveSpectrum Opposite HomogeneousLocalization

namespace StructureSheaf

variable (U : Opens (ProjectiveSpectrum 𝒜₁)) (V : Opens (ProjectiveSpectrum 𝒜₂))
  (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)

noncomputable def comapFun (s : ∀ x : U, AtPrime 𝒜₁ x.1.1.1) (y : V) :
    AtPrime 𝒜₂ y.1.1.1 :=
  localRingHom f _ y.1.1.1 rfl <| s ⟨.comap f hf y.1, hUV y.2⟩

lemma isLocallyFraction_comapFun
    (s : ∀ x : U, AtPrime 𝒜₁ x.1.1.1)
    (hs : (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜₁).pred s) :
    (ProjectiveSpectrum.StructureSheaf.isLocallyFraction 𝒜₂).pred
      (comapFun f hf U (unop (op V)) hUV ↑s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨.comap f hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (ProjectiveSpectrum.comap f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
    f.addHom i a, f.addHom i b, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩, ?_⟩
  rintro ⟨q, ⟨hqW, hqV⟩⟩
  ext
  specialize h_frac ⟨_, hqW⟩
  simp_all [comapFun]

noncomputable def comap :
    (Proj.structureSheaf 𝒜₁).1.obj (op U) →+* (Proj.structureSheaf 𝒜₂).1.obj (op V) where
  toFun s := ⟨comapFun _ _ _ _ hUV s.1, isLocallyFraction_comapFun _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [comapFun]
  map_zero' := by ext; simp [comapFun]
  map_add' x y := by ext; simp [comapFun]
  map_mul' x y := by ext; simp [comapFun]

end StructureSheaf

open CategoryTheory

@[simps (isSimp := false)] noncomputable def sheafedSpaceMap :
    Proj.toSheafedSpace 𝒜₂ ⟶ Proj.toSheafedSpace 𝒜₁ where
  base := TopCat.ofHom <| ProjectiveSpectrum.comap f hf
  c := { app U := CommRingCat.ofHom <| StructureSheaf.comap f hf _ _ Set.Subset.rfl }

@[simp] lemma germ_map_sectionInBasicOpen {p : ProjectiveSpectrum 𝒜₂}
    (c : NumDenSameDeg 𝒜₁ (p.comap f hf).1.toIdeal.primeCompl) :
    (toSheafedSpace 𝒜₂).presheaf.germ
      ((Opens.map (sheafedSpaceMap f hf).base).obj _) p (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMap f hf).c.app _ (sectionInBasicOpen 𝒜₁ _ c)) =
    (toSheafedSpace 𝒜₂).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4
      (sectionInBasicOpen 𝒜₂ p (c.map _ le_rfl)) :=
  rfl

@[simp] lemma val_sectionInBasicOpen_apply (p : ProjectiveSpectrum.top 𝒜₁)
    (c : NumDenSameDeg 𝒜₁ p.1.toIdeal.primeCompl)
    (q : ProjectiveSpectrum.basicOpen 𝒜₁ c.den) :
    ((sectionInBasicOpen 𝒜₁ p c).val q).val = .mk c.num ⟨c.den, q.2⟩ :=
  rfl

@[elementwise] theorem localRingHom_comp_stalkIso (p : ProjectiveSpectrum 𝒜₂) :
    (stalkIso 𝒜₁ (ProjectiveSpectrum.comap f hf p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫
        (stalkIso 𝒜₂ p).inv =
      (sheafedSpaceMap f hf).stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_apply, RingHom.coe_coe]
  -- I sincerely apologise for your eyes.
  erw [stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germ_map_sectionInBasicOpen]
  erw [stalkIso'_germ]
  simp

noncomputable def map : Proj 𝒜₂ ⟶ Proj 𝒜₁ where
  __ := sheafedSpaceMap f hf
  prop p := .mk fun x hx ↦ by
    rw [← localRingHom_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (stalkIso 𝒜₂ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (stalkIso 𝒜₁ (p.comap f hf)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx

@[simp] theorem map_preimage_basicOpen (s : A₁) :
    map f hf ⁻¹ᵁ basicOpen 𝒜₁ s = basicOpen 𝒜₂ (f s) :=
  rfl

theorem ι_comp_map (s : A₁) :
    (basicOpen 𝒜₂ (f s)).ι ≫ map f hf =
    (map f hf).resLE _ _ le_rfl ≫ (basicOpen 𝒜₁ s).ι := by
  simp

/-- Given `f, g : X ⟶ Spec(R)`, if the two induced maps `R ⟶ Γ(X)` are equal, then `f = g`. -/
lemma _root_.AlgebraicGeometry.ext_to_Spec {X : Scheme} {R : Type*} [CommRing R]
    {f g : X ⟶ Spec(R)}
    (h : (Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map f.op =
      (Scheme.ΓSpecIso (.of R)).inv ≫ Scheme.Γ.map g.op) :
    f = g :=
  (ΓSpec.adjunction.homEquiv X (op <| .of R)).symm.injective <| unop_injective h

lemma _root_.AlgebraicGeometry.Γ_map_Spec_map_ΓSpecIso_inv
    {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    Scheme.Γ.map (Spec.map f).op ((Scheme.ΓSpecIso R).inv x) = (Scheme.ΓSpecIso S).inv (f x) :=
  congr($((Scheme.ΓSpecIso_inv_naturality f).symm) x)

@[simp] lemma _root_.AlgebraicGeometry.Scheme.resLE_app_top
    {X Y : Scheme.{u}} (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) {h} :
    (f.resLE V U h).app ⊤ =
    V.topIso.hom ≫ f.appLE V U h ≫ U.topIso.inv := by
  simp [Scheme.Hom.resLE]

@[simp] lemma awayToSection_comp_appLE {i : ℕ} {s : A₁} (hs : s ∈ 𝒜₁ i) :
    awayToSection 𝒜₁ s ≫
      Scheme.Hom.appLE (map f hf) (basicOpen 𝒜₁ s) (basicOpen 𝒜₂ (f s)) (by rfl) =
    CommRingCat.ofHom (Away.map f rfl : Away 𝒜₁ s →+* Away 𝒜₂ (f s)) ≫
      awayToSection 𝒜₂ (f s) := by
  ext x
  obtain ⟨n, x, rfl⟩ := x.lof_surjective _ hs
  simp only [CommRingCat.hom_comp, smul_eq_mul, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom]
  conv => enter[2,2]; exact Away.map_lof _ _ _ _ _
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

/--
The following square commutes:
```
Proj 𝒜₂         ⟶ Proj 𝒜₁
    ^                   ^
    |                   |
Spec A₂[f(s)⁻¹]₀ ⟶ Spec A₁[s⁻¹]₀
```
-/
@[reassoc] theorem awayι_comp_map {i : ℕ} (hi : 0 < i) (s : A₁) (hs : s ∈ 𝒜₁ i) :
    awayι 𝒜₂ (f s) (f.2 hs) hi ≫ map f hf =
    Spec.map (CommRingCat.ofHom (Away.map f (by rfl))) ≫ awayι 𝒜₁ s hs hi := by
  rw [awayι, awayι, Category.assoc, ι_comp_map, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (basicOpen 𝒜₂ (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top, awayToSection_comp_appLE _ _ hs]

@[simps! I₀ f] noncomputable def mapAffineOpenCover : (Proj 𝒜₂).AffineOpenCover :=
  Proj.affineOpenCoverOfIrrelevantLESpan _ (fun s : (affineOpenCover 𝒜₁).I₀ ↦ f s.2) (fun s ↦ f.2 s.2.2)
    (fun s ↦ s.1.2) <| ((HomogeneousIdeal.toIdeal_le_toIdeal_iff _).mpr hf).trans <|
    Ideal.map_le_of_le_comap <| (HomogeneousIdeal.irrelevant_toIdeal_le _).mpr fun i hi x hx ↦
    Ideal.subset_span ⟨⟨⟨i, hi⟩, ⟨x, hx⟩⟩, rfl⟩

@[simp] lemma away_map_comp_fromZeroRingHom (s : A₁) :
    (Away.map f rfl).comp (fromZeroRingHom 𝒜₁ (Submonoid.powers s)) =
    (fromZeroRingHom 𝒜₂ (Submonoid.powers (f s))).comp f.zero :=
  RingHom.ext fun x ↦ by ext; simp [fromZeroRingHom, Away.map, map'_mk]

@[reassoc (attr := simp)] lemma map_comp_toSpecZero :
    map f hf ≫ toSpecZero 𝒜₁ = toSpecZero 𝒜₂ ≫ Spec.map (CommRingCat.ofHom f.zero) := by
  refine (mapAffineOpenCover f hf).openCover.hom_ext _ _ fun s ↦ ?_
  simp [awayι_comp_map_assoc _ _ s.1.2 (s.2 : A₁) s.2.2, awayι_toSpecZero, awayι_toSpecZero_assoc,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]

end AlgebraicGeometry.Proj

end nat

/-! # Isomorphism of Graded Algebras and Induced Isomorphism of Proj
-/

section arbitrary_index

variable {R₁ R₂ R₃ A₁ A₂ A₃ ι : Type*}
  [CommRing R₁] [CommRing R₂] [CommRing R₃] [CommRing A₁] [CommRing A₂] [CommRing A₃]
  [Algebra R₁ A₁] [Algebra R₂ A₂] [Algebra R₃ A₃]

/-- graded ring equiv -/
structure GradedAlgEquiv (𝒜₁ : ι → Submodule R₁ A₁) (𝒜₂ : ι → Submodule R₂ A₂)
    extends RingEquiv A₁ A₂, GradedAlgHom 𝒜₁ 𝒜₂

@[inherit_doc] notation 𝒜 " ≃ᵍᵃ " ℬ => GradedAlgEquiv 𝒜 ℬ

namespace GradedAlgEquiv

variable {𝒜₁ : ι → Submodule R₁ A₁} {𝒜₂ : ι → Submodule R₂ A₂} {𝒜₃ : ι → Submodule R₃ A₃}

instance (priority := 100) : EquivLike (𝒜₁ ≃ᵍᵃ 𝒜₂) A₁ A₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' e₁ e₂ h₁ h₂ := by
    cases e₁
    cases e₂
    congr
    exact RingEquiv.toRingHom_injective <| RingHom.ext (congr($h₁ ·))

instance (priority := 100) : RingEquivClass (𝒜₁ ≃ᵍᵃ 𝒜₂) A₁ A₂ where
  map_mul f := f.map_mul
  map_add f := f.map_add

@[simp] lemma coe_toRingEquiv (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) : (e.toRingEquiv : A₁ → A₂) = e := rfl

@[simp] lemma coe_toGradedAlgHom (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) : (e.toGradedAlgHom : A₁ → A₂) = e := rfl

@[ext]
theorem ext {f g : 𝒜₁ ≃ᵍᵃ 𝒜₂} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[refl]
def refl : 𝒜₁ ≃ᵍᵃ 𝒜₁ where
  __ := RingEquiv.refl A₁
  map_one' := rfl
  map_zero' := rfl
  map_mem' _ _ := id

@[trans] protected def trans (e₁₂ : 𝒜₁ ≃ᵍᵃ 𝒜₂) (e₂₃ : 𝒜₂ ≃ᵍᵃ 𝒜₃) : 𝒜₁ ≃ᵍᵃ 𝒜₃ where
  __ := RingEquiv.trans e₁₂.toRingEquiv e₂₃
  map_one' := by simp
  map_zero' := by simp
  map_mem' i x := e₂₃.map_mem ∘ e₁₂.map_mem

@[simp] lemma trans_apply (e₁₂ : 𝒜₁ ≃ᵍᵃ 𝒜₂) (e₂₃ : 𝒜₂ ≃ᵍᵃ 𝒜₃) (x : A₁) :
    (e₁₂.trans e₂₃) x = e₂₃ (e₁₂ x) := rfl

variable [DecidableEq ι] [AddMonoid ι] [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂]

@[symm]
protected def symm
    (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) : 𝒜₂ ≃ᵍᵃ 𝒜₁ where
  __ := RingEquiv.symm e
  map_one' := e.symm_apply_eq.mpr e.map_one.symm
  map_zero' := e.symm_apply_eq.mpr e.map_zero.symm
  map_mem' i x hx := by
    change e.toRingEquiv.symm x ∈ 𝒜₁ i
    classical
    rw [← DirectSum.sum_support_decompose 𝒜₁ (e.toRingEquiv.symm x : A₁)]
    refine sum_mem fun j hj ↦ ?_
    rw [DFinsupp.mem_support_iff, ne_eq, ← ZeroMemClass.coe_eq_zero, ← ne_eq,
      ← e.map_ne_zero_iff, coe_toRingEquiv, ← coe_toGradedAlgHom,
      e.toGradedAlgHom.map_coe_decompose, coe_toGradedAlgHom, ← coe_toRingEquiv, e.apply_symm_apply,
      DirectSum.decompose_of_mem _ hx, DirectSum.of_apply] at hj
    by_cases h : i = j
    · subst h; exact Subtype.prop _
    · rw [dif_neg h] at hj
      exact (hj rfl).elim

@[simp] lemma apply_symm_apply (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) (x : A₂) : e (e.symm x) = x := e.right_inv x

@[simp] lemma self_trans_symm (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) : e.trans e.symm = GradedAlgEquiv.refl :=
  ext e.left_inv

@[simp] lemma symm_trans_self (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) : e.symm.trans e = GradedAlgEquiv.refl :=
  ext e.right_inv

end GradedAlgEquiv

end arbitrary_index


section irrelevant

variable {R₁ R₂ ι : Type*} {A₁ A₂ : Type u}
  [CommRing R₁] [CommRing R₂] [CommRing A₁] [CommRing A₂] [Algebra R₁ A₁] [Algebra R₂ A₂]
  [DecidableEq ι] [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
  (𝒜₁ : ι → Submodule R₁ A₁) (𝒜₂ : ι → Submodule R₂ A₂)
  [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂] (e : 𝒜₁ ≃ᵍᵃ 𝒜₂)

theorem GradedAlgEquiv.admissible :
    HomogeneousIdeal.irrelevant 𝒜₂ ≤ (HomogeneousIdeal.irrelevant 𝒜₁).map e.toGradedAlgHom := by
  intro x hx
  rw [← e.apply_symm_apply x]
  refine Ideal.mem_map_of_mem _ (?_ : _ ∈ HomogeneousIdeal.irrelevant 𝒜₁)
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hx ⊢
  rw [← coe_toGradedAlgHom e.symm, ← e.symm.map_coe_decompose, hx, map_zero]

end irrelevant


namespace AlgebraicGeometry.Proj

open CategoryTheory HomogeneousIdeal

notation:max 𝒜"₊" => irrelevant 𝒜

variable {R₁ R₂ R₃ : Type*} {A₁ A₂ A₃ : Type u}
  [CommRing R₁] [CommRing R₂] [CommRing R₃]
  [CommRing A₁] [CommRing A₂] [CommRing A₃] [Algebra R₁ A₁] [Algebra R₂ A₂] [Algebra R₃ A₃]
  (𝒜₁ : ℕ → Submodule R₁ A₁) (𝒜₂ : ℕ → Submodule R₂ A₂) (𝒜₃ : ℕ → Submodule R₃ A₃)

-- MOVE
variable {𝒜₁ 𝒜₂ 𝒜₃} (f₂₃ : 𝒜₂ →ᵍᵃ 𝒜₃) (f₁₂ : 𝒜₁ →ᵍᵃ 𝒜₂)
def _root_.GradedAlgHom.comp : 𝒜₁ →ᵍᵃ 𝒜₃ where
  __ := f₂₃.toRingHom.comp f₁₂
  map_mem' _ _ := f₂₃.map_mem ∘ f₁₂.map_mem

def _root_.GradedAlgHom.id : 𝒜₁ →ᵍᵃ 𝒜₁ where
  __ := RingHom.id A₁
  map_mem' _ _ h := h

@[simp] lemma _root_.GradedAlgHom.id_apply (x : A₁) : (GradedAlgHom.id : 𝒜₁ →ᵍᵃ 𝒜₁) x = x := rfl

@[simp] lemma _root_.GradedAlgHom.comp_apply (x : A₁) :
    (f₂₃.comp f₁₂) x = f₂₃ (f₁₂ x) := rfl

@[simp] lemma _root_.GradedAlgEquiv.trans_toGradedAlgHom
    (e₁₂ : 𝒜₁ ≃ᵍᵃ 𝒜₂) (e₂₃ : 𝒜₂ ≃ᵍᵃ 𝒜₃) :
    (e₁₂.trans e₂₃).toGradedAlgHom = e₂₃.toGradedAlgHom.comp e₁₂.toGradedAlgHom :=
  rfl

@[simp] lemma _root_.GradedAlgEquiv.refl_toGradedAlgHom (𝒜 : ℕ → Submodule R₁ A₁) :
    (GradedAlgEquiv.refl : 𝒜 ≃ᵍᵃ 𝒜).toGradedAlgHom = GradedAlgHom.id := rfl

variable [GradedAlgebra 𝒜₁] [GradedAlgebra 𝒜₂] [GradedAlgebra 𝒜₃]

lemma _root_.HomogeneousIdeal.map_comp (P : HomogeneousIdeal 𝒜₁) :
    P.map (f₂₃.comp f₁₂) = (P.map f₁₂).map f₂₃ :=
  HomogeneousIdeal.ext (Ideal.map_map _ _).symm

variable {f₂₃ f₁₂} in
theorem _root_.GradedAlgHom.comp_admissible (h₁₂ : 𝒜₂₊ ≤ 𝒜₁₊.map f₁₂) (h₂₃ : 𝒜₃₊ ≤ 𝒜₂₊.map f₂₃) :
    𝒜₃₊ ≤ 𝒜₁₊.map (f₂₃.comp f₁₂) :=
  h₂₃.trans <| by rw [map_comp]; exact Ideal.map_mono h₁₂

theorem _root_.GradedAlgHom.id_admissible :
    𝒜₁₊ ≤ 𝒜₁₊.map (GradedAlgHom.id : 𝒜₁ →ᵍᵃ 𝒜₁) :=
  le_of_eq <| HomogeneousIdeal.ext (Ideal.map_id _).symm

theorem map_comp (h₁₂) (h₂₃) :
    map (f₂₃.comp f₁₂) (GradedAlgHom.comp_admissible h₁₂ h₂₃) = map f₂₃ h₂₃ ≫ map f₁₂ h₁₂ := by
  refine (mapAffineOpenCover _ (GradedAlgHom.comp_admissible h₁₂ h₂₃)).openCover.hom_ext _ _
    fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_X, Scheme.AffineOpenCover.openCover_f,
    mapAffineOpenCover_f]
  rw [awayι_comp_map _ _ _ _ s.2.2]
  simp only [GradedAlgHom.comp_apply]
  rw [awayι_comp_map_assoc _ _ _ _ (f₁₂.map_mem s.2.2), awayι_comp_map _ _ _ _ s.2.2,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  ext x
  obtain ⟨n, a, ha, rfl⟩ := x.mk_surjective _ s.2.2
  simp

theorem map_id : map .id GradedAlgHom.id_admissible = 𝟙 (Proj 𝒜₁) := by
  refine (affineOpenCover _).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [affineOpenCover, Proj.affineOpenCoverOfIrrelevantLESpan,
    Scheme.AffineOpenCover.openCover_X, Scheme.AffineOpenCover.openCover_f, Category.comp_id]
  conv_lhs => exact awayι_comp_map .id _ _ _ s.2.2
  generalize_proofs h₁ h₂ h₃
  have : HomogeneousLocalization.Away.map GradedAlgHom.id h₁ = RingHom.id _ := by
    ext x
    obtain ⟨n, a, ha, rfl⟩ := x.mk_surjective _ h₂
    simp
  rw [this, CommRingCat.ofHom_id, Spec.map_id]
  exact Category.id_comp _

@[simps] protected noncomputable def congr (e : 𝒜₁ ≃ᵍᵃ 𝒜₂) : Proj 𝒜₁ ≅ Proj 𝒜₂ where
  hom := Proj.map _ e.symm.admissible
  inv := Proj.map _ e.admissible
  hom_inv_id := by
    rw [← map_comp]
    generalize_proofs
    generalize he : e.symm.toGradedAlgHom.comp e.toGradedAlgHom = e' at *
    rw [← GradedAlgEquiv.trans_toGradedAlgHom, e.self_trans_symm,
      GradedAlgEquiv.refl_toGradedAlgHom] at he
    subst he
    rw [map_id]
  inv_hom_id := by
    rw [← map_comp]
    generalize_proofs
    generalize he : e.toGradedAlgHom.comp e.symm.toGradedAlgHom = e' at *
    rw [← GradedAlgEquiv.trans_toGradedAlgHom, e.symm_trans_self,
      GradedAlgEquiv.refl_toGradedAlgHom] at he
    subst he
    rw [map_id]

end AlgebraicGeometry.Proj

/-! # Tensor Product of Graded Algebra

In this file we show that if `A` is a graded `R`-algebra then `S ⊗[R] A` is a graded `S`-algebra.
-/

universe w

open DirectSum TensorProduct

@[simps!] def DirectSum.baseChangeLEquiv {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι]
    (M : ι → Type*) [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    (S : Type*) [Semiring S] [Algebra R S] :
    S ⊗[R] (⨁ i, M i) ≃ₗ[S] ⨁ i, S ⊗[R] M i where
  __ := directSumRight R S M
  map_smul' s x := by
    change directSumRight R S M (s • x) = s • directSumRight R S M x
    induction x with
    | zero => simp only [smul_zero, map_zero]
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul s₂ m => induction m using DirectSum.induction_on with
      | zero => simp only [tmul_zero, smul_zero, map_zero]
      | add m₁ m₂ hm₁ hm₂ => simp only [tmul_add, smul_add, map_add, hm₁, hm₂]
      | of i m => rw [← lof_eq_of R, smul_tmul', directSumRight_tmul_lof, directSumRight_tmul_lof,
          lof_eq_of, lof_eq_of, ← of_smul, smul_tmul']

theorem TensorProduct.congr_cast {R : Type*} [CommSemiring R] {ι : Type*}
    {M : ι → Type*} [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    {S : Type*} [AddCommMonoid S] [Module R S]
    {i j : ι} (h : i = j) :
    congr (.refl R S) (.cast h) = .cast (M := fun i ↦ S ⊗[R] M i) h := by
  subst h
  exact LinearEquiv.toLinearMap_injective <| ext' fun x y ↦ by simp

namespace GradedMonoid

theorem extₗ (R : Type*) [CommSemiring R] {ι : Type*}
    {A : ι → Type*} [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    {x y : GradedMonoid fun i ↦ A i}
    (h₁ : x.fst = y.fst) (h₂ : LinearEquiv.cast (R := R) h₁ x.snd = y.snd) : x = y := by
  obtain ⟨x₁, x₂⟩ := x
  obtain ⟨y₁, y₂⟩ := y
  dsimp only at h₁; subst h₁
  dsimp only at h₂; subst h₂
  rfl

@[simp] lemma gone {ι : Type*} [Zero ι] {A : ι → Type*} [GOne A] :
    GOne.one (A := A) = 1 :=
  rfl

@[simp] lemma one_gmul {ι : Type*} [AddMonoid ι]
    {A : ι → Type*} [GMonoid A] {i : ι} (x : A i) :
    GMul.mul (1 : A 0) x = cast (by rw [zero_add]) x :=
  eq_cast_iff_heq.mpr (Sigma.ext_iff.mp (GMonoid.one_mul ⟨_, x⟩)).2

@[simp] lemma gmul_one {ι : Type*} [AddMonoid ι]
    {A : ι → Type*} [GMonoid A] {i : ι} (x : A i) :
    GMul.mul x (1 : A 0) = cast (by rw [add_zero]) x :=
  eq_cast_iff_heq.mpr (Sigma.ext_iff.mp (GMonoid.mul_one ⟨_, x⟩)).2

@[simp] lemma gmul_assoc {ι : Type*} [AddMonoid ι]
    {A : ι → Type*} [GMonoid A] {i j k : ι} (x : A i) (y : A j) (z : A k) :
    GMul.mul (GMul.mul x y) z = cast (by rw [add_assoc]) (GMul.mul x (GMul.mul y z)) :=
  eq_cast_iff_heq.mpr (Sigma.ext_iff.mp (GMonoid.mul_assoc ⟨_, x⟩ ⟨_, y⟩ ⟨_, z⟩)).2

lemma gmul_comm {ι : Type*} [AddCommMonoid ι]
    {A : ι → Type*} [GCommMonoid A] {i j : ι} (x : A i) (y : A j) :
    GMul.mul x y = cast (by rw [add_comm]) (GMul.mul y x) :=
  eq_cast_iff_heq.mpr (Sigma.ext_iff.mp (GCommMonoid.mul_comm ⟨_, x⟩ ⟨_, y⟩)).2

instance GOne.tensorProduct {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddMonoid ι]
    (A : ι → Type*) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GSemiring A]
    (S : Type*) [AddCommMonoidWithOne S] [Module R S] :
    GOne fun i ↦ S ⊗[R] A i where
  one := 1

instance GMonoid.tensorProduct {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddMonoid ι]
    (A : ι → Type*) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GSemiring A] [GAlgebra R A]
    (S : Type*) [Semiring S] [Algebra R S] :
    GMonoid fun i ↦ S ⊗[R] A i where
  __ := GOne.tensorProduct A S
  mul x y := map₂ (LinearMap.mul R S) (gMulLHom R A) x y
  one_mul x := by
    refine extₗ R (by simp) ?_
    simp only [fst_mul, fst_one, snd_mul, snd_one, gone, Algebra.TensorProduct.one_def,
      map₂_apply_tmul]
    rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply]
    nth_rw 2 [← LinearMap.id_apply (R := R) x.snd]
    congr 1
    exact ext' (by simp_rw [← congr_cast]; simp)
  mul_one x := by
    refine extₗ R (by simp) ?_
    simp only [fst_mul, fst_one, snd_mul, snd_one, gone, Algebra.TensorProduct.one_def]
    rw [← LinearMap.flip_apply, ← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply]
    nth_rw 2 [← LinearMap.id_apply (R := R) x.snd]
    congr 1
    exact ext' (by simp_rw [← congr_cast]; simp)
  mul_assoc x y z := by
    refine extₗ R (by simp [add_assoc]) ?_
    simp only [fst_mul, snd_mul]
    induction x.snd using TensorProduct.induction_on with
    | zero => simp [-LinearEquiv.cast_apply]
    | add x₁ x₂ hx₁ hx₂ => simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
    | tmul s₁ a =>
      induction y.snd using TensorProduct.induction_on with
      | zero => simp [-LinearEquiv.cast_apply]
      | add y₁ y₂ hy₁ hy₂ => simp only [map_add, LinearMap.add_apply, hy₁, hy₂]
      | tmul s₂ b =>
        induction z.snd using TensorProduct.induction_on with
        | zero => simp [-LinearEquiv.cast_apply]
        | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
        | tmul s₃ c => rw [← congr_cast]; simp [_root_.mul_assoc]
  gnpow_zero' x := extₗ R (by simp) (by simp [GradedMonoid.mk, gnpowRec])
  gnpow_succ' n x := extₗ R (by simp) (by simp [GradedMonoid.mk, gnpowRec])

@[simp] lemma gmul_tensor_product {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddMonoid ι]
    (A : ι → Type*) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GSemiring A] [GAlgebra R A]
    (S : Type*) [Semiring S] [Algebra R S]
    {i j : ι} (x : S ⊗[R] A i) (y : S ⊗[R] A j) :
    GMul.mul (A := fun i ↦ S ⊗[R] A i) x y = map₂ (LinearMap.mul R S) (gMulLHom R A) x y :=
  rfl

instance GCommMonoid.tensorProduct {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    (A : ι → Type*) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GCommSemiring A] [GAlgebra R A]
    (S : Type*) [CommSemiring S] [Algebra R S] :
    GCommMonoid fun i ↦ S ⊗[R] A i where
  __ := GMonoid.tensorProduct A S
  mul_comm x y := by
    refine extₗ R (by simp [add_comm]) ?_
    simp only [fst_mul, snd_mul, gmul_tensor_product]
    induction x.snd using TensorProduct.induction_on with
    | zero => simp [-LinearEquiv.cast_apply]
    | add x₁ x₂ hx₁ hx₂ => simp only [map_add, LinearMap.add_apply, hx₁, hx₂]
    | tmul s₁ a =>
      induction y.snd using TensorProduct.induction_on with
      | zero => simp [-LinearEquiv.cast_apply]
      | add y₁ y₂ hy₁ hy₂ => simp only [map_add, LinearMap.add_apply, hy₁, hy₂]
      | tmul s₂ b => rw [← congr_cast]; simp [gmul_comm a, _root_.mul_comm s₁]

end GradedMonoid

namespace DirectSum

instance GCommSemiring.tensorProduct {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    (A : ι → Type*) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GCommSemiring A] [GAlgebra R A]
    (S : Type*) [CommSemiring S] [Algebra R S] :
    GCommSemiring fun i ↦ S ⊗[R] A i where
  __ := GradedMonoid.GCommMonoid.tensorProduct A S
  natCast n := n
  natCast_zero := by simp
  natCast_succ n := by simp
  mul_zero := by simp
  zero_mul := by simp
  mul_add := by simp
  add_mul := by simp

instance GAlgebra.tensorProduct {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    (A : ι → Type*) [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GCommSemiring A] [GAlgebra R A]
    (S : Type*) [CommSemiring S] [Algebra R S] :
    GAlgebra S fun i ↦ S ⊗[R] A i where
  toFun := (TensorProduct.mk R S (A 0)).flip 1
  map_one := rfl
  map_mul x y := GradedMonoid.extₗ R (by simp [GradedMonoid.mk])
    (by rw [← congr_cast]; simp [GradedMonoid.mk])
  commutes s x := by
    refine GradedMonoid.extₗ R (by simp [GradedMonoid.mk]) ?_
    simp_rw [← congr_cast, GradedMonoid.snd_mul, GradedMonoid.gmul_tensor_product, GradedMonoid.mk,
      GradedMonoid.fst_mul]
    rw [← LinearMap.flip_apply (m := x.snd), ← LinearEquiv.coe_toLinearMap, ← LinearMap.comp_apply]
    congr 1
    ext; simp [_root_.mul_comm]
  smul_def s x := by
    refine GradedMonoid.extₗ R (by simp [GradedMonoid.mk]) ?_
    simp only [AddMonoidHom.coe_coe, LinearMap.flip_apply, mk_apply, GradedMonoid.fst_mul,
      GradedMonoid.fst_smul, GradedMonoid.snd_smul, GradedMonoid.snd_mul,
      GradedMonoid.gmul_tensor_product, GradedMonoid.mk]
    induction x.snd using TensorProduct.induction_on with
    | zero => simp [-LinearEquiv.cast_apply]
    | add x₁ x₂ hx₁ hx₂ => simp only [smul_add, map_add, hx₁, hx₂]
    | tmul r a => rw [← congr_cast]; simp [smul_tmul']

end DirectSum

def DirectSum.baseChangeAlgEquiv {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A : ι → Type*} [∀ i, AddCommMonoid (A i)] [∀ i, Module R (A i)]
    [GCommSemiring A] [GAlgebra R A]
    {S : Type*} [CommSemiring S] [Algebra R S] :
    S ⊗[R] DirectSum ι A ≃ₐ[S] ⨁ i, S ⊗[R] A i where
  __ := directSumRight R S A
  map_mul' x y := by
    dsimp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x₁ x₂ hx₁ hx₂ => simp only [add_mul, map_add, hx₁, hx₂]
    | tmul s₁ a₁ =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ hy₁ hy₂ => simp only [mul_add, map_add, hy₁, hy₂]
      | tmul s₂ a₂ =>
        induction a₁ using DirectSum.induction_on with
        | zero => simp
        | add a₁ b₁ ha₁ hb₁ => simp only [tmul_add, add_mul, map_add, ha₁, hb₁]
        | of i a₁ =>
          induction a₂ using DirectSum.induction_on with
          | zero => simp
          | add a₂ b₂ ha₂ hb₂ => simp only [tmul_add, mul_add, map_add, ha₂, hb₂]
          | of j a₂ => simp_rw [Algebra.TensorProduct.tmul_mul_tmul, of_mul_of,
              ← lof_eq_of R, directSumRight_tmul_lof, lof_eq_of, of_mul_of,
              GradedMonoid.gmul_tensor_product]; simp
  commutes' s := by
    dsimp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    rw [DirectSum.one_def, ← lof_eq_of R, directSumRight_tmul_lof, algebraMap_apply]
    rfl

def DirectSum.lequivOfComponents {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A₁ : ι → Type*} [∀ i, AddCommMonoid (A₁ i)] [∀ i, Module R (A₁ i)]
    {A₂ : ι → Type*} [∀ i, AddCommMonoid (A₂ i)] [∀ i, Module R (A₂ i)]
    (e : ∀ i, A₁ i ≃ₗ[R] A₂ i) :
    DirectSum ι A₁ ≃ₗ[R] DirectSum ι A₂ :=
  .ofLinear (toModule _ _ _ (fun i ↦ lof R ι A₂ i ∘ₗ e i))
    (toModule _ _ _ (fun i ↦ lof R ι A₁ i ∘ₗ (e i).symm))
    (by ext; simp)
    (by ext; simp)

def DirectSum.algEquivOfComponents {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
    {A₁ : ι → Type*} [∀ i, AddCommMonoid (A₁ i)] [∀ i, Module R (A₁ i)]
    {A₂ : ι → Type*} [∀ i, AddCommMonoid (A₂ i)] [∀ i, Module R (A₂ i)]
    [GCommSemiring A₁] [GAlgebra R A₁]
    [GCommSemiring A₂] [GAlgebra R A₂]
    (e : ∀ i, A₁ i ≃ₗ[R] A₂ i)
    (one : e 0 1 = 1)
    (mul : ∀ {i j} (x : A₁ i) (y : A₁ j), e (i + j) (GradedMonoid.GMul.mul x y) =
      GradedMonoid.GMul.mul (e i x) (e j y)) :
    DirectSum ι A₁ ≃ₐ[R] DirectSum ι A₂ :=
  .ofAlgHom (toAlgebra _ _ (fun i ↦ lof R ι A₂ i ∘ₗ e i) (by simp [one, lof_eq_of])
      fun xi xj ↦ by simp [mul, lof_eq_of, of_mul_of])
    (toAlgebra _ _ (fun i ↦ lof R ι A₁ i ∘ₗ (e i).symm) (by simp [← one, lof_eq_of])
      fun xi xj ↦ by simp [lof_eq_of, of_mul_of, ← (e _).symm_apply_eq.mpr (mul _ _).symm])
    (by ext; simp [lof_eq_of])
    (by ext; simp [lof_eq_of])

def Submodule.toBaseChange {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (S : Type*) [Semiring S] [Algebra R S]
    (N : Submodule R M) : S ⊗[R] N →ₗ[S] N.baseChange S :=
  LinearMap.rangeRestrict _

@[simp] lemma Submodule.toBaseChange_tmul_coe {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (S : Type*) [Semiring S] [Algebra R S]
    (N : Submodule R M) (s : S) (n : N) :
    Submodule.toBaseChange S N (s ⊗ₜ[R] n) = s ⊗ₜ[R] (n : M) :=
  rfl

lemma Submodule.toBaseChange_surjective {R : Type*} [CommSemiring R]
    {M : Type*} [AddCommMonoid M] [Module R M]
    (S : Type*) [Semiring S] [Algebra R S]
    (N : Submodule R M) :
    Function.Surjective (Submodule.toBaseChange S N) :=
  LinearMap.surjective_rangeRestrict _

lemma Function.Bijective.of_comp_of_surjective {α β γ : Sort*} {f : β → γ} {g : α → β}
    (hfg : Function.Bijective (f ∘ g)) (hg : Function.Surjective g) : Function.Bijective f :=
  ⟨.of_comp_right hfg.injective hg, .of_comp hfg.surjective⟩

private theorem DirectSum.IsInternal.baseChange_aux {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι]
    {A : Type*} [AddCommMonoid A] [Module R A]
    {𝒜 : ι → Submodule R A} (internal : IsInternal 𝒜)
    (S : Type*) [Semiring S] [Algebra R S] :
    (IsInternal fun i ↦ (𝒜 i).baseChange S) ∧ ∀ i, Function.Injective ((𝒜 i).toBaseChange S) := by
  have := internal.chooseDecomposition
  let e := (baseChangeLEquiv (R := R) (fun i ↦ 𝒜 i) S).symm ≪≫ₗ
    (decomposeLinearEquiv 𝒜).symm.baseChange R S
  let e₁ : (⨁ i, S ⊗[R] 𝒜 i) →ₗ[S] ⨁ i, (𝒜 i).baseChange S :=
    lmap fun i ↦ (𝒜 i).toBaseChange S
  let e₂ : (⨁ i, (𝒜 i).baseChange S) →ₗ[S] S ⊗[R] A :=
    toModule _ _ _ fun i ↦ Submodule.subtype _
  have he : e₂ ∘ₗ e₁ = e := by
    ext
    simp only [AlgebraTensorModule.curry_apply, curry_apply,
      LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply, lmap_lof,
      toModule_lof, Submodule.subtype_apply, Submodule.toBaseChange_tmul_coe, LinearEquiv.coe_coe,
      LinearEquiv.trans_apply, baseChangeLEquiv_symm_apply, e₂, e₁, e]
    rw [lof_eq_of S, ← lof_eq_of R, directSumRight_symm_lof_tmul]
    simp [LinearEquiv.baseChange, lof_eq_of]
  have he' : e₂ ∘ e₁ = e := congr($he)
  have he₂ : Function.Bijective e₂ :=
    .of_comp_of_surjective (g := e₁) (he' ▸ e.bijective)
      ((lmap_surjective _).mpr fun _ ↦ LinearMap.surjective_rangeRestrict _)
  have he₁ : Function.Injective e₁ := .of_comp (f := e₂) (he' ▸ e.injective)
  exact ⟨he₂, fun i x y h ↦ of_injective (β := fun i ↦ S ⊗[R] 𝒜 i) i <| he₁ <| by simp [e₁, h]⟩

theorem DirectSum.IsInternal.baseChange {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι]
    {A : Type*} [AddCommMonoid A] [Module R A]
    {𝒜 : ι → Submodule R A} (internal : IsInternal 𝒜)
    (S : Type*) [Semiring S] [Algebra R S] :
    IsInternal fun i ↦ (𝒜 i).baseChange S :=
  (internal.baseChange_aux S).1

theorem DirectSum.IsInternal.toBaseChange_bijective {R : Type*} [CommSemiring R]
    {ι : Type*} [DecidableEq ι]
    {A : Type*} [AddCommMonoid A] [Module R A]
    {𝒜 : ι → Submodule R A} (internal : IsInternal 𝒜)
    (S : Type*) [Semiring S] [Algebra R S] (i : ι) :
    Function.Bijective (Submodule.toBaseChange S (𝒜 i)) :=
  ⟨(internal.baseChange_aux S).2 i, (𝒜 i).toBaseChange_surjective S⟩

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  {ι : Type*} [DecidableEq ι] [AddCommMonoid ι]
  (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
  (S : Type*) [CommRing S] [Algebra R S]

namespace GradedAlgebra

open TensorProduct Submodule DirectSum

instance : SetLike.GradedMonoid (fun n ↦ (𝒜 n).baseChange S) where
  one_mem := by
    rw [Algebra.TensorProduct.one_def]
    exact tmul_mem_baseChange_of_mem _ (SetLike.one_mem_graded _)
  mul_mem {i j} := by
    suffices h : (𝒜 i).baseChange S * (𝒜 j).baseChange S ≤ (𝒜 (i + j)).baseChange S from
      fun _ _ hx hy ↦ h (mul_mem_mul hx hy)
    rw [baseChange_eq_span, baseChange_eq_span, span_mul_span, span_le, Set.mul_subset_iff]
    rintro - ⟨x, hx, rfl⟩ - ⟨y, hy, rfl⟩
    simp only [mk_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    exact tmul_mem_baseChange_of_mem _ (SetLike.mul_mem_graded hx hy)

-- def tensorProductAlgEquiv : S ⊗[R] A ≃ₐ[S] ⨁ i, (𝒜 i).baseChange S :=
--   (Algebra.TensorProduct.congr AlgEquiv.refl (DirectSum.decomposeAlgEquiv 𝒜)).trans <|
--     (baseChangeAlgEquiv (R := R) (S := S) (A := fun i ↦ 𝒜 i)).trans <|
--       algEquivOfComponents (fun i ↦ .ofBijective ((𝒜 i).toBaseChange S) _)  _  _

noncomputable def baseChangeLEquiv (n : ι) : S ⊗[R] 𝒜 n ≃ₗ[S] (𝒜 n).baseChange S :=
  LinearEquiv.ofBijective _ ((Decomposition.isInternal 𝒜).toBaseChange_bijective S n)

noncomputable instance : GradedAlgebra (fun n ↦ (𝒜 n).baseChange S) :=
  ((Decomposition.isInternal 𝒜).baseChange S).gradedAlgebra

/- where
  one_mem := by
    rw [Algebra.TensorProduct.one_def]
    exact tmul_mem_baseChange_of_mem _ (SetLike.one_mem_graded _)
  mul_mem {i j} := by
    suffices h : (𝒜 i).baseChange S * (𝒜 j).baseChange S ≤ (𝒜 (i + j)).baseChange S from
      fun _ _ hx hy ↦ h (mul_mem_mul hx hy)
    rw [baseChange_eq_span, baseChange_eq_span, span_mul_span, span_le, Set.mul_subset_iff]
    rintro - ⟨x, hx, rfl⟩ - ⟨y, hy, rfl⟩
    simp only [mk_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    exact tmul_mem_baseChange_of_mem _ (SetLike.mul_mem_graded hx hy)
  decompose' := _ -/

end GradedAlgebra

/-! # Proj of Tensor Product

In this file we show `Proj (S ⊗[R] 𝒜) ≅ Spec S ×_R Proj 𝒜` where `𝒜` is a graded `R`-algebra.
-/

open TensorProduct in
def AlgHom.liftBaseChange {R S A B : Type*}
    [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f : A →ₐ[R] B) :
    S ⊗[R] A →ₐ[S] B :=
  .ofLinearMap (.liftBaseChange S f) (by simp [Algebra.TensorProduct.one_def]) fun x y ↦ by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x₁ x₂ hx₁ hx₂ => simp [add_mul, hx₁, hx₂]
    | tmul s₁ a₁ => induction y using TensorProduct.induction_on with
      | zero => simp
      | add y₁ y₂ hy₁ hy₂ => simp [mul_add, hy₁, hy₂]
      | tmul s₂ a₂ => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_smul, smul_comm s₁]

@[simp] lemma AlgHom.liftBaseChange_tmul {R S A B : Type*}
    [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
    [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S B] [IsScalarTower R S B]
    (f : A →ₐ[R] B) (s : S) (a : A) :
    f.liftBaseChange (s ⊗ₜ a) = s • f a := rfl

open TensorProduct in
@[ext high] theorem Algebra.TensorProduct.ext_ring {R S A B : Type*}
    [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
    [CommSemiring S] [Algebra R S] [Algebra S B] [IsScalarTower R S B]
    {f g : S ⊗[R] A →ₐ[S] B}
    (h : (AlgHom.restrictScalars R f).comp Algebra.TensorProduct.includeRight =
      (AlgHom.restrictScalars R g).comp Algebra.TensorProduct.includeRight) :
    f = g :=
  ext (Subsingleton.elim _ _) h

section degree

noncomputable def DirectSum.degree {ι M σ : Type*} [Zero M] [SetLike σ M] [ZeroMemClass σ M]
    [Zero ι] (ℳ : ι → σ) (x : M) : ι :=
  open Classical in if h : x ≠ 0 ∧ ∃ i, x ∈ ℳ i then h.2.choose else 0

namespace DirectSum

variable {ι M σ : Type*} [SetLike σ M] (ℳ : ι → σ)

theorem degree_of_mem [AddCommMonoid M] [DecidableEq ι] [Zero ι] [AddSubmonoidClass σ M]
    [Decomposition ℳ] (x : M) (i : ι) (hx₀ : x ≠ 0) (hxi : x ∈ ℳ i) : degree ℳ x = i := by
  rw [degree, dif_pos ⟨hx₀, _, hxi⟩]
  generalize_proofs h
  exact degree_eq_of_mem_mem _ h.choose_spec hxi hx₀

theorem mem_degree [AddCommMonoid M] [DecidableEq ι] [Zero ι] [AddSubmonoidClass σ M]
    [Decomposition ℳ] (x : M) (hx : SetLike.IsHomogeneousElem ℳ x) : x ∈ ℳ (degree ℳ x) := by
  by_cases hx₀ : x = 0
  · rw [hx₀]; exact zero_mem _
  obtain ⟨i, hxi⟩ := hx
  rwa [degree_of_mem ℳ x i hx₀ hxi]

theorem decompose_of_homogeneous [AddCommMonoid M] [DecidableEq ι] [Zero ι] [AddSubmonoidClass σ M]
    [Decomposition ℳ] (x : M) (hx : SetLike.IsHomogeneousElem ℳ x) :
    decompose ℳ x = of (fun i ↦ ℳ i) (degree ℳ x) (⟨x, mem_degree ℳ x hx⟩ : ℳ _) :=
  decompose_of_mem ℳ _

theorem degree_mul [Semiring M] [AddSubmonoidClass σ M] [DecidableEq ι] [AddMonoid ι]
    [GradedRing ℳ] (x y : M) (hx : SetLike.IsHomogeneousElem ℳ x)
    (hy : SetLike.IsHomogeneousElem ℳ y) (hxy : x * y ≠ 0) :
    degree ℳ (x * y) = degree ℳ x + degree ℳ y :=
  degree_of_mem _ _ _ hxy <| SetLike.mul_mem_graded (mem_degree _ _ hx) (mem_degree _ _ hy)

theorem coe_apply_congr [AddCommMonoid M] [AddSubmonoidClass σ M]
    {x : ⨁ i, ℳ i} {i j : ι} (h : i = j) : (x i : M) = x j := by
  subst h; rfl

end DirectSum

end degree

open DirectSum in
noncomputable def HomogeneousLocalization.proj₀ {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
    (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (S : Submonoid A) (homog : S ≤ SetLike.homogeneousSubmonoid 𝒜) :
    Localization S →ₗ[HomogeneousLocalization 𝒜 S] HomogeneousLocalization 𝒜 S where
  toFun x := x.liftOn (fun a s ↦ .mk ⟨degree 𝒜 s.1, decompose 𝒜 a _,
    ⟨s, mem_degree _ _ (homog s.2)⟩, s.2⟩) fun {a₁ a₂} {s₁ s₂} h ↦ by
      ext
      simp_rw [val_mk, Localization.mk_eq_mk_iff]
      rw [Localization.r_iff_exists] at h ⊢
      obtain ⟨s, hs⟩ := h
      refine ⟨s, ?_⟩
      have hs' := congr((decompose 𝒜 $hs (degree 𝒜 (s : A) +
        (degree 𝒜 (s₁ : A) + degree 𝒜 (s₂ : A))) : A))
      simp_rw [decompose_mul, decompose_of_homogeneous _ _ (homog s.2),
        decompose_of_homogeneous _ _ (homog s₁.2), decompose_of_homogeneous _ _ (homog s₂.2),
        coe_of_mul_apply_add, coe_apply_congr _ (add_comm (degree 𝒜 (s₁ : A)) _),
        coe_of_mul_apply_add] at hs'
      exact hs'
  map_add' x y := Localization.induction_on₂ x y fun c d ↦ by
    ext
    by_cases hs₀ : 0 ∈ S
    · subsingleton [IsLocalization.uniqueOfZeroMem hs₀]
    have ne_zero {x} (hx : x ∈ S) : (x : A) ≠ 0 := fun hx₀ ↦ hs₀ <| hx₀ ▸ hx
    simp_rw [val_add, Localization.add_mk, Localization.liftOn_mk, val_mk,
      Localization.add_mk, decompose_add, add_apply, Submonoid.coe_mul, decompose_mul,
      Submodule.coe_add, Subtype.coe_eta]
    rw [degree_mul _ _ _ (homog c.2.2) (homog d.2.2) (ne_zero (c.2 * d.2).2),
      decompose_of_homogeneous _ _ (homog c.2.2),
      decompose_of_homogeneous _ _ (homog d.2.2),
      coe_of_mul_apply_add, coe_apply_congr _ (add_comm (degree 𝒜 (c.2 : A)) _),
      coe_of_mul_apply_add]
    rfl
  map_smul' r x := Localization.induction_on x fun d ↦ by
    obtain ⟨c, rfl⟩ := mk_surjective r
    ext
    by_cases hs₀ : 0 ∈ S
    · subsingleton [IsLocalization.uniqueOfZeroMem hs₀]
    have ne_zero {x} (hx : x ∈ S) : (x : A) ≠ 0 := fun hx₀ ↦ hs₀ <| hx₀ ▸ hx
    rw [RingHom.id_apply, Algebra.smul_def, smul_eq_mul, val_mul, algebraMap_apply, val_mk]
    simp_rw [Localization.mk_mul, Localization.liftOn_mk, val_mk, Localization.mk_mul,
      decompose_mul, decompose_coe, Subtype.coe_eta, Submonoid.coe_mul]
    rw [degree_mul _ _ _ ⟨_, c.den.2⟩ (homog d.2.2) (ne_zero <| S.mul_mem c.den_mem d.2.2),
      degree_of_mem _ _ _ (ne_zero c.den_mem) c.den.2,
      coe_of_mul_apply_add]

theorem HomogeneousLocalization.proj₀_mk {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
    (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (S : Submonoid A) (homog : S ≤ SetLike.homogeneousSubmonoid 𝒜)
    (a : A) (s : S) :
    HomogeneousLocalization.proj₀ 𝒜 S homog (Localization.mk a s) =
    HomogeneousLocalization.mk ⟨DirectSum.degree 𝒜 (s : A), DirectSum.decompose 𝒜 a _,
      ⟨s, DirectSum.mem_degree _ _ (homog s.2)⟩, s.2⟩ := rfl

@[simp] lemma HomogeneousLocalization.proj₀_val {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
    (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    (S : Submonoid A) (homog : S ≤ SetLike.homogeneousSubmonoid 𝒜)
    (x : HomogeneousLocalization 𝒜 S) :
    HomogeneousLocalization.proj₀ 𝒜 S homog x.val = x := by
  ext
  by_cases hs₀ : 0 ∈ S
  · subsingleton [IsLocalization.uniqueOfZeroMem hs₀]
  induction x using Quotient.inductionOn' with
  | h c =>
    simp_rw [val, Quotient.liftOn'_mk'', NumDenSameDeg.embedding, proj₀_mk, mk,
      Quotient.liftOn'_mk'', NumDenSameDeg.embedding]
    rw [DirectSum.decompose_of_mem _ c.num.2, DirectSum.coe_of_apply, if_pos]
    rw [DirectSum.degree_of_mem _ _ _ (mt (· ▸ c.den_mem) hs₀) c.den.2]

noncomputable def HomogeneousLocalization.Away.proj₀ {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
    (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i : ι} {f : A} (hf : f ∈ 𝒜 i) :
    Localization.Away (f : A) →ₗ[HomogeneousLocalization.Away 𝒜 f]
      HomogeneousLocalization.Away 𝒜 f :=
  HomogeneousLocalization.proj₀ _ _ <| Submonoid.powers_le.mpr ⟨_, hf⟩

theorem HomogeneousLocalization.Away.proj₀_mk {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
    (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i : ι} {f : A} (hf : f ∈ 𝒜 i) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • i)) :
    proj₀ 𝒜 hf (.mk a ⟨f ^ n, n, rfl⟩) = .mk _ hf n a ha :=
  proj₀_val _ _ _ (Away.mk _ hf _ _ _)

theorem HomogeneousLocalization.Away.proj₀_mk' {R A : Type*}
    [CommRing R] [CommRing A] [Algebra R A] {ι : Type*} [DecidableEq ι] [AddCancelCommMonoid ι]
    (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜]
    {i : ι} {f : A} (hf : f ∈ 𝒜 i) (n : ℕ) (a : 𝒜 (n • i)) :
    proj₀ 𝒜 hf (.mk a ⟨f ^ n, n, rfl⟩) = .lof _ hf n a :=
  proj₀_mk _ _ _ _ _

open TensorProduct in
/-- `(S ⊗[R] A)[(1 ⊗ₜ W)⁻¹] ≅ (S ⊗[R] A)[W⁻¹]`. -/
noncomputable def IsLocalization.tensorEquiv (R S A A₁ SA₁ : Type*)
    [CommSemiring R] [CommSemiring S] [CommSemiring A] [CommSemiring A₁] [CommSemiring SA₁]
    [Algebra R S] [Algebra R A] (W₁ : Submonoid A) (W₂ : Submonoid (S ⊗[R] A))
    (hw : W₁.map Algebra.TensorProduct.includeRight = W₂)
    [Algebra A A₁] [IsLocalization W₁ A₁]
    [Algebra R A₁] [IsScalarTower R A A₁]
    [Algebra (S ⊗[R] A) SA₁] [IsLocalization W₂ SA₁]
    [Algebra R SA₁] [Algebra S SA₁] [IsScalarTower R S SA₁] [IsScalarTower S (S ⊗[R] A) SA₁]
    [IsScalarTower R (S ⊗[R] A) SA₁] :
    SA₁ ≃ₐ[S] S ⊗[R] A₁ :=
  .ofAlgHom
  (IsLocalization.liftAlgHom
    (M := W₂)
    (f := Algebra.TensorProduct.map (1 : S →ₐ[S] S) (Algebra.algHom R A A₁)) <| by
      rw [← hw]
      rintro ⟨_, w, hw, rfl⟩
      exact (IsLocalization.map_units _ ⟨w, hw⟩).map Algebra.TensorProduct.includeRight)
  (AlgHom.liftBaseChange <| IsLocalization.liftAlgHom (M := W₁)
    (f := (Algebra.algHom _ _ _).comp (Algebra.TensorProduct.includeRight (R := R) (A := S)))
    fun w ↦ IsLocalization.map_units (M := W₂) SA₁ ⟨_, hw ▸ ⟨_, w.2, rfl⟩⟩)
  (Algebra.TensorProduct.ext_ring <| IsLocalization.algHom_ext W₁ <| by ext; simp [Algebra.algHom])
  (IsLocalization.algHom_ext W₂ <| by ext; simp [Algebra.algHom])

open TensorProduct in
/-- `(S ⊗[R] A)[(1 ⊗ₜ W)⁻¹] ≅ S ⊗[R] A[W⁻¹]`. -/
noncomputable def Localization.tensorEquiv (R S : Type*) {A : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring A]
    [Algebra R S] [Algebra R A] (W : Submonoid A) :
    Localization (W.map (Algebra.TensorProduct.includeRight (R := R) (A := S))) ≃ₐ[S]
    S ⊗[R] Localization W :=
  IsLocalization.tensorEquiv R S A _ _ W _ rfl

open TensorProduct in
/-- `(S ⊗[R] A)[(1 ⊗ₜ f)⁻¹] ≅ S ⊗[R] A[f⁻¹]`. -/
noncomputable def Localization.Away.tensorEquiv (R S : Type*) {A : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring A]
    [Algebra R S] [Algebra R A] (f : A) :
    Away (1 ⊗ₜ[R] f : S ⊗[R] A) ≃ₐ[S] S ⊗[R] Away f :=
  IsLocalization.tensorEquiv R S A _ _ (.powers f) (.powers (1 ⊗ₜ f)) (by simp)

@[simp] lemma Localization.Away.tensorEquiv_mk {R S : Type*} {A : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring A]
    [Algebra R S] [Algebra R A] (f : A) (s : S) (a : A) (n : ℕ) :
    tensorEquiv R S f (.mk (s ⊗ₜ a) ⟨1 ⊗ₜ (f ^ n), n, by simp⟩) = s ⊗ₜ .mk a ⟨f ^ n, n, rfl⟩ := by
  simp_rw [tensorEquiv, IsLocalization.tensorEquiv, AlgEquiv.ofAlgHom_apply,
    IsLocalization.liftAlgHom_apply, mk_eq_mk', IsLocalization.lift_mk',
    Units.mul_inv_eq_iff_eq_mul, IsUnit.coe_liftRight]
  simp only [Algebra.algHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Algebra.TensorProduct.map_tmul, AlgHom.one_apply, AlgHom.coe_mk, ← mk_one_eq_algebraMap,
    ← mk_eq_mk', RingHom.toMonoidHom_eq_coe, AlgHom.toRingHom_toMonoidHom,
    MonoidHom.restrict_apply, MonoidHom.coe_coe, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    mk_mul]
  congr 1
  exact mk_eq_mk_iff.mpr <| r_iff_exists.mpr ⟨1, by simp [mul_comm]⟩

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
  (S : Type u) [CommRing S] [Algebra R S]

namespace AlgebraicGeometry

open TensorProduct CategoryTheory Limits CommRingCat

noncomputable def Proj.toSpec : Proj 𝒜 ⟶ Spec(R) :=
  Proj.toSpecZero 𝒜 ≫ Spec.map (ofHom (algebraMap R (𝒜 0)))

lemma baseChange_iSupEqTop :
    (HomogeneousIdeal.irrelevant fun n ↦ (𝒜 n).baseChange S).toIdeal ≤
    Ideal.span (Set.range fun f : (Proj.affineOpenCover 𝒜).I₀ ↦ 1 ⊗ₜ[R] f.2) := by
  intro x hx
  classical
  rw [← DirectSum.sum_support_decompose (fun n ↦ (𝒜 n).baseChange S) x]
  refine sum_mem fun i hi ↦ ?_
  have hi₀ : i ≠ 0 := fun hi₀ ↦ DFinsupp.mem_support_iff.mp hi (hi₀ ▸ by simpa using hx)
  generalize DirectSum.decompose (fun n ↦ (𝒜 n).baseChange S) x i = y
  obtain ⟨_, y, rfl⟩ := y
  obtain ⟨s, rfl⟩ := exists_finset y
  simp only [map_sum, LinearMap.baseChange_tmul, Submodule.subtype_apply]
  refine Ideal.sum_mem _ fun c hc ↦ ?_
  rw [← mul_one c.1, ← one_mul (c.2: A), ← Algebra.TensorProduct.tmul_mul_tmul]
  refine Ideal.mul_mem_left _ _ <| Ideal.subset_span ⟨⟨⟨i, pos_of_ne_zero hi₀⟩, _⟩, rfl⟩

set_option maxHeartbeats 999999 in
-- I don't know why
noncomputable def awayBaseChange {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) :
    HomogeneousLocalization.Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f) ≃ₐ[S]
      S ⊗[R] HomogeneousLocalization.Away 𝒜 f := by
  let f₁ : HomogeneousLocalization.Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f) →ₐ[S]
      Localization.Away (1 ⊗ₜ f : S ⊗[R] A) := Algebra.algHom _ _ _
  let f₂ : Localization.Away (1 ⊗ₜ f : S ⊗[R] A) ≃ₐ[S]
      S ⊗[R] Localization.Away (f : A) := Localization.Away.tensorEquiv _ _ _
  let f₃ : S ⊗[R] Localization.Away (f : A) →ₗ[S] S ⊗[R] HomogeneousLocalization.Away 𝒜 f :=
    ((HomogeneousLocalization.Away.proj₀ 𝒜 hf).restrictScalars R).baseChange S
  let forwards : HomogeneousLocalization.Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f) →ₗ[S]
      S ⊗[R] HomogeneousLocalization.Away 𝒜 f :=
    f₃ ∘ₗ f₂.toLinearMap ∘ₗ f₁.toLinearMap
  let backwards : S ⊗[R] HomogeneousLocalization.Away 𝒜 f →ₐ[S]
      HomogeneousLocalization.Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f) :=
    AlgHom.liftBaseChange <| HomogeneousLocalization.Away.mapₐ
      (Algebra.TensorProduct.includeRight (R := R) (A := S))
      (fun _ _ ↦ Submodule.tmul_mem_baseChange_of_mem _) rfl
  refine
    have left : backwards.toLinearMap ∘ₗ forwards = 1 := ?_
    have right : forwards ∘ₗ backwards.toLinearMap = 1 := ?_
    .symm { __ := backwards, invFun := forwards, left_inv := ?_, right_inv := ?_ }
  · ext x
    obtain ⟨n, a, rfl⟩ := x.lof_surjective _ (Submodule.tmul_mem_baseChange_of_mem _ hf)
    obtain ⟨a, rfl⟩ := Submodule.toBaseChange_surjective _ _ a
    simp only [smul_eq_mul, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
      Module.End.one_apply]
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add a₁ a₂ ha₁ ha₂ => simp [ha₁, ha₂]
    | tmul s a =>
      simp only [forwards, f₁, f₂, f₃, backwards, Algebra.algHom]
      simp only [smul_eq_mul, LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        AlgHom.coe_mk, HomogeneousLocalization.algebraMap_apply, AlgEquiv.toLinearMap_apply]
      erw [HomogeneousLocalization.Away.val_lof]
      simp only [smul_eq_mul, Submodule.toBaseChange_tmul_coe, Algebra.TensorProduct.tmul_pow,
        one_pow, Localization.Away.tensorEquiv_mk, LinearMap.baseChange_tmul,
        LinearMap.coe_restrictScalars, HomogeneousLocalization.Away.proj₀_mk',
        AlgHom.liftBaseChange_tmul, HomogeneousLocalization.val_smul]
      erw [HomogeneousLocalization.Away.mapₐ_lof]
      rw [HomogeneousLocalization.Away.val_lof]
      simp only [smul_eq_mul, Algebra.TensorProduct.includeRight_apply,
        Algebra.TensorProduct.tmul_pow, one_pow, Localization.smul_mk]
      congr 1
      rw [← tmul_eq_smul_one_tmul]
  · ext x
    obtain ⟨n, a, rfl⟩ := x.lof_surjective _ hf
    simp only [forwards, f₁, f₂, f₃, backwards, Algebra.algHom]
    simp only [AlgebraTensorModule.curry_apply, LinearMap.restrictScalars_comp, smul_eq_mul,
      curry_apply, LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
      AlgHom.toLinearMap_apply, AlgHom.liftBaseChange_tmul, one_smul, AlgHom.coe_mk,
      HomogeneousLocalization.algebraMap_apply, AlgEquiv.toLinearMap_apply, Module.End.one_apply]
    erw [HomogeneousLocalization.Away.mapₐ_lof]
    rw [HomogeneousLocalization.Away.val_lof]
    simp [HomogeneousLocalization.Away.proj₀_mk']
  · exact fun x ↦ congr($right x)
  · exact fun x ↦ congr($left x)

@[simps!] def _root_.GradedAlgebra.toTensor : 𝒜 →ᵍᵃ fun n ↦ (𝒜 n).baseChange S where
  __ := Algebra.TensorProduct.includeRight
  map_mem' _ _ := Submodule.tmul_mem_baseChange_of_mem _

lemma _root_.GradedAlgebra.toTensor_admissible :
    (HomogeneousIdeal.irrelevant fun n ↦ (𝒜 n).baseChange S) ≤
    (HomogeneousIdeal.irrelevant 𝒜).map (GradedAlgebra.toTensor 𝒜 S) := by
  refine (HomogeneousIdeal.irrelevant_le _).mpr fun i hi x hx ↦ ?_
  obtain ⟨a, ha⟩ := Submodule.toBaseChange_surjective _ _ ⟨x, hx⟩
  replace ha := congr(($ha).val); subst ha
  induction a with
  | zero => simp
  | add => simp [*, add_mem]
  | tmul s a =>
    simp only [Submodule.toBaseChange_tmul_coe]
    rw [tmul_eq_smul_one_tmul, ← algebraMap_smul (S ⊗[R] A), smul_eq_mul]
    exact Ideal.mul_mem_left _ _ <| Ideal.mem_map_of_mem _ <|
      HomogeneousIdeal.mem_irrelevant_of_mem _ hi a.2

@[simp] lemma awayBaseChange_symm_tmul
    {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) {s : S} {x : HomogeneousLocalization.Away 𝒜 f} :
    (awayBaseChange 𝒜 S hf).symm (s ⊗ₜ x) =
    s • .map (GradedAlgebra.toTensor 𝒜 S) rfl x := by
  obtain ⟨n, a, rfl⟩ := x.lof_surjective _ hf
  rw [AlgEquiv.symm_apply_eq, HomogeneousLocalization.Away.map_lof, map_smul]
  simp only [smul_eq_mul, awayBaseChange, AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe,
    AlgHom.toRingHom_toMonoidHom, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe,
    Algebra.algHom, LinearMap.coe_comp, AlgEquiv.symm_mk, GradedAlgebra.toTensor_toFun,
    AlgEquiv.coe_mk, Equiv.coe_fn_mk, Function.comp_apply, AlgHom.toLinearMap_apply, AlgHom.coe_mk,
    HomogeneousLocalization.algebraMap_apply, AlgEquiv.toLinearMap_apply]
  conv => enter [2,2,2,2]; exact HomogeneousLocalization.Away.val_lof _ _ _ _
  simp [HomogeneousLocalization.Away.lof, HomogeneousLocalization.lof,
    HomogeneousLocalization.Away.proj₀_mk, HomogeneousLocalization.Away.mk,
    ← tmul_eq_smul_one_tmul]

@[simp] lemma awayBaseChange_lof {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) {s : S} {n : ℕ} {a : 𝒜 (n • i)} :
    awayBaseChange 𝒜 S hf (.lof (fun n ↦ (𝒜 n).baseChange S)
      (Submodule.tmul_mem_baseChange_of_mem _ hf) n (Submodule.toBaseChange _ _ (s ⊗ₜ a))) =
    s ⊗ₜ .lof _ hf n a := by
  rw [← AlgEquiv.eq_symm_apply, awayBaseChange_symm_tmul,
    HomogeneousLocalization.Away.map_lof, tmul_eq_smul_one_tmul s, map_smul, map_smul]
  rfl

noncomputable def Proj.baseChangeIsoComponent {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) :
    Spec(HomogeneousLocalization.Away (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ[R] f)) ≅
    pullback (Spec.map (ofHom (algebraMap R S)))
      (Spec.map (ofHom (algebraMap R (HomogeneousLocalization.Away 𝒜 f)))) :=
  Scheme.Spec.mapIso (awayBaseChange 𝒜 S hf).toCommRingCatIso.op.symm ≪≫
  (pullbackSpecIso _ _ _).symm

@[reassoc (attr := simp)] lemma Proj.baseChangeIsoComponent_hom_comp_pullback_fst
    {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) :
    (Proj.baseChangeIsoComponent 𝒜 S hf).hom ≫ pullback.fst _ _ =
    Spec.map (ofHom (algebraMap S _)) := by
  simp only [HomogeneousLocalization.algebraMap_eq', ofHom_comp, baseChangeIsoComponent,
    Scheme.Spec_obj, AlgEquiv.toRingEquiv_eq_coe, Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.op_inv, RingEquiv.toCommRingCatIso_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, Category.assoc]
  conv => enter [1,2]; exact pullbackSpecIso_inv_fst ..
  simp only [← Spec.map_comp, ← ofHom_comp]
  congr 2; ext s
  simp [← AlgEquiv.symm_toRingEquiv, IsScalarTower.algebraMap_apply S (S ⊗[R] A) (Localization _),
    ← Localization.mk_one_eq_algebraMap, tmul_eq_smul_one_tmul s, ← Localization.smul_mk,
    ← Algebra.TensorProduct.one_def, Localization.mk_one]

@[reassoc (attr := simp)] lemma Proj.baseChangeIsoComponent_hom_comp_pullback_snd
    {i : ℕ} {f : A} (hf : f ∈ 𝒜 i) :
    (Proj.baseChangeIsoComponent 𝒜 S hf).hom ≫ pullback.snd _ _ =
    Spec.map (ofHom (HomogeneousLocalization.Away.map (GradedAlgebra.toTensor ..) rfl)) := by
  simp only [HomogeneousLocalization.algebraMap_eq', ofHom_comp, baseChangeIsoComponent,
    Scheme.Spec_obj, AlgEquiv.toRingEquiv_eq_coe, Functor.mapIso_symm, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Iso.op_inv, RingEquiv.toCommRingCatIso_inv, Scheme.Spec_map,
    Quiver.Hom.unop_op, Category.assoc, GradedAlgebra.toTensor_toFun]
  conv => enter [1,2]; exact pullbackSpecIso_inv_snd ..
  rw [← Spec.map_comp, ← ofHom_comp]
  congr 2; ext x
  simp [← AlgEquiv.symm_toRingEquiv]

@[reassoc] lemma Proj.map_toSpec {R R₁ R₂ A B : Type u}
    [CommRing R] [CommRing R₁] [CommRing R₂] [CommRing A] [CommRing B]
    [Algebra R R₁] [Algebra R R₂] [Algebra R A] [Algebra R B]
    [Algebra R₁ A] [IsScalarTower R R₁ A] [Algebra R₂ B] [IsScalarTower R R₂ B]
    (𝒜 : ℕ → Submodule R₁ A) [GradedAlgebra 𝒜]
    (ℬ : ℕ → Submodule R₂ B) [GradedAlgebra ℬ]
    (f : 𝒜 →ᵍᵃ ℬ) (hf) (hfr : ∀ r, f (algebraMap R A r) = algebraMap R B r) :
    Proj.map f hf ≫ Proj.toSpec 𝒜 ≫ Spec.map (ofHom (algebraMap R R₁)) =
    Proj.toSpec ℬ ≫ Spec.map (ofHom (algebraMap R R₂)) := by
  simp only [toSpec, Category.assoc, ← Spec.map_comp, ← ofHom_comp, map_comp_toSpecZero_assoc]
  congr 3; ext; simp [← IsScalarTower.algebraMap_apply, hfr]

@[reassoc (attr := simp)] lemma Proj.map_toTensor_toSpec :
    Proj.map _ (GradedAlgebra.toTensor_admissible 𝒜 S) ≫ Proj.toSpec 𝒜 =
    Proj.toSpec _ ≫ Spec.map (ofHom (algebraMap R S)) := by
  simpa using Proj.map_toSpec (R := R) _ _ _ (GradedAlgebra.toTensor_admissible 𝒜 S) fun r ↦ by
    simp [Algebra.TensorProduct.one_def, Algebra.algebraMap_eq_smul_one r, smul_tmul']

noncomputable def ofProjTensor :
    Proj (fun n ↦ (𝒜 n).baseChange S) ⟶
    pullback (Spec.map (ofHom (algebraMap R S))) (Proj.toSpec 𝒜) :=
  pullback.lift (Proj.toSpec _) (Proj.map _ <| GradedAlgebra.toTensor_admissible _ _) <| by simp

@[reassoc (attr := simp)] lemma Proj.awayι_comp_toSpec
    {i : ℕ} (hi : 0 < i) {s : A} (hs : s ∈ 𝒜 i) :
    Proj.awayι 𝒜 s hs hi ≫ Proj.toSpec 𝒜 = Spec.map (ofHom (algebraMap _ _)) := by
  simp [toSpec, awayι_toSpecZero_assoc]

/--
The following square commutes:
```
Proj(S ⊗[R] 𝒜) ---------⟶ Spec(S) ×[Spec(R)] Proj(𝒜)
    ^           ofProjTensor             ^
    |                                    |
    | awayι                              | 𝟙 × awayι
    |                                    |
    |           baseChangeIsoComponent   |
Spec((S⊗[R]A)[(1⊗s)⁻¹]) ⟶ Spec(S) ×[Spec(R)] Spec(A[s⁻¹])
```
-/
@[simp] lemma awayι_comp_ofProjTensor {i : ℕ} (hi : 0 < i) {s : A} (hs : s ∈ 𝒜 i) :
    Proj.awayι (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ s) (Submodule.tmul_mem_baseChange_of_mem _ hs)
      hi ≫ ofProjTensor 𝒜 S =
    (Proj.baseChangeIsoComponent 𝒜 S hs).hom ≫
      pullback.map _ _ _ _ (𝟙 _) (Proj.awayι _ s hs hi) (𝟙 _) (by simp) (by simp) :=
  pullback.hom_ext (by simp [- HomogeneousLocalization.algebraMap_eq', ofProjTensor]) <| by
  simpa [- HomogeneousLocalization.algebraMap_eq', ofProjTensor] using
    Proj.awayι_comp_map _ (GradedAlgebra.toTensor_admissible 𝒜 S) hi s hs

namespace Scheme

@[simp] lemma image_comp {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [IsOpenImmersion f] [IsOpenImmersion g] (U : X.Opens) :
    (f ≫ g) ''ᵁ U = g ''ᵁ f ''ᵁ U :=
  TopologicalSpace.Opens.ext <| Set.image_comp g.base f.base (U : Set X)

lemma image_id' {X : Scheme.{u}} {f : X ⟶ X} [IsOpenImmersion f] (hf : f = 𝟙 X) {U : X.Opens} :
    f ''ᵁ U = U := by
  subst hf; exact TopologicalSpace.Opens.ext <| Set.image_id _

@[simp] lemma image_inv {X Y : Scheme.{u}} {f : X ≅ Y} (V : Y.Opens) :
    f.inv ''ᵁ V = f.hom ⁻¹ᵁ V := by
  rw [← f.hom.preimage_image_eq (f.inv ''ᵁ V), ← image_comp, image_id' (by simp)]

@[simp] lemma image_inv' {X Y : Scheme.{u}} {f : X ⟶ Y} [IsIso f] (V : Y.Opens) :
    (inv f) ''ᵁ V = f ⁻¹ᵁ V :=
  image_inv (f := asIso f) V

@[simp] lemma image_preimage {X Y : Scheme.{u}} {f : X ⟶ Y} [IsIso f] {V : Y.Opens} :
    f ''ᵁ (f ⁻¹ᵁ V) = V :=
  TopologicalSpace.Opens.ext <| Set.image_preimage_eq _
    (ConcreteCategory.bijective_of_isIso f.base).surjective

lemma image_eq_iff_eq_preimage {X Y : Scheme.{u}} {f : X ⟶ Y} [IsIso f]
    {U : X.Opens} {V : Y.Opens} :
    f ''ᵁ U = V ↔ U = f ⁻¹ᵁ V :=
  ⟨(· ▸ by simp), (· ▸ by simp)⟩

end Scheme

/-- To check if `f : X ⟶ Y` is an isomorphism, one can supply an open cover of `X` and an open
cover of `Y` (indexed by the same set `S`), and then maps `f_i : U_i ⟶ V_i` for `i : S` that are
iso such that the squares commute. -/
theorem isIso_of_cover {X Y : Scheme.{v}} (f : X ⟶ Y)
    (U : X.OpenCover) (V : Y.OpenCover)
    {ι : Type*} (iU : ι → U.I₀) (hu : iU.Surjective) (iV : ι → V.I₀) (hv : iV.Surjective)
    (φ : ∀ i : ι, U.X (iU i) ⟶ V.X (iV i)) [∀ i, IsIso (φ i)]
    (hfφ : ∀ i : ι, U.f (iU i) ≫ f = φ i ≫ V.f (iV i))
    (preimage : ∀ i : ι, f ⁻¹ᵁ (V.f (iV i)).opensRange = (U.f (iU i)).opensRange) :
    IsIso f :=
  let U' : X.OpenCover :=
  { I₀ := ι
    X i := U.X (iU i)
    f i := U.f (iU i)
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ?_, inferInstance⟩
      obtain ⟨i, x, rfl⟩ := U.exists_eq x
      obtain ⟨i, rfl⟩ := hu i
      exact ⟨i, x, rfl⟩ }
  let V' : Y.OpenCover :=
  { I₀ := ι
    X i := V.X (iV i)
    f i := V.f (iV i)
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ?_, inferInstance⟩
      obtain ⟨i, x, rfl⟩ := V.exists_eq x
      obtain ⟨i, rfl⟩ := hv i
      exact ⟨i, x, rfl⟩ }
  let inv : Y ⟶ X := V'.glueMorphisms (fun i : ι ↦ inv (φ i) ≫ U'.f i) fun i₁ i₂ : ι ↦ by
    let p : pullback (V'.f i₁) (V'.f i₂) ⟶ pullback (U'.f i₁) (U'.f i₂) :=
      IsOpenImmersion.lift (pullback.fst _ _) (pullback.fst _ _ ≫ inv (φ i₁)) <| by
        rw [← Scheme.Hom.coe_opensRange, ← Scheme.Hom.coe_opensRange, SetLike.coe_subset_coe,
          IsOpenImmersion.opensRange_pullback_fst_of_right, Scheme.Hom.opensRange_comp,
          IsOpenImmersion.opensRange_pullback_fst_of_right, Scheme.image_inv',
          ← Scheme.preimage_comp, ← hfφ, Scheme.preimage_comp, preimage]
    have hp₁ : p ≫ pullback.fst _ _ = pullback.fst _ _ ≫ inv (φ i₁) :=
      IsOpenImmersion.lift_fac _ _ _
    have hp₂ : p ≫ pullback.snd _ _ = pullback.snd _ _ ≫ inv (φ i₂) := by
      rw [IsIso.eq_comp_inv]
      refine (cancel_mono (V'.f i₂)).mp ?_
      simp_rw [Category.assoc]
      rw [← hfφ, ← pullback.condition_assoc, reassoc_of% hp₁, hfφ, IsIso.inv_hom_id_assoc,
        pullback.condition]
    dsimp only
    rw [← reassoc_of% hp₁, pullback.condition, reassoc_of% hp₂]
  have comp_inv : f ≫ inv = 𝟙 X := U'.hom_ext _ _ fun i ↦ by
    unfold inv
    rw [reassoc_of% hfφ, V'.ι_glueMorphisms, IsIso.hom_inv_id_assoc, Category.comp_id]
  have inv_comp : inv ≫ f = 𝟙 Y := V'.hom_ext _ _ fun i ↦ by
    unfold inv
    rw [V'.ι_glueMorphisms_assoc, Category.assoc, hfφ, IsIso.inv_hom_id_assoc, Category.comp_id]
  ⟨inv, comp_inv, inv_comp⟩

noncomputable def Proj.openCoverBaseChange :
    (Proj fun n ↦ (𝒜 n).baseChange S).AffineOpenCover :=
  Proj.mapAffineOpenCover _ <| GradedAlgebra.toTensor_admissible 𝒜 S

noncomputable def Proj.openCoverPullback :
    (pullback (Spec.map (ofHom (algebraMap R S))) (Proj.toSpec 𝒜)).OpenCover :=
  (Scheme.Pullback.openCoverOfRight (Proj.affineOpenCover 𝒜).openCover
      (Spec.map <| ofHom <| algebraMap R S) (Proj.toSpec 𝒜)).copy
    (Proj.affineOpenCover 𝒜).I₀
    (fun f ↦ pullback (Spec.map (ofHom (algebraMap R S)))
      (Spec.map (ofHom (algebraMap R (HomogeneousLocalization.Away 𝒜 f.2)))))
    (fun f ↦ pullback.map _ _ _ _ (𝟙 _) (Proj.awayι 𝒜 f.2 f.2.2 f.1.2) (𝟙 _) (by simp) (by simp))
    (Equiv.refl _) (fun _ ↦ pullback.congrHom rfl
      (by simp [affineOpenCover, affineOpenCoverOfIrrelevantLESpan]))
    fun f ↦ pullback.hom_ext (by simp)
      (by simp [Proj.affineOpenCover, Proj.affineOpenCoverOfIrrelevantLESpan])

@[simp] lemma Proj.opensRange_openCoverPullback {f} :
    ((Proj.openCoverPullback 𝒜 S).f f).opensRange =
    pullback.snd (Spec.map (ofHom (algebraMap R S))) (toSpec 𝒜) ⁻¹ᵁ basicOpen _ f.2 :=
  TopologicalSpace.Opens.ext <| by
    simp [openCoverPullback, Scheme.Pullback.range_map, ← Proj.opensRange_awayι _ _ f.2.2]

instance : IsIso (ofProjTensor 𝒜 S) :=
  isIso_of_cover _ (Proj.openCoverBaseChange 𝒜 S).openCover
    (Proj.openCoverPullback 𝒜 S)
    id Function.surjective_id id Function.surjective_id
    (fun f ↦ (Proj.baseChangeIsoComponent 𝒜 S f.2.2).hom)
    (fun f ↦ by simp [Proj.openCoverBaseChange, Proj.openCoverPullback])
    fun f ↦ by simp [← Scheme.preimage_comp, - TopologicalSpace.Opens.map_comp_obj, ofProjTensor,
      Proj.openCoverBaseChange, Proj.opensRange_awayι]

-- https://math.arizona.edu/~cais/CourseNotes/AlgGeom04/notes216.pdf
noncomputable def projTensorProduct : Proj (fun n ↦ (𝒜 n).baseChange S) ≅
    pullback (Spec.map (ofHom (algebraMap R S))) (Proj.toSpec 𝒜) :=
  asIso <| ofProjTensor 𝒜 S

@[simp] lemma projTensorProduct_hom_comp_pullback_fst :
    (projTensorProduct 𝒜 S).hom ≫ pullback.fst _ _ = Proj.toSpec _ := by
  simp [projTensorProduct, ofProjTensor]

@[simp] lemma projTensorProduct_hom_comp_pullback_snd :
    (projTensorProduct 𝒜 S).hom ≫ pullback.snd _ _ =
    Proj.map _ (GradedAlgebra.toTensor_admissible 𝒜 S) := by
  simp [projTensorProduct, ofProjTensor]

@[simp] lemma awayι_comp_projTensorProduct {i : ℕ} (hi : 0 < i) {s : A} (hs : s ∈ 𝒜 i) :
    Proj.awayι (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ s) (Submodule.tmul_mem_baseChange_of_mem _ hs)
      hi ≫ (projTensorProduct 𝒜 S).hom =
    (Proj.baseChangeIsoComponent 𝒜 S hs).hom ≫
      pullback.map _ _ _ _ (𝟙 _) (Proj.awayι _ s hs hi) (𝟙 _) (by simp) (by simp) :=
  awayι_comp_ofProjTensor _ _ _ _

@[simp] lemma projTensorProduct_image_basicOpen {s : A} :
    (projTensorProduct 𝒜 S).hom ''ᵁ (Proj.basicOpen (fun n ↦ (𝒜 n).baseChange S) (1 ⊗ₜ s)) =
    pullback.snd (Spec.map (ofHom (algebraMap R S))) (Proj.toSpec 𝒜) ⁻¹ᵁ Proj.basicOpen 𝒜 s := by
  rw [Scheme.image_eq_iff_eq_preimage, ← Scheme.preimage_comp,
    projTensorProduct_hom_comp_pullback_snd, Proj.map_preimage_basicOpen,
    GradedAlgebra.toTensor_toFun]

end AlgebraicGeometry

/-!
# Projective Space as Scheme

## Main definitions

- `AlgebraicGeometry.ProjectiveSpace`: `ℙ(n; S)` is the projective `n`-space over a scheme `S`.

## TODO

- `AlgebraicGeometry.ProjectiveSpace.SpecIso`: `ℙ(n; Spec R) ≅ Proj R[n]`.
- `AlgebraicGeometry.ProjectiveSpace.openCover`: the canonical cover of `ℙ(n; S)` by `n` affine
  charts. The `i`ᵗʰ chart is `𝔸({k // k ≠ i}; S) ⟶ ℙ(n; S)`, and represents the open set where
  the function `Xᵢ` does not vanish.
- Functoriality of `ProjectiveSpace` on the `S` component.
- Show that a map `Spec A ⟶ ℙ(n; S)` corresponds to a map `p : Spec A ⟶ S` and a unique
  `A`-submodule `N` of `n →₀ A` such that `(n →₀ A) ⧸ N` is locally free of rank 1.
-/

-- Also see https://github.com/leanprover-community/mathlib4/pull/26061

open CategoryTheory Limits MvPolynomial HomogeneousLocalization

noncomputable section

namespace AlgebraicGeometry

variable (n : Type u) (S : Scheme.{u})

attribute [local instance] gradedAlgebra

/-- The structure of a graded algebra on `ℤ[n]`, i.e. on `MvPolynomial n (ULift.{u} ℤ)`. -/
local notation3 "ℤ[" n "].{" u "}" => homogeneousSubmodule n (ULift.{u} ℤ)

/-- `ℙ(n; S)` is the projective `n`-space over `S`.
Note that `n` is an arbitrary index type (e.g. `ULift (Fin m)`). -/
def ProjectiveSpace (n : Type u) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (Proj ℤ[n].{u}))

@[inherit_doc] scoped notation "ℙ("n"; "S")" => ProjectiveSpace n S

namespace Proj

-- /-- The canonical affine open cover of `Proj (MvPolynomial σ R)`. The cover is indexed by `σ`,
-- and each `i : σ` corresponds to `Spec (MvPolynomial {k // k ≠ i} R)`. -/
-- @[simps!] def openCoverMvPolynomial (σ : Type*) (R : Type*) [CommRing R] :
--     (Proj (homogeneousSubmodule σ R)).AffineOpenCover :=
--   (openCoverOfISupEqTop
--       (homogeneousSubmodule σ R) .X (fun _ ↦ isHomogeneous_X _ _) (fun _ ↦ zero_lt_one)
--       (by rw [homogeneous_eq_span, Ideal.span_le, Set.range_subset_iff]; exact
--         fun i ↦ Ideal.subset_span <| Set.mem_range_self _)).copy
--     _ _ _
    -- (Equiv.refl σ) (.of <| MvPolynomial {k // k ≠ ·} R) (algEquivAway R · |>.toCommRingCatIso)

end Proj

instance _root_.ULift.algebraLeft {R A : Type*} [CommSemiring R] [Semiring A] [Algebra R A] :
    Algebra (ULift R) A where
  algebraMap := (algebraMap R A).comp (ULift.ringEquiv (R := R))
  commutes' _ := Algebra.commutes _
  smul_def' _ := Algebra.smul_def _

@[simps] def _root_.CategoryTheory.Limits.pullback.mapIso {C : Type*} [Category C]
    {X₁ X₂ Y₁ Y₂ W₁ W₂ : C} {f₁ : X₁ ⟶ W₁} {g₁ : Y₁ ⟶ W₁} {f₂ : X₂ ⟶ W₂} {g₂ : Y₂ ⟶ W₂}
    [HasPullback f₁ g₁] [HasPullback f₂ g₂] (eX : X₁ ≅ X₂) (eY : Y₁ ≅ Y₂) (eW : W₁ ≅ W₂)
    (comm₁ : f₁ ≫ eW.hom = eX.hom ≫ f₂) (comm₂ : g₁ ≫ eW.hom = eY.hom ≫ g₂) :
    pullback f₁ g₁ ≅ pullback f₂ g₂ where
  hom := pullback.map _ _ _ _ eX.hom eY.hom eW.hom comm₁ comm₂
  inv := pullback.map _ _ _ _ eX.inv eY.inv eW.inv
    (by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, comm₁])
    (by rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp, comm₂])
  hom_inv_id := pullback.hom_ext (by simp) (by simp)
  inv_hom_id := pullback.hom_ext (by simp) (by simp)

def _root_.MvPolynomial.algebraTensorGAlgEquiv (R : Type*) [CommRing R] {σ : Type*}
    (A : Type*) [CommRing A] [Algebra R A] :
    (fun n ↦ (homogeneousSubmodule σ R n).baseChange A) ≃ᵍᵃ homogeneousSubmodule σ A where
  __ := MvPolynomial.algebraTensorAlgEquiv R A
  map_one' := by simp
  map_zero' := by simp
  map_mem' n x hx := by
    obtain ⟨x, hx⟩ := Submodule.toBaseChange_surjective _ _ ⟨x, hx⟩
    replace hx := congr(($hx).val); subst hx
    simp only [AlgEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, RingHom.coe_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, mem_homogeneousSubmodule]
    induction x with
    | zero => simp [isHomogeneous_zero]
    | add => simp [IsHomogeneous.add, *]
    | tmul a x => simpa [smul_eq_C_mul] using (x.2.map _).C_mul _

/-- `ℙ(n; Spec(R))` is isomorphic to `Proj R[n]`. -/
def SpecIso (R : Type u) [CommRing R] : ℙ(n; Spec(R)) ≅ Proj (homogeneousSubmodule n R) :=
  pullback.mapIso (Iso.refl _) (Iso.refl _) (terminalIsoIsTerminal specULiftZIsTerminal)
    (specULiftZIsTerminal.hom_ext ..) (specULiftZIsTerminal.hom_ext ..) ≪≫
  (projTensorProduct ℤ[n].{u} R).symm ≪≫
  Proj.congr (MvPolynomial.algebraTensorGAlgEquiv _ _)

end AlgebraicGeometry
