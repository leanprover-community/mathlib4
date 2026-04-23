/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.Algebra.Category.LocAlgCat.Defs
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.Length

import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Basic Constructions and Lemmas in `LocAlgCat`

## Main Results

* `LocAlgCat.ofQuot` : The object in `LocAlgCat` obtained from the quotient by a proper ideal.

* `LocAlgCat.toOfQuot` : Upgrades the canonical quotient map from `A → A ⧸ I` to a morphism
  `A ⟶ A.ofQuot I`.

* `LocAlgCat.mapOfQuot` : The canonical morphism `A.ofQuot I ⟶ B.ofQuot J` induced
  by a morphism `f : A ⟶ B`. This is the categorical counterpart to `Ideal.quotientMapₐ`.

* `LocAlgCat.infinitesimalNeighborhood` : The object in `LocAlgCat` obtained from the quotient by
  the `n`-th power of the maximal ideal.

* `LocAlgCat.specialFiber` : The special fiber of an object over a local base ring, defined as
  the object in `LocAlgCat` obtained from quotient by the extended maximal ideal of the base ring.

-/

@[expose] public section

universe w v u

namespace LocAlgCat

open IsLocalRing CategoryTheory Function

variable {Λ : Type u} [CommRing Λ] {k : Type v} [Field k] [Algebra Λ k] {A B C : LocAlgCat.{w} Λ k}

variable (A) in
lemma isLocalHom_algebraMap [IsLocalRing Λ] [Algebra.IsIntegral Λ k] :
    IsLocalHom (algebraMap Λ A) := by
  have : IsLocalHom (algebraMap Λ k) := isLocalHom_of_isIntegral Λ k
  rw [IsScalarTower.algebraMap_eq Λ A] at this
  exact isLocalHom_of_comp (algebraMap Λ A) (algebraMap A k)

variable (A) in
lemma comap_algebraMap_maximalIdeal [IsLocalRing Λ] [Algebra.IsIntegral Λ k] :
    (maximalIdeal A).comap (algebraMap Λ A) = maximalIdeal Λ := by
  have : IsLocalHom (algebraMap Λ k) := isLocalHom_of_isIntegral Λ k
  have := ((local_hom_TFAE (algebraMap Λ k)).out 0 4).mp ‹_›
  rw [eq_comm, ← this, IsScalarTower.algebraMap_eq Λ A, ← Ideal.comap_comap,
    eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ A.surj)]

instance [IsLocalRing Λ] [Algebra.IsIntegral Λ k] :
    Nontrivial (A ⧸ ((maximalIdeal Λ).map (algebraMap Λ A))) :=
  Ideal.Quotient.nontrivial_iff.mpr <| ne_top_of_le_ne_top (maximalIdeal.isMaximal A).ne_top <|
    ((local_hom_TFAE (algebraMap Λ A)).out 4 2).mp (comap_algebraMap_maximalIdeal A)

instance (f : A ⟶ B) : Nontrivial (A ⧸ RingHom.ker (f.toAlgHom)) :=
  Ideal.Quotient.nontrivial_iff.mpr <| RingHom.ker_ne_top f.toAlgHom

instance (n : ℕ) [NeZero n] : Nontrivial (A ⧸ maximalIdeal A ^ n) := by
  rw [Ideal.Quotient.nontrivial_iff, Ideal.ne_top_iff_exists_maximal]
  exact ⟨maximalIdeal A, maximalIdeal.isMaximal A, Ideal.pow_le_self (NeZero.ne n)⟩

section ofQuot

variable {I : Ideal A}

/-- The residue algebra structure on `ofQuot`. -/
instance ofQuotResidueAlgebra [Nontrivial (A ⧸ I)] : Algebra (A ⧸ I) k :=
  fast_instance% (Ideal.Quotient.lift I (algebraMap A k) fun a a_in ↦ by
    rw [← residue_apply, residue_eq_zero_iff]
    exact le_maximalIdeal (by rwa [← Ideal.Quotient.nontrivial_iff]) a_in).toAlgebra

instance isScalarTower_ofQuotResidueAlgebra [Nontrivial (A ⧸ I)] : IsScalarTower Λ (A ⧸ I) k :=
  .of_algebraMap_eq fun r ↦ by rw [IsScalarTower.algebraMap_apply Λ A (A ⧸ I),
    Ideal.Quotient.algebraMap_eq, RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_mk,
    IsScalarTower.algebraMap_apply Λ A]

instance isScalarTower_ofQuotResidueAlgebra' [Nontrivial (A ⧸ I)] : IsScalarTower A (A ⧸ I) k :=
  .of_algebraMap_eq fun _ ↦ by rw [RingHom.algebraMap_toAlgebra, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.lift_mk]

/-- The quotient of an object `A` in `LocAlgCat` by a proper ideal `I`. -/
def ofQuot (A : LocAlgCat.{w} Λ k) (I : Ideal A) [Nontrivial (A ⧸ I)] : LocAlgCat.{w} Λ k :=
  letI : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  of Λ k (A ⧸ I) (Surjective.of_comp (g := Ideal.Quotient.mk _) (by
    rw [← RingHom.coe_comp, RingHom.algebraMap_toAlgebra, Ideal.Quotient.lift_comp_mk]
    exact A.surj))

@[simp]
lemma residue_ofQuot_mk_apply [Nontrivial (A ⧸ I)] (a : A) :
    (A.ofQuot I).residue (Ideal.Quotient.mk I a) = A.residue a := rfl

instance algebraOfQuot (A : LocAlgCat.{w} Λ k) {I : Ideal A} [Nontrivial (A ⧸ I)] :
    Algebra A (A.ofQuot I) := fast_instance% Ideal.Quotient.algebra _

instance isScalarTower_algebraOfQuot (A : LocAlgCat.{w} Λ k) {I : Ideal A} [Nontrivial (A ⧸ I)] :
    IsScalarTower Λ A (A.ofQuot I) := .of_algebraMap_eq fun _ ↦ rfl

/-- Upgrades the canonical quotient map from `A` to `A ⧸ I` to a morphism in `LocAlgCat`. -/
def toOfQuot (A : LocAlgCat.{w} Λ k) (I : Ideal A) [Nontrivial (A ⧸ I)] : A ⟶ A.ofQuot I :=
  letI : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  ofHom (IsScalarTower.toAlgHom Λ A (A ⧸ I)) (eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective
    _ Ideal.Quotient.mk_surjective)) (by ext; simpa [residue] using residue_ofQuot_mk_apply ..)

@[simp]
lemma toAlgHom_toOfQuot_apply [Nontrivial (A ⧸ I)] (a : A) :
    (A.toOfQuot I).toAlgHom a = Ideal.Quotient.mk I a := rfl

@[simp]
lemma ker_toAlgHom_toOfQuot [Nontrivial (A ⧸ I)] : RingHom.ker (A.toOfQuot I).toAlgHom = I :=
  Ideal.mk_ker

lemma surjective_toAlgHom_toOfQuot [Nontrivial (A ⧸ I)] : Surjective (A.toOfQuot I).toAlgHom :=
  Ideal.Quotient.mk_surjective

theorem map_toAlgHom_toOfQuot_maximalIdeal_eq [Nontrivial (A ⧸ I)] :
    (maximalIdeal A).map (A.toOfQuot I).toAlgHom = maximalIdeal (A.ofQuot I) :=
  map_maximalIdeal_of_surjective _ surjective_toAlgHom_toOfQuot

/-- The morphism between quotient objects in `LocAlgCat` induced by a morphism `f : A ⟶ B`.
This is the categorical counterpart to `Ideal.quotientMapₐ`. -/
def mapOfQuot (f : A ⟶ B) {J : Ideal B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)]
    (hf : I ≤ J.comap f.toAlgHom) : A.ofQuot I ⟶ B.ofQuot J :=
  haveI : IsLocalRing (A ⧸ I) := .of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : IsLocalRing (B ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
  ofHom (Ideal.quotientMapₐ J f.toAlgHom hf) (by
    rw [← (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective).eq_iff,
      ← Ideal.comap_coe (Ideal.quotientMapₐ J f.toAlgHom hf), Ideal.comap_comap]
    change Ideal.comap (((Ideal.quotientMap J f.toAlgHom hf)).comp (Ideal.Quotient.mk I))
      (maximalIdeal (B ⧸ J)) = _
    rw [Ideal.quotientMap_comp_mk, ← Ideal.comap_comap, Ideal.comap_coe, eq_maximalIdeal
      (Ideal.comap_isMaximal_of_surjective ((Ideal.Quotient.mk J)) Ideal.Quotient.mk_surjective),
        f.comap_maximalIdeal_eq, eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective
          (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective)] ) (AlgHom.ext fun x ↦ by
    rcases Ideal.Quotient.mk_surjective x with ⟨x, rfl⟩
    exact DFunLike.congr_fun f.residue_comp x )

@[simp]
theorem toOfQuot_comp_mapOfQuot (f : A ⟶ B) {J : Ideal B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)]
    (hf : I ≤ J.comap f.toAlgHom) : A.toOfQuot I ≫ mapOfQuot f hf = f ≫ B.toOfQuot J := rfl

@[simp]
lemma toAlgHom_mapOfQuot_apply (f : A ⟶ B) {J : Ideal B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)]
    (hf : I ≤ J.comap f.toAlgHom) (a : A) : (mapOfQuot f hf).toAlgHom (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J (f.toAlgHom a) := rfl

/-- The isomorphism between `A.ofQuot (RingHom.ker f.toAlgHom)` and the codomain `B`
when the underlying `AlgHom` of a morphism `f : A ⟶ B` is surjective.
This is the categorical counterpart to `Ideal.quotientKerAlgEquivOfSurjective`. -/
noncomputable def ofQuotKerIsoOfSurjective (f : A ⟶ B) (h : Surjective f.toAlgHom) :
    A.ofQuot (RingHom.ker f.toAlgHom) ≅ B := isoMk (Ideal.quotientKerAlgEquivOfSurjective h) (by
  ext x
  rcases Ideal.Quotient.mk_surjective x with ⟨x, rfl⟩
  change _ = (A.ofQuot (RingHom.ker f.toAlgHom)).residue _
  simp [← AlgHom.comp_apply, f.residue_comp])

@[simp]
lemma toAlgHom_ofQuotKerIsoOfSurjective_hom_apply {f : A ⟶ B} (h : Surjective f.toAlgHom) (a : A) :
    (ofQuotKerIsoOfSurjective f h).hom.toAlgHom (Ideal.Quotient.mk (RingHom.ker f.toAlgHom) a) =
      f.toAlgHom a := rfl

@[simp]
lemma toAlgHom_ofQuotKerIsoOfSurjective_inv_apply {f : A ⟶ B} (h : Surjective f.toAlgHom) (a : A) :
    (ofQuotKerIsoOfSurjective f h).inv.toAlgHom (f.toAlgHom a) =
      Ideal.Quotient.mk (RingHom.ker f.toAlgHom) a :=
  (Ideal.quotientKerAlgEquivOfSurjective h).symm_apply_apply a

@[simp]
lemma toOfQuot_comp_ofQuotKerIsoOfSurjective_hom {f : A ⟶ B} (h : Surjective f.toAlgHom) :
    A.toOfQuot (RingHom.ker f.toAlgHom) ≫ (ofQuotKerIsoOfSurjective f h).hom = f := Hom.ext rfl

/-- The quotient of a local algebra by the `n`-th power of its maximal ideal.
Geometrically, this represents an infinitesimal neighborhood of the closed point. -/
abbrev infinitesimalNeighborhood (n : ℕ) [NeZero n] (A : LocAlgCat.{w} Λ k) : LocAlgCat Λ k :=
  A.ofQuot (maximalIdeal A ^ n)

/-- The canonical quotient morphism from `A` to its infinitesimal neighborhood. -/
abbrev toInfinitesimalNeighborhood (n : ℕ) [NeZero n] (A : LocAlgCat.{w} Λ k) :
    A ⟶ A.infinitesimalNeighborhood n :=
  toOfQuot ..

/-- The morphism between infinitesimal neighborhoods induced by a morphism in `LocAlgCat`. -/
abbrev mapInfinitesimalNeighborhood (m n : ℕ) [NeZero m] [NeZero n] (hmn : n ≤ m) (f : A ⟶ B) :
    A.infinitesimalNeighborhood m ⟶ B.infinitesimalNeighborhood n :=
  mapOfQuot f (le_trans (Ideal.pow_le_pow_right hmn) (f.comap_maximalIdeal_eq ▸
      Ideal.le_comap_pow f.toAlgHom n))

lemma toInfinitesimalNeighborhood_comp_map (m n : ℕ) [NeZero m] [NeZero n] (hmn : n ≤ m)
    (f : A ⟶ B) : A.toInfinitesimalNeighborhood m ≫ mapInfinitesimalNeighborhood m n hmn f =
      f ≫ B.toInfinitesimalNeighborhood n := by simp

/-- The special fiber of `A` over `Λ` when `Λ` is a local ring, defined as the quotient by
the extended maximal ideal of `Λ`, viewed as an object in `LocAlgCat`. -/
abbrev specialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (A : LocAlgCat.{w} Λ k) :
    LocAlgCat.{w} Λ k := A.ofQuot ((maximalIdeal Λ).map (algebraMap Λ A))

/-- The canonical morphism from `A` to its special fiber. -/
abbrev toSpecialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (A : LocAlgCat.{w} Λ k) :
    A ⟶ A.specialFiber := toOfQuot ..

/-- The morphism between special fibers induced by a morphism between two objects. -/
abbrev mapSpecialFiber [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (f : A ⟶ B) :
    A.specialFiber ⟶ B.specialFiber :=
  mapOfQuot f (by rw [Ideal.map_le_iff_le_comap, ← Ideal.comap_coe f.toAlgHom,
    Ideal.comap_comap, AlgHom.comp_algebraMap, ← Ideal.map_le_iff_le_comap])

lemma toInfinitesimalNeighborhood_comp_mapInfinitesimalNeighborhood_toSpecialFiber [IsLocalRing Λ]
    [Algebra.IsIntegral Λ k] (n : ℕ) [NeZero n] (A : LocAlgCat.{w} Λ k) :
    A.toInfinitesimalNeighborhood n ≫ mapInfinitesimalNeighborhood n n le_rfl A.toSpecialFiber =
      A.toSpecialFiber ≫ (A.specialFiber).toInfinitesimalNeighborhood n := by simp

@[simp]
lemma algebraMap_specialFiber_apply_eq_zero [IsLocalRing Λ] [Algebra.IsIntegral Λ k]
    (A : LocAlgCat.{w} Λ k) {y : Λ} (y_in : y ∈ maximalIdeal Λ) :
    algebraMap Λ A.specialFiber y = 0 := by
  rw [IsScalarTower.algebraMap_apply Λ A A.specialFiber]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ y_in)

end ofQuot

section ofPullback

variable {f : A ⟶ C} {g : B ⟶ C}

instance ofPullbackResidueAlgebra : Algebra (f.toAlgHom.pullback g.toAlgHom) k :=
  fast_instance% (A.residue.comp (f.toAlgHom.pullbackFst g.toAlgHom)).toAlgebra

instance isScalarTower_ofPullbackResidueAlgebra :
    IsScalarTower Λ (f.toAlgHom.pullback g.toAlgHom) k := .of_algebraMap_eq (by
  simp [RingHom.algebraMap_toAlgebra])

/-- Given morphisms `f : A ⟶ C` and `g : B ⟶ C` in `LocAlgCat` where `g.toAlgHom` is surjective,
`ofPullback` is the object in `LocAlgCat` obtained from the pullback of the underlying
algebra homomorphisms`. -/
def ofPullback (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) : LocAlgCat.{w} Λ k :=
  letI : IsLocalRing ↥(f.toAlgHom.pullback g.toAlgHom) :=
    AlgHom.isLocalRing_pullback f.toAlgHom g.toAlgHom ⟨hg.isLocalHom.map_nonunit⟩
  of Λ k (f.toAlgHom.pullback g.toAlgHom) (by
    simpa [RingHom.algebraMap_toAlgebra] using Surjective.comp A.surj
      (AlgHom.surjective_pullbackFst_of_surjective _ _ hg))

/-- Upgrades the first projection map from the pullback algebra to a morphism in `LocAlgCat`. -/
abbrev pullbackFst (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) :
    ofPullback f g hg ⟶ A :=
  letI : IsLocalRing ↥(f.toAlgHom.pullback g.toAlgHom) :=
    AlgHom.isLocalRing_pullback f.toAlgHom g.toAlgHom ⟨hg.isLocalHom.map_nonunit⟩
  ⟨f.toAlgHom.pullbackFst g.toAlgHom, eq_maximalIdeal <| Ideal.comap_isMaximal_of_surjective _
    (AlgHom.surjective_pullbackFst_of_surjective f.toAlgHom g.toAlgHom hg), rfl⟩

lemma residue_comp_pullbackFst (f : A ⟶ C) (g : B ⟶ C) :
    A.residue.comp (f.toAlgHom.pullbackFst g.toAlgHom) =
      B.residue.comp (f.toAlgHom.pullbackSnd g.toAlgHom) := by
  ext ⟨_, h⟩
  simp only [AlgHom.mem_equalizer, AlgHom.coe_comp, Function.comp_apply, AlgHom.fst_apply,
    AlgHom.snd_apply, Subalgebra.coe_val] at h ⊢
  rw [← DFunLike.congr_fun f.residue_comp, ← DFunLike.congr_fun g.residue_comp,
    AlgHom.comp_apply, AlgHom.comp_apply, h]

/-- Upgrades the second projection map from the pullback algebra to a morphism in `LocAlgCat`. -/
abbrev pullbackSnd (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) :
    ofPullback f g hg ⟶ B :=
  letI : IsLocalRing ↥(f.toAlgHom.pullback g.toAlgHom) :=
    AlgHom.isLocalRing_pullback f.toAlgHom g.toAlgHom ⟨hg.isLocalHom.map_nonunit⟩
  haveI : IsLocalHom f.toAlgHom.toRingHom := ⟨f.isLocalHom_toAlgHom.map_nonunit⟩
  haveI : IsLocalHom (f.toAlgHom.pullbackSnd g.toAlgHom).toRingHom :=
    ⟨(RingHom.isLocalHom_pullbackSnd f.toAlgHom.toRingHom g.toAlgHom.toRingHom).map_nonunit⟩
  ⟨f.toAlgHom.pullbackSnd g.toAlgHom, IsLocalRing.maximalIdeal_comap
    (f.toAlgHom.pullbackSnd g.toAlgHom).toRingHom, (residue_comp_pullbackFst f g).symm⟩

lemma pullback_comm_sq (f : A ⟶ C) (g : B ⟶ C) (hg : Surjective g.toAlgHom) :
    pullbackFst f g hg ≫ f = pullbackSnd f g hg ≫ g :=
  Hom.ext <| AlgHom.pullback_comm_sq f.toAlgHom g.toAlgHom

open Polynomial in
private lemma not_isUnit_aeval_of_aeval_eq_zero [IsLocalRing Λ] [Algebra.IsIntegral Λ k] (x : k)
    {a : A} {p : (ResidueField Λ)[X]} {q : Λ[X]} (hp : aeval x p = 0)
    (hq : q.map (IsLocalRing.residue Λ) = p) (ha : algebraMap A k a = x) :
    ¬ IsUnit (aeval a q) := fun h ↦ by
  replace h := IsUnit.map (algebraMap A k) h
  have : algebraMap A k (aeval a q) = 0 := by
    rw [← aeval_algebraMap_apply, ha, ← Polynomial.aeval_map_algebraMap (ResidueField Λ),
    ResidueField.algebraMap_eq, hq, hp]
  simp [this] at h

open Polynomial in
private lemma isUnit_aeval_derivative_of_isSeparable [IsLocalRing Λ] [Algebra.IsIntegral Λ k]
    {x : k} {a : A} {q : Λ[X]} (hx : IsSeparable (ResidueField Λ) x)
    (hq : q.map (IsLocalRing.residue Λ) = minpoly (ResidueField Λ) x) (ha : residue A a = x) :
    IsUnit (aeval a (derivative q)) := by
  rw [← notMem_maximalIdeal, ← ker_residue, RingHom.mem_ker, ← RingHom.coe_coe, aeval_def,
    hom_eval₂, AlgHom.comp_algebraMap_of_tower, RingHom.coe_coe, ← Polynomial.eval_map,
    IsScalarTower.algebraMap_eq Λ (ResidueField Λ) k, ← map_map, ResidueField.algebraMap_eq,
    ← derivative_map, hq, Polynomial.eval_map, ← aeval_def, ha]
  exact hx.aeval_derivative_ne_zero (minpoly.aeval (ResidueField Λ) x)

open Polynomial in
@[stacks 06GH "(3)"]
theorem surjective_residue_comp_pullbackFst_of_isSeparable [IsLocalRing Λ] [Module.Finite Λ k]
    [HenselianRing A (maximalIdeal A)] [HenselianRing B (maximalIdeal B)]
    [Algebra.IsSeparable (ResidueField Λ) k] (f : A ⟶ C) (g : B ⟶ C) :
    Surjective (A.residue.comp (f.toAlgHom.pullbackFst g.toAlgHom)) := by
  obtain ⟨x, hx⟩ := Field.exists_primitive_element (ResidueField Λ) k
  let p := minpoly (ResidueField Λ) x
  obtain ⟨q, map_q, deg_q, monic_q⟩ := lifts_and_natDegree_eq_and_monic
    (show p ∈ lifts (IsLocalRing.residue Λ) by
      rw [lifts_iff_coeff_lifts]; intro; exact IsLocalRing.residue_surjective _)
    (minpoly.monic (Algebra.IsIntegral.isIntegral x))
  obtain ⟨a', ha⟩ := A.residue_surjective x
  obtain ⟨a, a_rt, a_sub⟩ := HenselianRing.is_henselian (R := A) (I := maximalIdeal A)
    (q.map (algebraMap Λ A)) (Monic.map _ monic_q) a' (by
      simpa using LocAlgCat.not_isUnit_aeval_of_aeval_eq_zero x (minpoly.aeval (ResidueField Λ) x)
        map_q ha)
    (by change IsUnit ((IsLocalRing.residue A) _); simpa using
        LocAlgCat.isUnit_aeval_derivative_of_isSeparable (Algebra.IsSeparable.isSeparable
          (ResidueField Λ) x) map_q ha)
  replace ha : A.residue a = x := by
    rw [← sub_add_cancel a a', map_add, ha, LocAlgCat.residue_eq_zero_iff.mpr a_sub, zero_add]
  obtain ⟨b', hb⟩ := B.residue_surjective x
  obtain ⟨b, b_rt, b_sub⟩ := HenselianRing.is_henselian (R := B) (I := maximalIdeal B)
    (q.map (algebraMap Λ B)) (Monic.map _ monic_q) b' (by
      simpa using LocAlgCat.not_isUnit_aeval_of_aeval_eq_zero x (minpoly.aeval (ResidueField Λ) x)
        map_q hb)
    (by change IsUnit ((IsLocalRing.residue B) _); simpa using
        LocAlgCat.isUnit_aeval_derivative_of_isSeparable
          (Algebra.IsSeparable.isSeparable (ResidueField Λ) x) map_q hb)
  replace hb : B.residue b = x := by
    rw [← sub_add_cancel b b', map_add, hb, LocAlgCat.residue_eq_zero_iff.mpr b_sub, zero_add]
  clear a' a_sub b' b_sub
  have hab : f.toAlgHom a = g.toAlgHom b := by
    simp only [IsRoot.def, eval_map_algebraMap, aeval_def] at a_rt b_rt
    apply DFunLike.congr_arg f.toAlgHom at a_rt
    apply DFunLike.congr_arg g.toAlgHom at b_rt
    rw [algHom_eval₂_algebraMap, map_zero, eval₂_eq_eval_map] at a_rt b_rt
    refine eq_of_eval_eq_zero_of_not_isUnit_sub a_rt b_rt ?_ ?_
    · rw [← notMem_maximalIdeal, not_not, ← LocAlgCat.residue_eq_zero_iff, map_sub, sub_eq_zero,
        ← AlgHom.comp_apply, ← AlgHom.comp_apply, f.residue_comp, g.residue_comp, ha, hb]
    · rw [derivative_map, eval_map_algebraMap]
      exact LocAlgCat.isUnit_aeval_derivative_of_isSeparable
        (Algebra.IsSeparable.isSeparable (ResidueField Λ) x) map_q (by
          rwa [← AlgHom.comp_apply, f.residue_comp])
  apply Algebra.adjoin_eq_top_of_primitive_element (Algebra.IsAlgebraic.isAlgebraic x) at hx
  simp only [SetLike.ext_iff, Algebra.mem_top, iff_true] at hx
  intro y
  simp only [AlgHom.coe_comp, Subalgebra.coe_val, Function.comp_apply, AlgHom.fst_apply,
    Subtype.exists, AlgHom.mem_equalizer, AlgHom.snd_apply, exists_prop, Prod.exists,
    exists_and_right]
  obtain ⟨r, hr⟩ := Algebra.adjoin_eq_exists_aeval (ResidueField Λ) x ⟨y, hx y⟩
  obtain ⟨r, rfl⟩ :=
    map_surjective (algebraMap Λ (ResidueField Λ)) IsLocalRing.residue_surjective r
  rw [aeval_map_algebraMap] at hr
  exact ⟨aeval a r, ⟨aeval b r, by simp [aeval_def, hab]⟩, by simpa [aeval_def, ha]⟩

end ofPullback

section ArtinianRing

variable [IsLocalRing Λ] [Module.Finite Λ k]

open Module in
@[stacks 06GG]
theorem length_restrictScalars {M : Type*} [AddCommGroup M] [Module A M] [Module Λ M]
    [IsScalarTower Λ A M] : length Λ M = finrank (ResidueField Λ) k * length A M := by
  have : IsLocalHom (algebraMap Λ A) := isLocalHom_algebraMap A
  rw [IsLocalRing.length_restrictScalars Λ A M, mul_comm, ← length_eq_finrank,
    (A.residueEquiv.toLinearEquiv.extendScalarsOfSurjective <|
      IsLocalRing.residue_surjective (R := Λ)).length_eq]

variable (A) in
theorem isFiniteLength_of_isArtinianRing [IsArtinianRing A] : IsFiniteLength Λ A := by
  rw [← Module.length_ne_top_iff, length_restrictScalars (A := A)]
  have (n : ℕ) (s : ENat) (hs : s ≠ ⊤) : n * s ≠ ⊤ := by
    lift s to ℕ using hs
    exact WithTop.coe_ne_top
  exact this _ _ Module.length_ne_top

instance [IsArtinianRing A] : IsNoetherian Λ A :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_of_isArtinianRing A)).left

instance [IsArtinianRing A] : IsArtinian Λ A :=
  (isFiniteLength_iff_isNoetherian_isArtinian.mp (isFiniteLength_of_isArtinianRing A)).right

instance [IsArtinianRing A] [IsArtinianRing B] (f : A ⟶ C) (g : B ⟶ C) :
    IsArtinianRing (f.toAlgHom.pullback g.toAlgHom) := by
  let PB := f.toAlgHom.pullback g.toAlgHom
  rw [isArtinianRing_iff_isFiniteLength, ← Module.length_ne_top_iff]
  refine ne_top_of_le_ne_top (b := Module.length Λ PB) ?_ ?_
  · refine ne_top_of_le_ne_top (b := Module.length Λ (A × B)) ?_ ?_
    · rw [Module.length_prod]
      exact WithTop.add_ne_top.mpr ⟨Module.length_ne_top, Module.length_ne_top⟩
    · exact Module.length_le_of_injective (Submodule.subtype PB.toSubmodule)
        (Submodule.subtype_injective _)
  have := Submodule.length_le_length_restrictScalars (R := PB) (M := PB) Λ ⊤
  rwa [Module.length_top, Submodule.restrictScalars_top, Module.length_top] at this

theorem isArtinianRing_ofPullback [IsArtinianRing A] [IsArtinianRing B] (f : A ⟶ C) (g : B ⟶ C)
    (h : Surjective g.toAlgHom) : IsArtinianRing (ofPullback f g h) := by
  rw [ofPullback]
  infer_instance

end ArtinianRing

lemma exists_mem_maximalIdeal_toAlgHom_apply_add_eq (f : A ⟶ C) (g : B ⟶ C) (a : A)
    (hf : Surjective f.toAlgHom) : ∃ (b : B) (m : A), m ∈ maximalIdeal A ∧
      f.toAlgHom (a + m) = g.toAlgHom b := by
  rcases B.residue_surjective (residue A a) with ⟨b, hb⟩
  rw [← g.residue_comp, ← f.residue_comp, AlgHom.comp_apply, AlgHom.comp_apply, ← sub_eq_zero,
    ← map_sub, residue_eq_zero_iff, ← map_maximalIdeal_of_surjective (f.toAlgHom : A →+* C) hf,
    Ideal.mem_map_iff_of_surjective (f.toAlgHom : A →+* C) hf] at hb
  rcases hb with ⟨m, hm⟩
  simp only [RingHom.coe_coe, eq_sub_iff_add_eq', ← map_add] at hm
  exact ⟨b, m, hm⟩

end LocAlgCat
