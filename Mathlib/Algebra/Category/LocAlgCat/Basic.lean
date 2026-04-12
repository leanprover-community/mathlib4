/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

module

public import Mathlib.Algebra.Category.LocAlgCat.Defs

/-!
# Basic Constructions and Lemmas in `LocAlgCat`

## Main Results

* `LocAlgCat.ofQuot` : The object in `LocAlgCat` obtained from quotienting by a proper ideal.

* `LocAlgCat.toOfQuot` : The canonical quotient morphism `A ⟶ A.ofQuot I`.

* `LocAlgCat.mapOfQuot` : The categorical morphism between quotient objects induced
  by a morphism `f : A ⟶ B`. This is the categorical counterpart to `Ideal.quotientMapₐ`.

* `LocAlgCat.infinitesimalNeighborhood` : The quotient of a local algebra by the
  `n`-th power of its maximal ideal.

* `LocAlgCat.specialFiber` : The special fiber of `A` over a local base ring `Λ`,
  defined as the quotient of `A` by the extended maximal ideal of `Λ`.

-/

@[expose] public section

universe w v u

namespace LocAlgCat

open IsLocalRing CategoryTheory Function

variable {Λ : Type u} [CommRing Λ] {k : Type v} [Field k] [Algebra Λ k] {A B : LocAlgCat.{w} Λ k}

instance [IsLocalHom (algebraMap Λ k)] : IsLocalHom (algebraMap Λ A) :=
  haveI : IsLocalHom ((algebraMap A k).comp (algebraMap Λ A)) := by
    rwa [← IsScalarTower.algebraMap_eq]
  isLocalHom_of_comp _ (algebraMap A k)

lemma comap_algebraMap_maximalIdeal [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)] :
    (maximalIdeal A).comap (algebraMap Λ A) = maximalIdeal Λ := by
  have := ((local_hom_TFAE (algebraMap Λ k)).out 0 4).mp ‹_›
  rw [eq_comm, ← this, IsScalarTower.algebraMap_eq Λ A, ← Ideal.comap_comap,
    eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ A.surj)]

instance [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)] :
    Nontrivial (A ⧸ ((maximalIdeal Λ).map (algebraMap Λ A))) :=
  Ideal.Quotient.nontrivial_iff.mpr <| ne_top_of_le_ne_top
  (maximalIdeal.isMaximal A).ne_top <| ((local_hom_TFAE (algebraMap Λ A)).out 0 2).mp
    (by infer_instance)

section ofQuot

variable {I : Ideal A}

/-- The residue algebra structure on `ofQuot`. -/
instance ofQuotResidueAlgebra [Nontrivial (A ⧸ I)] : Algebra (A ⧸ I) k :=
  (Ideal.Quotient.lift I (algebraMap A k) fun a a_in ↦ by
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
    Algebra A (A.ofQuot I) := Ideal.Quotient.algebra _

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

@[simp, reassoc]
theorem toOfQuot_comp_mapOfQuot (f : A ⟶ B) {J : Ideal B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)]
    (hf : I ≤ J.comap f.toAlgHom) : A.toOfQuot I ≫ mapOfQuot f hf = f ≫ B.toOfQuot J := rfl

@[simp]
lemma toAlgHom_mapOfQuot_apply (f : A ⟶ B) {J : Ideal B} [Nontrivial (A ⧸ I)] [Nontrivial (B ⧸ J)]
    (hf : I ≤ J.comap f.toAlgHom) (a : A) : (mapOfQuot f hf).toAlgHom (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk J (f.toAlgHom a) := rfl

/-- The quotient of a local algebra by the `n`-th power of its maximal ideal.
Geometrically, this represents an infinitesimal neighborhood of the closed point. -/
abbrev infinitesimalNeighborhood {n : ℕ} (hn : n ≠ 0) (A : LocAlgCat.{w} Λ k) : LocAlgCat Λ k :=
  letI : Nontrivial (A ⧸ (maximalIdeal A) ^ n) := by
    rw [Ideal.Quotient.nontrivial_iff, Ideal.ne_top_iff_exists_maximal]
    exact ⟨maximalIdeal A, maximalIdeal.isMaximal A, Ideal.pow_le_self hn⟩
  A.ofQuot (maximalIdeal A ^ n)

/-- The canonical quotient morphism from `A` to its infinitesimal neighborhood. -/
abbrev toInfinitesimalNeighborhood {n : ℕ} (hn : n ≠ 0) (A : LocAlgCat.{w} Λ k) :
    A ⟶ A.infinitesimalNeighborhood hn :=
  letI : Nontrivial (A ⧸ (maximalIdeal A) ^ n) := by
    rw [Ideal.Quotient.nontrivial_iff, Ideal.ne_top_iff_exists_maximal]
    exact ⟨maximalIdeal A, maximalIdeal.isMaximal A, Ideal.pow_le_self hn⟩
  toOfQuot ..

/-- The morphism between infinitesimal neighborhoods induced by a morphism in `LocAlgCat`. -/
abbrev mapInfinitesimalNeighborhood {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) (hmn : n ≤ m) (f : A ⟶ B) :
    A.infinitesimalNeighborhood hm ⟶ B.infinitesimalNeighborhood hn :=
  letI : Nontrivial (A ⧸ (maximalIdeal A) ^ m) := by
    rw [Ideal.Quotient.nontrivial_iff, Ideal.ne_top_iff_exists_maximal]
    exact ⟨maximalIdeal A, maximalIdeal.isMaximal A, Ideal.pow_le_self hm⟩
  letI : Nontrivial (B ⧸ (maximalIdeal B) ^ n) := by
    rw [Ideal.Quotient.nontrivial_iff, Ideal.ne_top_iff_exists_maximal]
    exact ⟨maximalIdeal B, maximalIdeal.isMaximal B, Ideal.pow_le_self hn⟩
  mapOfQuot f (le_trans (Ideal.pow_le_pow_right hmn) (f.comap_maximalIdeal_eq ▸
      Ideal.le_comap_pow f.toAlgHom n))

/-- The special fiber of `A` over `Λ` when `Λ` is a local ring, defined as the quotient by
the extended maximal ideal of `Λ`, viewed as an object in `LocAlgCat`. -/
abbrev specialFiber [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (A : LocAlgCat.{w} Λ k) : LocAlgCat.{w} Λ k := A.ofQuot ((maximalIdeal Λ).map (algebraMap Λ A))

/-- The canonical morphism from `A` to its special fiber. -/
abbrev toSpecialFiber [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (A : LocAlgCat.{w} Λ k) : A ⟶ A.specialFiber := toOfQuot ..

/-- The morphism between special fibers induced by a morphism between two objects. -/
abbrev mapSpecialFiber [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (f : A ⟶ B) : A.specialFiber ⟶ B.specialFiber :=
  mapOfQuot f (by rw [Ideal.map_le_iff_le_comap, ← Ideal.comap_coe f.toAlgHom,
    Ideal.comap_comap, AlgHom.comp_algebraMap, ← Ideal.map_le_iff_le_comap])

@[simp]
lemma algebraMap_specialFiber_apply_eq_zero [IsLocalRing Λ] [IsLocalHom (algebraMap Λ k)]
    (A : LocAlgCat.{w} Λ k) {y : Λ} (y_in : y ∈ maximalIdeal Λ) :
    algebraMap Λ A.specialFiber y = 0 := by
  rw [IsScalarTower.algebraMap_apply Λ A A.specialFiber]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ y_in)

end ofQuot

end LocAlgCat
