/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Module.Basic
import Mathlib.LinearAlgebra.Finsupp
import Mathlib.LinearAlgebra.Quotient

/-!
# Presentations of modules

-/

universe w₁ w₀ v' v u

namespace Module

variable (A : Type u) [Ring A]

@[nolint checkUnivs]
structure PresentationData where
  G : Type w₀
  R : Type w₁
  relation (r : R) : G →₀ A

namespace PresentationData

variable {A} (data : PresentationData A)

abbrev Quotient := (data.G →₀ A) ⧸ Submodule.span A (Set.range data.relation)
def toQuotient : (data.G →₀ A) →ₗ[A] data.Quotient := Submodule.mkQ _

@[simp]
lemma toQuotient_relation (r : data.R) :
    data.toQuotient (data.relation r) = 0 := by
  dsimp only [toQuotient]
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Submodule.subset_span (by simp)

noncomputable def map : (data.R →₀ A) →ₗ[A] (data.G →₀ A) :=
  Finsupp.lift _ _ _ data.relation

@[simp]
lemma map_single (r : data.R) : data.map (Finsupp.single r 1) = data.relation r := by
  simp [map]

variable (M : Type v) [AddCommGroup M] [Module A M]

structure MapData where
  generator (g : data.G) : M
  relation (r : data.R) : Finsupp.lift _ A _ generator (data.relation r) = 0

namespace MapData

variable {data M}

section

variable (mapData : data.MapData M)

noncomputable def π : (data.G →₀ A) →ₗ[A] M := Finsupp.lift _ _ _ mapData.generator

@[simp]
lemma π_single (g : data.G) : mapData.π (Finsupp.single g 1) = mapData.generator g := by simp [π]

@[simp]
lemma π_relation (r : data.R) : mapData.π (data.relation r) = 0 := mapData.relation r

@[simp]
lemma π_comp_map : mapData.π.comp data.map = 0 := by aesop

@[simp]
lemma π_comp_map_apply (x : data.R →₀ A) : mapData.π (data.map x) = 0 := by
  change mapData.π.comp data.map x = 0
  rw [π_comp_map, LinearMap.zero_apply]

noncomputable def mapToKer : (data.R →₀ A) →ₗ[A] (LinearMap.ker mapData.π) :=
  LinearMap.codRestrict _ data.map (by simp)

@[simp]
lemma mapToKer_coe (x : data.R →₀ A) : (mapData.mapToKer x).1 = data.map x := rfl

lemma span_relation_le_ker_π :
    Submodule.span A (Set.range data.relation) ≤ LinearMap.ker mapData.π := by
  rw [Submodule.span_le]
  rintro _ ⟨r, rfl⟩
  simp only [SetLike.mem_coe, LinearMap.mem_ker, π_relation]

noncomputable def fromQuotient : data.Quotient →ₗ[A] M :=
  Submodule.liftQ _ mapData.π mapData.span_relation_le_ker_π

@[simp]
lemma fromQuotient_single (g : data.G) :
    mapData.fromQuotient (Submodule.Quotient.mk (Finsupp.single g 1)) =
      mapData.generator g := by
  simp [fromQuotient]

end

section

variable (π : (data.G →₀ A) →ₗ[A] M) (hπ : ∀ (r : data.R), π (data.relation r) = 0)

noncomputable def ofπ : data.MapData M where
  generator g := π (Finsupp.single g 1)
  relation r := by
    have : π = Finsupp.lift _ _ _ (fun g ↦ π (Finsupp.single g 1)) := by ext; simp
    rw [← this]
    exact hπ r

@[simp]
lemma ofπ_π : (ofπ π hπ).π = π := by ext; simp [ofπ]

end

section

variable (π : (data.G →₀ A) →ₗ[A] M) (hπ : π.comp data.map = 0)

/-- Variant of `ofπ` where the vanishing condition is expressed in terms
of a composition of linear maps. -/
noncomputable def ofπ' : data.MapData M :=
  ofπ π (fun r ↦ by
    simpa using DFunLike.congr_fun hπ (Finsupp.single r 1))

@[simp]
lemma ofπ'_π : (ofπ' π hπ).π = π := by simp [ofπ']

end

structure IsPresentation (mapData : data.MapData M) : Prop where
  bijective : Function.Bijective mapData.fromQuotient

namespace IsPresentation

variable {mapData : data.MapData M} (h : mapData.IsPresentation)

noncomputable def linearEquiv : data.Quotient ≃ₗ[A] M := LinearEquiv.ofBijective _ h.bijective

@[simp]
lemma linearEquiv_apply (x : data.Quotient) : h.linearEquiv x = mapData.fromQuotient x := rfl

@[simp]
lemma linearEquiv_symm_generator (g : data.G) :
    h.linearEquiv.symm (mapData.generator g) = Submodule.Quotient.mk (Finsupp.single g 1) :=
  h.linearEquiv.injective (by simp)

variable {N : Type v'} [AddCommGroup N] [Module A N]

noncomputable def desc (μ : data.MapData N) : M →ₗ[A] N :=
  μ.fromQuotient.comp h.linearEquiv.symm.toLinearMap

@[simp]
lemma desc_generator (μ : data.MapData N) (g : data.G) :
    h.desc μ (mapData.generator g) = μ.generator g := by
  dsimp [desc]
  rw [linearEquiv_symm_generator, fromQuotient_single]

include h in
lemma linearMap_ext {f f' : M →ₗ[A] N}
    (hff' : ∀ (g : data.G), f (mapData.generator g) = f' (mapData.generator g)) : f = f' := by
  suffices f.comp mapData.fromQuotient = f'.comp mapData.fromQuotient by
    ext x
    obtain ⟨y, rfl⟩ := h.bijective.2 x
    exact DFunLike.congr_fun this y
  ext g
  simpa using hff' g

end IsPresentation

section

variable (data)

noncomputable def ofQuotient : data.MapData data.Quotient :=
  ofπ data.toQuotient (by simp)

@[simp]
lemma ofQuotient_π : (ofQuotient data).π = Submodule.mkQ _ := ofπ_π _ _

@[simp]
lemma ofQuotient_fromQuotient : (ofQuotient data).fromQuotient = .id := by aesop

lemma ofQuotient_isPresentation : (ofQuotient data).IsPresentation where
  bijective := by
    simpa only [ofQuotient_fromQuotient, LinearMap.id_coe] using Function.bijective_id

end

end MapData

end PresentationData

variable {A} (M : Type v) [AddCommGroup M] [Module A M] (data : PresentationData A)

structure Presentation where
  mapData : data.MapData M
  isPresentation : mapData.IsPresentation

end Module
