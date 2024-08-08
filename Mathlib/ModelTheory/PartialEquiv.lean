/-
Copyright (c) 2024 Gabin Kolly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly
-/
import Mathlib.ModelTheory.Substructures

/-!
# Partial Isomorphisms
This file defines partial isomorphisms between first-order structures.

## Main Definitions
- `FirstOrder.Language.Substructure.PartialEquiv` is defined so that `L.PartialEquiv M N`, annotated
  `M ≃ₚ[L] N`, is the type of equivalences between substructures of `M` and `N`.

-/

universe u v w w'

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) (M : Type w) (N : Type w') {P : Type*}
variable [L.Structure M] [L.Structure N] [L.Structure P]

open FirstOrder Structure Substructure

/-- A partial `L`-equivalence, implemented as an equivalence between substructures. -/
structure PartialEquiv where
  /-- The substructure which is the domain of the equivalence. -/
  dom : L.Substructure M
  /-- The substructure which is the codomain of the equivalence. -/
  cod : L.Substructure N
  /-- The equivalence between the two subdomains. -/
  toEquiv : dom ≃[L] cod

@[inherit_doc]
scoped[FirstOrder] notation:25 M " ≃ₚ[" L "] " N =>
  FirstOrder.Language.PartialEquiv L M N

variable {L M N}

namespace PartialEquiv

noncomputable instance instInhabited_self : Inhabited (M ≃ₚ[L] M) :=
  ⟨⊤, ⊤, Equiv.refl L (⊤ : L.Substructure M)⟩

/-- Maps to the symmetric partial equivalence. -/
def symm (f : M ≃ₚ[L] N) : N ≃ₚ[L] M where
  dom := f.cod
  cod := f.dom
  toEquiv := f.toEquiv.symm

@[simp]
theorem symm_symm (f : M ≃ₚ[L] N) : f.symm.symm = f :=
  rfl

@[simp]
theorem symm_apply (f : M ≃ₚ[L] N) (x : f.cod) : f.symm.toEquiv x = f.toEquiv.symm x :=
  rfl

instance : LE (M ≃ₚ[L] N) :=
  ⟨fun f g ↦ ∃h : f.dom ≤ g.dom,
    (subtype _).comp (g.toEquiv.toEmbedding.comp (Substructure.inclusion h)) =
      (subtype _).comp f.toEquiv.toEmbedding⟩

theorem le_def (f g : M ≃ₚ[L] N) : f ≤ g ↔ ∃ h : f.dom ≤ g.dom,
    (subtype _).comp (g.toEquiv.toEmbedding.comp (Substructure.inclusion h)) =
      (subtype _).comp f.toEquiv.toEmbedding :=
  Iff.rfl

@[gcongr] theorem dom_le_dom {f g : M ≃ₚ[L] N} : f ≤ g → f.dom ≤ g.dom := fun ⟨le, _⟩ ↦ le

@[gcongr] theorem cod_le_cod {f g : M ≃ₚ[L] N} : f ≤ g → f.cod ≤ g.cod := by
  rintro ⟨_, eq_fun⟩ n hn
  let m := f.toEquiv.symm ⟨n, hn⟩
  have  : ((subtype _).comp f.toEquiv.toEmbedding) m = n := by simp only [m, Embedding.comp_apply,
    Equiv.coe_toEmbedding, Equiv.apply_symm_apply, coeSubtype]
  rw [← this, ← eq_fun]
  simp only [Embedding.comp_apply, coe_inclusion, Equiv.coe_toEmbedding, coeSubtype,
    SetLike.coe_mem]

theorem subtype_toEquiv_inclusion {f g : M ≃ₚ[L] N} (h : f ≤ g) :
    (subtype _).comp (g.toEquiv.toEmbedding.comp (Substructure.inclusion (dom_le_dom h))) =
      (subtype _).comp f.toEquiv.toEmbedding := by
  let ⟨_, eq⟩ := h; exact eq

theorem toEquiv_inclusion {f g : M ≃ₚ[L] N} (h : f ≤ g) :
    g.toEquiv.toEmbedding.comp (Substructure.inclusion (dom_le_dom h)) =
      (Substructure.inclusion (cod_le_cod h)).comp f.toEquiv.toEmbedding := by
  rw [← (subtype _).comp_inj, subtype_toEquiv_inclusion h]
  ext
  simp

theorem toEquiv_inclusion_apply {f g : M ≃ₚ[L] N} (h : f ≤ g) (x : f.dom) :
    g.toEquiv (Substructure.inclusion (dom_le_dom h) x) =
      Substructure.inclusion (cod_le_cod h) (f.toEquiv x) := by
  apply (subtype _).injective
  change (subtype _).comp (g.toEquiv.toEmbedding.comp (inclusion _)) x = _
  rw [subtype_toEquiv_inclusion h]
  simp

theorem le_iff {f g : M ≃ₚ[L] N} : f ≤ g ↔
    ∃ dom_le_dom : f.dom ≤ g.dom,
    ∃ cod_le_cod : f.cod ≤ g.cod,
    ∀ x, inclusion cod_le_cod (f.toEquiv x) = g.toEquiv (inclusion dom_le_dom x) := by
  constructor
  · exact fun h ↦ ⟨dom_le_dom h, cod_le_cod h,
      by intro x; apply (subtype _).inj'; rwa [toEquiv_inclusion_apply]⟩
  · rintro ⟨dom_le_dom, le_cod, h_eq⟩
    rw [le_def]
    exact ⟨dom_le_dom, by ext; change subtype _ (g.toEquiv _) = _; rw [← h_eq]; rfl⟩

theorem le_trans (f g h : M ≃ₚ[L] N) : f ≤ g → g ≤ h → f ≤ h := by
  rintro ⟨le_fg, eq_fg⟩ ⟨le_gh, eq_gh⟩
  refine ⟨le_fg.trans le_gh, ?_⟩
  rw [← eq_fg, ← Embedding.comp_assoc (g := g.toEquiv.toEmbedding), ← eq_gh]
  ext
  simp

private theorem le_refl (f : M ≃ₚ[L] N) : f ≤ f := ⟨le_rfl, rfl⟩

private theorem le_antisymm (f g : M ≃ₚ[L] N) (le_fg : f ≤ g) (le_gf : g ≤ f) : f = g := by
  let ⟨dom_f, cod_f, equiv_f⟩ := f
  cases _root_.le_antisymm (dom_le_dom le_fg) (dom_le_dom le_gf)
  cases _root_.le_antisymm (cod_le_cod le_fg) (cod_le_cod le_gf)
  convert rfl
  exact Equiv.injective_toEmbedding ((subtype _).comp_injective (subtype_toEquiv_inclusion le_fg))

instance : PartialOrder (M ≃ₚ[L] N) where
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

@[gcongr] lemma symm_le_symm {f g : M ≃ₚ[L] N} (hfg : f ≤ g) : f.symm ≤ g.symm := by
  rw [le_iff]
  refine ⟨cod_le_cod hfg, dom_le_dom hfg, ?_⟩
  intro x
  apply g.toEquiv.injective
  change g.toEquiv (inclusion _ (f.toEquiv.symm x)) = g.toEquiv (g.toEquiv.symm _)
  rw [g.toEquiv.apply_symm_apply, (Equiv.apply_symm_apply f.toEquiv x).symm,
    f.toEquiv.symm_apply_apply]
  exact toEquiv_inclusion_apply hfg _

theorem monotone_symm : Monotone (fun (f : M ≃ₚ[L] N) ↦ f.symm) := fun _ _ => symm_le_symm

theorem symm_le_iff {f : M ≃ₚ[L] N} {g : N ≃ₚ[L] M} : f.symm ≤ g ↔ f ≤ g.symm :=
  ⟨by intro h; rw [← f.symm_symm]; exact monotone_symm h,
    by intro h; rw  [← g.symm_symm]; exact monotone_symm h⟩

theorem ext {f g : M ≃ₚ[L] N} (h_dom : f.dom = g.dom) : (∀ x : M, ∀ h : x ∈ f.dom,
    subtype _ (f.toEquiv ⟨x, h⟩) = subtype _ (g.toEquiv ⟨x, (h_dom ▸ h)⟩)) → f = g := by
  intro h
  rcases f with ⟨dom_f, cod_f, equiv_f⟩
  cases h_dom
  apply le_antisymm <;> (rw [le_def]; use le_rfl; ext ⟨x, hx⟩)
  · exact (h x hx).symm
  · exact h x hx

theorem ext_iff {f g : M ≃ₚ[L] N} : f = g ↔ ∃ h_dom : f.dom = g.dom,
    ∀ x : M, ∀ h : x ∈ f.dom,
    subtype _ (f.toEquiv ⟨x, h⟩) = subtype _ (g.toEquiv ⟨x, (h_dom ▸ h)⟩) := by
  constructor
  · intro h_eq
    rcases f with ⟨dom_f, cod_f, equiv_f⟩
    cases h_eq
    exact ⟨rfl, fun _ _ ↦ rfl⟩
  · rintro ⟨h, H⟩; exact ext h H

theorem monotone_dom : Monotone (fun f : M ≃ₚ[L] N ↦ f.dom) := fun _ _ ↦ dom_le_dom

theorem monotone_cod : Monotone (fun f : M ≃ₚ[L] N ↦ f.cod) := fun _ _ ↦ cod_le_cod

/-- Restriction of a partial equivalence to a substructure of the domain. -/
noncomputable def domRestrict (f : M ≃ₚ[L] N) {A : L.Substructure M} (h : A ≤ f.dom) :
    M ≃ₚ[L] N := by
  let g := (subtype _).comp (f.toEquiv.toEmbedding.comp (A.inclusion h))
  exact {
    dom := A
    cod := g.toHom.range
    toEquiv := g.equivRange
  }

theorem domRestrict_le (f : M ≃ₚ[L] N) {A : L.Substructure M} (h : A ≤ f.dom) :
    f.domRestrict h ≤ f := ⟨h, rfl⟩

theorem le_domRestrict (f g : M ≃ₚ[L] N) {A : L.Substructure M} (hf : f.dom ≤ A)
    (hg : A ≤ g.dom) (hfg : f ≤ g) : f ≤ g.domRestrict hg :=
  ⟨hf, by rw [← (subtype_toEquiv_inclusion hfg)]; rfl⟩

/-- Restriction of a partial equivalence to a substructure of the codomain. -/
noncomputable def codRestrict (f : M ≃ₚ[L] N) {A : L.Substructure N} (h : A ≤ f.cod) :
    M ≃ₚ[L] N :=
  (f.symm.domRestrict h).symm

theorem codRestrict_le (f : M ≃ₚ[L] N) {A : L.Substructure N} (h : A ≤ f.cod) :
    codRestrict f h ≤ f :=
  symm_le_iff.2 (f.symm.domRestrict_le h)

theorem le_codRestrict (f g : M ≃ₚ[L] N) {A : L.Substructure N} (hf : f.cod ≤ A)
    (hg : A ≤ g.cod) (hfg : f ≤ g) : f ≤ g.codRestrict hg :=
  symm_le_iff.1 (le_domRestrict f.symm g.symm hf hg (monotone_symm hfg))

/-- A partial equivalence as an embedding from its domain. -/
def toEmbedding (f : M ≃ₚ[L] N) : f.dom ↪[L] N :=
  (subtype _).comp f.toEquiv.toEmbedding

@[simp]
theorem toEmbedding_apply {f : M ≃ₚ[L] N} (m : f.dom) :
    f.toEmbedding m = f.toEquiv m :=
  rfl

/-- Given a partial equivalence which has the whole structure as domain,
  returns the corresponding embedding. -/
def toEmbeddingOfEqTop {f : M ≃ₚ[L] N} (h : f.dom = ⊤) : M ↪[L] N :=
  (h ▸ f.toEmbedding).comp topEquiv.symm.toEmbedding

@[simp]
theorem toEmbeddingOfEqTop__apply {f : M ≃ₚ[L] N} (h : f.dom = ⊤) (m : M) :
    toEmbeddingOfEqTop h m = f.toEquiv ⟨m, h.symm ▸ mem_top m⟩ := by
  rcases f with ⟨dom, cod, g⟩
  cases h
  rfl

/-- Given a partial equivalence which has the whole structure as domain and
  as codomain, returns the corresponding equivalence. -/
def toEquivOfEqTop {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤)
    (h_cod : f.cod = ⊤) : M ≃[L] N :=
  (topEquiv (M := N)).comp ((h_dom ▸ h_cod ▸ f.toEquiv).comp (topEquiv (M := M)).symm)

@[simp]
theorem toEquivOfEqTop_toEmbedding {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤)
    (h_cod : f.cod = ⊤) :
    (toEquivOfEqTop h_dom h_cod).toEmbedding = toEmbeddingOfEqTop h_dom := by
  rcases f with ⟨dom, cod, g⟩
  cases h_dom
  cases h_cod
  rfl

end PartialEquiv

namespace Embedding

/-- Given an embedding, returns the corresponding partial equivalence with `⊤` as domain. -/
noncomputable def toPartialEquiv (f : M ↪[L] N) : M ≃ₚ[L] N :=
  ⟨⊤, f.toHom.range, f.equivRange.comp (Substructure.topEquiv)⟩

theorem toPartialEquiv_injective :
    Function.Injective (fun f : M ↪[L] N ↦ f.toPartialEquiv) := by
  intro _ _ h
  ext
  rw [PartialEquiv.ext_iff] at h
  rcases h with ⟨_, H⟩
  exact H _ (Substructure.mem_top _)

@[simp]
theorem toEmbedding_toPartialEquiv (f : M ↪[L] N) :
    PartialEquiv.toEmbeddingOfEqTop (f := f.toPartialEquiv) rfl = f :=
  rfl

@[simp]
theorem toPartialEquiv_toEmbedding {f :  M ≃ₚ[L] N} (h : f.dom = ⊤) :
    (PartialEquiv.toEmbeddingOfEqTop h).toPartialEquiv = f := by
  rcases f with ⟨_, _, _⟩
  cases h
  apply PartialEquiv.ext
  · intro _ _
    rfl
  · rfl

end Embedding

end Language

end FirstOrder
