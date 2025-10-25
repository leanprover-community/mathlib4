/-
Copyright (c) 2024 Gabin Kolly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly, David Wärn
-/
import Mathlib.ModelTheory.DirectLimit
import Mathlib.Order.Ideal

/-!
# Partial Isomorphisms
This file defines partial isomorphisms between first-order structures.

## Main Definitions
- `FirstOrder.Language.PartialEquiv` is defined so that `L.PartialEquiv M N`, annotated
  `M ≃ₚ[L] N`, is the type of equivalences between substructures of `M` and `N`. These can be
  ordered, with an order that is defined here in terms of a commutative square, but could also be
  defined as the order on the graphs of the partial equivalences under inclusion as subsets of
  `M × N`.
- `FirstOrder.Language.FGEquiv` is the type of partial equivalences `M ≃ₚ[L] N` with
  finitely-generated domain (or equivalently, codomain).
- `FirstOrder.Language.IsExtensionPair` is defined so that `L.IsExtensionPair M N` indicates that
  any finitely-generated partial equivalence from `M` to `N` can be extended to include an arbitrary
  element `m : M` in its domain.

## Main Results
- `FirstOrder.Language.embedding_from_cg` shows that if structures `M` and `N` form an equivalence
  pair with `M` countably-generated, then any finite-generated partial equivalence between them
  can be extended to an embedding `M ↪[L] N`.
- `FirstOrder.Language.equiv_from_cg` shows that if countably-generated structures `M` and `N` form
  an equivalence pair in both directions, then any finite-generated partial equivalence between them
  can be extended to an isomorphism `M ↪[L] N`.
- The proofs of these results are adapted in part from David Wärn's approach to countable dense
  linear orders, a special case of this phenomenon in the case where `L = Language.order`.

-/

universe u v w w' w''

namespace FirstOrder

namespace Language

variable (L : Language.{u, v}) (M : Type w) (N : Type w') (P : Type w'')
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

variable {L M N P}

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

theorem symm_bijective : Function.Bijective (symm : (M ≃ₚ[L] N) → _) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
theorem symm_apply (f : M ≃ₚ[L] N) (x : f.cod) : f.symm.toEquiv x = f.toEquiv.symm x :=
  rfl

instance : LE (M ≃ₚ[L] N) :=
  ⟨fun f g ↦ ∃ h : f.dom ≤ g.dom,
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
  have : ((subtype _).comp f.toEquiv.toEmbedding) m = n := by simp only [m, Embedding.comp_apply,
    Equiv.coe_toEmbedding, Equiv.apply_symm_apply, coe_subtype]
  rw [← this, ← eq_fun]
  simp only [Embedding.comp_apply, coe_inclusion, Equiv.coe_toEmbedding, coe_subtype,
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
    cases h_eq
    exact ⟨rfl, fun _ _ ↦ rfl⟩
  · rintro ⟨h, H⟩; exact ext h H

/-- Extensionality lemma using EquivOfEq. -/
theorem ext_iff' {f g : M ≃ₚ[L] N} : f = g ↔ ∃ h_dom : f.dom = g.dom, ∃ h_cod : f.cod = g.cod,
    (equivOfEq h_cod).comp f.toEquiv = g.toEquiv.comp (equivOfEq h_dom) := by
  constructor
  · intro h_eq
    cases h_eq
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨h_dom, h_cod, H⟩
    rcases f with ⟨f, _, _⟩
    cases h_dom
    cases h_cod
    simp only [equivOfEq_refl, Equiv.refl_comp, Equiv.comp_refl] at H
    rw [H]

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
theorem toEmbeddingOfEqTop_apply {f : M ≃ₚ[L] N} (h : f.dom = ⊤) (m : M) :
    toEmbeddingOfEqTop h m = f.toEquiv ⟨m, h.symm ▸ mem_top m⟩ := by
  rcases f with ⟨dom, cod, g⟩
  cases h
  rfl

set_option linter.style.nameCheck false in
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

/-- Map of a self-PartialEquiv through an embedding. -/
noncomputable def map (f : M ↪[L] N) (g : M ≃ₚ[L] M) : N ≃ₚ[L] N where
  dom := g.dom.map f.toHom
  cod := g.cod.map f.toHom
  toEquiv := (f.substructureEquivMap g.cod).comp <|
    g.toEquiv.comp (f.substructureEquivMap g.dom).symm

@[simp]
theorem map_dom (f : M ↪[L] N) (g : M ≃ₚ[L] M) : (g.map f).dom = g.dom.map f.toHom := rfl

@[simp]
theorem map_cod (f : M ↪[L] N) (g : M ≃ₚ[L] M) : (g.map f).cod = g.cod.map f.toHom := rfl

theorem map_toEquiv_comp_substructureEquivMap (f : M ↪[L] N) (g : M ≃ₚ[L] M) :
    (g.map f).toEquiv.comp (f.substructureEquivMap g.dom) =
      (f.substructureEquivMap g.cod).comp g.toEquiv := by
  ext
  simp only [map, Equiv.comp_apply, Equiv.symm_apply_apply, Embedding.substructureEquivMap_apply]

theorem map_toEquiv_comp_substructureEquivMap_apply (f : M ↪[L] N) (g : M ≃ₚ[L] M) (m : g.dom) :
    (g.map f).toEquiv ⟨f m, g.dom.apply_coe_mem_map _ _⟩ =
      ⟨f (g.toEquiv m), g.cod.apply_coe_mem_map _ _⟩ := by
  exact congr_fun (congr_arg DFunLike.coe (g.map_toEquiv_comp_substructureEquivMap f)) m

@[simp]
theorem map_refl (f : M ≃ₚ[L] M) : f.map (Embedding.refl L M) = f := by
  rw [ext_iff']
  simp only [map, Embedding.refl_toHom, substructureEquivMap_refl, equivOfEq_symm, map_id,
    exists_true_left]
  rw [← Equiv.comp_assoc, equivOfEq_comp, equivOfEq_refl, Equiv.refl_comp]

theorem map_monotone (f : M ↪[L] N) : Monotone (map f) := by
  intro g g' h
  rw [le_iff]
  use Substructure.monotone_map (dom_le_dom h)
  use Substructure.monotone_map (cod_le_cod h)
  rintro ⟨x, hx⟩
  let ⟨u, u_mem, eq_u_x⟩ := mem_map.2 hx
  cases eq_u_x
  apply Subtype.coe_injective
  simp only [map, Embedding.coe_toHom, Equiv.comp_apply, coe_inclusion, Set.coe_inclusion,
    Embedding.substructureEquivMap_apply, Set.inclusion_mk, EmbeddingLike.apply_eq_iff_eq]
  let ⟨_, _, eq⟩ := le_iff.1 h
  have eq := congr_arg (Subtype.val) (eq ((Equiv.symm (Embedding.substructureEquivMap f g.dom))
    { val := f u, property := (g.dom.mem_map).2 ⟨u, u_mem, rfl⟩}))
  simp only [coe_inclusion, Set.coe_inclusion] at eq
  rw [← coe_inclusion] at eq
  rw [eq, Subtype.coe_inj]
  apply congr_arg g'.toEquiv
  apply Subtype.coe_injective
  change subtype _ ((Equiv.symm (Embedding.substructureEquivMap f g.dom))
    (f.substructureEquivMap g.dom ⟨u, u_mem⟩)) =
    subtype _ ((Equiv.symm (Embedding.substructureEquivMap f g'.dom))
      (f.substructureEquivMap g'.dom ⟨u, dom_le_dom h u_mem⟩))
  simp only [Equiv.symm_apply_apply, coeSubtype]

@[simp]
theorem map_map (f : M ↪[L] N) (g : N ↪[L] P) (h : M ≃ₚ[L] M) :
    (h.map f).map g = h.map (g.comp f) := by
  rw [ext_iff']
  use Substructure.map_map ..
  use Substructure.map_map ..
  simp only [map, Embedding.comp_toHom, Equiv.comp_assoc]
  rw [← Equiv.comp_assoc _ _ (g.substructureEquivMap (Substructure.map f.toHom h.cod)),
    substructureEquivMap_comp_substructureEquivMap]
  simp only [← Equiv.comp_assoc, equivOfEq_comp, equivOfEq_refl, Equiv.refl_comp]
  simp only [Equiv.comp_assoc]
  rw [← Equiv.comp_symm, substructureEquivMap_comp_substructureEquivMap]
  simp only [Equiv.comp_symm, equivOfEq_symm]

theorem map_fg (f : M ↪[L] N) {g : M ≃ₚ[L] M} (g_fg : g.dom.FG) : (g.map f).dom.FG :=
  g_fg.map f.toHom

theorem exists_preimage_map_iff (f : M ↪[L] N) (g : N ≃ₚ[L] N) :
    (∃ (g' : M ≃ₚ[L] M), g'.map f = g) ↔ g.dom ⊔ g.cod ≤ f.toHom.range := by
  constructor
  · intro ⟨g', g'_map⟩
    have : g'.dom.map f.toHom ≤ f.toHom.range := Hom.map_le_range
    have : g'.cod.map f.toHom ≤ f.toHom.range := Hom.map_le_range
    apply sup_le <;> simpa [← g'_map, map_dom, map_cod]
  · intro dom_cod_le_range
    rw [sup_le_iff] at dom_cod_le_range
    let ⟨dom_le_range, cod_le_range⟩ := dom_cod_le_range
    let dom' := g.dom.comap f.toHom
    let cod' := g.cod.comap f.toHom
    have dom'_map : dom'.map f.toHom = g.dom := by
      unfold dom'
      rwa [Substructure.map_comap, inf_eq_left]
    have cod'_map : cod'.map f.toHom = g.cod := by
      rwa [Substructure.map_comap, inf_eq_left]
    clear_value dom' cod'
    rcases g with ⟨dom, cod, g⟩
    simp only at *
    cases cod'_map
    cases dom'_map
    let g' : M ≃ₚ[L] M := ⟨dom',
      cod',
      (f.substructureEquivMap cod').symm.comp (g.comp (f.substructureEquivMap dom'))⟩
    use g'
    simp only [map, mk.injEq, heq_eq_eq, true_and, g']
    ext x
    simp only [Equiv.comp_apply, Equiv.apply_symm_apply]

/-- A partial equivalence `f` between substructures of `M` is fully extendable through an embedding
`g` if there is a partial equivalence between substructures of the codomain of `g`
which extends the map of `f` and whose domain contains the image of `M`.-/
def is_fully_extendable_through (f : M ≃ₚ[L] M) (g : M ↪[L] N) : Prop :=
  ∃ f', f.map g ≤ f' ∧ g.toHom.range ≤ f'.dom

theorem is_fully_extendable_through_comp (f : M ≃ₚ[L] M) (g : M ↪[L] N) (g' : N ↪[L] P)
    (H : is_fully_extendable_through f g) : is_fully_extendable_through f (g'.comp g) := by
  let ⟨h, ⟨le_h, le_h_dom⟩⟩ := H
  use h.map g'
  constructor
  · rw [← map_map]
    exact map_monotone _ le_h
  · rw [map_dom, Embedding.comp_toHom, Hom.range_comp]
    exact Substructure.monotone_map le_h_dom

theorem comp_is_fully_extendable_through (f : M ≃ₚ[L] M) (g : M ↪[L] N) (g' : N ↪[L] P)
    (H : is_fully_extendable_through (f.map g) g') : is_fully_extendable_through f (g'.comp g) := by
  let ⟨h, ⟨le_h, le_h_dom⟩⟩ := H
  use h
  constructor
  · rwa [← map_map]
  · rw [Embedding.comp_toHom, Hom.range_comp]
    exact Hom.map_le_range.trans le_h_dom

theorem dom_fg_iff_cod_fg {N : Type*} [L.Structure N] (f : M ≃ₚ[L] N) :
    f.dom.FG ↔ f.cod.FG := by
  rw [Substructure.fg_iff_structure_fg, f.toEquiv.fg_iff, Substructure.fg_iff_structure_fg]

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
theorem toPartialEquiv_toEmbedding {f : M ≃ₚ[L] N} (h : f.dom = ⊤) :
    (PartialEquiv.toEmbeddingOfEqTop h).toPartialEquiv = f := by
  rcases f with ⟨_, _, _⟩
  cases h
  apply PartialEquiv.ext
  · intro _ _
    rfl
  · rfl

end Embedding

namespace DirectLimit

open PartialEquiv

variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
variable (S : ι →o M ≃ₚ[L] N)

instance : DirectedSystem (fun i ↦ (S i).dom)
    (fun _ _ h ↦ Substructure.inclusion (dom_le_dom (S.monotone h))) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

instance : DirectedSystem (fun i ↦ (S i).cod)
    (fun _ _ h ↦ Substructure.inclusion (cod_le_cod (S.monotone h))) where
  map_self _ _ := rfl
  map_map _ _ _ _ _ _ := rfl

/-- The limit of a directed system of PartialEquivs. -/
noncomputable def partialEquivLimit : M ≃ₚ[L] N where
  dom := iSup (fun i ↦ (S i).dom)
  cod := iSup (fun i ↦ (S i).cod)
  toEquiv :=
    (Equiv_iSup {
      toFun := (fun i ↦ (S i).cod)
      monotone' := monotone_cod.comp S.monotone}
    ).comp
      ((DirectLimit.equiv_lift L ι (fun i ↦ (S i).dom)
        (fun _ _ hij ↦ Substructure.inclusion (dom_le_dom (S.monotone hij)))
        (fun i ↦ (S i).cod)
        (fun _ _ hij ↦ Substructure.inclusion (cod_le_cod (S.monotone hij)))
        (fun i ↦ (S i).toEquiv)
        (fun _ _ hij _ ↦ toEquiv_inclusion_apply (S.monotone hij) _)
      ).comp
        (Equiv_iSup {
          toFun := (fun i ↦ (S i).dom)
          monotone' := monotone_dom.comp S.monotone}).symm)

@[simp]
theorem dom_partialEquivLimit : (partialEquivLimit S).dom = iSup (fun x ↦ (S x).dom) := rfl

@[simp]
theorem cod_partialEquivLimit : (partialEquivLimit S).cod = iSup (fun x ↦ (S x).cod) := rfl

@[simp]
lemma partialEquivLimit_comp_inclusion {i : ι} :
    (partialEquivLimit S).toEquiv.toEmbedding.comp (Substructure.inclusion (le_iSup _ i)) =
    (Substructure.inclusion (le_iSup _ i)).comp (S i).toEquiv.toEmbedding := by
  simp only [partialEquivLimit, Equiv.comp_toEmbedding, Embedding.comp_assoc]
  rw [Equiv_isup_symm_inclusion]
  congr

theorem le_partialEquivLimit (i : ι) : S i ≤ partialEquivLimit S :=
  ⟨le_iSup (f := fun i ↦ (S i).dom) _, by
    #adaptation_note /-- https://github.com/leanprover/lean4/pull/5020
    these two `simp` calls cannot be combined. -/
    simp only [partialEquivLimit_comp_inclusion]
    simp only [cod_partialEquivLimit, ← Embedding.comp_assoc,
      subtype_comp_inclusion]⟩

end DirectLimit

section FGEquiv

open PartialEquiv Set DirectLimit

variable (M) (N) (L)

/-- The type of equivalences between finitely generated substructures. -/
abbrev FGEquiv := {f : M ≃ₚ[L] N // f.dom.FG}

/-- Two structures `M` and `N` form an extension pair if the domain of any finitely-generated map
from `M` to `N` can be extended to include any element of `M`. -/
def IsExtensionPair : Prop := ∀ (f : L.FGEquiv M N) (m : M), ∃ g, m ∈ g.1.dom ∧ f ≤ g

variable {M N L}

theorem countable_self_fgequiv_of_countable [Countable M] :
    Countable (L.FGEquiv M M) := by
  let g : L.FGEquiv M M →
      Σ U : { S : L.Substructure M // S.FG }, U.val →[L] M :=
    fun f ↦ ⟨⟨f.val.dom, f.prop⟩, (subtype _).toHom.comp f.val.toEquiv.toHom⟩
  have g_inj : Function.Injective g := by
    intro f f' h
    ext
    let ⟨⟨dom_f, cod_f, equiv_f⟩, f_fin⟩ := f
    cases congr_arg (·.1) h
    apply PartialEquiv.ext (by rfl)
    simp only [g, Sigma.mk.inj_iff, heq_eq_eq, true_and] at h
    exact fun x hx ↦ congr_fun (congr_arg (↑) h) ⟨x, hx⟩
  have : ∀ U : { S : L.Substructure M // S.FG }, Structure.FG L U.val :=
    fun U ↦ (U.val.fg_iff_structure_fg.1 U.prop)
  exact Function.Embedding.countable ⟨g, g_inj⟩

instance inhabited_self_FGEquiv : Inhabited (L.FGEquiv M M) :=
  ⟨⟨⟨⊥, ⊥, Equiv.refl L (⊥ : L.Substructure M)⟩, fg_bot⟩⟩

instance inhabited_FGEquiv_of_IsEmpty_Constants_and_Relations
    [IsEmpty L.Constants] [IsEmpty (L.Relations 0)] [L.Structure N] :
    Inhabited (L.FGEquiv M N) :=
  ⟨⟨⟨⊥, ⊥, {
      toFun := isEmptyElim
      invFun := isEmptyElim
      left_inv := isEmptyElim
      right_inv := isEmptyElim
      map_fun' := fun {n} f x => by
        subsingleton
      map_rel' := fun {n} r x => by
        cases n
        · exact isEmptyElim r
        · exact isEmptyElim (x 0)
    }⟩, fg_bot⟩⟩

/-- Maps to the symmetric finitely-generated partial equivalence. -/
@[simps]
def FGEquiv.symm (f : L.FGEquiv M N) : L.FGEquiv N M := ⟨f.1.symm, f.1.dom_fg_iff_cod_fg.1 f.2⟩

lemma isExtensionPair_iff_cod : L.IsExtensionPair M N ↔
    ∀ (f : L.FGEquiv N M) (m : M), ∃ g, m ∈ g.1.cod ∧ f ≤ g := by
  refine Iff.intro ?_ ?_ <;>
  · intro h f m
    obtain ⟨g, h1, h2⟩ := h f.symm m
    exact ⟨g.symm, h1, monotone_symm h2⟩

/-- An alternate characterization of an extension pair is that every finitely generated partial
isomorphism can be extended to include any particular element of the domain. -/
theorem isExtensionPair_iff_exists_embedding_closure_singleton_sup :
    L.IsExtensionPair M N ↔
    ∀ (S : L.Substructure M) (_ : S.FG) (f : S ↪[L] N) (m : M),
      ∃ g : (closure L {m} ⊔ S : L.Substructure M) ↪[L] N, f =
        g.comp (Substructure.inclusion le_sup_right) := by
  refine ⟨fun h S S_FG f m => ?_, fun h ⟨f, f_FG⟩ m => ?_⟩
  · obtain ⟨⟨f', hf'⟩, mf', ff'1, ff'2⟩ := h ⟨⟨S, _, f.equivRange⟩, S_FG⟩ m
    refine ⟨f'.toEmbedding.comp (Substructure.inclusion ?_), ?_⟩
    · simp only [sup_le_iff, ff'1, closure_le, singleton_subset_iff, SetLike.mem_coe, mf',
        and_self]
    · ext ⟨x, hx⟩
      rw [Embedding.subtype_equivRange] at ff'2
      simp only [← ff'2, Embedding.comp_apply, Substructure.coe_inclusion, inclusion_mk,
        Equiv.coe_toEmbedding, coe_subtype, PartialEquiv.toEmbedding_apply]
  · obtain ⟨f', eq_f'⟩ := h f.dom f_FG f.toEmbedding m
    refine ⟨⟨⟨closure L {m} ⊔ f.dom, f'.toHom.range, f'.equivRange⟩,
      (fg_closure_singleton _).sup f_FG⟩,
      subset_closure.trans (le_sup_left : (closure L) {m} ≤ _) (mem_singleton m),
      ⟨le_sup_right, Embedding.ext (fun _ => ?_)⟩⟩
    rw [PartialEquiv.toEmbedding] at eq_f'
    simp only [Embedding.comp_apply, Substructure.coe_inclusion, Equiv.coe_toEmbedding, coe_subtype,
      Embedding.equivRange_apply, eq_f']

namespace IsExtensionPair

protected alias ⟨cod, _⟩ := isExtensionPair_iff_cod

/-- The cofinal set of finite equivalences with a given element in their domain. -/
def definedAtLeft
    (h : L.IsExtensionPair M N) (m : M) : Order.Cofinal (FGEquiv L M N) where
  carrier := {f | m ∈ f.val.dom}
  isCofinal := fun f => h f m

/-- The cofinal set of finite equivalences with a given element in their codomain. -/
def definedAtRight
    (h : L.IsExtensionPair N M) (n : N) : Order.Cofinal (FGEquiv L M N) where
  carrier := {f | n ∈ f.val.cod}
  isCofinal := fun f => h.cod f n

end IsExtensionPair

/-- For a countably generated structure `M` and a structure `N`, if any partial equivalence
between finitely generated substructures can be extended to any element in the domain,
then there exists an embedding of `M` in `N`. -/
theorem embedding_from_cg (M_cg : Structure.CG L M) (g : L.FGEquiv M N)
    (H : L.IsExtensionPair M N) :
    ∃ f : M ↪[L] N, g ≤ f.toPartialEquiv := by
  rcases M_cg with ⟨X, _, X_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  let D : X → Order.Cofinal (FGEquiv L M N) := fun x ↦ H.definedAtLeft x
  let S : ℕ →o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals g D),
      (Subtype.mono_coe _).comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := DirectLimit.partialEquivLimit S
  have _ : X ⊆ F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem g D ⟨x, hx⟩
    exact dom_le_dom
      (le_partialEquivLimit S (Encodable.encode (⟨x, hx⟩ : X) + 1)) this
  have isTop : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  exact ⟨toEmbeddingOfEqTop isTop,
        by convert (le_partialEquivLimit S 0); apply Embedding.toPartialEquiv_toEmbedding⟩

/-- For two countably generated structure `M` and `N`, if any PartialEquiv
between finitely generated substructures can be extended to any element in the domain and to
any element in the codomain, then there exists an equivalence between `M` and `N`. -/
theorem equiv_between_cg (M_cg : Structure.CG L M) (N_cg : Structure.CG L N)
    (g : L.FGEquiv M N)
    (ext_dom : L.IsExtensionPair M N)
    (ext_cod : L.IsExtensionPair N M) :
    ∃ f : M ≃[L] N, g ≤ f.toEmbedding.toPartialEquiv := by
  rcases M_cg with ⟨X, X_count, X_gen⟩
  rcases N_cg with ⟨Y, Y_count, Y_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  have _ : Countable (↑Y : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑Y : Type _) := Encodable.ofCountable _
  let D : Sum X Y → Order.Cofinal (FGEquiv L M N) := fun p ↦
    Sum.recOn p (fun x ↦ ext_dom.definedAtLeft x) (fun y ↦ ext_cod.definedAtRight y)
  let S : ℕ →o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals g D),
      (Subtype.mono_coe _).comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := @DirectLimit.partialEquivLimit L M N _ _ ℕ _ _ _ S
  have _ : X ⊆ F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem g D (Sum.inl ⟨x, hx⟩)
    exact dom_le_dom
      (le_partialEquivLimit S (Encodable.encode (Sum.inl (⟨x, hx⟩ : X)) + 1)) this
  have _ : Y ⊆ F.cod := by
    intro y hy
    have := Order.sequenceOfCofinals.encode_mem g D (Sum.inr ⟨y, hy⟩)
    exact cod_le_cod
      (le_partialEquivLimit S (Encodable.encode (Sum.inr (⟨y, hy⟩ : Y)) + 1)) this
  have dom_top : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  have cod_top : F.cod = ⊤ := by rwa [← top_le_iff, ← Y_gen, Substructure.closure_le]
  refine ⟨toEquivOfEqTop dom_top cod_top, ?_⟩
  convert le_partialEquivLimit S 0
  rw [toEquivOfEqTop_toEmbedding]
  apply Embedding.toPartialEquiv_toEmbedding

end FGEquiv

end Language

end FirstOrder
