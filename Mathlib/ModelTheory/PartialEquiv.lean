/-
Copyright (c) 2024 Gabin Kolly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Gabin Kolly
-/
import Mathlib.ModelTheory.DirectLimit
import Mathlib.Order.Ideal

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
  equiv : dom ≃[L] cod

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
  equiv := f.equiv.symm

@[simp]
theorem symm_symm (f : M ≃ₚ[L] N) : f.symm.symm = f :=
  rfl

@[simp]
theorem symm_apply (f : M ≃ₚ[L] N) (x : f.cod) : f.symm.equiv x = f.equiv.symm x :=
  rfl

instance : LE (M ≃ₚ[L] N) :=
  ⟨fun f g ↦ ∃h : f.dom ≤ g.dom,
    (subtype _).comp (g.equiv.toEmbedding.comp (Substructure.inclusion h)) =
      (subtype _).comp f.equiv.toEmbedding⟩

theorem le_def (f g : M ≃ₚ[L] N) : f ≤ g ↔ ∃ h : f.dom ≤ g.dom,
    (subtype _).comp (g.equiv.toEmbedding.comp (Substructure.inclusion h)) =
      (subtype _).comp f.equiv.toEmbedding :=
  Iff.rfl

@[gcongr] theorem dom_le_dom {f g : M ≃ₚ[L] N} : f ≤ g → f.dom ≤ g.dom := fun ⟨le, _⟩ ↦ le

@[gcongr] theorem cod_le_cod {f g : M ≃ₚ[L] N} : f ≤ g → f.cod ≤ g.cod := by
  rintro ⟨_, eq_fun⟩ n hn
  let m := f.equiv.symm ⟨n, hn⟩
  have  : ((subtype _).comp f.equiv.toEmbedding) m = n := by simp only [m, Embedding.comp_apply,
    Equiv.coe_toEmbedding, Equiv.apply_symm_apply, coeSubtype]
  rw [← this, ← eq_fun]
  simp only [Embedding.comp_apply, coe_inclusion, Equiv.coe_toEmbedding, coeSubtype,
    SetLike.coe_mem]

theorem subtype_equiv_inclusion {f g : M ≃ₚ[L] N} (h : f ≤ g) :
    (subtype _).comp (g.equiv.toEmbedding.comp (Substructure.inclusion (dom_le_dom h))) =
      (subtype _).comp f.equiv.toEmbedding := by
  let ⟨_, eq⟩ := h; exact eq

theorem equiv_inclusion {f g : M ≃ₚ[L] N} (h : f ≤ g) :
    g.equiv.toEmbedding.comp (Substructure.inclusion (dom_le_dom h)) =
      (Substructure.inclusion (cod_le_cod h)).comp f.equiv.toEmbedding := by
  rw [← (subtype _).comp_inj, subtype_equiv_inclusion h]
  rfl

theorem equiv_inclusion_apply {f g : M ≃ₚ[L] N} (h : f ≤ g) (x : f.dom) :
    g.equiv (Substructure.inclusion (dom_le_dom h) x) =
      Substructure.inclusion (cod_le_cod h) (f.equiv x) := by
  apply (subtype _).injective
  change (subtype _).comp (g.equiv.toEmbedding.comp (inclusion _)) x = _
  rw [subtype_equiv_inclusion h]
  rfl

theorem le_iff {f g : M ≃ₚ[L] N} : f ≤ g ↔
    ∃ dom_le_dom : f.dom ≤ g.dom,
    ∃ cod_le_cod : f.cod ≤ g.cod,
    ∀ x, inclusion cod_le_cod (f.equiv x) = g.equiv (inclusion dom_le_dom x) := by
  constructor
  · exact fun h ↦ ⟨dom_le_dom h, cod_le_cod h,
      by intro x; apply (subtype _).inj'; rwa [equiv_inclusion_apply]⟩
  · rintro ⟨dom_le_dom, le_cod, h_eq⟩
    rw [le_def]
    exact ⟨dom_le_dom, by ext; change subtype _ (g.equiv _) = _; rw [← h_eq]; rfl⟩

theorem le_trans (f g h : M ≃ₚ[L] N) : f ≤ g → g ≤ h → f ≤ h := by
  rintro ⟨le_fg, eq_fg⟩ ⟨le_gh, eq_gh⟩
  refine ⟨le_fg.trans le_gh, ?_⟩
  rw [← eq_fg, ← Embedding.comp_assoc (g := g.equiv.toEmbedding), ← eq_gh]
  rfl

private theorem le_refl (f : M ≃ₚ[L] N) : f ≤ f := ⟨le_rfl, rfl⟩

private theorem le_antisymm (f g : M ≃ₚ[L] N) (le_fg : f ≤ g) (le_gf : g ≤ f) : f = g := by
  let ⟨dom_f, cod_f, equiv_f⟩ := f
  cases _root_.le_antisymm (dom_le_dom le_fg) (dom_le_dom le_gf)
  cases _root_.le_antisymm (cod_le_cod le_fg) (cod_le_cod le_gf)
  convert rfl
  exact Equiv.injective_toEmbedding ((subtype _).comp_injective (subtype_equiv_inclusion le_fg))

instance : PartialOrder (M ≃ₚ[L] N) where
  le_refl := le_refl
  le_trans := le_trans
  le_antisymm := le_antisymm

@[gcongr] lemma symm_le_symm {f g : M ≃ₚ[L] N} (hfg : f ≤ g) : f.symm ≤ g.symm := by
  rw [le_iff]
  refine ⟨cod_le_cod hfg, dom_le_dom hfg, ?_⟩
  intro x
  apply g.equiv.injective
  change g.equiv (inclusion _ (f.equiv.symm x)) = g.equiv (g.equiv.symm _)
  rw [g.equiv.apply_symm_apply, (Equiv.apply_symm_apply f.equiv x).symm, f.equiv.symm_apply_apply]
  exact equiv_inclusion_apply hfg _

theorem monotone_symm : Monotone (fun (f : M ≃ₚ[L] N) ↦ f.symm) := fun _ _ => symm_le_symm

theorem symm_le_iff {f : M ≃ₚ[L] N} {g : N ≃ₚ[L] M} : f.symm ≤ g ↔ f ≤ g.symm :=
  ⟨by intro h; rw [← f.symm_symm]; exact monotone_symm h,
    by intro h; rw  [← g.symm_symm]; exact monotone_symm h⟩

theorem ext {f g : M ≃ₚ[L] N} (h_dom : f.dom = g.dom) : (∀ x : M, ∀ h : x ∈ f.dom,
    subtype _ (f.equiv ⟨x, h⟩) = subtype _ (g.equiv ⟨x, (h_dom ▸ h)⟩)) → f = g := by
  intro h
  rcases f with ⟨dom_f, cod_f, equiv_f⟩
  cases h_dom
  apply le_antisymm <;> (rw [le_def]; use (by rfl); ext ⟨x, hx⟩)
  · exact (h x hx).symm
  · exact h x hx

theorem ext_iff {f g : M ≃ₚ[L] N} : f = g ↔ ∃ h_dom : f.dom = g.dom,
    ∀ x : M, ∀ h : x ∈ f.dom,
    subtype _ (f.equiv ⟨x, h⟩) = subtype _ (g.equiv ⟨x, (h_dom ▸ h)⟩) := by
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
  let g := (subtype _).comp (f.equiv.toEmbedding.comp (A.inclusion h))
  exact {
    dom := A
    cod := g.toHom.range
    equiv := g.equivRange
  }

theorem domRestrict_le (f : M ≃ₚ[L] N) {A : L.Substructure M} (h : A ≤ f.dom) :
    f.domRestrict h ≤ f := ⟨h, rfl⟩

theorem le_domRestrict (f g : M ≃ₚ[L] N) {A : L.Substructure M} (hf : f.dom ≤ A)
    (hg : A ≤ g.dom) (hfg : f ≤ g) : f ≤ g.domRestrict hg :=
  ⟨hf, by rw [← (subtype_equiv_inclusion hfg)]; rfl⟩

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

/-- Given a partial equivalence which has the whole structure as domain,
returns the corresponding embedding. -/
def dom_top_toEmbedding {f : M ≃ₚ[L] N} (h : f.dom = ⊤) : M ↪[L] N :=
  (subtype _).comp ((h ▸ f.equiv.toEmbedding).comp Substructure.topEquiv.symm.toEmbedding)

@[simp]
theorem dom_top_toEmbedding_apply {f : M ≃ₚ[L] N} (h : f.dom = ⊤) (m : M) :
    dom_top_toEmbedding h m = f.equiv ⟨m, h.symm ▸ mem_top m⟩ := by
  rcases f with ⟨dom, cod, g⟩
  cases h
  rfl

/-- Given a partial equivalence which has the whole structure as domain and
as codomain, returns the corresponding equivalence. -/
noncomputable def dom_cod_top_toEquiv {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤)
    (h_cod : f.cod = ⊤) : M ≃[L] N :=
  (topEquiv (M := N)).comp ((h_dom ▸ h_cod ▸ f.equiv).comp (topEquiv (M := M)).symm)

@[simp]
theorem dom_cod_top_toEquiv_toEmbedding {f : M ≃ₚ[L] N} (h_dom : f.dom = ⊤)
    (h_cod : f.cod = ⊤) :
    (dom_cod_top_toEquiv h_dom h_cod).toEmbedding = dom_top_toEmbedding h_dom := by
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
    PartialEquiv.dom_top_toEmbedding (f := f.toPartialEquiv) rfl = f :=
  rfl

@[simp]
theorem toPartialEquiv_toEmbedding {f :  M ≃ₚ[L] N} (h : f.dom = ⊤) :
    (PartialEquiv.dom_top_toEmbedding h).toPartialEquiv = f := by
  rcases f with ⟨_, _, _⟩
  cases h
  apply PartialEquiv.ext
  intro _ _
  rfl; rfl

end Embedding

namespace PartialEquiv

/-- Map of a self-partial equivalence through an embedding. -/
noncomputable def map (f : M ↪[L] N) (g : M ≃ₚ[L] M) : N ≃ₚ[L] N where
  dom := g.dom.map f.toHom
  cod := g.cod.map f.toHom
  equiv := (f.substructureEquivMap g.cod).comp <|
    g.equiv.comp (f.substructureEquivMap g.dom).symm

@[simp]
theorem map_dom (f : M ↪[L] N) (g : M ≃ₚ[L] M) : (g.map f).dom = g.dom.map f.toHom := rfl

@[simp]
theorem map_cod (f : M ↪[L] N) (g : M ≃ₚ[L] M) : (g.map f).cod = g.cod.map f.toHom := rfl

theorem map_comp_comm (f : M ↪[L] N) (g : M ≃ₚ[L] M) :
    (g.map f).equiv.comp (f.substructureEquivMap g.dom) =
      (f.substructureEquivMap g.cod).comp g.equiv := by
  unfold map
  ext
  simp only [Equiv.comp_apply, Equiv.symm_apply_apply, Embedding.substructureEquivMap_apply]

theorem map_comp_comm_apply (f : M ↪[L] N) (g : M ≃ₚ[L] M) (m : g.dom) :
    (g.map f).equiv ⟨f m, g.dom.apply_coe_mem_map _ _⟩ =
      ⟨f (g.equiv m), g.cod.apply_coe_mem_map _ _⟩ := by
  exact congr_fun (congr_arg DFunLike.coe (g.map_comp_comm f)) m

theorem map_monotone (f : M ↪[L] N) : Monotone (fun g : M ≃ₚ[L] M ↦ g.map f) := by
  intro g g' h
  rw [le_iff]
  use Substructure.monotone_map (dom_le_dom h)
  use Substructure.monotone_map (cod_le_cod h)
  rintro ⟨x, hx⟩
  unfold map
  let ⟨u, u_mem, eq_u_x⟩ := mem_map.2 hx
  cases eq_u_x
  apply Subtype.coe_injective
  simp only [Embedding.coe_toHom, Equiv.comp_apply, coe_inclusion, map_coe, Set.coe_inclusion,
    Embedding.substructureEquivMap_apply, Set.inclusion_mk, EmbeddingLike.apply_eq_iff_eq]
  let ⟨_, _, eq⟩ := le_iff.1 h
  have eq := congr_arg (Subtype.val) (eq ((Equiv.symm (Embedding.substructureEquivMap f g.dom))
    { val := f u, property := (g.dom.mem_map).2 ⟨u, u_mem, rfl⟩}))
  simp only [coe_inclusion, Set.coe_inclusion] at eq
  rw [← coe_inclusion] at eq
  rw [eq, Subtype.coe_inj]
  apply congr_arg g'.equiv
  apply Subtype.coe_injective
  change subtype _ ((Equiv.symm (Embedding.substructureEquivMap f g.dom))
    (f.substructureEquivMap g.dom ⟨u, u_mem⟩)) =
    subtype _ ((Equiv.symm (Embedding.substructureEquivMap f g'.dom))
      (f.substructureEquivMap g'.dom ⟨u, dom_le_dom h u_mem⟩))
  simp only [Equiv.symm_apply_apply, coeSubtype]

theorem fg_iff {N : Type*} [L.Structure N] (f : M ≃ₚ[L] N) :
    f.dom.FG ↔ f.cod.FG := by
  rw [Substructure.fg_iff_structure_fg, f.equiv.fg_iff, Substructure.fg_iff_structure_fg]

end PartialEquiv

namespace DirectLimit

open PartialEquiv

variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
variable (S : ι →o M ≃ₚ[L] N)

instance : DirectedSystem (fun i ↦ (S i).dom) (fun _ _ h ↦
  Substructure.inclusion (dom_le_dom (S.monotone h))) where
  map_self' := fun _ _ _ ↦ rfl
  map_map' := fun _ _ _ ↦ rfl

instance : DirectedSystem (fun i ↦ (S i).cod) (fun _ _ h ↦
  Substructure.inclusion (cod_le_cod (S.monotone h))) where
  map_self' := fun _ _ _ ↦ rfl
  map_map' := fun _ _ _ ↦ rfl

/-- The limit of a directed system of PartialEquivs.-/
noncomputable def partialEquivLimit : M ≃ₚ[L] N where
  dom := iSup (fun i ↦ (S i).dom)
  cod := iSup (fun i ↦ (S i).cod)
  equiv :=
    (Equiv_iSup {
      toFun := (fun i ↦ (S i).cod)
      monotone' := monotone_cod.comp S.monotone}
    ).comp
      ((DirectLimit.equiv_lift L ι (fun i ↦ (S i).dom)
        (fun _ _ hij ↦ Substructure.inclusion (dom_le_dom (S.monotone hij)))
        (fun i ↦ (S i).cod)
        (fun _ _ hij ↦ Substructure.inclusion (cod_le_cod (S.monotone hij)))
        (fun i ↦ (S i).equiv)
        (fun _ _ hij _ ↦ equiv_inclusion_apply (S.monotone hij) _)
      ).comp
        (Equiv_iSup {
          toFun := (fun i ↦ (S i).dom)
          monotone' := monotone_dom.comp S.monotone}).symm)

@[simp]
theorem partialEquiv_limit_dom : (partialEquivLimit S).dom = iSup (fun x ↦ (S x).dom) := rfl

@[simp]
theorem partialEquiv_limit_cod : (partialEquivLimit S).cod = iSup (fun x ↦ (S x).cod) := rfl

@[simp]
lemma partialEquivLimit_comp_inclusion {i : ι} :
    (partialEquivLimit S).equiv.toEmbedding.comp (Substructure.inclusion (le_iSup _ i)) =
    (Substructure.inclusion (le_iSup _ i)).comp (S i).equiv.toEmbedding := by
  simp only [partialEquivLimit, Equiv.comp_toEmbedding, Embedding.comp_assoc]
  rw [Equiv_iSup_symm_inclusion]
  congr

theorem le_partialEquivLimit : ∀ i, S i ≤ partialEquivLimit S :=
  fun i => ⟨le_iSup (f := fun i ↦ (S i).dom) _, by
    simp only [partialEquiv_limit_cod, partialEquiv_limit_dom, partialEquivLimit_comp_inclusion, ←
      Embedding.comp_assoc, subtype_comp_inclusion]⟩

end DirectLimit

section FGPartialEquiv

open PartialEquiv Set DirectLimit

variable (M) (N) (L)

/-- The type of equivalences between finitely generated substructures. -/
abbrev FiniteEquiv := {f : M ≃ₚ[L] N // f.dom.FG}

variable {M} {N} {L}

/-- The cofinal set of finite equivalences with a given element in their domain. -/
def definedAtLeft
    (h : ∀ f : (M ≃ₚ[L] N), ∀ _ : f.dom.FG, ∀ m : M, ∃ g : (M ≃ₚ[L] N), f ≤ g ∧ m ∈ g.dom)
    (m : M) : Order.Cofinal (FiniteEquiv L M N) where
  carrier := {f | m ∈ f.val.dom}
  mem_gt := by
    intro f
    rcases h f.val f.2 m with ⟨g, f_le_g, m_in_dom⟩
    have closure_le_dom : (Substructure.closure L (f.val.dom ∪ {m})) ≤ g.dom := by
      rw [Substructure.closure_le, union_subset_iff]
      exact ⟨dom_le_dom f_le_g, singleton_subset_iff.2 m_in_dom⟩
    have closure_fg : (Substructure.closure L (f.val.dom ∪ {m})).FG := by
      rw [Substructure.closure_union, Substructure.closure_eq]
      exact Substructure.FG.sup f.property (Substructure.fg_closure_singleton _)
    use ⟨domRestrict g closure_le_dom, closure_fg⟩
    constructor
    · simp only [union_singleton]
      exact Substructure.subset_closure <| mem_insert_iff.2 <| Or.inl <| refl m
    · apply le_domRestrict
      rw [Substructure.closure_union]
      simp only [Substructure.closure_eq, ge_iff_le,
        Substructure.closure_le, singleton_subset_iff, le_sup_left]
      exact f_le_g

/-- The cofinal set of finite equivalences with a given element in their codomain. -/
def definedAtRight
  (h : ∀ f : (M ≃ₚ[L] N), ∀ _ : f.dom.FG, ∀ n : N, ∃ g : (M ≃ₚ[L] N), f ≤ g ∧ n ∈ g.cod)
  (n : N) : Order.Cofinal (FiniteEquiv L M N) where
  carrier := {f | n ∈ f.val.cod}
  mem_gt := by
    intro f
    rcases h f.val f.2 n with ⟨g, f_le_g, n_in_cod⟩
    have closure_le_cod : (Substructure.closure L (f.val.cod ∪ {n})) ≤ g.cod := by
      rw [Substructure.closure_le, union_subset_iff]
      exact ⟨cod_le_cod f_le_g, singleton_subset_iff.2 n_in_cod⟩
    have closure_fg : (Substructure.closure L (f.val.cod ∪ {n})).FG := by
      rw [Substructure.closure_union, Substructure.closure_eq]
      exact Substructure.FG.sup ((f.1.fg_iff).1 f.prop) (Substructure.fg_closure_singleton _)
    use ⟨codRestrict g closure_le_cod, (codRestrict g closure_le_cod).fg_iff.2 closure_fg⟩
    constructor
    · simp only [union_singleton]
      exact Substructure.subset_closure <| mem_insert_iff.2 <| Or.inl <| refl n
    · apply le_codRestrict
      rw [Substructure.closure_union]
      simp only [Substructure.closure_eq, ge_iff_le,
        Substructure.closure_le, singleton_subset_iff, le_sup_left]
      exact f_le_g

theorem back_iff_symm_of_forth :
    (∀ f : (M ≃ₚ[L] N), ∀ _ : f.dom.FG, ∀ n : N, ∃ g : (M ≃ₚ[L] N), f ≤ g ∧ n ∈ g.cod) ↔
    ∀ f : (N ≃ₚ[L] M), ∀ _ : f.dom.FG, ∀ n : N, ∃ g : (N ≃ₚ[L] M), f ≤ g ∧ n ∈ g.dom := by
  constructor <;>
  · intro H f fg x
    let ⟨g, g_prop⟩ := H f.symm (f.fg_iff.1 fg) x
    use g.symm
    convert g_prop
    exact symm_le_iff.symm

/-- For a countably generated structure `M` and a structure `N`, if any partial equivalence
  between finitely generated substructures can be extended to any element in the domain,
  then there exists an embedding of `M` in `N`. -/
theorem embedding_from_cg (M_cg : Structure.CG L M) (h : (M ≃ₚ[L] N)) (h_fg : h.dom.FG)
    (H : ∀ f : M ≃ₚ[L] N, ∀ _ : f.dom.FG, ∀ m : M, ∃ g : (M ≃ₚ[L] N), f ≤ g ∧ m ∈ g.dom) :
    ∃ f : M ↪[L] N, h ≤ f.toPartialEquiv := by
  rcases M_cg with ⟨X, _, X_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  let D : X → Order.Cofinal (FiniteEquiv L M N) := fun x ↦ definedAtLeft H x
  let S : ℕ →o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals ⟨h, h_fg⟩ D),
      (Subtype.mono_coe _).comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := DirectLimit.partialEquivLimit S
  have _ : X ⊆ F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem ⟨h, h_fg⟩ D ⟨x, hx⟩
    exact dom_le_dom
      (le_partialEquivLimit S (Encodable.encode (⟨x, hx⟩ : X) + 1)) this
  have isTop : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  exact ⟨dom_top_toEmbedding isTop,
        by convert (le_partialEquivLimit S 0); apply Embedding.toPartialEquiv_toEmbedding⟩

/-- For two countably generated structure `M` and `N`, if any PartialEquiv
between finitely generated substructures can be extended to any element in the domain and to
any element in the codomain, then there exists an equivalence between `M` and `N`. -/
theorem equiv_between_cg (M_cg : Structure.CG L M) (N_cg : Structure.CG L N)
    (h : (M ≃ₚ[L] N)) (h_fg : h.dom.FG)
    (ext_dom : ∀ f : M ≃ₚ[L] N, ∀ _ : f.dom.FG, ∀ m : M, ∃ g : (M ≃ₚ[L] N),
      f ≤ g ∧ m ∈ g.dom)
    (ext_cod : ∀ f : M ≃ₚ[L] N, ∀ _ : f.dom.FG, ∀ n : N, ∃ g : (M ≃ₚ[L] N),
      f ≤ g ∧ n ∈ g.cod) :
    ∃ f : M ≃[L] N, h ≤ f.toEmbedding.toPartialEquiv := by
  rcases M_cg with ⟨X, X_count, X_gen⟩
  rcases N_cg with ⟨Y, Y_count, Y_gen⟩
  have _ : Countable (↑X : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑X : Type _) := Encodable.ofCountable _
  have _ : Countable (↑Y : Type _) := by simpa only [countable_coe_iff]
  have _ : Encodable (↑Y : Type _) := Encodable.ofCountable _
  let D : Sum X Y → Order.Cofinal (FiniteEquiv L M N) := fun p ↦
    Sum.recOn p (fun x ↦ definedAtLeft ext_dom x) (fun y ↦ definedAtRight ext_cod y)
  let S : ℕ →o M ≃ₚ[L] N :=
    ⟨Subtype.val ∘ (Order.sequenceOfCofinals ⟨h, h_fg⟩ D),
      (Subtype.mono_coe _).comp (Order.sequenceOfCofinals.monotone _ _)⟩
  let F := @DirectLimit.partialEquivLimit L M N _ _ ℕ _ _ _ S
  have _ : X ⊆ F.dom := by
    intro x hx
    have := Order.sequenceOfCofinals.encode_mem ⟨h, h_fg⟩ D (Sum.inl ⟨x, hx⟩)
    exact dom_le_dom
      (le_partialEquivLimit S (Encodable.encode (Sum.inl (⟨x, hx⟩ : X)) + 1)) this
  have _ : Y ⊆ F.cod := by
    intro y hy
    have := Order.sequenceOfCofinals.encode_mem ⟨h, h_fg⟩ D (Sum.inr ⟨y, hy⟩)
    exact cod_le_cod
      (le_partialEquivLimit S (Encodable.encode (Sum.inr (⟨y, hy⟩ : Y)) + 1)) this
  have dom_top : F.dom = ⊤ := by rwa [← top_le_iff, ← X_gen, Substructure.closure_le]
  have cod_top : F.cod = ⊤ := by rwa [← top_le_iff, ← Y_gen, Substructure.closure_le]
  refine ⟨dom_cod_top_toEquiv dom_top cod_top, ?_⟩
  convert le_partialEquivLimit S 0
  rw [dom_cod_top_toEquiv_toEmbedding]
  apply Embedding.toPartialEquiv_toEmbedding

theorem Substructure.countable_self_FGPartialEquiv_of_countable [Countable M] :
    Countable { f : M ≃ₚ[L] M // f.dom.FG } := by
  let g : { f : M ≃ₚ[L] M // f.dom.FG } →
      Σ U : { S : L.Substructure M // S.FG }, U.val →[L] M :=
    fun f ↦ ⟨⟨f.val.dom, f.prop⟩, (subtype _).toHom.comp f.val.equiv.toHom⟩
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

instance inhabited_self_FGPartialEquiv : Inhabited { f : M ≃ₚ[L] M // f.dom.FG } :=
  ⟨⟨⟨⊥, ⊥, Equiv.refl L (⊥ : L.Substructure M)⟩, fg_bot⟩⟩

end FGPartialEquiv

end Language

end FirstOrder
