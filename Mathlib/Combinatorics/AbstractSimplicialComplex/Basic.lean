/-
Copyright (c) 2024 Sophie Morel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sophie Morel

Adapted from the Lean3 file of Shing Tak Lam.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Finite
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Set.Lattice
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Nat.PartENat

/-!
# Abstract Simplicial Complex

In this file, we define abstract simplicial complexes over a type `α`. An abstract simplicial
complex is collection of nonempty finsets of α (called "faces") which is closed under inclusion.

We do not require all elements of `α` to be vertices, because it is convenient in examples to be
able to define an abstract simplicial complex on a bigger type. With our definition of a
morphism of simplicial complexes, every abstract simplicial complex `K` on a type `α` is isomorphic
to an abstract simplicial complex on the type of vertices of `K`.

## Simplicial maps

We chose to model a simplicial map from `K` to `L` as a pair of maps: `vertex_map` from the
vertices of `K` to the vertices of `L`, and `face_map` from the faces of `K` to the faces of `L`.
These maps must satisfy two obvious compatibility conditions. Of course the map on vertices
determines the map of faces, but this made the manipulation of the category of simplicial
complexes simpler.

We also do not require vertex_map to be defined at elements of `α` (if `K` is a simplicial complex
on `α`) that are not vertices. This avoids a localization step when we define the category of
simplicial complexes (i.e. we do not need to identify two simplicial maps that agree on vertices),
and it also avoids trouble when defining maps between empty simplicial complexes.

## Main definitions

* `AbstractSimplicialComplex α`: An abstract simplicial complex with vertices in `α`.
* `AbstractSimplicialComplex.vertices`: The zero dimensional faces of a simplicial complex.
* `AbstractSimplicialComplex.facets`: The maximal faces of a simplicial complex.
* `SimplicialMap K L`: Simplicial maps from a simplicial complex `K` to another simplicial
complex `L`.

## Notation

* `s ∈ K` means `s` is a face of `K`.
* `K ≤ L` means that `K` is a subcomplex of `L`· That is, all faces of `K` are faces of `L`.
* `K →ₛ L` is a `SimplicialMap K L`.

## TODO (maybe)

* `Geometry.SimplicialComplex` can extend `AbstractSimplicialComplex`.
-/

--set_option autoImplicit false

open Finset

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

variable (α)

/-- Definition of an abstract simplicial complex.-/
@[ext]
structure AbstractSimplicialComplex :=
  (faces : Set (Finset α))
  (nonempty_of_mem : ∀ {s : Finset α}, s ∈ faces → s.Nonempty)
  (down_closed : ∀ {s t : Finset α}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces)

variable {α}

namespace AbstractSimplicialComplex

instance : Membership (Finset α) (AbstractSimplicialComplex α) := ⟨fun s K => s ∈ K.faces⟩

/-- Construct an abstract simplicial complex from a downward-closed set of finsets by removing the
empty face for you.-/
@[simps!] def of_erase
    (faces : Set (Finset α))
    (down_closed : ∀ {s t : Finset α}, s ∈ faces → t ⊆ s → t ∈ faces) :
    AbstractSimplicialComplex α :=
{ faces := faces \ {∅},
  nonempty_of_mem := fun h => by simp only [Set.mem_diff, Set.mem_singleton_iff] at h
                                 rw [← ne_eq, ← nonempty_iff_ne_empty] at h
                                 exact h.2
  down_closed := fun hs hts ht => ⟨down_closed hs.1 hts, by rw [nonempty_iff_ne_empty,
                                                                ne_eq] at ht; exact ht⟩}

variable (K L : AbstractSimplicialComplex α)

/-- Construct an abstract simplicial complex as a subset of a given abstract simplicial complex.-/
@[simps] def of_subcomplex
    (faces : Set (Finset α))
    (subset : faces ⊆ K.faces)
    (down_closed : ∀ {s t}, s ∈ faces → t ⊆ s → t.Nonempty → t ∈ faces) :
    AbstractSimplicialComplex α :=
{ faces := faces
  nonempty_of_mem := fun h => K.nonempty_of_mem (subset h)
  down_closed := fun hs hts ht => down_closed hs hts ht}

variable {K}

/-- Faces have nonzero cardinality.-/
lemma face_card_nonzero {s : Finset α} (hsf : s ∈ K.faces) : Finset.card s ≠ 0 :=
  let ⟨_, has⟩ := K.nonempty_of_mem hsf
  Finset.card_ne_zero_of_mem has

/-! Vertices of an abstract simplicial complex.-/

variable (K)

/-- Definition of vertices: they are the elements `a` of `α` such that `{a}` is a face.-/
def vertices : Set α := {v : α | {v} ∈ K}

lemma mem_vertices (v : α) : v ∈ K.vertices ↔ {v} ∈ K := Iff.rfl

/-- The set of vertices is equal to the union of all the faces of `K`.-/
lemma vertices_eq : K.vertices = ⋃ s ∈ K.faces, (s : Set α) := by
  ext v
  constructor
  · exact fun hv ↦ by simp only [Set.mem_iUnion, mem_coe, exists_prop]
                      exact ⟨{v}, ⟨hv, mem_singleton_self v⟩⟩
  · exact fun hv ↦ by
      simp only [Set.mem_iUnion, mem_coe, exists_prop] at hv
      let ⟨s, hsf, hsv⟩ := hv
      exact K.down_closed hsf (singleton_subset_iff.mpr hsv) (singleton_nonempty v)

/-- An element of `α` is a vertex if and only if there exists a face containing it.-/
lemma mem_vertices_iff (x : α) : x ∈ K.vertices ↔ ∃ (s : K.faces), x ∈ s.1 := by
  rw [mem_vertices]
  constructor
  · exact fun hx => by simp only [Subtype.exists, exists_prop]
                       exact ⟨{x}, ⟨hx, mem_singleton.mpr (Eq.refl x)⟩⟩
  · exact fun hx => by simp only [Subtype.exists, exists_prop] at hx
                       let ⟨s, hsf, hsx⟩ := hx
                       exact K.down_closed hsf (singleton_subset_iff.mpr hsx)
                         (singleton_nonempty _)

/-- Every face is a subset of the set of vertices.-/
lemma face_subset_vertices (s : K.faces) : ↑s.1 ⊆ K.vertices := by
  rw [vertices_eq]
  have h := Set.subset_iUnion (fun (t : K.faces) => (t : Set α)) s
  simp only [Set.iUnion_coe_set] at h
  exact h

/-! Facets of an abstract simplicial complex. -/

/-- A facet is a maximal face.-/
def facets : Set (Finset α) := {s ∈ K.faces | ∀ ⦃t⦄, t ∈ K.faces → s ⊆ t → s = t}

lemma mem_facets_iff (s : Finset α) :
    s ∈ K.facets ↔ s ∈ K.faces ∧ ∀ ⦃t : Finset α⦄, t ∈ K.faces → s ≤ t → s = t := by
  unfold facets
  simp only [Set.mem_setOf_eq, Finset.le_eq_subset]

variable {K}

/-- Every facet is a face.-/
lemma facets_subset {s : Finset α} (hsf : s ∈ K.facets) : s ∈ K.faces :=
  ((mem_facets_iff K s).mp hsf).1

/-! Lattice structure on the set of abstract simplicial complexes. -/

section Lattice

/-- Partial order instance on the type of abstract simplicial complex on `α`: we say that `K` is a
subcomplex of `L` if every face of `K` is also a face of `L`.
-/
instance instPartialOrderFaces : PartialOrder.{u} (AbstractSimplicialComplex α) :=
  PartialOrder.lift faces (fun _ _ heq => by ext; rw [heq])

variable {L}

/-- If `K` is a subcomplex of `L`, then every facet of `L` that is a face of `K` is also a
facet of `K`.-/
lemma Facets_subcomplex (hKL : K ≤ L) {s : Finset α} (hsK : s ∈ K.faces) (hsL : s ∈ L.facets) :
    s ∈ K.facets := by
  rw [mem_facets_iff, and_iff_right hsK]
  exact fun _ htK hst => hsL.2 (hKL htK) hst

/-- The `Inf` of two abstract simplicial complexes `K` and `L` on `α` is the abstract simplicial
complex whose  set of faces is the intersection of the sets of faces of `K` and `L`.-/
instance Inf : Inf.{u} (AbstractSimplicialComplex α) :=
  ⟨fun K L =>
   { faces := K.faces ⊓ L.faces
     nonempty_of_mem := fun hs => K.nonempty_of_mem hs.1
     down_closed := fun ⟨hsK, hsL⟩ hts ht => ⟨K.down_closed hsK hts ht, L.down_closed hsL hts ht⟩}⟩

/-- The set of faces of `K ⊓ L` is the intersection of the sets of faces of `K` and `L`.-/
lemma inf_faces : (K ⊓ L).faces = K.faces ⊓ L.faces := rfl

/- The `Sup` of two abstract simplicial complexes `K` and `L` on `α` is the abstract simplicial
complex whose  set of faces is the union of the sets of faces of `K` and `L`.-/
instance Sup : Sup.{u} (AbstractSimplicialComplex α) :=
  ⟨fun K L =>
  { faces := K.faces ⊔ L.faces
    nonempty_of_mem := fun hs => by cases hs with
                                  | inl h => exact K.nonempty_of_mem h
                                  | inr h => exact L.nonempty_of_mem h
    down_closed := fun hs hts ht => by cases hs with
                                     | inl hsK => exact Or.inl $ K.down_closed hsK hts ht
                                     | inr hsL => exact Or.inr $ L.down_closed hsL hts ht}⟩

/-- The set of faces of `K ⊔ L` is the union of the sets of faces of `K` and `L`.-/
lemma sup_faces : (K ⊔ L).faces = K.faces ⊔ L.faces := rfl

/- `DistribLattice` instance on the type of absract simplicial complexes on `α`.-/
instance DistribLattice : DistribLattice.{u} (AbstractSimplicialComplex α) :=
{ AbstractSimplicialComplex.instPartialOrderFaces,
  AbstractSimplicialComplex.Inf,
  AbstractSimplicialComplex.Sup with
  le_sup_inf := fun K L M => @le_sup_inf _ _ K.faces L.faces M.faces
  le_sup_left := fun K L => @le_sup_left _ _ K.faces L.faces
  le_sup_right := fun K L => @le_sup_right _ _ K.faces L.faces
  sup_le := fun K L M (hKM : K.faces ≤ M.faces) (hLM : L.faces ≤ M.faces) => sup_le hKM hLM
  inf_le_left := fun K L => @inf_le_left _ _ K.faces L.faces
  inf_le_right := fun K L => @inf_le_right _ _ K.faces L.faces
  le_inf := fun K L M (hKL : K.faces ≤ L.faces) (hKM : K.faces ≤ M.faces) => le_inf hKL hKM}

/- `Top` instance on the type of abstract simplicial complexes on `α`: this is the abstract
simplicial complex whose set of faces is the set of all nonempty finsets of `α`.-/
instance Top : Top.{u} (AbstractSimplicialComplex α) :=
  ⟨{faces := {s : Finset α | s.Nonempty}
    nonempty_of_mem := fun hs => hs
    down_closed := fun _ _ ht => ht}⟩

/-- Proof that `AbstractSimplicialComplex.Top` is the biggest abstract simplicial complex
on `α`.-/
instance OrderTop : OrderTop.{u} (AbstractSimplicialComplex α) :=
{ AbstractSimplicialComplex.Top with
  le_top := fun K _ hσ => K.nonempty_of_mem hσ
}

/-- The faces of `AbstractSimplicialComplex.Top` are all nonempty finsets of α.-/
lemma faces_top (s : Finset α) :
    s.Nonempty ↔ s ∈ (⊤ : (AbstractSimplicialComplex α)).faces := by
  constructor
  · exact fun hsne ↦ by unfold Top; simp only [Set.mem_setOf_eq]; exact hsne
  · exact fun hsf => by unfold Top at hsf; simp only [Set.mem_setOf_eq] at hsf; exact hsf

/-- Every element of `α` is a vertex of `AbstractSimplicialComplex.Top`.-/
lemma vertices_top : (⊤ : AbstractSimplicialComplex α).vertices = ⊤ := by
  rw [Set.top_eq_univ, Set.eq_univ_iff_forall]
  exact fun _ ↦ (mem_vertices _ _).mpr ⟨_, Finset.mem_singleton_self _⟩

/-- `Bot` instance on the type of abstract simplicial complexes on `α`: this is the abstract
simplicial complex whose set of faces is empty.-/
instance Bot : Bot.{u} (AbstractSimplicialComplex α) :=
  ⟨{faces := (∅ : Set (Finset α))
    nonempty_of_mem := fun hs => False.elim (Set.not_mem_empty _ hs)
    down_closed := fun hs => False.elim (Set.not_mem_empty _ hs)}⟩

/-- Proof that `AbstractSimplicialComplex.Bot` is the smallest abstract simplicial complex
on `α`.-/
instance OrderBot : OrderBot.{u} (AbstractSimplicialComplex α) :=
{ AbstractSimplicialComplex.Bot with
  bot_le := fun _ _ hσ => False.elim (Set.not_mem_empty _ hσ)}

/-- `Supset` instance on the type of abstract simplicial complexes on `α`.-/
instance SupSet : SupSet.{u} (AbstractSimplicialComplex α) :=
  ⟨fun S =>
   { faces := sSup $ faces '' S
     nonempty_of_mem := fun ⟨k, ⟨K, _, hkK⟩, h⟩ => by rw [← hkK] at h; exact K.nonempty_of_mem h
     down_closed := fun ⟨_, ⟨K, hKs, rfl⟩, hk⟩ hlk hl =>
       ⟨K.faces, ⟨K, hKs, rfl⟩, K.down_closed hk hlk hl⟩}⟩

/-- If `S` is a set of abstract simplicial complexes on `α`, then the set of faces of
`sSup S` is the union of the sets of faces of elements of `S`.-/
lemma sSup_faces (S : Set (AbstractSimplicialComplex α)) : (sSup S).faces = sSup (faces '' S) :=
  rfl

/- `Infset` instance on the type of abstract simplicial complexes on `α`.-/
instance InfSet : InfSet.{u} (AbstractSimplicialComplex α) :=
  ⟨fun S =>
  { faces := {t ∈ sInf $ faces '' S | t.Nonempty}
    nonempty_of_mem := fun ⟨_, hσ⟩ => hσ
    down_closed := fun ⟨hk₁, _⟩ hlk hl =>
      ⟨fun m ⟨M, hM, hmM⟩ ↦ by rw [← hmM]; exact M.down_closed (hk₁ M.faces ⟨M, hM, rfl⟩) hlk hl,
      hl⟩}⟩

/-- If `S` is a set of abstract simplicial complexes on `α`, then the set of faces of
`sInf S` is the set of nonempty finsets of `α` that are faces of every element of `S`.-/
lemma sInf_faces (S : Set (AbstractSimplicialComplex α)) :
    (sInf S).faces = {t ∈ sInf $ faces '' S | t.Nonempty} := rfl

/-- If `S` is a nonempty set of abstract simplicial complexes on `α`, then the set of faces of
`sInf S` is the intersection of the sets of faces of elements of `S`.-/
lemma sInf_faces_of_nonempty {S : Set (AbstractSimplicialComplex α)} (h : S.Nonempty) :
    faces (sInf S) = sInf (faces '' S) := by
  let ⟨K, hK⟩ := h
  rw [sInf_faces]
  ext σ
  simp only [Set.sInf_eq_sInter, Set.sInter_image, Set.mem_iInter, Set.mem_setOf_eq,
    and_iff_left_iff_imp]
  exact fun hσ ↦ K.nonempty_of_mem (hσ K hK)

/-- `CompleteLattice` instance on the type of abstract simplicial complexes on `α`.-/
instance CompleteLattice  : CompleteLattice.{u} (AbstractSimplicialComplex α) :=
{ AbstractSimplicialComplex.DistribLattice.toLattice,
  AbstractSimplicialComplex.SupSet.{u},
  AbstractSimplicialComplex.InfSet.{u},
  AbstractSimplicialComplex.OrderTop,
  AbstractSimplicialComplex.OrderBot with
  sInf_le := fun _ K hK _ hσ ↦
    by rw [sInf_faces_of_nonempty ⟨K, hK⟩] at hσ; exact hσ K.faces ⟨K, hK, rfl⟩
  le_sInf := fun _ K h _ hσ ↦
    ⟨fun l ⟨L, hL, hlL⟩ ↦ by rw [← hlL]; exact h _ hL hσ, K.nonempty_of_mem hσ⟩
  sSup_le := fun _ _ h _ ⟨_, ⟨_, hLs, hLw⟩, hσL⟩ ↦ by rw [← hLw] at hσL; exact h _ hLs hσL
  le_sSup := fun _ K hK _ hσ ↦ ⟨K.faces, ⟨K, hK, rfl⟩, hσ⟩
  toTop := AbstractSimplicialComplex.Top
  toBot := AbstractSimplicialComplex.Bot
  }

/-- `CompleteDistribLattice` instance on the type of abstract simplicial complexes on `α`.-/
instance CompleteDistribLattice : CompleteDistribLattice.{u} (AbstractSimplicialComplex α) :=
{ AbstractSimplicialComplex.CompleteLattice.{u} with
  iInf_sup_le_sup_sInf := by classical
                             intro K s σ hσ
                             rw [iInf, sInf_faces] at hσ
                             obtain ⟨hσ₁, hσ₂ : σ.Nonempty⟩ := hσ
                             rw [sup_faces, sInf_faces]
                             by_cases hσK : σ ∈ K
                             · exact Or.inl hσK
                             · refine Or.inr ⟨?_, hσ₂⟩
                               intro l ⟨L,hL,hlL⟩
                               rw [← hlL]
                               specialize hσ₁ (K ⊔ L).faces ⟨K ⊔ L, ⟨L, _⟩, rfl⟩
                               simp only
                               rw [iInf_eq_if, if_pos hL]
                               exact Or.resolve_left hσ₁ hσK
  inf_sSup_le_iSup_inf := by classical
                             intro K s σ hσ
                             obtain ⟨hσ₁, l, ⟨L, hL, hlL⟩, hσ₂⟩ := hσ
                             rw [iSup, sSup_faces]
                             rw [← hlL] at hσ₂
                             refine ⟨(K ⊓ L).faces, ⟨K ⊓ L, ⟨L, ?_⟩, rfl⟩, ⟨hσ₁, hσ₂⟩⟩
                             simp only
                             rw [iSup_eq_if, if_pos hL]
  }

end Lattice

/-! Finite abstract simplciial complexes.-/

variable (K)

/-- An abstract simplicial complex is finite if its set of faces is finite.-/
def FiniteComplex : Prop := Finite K.faces

variable {K L}

/-- A subcomplex of a finite abstract simplicial complex is also finite.-/
lemma finite_isLowerSet (hKL : K ≤ L) (hLfin : L.FiniteComplex) : K.FiniteComplex :=
  letI : Finite L.faces := hLfin
  Finite.Set.subset L.faces hKL

/-- A finite simplicial complex has a finite set of facets.-/
lemma finite_facets_of_finiteComplex (hfin : K.FiniteComplex) : Finite K.facets :=
  letI : Finite K.faces := hfin
  Finite.Set.subset K.faces (fun _ hsf => facets_subset hsf)

/-! Dimension-/

variable (K)

/-- The dimension of an abstract simplicial complex is the `sup` of the dimension of its faces
(where the dimension of a face `s` is `s.card - 1`). We take the `sup` in `ENat`.-/
noncomputable def dimension : ENat :=
  iSup (fun (s : K.faces) => (s.1.card : ENat)) - 1

variable {K}

/-- A finite abstract simplicial complex has finite dimension.-/
lemma Finite_implies_finite_dimension (hfin : FiniteComplex K) : dimension K ≠ ⊤ := by
  rw [← WithTop.lt_top_iff_ne_top]
  set n := Finset.sup (Set.Finite.toFinset (@Set.toFinite _ _ hfin)) (fun s => (Finset.card s))
  have hboun : dimension K ≤ ↑n := by
    unfold dimension
    refine le_trans (@tsub_le_self _ _ _ _ _ 1) (iSup_le_iff.mpr ?_)
    exact fun s ↦ by erw [WithTop.coe_le_coe, Nat.cast_le]
                     exact Finset.le_sup ((Set.Finite.mem_toFinset _).mpr s.2)
  exact lt_of_le_of_lt hboun (WithTop.coe_lt_top n)

variable (K)

/-- An abstract simplicial complex is pure if its dimension is equal to the dimension of any
of its facets.-/
def Pure : Prop :=
  ∀ ⦃s : Finset α⦄, s ∈ K.facets → ((s.card - 1 : ℕ) : ENat) = K.dimension

/-! Skeleton.-/

/-- The `d`-skeleton of an abstract simplicial complex is the subcomplex of faces of
dimension ≤ `d`, i.e. of cardinality `≤ d + 1`.-/
def skeleton (d : ℕ) : AbstractSimplicialComplex α :=
{ faces := {s ∈ K.faces | s.card ≤ d + 1}
  nonempty_of_mem := fun hs => K.nonempty_of_mem hs.1
  down_closed := fun ⟨hsK, hsd⟩ hts ht => ⟨K.down_closed hsK hts ht,
    le_trans (Finset.card_le_card hts) hsd⟩}

/-- Let `K` be an abstract simplicial complex and `s` be a face of `K`. The link of `s` in `K`
is the abstract simplicial complex with faces the faces `t` of `K` such that `s ⊓ t` is empty
and `s ⊔ t` is a face of `K`.  We define it for an arbitrary finset `s` of `α`.-/
def link [DecidableEq α] (s : Finset α) : AbstractSimplicialComplex α :=
{ faces := {t ∈ K.faces | s ∩ t = ∅ ∧ s ∪ t ∈ K}
  nonempty_of_mem := fun hσ => K.nonempty_of_mem hσ.1
  down_closed := fun ⟨hσK, hσint, hσunion⟩ hτσ hτ => ⟨K.down_closed hσK hτσ hτ,
    eq_bot_iff.2 $ le_trans (Finset.inter_subset_inter_left hτσ) (eq_bot_iff.1 hσint),
    K.down_closed hσunion (Finset.union_subset_union (Finset.Subset.refl _) hτσ)
      (by rw [Finset.nonempty_iff_ne_empty, ne_eq, Finset.union_eq_empty, not_and_or, ← ne_eq,
              ← ne_eq, ← Finset.nonempty_iff_ne_empty, ← Finset.nonempty_iff_ne_empty]
          exact Or.inr hτ)⟩}

end AbstractSimplicialComplex

/-! Simpliciap maps.-/

open AbstractSimplicialComplex

variable {K : AbstractSimplicialComplex α} {L : AbstractSimplicialComplex β}
  {M : AbstractSimplicialComplex γ}

variable (K L)

/-- A simplicial map from `K` to `L` is a pair of maps, `vertex_map : K.vertices → L.vertices` and
`face_map : K.faces → L.faces`, with the obvious compatibility conditions.-/
@[ext]
structure SimplicialMap :=
  (vertex_map : K.vertices → L.vertices)
  (face_map : K.faces → L.faces)
  (vertex_face : ∀ (a : K.vertices),
    face_map ⟨{a.1}, a.2⟩ = ⟨{(vertex_map a).1}, (vertex_map a).2⟩)
  (face_vertex : ∀ (s : K.faces) (b : β),
    b ∈ (face_map s).1 ↔ (∃ (a : α) (has : a ∈ s.1),
    (vertex_map ⟨a, face_subset_vertices K s has⟩).1 = b))

notation:100 K:100 " →ₛ " L:100 => SimplicialMap K L

variable {K L}

namespace SimplicialMap

/-- Two simplicial maps with the same `vertex_map` (i.e. that are equal on vertices) are equal.-/
@[simp]
lemma ext_vertex  (f g : SimplicialMap K L) : f.vertex_map = g.vertex_map → f = g :=
  fun heq ↦ SimplicialMap.ext _ _ heq (by ext s a; rw [f.face_vertex, g.face_vertex, heq])

/-- If `f` is a map from `α` to `β` such that, for every face `s` of `K`, `f s` is a face of `L`,
then `f` defines a simplicial map from `K` to `L`.-/
noncomputable def ofMap [DecidableEq β] {f : α → β}
    (hf : ∀ (s : Finset α), s ∈ K.faces → Finset.image f s ∈ L.faces) : K →ₛ L
    where
  vertex_map a := ⟨f a.1, hf {a.1} ((K.mem_vertices _).mp a.2)⟩
  face_map s := ⟨Finset.image f s, hf s.1 s.2⟩
  vertex_face _ := by simp only [Finset.image_singleton]
  face_vertex _ _ := by simp only [Finset.mem_image, exists_prop]

/-- If `f` is a map from `α` to `β` such that, for every face `s` of `K`, `f s` is a face of `L`,
then the `vertex_map` of the simplicial map defined by `f` (cf. `SimplicialMap.ofMap`) is the
restriction of `f` to the set of vertices of `K`.-/
lemma ofMap_vertex_map [DecidableEq β] {f : α → β}
    (hf : ∀ (s : Finset α), s ∈ K.faces → Finset.image f s ∈ L.faces) (a : K.vertices) :
    ((ofMap hf).vertex_map a).1 = f a.1 := by
  unfold ofMap
  simp only

/-- If `f` is any map from a type `α` to a type `β`, it defines a simplicial map between the
maximal abstract simplicial complexes on `α` and `β`.-/
noncomputable def mapTop [DecidableEq β] (f : α → β) :
    SimplicialMap (⊤ : AbstractSimplicialComplex α) (⊤ : AbstractSimplicialComplex β) where
  vertex_map a := ⟨f a.1, by simp only [vertices_top, Set.top_eq_univ, Set.mem_univ]⟩
  face_map s := ⟨Finset.image f s.1, (faces_top _).mp ((image_nonempty (f := f)).mpr
                 ((faces_top _).mpr s.2))⟩
  vertex_face _ := by simp only [Finset.image_singleton]
  face_vertex _ := by simp only [mem_image, exists_prop, implies_true]

/-- Composition of simplicial maps: we compose `vertex_map` and `face_map` in the obvious way.-/
def comp (g : L →ₛ M) (f : K →ₛ L) : K →ₛ M where
  vertex_map := g.vertex_map ∘ f.vertex_map
  face_map := g.face_map ∘ f.face_map
  vertex_face a := by
    simp only [Function.comp_apply, f.vertex_face a, g.vertex_face (f.vertex_map a)]
  face_vertex s c := by
    simp only [Function.comp_apply, g.face_vertex, f.face_vertex]
    constructor
    · intro ⟨b, ⟨a, has, hab⟩, hbc⟩
      existsi a, has
      have hav : a ∈ K.vertices := face_subset_vertices K s has
      have hbv : b ∈ L.vertices := by rw [← hab]; exact (f.vertex_map ⟨a, hav⟩).2
      have hab' : f.vertex_map ⟨a, hav⟩ = ⟨b, hbv⟩ := by rw [← SetCoe.ext_iff]; simp only [hab]
      rw [hab', hbc]
    · intro ⟨a, has, hac⟩
      existsi (f.vertex_map ⟨a, face_subset_vertices K s has⟩).1
      simp only [Subtype.coe_eta, exists_prop]
      exact ⟨⟨a, has, by simp only⟩, by simp only [hac]⟩

variable (K)

/-- The identity as a simplicial map.-/
noncomputable def id : K →ₛ K where
  vertex_map a := a
  face_map s := s
  vertex_face _ := by simp only
  face_vertex _ _ := by simp only [exists_prop, exists_eq_right]

/- The identity of α defines the identity of the infinite simplex on α.-/
lemma MapSimplex.id : MapSimplex (fun x => x) = SimplicialMap.id (Simplex α) := by
  apply SimplicialMap.ext_vertex
  unfold MapSimplex SimplicialMap.id
  simp only

/- Sending a map of types to the corresponding map of infinite simplices preserves composition.-/
lemma MapSimplex.comp (f : α → β) (g : β → γ) : (MapSimplex g).comp (MapSimplex f) = MapSimplex (g ∘ f) := by
  apply SimplicialMap.ext_vertex
  ext ⟨a, hav⟩
  unfold MapSimplex SimplicialMap.comp
  simp only [Function.comp_apply]


end SimplicialMap



/- Subcomplex generated by a set of faces, or by one face.-/

namespace AbstractSimplicialComplex

variable {α : Type u}

/- Subcomplex of a complex K generated by a set F of finsets of α : we only keep the faces contained in some
element of F.-/
def SubcomplexGenerated (K : AbstractSimplicialComplex α) (F : Set (Finset α)) : AbstractSimplicialComplex α :=
of_subcomplex K {s : Finset α | s ∈ K.faces ∧ ∃ (t : Finset α), t ∈ F ∧ s ⊆ t} (by simp only [Set.sep_subset])
(by intro s t hs hts htne
    constructor
    · exact K.down_closed hs.1 hts htne
    · match hs.2 with
      | ⟨u, ⟨huF, hsu⟩⟩ => exact ⟨u, ⟨huF, subset_trans hts hsu⟩⟩)



lemma SubcomplexGenerated_mem (K : AbstractSimplicialComplex α) (F : Set (Finset α)) (s : Finset α) :
s ∈ SubcomplexGenerated K F ↔ s ∈ K.faces ∧ ∃ (t : F), s ⊆ t := by
  unfold SubcomplexGenerated
  change s ∈ {s | s ∈ K.faces ∧ ∃ (t : Finset α), t ∈ F ∧  s ⊆ t} ↔ _
  simp only [Set.mem_setOf_eq, Subtype.exists, exists_prop]


/- The boundary of a simplex of K is the set of subfaces of s that are different from s.-/
def Boundary {K : AbstractSimplicialComplex α} (s : K.faces) : AbstractSimplicialComplex α :=
of_subcomplex K {t : Finset α | t ∈ K.faces ∧ t ⊂ s} (by simp only [Set.sep_subset])
(by intro t u ht hut hune
    constructor
    · exact K.down_closed ht.1 hut hune
    · exact lt_of_le_of_lt hut ht.2)

lemma Boundary_mem {K : AbstractSimplicialComplex α} (s : K.faces) (t : Finset α):
t ∈ (Boundary s).faces ↔ t ∈ K.faces ∧ t ⊆ s.1 ∧ t ≠ s.1 := by
  unfold Boundary
  change t ∈ {t : Finset α | t ∈ K.faces ∧ t ⊂ s} ↔ _
  simp only [Set.mem_setOf_eq, ne_eq, and_congr_right_iff]
  exact fun _ => by rw [Finset.ssubset_iff_subset_ne]



/- The boundary of a face is a finite complex.-/
lemma BoundaryFinite {K : AbstractSimplicialComplex α} (s : K.faces) : FiniteComplex (Boundary s) := by
  apply @Finite.of_injective (Boundary s).faces {u : Set α | u ⊆ ↑s.1} (Set.finite_coe_iff.mpr (@Set.Finite.finite_subsets α ↑s.1 (Finset.finite_toSet _)))
    (fun (t : (Boundary s).faces) => by have ht := t.2
                                        rw [Boundary_mem, ← Finset.coe_subset] at ht
                                        exact (⟨↑t.1, ht.2.1⟩ : {u : Set α | u ⊆ ↑s.1}))
  intro t u heq
  simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.mk.injEq, Finset.coe_inj] at heq
  rw [SetCoe.ext_iff] at heq
  exact heq

end AbstractSimplicialComplex
