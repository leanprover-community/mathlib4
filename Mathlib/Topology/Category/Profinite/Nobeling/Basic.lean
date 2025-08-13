/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.SetTheory.Ordinal.Basic
import Mathlib.Topology.Category.Profinite.Product
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Preliminaries for Nöbeling's theorem

This file constructs basic objects and results concerning them that are needed in the proof of
Nöbeling's theorem, which is in `Mathlib/Topology/Category/Profinite/Nobeling/Induction.lean`.
See the section docstrings for more information.

## Proof idea

We follow the proof of theorem 5.4 in [scholze2019condensed], in which the idea is to embed `S` in
a product of `I` copies of `Bool` for some sufficiently large `I`, and then to choose a
well-ordering on `I` and use ordinal induction over that well-order. Here we can let `I` be
the set of clopen subsets of `S` since `S` is totally separated.

The above means it suffices to prove the following statement: For a closed subset `C` of `I → Bool`,
the `ℤ`-module `LocallyConstant C ℤ` is free.

For `i : I`, let `e C i : LocallyConstant C ℤ` denote the map `fun f ↦ (if f.val i then 1 else 0)`.

The basis will consist of products `e C iᵣ * ⋯ * e C i₁` with `iᵣ > ⋯ > i₁` which cannot be written
as linear combinations of lexicographically smaller products. We call this set `GoodProducts C`.

What is proved by ordinal induction (in
`Mathlib/Topology/Category/Profinite/Nobeling/ZeroLimit.lean` and
`Mathlib/Topology/Category/Profinite/Nobeling/Successor.lean`) is that this set is linearly
independent. The fact that it spans is proved directly in
`Mathlib/Topology/Category/Profinite/Nobeling/Span.lean`.

## References

- [scholze2019condensed], Theorem 5.4.
-/

open CategoryTheory ContinuousMap Limits Opposite Submodule

universe u

namespace Profinite.NobelingProof

variable {I : Type u} (C : Set (I → Bool))

section Projections
/-!
## Projection maps

The purpose of this section is twofold.

Firstly, in the proof that the set `GoodProducts C` spans the whole module `LocallyConstant C ℤ`,
we need to project `C` down to finite discrete subsets and write `C` as a cofiltered limit of those.

Secondly, in the inductive argument, we need to project `C` down to "smaller" sets satisfying the
inductive hypothesis.

In this section we define the relevant projection maps and prove some compatibility results.

### Main definitions

* Let `J : I → Prop`. Then `Proj J : (I → Bool) → (I → Bool)` is the projection mapping everything
  that satisfies `J i` to itself, and everything else to `false`.

* The image of `C` under `Proj J` is denoted `π C J` and the corresponding map `C → π C J` is called
  `ProjRestrict`. If `J` implies `K` we have a map `ProjRestricts : π C K → π C J`.

* `spanCone_isLimit` establishes that when `C` is compact, it can be written as a limit of its
  images under the maps `Proj (· ∈ s)` where `s : Finset I`.
-/

variable (J K L : I → Prop) [∀ i, Decidable (J i)] [∀ i, Decidable (K i)] [∀ i, Decidable (L i)]

/--
The projection mapping everything that satisfies `J i` to itself, and everything else to `false`
-/
def Proj : (I → Bool) → (I → Bool) :=
  fun c i ↦ if J i then c i else false

@[simp]
theorem continuous_proj :
    Continuous (Proj J : (I → Bool) → (I → Bool)) := by
  dsimp +unfoldPartialApp [Proj]
  apply continuous_pi
  intro i
  split
  · apply continuous_apply
  · apply continuous_const

/-- The image of `Proj π J` -/
def π : Set (I → Bool) := (Proj J) '' C

/-- The restriction of `Proj π J` to a subset, mapping to its image. -/
@[simps!]
def ProjRestrict : C → π C J :=
  Set.MapsTo.restrict (Proj J) _ _ (Set.mapsTo_image _ _)

@[simp]
theorem continuous_projRestrict : Continuous (ProjRestrict C J) :=
  Continuous.restrict _ (continuous_proj _)

theorem proj_eq_self {x : I → Bool} (h : ∀ i, x i ≠ false → J i) : Proj J x = x := by
  ext i
  simp only [Proj, ite_eq_left_iff]
  contrapose!
  simpa only [ne_comm] using h i

theorem proj_prop_eq_self (hh : ∀ i x, x ∈ C → x i ≠ false → J i) : π C J = C := by
  ext x
  refine ⟨fun ⟨y, hy, h⟩ ↦ ?_, fun h ↦ ⟨x, h, ?_⟩⟩
  · rwa [← h, proj_eq_self]; exact (hh · y hy)
  · rw [proj_eq_self]; exact (hh · x h)

theorem proj_comp_of_subset (h : ∀ i, J i → K i) : (Proj J ∘ Proj K) =
    (Proj J : (I → Bool) → (I → Bool)) := by
  ext x i; dsimp [Proj]; aesop

theorem proj_eq_of_subset (h : ∀ i, J i → K i) : π (π C K) J = π C J := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := h
    refine ⟨z, hz, (?_ : _ = (Proj J ∘ Proj K) z)⟩
    rw [proj_comp_of_subset J K h]
  · obtain ⟨y, hy, rfl⟩ := h
    dsimp [π]
    rw [← Set.image_comp]
    refine ⟨y, hy, ?_⟩
    rw [proj_comp_of_subset J K h]

variable {J K L}

/-- A variant of `ProjRestrict` with domain of the form `π C K` -/
@[simps!]
def ProjRestricts (h : ∀ i, J i → K i) : π C K → π C J :=
  Homeomorph.setCongr (proj_eq_of_subset C J K h) ∘ ProjRestrict (π C K) J

@[simp]
theorem continuous_projRestricts (h : ∀ i, J i → K i) : Continuous (ProjRestricts C h) :=
  Continuous.comp (Homeomorph.continuous _) (continuous_projRestrict _ _)

theorem surjective_projRestricts (h : ∀ i, J i → K i) : Function.Surjective (ProjRestricts C h) :=
  (Homeomorph.surjective _).comp (Set.surjective_mapsTo_image_restrict _ _)

variable (J) in
theorem projRestricts_eq_id : ProjRestricts C (fun i (h : J i) ↦ h) = id := by
  ext ⟨x, y, hy, rfl⟩ i
  simp +contextual only [π, Proj, ProjRestricts_coe, id_eq, if_true]

theorem projRestricts_eq_comp (hJK : ∀ i, J i → K i) (hKL : ∀ i, K i → L i) :
    ProjRestricts C hJK ∘ ProjRestricts C hKL = ProjRestricts C (fun i ↦ hKL i ∘ hJK i) := by
  ext x i
  simp only [π, Proj, Function.comp_apply, ProjRestricts_coe]
  aesop

theorem projRestricts_comp_projRestrict (h : ∀ i, J i → K i) :
    ProjRestricts C h ∘ ProjRestrict C K = ProjRestrict C J := by
  ext x i
  simp only [π, Proj, Function.comp_apply, ProjRestricts_coe, ProjRestrict_coe]
  aesop

variable (J)

/-- The objectwise map in the isomorphism `spanFunctor ≅ Profinite.indexFunctor`. -/
def iso_map : C(π C J, (IndexFunctor.obj C J)) :=
  ⟨fun x ↦ ⟨fun i ↦ x.val i.val, by
    rcases x with ⟨x, y, hy, rfl⟩
    refine ⟨y, hy, ?_⟩
    ext ⟨i, hi⟩
    simp [precomp, Proj, hi]⟩, by
    refine Continuous.subtype_mk (continuous_pi fun i ↦ ?_) _
    exact (continuous_apply i.val).comp continuous_subtype_val⟩

lemma iso_map_bijective : Function.Bijective (iso_map C J) := by
  refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
  · ext i
    rw [Subtype.ext_iff] at h
    by_cases hi : J i
    · exact congr_fun h ⟨i, hi⟩
    · rcases a with ⟨_, c, hc, rfl⟩
      rcases b with ⟨_, d, hd, rfl⟩
      simp only [Proj, if_neg hi]
  · refine ⟨⟨fun i ↦ if hi : J i then a.val ⟨i, hi⟩ else false, ?_⟩, ?_⟩
    · rcases a with ⟨_, y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · ext i
      exact dif_pos i.prop

variable {C}

/--
For a given compact subset `C` of `I → Bool`, `spanFunctor` is the functor from the poset of finsets
of `I` to `Profinite`, sending a finite subset set `J` to the image of `C` under the projection
`Proj J`.
-/
noncomputable
def spanFunctor [∀ (s : Finset I) (i : I), Decidable (i ∈ s)] (hC : IsCompact C) :
    (Finset I)ᵒᵖ ⥤ Profinite.{u} where
  obj s := @Profinite.of (π C (· ∈ (unop s))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (continuous_proj _)) _ _
  map h := @CompHausLike.ofHom _ _ _ (_) (_) (_) (_) (_) (_) (_) (_)
    ⟨(ProjRestricts C (leOfHom h.unop)), continuous_projRestricts _ _⟩
  map_id J := by simp only [projRestricts_eq_id C (· ∈ (unop J))]; rfl
  map_comp _ _ := by rw [← CompHausLike.ofHom_comp]; congr; dsimp; rw [projRestricts_eq_comp]

/-- The limit cone on `spanFunctor` with point `C`. -/
noncomputable
def spanCone [∀ (s : Finset I) (i : I), Decidable (i ∈ s)] (hC : IsCompact C) :
    Cone (spanFunctor hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π :=
  { app := fun s ↦ TopCat.ofHom ⟨ProjRestrict C (· ∈ unop s), continuous_projRestrict _ _⟩
    naturality := by
      intro X Y h
      simp only [Functor.const_obj_obj,
        Functor.const_obj_map, Category.id_comp, ← projRestricts_comp_projRestrict C
        (leOfHom h.unop)]
      rfl }

/-- `spanCone` is a limit cone. -/
noncomputable
def spanCone_isLimit [∀ (s : Finset I) (i : I), Decidable (i ∈ s)] (hC : IsCompact C) :
    CategoryTheory.Limits.IsLimit (spanCone hC) := by
  refine (IsLimit.postcomposeHomEquiv (NatIso.ofComponents
    (fun s ↦ (CompHausLike.isoOfBijective _ (iso_map_bijective C (· ∈ unop s)))) ?_) (spanCone hC))
    (IsLimit.ofIsoLimit (indexCone_isLimit hC) (Cones.ext (Iso.refl _) ?_))
  · intro ⟨s⟩ ⟨t⟩ ⟨⟨⟨f⟩⟩⟩
    ext x
    have : iso_map C (· ∈ t) ∘ ProjRestricts C f = IndexFunctor.map C f ∘ iso_map C (· ∈ s) := by
      ext _ i; exact dif_pos i.prop
    exact congr_fun this x
  · intro ⟨s⟩
    ext x
    have : iso_map C (· ∈ s) ∘ ProjRestrict C (· ∈ s) = IndexFunctor.π_app C (· ∈ s) := by
      ext _ i; exact dif_pos i.prop
    erw [← this]
    rfl

end Projections

section Products
/-!
## Defining the basis

Our proposed basis consists of products `e C iᵣ * ⋯ * e C i₁` with `iᵣ > ⋯ > i₁` which cannot be
written as linear combinations of lexicographically smaller products. See below for the definition
of `e`.

### Main definitions

* For `i : I`, we let `e C i : LocallyConstant C ℤ` denote the map
  `fun f ↦ (if f.val i then 1 else 0)`.

* `Products I` is the type of lists of decreasing elements of `I`, so a typical element is
  `[i₁, i₂,..., iᵣ]` with `i₁ > i₂ > ... > iᵣ`.

* `Products.eval C` is the `C`-evaluation of a list. It takes a term `[i₁, i₂,..., iᵣ] : Products I`
  and returns the actual product `e C i₁ ··· e C iᵣ : LocallyConstant C ℤ`.

* `GoodProducts C` is the set of `Products I` such that their `C`-evaluation cannot be written as
  a linear combination of evaluations of lexicographically smaller lists.

### Main results

* `Products.evalFacProp` and `Products.evalFacProps` establish the fact that `Products.eval`
  interacts nicely with the projection maps from the previous section.

* `GoodProducts.span_iff_products`: the good products span `LocallyConstant C ℤ` iff all the
  products span `LocallyConstant C ℤ`.
-/

/--
`e C i` is the locally constant map from `C : Set (I → Bool)` to `ℤ` sending `f` to 1 if
`f.val i = true`, and 0 otherwise.
-/
def e (i : I) : LocallyConstant C ℤ where
  toFun := fun f ↦ (if f.val i then 1 else 0)
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_continuous]
    exact (continuous_of_discreteTopology (f := fun (a : Bool) ↦ (if a then (1 : ℤ) else 0))).comp
      ((continuous_apply i).comp continuous_subtype_val)

variable [LinearOrder I]

/--
`Products I` is the type of lists of decreasing elements of `I`, so a typical element is
`[i₁, i₂, ...]` with `i₁ > i₂ > ...`. We order `Products I` lexicographically, so `[] < [i₁, ...]`,
and `[i₁, i₂, ...] < [j₁, j₂, ...]` if either `i₁ < j₁`, or `i₁ = j₁` and `[i₂, ...] < [j₂, ...]`.

Terms `m = [i₁, i₂, ..., iᵣ]` of this type will be used to represent products of the form
`e C i₁ ··· e C iᵣ : LocallyConstant C ℤ` . The function associated to `m` is `m.eval`.
-/
def Products (I : Type*) [LinearOrder I] := {l : List I // l.Chain' (· > ·)}

namespace Products

instance : LinearOrder (Products I) :=
  inferInstanceAs (LinearOrder {l : List I // l.Chain' (· > ·)})

@[simp]
theorem lt_iff_lex_lt (l m : Products I) : l < m ↔ List.Lex (· < ·) l.val m.val := by
  simp

instance [WellFoundedLT I] : WellFoundedLT (Products I) := by
  have : (· < · : Products I → _ → _) = (fun l m ↦ List.Lex (· < ·) l.val m.val) := by
    ext; exact lt_iff_lex_lt _ _
  rw [WellFoundedLT, this]
  dsimp [Products]
  rw [(by rfl : (· > · : I → _) = flip (· < ·))]
  infer_instance

/-- The evaluation `e C i₁ ··· e C iᵣ : C → ℤ` of a formal product `[i₁, i₂, ..., iᵣ]`. -/
def eval (l : Products I) := (l.1.map (e C)).prod

/--
The predicate on products which we prove picks out a basis of `LocallyConstant C ℤ`. We call such a
product "good".
-/
def isGood (l : Products I) : Prop :=
  l.eval C ∉ Submodule.span ℤ ((Products.eval C) '' {m | m < l})

theorem rel_head!_of_mem [Inhabited I] {i : I} {l : Products I} (hi : i ∈ l.val) :
    i ≤ l.val.head! :=
  List.Sorted.le_head! (List.chain'_iff_pairwise.mp l.prop) hi

theorem head!_le_of_lt [Inhabited I] {q l : Products I} (h : q < l) (hq : q.val ≠ []) :
    q.val.head! ≤ l.val.head! :=
  List.head!_le_of_lt l.val q.val h hq

end Products

/-- The set of good products. -/
def GoodProducts := {l : Products I | l.isGood C}

namespace GoodProducts

/-- Evaluation of good products. -/
def eval (l : {l : Products I // l.isGood C}) : LocallyConstant C ℤ :=
  Products.eval C l.1

theorem injective : Function.Injective (eval C) := by
  intro ⟨a, ha⟩ ⟨b, hb⟩ h
  dsimp [eval] at h
  by_contra! hne
  cases hne.lt_or_gt with
  | inl h' => apply hb; rw [← h]; exact Submodule.subset_span ⟨a, h', rfl⟩
  | inr h' => apply ha; rw [h]; exact Submodule.subset_span ⟨b, h', rfl⟩

/-- The image of the good products in the module `LocallyConstant C ℤ`. -/
def range := Set.range (GoodProducts.eval C)

/-- The type of good products is equivalent to its image. -/
noncomputable
def equiv_range : GoodProducts C ≃ range C :=
  Equiv.ofInjective (eval C) (injective C)

theorem equiv_toFun_eq_eval : (equiv_range C).toFun = Set.rangeFactorization (eval C) := rfl

theorem linearIndependent_iff_range : LinearIndependent ℤ (GoodProducts.eval C) ↔
    LinearIndependent ℤ (fun (p : range C) ↦ p.1) := by
  rw [← @Set.rangeFactorization_eq _ _ (GoodProducts.eval C), ← equiv_toFun_eq_eval C]
  exact linearIndependent_equiv (equiv_range C)

end GoodProducts

namespace Products

theorem eval_eq (l : Products I) (x : C) :
    l.eval C x = if ∀ i, i ∈ l.val → (x.val i = true) then 1 else 0 := by
  change LocallyConstant.evalMonoidHom x (l.eval C) = _
  rw [eval, map_list_prod]
  split_ifs with h
  · simp only [List.map_map]
    apply List.prod_eq_one
    simp only [List.mem_map, Function.comp_apply]
    rintro _ ⟨i, hi, rfl⟩
    exact if_pos (h i hi)
  · simp only [List.map_map, List.prod_eq_zero_iff, List.mem_map, Function.comp_apply]
    push_neg at h
    convert h with i
    dsimp [LocallyConstant.evalMonoidHom, e]
    simp only [ite_eq_right_iff, one_ne_zero]

theorem evalFacProp {l : Products I} (J : I → Prop)
    (h : ∀ a, a ∈ l.val → J a) [∀ j, Decidable (J j)] :
    l.eval (π C J) ∘ ProjRestrict C J = l.eval C := by
  ext x
  dsimp [ProjRestrict]
  rw [Products.eval_eq, Products.eval_eq]
  simp +contextual [h, Proj]

theorem evalFacProps {l : Products I} (J K : I → Prop)
    (h : ∀ a, a ∈ l.val → J a) [∀ j, Decidable (J j)] [∀ j, Decidable (K j)]
    (hJK : ∀ i, J i → K i) :
    l.eval (π C J) ∘ ProjRestricts C hJK = l.eval (π C K) := by
  have : l.eval (π C J) ∘ Homeomorph.setCongr (proj_eq_of_subset C J K hJK) =
      l.eval (π (π C K) J) := by
    ext; simp [Homeomorph.setCongr, Products.eval_eq]
  rw [ProjRestricts, ← Function.comp_assoc, this, ← evalFacProp (π C K) J h]

theorem prop_of_isGood {l : Products I} (J : I → Prop) [∀ j, Decidable (J j)]
    (h : l.isGood (π C J)) : ∀ a, a ∈ l.val → J a := by
  intro i hi
  by_contra h'
  apply h
  suffices eval (π C J) l = 0 by
    rw [this]
    exact Submodule.zero_mem _
  ext ⟨_, _, _, rfl⟩
  rw [eval_eq, if_neg fun h ↦ ?_, LocallyConstant.zero_apply]
  simpa [Proj, h'] using h i hi

end Products

/-- The good products span `LocallyConstant C ℤ` if and only all the products do. -/
theorem GoodProducts.span_iff_products [WellFoundedLT I] :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval C)) ↔
      ⊤ ≤ Submodule.span ℤ (Set.range (Products.eval C)) := by
  refine ⟨fun h ↦ le_trans h (span_mono (fun a ⟨b, hb⟩ ↦ ⟨b.val, hb⟩)), fun h ↦ le_trans h ?_⟩
  rw [span_le]
  rintro f ⟨l, rfl⟩
  let L : Products I → Prop := fun m ↦ m.eval C ∈ span ℤ (Set.range (GoodProducts.eval C))
  suffices L l by assumption
  apply IsWellFounded.induction (· < · : Products I → Products I → Prop)
  intro l h
  dsimp
  by_cases hl : l.isGood C
  · apply subset_span
    exact ⟨⟨l, hl⟩, rfl⟩
  · simp only [Products.isGood, not_not] at hl
    suffices Products.eval C '' {m | m < l} ⊆ span ℤ (Set.range (GoodProducts.eval C)) by
      rw [← span_le] at this
      exact this hl
    rintro a ⟨m, hm, rfl⟩
    exact h m hm

end Products

variable [LinearOrder I] [WellFoundedLT I]

section Ordinal
/-!
## Relating elements of the well-order `I` with ordinals

We choose a well-ordering on `I`. This amounts to regarding `I` as an ordinal, and as such it
can be regarded as the set of all strictly smaller ordinals, allowing to apply ordinal induction.

### Main definitions

* `ord I i` is the term `i` of `I` regarded as an ordinal.

* `term I ho` is a sufficiently small ordinal regarded as a term of `I`.

* `contained C o` is a predicate saying that `C` is "small" enough in relation to the ordinal `o`
  to satisfy the inductive hypothesis.

* `P I` is the predicate on ordinals about linear independence of good products, which the rest of
  this file is spent on proving by induction.
-/

variable (I)

/-- A term of `I` regarded as an ordinal. -/
def ord (i : I) : Ordinal := Ordinal.typein ((· < ·) : I → I → Prop) i

/-- An ordinal regarded as a term of `I`. -/
noncomputable
def term {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I → I → Prop)) : I :=
  Ordinal.enum ((· < ·) : I → I → Prop) ⟨o, ho⟩

variable {I}

theorem term_ord_aux {i : I} (ho : ord I i < Ordinal.type ((· < ·) : I → I → Prop)) :
    term I ho = i := by
  simp only [term, ord, Ordinal.enum_typein]

@[simp]
theorem ord_term_aux {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I → I → Prop)) :
    ord I (term I ho) = o := by
  simp only [ord, term, Ordinal.typein_enum]

theorem ord_term {o : Ordinal} (ho : o < Ordinal.type ((· < ·) : I → I → Prop)) (i : I) :
    ord I i = o ↔ term I ho = i := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · subst h
    exact term_ord_aux ho
  · subst h
    exact ord_term_aux ho

/-- A predicate saying that `C` is "small" enough to satisfy the inductive hypothesis. -/
def contained (o : Ordinal) : Prop := ∀ f, f ∈ C → ∀ (i : I), f i = true → ord I i < o

variable (I) in
/--
The predicate on ordinals which we prove by induction, see `GoodProducts.P0`,
`GoodProducts.Plimit` and `GoodProducts.linearIndependentAux` in the section `Induction` below
-/
def P (o : Ordinal) : Prop :=
  o ≤ Ordinal.type (· < · : I → I → Prop) →
  (∀ (C : Set (I → Bool)), IsClosed C → contained C o →
    LinearIndependent ℤ (GoodProducts.eval C))

theorem Products.prop_of_isGood_of_contained {l : Products I} (o : Ordinal) (h : l.isGood C)
    (hsC : contained C o) (i : I) (hi : i ∈ l.val) : ord I i < o := by
  by_contra h'
  apply h
  suffices eval C l = 0 by simp [this]
  ext x
  simp only [eval_eq, LocallyConstant.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero]
  contrapose! h'
  exact hsC x.val x.prop i (h'.1 i hi)

end Ordinal

section Maps
/-!
## `ℤ`-linear maps induced by projections

We define injective `ℤ`-linear maps between modules of the form `LocallyConstant C ℤ` induced by
precomposition with the projections defined in the section `Projections`.

### Main definitions

* `πs` and `πs'` are the `ℤ`-linear maps corresponding to `ProjRestrict` and `ProjRestricts`
  respectively.

### Main result

* We prove that `πs` and `πs'` interact well with `Products.eval` and the main application is the
  theorem `isGood_mono` which says that the property `isGood` is "monotone" on ordinals.
-/

theorem contained_eq_proj (o : Ordinal) (h : contained C o) :
    C = π C (ord I · < o) := by
  have := proj_prop_eq_self C (ord I · < o)
  simp only [ne_eq, Bool.not_eq_false, π] at this
  exact (this (fun i x hx ↦ h x hx i)).symm

theorem isClosed_proj (o : Ordinal) (hC : IsClosed C) : IsClosed (π C (ord I · < o)) :=
  (continuous_proj (ord I · < o)).isClosedMap C hC

theorem contained_proj (o : Ordinal) : contained (π C (ord I · < o)) o := by
  intro x ⟨_, _, h⟩ j hj
  aesop (add simp Proj)

/-- The `ℤ`-linear map induced by precomposition of the projection `C → π C (ord I · < o)`. -/
@[simps!]
noncomputable
def πs (o : Ordinal) : LocallyConstant (π C (ord I · < o)) ℤ →ₗ[ℤ] LocallyConstant C ℤ :=
  LocallyConstant.comapₗ ℤ ⟨(ProjRestrict C (ord I · < o)), (continuous_projRestrict _ _)⟩

theorem coe_πs (o : Ordinal) (f : LocallyConstant (π C (ord I · < o)) ℤ) :
    πs C o f = f ∘ ProjRestrict C (ord I · < o) := by
  rfl

theorem injective_πs (o : Ordinal) : Function.Injective (πs C o) :=
  LocallyConstant.comap_injective ⟨_, (continuous_projRestrict _ _)⟩
    (Set.surjective_mapsTo_image_restrict _ _)

/-- The `ℤ`-linear map induced by precomposition of the projection
`π C (ord I · < o₂) → π C (ord I · < o₁)` for `o₁ ≤ o₂`. -/
@[simps!]
noncomputable
def πs' {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) :
    LocallyConstant (π C (ord I · < o₁)) ℤ →ₗ[ℤ] LocallyConstant (π C (ord I · < o₂)) ℤ :=
  LocallyConstant.comapₗ ℤ ⟨(ProjRestricts C (fun _ hh ↦ lt_of_lt_of_le hh h)),
    (continuous_projRestricts _ _)⟩

theorem coe_πs' {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) (f : LocallyConstant (π C (ord I · < o₁)) ℤ) :
    (πs' C h f).toFun = f.toFun ∘ (ProjRestricts C (fun _ hh ↦ lt_of_lt_of_le hh h)) := by
  rfl

theorem injective_πs' {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : Function.Injective (πs' C h) :=
  LocallyConstant.comap_injective ⟨_, (continuous_projRestricts _ _)⟩
    (surjective_projRestricts _ fun _ hi ↦ lt_of_lt_of_le hi h)

namespace Products

theorem lt_ord_of_lt {l m : Products I} {o : Ordinal} (h₁ : m < l)
    (h₂ : ∀ i ∈ l.val, ord I i < o) : ∀ i ∈ m.val, ord I i < o :=
  List.Sorted.lt_ord_of_lt (List.chain'_iff_pairwise.mp l.2) (List.chain'_iff_pairwise.mp m.2) h₁ h₂

theorem eval_πs {l : Products I} {o : Ordinal} (hlt : ∀ i ∈ l.val, ord I i < o) :
    πs C o (l.eval (π C (ord I · < o))) = l.eval C := by
  simpa only [← LocallyConstant.coe_inj] using evalFacProp C (ord I · < o) hlt

theorem eval_πs' {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hlt : ∀ i ∈ l.val, ord I i < o₁) :
    πs' C h (l.eval (π C (ord I · < o₁))) = l.eval (π C (ord I · < o₂)) := by
  rw [← LocallyConstant.coe_inj, ← LocallyConstant.toFun_eq_coe]
  exact evalFacProps C (fun (i : I) ↦ ord I i < o₁) (fun (i : I) ↦ ord I i < o₂) hlt
    (fun _ hh ↦ lt_of_lt_of_le hh h)

theorem eval_πs_image {l : Products I} {o : Ordinal}
    (hl : ∀ i ∈ l.val, ord I i < o) : eval C '' { m | m < l } =
    (πs C o) '' (eval (π C (ord I · < o)) '' { m | m < l }) := by
  ext f
  simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs C (lt_ord_of_lt hm hl)]

theorem eval_πs_image' {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : ∀ i ∈ l.val, ord I i < o₁) : eval (π C (ord I · < o₂)) '' { m | m < l } =
    (πs' C h) '' (eval (π C (ord I · < o₁)) '' { m | m < l }) := by
  ext f
  simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs' C h (lt_ord_of_lt hm hl)]

theorem head_lt_ord_of_isGood [Inhabited I] {l : Products I} {o : Ordinal}
    (h : l.isGood (π C (ord I · < o))) (hn : l.val ≠ []) : ord I (l.val.head!) < o :=
  prop_of_isGood C (ord I · < o) h l.val.head! (List.head!_mem_self hn)

/--
If `l` is good w.r.t. `π C (ord I · < o₁)` and `o₁ ≤ o₂`, then it is good w.r.t.
`π C (ord I · < o₂)`
-/
theorem isGood_mono {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (π C (ord I · < o₁))) : l.isGood (π C (ord I · < o₂)) := by
  intro hl'
  apply hl
  rwa [eval_πs_image' C h (prop_of_isGood C _ hl), ← eval_πs' C h (prop_of_isGood C _ hl),
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C h)] at hl'

end Products

end Maps

end Profinite.NobelingProof
