/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Product
import Mathlib.Topology.LocallyConstant.Algebra

/-!
# Nöbeling's theorem

This file proves Nöbeling's theorem.

## Main result

* `LocallyConstant.freeOfProfinite`: Nöbeling's theorem.
  For `S : Profinite`, the `ℤ`-module `LocallyConstant S ℤ` is free.

## Proof idea

We follow the proof of theorem 5.4 in [scholze2019condensed], in which the idea is to embed `S` in
a product of `I` copies of `Bool` for some sufficiently large `I`, and then to choose a
well-ordering on `I` and use ordinal induction over that well-order. Here we can let `I` be
the set of clopen subsets of `S` since `S` is totally separated.

The above means it suffices to prove the following statement: For a closed subset `C` of `I → Bool`,
the `ℤ`-module `LocallyConstant C ℤ` is free.

For `i : I`, let `e C i : LocallyConstant C ℤ` denote the map `fun f ↦ (if f.val i then 1 else 0)`.

The basis will consist of products `e C iᵣ * ⋯ * e C i₁` with `iᵣ > ⋯ > i₁` which cannot be written
as linear combinations of lexicographically smaller products. We call this set `GoodProducts C`

What is proved by ordinal induction is that this set is linearly independent. The fact that it
spans can be proved directly.

## References

- [scholze2019condensed], Theorem 5.4.
-/

open CategoryTheory ContinuousMap Limits Opposite Profinite Submodule Topology

universe u

namespace Profinite

namespace NobelingProof

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
  dsimp (config := { unfoldPartialApp := true }) [Proj]
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
  map_comp _ _ := by dsimp; rw [← CompHausLike.ofHom_comp]; congr; dsimp; rw [projRestricts_eq_comp]

/-- The limit cone on `spanFunctor` with point `C`. -/
noncomputable
def spanCone [∀ (s : Finset I) (i : I), Decidable (i ∈ s)] (hC : IsCompact C) :
    Cone (spanFunctor hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π :=
  { app := fun s ↦ TopCat.ofHom ⟨ProjRestrict C (· ∈ unop s), continuous_projRestrict _ _⟩
    naturality := by
      intro X Y h
      simp only [Functor.const_obj_obj, Homeomorph.setCongr, Homeomorph.homeomorph_mk_coe,
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
  cases l; cases m; rw [Subtype.mk_lt_mk]; exact Iff.rfl

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
  rcases lt_trichotomy a b with (h'|rfl|h')
  · exfalso; apply hb; rw [← h]
    exact Submodule.subset_span ⟨a, h', rfl⟩
  · rfl
  · exfalso; apply ha; rw [h]
    exact Submodule.subset_span ⟨b, ⟨h',rfl⟩⟩

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
  congr
  apply forall_congr; intro i
  apply forall_congr; intro hi
  simp [h i hi, Proj]

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

variable [LinearOrder I]

section Span
/-!
## The good products span

Most of the argument is developing an API for `π C (· ∈ s)` when `s : Finset I`; then the image
of `C` is finite with the discrete topology. In this case, there is a direct argument that the good
products span. The general result is deduced from this.

### Main theorems

* `GoodProducts.spanFin` : The good products span the locally constant functions on `π C (· ∈ s)`
  if `s` is finite.

* `GoodProducts.span` : The good products span `LocallyConstant C ℤ` for every closed subset `C`.
-/

section Fin

variable (s : Finset I)

/-- The `ℤ`-linear map induced by precomposition of the projection `C → π C (· ∈ s)`. -/
noncomputable
def πJ : LocallyConstant (π C (· ∈ s)) ℤ →ₗ[ℤ] LocallyConstant C ℤ :=
  LocallyConstant.comapₗ ℤ ⟨_, (continuous_projRestrict C (· ∈ s))⟩

theorem eval_eq_πJ (l : Products I) (hl : l.isGood (π C (· ∈ s))) :
    l.eval C = πJ C s (l.eval (π C (· ∈ s))) := by
  ext f
  simp only [πJ, LocallyConstant.comapₗ, LinearMap.coe_mk, AddHom.coe_mk,
    (continuous_projRestrict C (· ∈ s)), LocallyConstant.coe_comap, Function.comp_apply]
  exact (congr_fun (Products.evalFacProp C (· ∈ s) (Products.prop_of_isGood  C (· ∈ s) hl)) _).symm

/-- `π C (· ∈ s)` is finite for a finite set `s`. -/
noncomputable
instance : Fintype (π C (· ∈ s)) := by
  let f : π C (· ∈ s) → (s → Bool) := fun x j ↦ x.val j.val
  refine Fintype.ofInjective f ?_
  intro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩ h
  ext i
  by_cases hi : i ∈ s
  · exact congrFun h ⟨i, hi⟩
  · simp only [Proj, if_neg hi]


open scoped Classical in
/-- The Kronecker delta as a locally constant map from `π C (· ∈ s)` to `ℤ`. -/
noncomputable
def spanFinBasis (x : π C (· ∈ s)) : LocallyConstant (π C (· ∈ s)) ℤ where
  toFun := fun y ↦ if y = x then 1 else 0
  isLocallyConstant :=
    haveI : DiscreteTopology (π C (· ∈ s)) := Finite.instDiscreteTopology
    IsLocallyConstant.of_discrete _

open scoped Classical in
theorem spanFinBasis.span : ⊤ ≤ Submodule.span ℤ (Set.range (spanFinBasis C s)) := by
  intro f _
  rw [Finsupp.mem_span_range_iff_exists_finsupp]
  use Finsupp.onFinset (Finset.univ) f.toFun (fun _ _ ↦ Finset.mem_univ _)
  ext x
  change LocallyConstant.evalₗ ℤ x _ = _
  simp only [zsmul_eq_mul, map_finsuppSum, LocallyConstant.evalₗ_apply,
    LocallyConstant.coe_mul, Pi.mul_apply, spanFinBasis, LocallyConstant.coe_mk, mul_ite, mul_one,
    mul_zero, Finsupp.sum_ite_eq, Finsupp.mem_support_iff, ne_eq, ite_not]
  split_ifs with h <;> [exact h.symm; rfl]

/--
A certain explicit list of locally constant maps. The theorem `factors_prod_eq_basis` shows that the
product of the elements in this list is the delta function `spanFinBasis C s x`.
-/
def factors (x : π C (· ∈ s)) : List (LocallyConstant (π C (· ∈ s)) ℤ) :=
  List.map (fun i ↦ if x.val i = true then e (π C (· ∈ s)) i else (1 - (e (π C (· ∈ s)) i)))
    (s.sort (·≥·))

theorem list_prod_apply {I} (C : Set (I → Bool)) (x : C) (l : List (LocallyConstant C ℤ)) :
    l.prod x = (l.map (LocallyConstant.evalMonoidHom x)).prod := by
  rw [← map_list_prod (LocallyConstant.evalMonoidHom x) l]
  rfl

theorem factors_prod_eq_basis_of_eq {x y : (π C fun x ↦ x ∈ s)} (h : y = x) :
    (factors C s x).prod y = 1 := by
  rw [list_prod_apply (π C (· ∈ s)) y _]
  apply List.prod_eq_one
  simp only [h, List.mem_map, LocallyConstant.evalMonoidHom, factors]
  rintro _ ⟨a, ⟨b, _, rfl⟩, rfl⟩
  dsimp
  split_ifs with hh
  · rw [e, LocallyConstant.coe_mk, if_pos hh]
  · rw [LocallyConstant.sub_apply, e, LocallyConstant.coe_mk, LocallyConstant.coe_mk, if_neg hh]
    simp only [LocallyConstant.toFun_eq_coe, LocallyConstant.coe_one, Pi.one_apply, sub_zero]

theorem e_mem_of_eq_true {x : (π C (· ∈ s))} {a : I} (hx : x.val a = true) :
    e (π C (· ∈ s)) a ∈ factors C s x := by
  rcases x with ⟨_, z, hz, rfl⟩
  simp only [factors, List.mem_map, Finset.mem_sort]
  refine ⟨a, ?_, if_pos hx⟩
  aesop (add simp Proj)

theorem one_sub_e_mem_of_false {x y : (π C (· ∈ s))} {a : I} (ha : y.val a = true)
    (hx : x.val a = false) : 1 - e (π C (· ∈ s)) a ∈ factors C s x := by
  simp only [factors, List.mem_map, Finset.mem_sort]
  use a
  simp only [hx, ite_false, and_true]
  rcases y with ⟨_, z, hz, rfl⟩
  aesop (add simp Proj)

theorem factors_prod_eq_basis_of_ne {x y : (π C (· ∈ s))} (h : y ≠ x) :
    (factors C s x).prod y = 0 := by
  rw [list_prod_apply (π C (· ∈ s)) y _]
  apply List.prod_eq_zero
  simp only [List.mem_map]
  obtain ⟨a, ha⟩ : ∃ a, y.val a ≠ x.val a := by contrapose! h; ext; apply h
  cases hx : x.val a
  · rw [hx, ne_eq, Bool.not_eq_false] at ha
    refine ⟨1 - (e (π C (· ∈ s)) a), ⟨one_sub_e_mem_of_false _ _ ha hx, ?_⟩⟩
    rw [e, LocallyConstant.evalMonoidHom_apply, LocallyConstant.sub_apply,
      LocallyConstant.coe_one, Pi.one_apply, LocallyConstant.coe_mk, if_pos ha, sub_self]
  · refine ⟨e (π C (· ∈ s)) a, ⟨e_mem_of_eq_true _ _ hx, ?_⟩⟩
    rw [hx] at ha
    rw [LocallyConstant.evalMonoidHom_apply, e, LocallyConstant.coe_mk, if_neg ha]

/-- If `s` is finite, the product of the elements of the list `factors C s x`
is the delta function at `x`. -/
theorem factors_prod_eq_basis (x : π C (· ∈ s)) :
    (factors C s x).prod = spanFinBasis C s x := by
  ext y
  dsimp [spanFinBasis]
  split_ifs with h <;> [exact factors_prod_eq_basis_of_eq _ _ h;
    exact factors_prod_eq_basis_of_ne _ _ h]

theorem GoodProducts.finsuppSum_mem_span_eval {a : I} {as : List I}
    (ha : List.Chain' (· > ·) (a :: as)) {c : Products I →₀ ℤ}
    (hc : (c.support : Set (Products I)) ⊆ {m | m.val ≤ as}) :
    (Finsupp.sum c fun a_1 b ↦ e (π C (· ∈ s)) a * b • Products.eval (π C (· ∈ s)) a_1) ∈
      Submodule.span ℤ (Products.eval (π C (· ∈ s)) '' {m | m.val ≤ a :: as}) := by
  apply Submodule.finsuppSum_mem
  intro m hm
  have hsm := (LinearMap.mulLeft ℤ (e (π C (· ∈ s)) a)).map_smul
  dsimp at hsm
  rw [hsm]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hmas : m.val ≤ as := by
    apply hc
    simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hm
  refine ⟨⟨a :: m.val, ha.cons_of_le m.prop hmas⟩, ⟨List.cons_le_cons a hmas, ?_⟩⟩
  simp only [Products.eval, List.map, List.prod_cons]

@[deprecated (since := "2025-04-06")]
alias GoodProducts.finsupp_sum_mem_span_eval := GoodProducts.finsuppSum_mem_span_eval

/-- If `s` is a finite subset of `I`, then the good products span. -/
theorem GoodProducts.spanFin [WellFoundedLT I] :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (· ∈ s)))) := by
  rw [span_iff_products]
  refine le_trans (spanFinBasis.span C s) ?_
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [← factors_prod_eq_basis]
  let l := s.sort (·≥·)
  dsimp [factors]
  suffices l.Chain' (· > ·) → (l.map (fun i ↦ if x.val i = true then e (π C (· ∈ s)) i
      else (1 - (e (π C (· ∈ s)) i)))).prod ∈
      Submodule.span ℤ ((Products.eval (π C (· ∈ s))) '' {m | m.val ≤ l}) from
    Submodule.span_mono (Set.image_subset_range _ _) (this (Finset.sort_sorted_gt _).chain')
  induction l with
  | nil =>
    intro _
    apply Submodule.subset_span
    exact ⟨⟨[], List.chain'_nil⟩,⟨Or.inl rfl, rfl⟩⟩
  | cons a as ih =>
    rw [List.map_cons, List.prod_cons]
    intro ha
    specialize ih (by rw [List.chain'_cons'] at ha; exact ha.2)
    rw [Finsupp.mem_span_image_iff_linearCombination] at ih
    simp only [Finsupp.mem_supported, Finsupp.linearCombination_apply] at ih
    obtain ⟨c, hc, hc'⟩ := ih
    rw [← hc']; clear hc'
    have hmap := fun g ↦ map_finsuppSum (LinearMap.mulLeft ℤ (e (π C (· ∈ s)) a)) c g
    dsimp at hmap ⊢
    split_ifs
    · rw [hmap]
      exact finsuppSum_mem_span_eval _ _ ha hc
    · ring_nf
      rw [hmap]
      apply Submodule.add_mem
      · apply Submodule.neg_mem
        exact finsuppSum_mem_span_eval _ _ ha hc
      · apply Submodule.finsuppSum_mem
        intro m hm
        apply Submodule.smul_mem
        apply Submodule.subset_span
        refine ⟨m, ⟨?_, rfl⟩⟩
        simp only [Set.mem_setOf_eq]
        have hmas : m.val ≤ as :=
          hc (by simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hm)
        refine le_trans hmas ?_
        cases as with
        | nil => exact (List.nil_lt_cons a []).le
        | cons b bs =>
          apply le_of_lt
          rw [List.chain'_cons] at ha
          exact (List.lt_iff_lex_lt _ _).mp (List.Lex.rel ha.1)

end Fin

theorem fin_comap_jointlySurjective
    (hC : IsClosed C)
    (f : LocallyConstant C ℤ) : ∃ (s : Finset I)
    (g : LocallyConstant (π C (· ∈ s)) ℤ), f = g.comap ⟨(ProjRestrict C (· ∈ s)),
      continuous_projRestrict _ _⟩ := by
  obtain ⟨J, g, h⟩ := @Profinite.exists_locallyConstant (Finset I)ᵒᵖ _ _ _
    (spanCone hC.isCompact) ℤ
    (spanCone_isLimit hC.isCompact) f
  exact ⟨(Opposite.unop J), g, h⟩

/-- The good products span all of `LocallyConstant C ℤ` if `C` is closed. -/
theorem GoodProducts.span [WellFoundedLT I] (hC : IsClosed C) :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval C)) := by
  rw [span_iff_products]
  intro f _
  obtain ⟨K, f', rfl⟩ : ∃ K f', f = πJ C K f' := fin_comap_jointlySurjective C hC f
  refine Submodule.span_mono ?_ <| Submodule.apply_mem_span_image_of_mem_span (πJ C K) <|
    spanFin C K (Submodule.mem_top : f' ∈ ⊤)
  rintro l ⟨y, ⟨m, rfl⟩, rfl⟩
  exact ⟨m.val, eval_eq_πJ C K m.val m.prop⟩

end Span

variable [WellFoundedLT I]

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
  suffices eval C l = 0 by simp [this, Submodule.zero_mem]
  ext x
  simp only [eval_eq, LocallyConstant.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero]
  contrapose! h'
  exact hsC x.val x.prop i (h'.1 i hi)

end Ordinal

section Zero
/-!

## The zero case of the induction

In this case, we have `contained C 0` which means that `C` is either empty or a singleton.
-/

instance : Subsingleton (LocallyConstant (∅ : Set (I → Bool)) ℤ) :=
  subsingleton_iff.mpr (fun _ _ ↦ LocallyConstant.ext isEmptyElim)

instance : IsEmpty { l // Products.isGood (∅ : Set (I → Bool)) l } :=
  isEmpty_iff.mpr fun ⟨l, hl⟩ ↦ hl <| by
    rw [subsingleton_iff.mp inferInstance (Products.eval ∅ l) 0]
    exact Submodule.zero_mem _

theorem GoodProducts.linearIndependentEmpty {I} [LinearOrder I] :
    LinearIndependent ℤ (eval (∅ : Set (I → Bool))) := linearIndependent_empty_type

/-- The empty list as a `Products` -/
def Products.nil : Products I := ⟨[], by simp only [List.chain'_nil]⟩

theorem Products.lt_nil_empty {I} [LinearOrder I] : { m : Products I | m < Products.nil } = ∅ := by
  ext ⟨m, hm⟩
  refine ⟨fun h ↦ ?_, by tauto⟩
  simp only [Set.mem_setOf_eq, lt_iff_lex_lt, nil, List.not_lex_nil] at h

instance {α : Type*} [TopologicalSpace α] [Nonempty α] : Nontrivial (LocallyConstant α ℤ) :=
  ⟨0, 1, ne_of_apply_ne DFunLike.coe <| (Function.const_injective (β := ℤ)).ne zero_ne_one⟩

theorem Products.isGood_nil {I} [LinearOrder I] :
    Products.isGood ({fun _ ↦ false} : Set (I → Bool)) Products.nil := by
  intro h
  simp [Products.eval, Products.nil] at h

theorem Products.span_nil_eq_top {I} [LinearOrder I] :
    Submodule.span ℤ (eval ({fun _ ↦ false} : Set (I → Bool)) '' {nil}) = ⊤ := by
  rw [Set.image_singleton, eq_top_iff]
  intro f _
  rw [Submodule.mem_span_singleton]
  refine ⟨f default, ?_⟩
  simp only [eval, List.map, List.prod_nil, zsmul_eq_mul, mul_one, Products.nil]
  ext x
  obtain rfl : x = default := by simp only [Set.default_coe_singleton, eq_iff_true_of_subsingleton]
  rfl

/-- There is a unique `GoodProducts` for the singleton `{fun _ ↦ false}`. -/
noncomputable
instance : Unique { l // Products.isGood ({fun _ ↦ false} : Set (I → Bool)) l } where
  default := ⟨Products.nil, Products.isGood_nil⟩
  uniq := by
    intro ⟨⟨l, hl⟩, hll⟩
    ext
    apply Subtype.ext
    apply (List.lex_nil_or_eq_nil l (r := (· < ·))).resolve_left
    intro _
    apply hll
    have he : {Products.nil} ⊆ {m | m < ⟨l,hl⟩} := by
      simpa only [Products.nil, Products.lt_iff_lex_lt, Set.singleton_subset_iff, Set.mem_setOf_eq]
    apply Submodule.span_mono (Set.image_subset _ he)
    rw [Products.span_nil_eq_top]
    exact Submodule.mem_top

instance (α : Type*) [TopologicalSpace α] : NoZeroSMulDivisors ℤ (LocallyConstant α ℤ) := by
  constructor
  intro c f h
  rw [or_iff_not_imp_left]
  intro hc
  ext x
  apply mul_right_injective₀ hc
  simp [LocallyConstant.ext_iff] at h
  simpa [LocallyConstant.ext_iff] using h x

theorem GoodProducts.linearIndependentSingleton {I} [LinearOrder I] :
    LinearIndependent ℤ (eval ({fun _ ↦ false} : Set (I → Bool))) := by
  refine linearIndependent_unique (eval ({fun _ ↦ false} : Set (I → Bool))) ?_
  simp [eval, Products.eval, Products.nil, default]

end Zero

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
  rwa [eval_πs_image' C h (prop_of_isGood  C _ hl), ← eval_πs' C h (prop_of_isGood  C _ hl),
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C h)] at hl'

end Products

end Maps

section Limit
/-!

## The limit case of the induction

We relate linear independence in `LocallyConstant (π C (ord I · < o')) ℤ` with linear independence
in `LocallyConstant C ℤ`, where `contained C o` and `o' < o`.

When `o` is a limit ordinal, we prove that the good products in `LocallyConstant C ℤ` are linearly
independent if and only if a certain directed union is linearly independent. Each term in this
directed union is in bijection with the good products w.r.t. `π C (ord I · < o')` for an ordinal
`o' < o`, and these are linearly independent by the inductive hypothesis.

### Main definitions

* `GoodProducts.smaller` is the image of good products coming from a smaller ordinal.

* `GoodProducts.range_equiv`: The image of the `GoodProducts` in `C` is equivalent to the union of
  `smaller C o'` over all ordinals `o' < o`.

### Main results

* `Products.limitOrdinal`: for `o` a limit ordinal such that `contained C o`, a product `l` is good
  w.r.t. `C` iff it there exists an ordinal `o' < o` such that `l` is good w.r.t.
  `π C (ord I · < o')`.

* `GoodProducts.linearIndependent_iff_union_smaller` is the result mentioned above, that the good
  products are linearly independent iff a directed union is.
-/

namespace GoodProducts

/--
The image of the `GoodProducts` for `π C (ord I · < o)` in `LocallyConstant C ℤ`. The name `smaller`
refers to the setting in which we will use this, when we are mapping in `GoodProducts` from a
smaller set, i.e. when `o` is a smaller ordinal than the one `C` is "contained" in.
-/
def smaller (o : Ordinal) : Set (LocallyConstant C ℤ) :=
  (πs C o) '' (range (π C (ord I · < o)))

/--
The map from the image of the `GoodProducts` in `LocallyConstant (π C (ord I · < o)) ℤ` to
`smaller C o`
-/
noncomputable
def range_equiv_smaller_toFun (o : Ordinal) (x : range (π C (ord I · < o))) : smaller C o :=
  ⟨πs C o ↑x, x.val, x.property, rfl⟩

theorem range_equiv_smaller_toFun_bijective (o : Ordinal) :
    Function.Bijective (range_equiv_smaller_toFun C o) := by
  dsimp (config := { unfoldPartialApp := true }) [range_equiv_smaller_toFun]
  refine ⟨fun a b hab ↦ ?_, fun ⟨a, b, hb⟩ ↦ ?_⟩
  · ext1
    simp only [Subtype.mk.injEq] at hab
    exact injective_πs C o hab
  · use ⟨b, hb.1⟩
    simpa only [Subtype.mk.injEq] using hb.2

/--
The equivalence from the image of the `GoodProducts` in `LocallyConstant (π C (ord I · < o)) ℤ` to
`smaller C o`
-/
noncomputable
def range_equiv_smaller (o : Ordinal) : range (π C (ord I · < o)) ≃ smaller C o :=
  Equiv.ofBijective (range_equiv_smaller_toFun C o) (range_equiv_smaller_toFun_bijective C o)

theorem smaller_factorization (o : Ordinal) :
    (fun (p : smaller C o) ↦ p.1) ∘ (range_equiv_smaller C o).toFun =
    (πs C o) ∘ (fun (p : range (π C (ord I · < o))) ↦ p.1) := by rfl

theorem linearIndependent_iff_smaller (o : Ordinal) :
    LinearIndependent ℤ (GoodProducts.eval (π C (ord I · < o))) ↔
    LinearIndependent ℤ (fun (p : smaller C o) ↦ p.1) := by
  rw [GoodProducts.linearIndependent_iff_range,
    ← LinearMap.linearIndependent_iff (πs C o)
    (LinearMap.ker_eq_bot_of_injective (injective_πs _ _)), ← smaller_factorization C o]
  exact linearIndependent_equiv _

theorem smaller_mono {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : smaller C o₁ ⊆ smaller C o₂ := by
  rintro f ⟨g, hg, rfl⟩
  simp only [smaller, Set.mem_image]
  use πs' C h g
  obtain ⟨⟨l, gl⟩, rfl⟩ := hg
  refine ⟨?_, ?_⟩
  · use ⟨l, Products.isGood_mono C h gl⟩
    ext x
    rw [eval, ← Products.eval_πs' _ h (Products.prop_of_isGood  C _ gl), eval]
  · rw [← LocallyConstant.coe_inj, coe_πs C o₂, ← LocallyConstant.toFun_eq_coe, coe_πs',
      Function.comp_assoc, projRestricts_comp_projRestrict C _, coe_πs]
    rfl

end GoodProducts

variable {o : Ordinal} (ho : o.IsLimit)
include ho

theorem Products.limitOrdinal (l : Products I) : l.isGood (π C (ord I · < o)) ↔
    ∃ (o' : Ordinal), o' < o ∧ l.isGood (π C (ord I · < o')) := by
  refine ⟨fun h ↦ ?_, fun ⟨o', ⟨ho', hl⟩⟩ ↦ isGood_mono C (le_of_lt ho') hl⟩
  use Finset.sup l.val.toFinset (fun a ↦ Order.succ (ord I a))
  have hslt : Finset.sup l.val.toFinset (fun a ↦ Order.succ (ord I a)) < o := by
    simp only [Finset.sup_lt_iff ho.pos, List.mem_toFinset]
    exact fun b hb ↦ ho.succ_lt (prop_of_isGood C (ord I · < o) h b hb)
  refine ⟨hslt, fun he ↦ h ?_⟩
  have hlt : ∀ i ∈ l.val, ord I i < Finset.sup l.val.toFinset (fun a ↦ Order.succ (ord I a)) := by
    intro i hi
    simp only [Finset.lt_sup_iff, List.mem_toFinset, Order.lt_succ_iff]
    exact ⟨i, hi, le_rfl⟩
  rwa [eval_πs_image' C (le_of_lt hslt) hlt, ← eval_πs' C (le_of_lt hslt) hlt,
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C _)]

variable (hsC : contained C o)
include hsC

theorem GoodProducts.union : range C = ⋃ (e : {o' // o' < o}), (smaller C e.val) := by
  ext p
  simp only [smaller, range, Set.mem_iUnion, Set.mem_image, Set.mem_range, Subtype.exists]
  refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
  · obtain ⟨l, hl, rfl⟩ := hp
    rw [contained_eq_proj C o hsC, Products.limitOrdinal C ho] at hl
    obtain ⟨o', ho'⟩ := hl
    refine ⟨o', ho'.1, eval (π C (ord I · < o')) ⟨l, ho'.2⟩, ⟨l, ho'.2, rfl⟩, ?_⟩
    exact Products.eval_πs C (Products.prop_of_isGood  C _ ho'.2)
  · obtain ⟨o', h, _, ⟨l, hl, rfl⟩, rfl⟩ := hp
    refine ⟨l, ?_, (Products.eval_πs C (Products.prop_of_isGood  C _ hl)).symm⟩
    rw [contained_eq_proj C o hsC]
    exact Products.isGood_mono C (le_of_lt h) hl

/--
The image of the `GoodProducts` in `C` is equivalent to the union of `smaller C o'` over all
ordinals `o' < o`.
-/
def GoodProducts.range_equiv : range C ≃ ⋃ (e : {o' // o' < o}), (smaller C e.val) :=
  Equiv.setCongr (union C ho hsC)

theorem GoodProducts.range_equiv_factorization :
    (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) ∘ (range_equiv C ho hsC).toFun =
    (fun (p : range C) ↦ (p.1 : LocallyConstant C ℤ)) := rfl

theorem GoodProducts.linearIndependent_iff_union_smaller :
    LinearIndependent ℤ (GoodProducts.eval C) ↔
      LinearIndependent ℤ (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) := by
  rw [GoodProducts.linearIndependent_iff_range, ← range_equiv_factorization C ho hsC]
  exact linearIndependent_equiv (range_equiv C ho hsC)

end Limit

end NobelingProof

end Profinite
