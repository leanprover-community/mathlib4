/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Product
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Data.Bool.Basic

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
def π : Set (I → Bool) := Proj J '' C

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
  map h := ⟨(ProjRestricts C (leOfHom h.unop)), continuous_projRestricts _ _⟩
  map_id J := by simp only [projRestricts_eq_id C (· ∈ (unop J))]; rfl
  map_comp _ _ := by dsimp; congr; dsimp; rw [projRestricts_eq_comp]

/-- The limit cone on `spanFunctor` with point `C`. -/
noncomputable
def spanCone [∀ (s : Finset I) (i : I), Decidable (i ∈ s)] (hC : IsCompact C) :
    Cone (spanFunctor hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π :=
  { app := fun s ↦ ⟨ProjRestrict C (· ∈ unop s), continuous_projRestrict _ _⟩
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
  toFun := fun f ↦ if f.val i then 1 else 0
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_continuous]
    exact (continuous_of_discreteTopology (f := fun a : Bool ↦ if a then 1 else 0)).comp
      ((continuous_apply i).comp continuous_subtype_val)

variable [LinearOrder I]

/--
`Products I` is the type of lists of decreasing elements of `I`, so a typical element is
`[i₁, i₂, ...]` with `i₁ > i₂ > ...`. We order `Products I` lexicographically, so `[] < [i₁, ...]`,
and `[i₁, i₂, ...] < [j₁, j₂, ...]` if either `i₁ < j₁`, or `i₁ = j₁` and `[i₂, ...] < [j₂, ...]`.

Terms `m = [i₁, i₂, ..., iᵣ]` of this type will be used to represent products of the form
`e C i₁ ··· e C iᵣ : LocallyConstant C ℤ` . The function associated to `m` is `m.eval`.
-/
def Products (I : Type*) [LinearOrder I] := {l : List I // l.Chain' (·>·)}

namespace Products

instance : LinearOrder (Products I) :=
  inferInstanceAs (LinearOrder {l : List I // l.Chain' (·>·)})

@[simp]
theorem lt_iff_lex_lt (l m : Products I) : l < m ↔ List.Lex (·<·) l.val m.val := by
  cases l; cases m; rw [Subtype.mk_lt_mk]; exact Iff.rfl

instance [WellFoundedLT I] : WellFoundedLT (Products I) := by
  have : (· < · : Products I → _ → _) = (fun l m ↦ List.Lex (·<·) l.val m.val) := by
    ext; exact lt_iff_lex_lt _ _
  rw [WellFoundedLT, this]
  dsimp [Products]
  rw [(by rfl : (·>· : I → _) = flip (·<·))]
  infer_instance

/-- The evaluation `e C i₁ ··· e C iᵣ : C → ℤ`  of a formal product `[i₁, i₂, ..., iᵣ]`. -/
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
  apply IsWellFounded.induction (·<· : Products I → Products I → Prop)
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
  simp only [zsmul_eq_mul, map_finsupp_sum, LocallyConstant.evalₗ_apply,
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

theorem GoodProducts.finsupp_sum_mem_span_eval {a : I} {as : List I}
    (ha : List.Chain' (· > ·) (a :: as)) {c : Products I →₀ ℤ}
    (hc : (c.support : Set (Products I)) ⊆ {m | m.val ≤ as}) :
    (Finsupp.sum c fun a_1 b ↦ e (π C (· ∈ s)) a * b • Products.eval (π C (· ∈ s)) a_1) ∈
      Submodule.span ℤ (Products.eval (π C (· ∈ s)) '' {m | m.val ≤ a :: as}) := by
  apply Submodule.finsupp_sum_mem
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
  suffices l.Chain' (·>·) → (l.map (fun i ↦ if x.val i = true then e (π C (· ∈ s)) i
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
    have hmap := fun g ↦ map_finsupp_sum (LinearMap.mulLeft ℤ (e (π C (· ∈ s)) a)) c g
    dsimp at hmap ⊢
    split_ifs
    · rw [hmap]
      exact finsupp_sum_mem_span_eval _ _ ha hc
    · ring_nf
      rw [hmap]
      apply Submodule.add_mem
      · apply Submodule.neg_mem
        exact finsupp_sum_mem_span_eval _ _ ha hc
      · apply Submodule.finsupp_sum_mem
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
          have hlex := List.lt.head bs (b :: bs) ha.1
          exact (List.lt_iff_lex_lt _ _).mp hlex

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

-- TODO: rename section?
section Ordinal
/-!

## Well-ordering `I`

We choose an arbitrary well-ordering on `I`. This will allow us to use limit induction.

### Main definitions

* `contained C o` is a predicate saying that `C` is "small" enough in relation to the element `o`
  to satisfy the inductive hypothesis.

* `P I` is the predicate on ordinals about linear independence of good products, which the rest of
  this file is spent on proving by induction.
-/

/-- A predicate saying that `C` is "small" enough to satisfy the inductive hypothesis. -/
def contained (o : I) : Prop := ∀ f, f ∈ C → ∀ i : I, f i = true → i < o

/--
The predicate on ordinals which we prove by induction, see `GoodProducts.P0`,
`GoodProducts.Plimit` and `GoodProducts.linearIndependentAux` in the section `Induction` below
-/
def P (o : I) : Prop := ∀ C : Set (I → Bool), IsClosed C → contained C o →
    LinearIndependent ℤ (GoodProducts.eval C)

theorem Products.prop_of_isGood_of_contained {l : Products I} (o : I) (h : l.isGood C)
    (hsC : contained C o) (i : I) (hi : i ∈ l.val) : i < o := by
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
  simp only [Set.mem_setOf_eq, lt_iff_lex_lt, nil, List.Lex.not_nil_right] at h

instance {α : Type*} [TopologicalSpace α] [Nonempty α] : Nontrivial (LocallyConstant α ℤ) :=
  ⟨0, 1, ne_of_apply_ne DFunLike.coe <| (Function.const_injective (β := ℤ)).ne zero_ne_one⟩

theorem Products.isGood_nil {I} [LinearOrder I] :
    Products.isGood ({fun _ ↦ false} : Set (I → Bool)) Products.nil := by
  intro h
  simp only [Products.lt_nil_empty, Products.eval, List.map, List.prod_nil, Set.image_empty,
    Submodule.span_empty, Submodule.mem_bot, one_ne_zero] at h

theorem Products.span_nil_eq_top {I} [LinearOrder I] :
    Submodule.span ℤ (eval ({fun _ ↦ false} : Set (I → Bool)) '' {nil}) = ⊤ := by
  rw [Set.image_singleton, eq_top_iff]
  intro f _
  rw [Submodule.mem_span_singleton]
  refine ⟨f default, ?_⟩
  simp only [eval, List.map, List.prod_nil, zsmul_eq_mul, mul_one]
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
    apply (List.Lex.nil_left_or_eq_nil l (r := (·<·))).resolve_left
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
  simp only [eval, Products.eval, List.map, List.prod_nil, ne_eq, one_ne_zero, not_false_eq_true]

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

-- TODO: make x implicit
-- TODO: use `Iio o` instead? Redefine π? Why does it even have a decidability instance???
theorem contained_eq_proj (o : I) (h : contained C o) : C = π C (· < o) := by
  have := proj_prop_eq_self C (· < o)
  simp only [ne_eq, Bool.not_eq_false, π] at this
  exact (this (fun i x hx ↦ h x hx i)).symm

theorem isClosed_proj (o : I) (hC : IsClosed C) : IsClosed (π C (· < o)) :=
  (continuous_proj _).isClosedMap C hC

theorem contained_proj (o : I) : contained (π C (· < o)) o := by
  intro x ⟨_, _, h⟩ j hj
  aesop (add simp Proj)

/-- The `ℤ`-linear map induced by precomposition of the projection `C → π C (· < o)`. -/
@[simps!]
noncomputable
def πs (o : I) : LocallyConstant (π C (· < o)) ℤ →ₗ[ℤ] LocallyConstant C ℤ :=
  LocallyConstant.comapₗ ℤ ⟨(ProjRestrict C _), (continuous_projRestrict _ _)⟩

theorem coe_πs (o : I) (f : LocallyConstant (π C (· < o)) ℤ) :
    πs C o f = f ∘ ProjRestrict C (· < o) :=
  rfl

theorem injective_πs (o : I) : Function.Injective (πs C o) :=
  LocallyConstant.comap_injective ⟨_, (continuous_projRestrict _ _)⟩
    (Set.surjective_mapsTo_image_restrict _ _)

/-- The `ℤ`-linear map induced by precomposition of the projection
    `π C (· < y) → π C (· < x)` for `x ≤ y`. -/
@[simps!]
noncomputable
def πs' {o o' : I} (h : o' ≤ o) :
    LocallyConstant (π C (· < o')) ℤ →ₗ[ℤ] LocallyConstant (π C (· < o)) ℤ :=
  LocallyConstant.comapₗ ℤ ⟨(ProjRestricts C fun _ hh ↦ hh.trans_le h),
    (continuous_projRestricts _ _)⟩

theorem coe_πs' {o o' : I} (h : o' ≤ o) (f : LocallyConstant (π C (· < o')) ℤ) :
    (πs' C h f).toFun = f.toFun ∘ (ProjRestricts C fun _ hh ↦ hh.trans_le h) := by
  rfl

theorem injective_πs' {o o' : I} (h : o' ≤ o) : Function.Injective (πs' C h) :=
  LocallyConstant.comap_injective ⟨_, (continuous_projRestricts _ _)⟩
    (surjective_projRestricts _ fun _ hi ↦ lt_of_lt_of_le hi h)

namespace Products

-- TODO: move elsewhere
-- TODO: remove all the `List` namespaces.
theorem _root_.List.Sorted.forall_lt_of_lt {α} [Preorder α] {l m : List α} {a : α}
    (hm : m.Sorted (· > ·)) (h : m < l) (hlt : ∀ i ∈ l, i < a) : ∀ i ∈ m, i < a :=
  match l with
  | [] => (List.Lex.not_nil_right _ _ h).elim
  | a::l => fun i hi ↦
    have : Inhabited α := ⟨i⟩
    ((hm.le_head! hi).trans <| List.head!_le_of_lt _ _ h (List.ne_nil_of_mem hi)).trans_lt <|
      hlt _ <| List.head!_mem_self (List.cons_ne_nil a l)

-- TODO: rename / delete?
theorem lt_ord_of_lt {l m : Products I} {o : I} (h₁ : m < l) (h₂ : ∀ i ∈ l.val, i < o) :
    ∀ i ∈ m.val, i < o :=
  List.Sorted.forall_lt_of_lt (List.chain'_iff_pairwise.mp m.2) h₁ h₂
-- (List.chain'_iff_pairwise.mp l.2)

theorem eval_πs {l : Products I} {o : I} (hlt : ∀ i ∈ l.val, i < o) :
    πs C o (l.eval (π C (· < o))) = l.eval C := by
  simpa only [← LocallyConstant.coe_inj] using evalFacProp C _ hlt

theorem eval_πs' {l : Products I} {o' o : I} (h : o' ≤ o) (hlt : ∀ i ∈ l.val, i < o') :
    πs' C h (l.eval (π C (· < o'))) = l.eval (π C (· < o)) := by
  rw [← LocallyConstant.coe_inj, ← LocallyConstant.toFun_eq_coe]
  exact evalFacProps C _ _ hlt fun _ hh ↦ hh.trans_le h

-- TODO: use Iio?
theorem eval_πs_image {l : Products I} {o : I}
    (hl : ∀ i ∈ l.val, i < o) : eval C '' { m | m < l } =
    πs C o '' (eval (π C (· < o)) '' { m | m < l }) := by
  ext f
  simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs C (lt_ord_of_lt hm hl)]

theorem eval_πs_image' {l : Products I} {o₁ o₂ : I} (h : o₁ ≤ o₂) (hl : ∀ i ∈ l.val, i < o₁) :
    eval (π C (· < o₂)) '' { m | m < l } = πs' C h '' (eval (π C (· < o₁)) '' { m | m < l }) := by
  ext f
  simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs' C h (lt_ord_of_lt hm hl)]

theorem head_lt_ord_of_isGood [Inhabited I] {l : Products I} {o : I}
    (h : l.isGood (π C (· < o))) (hn : l.val ≠ []) : l.val.head! < o :=
  prop_of_isGood C _ h l.val.head! (List.head!_mem_self hn)

/--
If `l` is good w.r.t. `π C (· < o₁)` and `o₁ ≤ o₂`, then it is good w.r.t. `π C (· < o₂)`
-/
theorem isGood_mono {l : Products I} {o₁ o₂ : I} (h : o₁ ≤ o₂) (hl : l.isGood (π C (· < o₁))) :
    l.isGood (π C (· < o₂)) := by
  intro hl'
  apply hl
  rwa [eval_πs_image' C h (prop_of_isGood  C _ hl), ← eval_πs' C h (prop_of_isGood  C _ hl),
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C h)] at hl'

end Products

end Maps

section Limit
/-!

## The limit case of the induction

We relate linear independence in `LocallyConstant (π C (· < o')) ℤ` with linear independence
in `LocallyConstant C ℤ`, where `contained C o` and `o' < o`.

When `o` is a limit element, we prove that the good products in `LocallyConstant C ℤ` are linearly
independent if and only if a certain directed union is linearly independent. Each term in this
directed union is in bijection with the good products w.r.t. `π C (ord I · < o')` for an ordinal
`o' < o`, and these are linearly independent by the inductive hypothesis.

### Main definitions

* `GoodProducts.smaller` is the image of good products coming from a smaller element.

* `GoodProducts.range_equiv`: The image of the `GoodProducts` in `C` is equivalent to the union of
  `smaller C o'` over all `o' < o`.

### Main results

-- TODO: rename
* `Products.limitOrdinal`: for `o` a limit element such that `contained C o`, a product `l` is good
  w.r.t. `C` iff it there exists `o' < o` such that `l` is good w.r.t. `π C (· < o')`.

* `GoodProducts.linearIndependent_iff_union_smaller` is the result mentioned above, that the good
  products are linearly independent iff a directed union is.
-/

namespace GoodProducts

/--
The image of the `GoodProducts` for `π C (· < o)` in `LocallyConstant C ℤ`. The name `smaller`
refers to the setting in which we will use this, when we are mapping in `GoodProducts` from a
smaller set, i.e. when `x` is a smaller element than the one `C` is "contained" in.
-/
def smaller (o : I) : Set (LocallyConstant C ℤ) :=
  πs C o '' range (π C (· < o))

/--
The map from the image of the `GoodProducts` in `LocallyConstant (π C (· < x)) ℤ` to `smaller C x`
-/
noncomputable
def range_equiv_smaller_toFun (o : I) (x : range (π C (· < o))) : smaller C o :=
  ⟨πs C o ↑x, x.val, x.property, rfl⟩

theorem range_equiv_smaller_toFun_bijective (o : I) :
    Function.Bijective (range_equiv_smaller_toFun C o) := by
  dsimp (config := { unfoldPartialApp := true }) [range_equiv_smaller_toFun]
  refine ⟨fun a b hab ↦ ?_, fun ⟨a, b, hb⟩ ↦ ?_⟩
  · ext1
    simp only [Subtype.mk.injEq] at hab
    exact injective_πs C o hab
  · use ⟨b, hb.1⟩
    simpa only [Subtype.mk.injEq] using hb.2

/--
The equivalence from the image of the `GoodProducts` in `LocallyConstant (π C (· < o)) ℤ` to
`smaller C o`
-/
noncomputable
def range_equiv_smaller (o : I) : range (π C (· < o)) ≃ smaller C o :=
  Equiv.ofBijective (range_equiv_smaller_toFun C o) (range_equiv_smaller_toFun_bijective C o)

theorem smaller_factorization (o : I) :
    (fun p : smaller C o ↦ p.1) ∘ (range_equiv_smaller C o).toFun =
    πs C o ∘ fun p : range (π C (· < o)) ↦ p.1 := rfl

theorem linearIndependent_iff_smaller (o : I) :
    LinearIndependent ℤ (GoodProducts.eval (π C (· < o))) ↔
    LinearIndependent ℤ (fun (p : smaller C o) ↦ p.1) := by
  rw [GoodProducts.linearIndependent_iff_range,
    ← LinearMap.linearIndependent_iff (πs C o)
    (LinearMap.ker_eq_bot_of_injective (injective_πs _ _)), ← smaller_factorization C o]
  exact linearIndependent_equiv _

theorem smaller_mono {o o' : I} (h : o' ≤ o) : smaller C o' ⊆ smaller C o := by
  rintro f ⟨g, hg, rfl⟩
  simp only [smaller, Set.mem_image]
  use πs' C h g
  obtain ⟨⟨l, gl⟩, rfl⟩ := hg
  refine ⟨?_, ?_⟩
  · use ⟨l, Products.isGood_mono C h gl⟩
    ext x
    rw [eval, ← Products.eval_πs' _ h (Products.prop_of_isGood  C _ gl), eval]
  · rw [← LocallyConstant.coe_inj, coe_πs C o, ← LocallyConstant.toFun_eq_coe, coe_πs',
      Function.comp_assoc, projRestricts_comp_projRestrict C _, coe_πs]
    rfl

end GoodProducts

variable {o : I} (ho : Order.IsSuccLimit o) [SuccOrder I]
include ho

-- TODO: move elsewhere
theorem _root_.Order.IsSuccLimit.lt_finset (s : Finset I) (hs : ∀ y ∈ s, y < o) :
    ∃ z < o, ∀ y ∈ s, y < z := by
  obtain rfl | hn := s.eq_empty_or_nonempty
  · obtain ⟨z, hz⟩ := not_isMin_iff.1 ho.not_isMin
    refine ⟨z, hz, ?_⟩
    simp
  · refine ⟨s.sup' hn Order.succ, ?_, fun y hy ↦ ?_⟩
    · rw [Finset.sup'_lt_iff]
      exact fun y hy ↦ ho.succ_lt (hs y hy)
    · rw [Finset.lt_sup'_iff]
      exact ⟨y, hy, Order.lt_succ_of_not_isMax (hs y hy).not_isMax⟩

-- TODO: rename
theorem Products.limitOrdinal (l : Products I) : l.isGood (π C (· < o)) ↔
    ∃ y < o, l.isGood (π C (· < y)) := by
  refine ⟨fun h ↦ ?_, fun ⟨y, ⟨hy, hl⟩⟩ ↦ isGood_mono C hy.le hl⟩
  obtain ⟨z, hz, hz'⟩ := ho.lt_finset l.val.toFinset (by simpa using prop_of_isGood C _ h)
  simp_rw [List.mem_toFinset] at hz'
  refine ⟨z, hz, fun he ↦ h ?_⟩
  rwa [eval_πs_image' C hz.le hz', ← eval_πs' C (le_of_lt hz) hz',
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C _)]

variable (hsC : contained C o)
include hsC

theorem GoodProducts.union : range C = ⋃ e : Set.Iio o, smaller C e.val := by
  ext p
  simp only [smaller, range, Set.mem_iUnion, Set.mem_image, Set.mem_range, Subtype.exists]
  refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
  · obtain ⟨l, hl, rfl⟩ := hp
    rw [contained_eq_proj C o hsC, Products.limitOrdinal C ho] at hl
    obtain ⟨o', ho'⟩ := hl
    refine ⟨o', ho'.1, eval (π C (· < o')) ⟨l, ho'.2⟩, ⟨l, ho'.2, rfl⟩, ?_⟩
    exact Products.eval_πs C (Products.prop_of_isGood  C _ ho'.2)
  · obtain ⟨o', h, _, ⟨l, hl, rfl⟩, rfl⟩ := hp
    refine ⟨l, ?_, (Products.eval_πs C (Products.prop_of_isGood C _ hl)).symm⟩
    rw [contained_eq_proj C o hsC]
    exact Products.isGood_mono C h.le hl

theorem GoodProducts.linearIndependent_iff_union_smaller :
    LinearIndependent ℤ (GoodProducts.eval C) ↔
      LinearIndependent ℤ fun p : ⋃ e : Set.Iio o, smaller C e.val ↦ p.1 := by
  rw [GoodProducts.linearIndependent_iff_range]
  exact linearIndependent_equiv (f := Subtype.val) (Equiv.Set.ofEq <| union C ho hsC)

end Limit

--TODO: rewrite this docstring so it does not refer to ordinals
section Successor
/-!

## The successor case in the induction

Here we assume that `o` is an ordinal such that `contained C (o+1)` and `o < I`. The element in `I`
corresponding to `o` is called `term I ho`, but in this informal docstring we refer to it simply as
`o`.

This section follows the proof in [scholze2019condensed] quite closely. A translation of the
notation there is as follows:

```
[scholze2019condensed]                  | This file
`S₀`                                    |`C0`
`S₁`                                    |`C1`
`\overline{S}`                          |`π C (ord I · < o)
`\overline{S}'`                         |`C'`
The left map in the exact sequence      |`πs`
The right map in the exact sequence     |`Linear_CC'`
```

When comparing the proof of the successor case in Theorem 5.4 in [scholze2019condensed] with this
proof, one should read the phrase "is a basis" as "is linearly independent". Also, the short exact
sequence in [scholze2019condensed] is only proved to be left exact here (indeed, that is enough
since we are only proving linear independence).

This section is split into two sections. The first one, `ExactSequence` defines the left exact
sequence mentioned in the previous paragraph (see `succ_mono` and `succ_exact`). It corresponds to
the penultimate paragraph of the proof in [scholze2019condensed]. The second one, `GoodProducts`
corresponds to the last paragraph in the proof in [scholze2019condensed].

### Main definitions

The main definitions in the section `ExactSequence` are all just notation explained in the table
above.

The main definitions in the section `GoodProducts` are as follows:

* `MaxProducts`: the set of good products that contain the ordinal `o` (since we have
  `contained C (o+1)`, these all start with `o`).

* `GoodProducts.sum_equiv`: the equivalence between `GoodProducts C` and the disjoint union of
  `MaxProducts C` and `GoodProducts (π C (ord I · < o))`.

### Main results

* The main results in the section `ExactSequence` are `succ_mono` and `succ_exact` which together
  say that the sequence given by `πs` and `Linear_CC'` is left exact:
  ```
                                              f                        g
  0 --→ LocallyConstant (π C (ord I · < o)) ℤ --→ LocallyConstant C ℤ --→ LocallyConstant C' ℤ
  ```
  where `f` is `πs` and `g` is `Linear_CC'`.

The main results in the section `GoodProducts` are as follows:

* `Products.max_eq_eval` says that the linear map on the right in the exact sequence, i.e.
  `Linear_CC'`, takes the evaluation of a term of `MaxProducts` to the evaluation of the
  corresponding list with the leading `o` removed.

* `GoodProducts.maxTail_isGood` says that removing the leading `o` from a term of `MaxProducts C`
  yields a list which `isGood` with respect to `C'`.
-/

variable {o : I} (hC : IsClosed C)

section ExactSequence

/-- The subset of `C` consisting of those elements with `f x = false`. -/
def C0 (o : I) := C ∩ {f | f o = false}

/-- The subset of `C` consisting of those elements with `f x = true`. -/
def C1 (o : I) := C ∩ {f | f o = true}

include hC in
theorem isClosed_C0 : IsClosed (C0 C o) := by
  refine hC.inter ?_
  have h : Continuous fun f : I → Bool ↦ f o := continuous_apply o
  exact IsClosed.preimage h (t := {false}) (isClosed_discrete _)

include hC in
theorem isClosed_C1 : IsClosed (C1 C o) := by
  refine hC.inter ?_
  have h : Continuous fun f : I → Bool ↦ f o := continuous_apply o
  exact IsClosed.preimage h (t := {true}) (isClosed_discrete _)

theorem contained_C1 : contained (π (C1 C o) (· < o)) o :=
  contained_proj _ _

theorem union_C0C1_eq : C0 C o ∪ C1 C o = C := by
  ext f
  simp only [C0, C1, Set.mem_union, Set.mem_inter_iff]
  have := Bool.dichotomy (f o)
  tauto

/--
The intersection of `C0` and the projection of `C1`. We will apply the inductive hypothesis to
this set.
-/
def C' (o : I) := C0 C o ∩ π (C1 C o) (· < o)

include hC in
theorem isClosed_C' : IsClosed (C' C o) :=
  IsClosed.inter (isClosed_C0 _ hC) (isClosed_proj _ _ (isClosed_C1 _ hC))

theorem contained_C' : contained (C' C o) o := fun f hf i hi ↦ contained_C1 C f hf.2 i hi

variable (o)

/-- Swapping the `o` coordinate to `true`. -/
noncomputable
def SwapTrue : (I → Bool) → I → Bool :=
  fun f i ↦ if i = o then true else f i

theorem continuous_swapTrue : Continuous (SwapTrue o) :=
  continuous_pi fun i ↦ continuous_bot.comp' (continuous_apply i)

variable {o}

theorem swapTrue_mem_C1 [SuccOrder I] (hsC : contained C (Order.succ o)) (f : π (C1 C o) (· < o)) :
    SwapTrue o f.val ∈ C1 C o := by
  obtain ⟨f, g, hg, rfl⟩ := f
  convert hg
  dsimp (config := { unfoldPartialApp := true }) [SwapTrue]
  ext i
  split_ifs with h
  · simpa only [← h] using hg.2.symm
  · simp only [Proj, ite_eq_left_iff, not_lt, @eq_comm _ false, ← Bool.not_eq_true]
    specialize hsC g hg.1 i
    intro h'
    contrapose! hsC
    exact ⟨hsC, (h'.lt_of_ne' h).succ_le⟩

/-- The first way to map `C'` into `C`. -/
def CC'₀ : C' C o → C := fun g ↦ ⟨g.val, g.prop.1.1⟩

/-- The second way to map `C'` into `C`. -/
noncomputable
def CC'₁ [SuccOrder I] (hsC : contained C (Order.succ o)) : C' C o → C :=
  fun g ↦ ⟨SwapTrue o g.val, (swapTrue_mem_C1 C hsC ⟨g.val, g.prop.2⟩).1⟩

theorem continuous_CC'₀ : Continuous (CC'₀ C (o := o)) :=
  Continuous.subtype_mk continuous_subtype_val _

theorem continuous_CC'₁ [SuccOrder I] (hsC : contained C (Order.succ o)) :
    Continuous (CC'₁ C hsC) :=
  Continuous.subtype_mk ((continuous_swapTrue o).comp continuous_subtype_val) _

/-- The `ℤ`-linear map induced by precomposing with `CC'₀` -/
noncomputable
def Linear_CC'₀ : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C o) ℤ :=
  LocallyConstant.comapₗ ℤ ⟨CC'₀ C, continuous_CC'₀ C⟩

variable [SuccOrder I] (hsC : contained C (Order.succ o))
include hsC

/-- The `ℤ`-linear map induced by precomposing with `CC'₁` -/
noncomputable
def Linear_CC'₁ : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C o) ℤ :=
  LocallyConstant.comapₗ ℤ ⟨CC'₁ C hsC, continuous_CC'₁ C hsC⟩

/-- The difference between `Linear_CC'₁` and `Linear_CC'₀`. -/
noncomputable
def Linear_CC' [SuccOrder I] (hsC : contained C (Order.succ o)) :
    LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C o) ℤ :=
  Linear_CC'₁ C hsC - Linear_CC'₀ C

theorem CC_comp_zero : ∀ y, Linear_CC' C hsC ((πs C o) y) = 0 := by
  intro y
  ext x
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁, LocallyConstant.sub_apply]
  simp only [Pi.zero_apply, sub_eq_zero]
  congr 1
  ext i
  dsimp [CC'₀, CC'₁, ProjRestrict, Proj]
  apply if_ctx_congr Iff.rfl _ (fun _ ↦ rfl)
  simp only [SwapTrue, ite_eq_right_iff]
  intro h₁ h₂
  exact (h₁.ne h₂).elim

theorem C0_projOrd {x : I → Bool} (hx : x ∈ C0 C o) : Proj (· < o) x = x := by
  ext i
  simp only [Proj, Set.mem_setOf, ite_eq_left_iff, not_lt]
  intro hi
  rw [le_iff_lt_or_eq] at hi
  cases' hi with hi hi
  · specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true] at hsC
    exact (hsC hi.succ_le).symm
  · simp only [C0, Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    rw [eq_comm] at hi
    rw [← hx.2, hi]

theorem C1_projOrd {x : I → Bool} (hx : x ∈ C1 C o) : SwapTrue o (Proj (· < o) x) = x := by
  ext i
  dsimp [SwapTrue, Proj]
  split_ifs with hi h
  · rw [← hx.2, hi]
  · rfl
  · simp only [not_lt] at h
    have h' : o < i := lt_of_le_of_ne h (Ne.symm hi)
    specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true] at hsC
    exact (hsC h'.succ_le).symm

include hC in
open scoped Classical in
theorem CC_exact {f : LocallyConstant C ℤ} (hf : Linear_CC' C hsC f = 0) :
    ∃ y, πs C o y = f := by
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁] at hf
  simp only [sub_eq_zero, ← LocallyConstant.coe_inj, LocallyConstant.coe_comap,
    continuous_CC'₀, continuous_CC'₁] at hf
  let C₀C : C0 C o → C := fun x ↦ ⟨x.val, x.prop.1⟩
  have h₀ : Continuous C₀C := Continuous.subtype_mk continuous_induced_dom _
  let C₁C : π (C1 C o) (· < o) → C :=
    fun x ↦ ⟨SwapTrue o x.val, (swapTrue_mem_C1 C hsC x).1⟩
  have h₁ : Continuous C₁C := Continuous.subtype_mk
    ((continuous_swapTrue o).comp continuous_subtype_val) _
  refine ⟨LocallyConstant.piecewise' ?_ (isClosed_C0 C hC)
      (isClosed_proj _ o (isClosed_C1 C hC)) (f.comap ⟨C₀C, h₀⟩) (f.comap ⟨C₁C, h₁⟩) ?_, ?_⟩
  · rintro _ ⟨y, hyC, rfl⟩
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [← union_C0C1_eq C] at hyC
    refine hyC.imp (fun hyC ↦ ?_) (fun hyC ↦ ⟨y, hyC, rfl⟩)
    rwa [C0_projOrd C hsC hyC]
  · intro x hx
    simpa only [h₀, h₁, LocallyConstant.coe_comap] using (congrFun hf ⟨x, hx⟩).symm
  · ext ⟨x, hx⟩
    rw [← union_C0C1_eq C (o := o)] at hx
    cases' hx with hx₀ hx₁
    · have hx₀' : ProjRestrict C (· < o) ⟨x, hx⟩ = x := by
        simpa only [ProjRestrict, Set.MapsTo.val_restrict_apply] using C0_projOrd C hsC hx₀
      simp only [C₀C, πs_apply_apply, hx₀', hx₀, LocallyConstant.piecewise'_apply_left,
        LocallyConstant.coe_comap, ContinuousMap.coe_mk, Function.comp_apply]
    · have hx₁' : (ProjRestrict C (· < o) ⟨x, hx⟩).val ∈ π (C1 C o) (· < o) := by
        simpa only [ProjRestrict, Set.MapsTo.val_restrict_apply] using ⟨x, hx₁, rfl⟩
      simp only [C₁C, πs_apply_apply, continuous_projRestrict, LocallyConstant.coe_comap,
        Function.comp_apply, hx₁', LocallyConstant.piecewise'_apply_right, h₁]
      congr
      simp only [ContinuousMap.coe_mk, Subtype.mk.injEq]
      exact C1_projOrd C hsC hx₁

variable (o) in
theorem succ_mono : CategoryTheory.Mono (ModuleCat.ofHom (πs C o)) := by
  rw [ModuleCat.mono_iff_injective]
  exact injective_πs _ _

include hC in
theorem succ_exact :
    (ShortComplex.mk (ModuleCat.ofHom (πs C o)) (ModuleCat.ofHom (Linear_CC' C hsC))
    (by ext : 2; apply CC_comp_zero)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro f
  exact CC_exact C hC hsC

end ExactSequence

section GoodProducts

namespace GoodProducts

/--
The `GoodProducts` in `C` that contain `o` (they necessarily start with `o`, see
`GoodProducts.head!_eq_o_of_maxProducts`)
-/
def MaxProducts (o : I) : Set (Products I) := {l | l.isGood C ∧ o ∈ l.val}

theorem union_succ [SuccOrder I] (hsC : contained C (Order.succ o)) :
    GoodProducts C = GoodProducts (π C (· < o)) ∪ MaxProducts C o := by
  ext l
  simp only [GoodProducts, MaxProducts, Set.mem_union, Set.mem_setOf_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_cases hh : o ∈ l.val
    · exact Or.inr ⟨h, hh⟩
    · refine Or.inl fun he ↦ h ?_
      have h' := Products.prop_of_isGood_of_contained C _ h hsC
      simp only [not_imp_not] at hh
      have hh' : ∀ a ∈ l.val, a < o := by
        refine fun a ha ↦ (Order.le_of_lt_succ (h' a ha)).lt_of_ne ?_
        rintro rfl
        contradiction
      rwa [Products.eval_πs_image C hh', ← Products.eval_πs C hh',
        Submodule.apply_mem_span_image_iff_mem_span (injective_πs _ _)]
  · refine h.elim (fun hh ↦ ?_) And.left
    rw [contained_eq_proj C _ hsC]
    exact Products.isGood_mono C (Order.le_succ o) hh

/-- The inclusion map from the sum of `GoodProducts (π C (· < o))` and `MaxProducts C o` to
`Products I`. -/
def sum_to (o : I) : GoodProducts (π C (· < o)) ⊕ MaxProducts C o → Products I :=
  Sum.elim Subtype.val Subtype.val

theorem injective_sum_to : Function.Injective (sum_to C o) := by
  apply Subtype.val_injective.sum_elim Subtype.val_injective
  rintro ⟨a, ha⟩ ⟨b, hb⟩ rfl
  exact (Products.prop_of_isGood C _ ha o hb.2).false

theorem sum_to_range : Set.range (sum_to C o) = GoodProducts (π C (· < o)) ∪ MaxProducts C o := by
  apply (Set.Sum.elim_range _ _).trans
  simp [GoodProducts, MaxProducts]

/-- The equivalence from the sum of `GoodProducts (π C (· < o))` and `MaxProducts C ho` to
`GoodProducts C`. -/
noncomputable
def sum_equiv [SuccOrder I] (hsC : contained C (Order.succ o)) :
    GoodProducts (π C (· < o)) ⊕ MaxProducts C o ≃ GoodProducts C :=
  calc _ ≃ Set.range (sum_to C o) := Equiv.ofInjective (sum_to C o) (injective_sum_to C)
       _ ≃ _ := Equiv.Set.ofEq <| by rw [sum_to_range C, union_succ C hsC]

theorem sum_equiv_comp_eval_eq_elim [SuccOrder I] (hsC : contained C (Order.succ o)) :
    eval C ∘ sum_equiv C hsC =
    Sum.elim (fun l : GoodProducts (π C (· < o)) ↦ Products.eval C l.1)
    (fun l : MaxProducts C o ↦ Products.eval C l.1) := by
  ext ⟨_, _⟩ <;> rfl

/-- Let

`N := LocallyConstant (π C (· < o)) ℤ`

`M := LocallyConstant C ℤ`

`P := LocallyConstant (C' C o) ℤ`

`ι := GoodProducts (π C (· < x))`

`ι' := GoodProducts (C' C o)`

`v : ι → N := GoodProducts.eval (π C (· < o))`

-- TODO: does this require ho?
Then `SumEval C o` is the map `u` in the diagram below. It is linearly independent if and only if
`GoodProducts.eval C` is, see `linearIndependent_iff_sum`. The top row is the exact sequence given
by `succ_exact` and `succ_mono`. The left square commutes by `GoodProducts.square_commutes`.
```
0 --→ N --→ M --→  P
      ↑     ↑      ↑
     v|    u|      |
      ι → ι ⊕ ι' ← ι'
```
-/
def SumEval (o : I) : GoodProducts (π C (· < o)) ⊕ MaxProducts C o → LocallyConstant C ℤ :=
  Sum.elim (fun l ↦ l.1.eval C) (fun l ↦ l.1.eval C)

variable [SuccOrder I] (hsC : contained C (Order.succ o))

include hsC in
theorem linearIndependent_iff_sum :
    LinearIndependent ℤ (eval C) ↔ LinearIndependent ℤ (SumEval C o) := by
  rw [← linearIndependent_equiv (sum_equiv C hsC), SumEval, ← sum_equiv_comp_eval_eq_elim C hsC]

include hsC in
theorem span_sum : Set.range (eval C) = Set.range (Sum.elim
    (fun (l : GoodProducts (π C (· < o))) ↦ Products.eval C l.1)
    (fun (l : MaxProducts C o) ↦ Products.eval C l.1)) := by
  rw [← sum_equiv_comp_eval_eq_elim C hsC]
  exact (EquivLike.range_comp (e := sum_equiv C hsC) _).symm

theorem square_commutes : SumEval C o ∘ Sum.inl =
    ModuleCat.ofHom (πs C o) ∘ eval (π C (· < o)) := by
  ext l
  dsimp [SumEval]
  rw [← Products.eval_πs C (Products.prop_of_isGood  _ _ l.prop)]
  rfl

end GoodProducts

theorem swapTrue_eq_true (x : I → Bool) : SwapTrue o x o = true :=
  if_pos rfl

theorem mem_C'_eq_false : ∀ x, x ∈ C' C o → x o = false := by
  rintro x ⟨_, y, _, rfl⟩
  simp only [Proj, lt_self_iff_false, ite_false]

/-- `List.tail` as a `Products`. -/
def Products.Tail (l : Products I) : Products I :=
  ⟨l.val.tail, List.Chain'.tail l.prop⟩

-- TODO: the inhabited assumptions are redundant
theorem Products.max_eq_o_cons_tail [Inhabited I] (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = o) : l.val = o :: l.Tail.val := by
  rw [← List.cons_head!_tail hl, hlh]
  rfl

theorem Products.max_eq_o_cons_tail' [Inhabited I] (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = o) (hlc : List.Chain' (·>·) (o :: l.Tail.val)) :
    l = ⟨o :: l.Tail.val, hlc⟩ := by
  simp_rw [← max_eq_o_cons_tail l hl hlh]
  rfl

variable [SuccOrder I] (hsC : contained C (Order.succ o))

include hsC in
theorem GoodProducts.head!_eq_o_of_maxProducts [Inhabited I] (l : ↑(MaxProducts C o)) :
    l.val.val.head! = o := by
  apply ((Products.rel_head!_of_mem l.prop.2)).antisymm' (Order.le_of_lt_succ _)
  exact Products.prop_of_isGood_of_contained C _ l.prop.1 hsC l.val.val.head!
    (List.head!_mem_self (List.ne_nil_of_mem l.prop.2))

include hsC in
theorem GoodProducts.max_eq_o_cons_tail (l : MaxProducts C o) :
    l.val.val = o :: l.val.Tail.val :=
  have : Inhabited I := ⟨o⟩
  Products.max_eq_o_cons_tail l.val (List.ne_nil_of_mem l.prop.2)
    (head!_eq_o_of_maxProducts _ hsC l)

theorem Products.evalCons {I} [LinearOrder I] {C : Set (I → Bool)} {l : List I} {a : I}
    (hla : (a :: l).Chain' (· > ·)) : Products.eval C ⟨a :: l, hla⟩ =
    e C a * Products.eval C ⟨l, List.Chain'.sublist hla (List.tail_sublist (a :: l))⟩ := by
  simp only [eval.eq_1, List.map, List.prod_cons]

theorem Products.max_eq_eval [Inhabited I] (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = o) :
    Linear_CC' C hsC (l.eval C) = l.Tail.eval (C' C o) := by
  have hlc : (o :: l.Tail.val).Chain' (· > ·) := by
    rw [← max_eq_o_cons_tail l hl hlh]; exact l.prop
  rw [max_eq_o_cons_tail' l hl hlh hlc, Products.evalCons]
  ext x
  simp only [Linear_CC', Linear_CC'₁, LocallyConstant.comapₗ, Linear_CC'₀, Subtype.coe_eta,
    LinearMap.sub_apply, LinearMap.coe_mk, AddHom.coe_mk, LocallyConstant.sub_apply,
    LocallyConstant.coe_comap, LocallyConstant.coe_mul, ContinuousMap.coe_mk, Function.comp_apply,
    Pi.mul_apply]
  rw [CC'₁, CC'₀, Products.eval_eq, Products.eval_eq, Products.eval_eq]
  simp only [mul_ite, mul_one, mul_zero]
  have hi' : ∀ i, i ∈ l.Tail.val → (x.val i = SwapTrue o x.val i) := by
    intro i hi
    rw [SwapTrue, eq_comm, ite_eq_right_iff]
    rintro rfl
    exact ((List.Chain.rel hlc hi).ne rfl).elim
  have H : (∀ i, i ∈ l.Tail.val → x.val i = true) =
      (∀ i, i ∈ l.Tail.val → SwapTrue o x.val i = true) := by
    apply forall_congr; intro i; apply forall_congr; intro hi; rw [hi' i hi]
  simp only [H]
  split_ifs with h₁ h₂ h₃ <;> try (dsimp [e])
  · rw [if_pos (swapTrue_eq_true _), if_neg]
    · rfl
    · simp [mem_C'_eq_false C x x.prop, Bool.coe_false]
  · push_neg at h₂; obtain ⟨i, hi⟩ := h₂; exfalso; rw [hi' i hi.1] at hi; exact hi.2 (h₁ i hi.1)
  · push_neg at h₁; obtain ⟨i, hi⟩ := h₁; exfalso; rw [← hi' i hi.1] at hi; exact hi.2 (h₃ i hi.1)

namespace GoodProducts

theorem max_eq_eval (l : MaxProducts C o) :
    Linear_CC' C hsC (l.val.eval C) = l.val.Tail.eval (C' C o) :=
  have : Inhabited I := ⟨o⟩
  Products.max_eq_eval _ _ _ (List.ne_nil_of_mem l.prop.2) (head!_eq_o_of_maxProducts _ hsC l)

theorem max_eq_eval_unapply :
    Linear_CC' C hsC ∘ (fun l : MaxProducts C o ↦ Products.eval C l.val) =
    fun l ↦ l.val.Tail.eval (C' C o) := by
  ext1 l
  exact max_eq_eval ..

include hsC in
theorem chain'_cons_of_lt (l : MaxProducts C o)
    (q : Products I) (hq : q < l.val.Tail) :
    List.Chain' (fun x x_1 ↦ x > x_1) (o :: q.val) := by
  have : Inhabited I := ⟨o⟩
  rw [List.chain'_iff_pairwise]
  simp only [gt_iff_lt, List.pairwise_cons]
  refine ⟨fun a ha ↦ lt_of_le_of_lt (Products.rel_head!_of_mem ha) ?_,
    List.chain'_iff_pairwise.mp q.prop⟩
  refine lt_of_le_of_lt (Products.head!_le_of_lt hq (q.val.ne_nil_of_mem ha)) ?_
  by_cases hM : l.val.Tail.val = []
  · rw [Products.lt_iff_lex_lt, hM] at hq
    simp only [List.Lex.not_nil_right] at hq
  · have := l.val.prop
    rw [max_eq_o_cons_tail C hsC l, List.chain'_iff_pairwise] at this
    exact List.rel_of_pairwise_cons this (List.head!_mem_self hM)

include hsC in
theorem good_lt_maxProducts (q : GoodProducts (π C (· < o)))
    (l : MaxProducts C o) : List.Lex (· < ·) q.val.val l.val.val := by
  have : Inhabited I := ⟨o⟩
  by_cases h : q.val.val = []
  · rw [h, max_eq_o_cons_tail C hsC l]
    exact List.Lex.nil
  · rw [← List.cons_head!_tail h, max_eq_o_cons_tail C hsC l]
    exact List.Lex.rel <|
      Products.prop_of_isGood C _ q.prop q.val.val.head! (List.head!_mem_self h)

include hC hsC in
/--
Removing the leading `o` from a term of `MaxProducts C` yields a list which `isGood` with respect to
`C'`.
-/
theorem maxTail_isGood (l : MaxProducts C o)
    (h₁ : ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (· < o))))) :
    l.val.Tail.isGood (C' C o) := by
  have : Inhabited I := ⟨o⟩
  -- Write `l.Tail` as a linear combination of smaller products:
  intro h
  rw [Finsupp.mem_span_image_iff_linearCombination, ← max_eq_eval C hsC] at h
  obtain ⟨m, ⟨hmmem, hmsum⟩⟩ := h
  rw [Finsupp.linearCombination_apply] at hmsum

  -- Write the image of `l` under `Linear_CC'` as `Linear_CC'` applied to the linear combination
  -- above, with leading `term I ho`'s added to each term:
  have : Linear_CC' C hsC (l.val.eval C) = Linear_CC' C hsC
      (m.sum fun i a ↦ a • ((o :: i.1).map (e C)).prod) := by
    rw [← hmsum]
    simp only [map_finsupp_sum]
    apply Finsupp.sum_congr
    intro q hq
    rw [LinearMap.map_smul]
    rw [Finsupp.mem_supported] at hmmem
    have hx'' : q < l.val.Tail := hmmem hq
    have : ∃ (p : Products I), p.val ≠ [] ∧ p.val.head! = o ∧ q = p.Tail :=
      ⟨⟨o :: q.val, chain'_cons_of_lt C hsC l q hx''⟩,
        ⟨List.cons_ne_nil _ _, by simp only [List.head!_cons],
        by simp only [Products.Tail, List.tail_cons, Subtype.coe_eta]⟩⟩
    obtain ⟨p, hp⟩ := this
    rw [hp.2.2, ← Products.max_eq_eval C hsC p hp.1 hp.2.1]
    dsimp [Products.eval]
    rw [Products.max_eq_o_cons_tail p hp.1 hp.2.1]
    rfl
  have hse := succ_exact C hC hsC
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hse

  -- Rewrite `this` using exact sequence manipulations to conclude that a term is in the range of
  -- the linear map `πs`:
  rw [← LinearMap.sub_mem_ker_iff, ← hse] at this
  obtain ⟨n, hn⟩ := this
  rw [eq_sub_iff_add_eq] at hn
  have hn' : n ∈ _ := h₁ Submodule.mem_top
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn'
  obtain ⟨w, hc⟩ := hn'
  rw [← hc, map_finsupp_sum] at hn
  apply l.prop.1
  rw [← hn]

  -- Now we just need to prove that a sum of two terms belongs to a span:
  apply Submodule.add_mem <;> refine Submodule.finsupp_sum_mem _ _ _ _ fun q hq ↦ ?_
  · rw [LinearMap.map_smul]
    apply Submodule.smul_mem _ _ (Submodule.subset_span _)
    rw [eval, Products.eval_πs C (Products.prop_of_isGood _ _ q.prop)]
    refine ⟨q.val, ⟨?_, rfl⟩⟩
    simp only [Products.lt_iff_lex_lt, Set.mem_setOf_eq]
    exact good_lt_maxProducts C hsC q l
  · apply Submodule.smul_mem _ _ (Submodule.subset_span _)
    rw [Finsupp.mem_supported] at hmmem
    rw [← Finsupp.mem_support_iff] at hq
    refine ⟨⟨o :: q.val, chain'_cons_of_lt C hsC l q (hmmem hq)⟩, ⟨?_, rfl⟩⟩
    simp only [Products.lt_iff_lex_lt, Set.mem_setOf_eq]
    rw [max_eq_o_cons_tail C hsC l]
    exact List.Lex.cons ((Products.lt_iff_lex_lt q l.val.Tail).mp (hmmem hq))

/-- Given `l : MaxProducts C ho`, its `Tail` is a `GoodProducts (C' C ho)`. -/
noncomputable
def MaxToGood (h₁ : ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (· < o))))) :
    MaxProducts C o → GoodProducts (C' C o) :=
  fun l ↦ ⟨l.val.Tail, maxTail_isGood C hC hsC l h₁⟩

theorem maxToGood_injective
    (h₁ : ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (· < o))))) :
    (MaxToGood C hC hsC h₁).Injective := by
  apply fun m n h ↦ Subtype.ext (Subtype.ext ?_)
  rw [Subtype.ext_iff] at h
  dsimp [MaxToGood] at h
  rw [max_eq_o_cons_tail C hsC m, max_eq_o_cons_tail C hsC n, h]

include hC in
theorem linearIndependent_comp_of_eval
    (h₁ : ⊤ ≤ Submodule.span ℤ (Set.range (eval (π C (· < o))))) :
    LinearIndependent ℤ (eval (C' C o)) →
    LinearIndependent ℤ (ModuleCat.ofHom (Linear_CC' C hsC) ∘ SumEval C o ∘ Sum.inr) := by
  dsimp [SumEval, ModuleCat.ofHom]
  rw [max_eq_eval_unapply C hsC]
  exact fun h ↦ h.comp (MaxToGood C hC hsC h₁) (maxToGood_injective C hC hsC h₁)

end GoodProducts

end GoodProducts

end Successor

section Induction
/-!

## The induction

Here we put together the results of the sections `Zero`, `Limit` and `Successor` to prove the
predicate `P I o` holds for all ordinals `o`, and conclude with the main result:

* `GoodProducts.linearIndependent` which says that `GoodProducts C` is linearly independent when `C`
  is closed.

We also define

* `GoodProducts.Basis` which uses `GoodProducts.linearIndependent` and `GoodProducts.span` to
  define a basis for `LocallyConstant C ℤ`
-/

theorem GoodProducts.Pmin (o : I) (ho : IsMin o) : P o := fun C _ hsC ↦ by
  have : C ⊆ {fun _ ↦ false} := fun c hc ↦ by
    ext x; exact Bool.eq_false_iff.mpr fun ht ↦ ho.not_lt (hsC c hc x ht)
  rw [Set.subset_singleton_iff_eq] at this
  obtain rfl | rfl := this
  exacts [linearIndependentEmpty, linearIndependentSingleton]

-- TODO: o implicit?
theorem GoodProducts.Plimit [SuccOrder I] (o : I) (ho : Order.IsSuccLimit o) :
    (∀ o' < o, P o') → P o := by
  intro h C hC hsC
  rw [linearIndependent_iff_union_smaller C ho hsC]
  exact linearIndependent_iUnion_of_directed
    (Monotone.directed_le fun _ _ h ↦ GoodProducts.smaller_mono C h) fun ⟨o', ho'⟩ ↦
    (linearIndependent_iff_smaller _ _).mp (h o' ho' _ (isClosed_proj _ _ hC) (contained_proj _ _))

theorem GoodProducts.linearIndependentAux [SuccOrder I] [WellFoundedLT I] (μ : I) : P μ := by
  refine SuccOrder.limitRecOn μ Pmin (fun o _ h C hC hsC ↦ ?_) Plimit
  rw [linearIndependent_iff_sum C hsC]
  refine ModuleCat.linearIndependent_leftExact (succ_exact C hC hsC) ?_ ?_ (succ_mono C o hsC)
    (square_commutes C)
  · exact h _ (isClosed_proj C o hC) (contained_proj C o)
  · exact linearIndependent_comp_of_eval C hC hsC (span _ (isClosed_proj C o hC))
      (h (C' C o) (isClosed_C' C hC) (contained_C' C))

theorem GoodProducts.linearIndependent [SuccOrder I] [WellFoundedLT I] (hC : IsClosed C) :
    LinearIndependent ℤ (GoodProducts.eval C) :=
  sorry

/-- `GoodProducts C` as a `ℤ`-basis for `LocallyConstant C ℤ`. -/
noncomputable
def GoodProducts.Basis [SuccOrder I] [WellFoundedLT I] (hC : IsClosed C) :
    Basis (GoodProducts C) ℤ (LocallyConstant C ℤ) :=
  Basis.mk (GoodProducts.linearIndependent C hC) (GoodProducts.span C hC)

end Induction

variable {S : Profinite} {ι : S → I → Bool} (hι : IsClosedEmbedding ι)
include hι

/--
Given a profinite set `S` and a closed embedding `S → (I → Bool)`, the `ℤ`-module
`LocallyConstant C ℤ` is free.
-/
theorem Nobeling_aux [SuccOrder I] [WellFoundedLT I] :
    Module.Free ℤ (LocallyConstant S ℤ) := Module.Free.of_equiv'
  (Module.Free.of_basis <| GoodProducts.Basis _ hι.isClosed_range) (LocallyConstant.congrLeftₗ ℤ
    (.ofIsEmbedding ι hι.isEmbedding)).symm

end NobelingProof

variable (S : Profinite.{u})

open scoped Classical in
/-- The embedding `S → (I → Bool)` where `I` is the set of clopens of `S`. -/
noncomputable
def Nobeling.ι : S → ({C : Set S // IsClopen C} → Bool) := fun s C => decide (s ∈ C.1)

open scoped Classical in
/-- The map `Nobeling.ι` is a closed embedding. -/
theorem Nobeling.isClosedEmbedding : IsClosedEmbedding (Nobeling.ι S) := by
  apply Continuous.isClosedEmbedding
  · dsimp (config := { unfoldPartialApp := true }) [ι]
    refine continuous_pi ?_
    intro C
    rw [← IsLocallyConstant.iff_continuous]
    refine ((IsLocallyConstant.tfae _).out 0 3).mpr ?_
    rintro ⟨⟩
    · refine IsClopen.isOpen (isClopen_compl_iff.mp ?_)
      convert C.2
      ext x
      simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_singleton_iff,
        decide_eq_false_iff_not, not_not]
    · refine IsClopen.isOpen ?_
      convert C.2
      ext x
      simp only [Set.mem_preimage, Set.mem_singleton_iff, decide_eq_true_eq]
  · intro a b h
    by_contra hn
    obtain ⟨C, hC, hh⟩ := exists_isClopen_of_totally_separated hn
    apply hh.2 ∘ of_decide_eq_true
    dsimp (config := { unfoldPartialApp := true }) [ι] at h
    rw [← congr_fun h ⟨C, hC⟩]
    exact decide_eq_true hh.1

@[deprecated (since := "2024-10-26")]
alias Nobeling.embedding := Nobeling.isClosedEmbedding

end Profinite

open Profinite NobelingProof

/-- Nöbeling's theorem: the `ℤ`-module `LocallyConstant S ℤ` is free for every `S : Profinite` -/
instance LocallyConstant.freeOfProfinite (S : Profinite.{u}) :
    Module.Free ℤ (LocallyConstant S ℤ) := by
  obtain ⟨_, _⟩ := exists_wellOrder {C : Set S // IsClopen C}
  have := SuccOrder.ofLinearWellFoundedLT
  exact Nobeling_aux (ι := Nobeling.ι S) (Nobeling.isClosedEmbedding S)

set_option linter.style.longFile 1900
