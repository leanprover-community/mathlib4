/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Algebra.Category.ModuleCat.Free
import Mathlib.Algebra.Homology.ShortExact.Abelian
import Mathlib.Data.List.MinMax
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.SetTheory.Ordinal.Arithmetic
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Category.Profinite.Product
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.Topology.Separation

/-!

# Nöbeling's theorem

This file proves Nöbeling's theorem.

## Main result

- `Nobeling`: For `S : Profinite`, the `ℤ`-module `LocallyConstant S ℤ` is free.

## Proof idea

We follow the proof of theorem 5.4 in [scholze2019condensed], in which the idea is to embed `S` in
a product of `I` copies of `Bool`, choosing a well-ordering on `I` and using ordinal induction over
that well-order. Here we can let `I` be the set of clopen subsets of `S` since `S` is totally
separated.

For `i : I`, let `e S i : LocallyConstant (S : Set (I → Bool)) ℤ` denote the map
`fun f ↦ (if f.val i then 1 else 0)`.

The basis will consist of products `e S iᵣ * ⋯ * e S i₁` with `iᵣ > ⋯ > i₁` which cannot be written
as linear combinations of lexicographically smaller products.

What is proved by ordinal induction is that this set is linearly independent. The fact that it
spans can be proved directly.

## References

- [scholze2019condensed]: *Lectures on Condensed Mathematics*, 2019.

-/

universe u

namespace NobelingProof

variable {I : Type u} [Inhabited I] [LinearOrder I] [IsWellOrder I (·<·)] (C : Set (I → Bool))

section Projections

variable (J K L : I → Prop) [∀ i, Decidable (J i)] [∀ i, Decidable (K i)] [∀ i, Decidable (L i)]

/-- The projection mapping everything that satisfies `J i` to itself, and everything else to
    `false` -/
def Proj : (I → Bool) → (I → Bool) :=
  fun c i ↦ if J i then c i else false

@[simp]
theorem continuous_proj :
    Continuous (Proj J : (I → Bool) → (I → Bool)) := by
  dsimp [Proj]
  apply continuous_pi
  intro i
  split
  · apply continuous_apply
  · apply continuous_const

/-- The image of `Proj π J` -/
def _root_.Set.proj : Set (I → Bool) := (Proj J) '' C

/-- The restriction of `Proj π J` to a subset, mapping to its image. -/
@[simps!]
def ProjRestrict : C → C.proj J :=
  Set.MapsTo.restrict (Proj J) _ _ (Set.mapsTo_image _ _)

@[simp]
theorem continuous_projRestrict : Continuous (ProjRestrict C J) :=
  Continuous.restrict _ (continuous_proj _)

theorem surjective_projRestrict :
    Function.Surjective (ProjRestrict C J) := by
  intro x
  obtain ⟨y, hy⟩ := x.prop
  refine ⟨⟨y, hy.1⟩, Subtype.ext hy.2⟩

theorem proj_eq_self {x : I → Bool} (h : ∀ i, x i ≠ false → J i) : Proj J x = x := by
  ext i
  simp only [Proj, ite_eq_left_iff]
  contrapose!
  simpa only [ne_comm] using h i

theorem proj_prop_eq_self (hh : ∀ i x, x ∈ C → x i ≠ false → J i) : C.proj J = C := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, hy, rfl⟩ := h
    rwa [proj_eq_self]
    exact (hh · y hy)
  · refine ⟨x, h, ?_⟩
    rw [proj_eq_self]
    exact (hh · x h)

theorem proj_comp_of_subset (h : ∀ i, J i → K i) : (Proj J ∘ Proj K) =
    (Proj J : (I → Bool) → (I → Bool)) := by
  ext x i
  dsimp [Proj]
  split_ifs with hh hh' <;> aesop

theorem proj_eq_of_subset (h : ∀ i, J i → K i) : (C.proj K).proj J = C.proj J := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, hy, rfl⟩ := h
    obtain ⟨z, hz, rfl⟩ := hy
    suffices Proj J z = (Proj J ∘ Proj K) z by exact ⟨z, ⟨hz, this⟩⟩
    rw [proj_comp_of_subset J K h]
  · obtain ⟨y, hy, rfl⟩ := h
    dsimp [Set.proj]
    rw [← Set.image_comp]
    refine ⟨y, ⟨hy, ?_⟩⟩
    rw [proj_comp_of_subset J K h]

variable {J K L}

/-- A variant of `ProjRestrict` with domain of the form `C.proj K` -/
@[simps!]
def ProjRestricts (h : ∀ i, J i → K i) : C.proj K → C.proj J :=
  Homeomorph.setCongr (proj_eq_of_subset C J K h) ∘ ProjRestrict (C.proj K) J

@[simp]
theorem continuous_projRestricts (h : ∀ i, J i → K i) : Continuous (ProjRestricts C h) :=
  Continuous.comp (Homeomorph.continuous _) (continuous_projRestrict _ _)

theorem surjective_projRestricts (h : ∀ i, J i → K i) : Function.Surjective (ProjRestricts C h) :=
  (Homeomorph.surjective _).comp (surjective_projRestrict _ _)

variable (J) in
theorem projRestricts_eq_id : ProjRestricts C (fun i (h : J i) ↦ h) = id := by
  ext ⟨x, y, hy, rfl⟩ i
  simp (config := { contextual := true }) only [Set.proj, Proj, ProjRestricts_coe, id_eq, if_true]

theorem projRestricts_eq_comp (hJK : ∀ i, J i → K i) (hKL : ∀ i, K i → L i) :
    ProjRestricts C hJK ∘ ProjRestricts C hKL = ProjRestricts C (fun i ↦ hKL i ∘ hJK i) := by
  ext x i
  simp only [Set.proj, Proj, Function.comp_apply, ProjRestricts_coe]
  split_ifs with h hh <;> aesop

theorem projRestricts_comp_projRestrict (h : ∀ i, J i → K i) :
    ProjRestricts C h ∘ ProjRestrict C K = ProjRestrict C J := by
  ext x i
  simp only [Set.proj, Proj, Function.comp_apply, ProjRestricts_coe, ProjRestrict_coe]
  split_ifs with hh hh' <;> aesop

variable (J)

open Profinite ContinuousMap

/-- The objectwise map in the isomorphism `spanFunctor ≅ Profinite.indexFunctor`. -/
def iso_map : C(C.proj J, (IndexFunctor.obj C J)) :=
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

variable (K)

lemma iso_naturality (h : ∀ i, J i → K i) :
    iso_map C J ∘ ProjRestricts C h = IndexFunctor.map C h ∘ iso_map C K := by
  ext _ ⟨i, hi⟩
  exact if_pos hi

lemma cones_naturality :
    iso_map C J ∘ ProjRestrict C J = IndexFunctor.π_app C J := by
  ext _ i
  exact dif_pos i.prop

open CategoryTheory Limits Opposite

variable {C} (hC : IsCompact C)

/-- The functor from the poset of finsets of `I` to  `Profinite`, indexing the limit. -/
noncomputable
def spanFunctor :
    (Finset I)ᵒᵖ ⥤ Profinite.{u} where
  obj J := @Profinite.of (C.proj (· ∈ (unop J))) _
    (by rw [← isCompact_iff_compactSpace]; exact hC.image (continuous_proj _)) _ _
  map h := ⟨(ProjRestricts C (leOfHom h.unop)), continuous_projRestricts _ _⟩
  map_id J := by dsimp; simp_rw [projRestricts_eq_id C (· ∈ (unop J))]; rfl
  map_comp _ _ := by dsimp; congr; dsimp; rw [projRestricts_eq_comp]

/-- The natural isomorphism `spanFunctor ≅ Profinite.indexFunctor`. -/
noncomputable
def spanIsoIndex : spanFunctor hC ≅ indexFunctor hC := NatIso.ofComponents
  (fun J ↦ (Profinite.isoOfBijective (iso_map C (· ∈ unop J)) (iso_map_bijective C (· ∈ unop J))))
  (by
    intro ⟨J⟩ ⟨K⟩ ⟨⟨⟨f⟩⟩⟩
    ext x
    exact congr_fun (iso_naturality C (· ∈ K) (· ∈ J) f) x)

/-- The limit cone on `spanFunctor` -/
noncomputable
def spanCone : Cone (spanFunctor hC) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π :=
  { app := fun J ↦ ⟨ProjRestrict C (· ∈ unop J), continuous_projRestrict _ _⟩
    naturality := by
      intro X Y h
      simp only [Functor.const_obj_obj, Homeomorph.setCongr,
        Homeomorph.homeomorph_mk_coe, Functor.const_obj_map, Category.id_comp]
      congr
      rw [← projRestricts_comp_projRestrict C (leOfHom h.unop)]
      rfl }

/-- The isomorphism of cones `spanCone ≅ Profinite.indexCone` -/
noncomputable
def spanConeIsoIndex :
    (Cones.postcompose (spanIsoIndex hC).hom).obj (spanCone hC) ≅ indexCone hC :=
  Cones.ext (Iso.refl _) (by
    intro ⟨J⟩
    ext x
    exact congr_fun (cones_naturality C (· ∈ J)) x)

/-- `spanCone` is a limit cone. -/
noncomputable
def spanCone_isLimit : CategoryTheory.Limits.IsLimit (spanCone hC) :=
  (IsLimit.postcomposeHomEquiv (spanIsoIndex hC) (spanCone hC))
    (IsLimit.ofIsoLimit (indexCone_isLimit hC) (spanConeIsoIndex _).symm)

end Projections

section Products

/-- The locally constant map from `C` to `ℤ` whose `i`-th projection is given by 1 if
    `f.val i = true`, and 0 otherwise.  -/
def e (i : I) : LocallyConstant C ℤ where
  toFun := fun f ↦ (if f.val i then 1 else 0)
  isLocallyConstant := by
    rw [IsLocallyConstant.iff_continuous]
    exact (continuous_of_discreteTopology (f := fun (a : Bool) ↦ (if a then (1 : ℤ) else 0))).comp
      ((continuous_apply i).comp continuous_subtype_val)

/-- Formal products of the form `e C i₁ ··· e C iᵣ` with `i₁ > ··· > iᵣ`. -/
def Products (I : Type*) [LinearOrder I] := {l : List I // l.Chain' (·>·)}

namespace Products

noncomputable
instance : LinearOrder (Products I) :=
  inferInstanceAs (LinearOrder {l : List I // l.Chain' (·>·)})

@[simp]
theorem lt_iff_lex_lt (l m : Products I) : l < m ↔ List.Lex (·<·) l.val m.val := by
  cases l; cases m; rw [Subtype.mk_lt_mk]; exact Iff.rfl

/-- The evaluation of of a formal product. -/
def eval (l : Products I) := (l.1.map (e C)).prod

/-- The predicate on products defining the basis. -/
def isGood (l : Products I) : Prop :=
  l.eval C ∉ Submodule.span ℤ ((Products.eval C) '' {m | m < l})

theorem rel_head!_of_mem {i : I} {l : Products I} (hi : i ∈ l.val) : i ≤ l.val.head! :=
  List.Sorted.le_head! (List.chain'_iff_pairwise.mp l.prop) hi

theorem head!_le_of_lt {q l : Products I} (h : q < l) (hq : q.val ≠ []) :
    q.val.head! ≤ l.val.head! :=
  List.head!_le_of_lt l.val q.val ((List.lt_iff_lex_lt q.val l.val).mpr h) hq

end Products

/-- The type of good products. -/
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
    exact Submodule.subset_span ⟨a, ⟨h',rfl⟩⟩
  · rfl
  · exfalso; apply ha; rw [h]
    exact Submodule.subset_span ⟨b, ⟨h',rfl⟩⟩

/-- The image of the good products in the module `LocallyConstant C ℤ`. -/
def range := Set.range (GoodProducts.eval C)

/-- The type of good products is equivalent to its image. -/
noncomputable
def equiv_range : GoodProducts C ≃ range C :=
  Equiv.ofInjective (eval C) (injective C)

theorem equiv_toFun_eq_eval : (equiv_range C).toFun = Set.rangeFactorization (eval C) := by rfl

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
    simp only [ite_eq_right_iff]

theorem evalFacProp {l : Products I} (J : I → Prop)
    (h : ∀ a, a ∈ l.val → J a) [∀ j, Decidable (J j)] :
    l.eval (C.proj J) ∘ ProjRestrict C J = l.eval C := by
  ext x
  dsimp [ProjRestrict]
  rw [Products.eval_eq, Products.eval_eq]
  congr
  apply forall_congr; intro i
  apply forall_congr; intro hi
  simp [h i hi, Proj]

theorem evalFacPropsAux {l : Products I} (J K : I → Prop) (hJK : ∀ i, J i → K i)
    [∀ j, Decidable (J j)] [∀ j, Decidable (K j)] :
    l.eval (C.proj J) ∘ Homeomorph.setCongr (proj_eq_of_subset C J K hJK) =
    l.eval ((C.proj K).proj J) := by
  ext _
  simp only [Homeomorph.setCongr, Homeomorph.homeomorph_mk_coe, Function.comp_apply,
    Equiv.setCongr_apply, Products.eval_eq]

theorem evalFacProps {l : Products I} (J K : I → Prop)
    (h : ∀ a, a ∈ l.val → J a) [∀ j, Decidable (J j)] [∀ j, Decidable (K j)]
    (hJK : ∀ i, J i → K i) :
    l.eval (C.proj J) ∘ ProjRestricts C hJK = l.eval (C.proj K) := by
  dsimp only [ProjRestricts]
  rw [← Function.comp.assoc, evalFacPropsAux C J K hJK, ← evalFacProp (C.proj K) J h]

theorem prop_of_isGood  {l : Products I} (J : I → Prop) [∀ j, Decidable (J j)]
    (h : l.isGood (C.proj J)) : ∀ a, a ∈ l.val → J a := by
  intro i hi
  by_contra h'
  apply h
  suffices : eval (C.proj J) l = 0
  · rw [this]
    exact Submodule.zero_mem _
  ext ⟨_, ⟨_, ⟨_, rfl⟩⟩⟩
  rw [eval_eq, if_neg]
  · rfl
  · intro h
    specialize h i hi
    simp only [Proj, Bool.ite_eq_true_distrib, if_false_right_eq_and] at h
    exact h' h.1

instance : IsWellFounded (Products I) (·<·) := by
  have : (fun (l m : Products I) ↦ l < m) = (fun l m ↦ List.Lex (·<·) l.val m.val)
  · ext l m
    exact Products.lt_iff_lex_lt l m
  rw [this]
  dsimp [Products]
  have hflip : (·>· : I → I → Prop) = flip (·<· : I → I → Prop) := rfl
  rw [hflip]
  infer_instance

theorem eval_mem_span_goodProducts (l : Products I) :
    l.eval C ∈ Submodule.span ℤ (Set.range (GoodProducts.eval C)) := by
  let L : Products I → Prop := fun m ↦ m.eval C ∈ Submodule.span ℤ (Set.range (GoodProducts.eval C))
  suffices L l by assumption
  apply IsWellFounded.induction (·<· : Products I → Products I → Prop)
  intro l h
  dsimp
  by_cases hl : l.isGood C
  · apply Submodule.subset_span
    exact ⟨⟨l, hl⟩, rfl⟩
  · simp only [Products.isGood, not_not] at hl
    suffices : Products.eval C '' {m | m < l} ⊆ Submodule.span ℤ (Set.range (GoodProducts.eval C))
    · rw [← Submodule.span_le] at this
      exact this hl
    rintro a ⟨m, hm, rfl⟩
    exact h m hm

end Products

theorem GoodProducts.span_iff_products : ⊤ ≤ Submodule.span ℤ (Set.range (eval C)) ↔
    ⊤ ≤ Submodule.span ℤ (Set.range (Products.eval C)) := by
  refine ⟨fun h ↦ le_trans h (Submodule.span_mono (fun a ⟨b, hb⟩ ↦ ⟨b.val, hb⟩)), fun h ↦ ?_⟩
  refine le_trans h ?_
  rw [Submodule.span_le]
  rintro f ⟨l, rfl⟩
  exact Products.eval_mem_span_goodProducts C l

end Products

section Span
section Fin

variable (J : Finset I)

/-- The `ℤ`-linear map induced by precomposition of the projection `C → C.proj (· ∈ J)`. -/
noncomputable
def πJ : LocallyConstant (C.proj (· ∈ J)) ℤ →ₗ[ℤ] LocallyConstant C ℤ :=
  LocallyConstant.comapₗ ℤ _ (continuous_projRestrict C (· ∈ J))

theorem eval_eq_πJ (l : Products I) (hl : l.isGood (C.proj (· ∈ J))) :
    l.eval C = πJ C J (l.eval (C.proj (· ∈ J))) := by
  ext f
  simp only [πJ, LocallyConstant.comapₗ, LinearMap.coe_mk, AddHom.coe_mk,
    (continuous_projRestrict C (· ∈ J)), LocallyConstant.coe_comap, Function.comp_apply]
  exact (congr_fun (Products.evalFacProp C (· ∈ J) (Products.prop_of_isGood  C (· ∈ J) hl)) _).symm

/-- `C.proj (· ∈ J)` is finite for a finite set `J`. -/
noncomputable
instance : Fintype (C.proj (· ∈ J)) := by
  let f : C.proj (· ∈ J) → (J → Bool) := fun x j ↦ x.val j.val
  refine Fintype.ofInjective f ?_
  intro ⟨_, x, hx, rfl⟩ ⟨_, y, hy, rfl⟩ h
  ext i
  by_cases hi : i ∈ J
  · exact congrFun h ⟨i, hi⟩
  · simp only [Proj, if_neg hi]


open Classical in
/-- The Kronecker delta as a locally constant map from `C.proj (· ∈ J)` to `ℤ`. -/
noncomputable
def spanFinBasis (x : C.proj (· ∈ J)) : LocallyConstant (C.proj (· ∈ J)) ℤ where
  toFun := fun y ↦ if y = x then 1 else 0
  isLocallyConstant :=
    haveI : DiscreteTopology (C.proj (· ∈ J)) := discrete_of_t1_of_finite
    IsLocallyConstant.of_discrete _

open Classical in
theorem spanFinBasis.span : ⊤ ≤ Submodule.span ℤ (Set.range (spanFinBasis C J)) := by
  intro f _
  rw [Finsupp.mem_span_range_iff_exists_finsupp]
  use Finsupp.onFinset (Finset.univ) f.toFun (fun _ _ ↦ Finset.mem_univ _)
  ext x
  change LocallyConstant.evalₗ ℤ x _ = _
  simp only [zsmul_eq_mul, map_finsupp_sum, LocallyConstant.evalₗ_apply,
    LocallyConstant.coe_mul, Pi.mul_apply, spanFinBasis, LocallyConstant.coe_mk, mul_ite, mul_one,
    mul_zero, Finsupp.sum_ite_eq, Finsupp.mem_support_iff, ne_eq, ite_not]
  split_ifs with h <;> [exact h.symm; rfl]

/-- A list of locally constant maps whose product is `spanFinBasis C J x` (see
    `factors_prod_eq_basis`) -/
def factors (x : C.proj (· ∈ J)) : List (LocallyConstant (C.proj (· ∈ J)) ℤ) :=
  List.map (fun i ↦ if x.val i = true then e (C.proj (· ∈ J)) i else (1 - (e (C.proj (· ∈ J)) i)))
    (J.sort (·≥·))

theorem list_prod_apply (x : C) (l : List (LocallyConstant C ℤ)) :
    l.prod x = (l.map (LocallyConstant.evalMonoidHom x)).prod := by
  rw [← map_list_prod (LocallyConstant.evalMonoidHom x) l]
  rfl

theorem factors_prod_eq_basis_of_eq {x y : (Set.proj C fun x ↦ x ∈ J)} (h : y = x) :
    (factors C J x).prod y = 1 := by
  rw [list_prod_apply (C.proj (· ∈ J)) y _]
  apply List.prod_eq_one
  simp only [h, List.mem_map, LocallyConstant.evalMonoidHom, factors]
  rintro _ ⟨a, ⟨b, _, rfl⟩, rfl⟩
  dsimp
  split_ifs with hh
  · rw [e, LocallyConstant.coe_mk, if_pos hh]
  · rw [LocallyConstant.sub_apply, e, LocallyConstant.coe_mk, LocallyConstant.coe_mk, if_neg hh]
    simp only [LocallyConstant.toFun_eq_coe, LocallyConstant.coe_one, Pi.one_apply, sub_zero]

theorem e_mem_of_eq_true {x : (Set.proj C (· ∈ J))} {a : I} (hx : x.val a = true) :
    e (Set.proj C (· ∈ J)) a ∈ factors C J x := by
  rcases x with ⟨_, z, hz, rfl⟩
  simp only [factors, List.mem_map, Finset.mem_sort]
  refine ⟨a, ⟨?_, if_pos hx⟩⟩
  simp only [Proj, Bool.ite_eq_true_distrib, if_false_right_eq_and] at hx
  exact hx.1

theorem one_sub_e_mem_of_false {x y : (Set.proj C (· ∈ J))} {a : I} (ha : y.val a = true)
    (hx : x.val a = false) : 1 - e (Set.proj C (· ∈ J)) a ∈ factors C J x := by
  simp only [factors, List.mem_map, Finset.mem_sort]
  use a
  simp only [hx, ite_false, and_true]
  rcases y with ⟨_, z, hz, rfl⟩
  simp only [Proj, Bool.ite_eq_true_distrib, if_false_right_eq_and] at ha
  exact ha.1

theorem factors_prod_eq_basis_of_ne {x y : (Set.proj C (· ∈ J))} (h : y ≠ x) :
    (factors C J x).prod y = 0 := by
  rw [list_prod_apply (C.proj (· ∈ J)) y _]
  apply List.prod_eq_zero
  simp only [List.mem_map]
  obtain ⟨a, ha⟩ : ∃ a, y.val a ≠ x.val a
  · contrapose! h; ext; apply h
  cases hx : x.val a
  · rw [hx, ne_eq, Bool.not_eq_false] at ha
    refine ⟨1 - (e (C.proj (· ∈ J)) a), ⟨one_sub_e_mem_of_false _ _ ha hx, ?_⟩⟩
    rw [e, LocallyConstant.evalMonoidHom_apply, LocallyConstant.sub_apply,
      LocallyConstant.coe_one, Pi.one_apply, LocallyConstant.coe_mk, if_pos ha, sub_self]
  · refine ⟨e (C.proj (· ∈ J)) a, ⟨e_mem_of_eq_true _ _ hx, ?_⟩⟩
    rw [hx] at ha
    rw [LocallyConstant.evalMonoidHom_apply, e, LocallyConstant.coe_mk, if_neg ha]

theorem factors_prod_eq_basis (x : C.proj (· ∈ J)) :
    (factors C J x).prod = spanFinBasis C J x := by
  ext y
  dsimp [spanFinBasis]
  split_ifs with h <;> [exact factors_prod_eq_basis_of_eq _ _ h;
    exact factors_prod_eq_basis_of_ne _ _ h]

-- #7895
theorem Finset.sort_chain'_gt {α : Type*} [LinearOrder α] [DecidableRel (α := α) (·≥·)]
    (s : Finset α) : (s.sort (·≥·)).Chain' (·>·) := by
  rw [List.chain'_iff_pairwise]
  have hr : (·>· : α → α → Prop) = (fun a b ↦ a ≥ b ∧ a ≠ b)
  · ext a b
    rw [gt_iff_lt, lt_iff_le_and_ne]
    exact Iff.and Iff.rfl ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩
  rw [hr, List.pairwise_and_iff]
  refine ⟨List.chain'_iff_pairwise.mp ?_, Finset.sort_nodup _ _⟩
  rw [List.chain'_iff_pairwise]
  exact Finset.sort_sorted _ _

-- #7896
theorem _root_.List.Chain'.cons_of_le {a : I} {as m : List I}
    (ha : List.Chain' (· > ·) (a :: as)) (hm : List.Chain' (· > ·) m) (hmas : m ≤ as) :
    List.Chain' (· > ·) (a :: m) := by
  cases m with
  | nil => simp only [List.chain'_singleton]
  | cons b bs =>
    apply hm.cons
    cases as with
    | nil =>
      simp only [le_iff_lt_or_eq, or_false] at hmas
      exact (List.Lex.not_nil_right (·<·) _ hmas).elim
    | cons a' as =>
      rw [List.chain'_cons] at ha
      refine gt_of_gt_of_ge ha.1 ?_
      rw [le_iff_lt_or_eq] at hmas
      cases' hmas with hmas hmas
      · by_contra' hh
        rw [← not_le] at hmas
        apply hmas
        apply le_of_lt
        exact (List.lt_iff_lex_lt _ _).mp (List.lt.head _ _ hh)
      · simp only [List.cons.injEq] at hmas
        rw [ge_iff_le, le_iff_lt_or_eq]
        exact Or.inr hmas.1

-- #7897
theorem _root_.List.le_cons (a : I) {as m : List I} (hmas : m ≤ as) : a :: m ≤ a :: as := by
  rw [le_iff_lt_or_eq] at hmas ⊢
  refine hmas.imp ?_ (congr_arg _)
  intro hmas
  have haa : ¬(a < a) := gt_irrefl a
  exact (List.lt_iff_lex_lt _ _).mp
    (List.lt.tail haa haa ((List.lt_iff_lex_lt _ _).mpr hmas))

theorem GoodProducts.finsupp_sum_mem_span_eval {a : I} {as : List I}
    (ha : List.Chain' (· > ·) (a :: as)) {c : Products I →₀ ℤ}
    (hc : (c.support : Set (Products I)) ⊆ {m | m.val ≤ as}) :
    (Finsupp.sum c fun a_1 b ↦ e (C.proj (· ∈ J)) a * b • Products.eval (C.proj (· ∈ J)) a_1) ∈
      Submodule.span ℤ (Products.eval (C.proj (· ∈ J)) '' {m | m.val ≤ a :: as}) := by
  apply Submodule.finsupp_sum_mem
  intro m hm
  have hsm := (LinearMap.mulLeft ℤ (e (C.proj (· ∈ J)) a)).map_smul
  dsimp at hsm
  rw [hsm]
  apply Submodule.smul_mem
  apply Submodule.subset_span
  have hmas : m.val ≤ as
  · apply hc
    simpa only [Finset.mem_coe, Finsupp.mem_support_iff] using hm
  refine ⟨⟨a :: m.val, ha.cons_of_le m.prop hmas⟩, ⟨List.le_cons a hmas, ?_⟩⟩
  simp only [Products.eval, List.map, List.prod_cons]

theorem GoodProducts.spanFin : ⊤ ≤ Submodule.span ℤ (Set.range (eval (C.proj (· ∈ J)))) := by
  rw [span_iff_products]
  refine le_trans (spanFinBasis.span C J) ?_
  rw [Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  rw [← factors_prod_eq_basis]
  let l := J.sort (·≥·)
  dsimp [factors]
  suffices : l.Chain' (·>·) → (l.map (fun i ↦ if x.val i = true then e (C.proj (· ∈ J)) i
      else (1 - (e (C.proj (· ∈ J)) i)))).prod ∈
      Submodule.span ℤ ((Products.eval (C.proj (· ∈ J))) '' {m | m.val ≤ l})
  · exact Submodule.span_mono (Set.image_subset_range _ _) (this (Finset.sort_chain'_gt _))
  induction l with
  | nil =>
    intro _
    apply Submodule.subset_span
    exact ⟨⟨[], List.chain'_nil⟩,⟨Or.inl rfl, rfl⟩⟩
  | cons a as ih =>
    rw [List.map_cons, List.prod_cons]
    intro ha
    specialize ih (by rw [List.chain'_cons'] at ha; exact ha.2)
    rw [Finsupp.mem_span_image_iff_total] at ih
    simp only [Finsupp.mem_supported, Finsupp.total_apply] at ih
    obtain ⟨c, hc, hc'⟩ := ih
    rw [← hc']; clear hc'
    have hmap := fun g ↦ map_finsupp_sum (LinearMap.mulLeft ℤ (e (C.proj (· ∈ J)) a)) c g
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
    (f : LocallyConstant C ℤ) : ∃ (J : Finset I)
    (g : LocallyConstant (C.proj (· ∈ J)) ℤ), f = g.comap (ProjRestrict C (· ∈ J)) := by
  obtain ⟨J, g, h⟩ := @Profinite.exists_locallyConstant (Finset I)ᵒᵖ _ _ _
    (spanCone hC.isCompact) _
    (spanCone_isLimit hC.isCompact) f
  exact ⟨(Opposite.unop J), g, h⟩

theorem GoodProducts.span (hC : IsClosed C) :
    ⊤ ≤ Submodule.span ℤ (Set.range (eval C)) := by
  rw [span_iff_products]
  intro f _
  obtain ⟨K, f', rfl⟩ : ∃ K f', f = πJ C K f' := fin_comap_jointlySurjective C hC f
  refine Submodule.span_mono ?_ <| Submodule.apply_mem_span_image_of_mem_span (πJ C K) <|
    spanFin C K (Submodule.mem_top : f' ∈ ⊤)
  rintro l ⟨y, ⟨m, rfl⟩, rfl⟩
  exact ⟨m.val, eval_eq_πJ C K m.val m.prop⟩

end Span

variable (I)

/-- A term of `I` regarded as an ordinal. -/
def ord (i : I) : Ordinal := Ordinal.typein ((·<·) : I → I → Prop) i

/-- An ordinal regarded as a term of `I`. -/
noncomputable
def term {o : Ordinal} (ho : o < Ordinal.type ((·<·) : I → I → Prop)) : I :=
  Ordinal.enum ((·<·) : I → I → Prop) o ho

variable {I}

theorem term_ord_aux {i : I} (ho : ord I i < Ordinal.type ((·<·) : I → I → Prop)) :
    term I ho = i := by
  simp only [term, ord, Ordinal.enum_typein]

@[simp]
theorem ord_term_aux {o : Ordinal} (ho : o < Ordinal.type ((·<·) : I → I → Prop)) :
    ord I (term I ho) = o := by
  simp only [ord, term, Ordinal.typein_enum]

theorem ord_term {o : Ordinal} (ho : o < Ordinal.type ((·<·) : I → I → Prop)) (i : I) :
    ord I i = o ↔ term I ho = i := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · subst h
    exact term_ord_aux ho
  · subst h
    exact ord_term_aux ho

/-- A predicate saying that `C` is "small" enough to satisfy the inductive hypothesis. -/
def contained (o : Ordinal) : Prop := ∀ f, f ∈ C → ∀ (i : I), f i = true → ord I i < o

theorem Products.prop_of_isGood_of_contained  {l : Products I} (o : Ordinal) (h : l.isGood C)
    (hsC : contained C o) (i : I) (hi : i ∈ l.val) : ord I i < o := by
  by_contra h'
  apply h
  suffices : eval C l = 0
  · simp [this, Submodule.zero_mem]
  ext x
  simp only [eval_eq, LocallyConstant.coe_zero, Pi.zero_apply, ite_eq_right_iff, one_ne_zero]
  contrapose! h'
  exact hsC x.val x.prop i (h'.1 i hi)

section Zero

instance : Subsingleton (LocallyConstant (∅ : Set (I → Bool)) ℤ) :=
  subsingleton_iff.mpr (fun _ _ ↦ LocallyConstant.ext isEmptyElim)

instance : IsEmpty { l // Products.isGood (∅ : Set (I → Bool)) l } :=
  isEmpty_iff.mpr fun ⟨l, hl⟩ ↦ hl <| by
    rw [subsingleton_iff.mp inferInstance (Products.eval ∅ l) 0]
    exact Submodule.zero_mem _

theorem GoodProducts.linearIndependentEmpty :
    LinearIndependent ℤ (eval (∅ : Set (I → Bool))) := linearIndependent_empty_type

/-- The empty list as a `Products` -/
def Products.nil : Products I := ⟨[], by simp only [List.chain'_nil]⟩

theorem Products.lt_nil_empty : { m : Products I | m < Products.nil } = ∅ := by
  ext ⟨m, hm⟩
  refine ⟨fun h ↦ ?_, by tauto⟩
  simp only [Set.mem_setOf_eq, lt_iff_lex_lt, nil, List.Lex.not_nil_right] at h

instance {α : Type*} [TopologicalSpace α] [Inhabited α] : Nontrivial (LocallyConstant α ℤ) := by
  refine ⟨0, 1, fun h ↦ ?_⟩
  apply @zero_ne_one ℤ
  exact FunLike.congr_fun h default

theorem Products.isGood_nil : Products.isGood ({fun _ ↦ false} : Set (I → Bool)) Products.nil:= by
  intro h
  simp only [Products.lt_nil_empty, Products.eval, List.map, List.prod_nil, Set.image_empty,
    Submodule.span_empty, Submodule.mem_bot, one_ne_zero] at h

theorem Products.span_nil_eq_top :
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
    have he : {Products.nil} ⊆ {m | m < ⟨l,hl⟩}
    · simpa only [Products.nil, Products.lt_iff_lex_lt, Set.singleton_subset_iff, Set.mem_setOf_eq]
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
  simp [LocallyConstant.ext_iff] at h ⊢
  exact h x

theorem GoodProducts.linearIndependentSingleton :
    LinearIndependent ℤ (eval ({fun _ ↦ false} : Set (I → Bool))) := by
  refine linearIndependent_unique (eval ({fun _ ↦ false} : Set (I → Bool))) ?_
  simp only [eval, Products.eval, List.map, List.prod_nil, ne_eq, one_ne_zero, not_false_eq_true]

end Zero

section Maps

theorem contained_eq_proj (o : Ordinal) (h : contained C o) :
    C = C.proj (ord I · < o) := by
  have := proj_prop_eq_self C (ord I · < o)
  simp [Set.proj, Bool.not_eq_false] at this
  exact (this (fun i x hx ↦ h x hx i)).symm

theorem isClosed_proj (o : Ordinal) (hC : IsClosed C) : IsClosed (C.proj (ord I · < o)) :=
  (continuous_proj (ord I · < o)).isClosedMap C hC

theorem contained_proj (o : Ordinal) : contained (C.proj (ord I · < o)) o := by
  intro x ⟨_, ⟨_, h⟩⟩ j hj
  dsimp [Proj] at h
  simp only [← congr_fun h j, Bool.ite_eq_true_distrib, if_false_right_eq_and] at hj
  exact hj.1

/-- The `ℤ`-linear map induced by precomposition of the projection `C → C.proj (ord I · < o)`. -/
@[simps!]
noncomputable
def πs (o : Ordinal) : LocallyConstant (C.proj (ord I · < o)) ℤ →ₗ[ℤ] LocallyConstant C ℤ :=
  LocallyConstant.comapₗ ℤ (ProjRestrict C (ord I · < o)) (continuous_projRestrict _ _)

theorem coe_πs (o : Ordinal) (f : LocallyConstant (C.proj (ord I · < o)) ℤ) :
    πs C o f = f ∘ ProjRestrict C (ord I · < o) := by
  simp only [πs_apply, continuous_projRestrict, LocallyConstant.coe_comap]

theorem injective_πs (o : Ordinal) : Function.Injective (πs C o) :=
  LocallyConstant.comap_injective _ (continuous_projRestrict _ _) (surjective_projRestrict _ _)

/-- The `ℤ`-linear map induced by precomposition of the projection
    `C.proj (ord I · < o₂) → C.proj (ord I · < o₁)` for `o₁ ≤ o₂`. -/
@[simps!]
noncomputable
def πs' {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) :
    LocallyConstant (C.proj (ord I · < o₁)) ℤ →ₗ[ℤ] LocallyConstant (C.proj (ord I · < o₂)) ℤ :=
  LocallyConstant.comapₗ ℤ (ProjRestricts C (fun _ hh ↦ lt_of_lt_of_le hh h))
    (continuous_projRestricts _ _)

theorem coe_πs' {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) (f : LocallyConstant (C.proj (ord I · < o₁)) ℤ) :
    (πs' C h f).toFun = f.toFun ∘ (ProjRestricts C (fun _ hh ↦ lt_of_lt_of_le hh h)) := by
  simp only [πs'_apply, LocallyConstant.toFun_eq_coe, continuous_projRestricts,
    LocallyConstant.coe_comap]

theorem injective_πs' {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂) : Function.Injective (πs' C h) :=
  LocallyConstant.comap_injective _ (continuous_projRestricts _ _) (surjective_projRestricts _ _)

end Maps

section ProductsFactorisation

namespace Products

-- #7899
theorem _root_.List.Sorted.lt_iff_head!_lt {l : List I} (o : Ordinal) (hl : l.Sorted (· > ·)) :
    (l ≠ [] → Ordinal.typein (· < ·) l.head! < o) ↔ ∀ i ∈ l, Ordinal.typein (· < ·) i < o := by
  refine ⟨fun h _ ha ↦ lt_of_le_of_lt ?_ (h (List.ne_nil_of_mem ha)),
    fun h hn ↦ h l.head! (List.head!_mem_self hn)⟩
  simp only [Ordinal.typein_le_typein, not_lt]
  exact hl.le_head! ha

-- #7899
theorem _root_.List.Sorted.lt_ord_of_lt {l m : List I} {o : Ordinal} (hl : l.Sorted (· > ·))
    (hm : m.Sorted (· > ·)) (hmltl : m < l) (hlt : ∀ i ∈ l, Ordinal.typein (· < ·) i < o) :
    ∀ i ∈ m, Ordinal.typein (· < ·) i < o := by
  rw [← List.Sorted.lt_iff_head!_lt o hl] at hlt
  rw [← List.Sorted.lt_iff_head!_lt o hm]
  intro hm
  replace hmltl : List.Lex (· < ·) m l := hmltl
  by_cases hl : l = []
  · rw [hl] at hmltl
    simp only [List.Lex.not_nil_right] at hmltl
  · suffices hml : m.head! ≤ l.head! by refine lt_of_le_of_lt ?_ (hlt hl); simpa
    rw [← List.cons_head!_tail hl] at hmltl
    rw [← List.cons_head!_tail hm] at hmltl
    by_contra hn
    simp only [not_le] at hn
    exact List.Lex.isAsymm.aux _ _ _ (List.Lex.rel hn) hmltl

theorem lt_ord_of_lt {l m : Products I} {o : Ordinal} (h₁ : m < l)
    (h₂ : ∀ i ∈ l.val, ord I i < o) : ∀ i ∈ m.val, ord I i < o :=
  List.Sorted.lt_ord_of_lt (List.chain'_iff_pairwise.mp l.2) (List.chain'_iff_pairwise.mp m.2) h₁ h₂

theorem eval_πs {l : Products I} {o : Ordinal} (hlt : ∀ i ∈ l.val, ord I i < o) :
    πs C o (l.eval (C.proj (ord I · < o))) = l.eval C := by
  simpa only [← LocallyConstant.coe_inj, πs_apply, continuous_projRestrict,
    LocallyConstant.coe_comap] using evalFacProp C (ord I · < o) hlt

theorem eval_πs' {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hlt : ∀ i ∈ l.val, ord I i < o₁) :
    πs' C h (l.eval (C.proj (ord I · < o₁))) = l.eval (C.proj (ord I · < o₂)) := by
  rw [← LocallyConstant.coe_inj, ← LocallyConstant.toFun_eq_coe]
  simp only [πs'_apply, LocallyConstant.toFun_eq_coe, continuous_projRestricts,
    LocallyConstant.coe_comap]
  exact evalFacProps C (fun (i : I) ↦ ord I i < o₁) (fun (i : I) ↦ ord I i < o₂) hlt _

theorem eval_πs_image {l : Products I} {o : Ordinal}
    (hl : ∀ i ∈ l.val, ord I i < o) : eval C '' { m | m < l } =
    (πs C o) '' (eval (C.proj (ord I · < o)) '' { m | m < l }) := by
  ext f
  simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs C (lt_ord_of_lt hm hl)]

theorem eval_πs_image' {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : ∀ i ∈ l.val, ord I i < o₁) : eval (C.proj (ord I · < o₂)) '' { m | m < l } =
    (πs' C h) '' (eval (C.proj (ord I · < o₁)) '' { m | m < l }) := by
  ext f
  simp only [Set.mem_image, Set.mem_setOf_eq, exists_exists_and_eq_and]
  apply exists_congr; intro m
  apply and_congr_right; intro hm
  rw [eval_πs' C h (lt_ord_of_lt hm hl)]

theorem head_lt_ord_of_isGood {l : Products I} {o : Ordinal}
    (h : l.isGood (C.proj (ord I · < o))) (hn : l.val ≠ []) : ord I (l.val.head!) < o :=
  prop_of_isGood C (ord I · < o) h l.val.head! (List.head!_mem_self hn)

theorem isGood_mono {l : Products I} {o₁ o₂ : Ordinal} (h : o₁ ≤ o₂)
    (hl : l.isGood (C.proj (ord I · < o₁))) : l.isGood (C.proj (ord I · < o₂)) := by
  intro hl'
  apply hl
  rwa [eval_πs_image' C h (prop_of_isGood  C _ hl), ← eval_πs' C h (prop_of_isGood  C _ hl),
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C h)] at hl'

end Products

end ProductsFactorisation

section Smaller

namespace GoodProducts

/-- The image of the `GoodProducts` for `C.proj (ord I · < o)` in `LocallyConstant C ℤ` -/
def smaller (o : Ordinal) : Set (LocallyConstant C ℤ) :=
  (πs C o) '' (range (C.proj (ord I · < o)))

/-- The map from the image of the `GoodProducts` in `LocallyConstant (C.proj (ord I · < o)) ℤ`
    to `smaller C o` -/
noncomputable
def range_equiv_smaller_toFun (o : Ordinal) (x : range (C.proj (ord I · < o))) : smaller C o :=
  ⟨πs C o ↑x, x.val, x.property, rfl⟩

theorem range_equiv_smaller_toFun_bijective (o : Ordinal) :
    Function.Bijective (range_equiv_smaller_toFun C o) := by
  dsimp [range_equiv_smaller_toFun]
  refine ⟨fun a b hab ↦ ?_, fun ⟨a, b, hb⟩ ↦ ?_⟩
  · ext1
    simp only [Subtype.mk.injEq] at hab
    exact injective_πs C o hab
  · use ⟨b, hb.1⟩
    simpa only [Subtype.mk.injEq] using hb.2

/-- The equivalence from the image of the `GoodProducts` in
    `LocallyConstant (C.proj (ord I · < o)) ℤ` to `smaller C o` -/
noncomputable
def range_equiv_smaller (o : Ordinal) : range (C.proj (ord I · < o)) ≃ smaller C o :=
  Equiv.ofBijective (range_equiv_smaller_toFun C o) (range_equiv_smaller_toFun_bijective C o)

theorem smaller_factorization (o : Ordinal) :
    (fun (p : smaller C o) ↦ p.1) ∘ (range_equiv_smaller C o).toFun =
    (πs C o) ∘ (fun (p : range (C.proj (ord I · < o))) ↦ p.1) := by rfl

theorem linearIndependent_iff_smaller (o : Ordinal) :
    LinearIndependent ℤ (GoodProducts.eval (C.proj (ord I · < o))) ↔
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
      Function.comp.assoc, projRestricts_comp_projRestrict C _, coe_πs]
    rfl

end GoodProducts

end Smaller

section Limit

variable {o : Ordinal} (ho : o.IsLimit) (hsC : contained C o)

theorem Products.limitOrdinal (l : Products I) : l.isGood (C.proj (ord I · < o)) ↔
    ∃ (o' : Ordinal), o' < o ∧ l.isGood (C.proj (ord I · < o')) := by
  refine ⟨fun h ↦ ?_, fun ⟨o', ⟨ho', hl⟩⟩ ↦ isGood_mono C (le_of_lt ho') hl⟩
  use Finset.sup l.val.toFinset (fun a ↦ Order.succ (ord I a))
  have ha : ⊥ < o := by rw [Ordinal.bot_eq_zero, Ordinal.pos_iff_ne_zero]; exact ho.1
  have hslt : Finset.sup l.val.toFinset (fun a ↦ Order.succ (ord I a)) < o
  · simp only [Finset.sup_lt_iff ha, List.mem_toFinset]
    exact fun b hb ↦ ho.2 _ (prop_of_isGood C (ord I · < o) h b hb)
  refine ⟨hslt, fun he ↦ h ?_⟩
  have hlt : ∀ i ∈ l.val, ord I i < Finset.sup l.val.toFinset (fun a ↦ Order.succ (ord I a))
  · intro i hi
    simp only [Finset.lt_sup_iff, List.mem_toFinset, Order.lt_succ_iff]
    exact ⟨i, hi, le_rfl⟩
  rwa [eval_πs_image' C (le_of_lt hslt) hlt, ← eval_πs' C (le_of_lt hslt) hlt,
    Submodule.apply_mem_span_image_iff_mem_span (injective_πs' C _)]

theorem GoodProducts.union : range C = ⋃ (e : {o' // o' < o}), (smaller C e.val) := by
  ext p
  simp only [smaller, range, Set.mem_iUnion, Set.mem_image, Set.mem_range, Subtype.exists]
  refine ⟨fun hp ↦ ?_, fun hp ↦ ?_⟩
  · obtain ⟨l, hl, rfl⟩ := hp
    rw [contained_eq_proj C o hsC, Products.limitOrdinal C ho] at hl
    obtain ⟨o', ho'⟩ := hl
    refine ⟨o', ho'.1, eval (C.proj (ord I · < o')) ⟨l, ho'.2⟩, ⟨l, ho'.2, rfl⟩, ?_⟩
    exact Products.eval_πs C (Products.prop_of_isGood  C _ ho'.2)
  · obtain ⟨o', h, _, ⟨l, hl, rfl⟩, rfl⟩ := hp
    refine ⟨l, ?_, (Products.eval_πs C (Products.prop_of_isGood  C _ hl)).symm⟩
    rw [contained_eq_proj C o hsC]
    exact Products.isGood_mono C (le_of_lt h) hl

/-- The image of the `GoodProducts` in `C` is equivalent to the union of `smaller C o'` over all
    ordinals `o' < o`. -/
def GoodProducts.range_equiv : range C ≃ ⋃ (e : {o' // o' < o}), (smaller C e.val) :=
  Equiv.Set.ofEq (union C ho hsC)

theorem GoodProducts.range_equiv_factorization :
    (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) ∘ (range_equiv C ho hsC).toFun =
    (fun (p : range C) ↦ (p.1 : LocallyConstant C ℤ)) := rfl

theorem GoodProducts.linearIndependent_iff_union_smaller {o : Ordinal} (ho : o.IsLimit)
    (hsC : contained C o) : LinearIndependent ℤ (GoodProducts.eval C) ↔
    LinearIndependent ℤ (fun (p : ⋃ (e : {o' // o' < o}), (smaller C e.val)) ↦ p.1) := by
  rw [GoodProducts.linearIndependent_iff_range, ← range_equiv_factorization C ho hsC]
  exact linearIndependent_equiv (range_equiv C ho hsC)

end Limit

section Successor

variable {o : Ordinal} (hC : IsClosed C) (hsC : contained C (Order.succ o))
  (ho : o < Ordinal.type (·<· : I → I → Prop))

section ExactSequence

/-- The subset of `C` consisting of those elements whose `o`-th entry is `false`. -/
def C0 := C ∩ {f | f (term I ho) = false}

/-- The subset of `C` consisting of those elements whose `o`-th entry is `true`. -/
def C1 := C ∩ {f | f (term I ho) = true}

theorem isClosed_C0 : IsClosed (C0 C ho) := by
  refine hC.inter ?_
  have h : Continuous (fun (f : I → Bool) ↦ f (term I ho)) := continuous_apply (term I ho)
  exact IsClosed.preimage h (s := {false}) (isClosed_discrete _)

theorem isClosed_C1 : IsClosed (C1 C ho) := by
  refine hC.inter ?_
  have h : Continuous (fun (f : I → Bool) ↦ f (term I ho)) := continuous_apply (term I ho)
  exact IsClosed.preimage h (s := {true}) (isClosed_discrete _)

theorem contained_C1 : contained ((C1 C ho).proj (ord I · < o)) o :=
  contained_proj _ _

theorem union_C0C1_eq : (C0 C ho) ∪ (C1 C ho) = C := by
  ext x
  simp only [C0, C1, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq,
    ← and_or_left, and_iff_left_iff_imp, Bool.dichotomy (x (term I ho)), implies_true]

/-- The intersection of `C0` and the projection of `C1`. We will apply the inductive hypothesis to
    this set. -/
def C' := C0 C ho ∩ (C1 C ho).proj (ord I · < o)

theorem isClosed_C' : IsClosed (C' C ho) :=
  IsClosed.inter (isClosed_C0 _ hC _) (isClosed_proj _ _ (isClosed_C1 _ hC _))

theorem contained_C' : contained (C' C ho) o := fun f hf i hi ↦ contained_C1 C ho f hf.2 i hi

variable (o)

/-- Swapping the `o`-th coordinate to `true`. -/
noncomputable
def SwapTrue : (I → Bool) → I → Bool :=
  fun f i ↦ if ord I i = o then true else f i

theorem continuous_swapTrue  :
    Continuous (SwapTrue o : (I → Bool) → I → Bool) := by
  dsimp [SwapTrue]
  apply continuous_pi
  intro i
  apply Continuous.comp'
  · apply continuous_bot
  · apply continuous_apply

variable {o}

theorem swapTrue_mem_C1 (f : (C1 C ho).proj (ord I · < o)) :
    SwapTrue o f.val ∈ C1 C ho := by
  obtain ⟨f, g, hg, rfl⟩ := f
  convert hg
  dsimp [SwapTrue]
  ext i
  split_ifs with h
  · rw [ord_term ho] at h
    simpa only [← h] using hg.2.symm
  · simp only [Proj, ite_eq_left_iff, not_lt, @eq_comm _ false, ← Bool.not_eq_true]
    specialize hsC g hg.1 i
    intro h'
    contrapose! hsC
    exact ⟨hsC, Order.succ_le_of_lt (h'.lt_of_ne' h)⟩

/-- The first way to map `C'` into `C`. -/
def CC'₀ : C' C ho → C := fun g ↦ ⟨g.val,g.prop.1.1⟩

/-- The second way to map `C'` into `C`. -/
noncomputable
def CC'₁ : C' C ho → C :=
  fun g ↦ ⟨SwapTrue o g.val, (swapTrue_mem_C1 C hsC ho ⟨g.val,g.prop.2⟩).1⟩

theorem continuous_CC'₀ : Continuous (CC'₀ C ho) := Continuous.subtype_mk continuous_subtype_val _

theorem continuous_CC'₁ : Continuous (CC'₁ C hsC ho) :=
  Continuous.subtype_mk (Continuous.comp (continuous_swapTrue o) continuous_subtype_val) _

/-- The `ℤ`-linear map induced by precomposing with `CC'₀` -/
noncomputable
def Linear_CC'₀ : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C ho) ℤ :=
  LocallyConstant.comapₗ ℤ (CC'₀ C ho) (continuous_CC'₀ C ho)

/-- The `ℤ`-linear map induced by precomposing with `CC'₁` -/
noncomputable
def Linear_CC'₁ : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C ho) ℤ :=
  LocallyConstant.comapₗ ℤ (CC'₁ C hsC ho) (continuous_CC'₁ C hsC ho)

/-- The difference between `Linear_CC'₁` and `Linear_CC'₀`. -/
noncomputable
def Linear_CC' : LocallyConstant C ℤ →ₗ[ℤ] LocallyConstant (C' C ho) ℤ :=
  Linear_CC'₁ C hsC ho - Linear_CC'₀ C ho

theorem CC_comp_zero : ∀ y, (Linear_CC' C hsC ho) ((πs C o) y) = 0 := by
  intro y
  ext x
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁, LocallyConstant.sub_apply]
  simp only [continuous_CC'₀, continuous_CC'₁, LocallyConstant.coe_comap, continuous_projRestrict,
    Function.comp_apply, sub_eq_zero]
  congr 1
  ext i
  dsimp [CC'₀, CC'₁, ProjRestrict, Proj]
  apply if_ctx_congr Iff.rfl _ (fun _ ↦ rfl)
  simp only [SwapTrue, ite_eq_right_iff]
  intro h₁ h₂
  exact (h₁.ne h₂).elim

theorem C0_projOrd {x : I → Bool} (hx : x ∈ C0 C ho) : Proj (ord I · < o) x = x := by
  ext i
  simp only [Proj, Set.mem_setOf, ite_eq_left_iff, not_lt]
  intro hi
  rw [le_iff_lt_or_eq] at hi
  cases' hi with hi hi
  · specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true, Order.succ_le_iff] at hsC
    exact (hsC hi).symm
  · simp only [C0, Set.mem_inter_iff, Set.mem_setOf_eq] at hx
    rw [eq_comm, ord_term ho] at hi
    rw [← hx.2, hi]

theorem C1_projOrd {x : I → Bool} (hx : x ∈ C1 C ho) : SwapTrue o (Proj (ord I · < o) x) = x := by
  ext i
  dsimp [SwapTrue, Proj]
  split_ifs with hi h
  · rw [ord_term ho] at hi
    rw [← hx.2, hi]
  · rfl
  · simp only [not_lt] at h
    have h' : o < ord I i := lt_of_le_of_ne h (Ne.symm hi)
    specialize hsC x hx.1 i
    rw [← not_imp_not] at hsC
    simp only [not_lt, Bool.not_eq_true, Order.succ_le_iff] at hsC
    exact (hsC h').symm

open Classical in
theorem CC_exact {f : LocallyConstant C ℤ} (hf : Linear_CC' C hsC ho f = 0) :
    ∃ y, πs C o y = f := by
  dsimp [Linear_CC', Linear_CC'₀, Linear_CC'₁] at hf
  simp only [sub_eq_zero, ← LocallyConstant.coe_inj, LocallyConstant.coe_comap,
    continuous_CC'₀, continuous_CC'₁] at hf
  let C₀C : C0 C ho → C := fun x ↦ ⟨x.val, x.prop.1⟩
  have h₀ : Continuous C₀C := Continuous.subtype_mk continuous_induced_dom _
  let C₁C : (C1 C ho).proj (ord I · < o) → C :=
    fun x ↦ ⟨SwapTrue o x.val, (swapTrue_mem_C1 C hsC ho x).1⟩
  have h₁ : Continuous C₁C := Continuous.subtype_mk
    ((continuous_swapTrue o).comp continuous_subtype_val) _
  refine ⟨LocallyConstant.piecewise' ?_ (isClosed_C0 C hC ho)
      (isClosed_proj _ o (isClosed_C1 C hC ho)) (f.comap C₀C) (f.comap C₁C) ?_, ?_⟩
  · rintro _ ⟨y, hyC, rfl⟩
    simp only [Set.mem_union, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    rw [← union_C0C1_eq C ho] at hyC
    refine hyC.imp (fun hyC ↦ ?_) (fun hyC ↦ ⟨y, hyC, rfl⟩)
    rwa [C0_projOrd C hsC ho hyC]
  · intro x hx
    simpa only [h₀, h₁, LocallyConstant.coe_comap] using (congrFun hf ⟨x, hx⟩).symm
  · ext ⟨x, hx⟩
    rw [← union_C0C1_eq C ho] at hx
    cases' hx with hx₀ hx₁
    · have hx₀' : ProjRestrict C (ord I · < o) ⟨x, hx⟩ = x
      · simpa only [ProjRestrict, Set.MapsTo.val_restrict_apply] using C0_projOrd C hsC ho hx₀
      simp only [hx₀', hx₀, h₀, LocallyConstant.piecewise'_apply_left, LocallyConstant.coe_comap,
        Function.comp_apply, πs_apply, continuous_projRestrict]
    · have hx₁' : (ProjRestrict C (ord I · < o) ⟨x, hx⟩).val ∈ (C1 C ho).proj (ord I · < o)
      · simpa only [ProjRestrict, Set.MapsTo.val_restrict_apply] using ⟨x, hx₁, rfl⟩
      simp only [πs_apply, continuous_projRestrict, LocallyConstant.coe_comap, Function.comp_apply,
        hx₁', LocallyConstant.piecewise'_apply_right, h₁]
      congr
      exact C1_projOrd C hsC ho hx₁

variable (o) in
theorem succ_mono : CategoryTheory.Mono (ModuleCat.ofHom (πs C o)) := by
  rw [ModuleCat.mono_iff_injective]
  exact injective_πs _ _

theorem succ_exact :
    CategoryTheory.Exact (ModuleCat.ofHom (πs C o)) (ModuleCat.ofHom (Linear_CC' C hsC ho)) := by
  rw [ModuleCat.exact_iff]
  ext f
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  refine ⟨fun ⟨y, hy⟩ ↦ ?_, fun hf ↦ ?_⟩
  · simpa only [ModuleCat.ofHom, ← hy] using CC_comp_zero _ _ _ y
  · exact CC_exact _ hC _ ho hf

end ExactSequence

section GoodProducts

namespace GoodProducts

/-- The `GoodProducts` in `C` that contain `o` (they necessarily start with `o`, see
    `GoodProducts.head!_eq_o_of_maxProducts`) -/
def MaxProducts : Set (Products I) := {l | l.isGood C ∧ term I ho ∈ l.val}

theorem union_succ : GoodProducts C = GoodProducts (C.proj (ord I · < o)) ∪ MaxProducts C ho := by
  ext l
  simp only [GoodProducts, MaxProducts, Set.mem_union, Set.mem_setOf_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_cases hh : term I ho ∈ l.val
    · exact Or.inr ⟨h, hh⟩
    · left
      intro he
      apply h
      have h' := Products.prop_of_isGood_of_contained C _ h hsC
      simp only [Order.lt_succ_iff] at h'
      simp only [not_imp_not] at hh
      have hh' : ∀ a ∈ l.val, ord I a < o
      · intro a ha
        refine (h' a ha).lt_of_ne ?_
        rw [ne_eq, ord_term ho a]
        rintro rfl
        contradiction
      rwa [Products.eval_πs_image C hh', ← Products.eval_πs C hh',
        Submodule.apply_mem_span_image_iff_mem_span (injective_πs _ _)]
  · refine h.elim (fun hh ↦ ?_) And.left
    have := Products.isGood_mono C (Order.lt_succ o).le hh
    rwa [contained_eq_proj C (Order.succ o) hsC]

/-- The inclusion map from the sum of `GoodProducts (C.proj (ord I · < o))` and
    `(MaxProducts C ho)` to `Products I`. -/
def sum_to : (GoodProducts (C.proj (ord I · < o))) ⊕ (MaxProducts C ho) → Products I :=
  Sum.elim Subtype.val Subtype.val

theorem injective_sum_to : Function.Injective (sum_to C ho) := by
  refine Function.Injective.sum_elim Subtype.val_injective Subtype.val_injective
    (fun ⟨a,ha⟩ ⟨b,hb⟩  ↦ (fun (hab : a = b) ↦ ?_))
  rw [← hab] at hb
  have ha' := Products.prop_of_isGood  C _ ha (term I ho) hb.2
  simp only [ord_term_aux, lt_self_iff_false] at ha'

theorem sum_to_range :
    Set.range (sum_to C ho) = GoodProducts (C.proj (ord I · < o)) ∪ MaxProducts C ho := by
  have h : Set.range (sum_to C ho) = _ ∪ _ := Set.Sum.elim_range _ _; rw [h]; congr<;> ext l
  · exact ⟨fun ⟨m,hm⟩ ↦ by rw [← hm]; exact m.prop, fun hl ↦ ⟨⟨l,hl⟩, rfl⟩⟩
  · exact ⟨fun ⟨m,hm⟩ ↦ by rw [← hm]; exact m.prop, fun hl ↦ ⟨⟨l,hl⟩, rfl⟩⟩

/-- The equivalence from the sum of `GoodProducts (C.proj (ord I · < o))` and
    `(MaxProducts C ho)` to `GoodProducts C`. -/
noncomputable
def sum_equiv : GoodProducts (C.proj (ord I · < o)) ⊕ (MaxProducts C ho) ≃ GoodProducts C :=
  calc _ ≃ Set.range (sum_to C ho) := Equiv.ofInjective (sum_to C ho) (injective_sum_to C ho)
       _ ≃ _ := Equiv.Set.ofEq <| by rw [sum_to_range C ho, union_succ C hsC ho]

theorem sum_equiv_comp_eval_eq_elim : eval C ∘ (sum_equiv C hsC ho).toFun =
    (Sum.elim (fun (l : GoodProducts (C.proj (ord I · < o))) ↦ Products.eval C l.1)
    (fun (l : MaxProducts C ho) ↦ Products.eval C l.1)) := by
  ext ⟨_,_⟩ <;> [rfl; rfl]

/-- Let

`N := LocallyConstant (C.proj (ord I · < o)) ℤ`

`M := LocallyConstant C ℤ`

`P := LocallyConstant (C' C ho) ℤ`

`ι := GoodProducts (C.proj (ord I · < o))`

`ι' := GoodProducts (C' C ho')`

`v : ι → N := GoodProducts.eval (C.proj (ord I · < o))`

Then `SumEval C ho` is the map `u` in the diagram below. It is linearly independent if and only if
`GoodProducts.eval C` is, see `linearIndependent_iff_sum`. The top row is the exact sequence given
by `succ_exact` and `succ_mono`. The left square commutes by `GoodProducts.square_commutes`.
```
0 --→ N --→ M --→  P
      ↑     ↑      ↑
     v|    u|      |
      ι → ι ⊕ ι' ← ι'
```
-/
def SumEval : GoodProducts (C.proj (ord I · < o)) ⊕ MaxProducts C ho →
    LocallyConstant C ℤ :=
  Sum.elim (fun l ↦ l.1.eval C) (fun l ↦ l.1.eval C)

theorem linearIndependent_iff_sum :
    LinearIndependent ℤ (eval C) ↔ LinearIndependent ℤ (SumEval C ho) := by
  rw [← linearIndependent_equiv (sum_equiv C hsC ho), SumEval,
    ← sum_equiv_comp_eval_eq_elim C hsC ho]
  exact Iff.rfl

theorem span_sum : Set.range (eval C) = Set.range (Sum.elim
    (fun (l : GoodProducts (C.proj (ord I · < o))) ↦ Products.eval C l.1)
    (fun (l : MaxProducts C ho) ↦ Products.eval C l.1)) := by
  rw [← sum_equiv_comp_eval_eq_elim C hsC ho, Equiv.toFun_as_coe,
    EquivLike.range_comp (e := sum_equiv C hsC ho)]


theorem square_commutes : SumEval C ho ∘ Sum.inl =
    ModuleCat.ofHom (πs C o) ∘ eval (C.proj (ord I · < o)) := by
  ext l
  dsimp [SumEval]
  rw [← Products.eval_πs C (Products.prop_of_isGood  _ _ l.prop)]
  rfl

end GoodProducts

theorem swapTrue_eq_true (x : I → Bool) : SwapTrue o x (term I ho) = true := by
  simp only [SwapTrue, ord_term_aux, ite_true]

theorem mem_C'_eq_false : ∀ x, x ∈ C' C ho → x (term I ho) = false := by
  rintro x ⟨_, y, _, rfl⟩
  simp only [Proj, ord_term_aux, lt_self_iff_false, ite_false]

/-- `List.tail` as a `Products`. -/
def Products.Tail (l : Products I) : Products I :=
  ⟨l.val.tail, List.Chain'.tail l.prop⟩

theorem Products.max_eq_o_cons_tail (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = term I ho) : l.val = term I ho :: l.Tail.val := by
  rw [← List.cons_head!_tail hl, hlh]
  rfl

theorem Products.max_eq_o_cons_tail' (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = term I ho) (hlc : List.Chain' (·>·) (term I ho :: l.Tail.val)) :
    l = ⟨term I ho :: l.Tail.val, hlc⟩ := by
  simp_rw [← max_eq_o_cons_tail ho l hl hlh]
  rfl

theorem GoodProducts.head!_eq_o_of_maxProducts (l : ↑(MaxProducts C ho)) :
    l.val.val.head! = term I ho := by
  rw [eq_comm, ← ord_term ho]
  have hm := l.prop.2
  have := Products.prop_of_isGood_of_contained C _ l.prop.1 hsC l.val.val.head!
    (List.head!_mem_self (List.ne_nil_of_mem hm))
  simp only [Order.lt_succ_iff] at this
  refine eq_of_le_of_not_lt this (not_lt.mpr ?_)
  have h : ord I (term I ho) ≤ ord I l.val.val.head!
  · simp only [← ord_term_aux, ord, Ordinal.typein_le_typein, not_lt]
    exact Products.rel_head!_of_mem hm
  rwa [ord_term_aux] at h

theorem GoodProducts.max_eq_o_cons_tail (l : MaxProducts C ho) :
    l.val.val = (term I ho) :: l.val.Tail.val :=
  Products.max_eq_o_cons_tail ho l.val (List.ne_nil_of_mem l.prop.2)
    (head!_eq_o_of_maxProducts _ hsC ho l)

theorem Products.evalCons {l : List I} {a : I}
    (hla : (a::l).Chain' (·>·)) : Products.eval C ⟨a::l,hla⟩ =
    (e C a) * Products.eval C ⟨l,List.Chain'.sublist hla (List.tail_sublist (a::l))⟩ := by
  simp only [eval._eq_1, List.map, List.prod_cons]

theorem Products.max_eq_eval (l : Products I) (hl : l.val ≠ [])
    (hlh : l.val.head! = term I ho) :
    Linear_CC' C hsC ho (l.eval C) = l.Tail.eval (C' C ho) := by
  have hlc : ((term I ho) :: l.Tail.val).Chain' (·>·)
  · rw [← max_eq_o_cons_tail ho l hl hlh]; exact l.prop
  rw [max_eq_o_cons_tail' ho l hl hlh hlc, Products.evalCons]
  ext x
  simp only [Linear_CC', Linear_CC'₀, Linear_CC'₁, LocallyConstant.comapₗ, Subtype.coe_eta,
    LinearMap.sub_apply, LinearMap.coe_mk, AddHom.coe_mk, LocallyConstant.sub_apply,
    continuous_CC'₀, continuous_CC'₁, LocallyConstant.coe_comap, LocallyConstant.coe_mul,
    Function.comp_apply, Pi.mul_apply]
  rw [CC'₁, CC'₀, Products.eval_eq, Products.eval_eq, Products.eval_eq]
  simp only [mul_ite, mul_one, mul_zero]
  have hi' : ∀ i, i ∈ l.Tail.val → (x.val i = SwapTrue o x.val i)
  · intro i hi
    simp only [SwapTrue, @eq_comm _ (x.val i), ite_eq_right_iff, ord_term ho]
    rintro rfl
    exact ((List.Chain.rel hlc hi).ne rfl).elim
  have H :
    (∀ i, i ∈ l.Tail.val → (x.val i = true)) = (∀ i, i ∈ l.Tail.val → (SwapTrue o x.val i = true))
  · apply forall_congr; intro i; apply forall_congr; intro hi; rw [hi' i hi]
  simp only [H]
  split_ifs with h₁ h₂ h₃ <;> dsimp [e]
  · rw [if_pos (swapTrue_eq_true _ _), if_neg]
    · rfl
    · simp [mem_C'_eq_false C ho x x.prop, Bool.coe_false]
  · push_neg at h₂; obtain ⟨i, hi⟩ := h₂; exfalso; rw [hi' i hi.1] at hi; exact hi.2 (h₁ i hi.1)
  · push_neg at h₁; obtain ⟨i, hi⟩ := h₁; exfalso; rw [← hi' i hi.1] at hi; exact hi.2 (h₃ i hi.1)
  · rfl

namespace GoodProducts

theorem max_eq_eval (l : MaxProducts C ho) :
    Linear_CC' C hsC ho (l.val.eval C) = l.val.Tail.eval (C' C ho) :=
  Products.max_eq_eval _ _ _ _ (List.ne_nil_of_mem l.prop.2)
    (head!_eq_o_of_maxProducts _ hsC ho l)

theorem max_eq_eval_unapply :
    (Linear_CC' C hsC ho) ∘ (fun (l : MaxProducts C ho) ↦ Products.eval C l.val) =
    (fun l ↦ l.val.Tail.eval (C' C ho)) := by
  ext1 l
  exact max_eq_eval _ _ _ _

theorem chain'_cons_of_lt (l : MaxProducts C ho)
    (q : Products I) (hq : q < l.val.Tail) :
    List.Chain' (fun x x_1 ↦ x > x_1) (term I ho :: q.val) := by
  rw [List.chain'_iff_pairwise]
  simp only [gt_iff_lt, List.pairwise_cons]
  refine ⟨fun a ha ↦ lt_of_le_of_lt (Products.rel_head!_of_mem ha) ?_,
    List.chain'_iff_pairwise.mp q.prop⟩
  refine lt_of_le_of_lt (Products.head!_le_of_lt hq (q.val.ne_nil_of_mem ha)) ?_
  by_cases hM : l.val.Tail.val = []
  · rw [Products.lt_iff_lex_lt, hM] at hq
    simp only [List.Lex.not_nil_right] at hq
  · have := l.val.prop
    rw [max_eq_o_cons_tail C hsC ho l, List.chain'_iff_pairwise] at this
    exact List.rel_of_pairwise_cons this (List.head!_mem_self hM)

theorem good_lt_maxProducts (q : GoodProducts (C.proj (ord I · < o)))
    (l : MaxProducts C ho) : List.Lex (·<·) q.val.val l.val.val := by
  by_cases h : q.val.val = []
  · rw [h, max_eq_o_cons_tail C hsC ho l]
    exact List.Lex.nil
  · rw [← List.cons_head!_tail h, max_eq_o_cons_tail C hsC ho l]
    apply List.Lex.rel
    rw [← Ordinal.typein_lt_typein (·<·)]
    simp only [term, Ordinal.typein_enum]
    exact Products.prop_of_isGood C _ q.prop q.val.val.head! (List.head!_mem_self h)

theorem maxTail_isGood (l : MaxProducts C ho)
    (h₁: ⊤ ≤ Submodule.span ℤ (Set.range (eval (C.proj (ord I · < o))))) :
    l.val.Tail.isGood (C' C ho) := by
  intro h
  rw [Finsupp.mem_span_image_iff_total, ← max_eq_eval C hsC ho] at h
  obtain ⟨m, ⟨hmmem, hmsum⟩⟩ := h
  rw [Finsupp.total_apply] at hmsum
  have : (Linear_CC' C hsC ho) (l.val.eval C) = (Linear_CC' C hsC ho)
    (Finsupp.sum m fun i a ↦ a • ((term I ho :: i.1).map (e C)).prod)
  · rw [← hmsum]
    simp only [map_finsupp_sum]
    apply Finsupp.sum_congr
    intro q hq
    rw [LinearMap.map_smul]
    rw [Finsupp.mem_supported] at hmmem
    have hx'' : q < l.val.Tail := hmmem hq
    have : ∃ (p : Products I), p.val ≠ [] ∧ p.val.head! = term I ho ∧ q = p.Tail :=
      ⟨⟨term I ho :: q.val, chain'_cons_of_lt C hsC ho l q hx''⟩,
        ⟨List.cons_ne_nil _ _, by simp only [List.head!_cons],
        by simp only [Products.Tail, List.tail_cons, Subtype.coe_eta]⟩⟩
    obtain ⟨p, hp⟩ := this
    rw [hp.2.2, ← Products.max_eq_eval C hsC ho p hp.1 hp.2.1]
    dsimp [Products.eval]
    rw [Products.max_eq_o_cons_tail ho p hp.1 hp.2.1]
    rfl
  have hse := succ_exact C hC hsC ho
  rw [ModuleCat.exact_iff] at hse
  dsimp [ModuleCat.ofHom] at hse
  rw [← LinearMap.sub_mem_ker_iff, ← hse] at this
  obtain ⟨(n : LocallyConstant (C.proj (ord I · < o)) ℤ), hn⟩ := this
  rw [eq_sub_iff_add_eq] at hn
  have hn' := h₁ (Submodule.mem_top : n ∈ ⊤)
  rw [Finsupp.mem_span_range_iff_exists_finsupp] at hn'
  obtain ⟨w,hc⟩ := hn'
  rw [← hc, map_finsupp_sum] at hn
  apply l.prop.1
  rw [← hn]
  apply Submodule.add_mem
  · apply Submodule.finsupp_sum_mem
    intro q _
    erw [LinearMap.map_smul (fₗ := πs C o) (c := w q) (x := eval (C.proj (ord I · < o)) q)]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    dsimp only [eval]
    rw [Products.eval_πs C (Products.prop_of_isGood _ _ q.prop)]
    refine ⟨q.val, ⟨?_, rfl⟩⟩
    simp only [Products.lt_iff_lex_lt, Set.mem_setOf_eq]
    exact good_lt_maxProducts C hsC ho q l
  · apply Submodule.finsupp_sum_mem
    intro q hq
    apply Submodule.smul_mem
    apply Submodule.subset_span
    rw [Finsupp.mem_supported] at hmmem
    rw [← Finsupp.mem_support_iff] at hq
    refine ⟨⟨term I ho :: q.val, chain'_cons_of_lt C hsC ho l q (hmmem hq)⟩, ⟨?_, rfl⟩⟩
    simp only [Products.lt_iff_lex_lt, Set.mem_setOf_eq]
    rw [max_eq_o_cons_tail C hsC ho l]
    exact List.Lex.cons ((Products.lt_iff_lex_lt q l.val.Tail).mp (hmmem hq))

/-- Given `l : MaxProducts C ho`, its `Tail` is a `GoodProducts (C' C ho)`. -/
noncomputable
def MaxToGood
    (h₁: ⊤ ≤ Submodule.span ℤ (Set.range (eval (C.proj (ord I · < o))))) :
    MaxProducts C ho → GoodProducts (C' C ho) :=
  fun l ↦ ⟨l.val.Tail, maxTail_isGood C hC hsC ho l h₁⟩

theorem maxToGood_injective
    (h₁: ⊤ ≤ Submodule.span ℤ (Set.range (eval (C.proj (ord I · < o))))) :
    (MaxToGood C hC hsC ho h₁).Injective := by
  intro m n h
  apply Subtype.ext ∘ Subtype.ext
  rw [Subtype.ext_iff] at h
  dsimp [MaxToGood] at h
  rw [max_eq_o_cons_tail C hsC ho m, max_eq_o_cons_tail C hsC ho n, h]

theorem linearIndependent_comp_of_eval
    (h₁: ⊤ ≤ Submodule.span ℤ (Set.range (eval (C.proj (ord I · < o))))) :
    LinearIndependent ℤ (eval (C' C ho)) →
    LinearIndependent ℤ (ModuleCat.ofHom (Linear_CC' C hsC ho) ∘ SumEval C ho ∘ Sum.inr) := by
  dsimp [SumEval, ModuleCat.ofHom]
  erw [max_eq_eval_unapply C hsC ho]
  intro h
  let f := MaxToGood C hC hsC ho h₁
  have hf : f.Injective := maxToGood_injective C hC hsC ho h₁
  have hh : (fun l ↦ Products.eval (C' C ho) l.val.Tail) = eval (C' C ho) ∘ f := rfl
  rw [hh]
  exact h.comp f hf

end GoodProducts

end GoodProducts

end Successor

section Induction

variable (I) in
/-- The predicate on ordinals which we prove by induction, see `GoodProducts.P0`,
    `GoodProducts.Plimit` and `GoodProducts.linearIndependentAux`.  -/
def P (o : Ordinal) : Prop :=
  o ≤ Ordinal.type (·<· : I → I → Prop) →
  (∀ (C : Set (I → Bool)), IsClosed C → contained C o →
    LinearIndependent ℤ (GoodProducts.eval C))

theorem GoodProducts.P0 : P I 0 := fun _ C _ hsC ↦ by
  have : C ⊆ {(fun _ ↦ false)} := fun c hc ↦ by
    ext x; exact Bool.eq_false_iff.mpr (fun ht ↦ (Ordinal.not_lt_zero (ord I x)) (hsC c hc x ht))
  rw [Set.subset_singleton_iff_eq] at this
  cases this
  · subst C
    exact linearIndependentEmpty
  · subst C
    exact linearIndependentSingleton

theorem GoodProducts.Plimit (o : Ordinal) (ho : Ordinal.IsLimit o) :
    (∀ (o' : Ordinal), o' < o → P I o') → P I o := by
  intro h hho C hC hsC
  rw [linearIndependent_iff_union_smaller C ho hsC]
  exact linearIndependent_iUnion_of_directed
    (directed_of_sup fun _ _ h ↦ GoodProducts.smaller_mono C h) fun ⟨o', ho'⟩ ↦
    (linearIndependent_iff_smaller _ _).mp (h o' ho' (le_of_lt (lt_of_lt_of_le ho' hho))
    (C.proj (ord I · < o')) (isClosed_proj _ _ hC) (contained_proj _ _))

theorem GoodProducts.linearIndependentAux (μ : Ordinal) : P I μ := by
  refine Ordinal.limitRecOn μ P0 (fun o h ho C hC hsC ↦ ?_)
      (fun o ho h ↦ (GoodProducts.Plimit o ho (fun o' ho' ↦ (h o' ho'))))
  have ho' : o < Ordinal.type (·<· : I → I → Prop) :=
    lt_of_lt_of_le (Order.lt_succ _) ho
  rw [linearIndependent_iff_sum C hsC ho']
  refine ModuleCat.linearIndependent_leftExact ?_ ?_ (succ_mono C o) (succ_exact C hC hsC ho')
      (square_commutes C ho')
  · exact h (le_of_lt ho') (C.proj (ord I · < o)) (isClosed_proj C o hC) (contained_proj C o)
  · exact linearIndependent_comp_of_eval C hC hsC ho' (span (C.proj (ord I · < o))
      (isClosed_proj C o hC)) (h (le_of_lt ho') (C' C ho') (isClosed_C' C hC ho')
      (contained_C' C ho'))

theorem GoodProducts.linearIndependent (hC : IsClosed C) :
    LinearIndependent ℤ (GoodProducts.eval C) :=
  GoodProducts.linearIndependentAux (Ordinal.type (·<· : I → I → Prop)) (le_refl _)
    C hC (fun _ _ _ _ ↦ Ordinal.typein_lt_type _ _)

/-- `GoodProducts C` as a `ℤ`-basis for `LocallyConstant C ℤ`.  -/
noncomputable
def GoodProducts.Basis (hC : IsClosed C) :
    Basis (GoodProducts C) ℤ (LocallyConstant C ℤ) :=
  Basis.mk (GoodProducts.linearIndependent C hC) (GoodProducts.span C hC)

end Induction

variable {S : Profinite} {ι : S → I → Bool} (hι : ClosedEmbedding ι)

theorem Nobeling : Module.Free ℤ (LocallyConstant S ℤ) := Module.Free.of_equiv'
  (Module.Free.of_basis <| GoodProducts.Basis _ hι.closed_range) (LocallyConstant.congrLeftₗ ℤ
  (Homeomorph.ofEmbedding ι hι.toEmbedding)).symm

end NobelingProof

variable (S : Profinite.{u})

open Classical in
/-- The embedding `S → (I → Bool)` where `I` is the set of clopens of `S`. -/
noncomputable
def Nobeling.ι : S → ({C : Set S // IsClopen C} → Bool) := fun s C => decide (s ∈ C.1)

open Classical in
theorem Nobeling.embedding : ClosedEmbedding (Nobeling.ι S) := by
  apply Continuous.closedEmbedding
  · dsimp [ι]
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
    obtain ⟨C, hC, hh⟩ := exists_clopen_of_totally_separated hn
    apply hh.2 ∘ of_decide_eq_true
    dsimp [ι] at h
    rw [← congr_fun h ⟨C, hC⟩]
    exact decide_eq_true hh.1

/-- Nöbeling's theorem: the `ℤ`-module `LocallyConstant S ℤ` is free for every `S : Profinite` -/
theorem Nobeling : Module.Free ℤ (LocallyConstant S ℤ) :=
  @NobelingProof.Nobeling {C : Set S // IsClopen C} ⟨⟨∅, isClopen_empty⟩⟩
    (IsWellOrder.linearOrder WellOrderingRel)
    WellOrderingRel.isWellOrder S (Nobeling.ι S) (Nobeling.embedding S)
