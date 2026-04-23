/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.AlgebraicTopology.RelativeCellComplex.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.AnodyneExtensions.Rank
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.CategoryTheory.Limits.Preorder
import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexEvaluation
import Mathlib.CategoryTheory.Category.Init
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Types.Pushouts
import Mathlib.CategoryTheory.MorphismProperty.FunctorCategory
import Mathlib.CategoryTheory.Types.Monomorphisms
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.Elementwise
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike

/-!
# The relative cell complex attached to a rank function for a pairing

Let `A` be a subcomplex of a simplicial set `X`. Let `P : A.Pairing`
be a proper pairing (in the sense of Moss) and `f : P.RankFunction ι`
be a rank function. We show that the inclusion `A.ι` is a relative
cell complex with basic cells given by horn inclusions.

## References
* [Sean Moss, *Another approach to the Kan-Quillen model structure*][moss-2020]

-/

@[expose] public section

universe v u

open CategoryTheory HomotopicalAlgebra Simplicial Limits Opposite

namespace SSet.Subcomplex.Pairing.RankFunction

variable {X : SSet.{u}} {A : X.Subcomplex} {P : A.Pairing}
  {ι : Type v} [LinearOrder ι] (f : P.RankFunction ι)

/-- Given a rank function `f : P.RankFunction ι` for a
pairing `P` of a subcomplex `A` of `X : SSet`, and `i : ι`,
this is the type of type (II) simplices of rank `i`. -/
@[ext]
structure Cell (i : ι) : Type u where
  /-- a type (II) simplex -/
  s : P.II
  rank_s : f.rank s = i

namespace Cell

variable {f} {i : ι} (c : f.Cell i)

/-- The dimension `c.dim` of a cell `c` of a rank function for a
pairing `P` of a subcomplex of a simplicial set. This is defined
as the dimension of the corresponding type (II) simplex.
(In the case `P` is proper, the corresponding type (I) simplex
will be of dimension `c.dim + 1`.) -/
abbrev dim : ℕ := c.s.val.dim

variable [P.IsProper]

/-- If `c` is a cell of a rank function for a proper pairing `P`
of a subcomplex of a simplicial set, this is the index
in `Fin (c.dim + 2)` of the face of the type (I) simplex
given by the corresponding type (II) simplex. -/
noncomputable def index : Fin (c.dim + 2) :=
  (P.isUniquelyCodimOneFace c.s).index rfl

/-- The horn in the standard simplex corresponding to a cell
of a rank function for a proper pairing of a subcomplex of
a simplicial set. -/
protected noncomputable abbrev horn : (Δ[c.dim + 1] : SSet.{u}).Subcomplex :=
  SSet.horn _ c.index

/-- The morphism `Δ[c.dim + 1] ⟶ X` corresponding to a cell of
a rank function for a proper pairing of a subcomplex of `X : SSet`. -/
abbrev map : Δ[c.dim + 1] ⟶ X :=
  yonedaEquiv.symm
    ((P.p c.s).val.cast (P.isUniquelyCodimOneFace c.s).dim_eq).simplex

@[simp]
lemma range_map : Subcomplex.range c.map = (P.p c.s).val.subcomplex := by
  rw [range_eq_ofSimplex, Equiv.apply_symm_apply, S.ofSimplex_eq_subcomplex_mk,
    ← S.cast_eq_self _ (P.dim_p c.s)]
  dsimp [S.subcomplex]

lemma map_app_objEquiv_symm_δ_index :
    c.map.app (op ⦋c.dim⦌) (stdSimplex.objEquiv.symm (SimplexCategory.δ c.index)) =
      c.s.val.simplex :=
  (P.isUniquelyCodimOneFace c.s).δ_index rfl

lemma subcomplex_not_le_image_horn : ¬ c.s.val.subcomplex ≤ c.horn.image c.map := by
  intro h
  simp only [Subfunctor.ofSection_le_iff, image_obj, Set.mem_image] at h
  obtain ⟨x, h₁, h₂⟩ := h
  obtain ⟨g, rfl⟩ := stdSimplex.objEquiv.symm.surjective x
  rw [← stdSimplex.map_objEquiv_op_apply, Equiv.apply_symm_apply] at h₂
  have := mono_of_nonDegenerate (x := ⟨_, c.s.val.nonDegenerate⟩) _ _ _ h₂
  obtain rfl := (P.isUniquelyCodimOneFace c.s).unique rfl _ h₂
  rw [← ofSimplex_le_iff, subcomplex_le_horn_iff, ← stdSimplex.face_singleton_compl] at h₁
  tauto

lemma image_horn_lt_subcomplex : c.horn.image c.map < (P.p c.s).val.subcomplex := by
  rw [lt_iff_le_and_ne]
  exact ⟨by simpa using image_le_range c.horn c.map,
    fun h ↦ c.subcomplex_not_le_image_horn (by simpa only [h] using P.le c.s)⟩

@[simp]
lemma image_face_index_compl :
    (stdSimplex.face {c.index}ᶜ).image c.map = c.s.val.subcomplex := by
  rw [stdSimplex.face_singleton_compl, image_ofSimplex]
  congr 1
  exact (P.isUniquelyCodimOneFace c.s).δ_index rfl

end Cell

variable [P.IsProper] in
/-- The horn inclusion corresponding to a cell of a rank function
for a proper pairing of a subcomplex of a simplicial set. -/
noncomputable abbrev basicCell (i : ι) (c : f.Cell i) : (c.horn : SSet) ⟶ Δ[c.dim + 1] :=
  c.horn.ι

/-- The filtration of a simplicial set given by a rank function
for a proper pairing of a subcomplex. -/
def filtration (i : ι) : X.Subcomplex :=
  A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cell j), (P.p c.s).val.subcomplex

lemma filtration_def (i : ι) :
    f.filtration i = A ⊔ ⨆ (j : ι) (_ : j < i) (c : f.Cell j), (P.p c.s).val.subcomplex :=
  rfl

lemma subcomplex_le_filtration {j : ι} (c : f.Cell j) {i : ι} (h : j < i) :
    (P.p c.s).val.subcomplex ≤ f.filtration i := by
  refine le_trans ?_ le_sup_right
  refine le_trans ?_ (le_iSup _ j)
  refine le_trans ?_ (le_iSup _ h)
  exact le_trans (by rfl) (le_iSup _ c)

@[simp]
lemma le_filtration (i : ι) : A ≤ f.filtration i := le_sup_left

@[simp]
lemma filtration_bot [OrderBot ι] : f.filtration ⊥ = A := by
  simp [filtration_def]

lemma filtration_monotone : Monotone f.filtration := by
  intro i₁ i₂ h
  conv_lhs => rw [filtration_def]
  simp only [sup_le_iff, iSup_le_iff, le_filtration, true_and]
  intro j hj c
  exact f.subcomplex_le_filtration c (lt_of_lt_of_le hj h)

lemma filtration_succ [SuccOrder ι] (i : ι) (hi : ¬ IsMax i) :
    f.filtration (Order.succ i) =
      f.filtration i ⊔ ⨆ (c : f.Cell i), (P.p c.s).val.subcomplex := by
  apply le_antisymm
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨(f.le_filtration _).trans le_sup_left, fun j hj c ↦ ?_⟩
    rw [Order.lt_succ_iff_of_not_isMax hi] at hj
    obtain hj | rfl := hj.lt_or_eq
    · exact (f.subcomplex_le_filtration _ hj).trans le_sup_left
    · exact le_trans (le_trans (by rfl) (le_iSup _ c)) le_sup_right
  · simp only [sup_le_iff, iSup_le_iff]
    exact ⟨f.filtration_monotone (Order.le_succ i),
      fun c ↦ f.subcomplex_le_filtration _ (Order.lt_succ_of_not_isMax hi)⟩

lemma filtration_of_isSuccLimit [OrderBot ι] [SuccOrder ι] (i : ι) (hi : Order.IsSuccLimit i) :
    f.filtration i = ⨆ (j : ι) (_ : j < i), f.filtration j := by
  apply le_antisymm
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff]
    refine ⟨?_, fun j hj c ↦ ?_⟩
    · refine le_trans ?_ (le_iSup _ ⊥)
      exact le_trans (by simp) (le_iSup _ hi.bot_lt)
    · refine le_trans ?_ (le_iSup _ (Order.succ j))
      refine le_trans ?_ (le_iSup _
        (by rwa [← Order.IsSuccLimit.succ_lt_iff hi] at hj))
      exact f.subcomplex_le_filtration _ (Order.lt_succ_of_not_isMax hj.not_isMax)
  · simp only [iSup_le_iff]
    intro j hj
    exact f.filtration_monotone hj.le

lemma iSup_filtration_iio [OrderBot ι] [SuccOrder ι] (m : ι) (hm : Order.IsSuccLimit m) :
    ⨆ (i : Set.Iio m), f.filtration i = f.filtration m := by
  apply le_antisymm
  · simp only [iSup_le_iff, Subtype.forall, Set.mem_Iio]
    intro j hj
    exact f.filtration_monotone hj.le
  · conv_lhs => rw [filtration_def]
    simp only [sup_le_iff, iSup_le_iff, ← f.filtration_bot]
    exact ⟨le_trans (by rfl) (le_iSup _ ⟨⊥, hm.bot_lt⟩), fun j hj c ↦
      (f.subcomplex_le_filtration c (Order.lt_succ_of_not_isMax (not_isMax_of_lt hj))).trans
        (le_trans (by rfl) (le_iSup _ ⟨Order.succ j, hm.succ_lt_iff.mpr hj⟩))⟩

variable {f} in
lemma Cell.subcomplex_not_le_filtration {j : ι} (c : f.Cell j) :
    ¬ c.s.val.subcomplex ≤ f.filtration j := by
  simp only [ofSimplex_le_iff, filtration_def, Subfunctor.max_obj, Subfunctor.iSup_obj,
    Set.mem_union, Set.mem_iUnion, not_or, not_exists]
  refine ⟨c.s.val.notMem, fun i hi c' h ↦ ?_⟩
  rw [← c.rank_s, ← c'.rank_s] at hi
  refine lt_irrefl _ (hi.trans (f.lt ?_))
  refine ⟨fun hxy ↦ ?_, lt_of_le_of_ne ?_ ((P.ne _ _).symm)⟩
  · rw [hxy] at hi
    exact (lt_irrefl _ hi).elim
  · rw [← ofSimplex_le_iff] at h
    rwa [Subcomplex.N.le_iff, SSet.N.le_iff]

variable [P.IsProper]

lemma iSup_filtration [OrderBot ι] [SuccOrder ι] [NoMaxOrder ι] :
    ⨆ (i : ι), f.filtration i = ⊤ := by
  refine le_antisymm (by simp) ?_
  rw [N.subcomplex_le_iff]
  intro s _
  cases s using SSet.Subcomplex.N.cases A with
  | mem s hs => exact hs.trans (le_trans (by simp) (le_iSup _ ⊥))
  | notMem s =>
    obtain ⟨t, ht⟩ := P.exists_or s
    refine le_trans ?_
      (le_trans (f.subcomplex_le_filtration ⟨t, rfl⟩ (Order.lt_succ _)) (le_iSup _ _))
    obtain rfl | rfl := ht
    · exact P.le t
    · rfl

variable {f} in
/-- The morphism `Δ[c.dim + 1] ⟶ f.filtration (Order.succ j)` given
by `c : f.Cell j`, when `f` is a rank function for a proper pairing
of a subcomplex of a simplicial set. -/
def Cell.mapToSucc {j : ι} [SuccOrder ι] [NoMaxOrder ι] (c : f.Cell j) :
    Δ[c.dim + 1] ⟶ f.filtration (Order.succ j) :=
  Subcomplex.lift c.map (by simpa using f.subcomplex_le_filtration c (Order.lt_succ _))

variable {f} in
@[reassoc (attr := simp)]
lemma Cell.mapToSucc_ι {j : ι} [SuccOrder ι] [NoMaxOrder ι] (c : f.Cell j) :
    c.mapToSucc ≫ (f.filtration (Order.succ j)).ι = c.map := rfl

section

/-!
The main technical result in this section is `SSet.Subcomplex.Pairing.RankFunction.isPushout`
which states that there is a pushout square:
```
                                      f.t j
∐ fun (c : f.Cell j) ↦ c.horn  -------------> f.filtration j
               |                                   |
         f.m j |                                   |
               v                      f.b j        v
∐ fun (c : f.Cell j) ↦ Δ[c.dim + 1]  -------> f.filtration (Order.succ j)
```
The map on the left is a coproduct of horn inclusions (the source and target
of the morphism `f.m j` are denoted `f.sigmaHorn j` and `f.sigmaStdSimplex j`).

-/

/-- Given a rank function for a proper pairing of a subcomplex of a
simplicial set, this is the coproduct of the horns corresponding to
all cells of rank `j`. -/
noncomputable abbrev sigmaHorn (j : ι) : SSet.{u} :=
  ∐ fun (c : f.Cell j) ↦ c.horn

variable {f} in
/-- Given a cell `c` of rank `j` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is the inclusion of
`c.horn` into `f.sigmaHorn j`. -/
noncomputable abbrev Cell.ιSigmaHorn {j : ι} (c : f.Cell j) :
    (c.horn : SSet) ⟶ f.sigmaHorn j :=
  Sigma.ι (fun (c : f.Cell j) ↦ (c.horn : SSet)) c

/-- Given a rank function for a proper pairing of a subcomplex of a
simplicial set, this is coproduct of the standard simplices corresponding
to all cells of rank `j`. -/
noncomputable abbrev sigmaStdSimplex (j : ι) : SSet.{u} :=
  ∐ fun (i : f.Cell j) ↦ Δ[i.dim + 1]

variable {f} in
/-- Given a cell `c` of rank `j` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is the inclusion of
`Δ[c.dim + 1]` into `f.sigmaStdSimplex j`. -/
noncomputable abbrev Cell.ιSigmaStdSimplex {j : ι} (c : f.Cell j) :
    Δ[c.dim + 1] ⟶ f.sigmaStdSimplex j :=
  Sigma.ι (fun (c : f.Cell j) ↦ Δ[c.dim + 1]) c

lemma ιSigmaHorn_jointly_surjective
    {d : ℕ} {j : ι} (a : (f.sigmaHorn j) _⦋d⦌) :
    ∃ (c : f.Cell j) (x : (c.horn : SSet) _⦋d⦌), c.ιSigmaHorn.app _ x = a :=
  Cofan.inj_jointly_surjective_of_isColimit
    ((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _))) a

omit [P.IsProper] in
lemma ιSigmaStdSimplex_jointly_surjective
    {d : ℕ} {j : ι} (a : (f.sigmaStdSimplex j) _⦋d⦌) :
    ∃ (c : f.Cell j) (x :  Δ[c.dim + 1] _⦋d⦌), c.ιSigmaStdSimplex.app _ x = a :=
  Cofan.inj_jointly_surjective_of_isColimit
    ((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _))) a

omit [P.IsProper] in
lemma ιSigmaStdSimplex_eq_iff {j : ι} {d : ℕ}
    (x : f.Cell j) (s : (Δ[x.dim + 1] : SSet.{u}) _⦋d⦌)
    (y : f.Cell j) (t : (Δ[y.dim + 1] : SSet.{u}) _⦋d⦌) :
    x.ιSigmaStdSimplex.app (op ⦋d⦌) s = y.ιSigmaStdSimplex.app (op ⦋d⦌) t ↔
      ∃ (h : x = y), t = cast (by rw [h]) s :=
  Cofan.inj_apply_eq_iff_of_isColimit
    (((isColimitCofanMkObjOfIsColimit ((CategoryTheory.evaluation _ _).obj _) _ _
      (coproductIsCoproduct _)))) _ _

instance {j : ι} (c : f.Cell j) : Mono c.ιSigmaStdSimplex := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨⟨d⟩⟩
  rw [mono_iff_injective]
  intro x y h
  simpa [f.ιSigmaStdSimplex_eq_iff] using h.symm

/-- The coproduct of the horn inclusions corresponding to all the cells
of rank `j` for a rank function for a proper pairing of a subcomplex
of a simplicial set. -/
noncomputable def m (j : ι) : f.sigmaHorn j ⟶ f.sigmaStdSimplex j :=
  Limits.Sigma.map (basicCell _ _)

instance (j : ι) : Mono (f.m j) :=
  MorphismProperty.colimitsOfShape_le (W := .monomorphisms _) _
    (MorphismProperty.colimitsOfShape_colimMap _
      (fun ⟨c⟩ ↦ by dsimp; infer_instance))

@[reassoc (attr := simp)]
lemma Cell.ι_m {j : ι} (c : f.Cell j) :
    c.ιSigmaHorn ≫ f.m j = c.horn.ι ≫ c.ιSigmaStdSimplex := by
  simp [m]

@[simp]
lemma Cell.preimage_filtration_map {j : ι} (c : f.Cell j) :
    (f.filtration j).preimage c.map = c.horn := by
  apply le_antisymm
  · simpa only [subcomplex_le_horn_iff, ← Subcomplex.image_le_iff,
      Cell.image_face_index_compl] using c.subcomplex_not_le_filtration
  · rw [← Subcomplex.image_le_iff, N.subcomplex_le_iff]
    intro s hs
    cases s using N.cases A with
    | mem s hs' => exact hs'.trans (by simp)
    | notMem s =>
      obtain ⟨t, ht⟩ := P.exists_or s
      rw [← c.rank_s]
      refine le_trans ?_ (f.subcomplex_le_filtration ⟨t, rfl⟩ (f.lt ?_))
      · obtain rfl | rfl := ht
        · exact P.le t
        · simp
      · replace hs : t.val.subcomplex ≤ c.horn.image c.map := by
          obtain rfl | rfl := ht
          · exact hs
          · refine le_trans ?_ hs
            rw [← S.le_def]
            exact (P.isUniquelyCodimOneFace t).le
        refine ⟨?_, ?_⟩
        · rintro rfl
          exact c.subcomplex_not_le_image_horn hs
        · rw [Subcomplex.N.lt_iff, SSet.N.lt_iff]
          exact lt_of_le_of_lt hs (c.image_horn_lt_subcomplex)

/-- Given a cell `c` of rank `j` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is the induced
morphism `c.horn ⟶ f.filtration j`. -/
noncomputable def Cell.mapHorn {j : ι} (c : f.Cell j) : (c.horn : SSet) ⟶ f.filtration j :=
  Subcomplex.lift (c.horn.ι ≫ c.map) (by
    simp [← image_top, image_le_iff, preimage_comp, c.preimage_filtration_map])

@[reassoc (attr := simp)]
lemma Cell.mapHorn_ι {j : ι} (c : f.Cell j) :
    c.mapHorn ≫ (f.filtration j).ι = c.horn.ι ≫ c.map := rfl

/-- Given a rank function `f : P.RankFunction ι` for a proper pairing `P`
of a subcomplex of a simplicial set, this is the induced morphism
`f.sigmaHorn j ⟶ f.filtration j` for any `j : ι`. -/
noncomputable def t (j : ι) : f.sigmaHorn j ⟶ f.filtration j :=
  Sigma.desc (fun c ↦ c.mapHorn)

variable {f} in
@[reassoc (attr := simp)]
lemma Cell.ι_t {j : ι} (c : f.Cell j) : c.ιSigmaHorn ≫ f.t j = c.mapHorn := by
  simp [t, Sigma.ι_desc]

variable {f} in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma Cell.ι_t_app {j : ι} (c : f.Cell j) (x : SimplexCategoryᵒᵖ) :
    c.ιSigmaHorn.app x ≫ (f.t j).app x = c.mapHorn.app x :=
  NatTrans.congr_app c.ι_t x

/-- Given a rank `j` cell `c` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is
the nondegenerate simplex in `f.sigmaStdSimplex j`
not in the image of `f.m j : f.sigmaHorn j ⟶ f.sigmaStdSimplex j`
which corresponds to `c.ιSigmaStdSimplex`. -/
@[simps]
noncomputable def Cell.type₁ {j : ι} (c : f.Cell j) : (Subcomplex.range (f.m j)).N where
  simplex := c.ιSigmaStdSimplex.app _ (stdSimplex.objEquiv.symm (𝟙 _))
  nonDegenerate := by
    rw [nonDegenerate_iff_of_mono, stdSimplex.mem_nonDegenerate_iff_mono,
      Equiv.apply_symm_apply]
    infer_instance
  notMem := by
    rintro ⟨y, hy⟩
    obtain ⟨x', ⟨y, hy'⟩, rfl⟩ := f.ιSigmaHorn_jointly_surjective y
    rw [← NatTrans.comp_app_apply, ι_m, NatTrans.comp_app_apply, ιSigmaStdSimplex_eq_iff] at hy
    obtain ⟨rfl, rfl⟩ := hy
    exact objEquiv_symm_notMem_horn_of_isIso _ _ hy'

/-- Given a rank `j` cell `c` for a rank function `f` for a proper
pairing of a subcomplex of a simplicial set, this is
the nondegenerate simplex in `f.sigmaStdSimplex j`
not in the image of `f.m j : f.sigmaHorn j ⟶ f.sigmaStdSimplex j`
which corresponds to the `c.index`th-face of `c.type₁`. -/
@[simps]
noncomputable def Cell.type₂ {j : ι} (c : f.Cell j) : (Subcomplex.range (f.m j)).N where
  simplex := c.ιSigmaStdSimplex.app _
    (stdSimplex.objEquiv.symm (SimplexCategory.δ c.index))
  nonDegenerate := by
    rw [nonDegenerate_iff_of_mono, stdSimplex.mem_nonDegenerate_iff_mono,
      Equiv.apply_symm_apply]
    infer_instance
  notMem := by
    rintro ⟨y, hy⟩
    obtain ⟨x', ⟨y, hy'⟩, rfl⟩ := f.ιSigmaHorn_jointly_surjective y
    rw [← NatTrans.comp_app_apply, ι_m, NatTrans.comp_app_apply, ιSigmaStdSimplex_eq_iff] at hy
    obtain ⟨rfl, rfl⟩ := hy
    simpa using (objEquiv_symm_δ_mem_horn_iff _ _).mp hy'

set_option backward.isDefEq.respectTransparency false in
lemma exists_or_of_range_m_N {j : ι} (s : (Subcomplex.range (f.m j)).N) :
    ∃ (c : f.Cell j), s = c.type₁ ∨ s = c.type₂ := by
  obtain ⟨d, s, hs, hs', rfl⟩ := s.mk_surjective
  obtain ⟨x, s, rfl⟩ := f.ιSigmaStdSimplex_jointly_surjective s
  replace hs' : s ∉ (horn _ x.index).obj _ :=
    fun h ↦ hs' ⟨x.ιSigmaHorn.app _ ⟨_, h⟩, by rw [← NatTrans.comp_app_apply]; simp⟩
  obtain ⟨g, rfl⟩ := stdSimplex.objEquiv.symm.surjective s
  rw [nonDegenerate_iff_of_mono, stdSimplex.mem_nonDegenerate_iff_mono,
    Equiv.apply_symm_apply] at hs
  obtain hd | rfl := (SimplexCategory.le_of_mono g).lt_or_eq
  · rw [Nat.lt_succ_iff] at hd
    obtain hd | rfl := hd.lt_or_eq
    · exact (hs' (by simp [horn_obj_eq_univ x.index d (by lia)])).elim
    · obtain ⟨i, rfl⟩ := SimplexCategory.eq_δ_of_mono g
      obtain rfl := (objEquiv_symm_δ_notMem_horn_iff _ _).mp hs'
      exact ⟨x, Or.inr rfl⟩
  · obtain rfl := SimplexCategory.eq_id_of_mono g
    exact ⟨x, Or.inl rfl⟩

variable [SuccOrder ι] [NoMaxOrder ι]

/-- Given a rank function `f : P.RankFunction ι` for a proper pairing `P`
of a subcomplex of a simplicial set, this is the induced morphism
`f.sigmaStdSimplex j ⟶ f.filtration (Order.succ j)` for any `j : ι`. -/
noncomputable def b (j : ι) : f.sigmaStdSimplex j ⟶ f.filtration (Order.succ j) :=
  Sigma.desc (fun c ↦ c.mapToSucc)

variable {f} in
@[reassoc (attr := simp)]
lemma Cell.ι_b {j : ι} (c : f.Cell j) : c.ιSigmaStdSimplex ≫ f.b j = c.mapToSucc := by
  simp [b, Sigma.ι_desc]

variable {f} in
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma Cell.ι_b_app {j : ι} (c : f.Cell j) (x : SimplexCategoryᵒᵖ) :
    c.ιSigmaStdSimplex.app x ≫ (f.b j).app x = c.mapToSucc.app x :=
  NatTrans.congr_app c.ι_b x

@[reassoc]
lemma w (j : ι) :
    f.t j ≫ homOfLE (f.filtration_monotone (Order.le_succ j)) = f.m j ≫ f.b j := by
  ext c : 1
  simp [← cancel_mono (Subcomplex.ι _)]

set_option backward.isDefEq.respectTransparency false in
lemma isPullback (j : ι) :
    IsPullback (f.t j) (f.m j) (homOfLE (f.filtration_monotone (Order.le_succ j))) (f.b j) where
  w := f.w j
  isLimit' := ⟨evaluationJointlyReflectsLimits _ (fun ⟨⟨d⟩⟩ ↦ by
    refine (isLimitMapConePullbackConeEquiv _ _).symm
      (IsPullback.isLimit ?_)
    rw [Types.isPullback_iff]
    dsimp
    refine ⟨congr_app (f.w j) (op ⦋d⦌),
      fun a₁ a₂ h ↦ (mono_iff_injective _).mp
        ((NatTrans.mono_iff_mono_app (f.m j)).mp inferInstance _) h.2, fun y b h ↦ ?_⟩
    obtain ⟨x, b, rfl⟩ := f.ιSigmaStdSimplex_jointly_surjective b
    have hb : b ∈ Λ[_, x.index].obj _ := by
      obtain ⟨y, hy⟩ := y
      simp only [← x.preimage_filtration_map]
      rw [Subtype.ext_iff] at h
      dsimp at h
      subst h
      rwa [x.ι_b_app_apply] at hy
    refine ⟨x.ιSigmaHorn.app _ ⟨b, hb⟩, ?_, ?_⟩
    · simpa only [Subfunctor.toFunctor_obj, Subtype.ext_iff,
        x.ι_b_app_apply, x.ι_t_app_apply] using h.symm
    · rw [← NatTrans.comp_app_apply]
      simp)⟩

set_option backward.isDefEq.respectTransparency false in
lemma range_homOfLE_app_union_range_b_app (j : ι) (d : SimplexCategoryᵒᵖ) :
    Set.range ((homOfLE (f.filtration_monotone (Order.le_succ j))).app d) ⊔
      Set.range ((f.b j).app d) = Set.univ := by
  ext ⟨x, hx⟩
  -- generated by `simp? [filtration_def, Subtype.ext_iff] at hx ⊢`
  simp only [filtration_def, Order.lt_succ_iff, Subfunctor.max_obj, Subfunctor.iSup_obj,
    Set.mem_union, Set.mem_iUnion, exists_prop, Subfunctor.toFunctor_obj, Subfunctor.homOfLe_app,
    TypeCat.hom_ofHom, TypeCat.Fun.coe_mk, Set.sup_eq_union, Set.mem_range, Subtype.ext_iff,
    Subtype.exists, exists_eq_right, Set.mem_univ, iff_true] at hx ⊢
  obtain hx | ⟨i, hi, c, hx⟩ := hx
  · exact Or.inl (Or.inl hx)
  · obtain hi | rfl := hi.lt_or_eq
    · exact Or.inl (Or.inr ⟨i, hi, c, hx⟩)
    · rw [← c.range_map, ← c.mapToSucc_ι, ← c.ι_b_assoc] at hx
      obtain ⟨y, hy⟩ := hx
      exact Or.inr ⟨_, hy⟩

/-- Given a rank function `f : P.RankFunction ι` for a proper pairing
of a subcomplex of a simplicial set `X`, this is the simplex of `X`
corresponding to an element in `(Subcomplex.range (f.m j)).N`. -/
noncomputable def mapN {j : ι} (x : (Subcomplex.range (f.m j)).N) : X.S :=
  S.mk ((f.b j).app _ x.simplex).val

@[simp]
lemma mapN_type₁ {j : ι} (c : f.Cell j) : f.mapN c.type₁ = S.mk (P.p c.s).val.simplex := by
  dsimp only [Cell.type₁, mapN]
  rw [← S.cast_eq_self _ (P.dim_p c.s)]
  dsimp
  rw [S.ext_iff, c.ι_b_app_apply]
  apply yonedaEquiv_symm_app_id

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma mapN_type₂ {j : ι} (c : f.Cell j) : f.mapN c.type₂ = S.mk c.s.val.simplex := by
  dsimp [mapN]
  rw [S.ext_iff, c.ι_b_app_apply, Cell.mapToSucc]
  dsimp
  rw [Cell.map_app_objEquiv_symm_δ_index]

private lemma isPushout_aux₁ {j : ι} (s : (Subcomplex.range (f.m j)).N) :
    (f.mapN s).simplex  ∈ SSet.nonDegenerate _ _ := by
  obtain ⟨c, rfl | rfl⟩ := f.exists_or_of_range_m_N s
  · rw [f.mapN_type₁]
    exact (P.p c.s).val.nonDegenerate
  · rw [f.mapN_type₂]
    exact c.s.val.nonDegenerate

private lemma isPushout_aux₂ {j : ι} : Function.Injective (f.mapN (j := j)) := by
  intro s t h
  obtain ⟨c, rfl | rfl⟩ := f.exists_or_of_range_m_N s <;>
    obtain ⟨c', rfl | rfl⟩ := f.exists_or_of_range_m_N t <;>
    simp only [mapN_type₁, mapN_type₂, ← Subcomplex.N.eq_iff_sMk_eq,
      ← Subtype.ext_iff] at h
  · obtain rfl : c = c' := by ext : 1; exact P.p.injective h
    rfl
  · exact (P.ne _ _ h).elim
  · exact (P.ne _ _ h.symm).elim
  · congr; aesop

private lemma isPushout_aux₃ {j : ι} :
    Function.Injective fun (x : (Subcomplex.range (f.m j)).N) ↦ S.mk ((f.b j).app _ x.simplex) :=
  fun _ _ h ↦ f.isPushout_aux₂ (congr_arg (S.map (Subcomplex.ι _)) h)

set_option backward.isDefEq.respectTransparency false in
lemma isPushout (j : ι) :
    IsPushout (f.t j) (f.m j) (homOfLE (f.filtration_monotone (Order.le_succ j))) (f.b j) where
  w := f.w j
  isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun ⟨⟨d⟩⟩ ↦ by
    refine (isColimitMapCoconePushoutCoconeEquiv _ _).symm
      (IsPushout.isColimit ?_)
    refine Types.isPushout_of_isPullback_of_mono'
      ((f.isPullback j).map ((CategoryTheory.evaluation _ _).obj _))
      (f.range_homOfLE_app_union_range_b_app _ _) (fun x₁ x₂ hx₁ hx₂ h ↦ ?_)
    obtain ⟨s₁, g₁, _, hg₁⟩ := (Subcomplex.range (f.m j)).existsN x₁ hx₁
    obtain ⟨s₂, g₂, _, hg₂⟩ := (Subcomplex.range (f.m j)).existsN x₂ hx₂
    obtain rfl : s₁ = s₂ := f.isPushout_aux₃ (by
      dsimp
      rw [S.eq_iff_ofSimplex_eq, ← Subcomplex.ofSimplex_map_of_epi g₁,
        ← Subcomplex.ofSimplex_map_of_epi g₂]
      · simp [← dsimp% (f.b j).naturality_apply, hg₁, hg₂, dsimp% h]
      all_goals
      · rw [Subcomplex.mem_nonDegenerate_iff]
        apply f.isPushout_aux₁)
    obtain rfl := X.unique_nonDegenerate_map (x := (((f.b _)).app _ x₁).val)
      g₁ ⟨_, f.isPushout_aux₁ s₁⟩
        (by simp [mapN, ← hg₁, dsimp% NatTrans.naturality_apply (f.b j)])
      g₂ ⟨_, f.isPushout_aux₁ s₁⟩
        (by simp [mapN, dsimp% h, ← hg₂, dsimp% NatTrans.naturality_apply (f.b j)])
    rw [← hg₁, hg₂])⟩

end

variable [SuccOrder ι] [OrderBot ι] [NoMaxOrder ι] [WellFoundedLT ι]

instance : f.filtration_monotone.functor.IsWellOrderContinuous where
  nonempty_isColimit m hm := ⟨Preorder.isColimitOfIsLUB _ _ (by
    dsimp
    rw [← f.iSup_filtration_iio m hm]
    apply isLUB_iSup)⟩

/-- Given a rank function `f : P.RankFunction ι` for a
proper pairing `P` of a subcomplex `A` of simplicial set `X`,
the inclusion `A.ι` is a relative cell complex with basic cells
given by horn inclusions. -/
noncomputable def relativeCellComplex :
    RelativeCellComplex f.basicCell A.ι where
  F := f.filtration_monotone.functor ⋙ Subcomplex.toSSetFunctor
  isoBot := Subcomplex.eqToIso (filtration_bot _)
  isColimit :=
    IsColimit.ofIsoColimit (isColimitOfPreserves Subcomplex.toSSetFunctor
      (Preorder.colimitCoconeOfIsLUB f.filtration_monotone.functor (pt := ⊤)
        (by rw [← f.iSup_filtration]; apply isLUB_iSup)).isColimit)
        (Cocone.ext (Subcomplex.topIso _))
  isWellOrderContinuous :=
    ⟨fun m hm ↦ ⟨isColimitOfPreserves Subcomplex.toSSetFunctor
      (Functor.isColimitOfIsWellOrderContinuous f.filtration_monotone.functor m hm)⟩⟩
  incl.app i := (f.filtration i).ι
  attachCells j _ :=
    { ι := f.Cell j
      π := id
      cofan₁ := _
      cofan₂ := _
      isColimit₁ := colimit.isColimit _
      isColimit₂ := colimit.isColimit _
      m := f.m j
      hm c := c.ι_m
      g₁ := f.t j
      g₂ := f.b j
      isPushout := f.isPushout j }

end SSet.Subcomplex.Pairing.RankFunction
