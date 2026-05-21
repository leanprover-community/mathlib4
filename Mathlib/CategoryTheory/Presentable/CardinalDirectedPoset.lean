/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Preorder
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.Order.Category.PartOrdEmb

/-!
# The κ-accessible category of κ-directed posets

Given a regular cardinal `κ : Cardinal.{u}`, we define the
category `CardinalFilteredPoset κ` of `κ`-directed partially ordered
types (with order embeddings as morphisms). We shall show that it is
a `κ`-accessible category (TODO @joelriou).

## References
* [Adámek, J. and Rosický, J., *Locally presentable and accessible categories*][Adamek_Rosicky_1994]

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace PartOrdEmb

variable (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- The property of objects in `PartOrdEmb` that are
satisfied by partially ordered types of cardinality `< κ`. -/
abbrev isCardinalFiltered : ObjectProperty PartOrdEmb.{u} :=
  fun X ↦ IsCardinalFiltered X κ

@[simp]
lemma isCardinalFiltered_iff (X : PartOrdEmb.{u}) :
    isCardinalFiltered κ X ↔ IsCardinalFiltered X κ := Iff.rfl

instance : (isCardinalFiltered κ).IsClosedUnderIsomorphisms where
  of_iso e _ := .of_equivalence κ (orderIsoOfIso e).equivalence

namespace Limits.CoconePt

variable {κ} {J : Type u} [SmallCategory J] [IsCardinalFiltered J κ]
  {F : J ⥤ PartOrdEmb.{u}} {c : Cocone (F ⋙ forget _)} (hc : IsColimit c)

lemma isCardinalFiltered_pt (hF : ∀ j, IsCardinalFiltered (F.obj j) κ) :
    haveI := isFiltered_of_isCardinalFiltered J κ
    IsCardinalFiltered (CoconePt hc) κ := by
  haveI := isFiltered_of_isCardinalFiltered J κ
  refine isCardinalFiltered_preorder _ _ (fun K f hK ↦ ?_)
  rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
  choose j₀ x₀ hx₀ using fun k ↦ Types.jointly_surjective_of_isColimit hc (f k)
  let j := IsCardinalFiltered.max j₀ hK
  let x₁ (k : K) : F.obj j := F.map (IsCardinalFiltered.toMax j₀ hK k) (x₀ k)
  have hx₁ (k : K) : c.ι.app j (x₁ k) = c.ι.app (j₀ k) (x₀ k) :=
    ConcreteCategory.congr_hom (c.w (IsCardinalFiltered.toMax j₀ hK k)) _
  refine ⟨(cocone hc).ι.app j (IsCardinalFiltered.max x₁ hK),
    fun k ↦ ?_⟩
  rw [← hx₀, ← hx₁]
  exact ((cocone hc).ι.app j).hom.monotone
    (leOfHom (IsCardinalFiltered.toMax x₁ hK k))

end Limits.CoconePt

instance (J : Type u) [SmallCategory J] [IsCardinalFiltered J κ] :
    (isCardinalFiltered κ).IsClosedUnderColimitsOfShape J where
  colimitsOfShape_le := by
    have := isFiltered_of_isCardinalFiltered J κ
    rintro X ⟨p⟩
    simp only [(isCardinalFiltered κ).prop_iff_of_iso
      (p.isColimit.coconePointUniqueUpToIso
        (Limits.isColimitCocone (colimit.isColimit (p.diag ⋙ forget PartOrdEmb)))),
      isCardinalFiltered_iff, Limits.cocone_pt_coe]
    exact Limits.CoconePt.isCardinalFiltered_pt _ p.prop_diag_obj

end PartOrdEmb

namespace CategoryTheory

variable (κ : Cardinal.{u}) [Fact κ.IsRegular]

/-- The category of `κ`-filtered partially ordered types,
with morphisms given by order embeddings. -/
abbrev CardinalFilteredPoset :=
  (PartOrdEmb.isCardinalFiltered κ).FullSubcategory

variable {κ}

/-- The embedding of the category of `κ`-filtered
partially ordered types in the category of partially
ordered types. -/
abbrev CardinalFilteredPoset.ι : CardinalFilteredPoset κ ⥤ PartOrdEmb :=
  ObjectProperty.ι _

namespace CardinalFilteredPoset

/-- Constructor for objects in `CardinalFilteredPoset κ`. -/
abbrev of (J : PartOrdEmb.{u}) [IsCardinalFiltered J κ] : CardinalFilteredPoset κ where
  obj := J
  property := inferInstance

instance (J : CardinalFilteredPoset κ) : IsCardinalFiltered J.obj κ := J.property

instance (J : CardinalFilteredPoset κ) : IsFiltered J.obj :=
  isFiltered_of_isCardinalFiltered _ κ

instance (J : CardinalFilteredPoset κ) : Nonempty J.obj := IsFiltered.nonempty

instance : HasCardinalFilteredColimits (CardinalFilteredPoset κ) κ where
  hasColimitsOfShape J _ _ := by
    have := isFiltered_of_isCardinalFiltered J κ
    infer_instance

instance (A : Type u) [SmallCategory A] [IsCardinalFiltered A κ] :
    PreservesColimitsOfShape A (forget (CardinalFilteredPoset κ)) := by
  have := isFiltered_of_isCardinalFiltered A κ
  change PreservesColimitsOfShape A (CardinalFilteredPoset.ι ⋙ forget _)
  infer_instance

instance (J : CardinalFilteredPoset κ) (κ' : Cardinal.{u}) [Fact κ'.IsRegular] :
    IsCardinalFiltered (WithTop (J.obj)) κ' :=
  isCardinalFiltered_of_hasTerminal _ _

/-- The map `CardinalFilteredPoset κ → CardinalFilteredPoset κ` which sends
a partially ordered `κ`-filtered type `J` to `WithTop J`. -/
abbrev withTop (J : CardinalFilteredPoset κ) : CardinalFilteredPoset κ :=
  .of (.of (WithTop J.obj))

namespace coconeWithTop

variable (J : CardinalFilteredPoset κ)

/-- Given two regular cardinals `κ ≤ κ'` and `J : CardinalFilteredPoset κ`,
this is the partially ordered set consisting of subsets `S` of `J.withTop`
that are of cardinality `< κ'` and contain `⊤`.
See `CardinalFilteredPoset.isColimitCoconeWithTop` for the fact that `withTop J`
identifies to the colimit of such `S`. -/
@[nolint unusedArguments]
def indexSet {κ' : Cardinal.{u}} [Fact κ'.IsRegular] (_ : κ ≤ κ') :
    Set (Set J.withTop.obj) :=
  setOf (fun S ↦ HasCardinalLT S κ' ∧ ⊤ ∈ S)

variable {κ' : Cardinal.{u}} [Fact κ'.IsRegular] {h : κ ≤ κ'}

variable {J} (h) in
lemma pair_mem_indexSet (j : J.obj) : {WithTop.some j, ⊤} ∈ indexSet J h :=
  ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out),
    Set.mem_insert_of_mem _ (by simp)⟩

instance (S : indexSet J h) : HasTerminal S :=
  IsTerminal.hasTerminal (X := ⟨⊤, S.2.2⟩)
    (IsTerminal.ofUniqueHom (fun _ ↦ homOfLE (by rw [Subtype.mk_le_mk]; exact le_top))
      (fun _ _ ↦ rfl))

instance (S : indexSet J h) : IsCardinalFiltered S κ := isCardinalFiltered_of_hasTerminal _ _

instance : IsCardinalFiltered (indexSet J h) κ' :=
  isCardinalFiltered_preorder _ _ (fun K α hK ↦ by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    have hκ' : Cardinal.aleph0 ≤ κ' := Cardinal.IsRegular.aleph0_le Fact.out
    refine ⟨⟨(⋃ (k : K), α k) ∪ {⊤},
      hasCardinalLT_union hκ' (hasCardinalLT_iUnion _ hK (fun k ↦ (α k).property.left))
        (hasCardinalLT_of_finite _ _ hκ'), by simp⟩, fun k ↦ ?_⟩
    rw [Subtype.mk_le_mk]
    simp only [Set.le_eq_subset]
    exact subset_trans (Set.subset_iUnion (fun i ↦ (α i).1) k) Set.subset_union_left)

instance : IsFiltered (indexSet J h) := isFiltered_of_isCardinalFiltered _ κ'

variable (h) in
/-- Given `J : CardinalFilteredPoset κ` and an inequality `κ ≤ κ'`
where `κ'` is a regular cardinal, this is the functor which sends
a subset `S` of `J.obj` of cardinality `< κ'` and containing `⊤` to `S`
as an object in `CardinalFilteredPoset κ`. -/
@[simps]
def functor : indexSet J h ⥤ CardinalFilteredPoset κ where
  obj S := of (.of S.val)
  map f := ObjectProperty.homMk (PartOrdEmb.ofHom
    { toFun x := ⟨x, leOfHom f x.2⟩
      inj' := by rintro ⟨x, _⟩ ⟨y, _⟩ h; simpa using h
      map_rel_iff' := by rfl })

end coconeWithTop

section

variable (J : CardinalFilteredPoset κ) {κ' : Cardinal.{u}} [Fact κ'.IsRegular] (h : κ ≤ κ')

/-- If `κ ≤ κ'` is an inequality between regular cardinals, and
`J : CardinalFilteredPoset κ`, this is the (colimit) cocone which
expresses `J.withTop` as a colimit of its subsets that are of
cardinality `< κ'` and contain `⊤`. -/
@[simps]
def coconeWithTop : Cocone (coconeWithTop.functor J h) where
  pt := J.withTop
  ι.app _ := ObjectProperty.homMk (PartOrdEmb.ofHom (OrderEmbedding.subtype _))

open coconeWithTop in
/-- If `κ ≤ κ'` is an inequality between regular cardinals, and
`J : CardinalFilteredPoset κ`, then `J.withTop` is the colimit of
its subsets that are of cardinality `< κ'` and contain `⊤`. -/
noncomputable def isColimitCoconeWithTop : IsColimit (coconeWithTop J h) :=
  isColimitOfReflects (CardinalFilteredPoset.ι ⋙ forget PartOrdEmb) (by
    refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun j ⟨x, _⟩ ⟨y, _⟩ h ↦ ?_)
    · induction x with
      | some x =>
        exact ⟨⟨_, pair_mem_indexSet _ x⟩, ⟨x, Set.mem_insert _ _⟩, rfl⟩
      | none =>
        exact ⟨⟨_, pair_mem_indexSet _ (Classical.arbitrary _)⟩,
          ⟨⊤, Set.mem_insert_of_mem _ rfl⟩, rfl⟩
    · obtain rfl : x = y := h
      exact ⟨j, 𝟙 _, rfl⟩)

end

end CardinalFilteredPoset

end CategoryTheory
