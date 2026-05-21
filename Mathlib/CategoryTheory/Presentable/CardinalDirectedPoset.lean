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
types (with order embeddings as morphisms), and we show that it is
a `κ`-accessible category.

If `κ ≤ κ'` where `κ'` is also a regular cardinal, we characterize
the `κ'`-presentable objects of `CardinalFilteredPoset κ` as
the objects `J` such that the underlying type `J.obj` has
cardinality `< κ'`.

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
    letI := isFiltered_of_isCardinalFiltered J κ
    IsCardinalFiltered (CoconePt hc) κ := by
  letI := isFiltered_of_isCardinalFiltered J κ
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

lemma Hom.injective {J₁ J₂ : CardinalFilteredPoset κ} (f : J₁ ⟶ J₂) :
    Function.Injective f := f.hom.injective

lemma Hom.le_iff_le {J₁ J₂ : CardinalFilteredPoset κ} (f : J₁ ⟶ J₂) (x₁ x₂ : J₁.obj) :
    f x₁ ≤ f x₂ ↔ x₁ ≤ x₂ :=
  f.hom.hom.le_iff_le

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

variable (κ) in
/-- The property of posets in `CardinalFilteredPoset κ` that are
of cardinality `< κ` and have terminal object. -/
def hasCardinalLTWithTerminal : ObjectProperty (CardinalFilteredPoset κ) :=
  fun J ↦ HasCardinalLT J.obj κ ∧ HasTerminal J.obj

instance : ObjectProperty.EssentiallySmall.{u} (hasCardinalLTWithTerminal κ) where
  exists_small_le' := by
    obtain ⟨X, hX⟩ : ∃ (X : Type u), Cardinal.mk X = κ := ⟨κ.ord.ToType, by simp⟩
    let α : Type u := Σ (S : Set X) (_ : PartialOrder S),
      ULift.{u} (PLift (IsCardinalFiltered S κ))
    let (a : α) : PartialOrder a.1 := a.2.1
    let ι (a : α) : CardinalFilteredPoset κ :=
      { obj := .of a.1
        property := a.2.2.down.down }
    refine ⟨.ofObj ι, inferInstance, fun J ⟨hJ, _⟩ ↦ ?_⟩
    obtain ⟨f⟩ : Cardinal.mk J.obj ≤ Cardinal.mk X := by
      simpa [hX] using ((hasCardinalLT_iff_cardinal_mk_lt _ _).1 hJ).le
    let e := Equiv.ofInjective _ f.injective
    letI : PartialOrder (Set.range f) := PartialOrder.lift e.symm e.symm.injective
    let e' : Set.range f ≃o J.obj := { toEquiv := e.symm, map_rel_iff' := by rfl }
    exact ⟨_, ⟨⟨Set.range f, inferInstance,
      ⟨⟨IsCardinalFiltered.of_equivalence κ e'.symm.equivalence⟩⟩⟩⟩,
        ⟨CardinalFilteredPoset.ι.preimageIso (PartOrdEmb.Iso.mk (by exact e'.symm))⟩⟩

set_option backward.isDefEq.respectTransparency false in
lemma isCardinalPresentable_of_hasCardinalLT_of_le (J : CardinalFilteredPoset κ)
    {κ' : Cardinal.{u}} [Fact κ'.IsRegular] (hJ : HasCardinalLT J.obj κ') (h : κ ≤ κ') :
    IsCardinalPresentable J κ' where
  preservesColimitOfShape A _ _ := ⟨fun {F} ↦ ⟨fun {c} hc ↦ ⟨by
  · have := isFiltered_of_isCardinalFiltered A κ'
    have := IsCardinalFiltered.of_le A h
    replace hc := isColimitOfPreserves (forget _) hc
    refine Types.FilteredColimit.isColimitOf' _ _ (fun f ↦ ?_) (fun j f g h ↦ ?_)
    · dsimp at f
      choose j g hg using fun (x : J.obj) ↦ Types.jointly_surjective_of_isColimit hc (f x)
      let m := IsCardinalFiltered.max j hJ
      let φ (x : J.obj) : (F.obj m).obj := F.map (IsCardinalFiltered.toMax j hJ x) (g x)
      have hφ (x : J.obj) : f x = c.ι.app _ (φ x) := by
        dsimp [φ]
        rw [← hg, ← ConcreteCategory.comp_apply, c.w]
        rfl
      refine ⟨m,
        ObjectProperty.homMk (PartOrdEmb.ofHom
          { toFun := φ
            inj' x y h := Hom.injective f (by simpa [hφ])
            map_rel_iff' {x y} := ?_ }), ?_⟩
      · simp only [Function.Embedding.coeFn_mk,
          ← Hom.le_iff_le f, hφ, Hom.le_iff_le (c.ι.app m)]
      · dsimp
        ext x
        exact (hg x).symm.trans
          (ConcreteCategory.congr_hom (c.w (IsCardinalFiltered.toMax j hJ x)).symm (g x))
    · choose k a hk using fun (x : J.obj) ↦
        (Types.FilteredColimit.isColimit_eq_iff' hc _ _).1 (ConcreteCategory.congr_hom h x)
      dsimp at f g h k a hk ⊢
      obtain ⟨l, b, c, hl⟩ : ∃ (l : A) (c : j ⟶ l) (b : ∀ x, k x ⟶ l),
          ∀ x, a x ≫ b x = c := by
        let φ (x : J.obj) : j ⟶ IsCardinalFiltered.max k hJ :=
          a x ≫ IsCardinalFiltered.toMax k hJ x
        exact ⟨IsCardinalFiltered.coeq φ hJ,
          IsCardinalFiltered.toCoeq φ hJ,
          fun x ↦ IsCardinalFiltered.toMax k hJ x ≫ IsCardinalFiltered.coeqHom φ hJ,
          fun x ↦ by simpa [φ] using IsCardinalFiltered.coeq_condition φ hJ x⟩
      refine ⟨l, b, ?_⟩
      ext x
      simpa only [← hl x, Functor.map_comp, ObjectProperty.FullSubcategory.comp_hom,
        PartOrdEmb.hom_comp, RelEmbedding.coe_trans, Function.comp_apply]
          using congr_arg _ (hk x)⟩⟩⟩

namespace coconeWithTop

variable (J : CardinalFilteredPoset κ)

instance (κ' : Cardinal.{u}) [Fact κ'.IsRegular] :
    IsCardinalFiltered (WithTop (J.obj)) κ' :=
  isCardinalFiltered_of_hasTerminal _ _

abbrev withTop : CardinalFilteredPoset κ := .of (.of (WithTop J.obj))

@[nolint unusedArguments]
def indexSet {κ' : Cardinal.{u}} [Fact κ'.IsRegular] (_ : κ ≤ κ') :
    Set (Set (withTop J).obj) :=
  setOf (fun S ↦ HasCardinalLT S κ' ∧ ⊤ ∈ S)

variable {κ' : Cardinal.{u}} [Fact κ'.IsRegular] {h : κ ≤ κ'}

variable {J} (h) in
lemma pair_mem_indexSet (j : J.obj) : {WithBot.some j, ⊤} ∈ indexSet J h :=
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

variable (h)
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

@[simps]
def coconeWithTop : Cocone (coconeWithTop.functor J h) where
  pt := .of (.of (WithTop J.obj))
  ι.app _ := ObjectProperty.homMk (PartOrdEmb.ofHom (OrderEmbedding.subtype _))

open coconeWithTop in
noncomputable def isColimitCoconeWithTop :
    IsColimit (coconeWithTop J h) :=
  isColimitOfReflects (CardinalFilteredPoset.ι ⋙ forget PartOrdEmb) (by
    refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun j ⟨x, _⟩ ⟨y, _⟩ h ↦ ?_)
    · induction x with
      | some x =>
        exact ⟨⟨_, pair_mem_indexSet _ x⟩, ⟨x, Set.mem_insert _ _⟩, rfl⟩
      | none =>
        exact ⟨⟨_, pair_mem_indexSet _ (Classical.arbitrary _)⟩,
          ⟨⊤, Set.mem_insert_of_mem _ rfl⟩, rfl⟩
    · obtain rfl : x = y := by simpa using h
      exact ⟨j, 𝟙 _, rfl⟩)

include h in
protected lemma isCardinalPresentable_iff :
    IsCardinalPresentable J κ' ↔ HasCardinalLT J.obj κ' := by
  refine ⟨fun _ ↦ ?_, fun hJ ↦ isCardinalPresentable_of_hasCardinalLT_of_le _ hJ h⟩
  obtain ⟨X, f, hf⟩ :=
    IsCardinalPresentable.exists_hom_of_isColimit κ' (isColimitCoconeWithTop J h)
      (ObjectProperty.homMk (PartOrdEmb.ofHom WithTop.coeOrderHom))
  replace hf : OrderEmbedding.subtype X.1 ∘ f = WithTop.coeOrderHom := by
    ext x
    exact ConcreteCategory.congr_hom hf x
  refine X.2.1.of_injective f (Function.Injective.of_comp
    (f := OrderEmbedding.subtype X.1) ?_)
  dsimp at hf ⊢
  rw [hf]
  exact WithTop.coe_injective

end

protected lemma isCardinalPresentable_iff' (J : CardinalFilteredPoset κ) :
    IsCardinalPresentable J κ ↔ HasCardinalLT J.obj κ :=
  CardinalFilteredPoset.isCardinalPresentable_iff _ (le_refl _)

namespace cocone

variable (J : CardinalFilteredPoset κ)

/-- Given `J : CardinalFilteredPoset κ`, this is hte partially ordered set consisting
of subsets of `J.obj` that are of cardinality `< κ` and have a terminal object. -/
def indexSet : Set (Set J.obj) := setOf (fun S ↦ HasCardinalLT S κ ∧ HasTerminal S)

instance (S : indexSet J) : HasTerminal S := S.prop.2

instance (S : indexSet J) : IsCardinalFiltered S κ := isCardinalFiltered_of_hasTerminal _ _

variable {J} in
lemma singleton_mem_indexSet (j : J.obj) : {j} ∈ indexSet J :=
  ⟨hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out), by
    let : OrderTop ({j} : Set J.obj) := { top := ⟨j, rfl⟩, le_top := by simp }
    exact isTerminalTop.hasTerminal⟩

instance : IsCardinalFiltered (indexSet J) κ :=
  isCardinalFiltered_preorder _ _ (fun K α hK ↦ by
    rw [← hasCardinalLT_iff_cardinal_mk_lt] at hK
    let t (k : K) : (α k).val := ⊤_ _
    let m := IsCardinalFiltered.max (fun k ↦ (t k).val) hK
    let S : Set J.obj := (⋃ (k : K), α k) ∪ {m}
    let : OrderTop S :=
      { top := ⟨m, by simp [S]⟩
        le_top := by
          rintro ⟨s, hs⟩
          simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_iUnion, S] at hs
          obtain rfl | ⟨k, hs⟩ := hs
          · simp
          · simp only [Subtype.mk_le_mk]
            exact leOfHom ((by exact terminal.from (C := (α k).val) ⟨_, hs⟩) ≫
              IsCardinalFiltered.toMax _ hK k) }
    refine ⟨⟨S, ?_, isTerminalTop.hasTerminal⟩, fun k ↦ ?_⟩
    · have hκ : Cardinal.aleph0 ≤ κ :=  Cardinal.IsRegular.aleph0_le Fact.out
      exact hasCardinalLT_union hκ (hasCardinalLT_iUnion _ hK (fun k ↦ (α k).2.1))
        (hasCardinalLT_of_finite _ _ hκ)
    · simp only [← Subtype.coe_le_coe, Set.le_eq_subset]
      exact subset_trans (Set.subset_iUnion_of_subset k (subset_refl _)) Set.subset_union_left )

instance : IsFiltered (indexSet J) := isFiltered_of_isCardinalFiltered _ κ

/-- Given `J : CardinalFilteredPoset κ`, this is the functor which sends
a subset `S` of `J.obj` of cardinality `< κ` with a terminal object to `S`
as an object in `CardinalFilteredPoset κ`. -/
@[simps]
def functor : indexSet J ⥤ CardinalFilteredPoset κ where
  obj S := of (PartOrdEmb.of S.val)
  map f := ObjectProperty.homMk (PartOrdEmb.ofHom
    { toFun x := ⟨x, leOfHom f x.2⟩
      inj' := by rintro ⟨x, _⟩ ⟨y, _⟩ h; simpa using h
      map_rel_iff' := by rfl })

end cocone

/-- The (colimit) cocone which expresses `J : CardinalFilteredPoset κ` as a colimit
of its subsets that are of cardinality `< κ` and have a terminal object. -/
@[simps]
def cocone (J : CardinalFilteredPoset κ) : Cocone (cocone.functor J) where
  pt := J
  ι.app _ := ObjectProperty.homMk (PartOrdEmb.ofHom (OrderEmbedding.subtype _))

open cocone in
/-- Any object `J : CardinalFilteredPoset κ` is a colimit
of its subsets that are of cardinality `< κ` and have a terminal object. -/
noncomputable def isColimitCocone (J : CardinalFilteredPoset κ) :
    IsColimit (cocone J) :=
  isColimitOfReflects (CardinalFilteredPoset.ι ⋙ forget PartOrdEmb) (by
    refine Types.FilteredColimit.isColimitOf' _ _ (fun x ↦ ?_) (fun j ⟨x, _⟩ ⟨y, _⟩ h ↦ ?_)
    · exact ⟨⟨_, singleton_mem_indexSet x⟩, ⟨x, rfl⟩, rfl⟩
    · obtain rfl : x = y := by simpa using h
      exact ⟨j, 𝟙 _, rfl⟩)

variable (κ) in
lemma isCardinalFilteredGenerator_hasCardinalLTWithTerminal :
    (hasCardinalLTWithTerminal κ).IsCardinalFilteredGenerator κ where
  le_isCardinalPresentable := by
    rintro J ⟨_, _⟩
    rwa [isCardinalPresentable_iff, J.isCardinalPresentable_iff']
  exists_colimitsOfShape J :=
    ⟨_, inferInstance, inferInstance, ⟨{
      diag := _
      ι := _
      isColimit := isColimitCocone J
      prop_diag_obj j := j.2 }⟩⟩

instance : IsCardinalAccessibleCategory (CardinalFilteredPoset κ) κ where
  exists_generator :=
    ⟨hasCardinalLTWithTerminal κ, inferInstance,
      isCardinalFilteredGenerator_hasCardinalLTWithTerminal κ⟩

end CardinalFilteredPoset

end CategoryTheory
