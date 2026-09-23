/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Inserter.Limits
public import Mathlib.CategoryTheory.Inserter.LocallySmall
public import Mathlib.CategoryTheory.Presentable.Comma
public import Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc
public import Mathlib.Tactic.CategoryTheory.Map
import Mathlib.Order.Interval.Set.InitialSeg

/-!
# Inserter categories are accessible

-/

namespace CategoryTheory.Inserter

universe w

section
-- Recall everything in the section below private.

/- The setup for accessibility of inserter categories, from Positetski’s paper:
`F G : K ⥤ L` are a parallel pair of κ-accessible functors between κ-accessible categories
where `F` in addition preserves κ-presentable objects. A given infinite cardinal Λ < κ such
that both `K` and `L` have colimits of Λ-chains is given, and we assume that `F` and `G` preserve
these colimits. Here, we realize `Λ` as a well-founded linear order directly
(instead of using `Cardinal.ord.ToType`). -/

section

variable {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalAccessibleCategory K κ] [IsCardinalAccessibleCategory L κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ]
    (Λ : Type w) [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ)
    [Limits.HasColimitsOfShape Λ K] [Limits.HasColimitsOfShape Λ L]
    [Limits.PreservesColimitsOfShape Λ F] [Limits.PreservesColimitsOfShape Λ G]

end

variable {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalAccessibleCategory K κ] [IsCardinalAccessibleCategory L κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ]

instance isCardinalPresentable_of_proj_isCardinalPresentable (X : Inserter F G)
    [IsCardinalPresentable X.obj κ] : IsCardinalPresentable X κ := by
  have : IsCardinalPresentable (proj F G |>.obj X) κ := by assumption
  apply IsCardinalPresentable.mk
  intro I _ filt B b hb
  have : Limits.HasColimitsOfShape I K := HasCardinalFilteredColimits.hasColimitsOfShape _ κ I
  have : Limits.HasColimitsOfShape I L := HasCardinalFilteredColimits.hasColimitsOfShape _ κ I
  have : Limits.PreservesColimitsOfShape I F :=
    Functor.IsCardinalAccessible.preservesColimitOfShape κ I
  have : Limits.PreservesColimitsOfShape I G :=
    Functor.IsCardinalAccessible.preservesColimitOfShape κ I
  have : Limits.PreservesColimitsOfShape I (proj F G) := inferInstance
  let hcolimG := Limits.isColimitOfPreserves (proj F G ⋙ G) hb
  let hcolim := Limits.isColimitOfPreserves (proj F G) hb
  refine ⟨fun f => ?_, ?_⟩
  · have : IsCardinalPresentable (F.obj X.obj) κ := inferInstance
    obtain ⟨i, f', hf'⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolim f.hom
    dsimp at f' hf'
    obtain ⟨j, u, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolimG
      (f₁ := F.map f' ≫ (B.obj i).hom) (f₂ := X.hom ≫ G.map f') (by dsimp; grind)
    refine ⟨j, ⟨f' ≫ (B.map u).hom, by grind⟩, ?_⟩
    · ext
      have := congr($(b.ι.naturality u).hom)
      dsimp at this ⊢
      grind
  · intros i f₁ f₂ h
    obtain ⟨j, u, hu⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolim
      (f₁ := f₁.hom) (f₂ := f₂.hom) congr($(h).hom)
    exact ⟨j, u, by grind⟩

variable (Λ : Type w) [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    -- (hΛ : HasCardinalLT Λ κ)
    -- [Limits.HasColimitsOfShape Λ K] [Limits.HasColimitsOfShape Λ L]
    -- [Limits.PreservesColimitsOfShape Λ F] [Limits.PreservesColimitsOfShape Λ G]

/-- The structure of a partial induction for constructing the chain
as in Positetski, 4.5.
To realize the induction, we transform `j ↦ PositetskiInductionDataUpTo … j` into a
presheaf on `j` so that we can use `Functor.WellOrderInductionData`. From
a section of the presheaf, we can extract the chain out of `J` that we are looking for. -/
@[ext]
structure PositetskiInductionDataUpTo
    (E : Inserter F G) (i : Λ) where
  /-- corresponds to all the previous ξᵢ's -/
  ξ : Set.Iic (Order.succ i) ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj
  /-- corresponds to the structure map ψᵢ : F.obj ξᵢ ⟶ G.obj ξᵢ₊₁ -/
  ψ (j : Λ) (hj : j ≤ i) :
    F.obj (ξ.obj ⟨j, hj.trans (Order.le_succ _)⟩).left.obj ⟶
      G.obj (ξ.obj ⟨Order.succ j, by simpa⟩).left.obj
  sq₁ (j : Λ) (hj : j ≤ i) :
    ψ j hj ≫ G.map (ξ.obj ⟨Order.succ j, by simpa⟩).hom =
    F.map (ξ.obj ⟨j, hj.trans (Order.le_succ _)⟩).hom ≫ E.hom
  sq₂ (j k : Λ) (hj : j ≤ k) (hki : k ≤ i) :
    ψ j (hj.trans hki) ≫ G.map (ξ.map (homOfLE (by simpa))).left.hom =
    F.map (ξ.map (homOfLE (by simpa))).left.hom ≫ ψ k hki

@[simp, grind =]
private lemma grind_helper {X : K}
  {x y : CostructuredArrow (isCardinalPresentable K κ).ι X} (f : x ⟶ y) :
      f.left.hom ≫ y.hom = x.hom := by simpa using f.w
/-- The structure of a partial induction for constructing the chain
as in Positetski, 4.5.
To realize the induction, we transform `j ↦ PositetskiInductionDataUpTo … j` into a
presheaf on `j` so that we can use `Functor.WellOrderInductionData`. From
a section of the presheaf, we can extract the chain out of `J` that we are looking for. -/
@[ext]
structure PositetskiInductionDataUpTo2
    (E : Inserter F G) (i : Λ) where
  /-- corresponds to all the previous ξᵢ's -/
  ξ : Set.Iic i ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj
  /-- A structure map ψⱼ : F.obj ξⱼ ⟶ G.obj ξₖ for all j < k ≤ i.
  In particular, this bundles a map F.obj ξᵢ₋₁ ⟶ G.obj ξᵢ when indices
  allow it. -/
  ψ (j k : Λ) (hj : j < k) (hk : k ≤ i) :
    F.obj (ξ.obj ⟨j, Set.mem_Iic.mpr <| hj.le.trans hk⟩).left.obj ⟶
      G.obj (ξ.obj ⟨k, Set.mem_Iic.mpr hk⟩).left.obj
  sq₁ (j : Λ) (hj : j < i) :
    ψ j i hj le_rfl ≫ G.map (ξ.obj ⟨i, Set.mem_Iic.mpr le_rfl⟩).hom =
    F.map (ξ.obj ⟨j, Set.mem_Iic.mpr hj.le⟩).hom ≫ E.hom
  t₁ (j k l : Λ) (hjk : j < k) (hkl : k < l) (hl : l ≤ i) :
    ψ j l (by grind) hl =
      F.map (ξ.map (homOfLE hjk.le)).left.hom ≫ ψ k l hkl (by grind)
  t₂ (j k l : Λ) (hjk : j < k) (hkl : k < l) (hl : l ≤ i) :
    ψ j l (by grind) hl =
      ψ j k hjk (by grind) ≫ G.map (ξ.map (homOfLE hkl.le)).left.hom

namespace PositetskiInductionDataUpTo2

omit [IsCardinalAccessibleCategory K κ]
  [IsCardinalAccessibleCategory L κ]
  [F.IsCardinalAccessible κ]
  [G.IsCardinalAccessible κ]
  [F.PreservesCardinalPresentable κ]
  [SuccOrder Λ]
  [WellFoundedLT Λ]
  [NoMaxOrder Λ] in
lemma sq₂ {i : Λ} {E : Inserter F G} (d : PositetskiInductionDataUpTo2 κ Λ E i)
    (j k l m : Λ) (hjk : j < k) (hkm : k < m) (hjl : j < l) (hlm : l < m) (hm : m ≤ i) :
    F.map (d.ξ.map (homOfLE hjl.le)).left.hom ≫ d.ψ l m hlm (by grind) =
    d.ψ j k hjk (by grind) ≫ G.map (d.ξ.map (homOfLE hkm.le)).left.hom := by
  rw [← d.t₂, ← d.t₁] <;> grind

set_option backward.isDefEq.respectTransparency false in
/-- Restricts a PositetskiInductionDataUpTo to a lower index,
turning PositetskiInductionDataUpTo into a presheaf. -/
def trunc (E : Inserter F G)
    {i i' : Λ} (hii' : i ≤ i') (d : PositetskiInductionDataUpTo2 κ Λ E i') :
    PositetskiInductionDataUpTo2 κ Λ E i where
  ξ := SmallObject.restrictionLE d.ξ hii'
  ψ j k hjk hk := d.ψ j k hjk (hk.trans hii')
  sq₁ j hj := by
    have := d.sq₁ j (by grind) |>.symm
    obtain rfl | hii' := hii'.eq_or_lt
    · simp [this]
    dsimp
    rw [this]
    grind [→ d.t₂]
  t₁ j k l hjk hkl hl := d.t₁ j k l hjk hkl (hl.trans hii')
  t₂ j k l hjk hkl hl := d.t₂ j k l hjk hkl (hl.trans hii')

def functor (E : Inserter F G) : Λᵒᵖ ⥤ Type _ where
  obj i := PositetskiInductionDataUpTo2 κ Λ E i.unop
  map f := TypeCat.ofHom <| trunc κ Λ E (leOfHom f.unop)

open SmallObject.SuccStruct in
-- set_option backward.isDefEq.respectTransparency false in
attribute [local grind =] Subtype.mk_le_mk Order.lt_succ_iff in
noncomputable def extend {E : Inserter F G} {i : Λ} (b : PositetskiInductionDataUpTo2 κ Λ E i)
    (ξₙ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν : b.ξ.obj ⟨i, Set.mem_Iic.mpr le_rfl⟩ ⟶ ξₙ)
    (ψ : F.obj (b.ξ.obj ⟨i, Set.mem_Iic.mpr le_rfl⟩).left.obj ⟶ G.obj ξₙ.left.obj)
    (h₁ : F.map (b.ξ.obj ⟨i, Set.mem_Iic.mpr le_rfl⟩).hom ≫ E.hom = ψ ≫ G.map ξₙ.hom) :
    PositetskiInductionDataUpTo2 κ Λ E (Order.succ i) :=
  let ξ' := extendToSucc (not_isMax _) b.ξ ν
  -- TODO: figure out how to remove the helper
  have grind_helper {x y : CostructuredArrow (isCardinalPresentable K κ).ι E.obj} (f : x ⟶ y) :
      f.left.hom ≫ y.hom = x.hom := by simp
  let ψ' (j k : Λ) (hjk : j < k) (hk : k ≤ Order.succ i) :
    F.obj (ξ'.obj ⟨j, Set.mem_Iic.mpr (hjk.le.trans hk)⟩).left.obj ⟶
      G.obj (ξ'.obj ⟨k, by simpa⟩).left.obj :=
    if hk' : k ≤ i then
      F.map (extendToSuccObjIso (not_isMax _) b.ξ ν j (by grind)).hom.left.hom ≫
        b.ψ j k (by grind) hk' ≫
        G.map (extendToSuccObjIso (not_isMax _) b.ξ ν k hk').inv.left.hom
    else
      --letI hki : k = Order.succ i := le_antisymm (by simpa) (by simpa using hk')
      F.map (ξ'.map <| homOfLE (by grind [Order.le_succ_iff_eq_or_le])).left.hom ≫
        (F.map (extendToSuccObjIso (not_isMax _) b.ξ ν _ _).hom.left.hom ≫ ψ ≫
        G.map (extendToSuccObjSuccIso (not_isMax _) b.ξ ν).inv.left.hom) ≫
        G.map (ξ'.map <| homOfLE (by grind [Order.le_succ_iff_eq_or_le])).left.hom
  { ξ := ξ'
    ψ := ψ'
    sq₁ j hj := by
      dsimp [ψ', ξ']
      split_ifs with h
      · simp at h
      · simp
        by_cases hj : j < i
        · have := b.sq₁ j hj
          exact this
        · obtain rfl : j = i := by grind
          sorry

    t₁ j k l hjk hkl hl := by
      dsimp [ψ', ξ']
      split_ifs with h
      · have bt₁ := b.t₁ j k l (by grind) (by grind) (by grind)
        have := congr(F.map
          $(extendToSuccObjIso_hom_naturality (not_isMax _) b.ξ ν j k hjk.le (by grind)).left.hom)
        simp only [homOfLE_leOfHom, CostructuredArrow.comp_left,
          ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at this
        simp [bt₁, reassoc_of% this]
      · obtain rfl : l = Order.succ i := le_antisymm (by simpa) (by simpa using h)
        by_cases hh : k = i
        · subst hh
          simp
        have := (extendToSucc (not_isMax _) b.ξ ν).map_comp
          (X := ⟨j, by grind⟩) (Y := ⟨k, by grind⟩) (Z := ⟨i, by grind⟩)
          (homOfLE <| by grind) (homOfLE <| by grind)
        simp only [homOfLE_leOfHom, homOfLE_comp, CostructuredArrow.hom_eq_iff,
          CostructuredArrow.comp_left] at this
        simp [this]
    t₂ j k l hjk hkl hl := by
      dsimp [ψ', ξ']
      split_ifs with h'' h'
      · sorry -- should reduce to t₂ in d
      · obtain rfl : l = Order.succ i := le_antisymm (by simpa) (by grind)
        simp at h''
      · obtain rfl : l = Order.succ i := le_antisymm (by simpa) (by simpa using h'')
        sorry -- actual case
      · grind

    /- sq₂ j k hj hk := by
      dsimp [ψ', ξ']
      split_ifs with hj' hk' hh
      · have sq2 := b.sq₂ j k hj hk'
        have := congr(G.map
          $(extendToSuccObjIso_hom_naturality (not_isMax _) b.ξ ν
            (Order.succ j) (Order.succ k) (Order.succ_mono hj) (by grind)).left.hom)
        simp only [homOfLE_leOfHom, CostructuredArrow.comp_left,
          ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc] at this ⊢
        rw [this]
        simp_rw [← F.map_comp_assoc, reassoc_of% sq2, ← F.map_comp_assoc]
        have := congr(F.map $(ξ'ObjIso_nat j k hj hk).left.hom)
        simp at this
        simp [this]
      · sorry
      · grind
      · obtain rfl : k = Order.succ i := le_antisymm (by simpa) (by simpa using hh)
        obtain rfl : j = Order.succ i := le_antisymm (by simpa) (by simpa using hj')
        simp -/ }
end PositetskiInductionDataUpTo2

namespace PositetskiInductionDataUpTo

/-- Restricts a PositetskiInductionDataUpTo to a lower index,
turning PositetskiInductionDataUpTo into a presheaf. -/
def trunc (E : Inserter F G)
    {i i' : Λ} (hii' : i ≤ i') (d : PositetskiInductionDataUpTo κ Λ E i') :
    PositetskiInductionDataUpTo κ Λ E i where
  ξ := (Set.initialSegIicIicOfLE (by simpa)).monotone.functor ⋙ d.ξ
  ψ j hj := by exact d.ψ j (hj.trans hii')
  sq₁ j hj := d.sq₁ j (hj.trans hii')
  sq₂ j k hjk hki := d.sq₂ j k (by grind) (by grind)

def functor (E : Inserter F G) : Λᵒᵖ ⥤ Type _ where
  obj i := PositetskiInductionDataUpTo κ Λ E i.unop
  map f := TypeCat.ofHom <| trunc κ Λ E (leOfHom f.unop)

-- let’s just check the "pentagonal diagram" commutes
example (E : Inserter F G) (i j : Λ) (hi : j ≤ i) (d : PositetskiInductionDataUpTo κ Λ E i) :
    F.map (d.ξ.map (homOfLE (Order.le_succ j))).left.hom ≫
      F.map ((d.ξ.obj ⟨Order.succ j, by simpa⟩).hom) ≫ E.hom =
    d.ψ j hi ≫ G.map (d.ξ.obj ⟨Order.succ j, by simpa⟩).hom := by
  rw [d.sq₁ _, ← F.map_comp_assoc]
  generalize_proofs u v w
  have := (d.ξ.map (homOfLE w)).w
  dsimp at this
  simp [this]

section
-- helper congruence lemma to work through the DTT hell inherent to the definitions

end

variable {κ} {Λ} in
omit [IsCardinalAccessibleCategory L κ] [WellFoundedLT Λ] in
/-- The main technical induction step from Positetski's 4.5, where we pick an index large enough
to ensure a set of properties. This crucially uses that Λ is small enough. -/
theorem exists_succ_of_hasCardinalLT {E : Inserter F G} {i : Λ}
    (b : PositetskiInductionDataUpTo κ Λ E i) (hΛ : HasCardinalLT Λ κ) :
    ∃ (ξ₂ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
      (ν : b.ξ.obj ⟨Order.succ i, le_rfl⟩ ⟶ ξ₂)
      (ψ : F.obj (b.ξ.obj ⟨Order.succ i, le_rfl⟩).left.obj ⟶ G.obj ξ₂.left.obj),
      (F.map (b.ξ.obj ⟨Order.succ i, le_rfl⟩).hom ≫ E.hom = ψ ≫ G.map ξ₂.hom) ∧
      (∀ (j : Λ) (hj : j ≤ i),
        b.ψ j hj ≫ G.map (b.ξ.map <| homOfLE <| by exact Order.succ_mono hj).left.hom ≫
          G.map ν.left.hom =
        F.map (b.ξ.map <| homOfLE <| hj.trans (Order.le_succ i)).left.hom ≫ ψ) := by
  let ξ₀ := b.ξ.obj ⟨i, Order.le_succ i⟩
  let ξ₁ := b.ξ.obj ⟨Order.succ i, le_rfl⟩
  -- First, we summon a diagram to write E.obj as a κ-filtered colimits of κ-presentable objects.
  let O₀ := isCardinalPresentable K κ
  have : IsFiltered (CostructuredArrow O₀.ι E.obj) := isFiltered_of_isCardinalFiltered _ κ
  let hcolimT := O₀.ι.denseAt E.obj -- E.obj ≅ colim_ξ T_ξ
  have (X : K) : Limits.PreservesColimitsOfShape (CostructuredArrow O₀.ι X) G :=
    G.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _
  have (X : K) : Limits.PreservesColimitsOfShape (CostructuredArrow O₀.ι X) F :=
    F.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _
  let hcolimGT := Limits.isColimitOfPreserves G (O₀.ι.denseAt E.obj) -- G(E.obj) ≅ colim_ξ G(T_ξ)
  let hcolimFT := Limits.isColimitOfPreserves F (O₀.ι.denseAt E.obj) -- F(E.obj) ≅ colim_ξ F(T_ξ)
  -- having this in context makes grind better in this proof
  have grind_helper {x y : CostructuredArrow O₀.ι E.obj} (f : x ⟶ y) :
      f.left.hom ≫ y.hom = x.hom := by simp
  obtain ⟨ξ₂₁, v₀, v₁, hv₀⟩ := IsCardinalPresentable.exists_hom_above_of_isColimit κ hcolimGT
    (F.map ξ₁.hom ≫ E.hom) ξ₁
  -- At this point, the squares required to make that into a functor are not necessarily natural
  -- so we must coequalize all of them, and then take another max
  -- We can probably wrap this part in a lemma as well
  have Uspec (j : Set.Iic i) :
    ∃ (uji : CostructuredArrow O₀.ι E.obj) (vji : ξ₂₁ ⟶ uji),
      b.ψ j.1 j.property ≫
        G.map (b.ξ.map <| homOfLE <| by exact Order.succ_mono j.property).left.hom ≫
        G.map v₀.left.hom ≫ G.map vji.left.hom =
      F.map (b.ξ.map <| homOfLE <| j.2.trans <| Order.le_succ i).left.hom ≫ v₁ ≫
        G.map vji.left.hom := by
    obtain ⟨uij, vij, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolimGT
      (b.ψ j.1 j.property ≫
        G.map (b.ξ.map <| homOfLE <| by exact Order.succ_mono j.property).left.hom ≫
        G.map v₀.left.hom)
      (F.map (b.ξ.map <| homOfLE <| j.2.trans <| Order.le_succ i).left.hom ≫ v₁)
      (by
        dsimp at *
        simp only [Category.id_comp] at hv₀
        simp only [homOfLE_leOfHom, Category.id_comp, Category.assoc, hv₀]
        simp_rw [← Functor.map_comp, grind_helper]
        simp [ξ₁, b.sq₁ j j.prop, ← Functor.map_comp_assoc, grind_helper])
    exact ⟨uij, vij, by simpa using h⟩
  choose u ν huν using Uspec
  have h' : HasCardinalLT (Set.Iic i) κ := by
    grw [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_set_le, ← hasCardinalLT_iff_cardinal_mk_lt]
    assumption
  let ξ₂₀ := IsCardinalFiltered.max (κ := κ) u h'
  let ν₂₀ := IsCardinalFiltered.toMax (κ := κ) u h'
  let ξ₂ := IsCardinalFiltered.coeq (κ := κ) (fun j ↦ ν j ≫ ν₂₀ j) h'
  let μ : ξ₁ ⟶ ξ₂ := v₀ ≫ IsCardinalFiltered.toCoeq (κ := κ) (fun j ↦ ν j ≫ ν₂₀ j) h'
  let ψ : F.obj ξ₁.left.obj ⟶ G.obj ξ₂.left.obj :=
    v₁ ≫ G.map (IsCardinalFiltered.toCoeq (κ := κ) (fun j ↦ ν j ≫ ν₂₀ j) h').left.hom
  -- Now, we check that we have obtained all the conditions we want:
  have cond_sq1 :
       F.map ξ₁.hom ≫ E.hom = ψ ≫ G.map ξ₂.hom := by
    dsimp [μ, ξ₁, ψ] at *
    grind
  refine ⟨ξ₂, μ, ψ, cond_sq1, fun j hj ↦ ?_⟩
  · have S1 := huν ⟨j, hj⟩
    have cond2 := IsCardinalFiltered.coeq_condition (κ := κ) (fun j ↦ ν j ≫ ν₂₀ j) h' ⟨j, hj⟩
    dsimp [μ, ξ₁, ψ] at *
    simp only [homOfLE_leOfHom, ← Functor.map_comp, ← cond2]
    simp [reassoc_of% S1]

section

open SmallObject.SuccStruct in
noncomputable def extend {E : Inserter F G} {i : Λ} (b : PositetskiInductionDataUpTo κ Λ E i)
    (ξₙ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν : b.ξ.obj ⟨Order.succ i, Set.mem_Iic.mpr le_rfl⟩ ⟶ ξₙ)
    (ψ : F.obj (b.ξ.obj ⟨Order.succ i, Set.mem_Iic.mpr le_rfl⟩).left.obj ⟶ G.obj ξₙ.left.obj)
    (h₁ : F.map (b.ξ.obj ⟨Order.succ i, Set.mem_Iic.mpr le_rfl⟩).hom ≫ E.hom = ψ ≫ G.map ξₙ.hom) :
    PositetskiInductionDataUpTo κ Λ E (Order.succ i) :=
  let ξ' := extendToSucc (not_isMax _) b.ξ ν
  have grind_helper {x y : CostructuredArrow (isCardinalPresentable K κ).ι E.obj} (f : x ⟶ y) :
      f.left.hom ≫ y.hom = x.hom := by simpa using f.w
  let ψ' (j : Λ) (hj : j ≤ Order.succ i) :
    F.obj (ξ'.obj ⟨j, hj.trans (Order.le_succ _)⟩).left.obj ⟶
      G.obj (ξ'.obj ⟨Order.succ j, by simpa⟩).left.obj :=
    if hj' : j ≤ i then
      F.map (extendToSuccObjIso (not_isMax _) b.ξ ν j (by grind)).hom.left.hom ≫
        b.ψ j (by grind) ≫
        G.map (extendToSuccObjIso (not_isMax _) b.ξ ν (Order.succ j)
          (Order.succ_mono hj')).inv.left.hom
    else
      eqToHom (by
          obtain rfl : j = Order.succ i := le_antisymm (by simpa) (by simpa using hj')
          rfl) ≫
        (F.map (extendToSuccObjIso (not_isMax _) b.ξ ν _ le_rfl).hom.left.hom ≫ ψ ≫
        G.map (extendToSuccObjSuccIso (not_isMax _) b.ξ ν).inv.left.hom) ≫
        eqToHom (by
          obtain rfl : j = Order.succ i := le_antisymm (by simpa) (by simpa using hj')
          rfl)
  { ξ := ξ'
    ψ := ψ'
    sq₁ j hj := by
      dsimp [ψ', ξ']
      split_ifs with h
      · simp [Category.assoc, ← G.map_comp, b.sq₁, ← F.map_comp_assoc, grind_helper]
      · obtain rfl : j = Order.succ i := le_antisymm (by simpa) (by simpa using h)
        simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc]
        simp_rw [← G.map_comp, grind_helper, ← h₁, ← F.map_comp_assoc, grind_helper]
    sq₂ j k hj hk := by
      dsimp [ψ', ξ']
      split_ifs with hj' hk' hh
      · have sq2 := b.sq₂ j k hj hk'
        have := congr(G.map
          $(extendToSuccObjIso_hom_naturality (not_isMax _) b.ξ ν
            (Order.succ j) (Order.succ k) (Order.succ_mono hj) (by grind)).left.hom)
        simp only [homOfLE_leOfHom, CostructuredArrow.comp_left,
          ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc] at this ⊢
        rw [this]
        simp_rw [← F.map_comp_assoc, reassoc_of% sq2, ← F.map_comp_assoc]
        have := congr(F.map $(ξ'ObjIso_nat j k hj hk).left.hom)
        simp at this
        simp [this]
      · sorry
      · grind
      · obtain rfl : k = Order.succ i := le_antisymm (by simpa) (by simpa using hh)
        obtain rfl : j = Order.succ i := le_antisymm (by simpa) (by simpa using hj')
        simp }

end
attribute [local grind .] Order.le_succ
set_option backward.isDefEq.respectTransparency false in
theorem surjective_trunc (hΛ : HasCardinalLT Λ κ) (E : Inserter F G) (i : Λ) :
    Function.Surjective (PositetskiInductionDataUpTo.trunc κ Λ E (Order.le_succ i)) := by
  intro b
  -- The hard work is done in exists_succ_of_hasCardinalLT, but we have to spend some time
  -- to repackage the output here
  obtain ⟨ξ₂, ν, ψ, h₁, h₂⟩ := exists_succ_of_hasCardinalLT b hΛ
  have grind_helper {x y : CostructuredArrow (isCardinalPresentable K κ).ι E.obj} (f : x ⟶ y) :
      f.left.hom ≫ y.hom = x.hom := by simpa using f.w
  -- Use the SmallObject.SuccStruct.extendToSucc API to extend the functor
  let ξ' := SmallObject.SuccStruct.extendToSucc (not_isMax _) b.ξ ν
  let ξ'ObjIso (j : Λ) (hj : j ≤ Order.succ i) :
      ξ'.obj ⟨j, by grind [Order.le_succ]⟩ ≅ b.ξ.obj ⟨j, by grind⟩ :=
    SmallObject.SuccStruct.extendToSuccObjIso ..
  let ξ'Succ :
      ξ'.obj ⟨Order.succ (Order.succ i), by grind [Order.le_succ]⟩ ≅ ξ₂ :=
    SmallObject.SuccStruct.extendToSuccObjSuccIso ..
  have ξ'ObjIso_nat (i₁ i₂ : Λ) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ Order.succ i) :
    ξ'.map (homOfLE hi) ≫ (ξ'ObjIso i₂ hi₂).hom =
      (ξ'ObjIso i₁ (by grind)).hom ≫ b.ξ.map (homOfLE hi) :=
    SmallObject.SuccStruct.extendToSuccObjIso_hom_naturality (not_isMax _) b.ξ ν ..
  have ξ'ObjIso_inv_nat (i₁ i₂ : Λ) (hi : i₁ ≤ i₂) (hi₂ : i₂ ≤ Order.succ i) :
    (ξ'ObjIso i₁ (by grind)).inv ≫ ξ'.map (homOfLE hi) =
      b.ξ.map (homOfLE hi) ≫ (ξ'ObjIso i₂ hi₂).inv := by
    sorry
  let ψ' (j : Λ) (hj : j ≤ Order.succ i) :
    F.obj (ξ'.obj ⟨j, hj.trans (Order.le_succ _)⟩).left.obj ⟶
      G.obj (ξ'.obj ⟨Order.succ j, by simpa⟩).left.obj :=
    if hj' : j ≤ i then
      F.map (ξ'ObjIso j (by grind)).hom.left.hom ≫ b.ψ j (by grind) ≫
        G.map (ξ'ObjIso _ (by grind)).inv.left.hom
    else
      eqToHom (by
        obtain rfl : j = Order.succ i := le_antisymm (by simpa) (by simpa using hj')
        rfl) ≫ (F.map (ξ'ObjIso _ le_rfl).hom.left.hom ≫ ψ ≫ G.map ξ'Succ.inv.left.hom) ≫
      eqToHom (by
        obtain rfl : j = Order.succ i := le_antisymm (by simpa) (by simpa using hj')
        rfl)
  -- now we just have to dive in DTT hell
  refine ⟨{ ξ := ξ', ψ := ψ', sq₁ := fun j hj ↦ ?_, sq₂ := fun j k hj hk ↦ ?_ }, ?_⟩
  · dsimp [ψ']
    split_ifs with h
    · simp_rw [Category.assoc, ← G.map_comp, grind_helper, b.sq₁, ← F.map_comp_assoc, grind_helper]
    · obtain rfl : j = Order.succ i := le_antisymm (by simpa) (by simpa using h)
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp, Category.assoc]
      simp_rw [← G.map_comp, grind_helper, ← h₁, ← F.map_comp_assoc, grind_helper]
  · dsimp [ψ']
    split_ifs with hj' hk' hh
    · have sq2 := b.sq₂ j k hj hk'
      have := congr(G.map
        $(ξ'ObjIso_inv_nat (Order.succ j) (Order.succ k) (Order.succ_mono hj) (by grind)).left.hom)
      simp only [homOfLE_leOfHom, CostructuredArrow.comp_left,
        ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc] at this ⊢
      rw [this]
      simp_rw [← F.map_comp_assoc, reassoc_of% sq2, ← F.map_comp_assoc]
      have := congr(F.map $(ξ'ObjIso_nat j k hj hk).left.hom)
      simp at this
      simp [this]
    · obtain rfl : k = Order.succ i := le_antisymm (by simpa) (by simpa using hk')
      have sq2 := b.sq₂ j i hj' le_rfl
      have := h₂ j hj'
      simp [ξ', ξ'ObjIso, ξ'Succ]
      -- missing lemma
      sorry
    · grind
    · obtain rfl : k = Order.succ i := le_antisymm (by simpa) (by simpa using hh)
      obtain rfl : j = Order.succ i := le_antisymm (by simpa) (by simpa using hj')
      simp
  · ext
    · apply Functor.ext_of_iso (SmallObject.SuccStruct.extendToSuccRestrictionLEIso ..)
      · rintro ⟨x, hx⟩
        simp only [Set.mem_Iic] at hx
        by_cases hx : x ≤ i
        · simp only [SmallObject.restrictionLE_obj]
          rw [SmallObject.SuccStruct.extendToSucc_obj_eq]
        · obtain rfl : x = Order.succ i := le_antisymm (by simpa) (by simpa using hx)
          simp [SmallObject.SuccStruct.extendToSucc_obj_eq]
    · apply Function.hfunext rfl
      intro a a' h
      rw [heq_iff_eq] at h
      subst h
      simp only [trunc, Functor.comp_obj, Monotone.functor_obj, Category.assoc, ψ']
      apply Function.hfunext rfl
      intro ha' u rfl
      simp only [SmallObject.SuccStruct.extendToSuccObjIso,
        SmallObject.SuccStruct.extendToSucc.objIso, eqToIso.hom, CostructuredArrow.eqToHom_left,
        ObjectProperty.eqToHom_hom, eqToHom_map, eqToIso.inv, eqToHom_trans_assoc, ξ'ObjIso]
      split_ifs
      simp


-- now this is where we cry

end PositetskiInductionDataUpTo

lemma positetski_4_5_attempt1 (E : Inserter F G) (S T : K)
    [IsCardinalPresentable S κ] [IsCardinalPresentable T κ]
    (σ : F.obj S ⟶ G.obj T)
    (u : S ⟶ T) (v : T ⟶ E.obj)
    (h : σ ≫ G.map v = F.map u ≫ F.map v ≫ E.hom) :
    ∃ (B : Inserter F G) (_ : IsCardinalPresentable B.obj κ) (f : B ⟶ E) (g : T ⟶ B.obj),
      σ ≫ G.map g = F.map u ≫ F.map g ≫ B.hom ∧
      g ≫ f.hom = v := by
  -- First, we summon a diagram to write T as a κ-filtered colimits of κ-filtered objects.
  let O₀ := isCardinalPresentable K κ
  have : IsFiltered (CostructuredArrow O₀.ι E.obj) := isFiltered_of_isCardinalFiltered _ κ
  let hcolimT := O₀.ι.denseAt E.obj -- E.obj ≅ colim_ξ T_ξ
  have (X : K) : Limits.PreservesColimitsOfShape (CostructuredArrow O₀.ι X) G :=
    G.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _
  have (X : K) : Limits.PreservesColimitsOfShape (CostructuredArrow O₀.ι X) F :=
    F.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _
  let hcolimGT := Limits.isColimitOfPreserves G (O₀.ι.denseAt E.obj) -- G(E.obj) ≅ colim_ξ G(T_ξ)
  let hcolimFT := Limits.isColimitOfPreserves F (O₀.ι.denseAt E.obj) -- F(E.obj) ≅ colim_ξ F(T_ξ)
  -- Now we get a first factorization for σ
  obtain ⟨ξ₀, v₀, hv₀⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimT v
  dsimp at v₀ hv₀
  simp only [Category.id_comp] at hv₀
  -- local grind helper :
  have help {x y : CostructuredArrow O₀.ι E.obj} (f : x ⟶ y) : f.left.hom ≫ y.hom = x.hom := by
    simpa using f.w
  -- "Then, the heptagonal diagram commutes"
  have hepta : F.map u ≫ F.map v₀ ≫ F.map ξ₀.hom ≫ E.hom = σ ≫ G.map v₀ ≫ G.map ξ₀.hom := by
    grind
  obtain ⟨ξ₁₀, ψ₀₀, hψ₀₀⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimGT
    (F.map ξ₀.hom ≫ E.hom)
  dsimp at ψ₀₀ hψ₀₀
  -- let’s continue : we want to have...
  obtain ⟨ξ₁, ψ₀₁, hψ₀₁⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolimGT
    (F.map u ≫ F.map v₀ ≫ ψ₀₀ ≫ G.map (IsFiltered.rightToMax ξ₀ ξ₁₀).left.hom)
    (σ ≫ G.map v₀ ≫ G.map (IsFiltered.leftToMax ξ₀ ξ₁₀).left.hom)
    (by
      dsimp
      grind)
  dsimp at ψ₀₀ hψ₀₁
  let u₀ : ξ₀ ⟶ ξ₁ := IsFiltered.leftToMax _ _ ≫ ψ₀₁
  let ψ₀ : F.obj ξ₀.left.obj ⟶ G.obj ξ₁.left.obj :=
    ψ₀₀ ≫ G.map (IsFiltered.rightToMax ξ₀ ξ₁₀).left.hom ≫ G.map ψ₀₁.left.hom
  -- "Then, the heptagonal diagram commutes"
  have : σ ≫ G.map v₀ ≫ G.map u₀.left.hom = F.map u ≫ F.map v₀ ≫ ψ₀ := by
    dsimp [u₀, ψ₀]
    grind
  -- "Notice that the pentagonal diagram commutes"
  have : ψ₀ ≫ G.map ξ₁.hom = F.map u₀.left.hom ≫ F.map ξ₁.hom ≫ E.hom := by
    dsimp [u₀, ψ₀]
    grind
  sorry

end


/-- Let `Λ < κ` be a pair of infinite cardinals, such that `κ` is regular. Assume that
- `K` and `L` are `κ`-accessible categories with colimits of `Λ`-chains.
- `F G : C ⥤ D` are `κ`-accessible functors preserving colimits of `Λ`-chains and with `F`
  preserving `κ`-presentable objects.
Then the category `Inserter F G` is κ-accessible.

Note that if `K` and `L` are `κ`-accessible, and `F`, `G` are `κ`-accessible with `F` preserving
`κ`-presentable objects, then as `κ` is sharply less than `κ⁺`, one can show that the pair `κ < κ⁺`
satisfies the conditions above, and hence `Inserter F G` is `κ⁺` accessible in this situation. -/
public theorem isCardinalAccessibleCategory
    {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalAccessibleCategory K κ] [IsCardinalAccessibleCategory L κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ]
    (Λ : Type w) [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ)
    [Limits.HasColimitsOfShape Λ K] [Limits.HasColimitsOfShape Λ L]
    [Limits.PreservesColimitsOfShape Λ F] [Limits.PreservesColimitsOfShape Λ G] :
    IsCardinalAccessibleCategory (Inserter F G) κ :=
  sorry

end CategoryTheory.Inserter
