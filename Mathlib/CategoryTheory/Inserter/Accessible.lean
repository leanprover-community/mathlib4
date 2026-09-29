/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Inserter.Limits
public import Mathlib.CategoryTheory.Inserter.LocallySmall
public import Mathlib.CategoryTheory.Presentable.Comma
import Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc
import Mathlib.CategoryTheory.SmallObject.Iteration.FunctorOfCocone
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
structure PositetskiInductionDataUpTo
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
  t₁ (j k l : Λ) (hjk : j ≤ k) (hkl : k < l) (hl : l ≤ i) :
    ψ j l (by grind) hl =
      F.map (ξ.map (homOfLE hjk)).left.hom ≫ ψ k l hkl (by grind)
  t₂ (j k l : Λ) (hjk : j < k) (hkl : k ≤ l) (hl : l ≤ i) :
    ψ j l (by grind) hl =
      ψ j k hjk (by grind) ≫ G.map (ξ.map (homOfLE hkl)).left.hom

namespace PositetskiInductionDataUpTo

/-- Macro for a quick discharger tactic that we will repeatedly use. This is an
optimized grind call for our use case (quick combinations of inequalities). -/
local macro "valid" : tactic =>
  `(tactic| grind (ematch := 2) (gen := 2) +order -ring +lia -inj -ac only
    [Subtype.mk_le_mk, Order.le_succ_iff_eq_or_le, Order.lt_succ_iff, Set.mem_Iic, Set.mem_Iio,
      Order.IsSuccLimit.succ_lt])

/-! In the following, we are going to move very frequently between Λ, Set.Iio _ and Set.Iic _.
Most of the time, this requires term annotations and rather boring grind-able proof obligations.
We also run into the fact that h : i ≤ j and i ∈ Set.Iic j are not defeq at implicit_reduible
transparency, which makes everything rather painful.

So we provide a small discharge tactic that is just a specialized `grind` call, and
elabs iio% i j for `⟨i, …⟩ : Set.Iio j`, and iic% i j for `⟨i, _⟩ : Set.Iic j`. -/


theorem eqToHom_ext {E : Inserter F G} {i : Λ} {b b' : PositetskiInductionDataUpTo κ Λ E i}
    (h_obj : ∀ (j : Set.Iic i), b.ξ.obj j = b'.ξ.obj j)
    (h_map : ∀ (j k : Λ) (hjk : j ≤ k) (hki : k ≤ i),
      b.ξ.map (homOfLE hjk : ⟨j, Set.mem_Iic.mpr (hjk.trans hki)⟩ ⟶ ⟨k, Set.mem_Iic.mpr hki⟩) =
      eqToHom (h_obj _) ≫ b'.ξ.map (homOfLE hjk) ≫ eqToHom (h_obj _).symm)
    (h_ψ : ∀ (j k : Λ) (hjk : j < k) (hki : k ≤ i),
      b.ψ j k hjk hki = F.map (eqToHom (congr($(h_obj _).left.obj))) ≫ b'.ψ j k hjk hki ≫
        G.map (eqToHom (congr($(h_obj _).left.obj)).symm)):
    b = b' := by
  ext
  · fapply Functor.ext
    · intro i
      exact h_obj i
    · intro j k f
      exact h_map j.1 k.1 (leOfHom f) k.property
  · refine Function.hfunext rfl fun a a' haa' ↦
      Function.hfunext rfl fun b b' hbb' ↦  ?_
    rw [heq_iff_eq] at haa' hbb'
    subst haa' hbb'
    refine Function.hfunext rfl fun _ _ _ ↦ Function.hfunext rfl fun _ _ _ ↦ ?_
    simp [h_ψ, eqToHom_map]

theorem congr_ψ {E : Inserter F G} {i : Λ} {b b' : PositetskiInductionDataUpTo κ Λ E i}
    (h : b = b') (j k : Λ) (hjk : j < k) (hki : k ≤ i) :
    b.ψ j k hjk hki = F.map (eqToHom congr((($h).ξ.obj _).left.obj)) ≫ b'.ψ j k hjk hki ≫
      G.map (eqToHom congr((($h).ξ.obj _).left.obj).symm) := by
  subst h
  simp

variable {κ} {Λ} in
omit [IsCardinalAccessibleCategory L κ] [WellFoundedLT Λ] [SuccOrder Λ]
  [NoMaxOrder Λ] in
/-- The main technical induction step from Positetski's 4.5, where we pick an index large enough
to ensure a set of properties. This crucially uses that Λ is small enough. -/
theorem exists_succ_of_hasCardinalLT {E : Inserter F G} {i : Λ}
    (b : PositetskiInductionDataUpTo κ Λ E i) (hΛ : HasCardinalLT Λ κ) :
    ∃ (ξ₂ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
      (ν : b.ξ.obj ⟨i, le_rfl⟩ ⟶ ξ₂)
      (ψ : F.obj (b.ξ.obj ⟨i, le_rfl⟩).left.obj ⟶ G.obj ξ₂.left.obj),
      (F.map (b.ξ.obj ⟨i, le_rfl⟩).hom ≫ E.hom = ψ ≫ G.map ξ₂.hom) ∧
      (∀ (j : Λ) (hj : j < i),
        b.ψ j i hj le_rfl ≫ G.map ν.left.hom =
        F.map (b.ξ.map <| homOfLE <| hj.le).left.hom ≫ ψ) := by
  let ξ₁ := b.ξ.obj ⟨i, le_rfl⟩
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
  have Uspec (j : Set.Iio i) :
    ∃ (uji : CostructuredArrow O₀.ι E.obj) (vji : ξ₂₁ ⟶ uji),
      b.ψ j.1 i j.property le_rfl ≫ G.map v₀.left.hom ≫ G.map vji.left.hom =
      F.map (b.ξ.map <| homOfLE <| j.property.le).left.hom ≫ v₁ ≫
        G.map vji.left.hom := by
    obtain ⟨uij, vij, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolimGT
      (b.ψ j.1 i j.property le_rfl ≫ G.map v₀.left.hom)
      (F.map (b.ξ.map <| homOfLE <| j.property.le).left.hom ≫ v₁)
      (by
        dsimp at *
        simp only [Category.id_comp] at hv₀
        simp only [homOfLE_leOfHom, Category.id_comp, Category.assoc, hv₀]
        simp_rw [← Functor.map_comp, grind_helper]
        simp [ξ₁, b.sq₁ j j.prop, ← Functor.map_comp_assoc, grind_helper])
    exact ⟨uij, vij, by simpa using h⟩
  choose u ν huν using Uspec
  have h' : HasCardinalLT (Set.Iio i) κ := by
    grw [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_set_le, ← hasCardinalLT_iff_cardinal_mk_lt]
    assumption
  let ξ₂₀ := IsCardinalFiltered.max (κ := κ) u h'
  let ν₂₀ := IsCardinalFiltered.toMax (κ := κ) u h'
  let ξ₂ := IsCardinalFiltered.coeq (κ := κ) (fun j ↦ ν j ≫ ν₂₀ j) h'
  let μ : ξ₁ ⟶ ξ₂ := v₀ ≫ IsCardinalFiltered.toCoeq (κ := κ) (fun j ↦ ν j ≫ ν₂₀ j) h'
  let ψ : F.obj ξ₁.left.obj ⟶ G.obj ξ₂.left.obj :=
    v₁ ≫ G.map (IsCardinalFiltered.toCoeq (κ := κ) (fun j ↦ ν j ≫ ν₂₀ j) h').left.hom
  -- Now, we check that we have obtained all the conditions we want:
  have cond_sq1 : F.map ξ₁.hom ≫ E.hom = ψ ≫ G.map ξ₂.hom := by
    dsimp [μ, ξ₁, ψ] at *
    grind
  refine ⟨ξ₂, μ, ψ, cond_sq1, fun j hj ↦ ?_⟩
  · have S1 := huν ⟨j, hj⟩
    have cond2 := IsCardinalFiltered.coeq_condition (κ := κ) (fun j ↦ ν j ≫ ν₂₀ j) h' ⟨j, hj⟩
    dsimp [μ, ξ₁, ψ] at *
    simp only [homOfLE_leOfHom, ← cond2]
    simp [reassoc_of% S1]

omit [IsCardinalAccessibleCategory K κ]
  [IsCardinalAccessibleCategory L κ]
  [F.IsCardinalAccessible κ]
  [G.IsCardinalAccessible κ]
  [F.PreservesCardinalPresentable κ]
  [SuccOrder Λ]
  [WellFoundedLT Λ]
  [NoMaxOrder Λ] in
lemma sq₂ {i : Λ} {E : Inserter F G} (d : PositetskiInductionDataUpTo κ Λ E i)
    (j k l m : Λ) (hjk : j < k) (hkm : k ≤ m) (hjl : j ≤ l) (hlm : l < m) (hm : m ≤ i) :
    F.map (d.ξ.map (homOfLE hjl)).left.hom ≫ d.ψ l m hlm (by valid) =
    d.ψ j k hjk (by valid) ≫ G.map (d.ξ.map (homOfLE hkm)).left.hom := by
  rw [← d.t₂, ← d.t₁]
  all_goals grind

set_option backward.isDefEq.respectTransparency false in
/-- Restricts a PositetskiInductionDataUpTo to a lower index,
turning PositetskiInductionDataUpTo into a presheaf. -/
@[implicit_reducible]
def trunc (E : Inserter F G)
    {i i' : Λ} (hii' : i ≤ i') (d : PositetskiInductionDataUpTo κ Λ E i') :
    PositetskiInductionDataUpTo κ Λ E i where
  ξ := SmallObject.restrictionLE d.ξ hii'
  ψ j k hjk hk := d.ψ j k hjk (hk.trans hii')
  sq₁ j hj := by
    have := d.sq₁ j (by valid) |>.symm
    obtain rfl | hii' := hii'.eq_or_lt
    · exact this.symm
    dsimp
    rw [this]
    grind [→ d.t₂]
  t₁ j k l hjk hkl hl := d.t₁ j k l hjk hkl (hl.trans hii')
  t₂ j k l hjk hkl hl := d.t₂ j k l hjk hkl (hl.trans hii')

abbrev functor (E : Inserter F G) : Λᵒᵖ ⥤ Type _ where
  obj i := PositetskiInductionDataUpTo κ Λ E i.unop
  map f := TypeCat.ofHom <| trunc κ Λ E (leOfHom f.unop)

open SmallObject.SuccStruct in
-- set_option backward.isDefEq.respectTransparency false in
attribute [local grind =] Subtype.mk_le_mk Order.lt_succ_iff homOfLE_comp in
attribute [local grind =] CostructuredArrow.comp_left ObjectProperty.FullSubcategory.comp_hom in
@[implicit_reducible]
-- TODO: move the aux decl and proofs in their own small namespace?
noncomputable def extend {E : Inserter F G} {i : Λ} (b : PositetskiInductionDataUpTo κ Λ E i)
    (ξₙ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν : b.ξ.obj ⟨i, Set.mem_Iic.mpr le_rfl⟩ ⟶ ξₙ)
    (ψ : F.obj (b.ξ.obj ⟨i, Set.mem_Iic.mpr le_rfl⟩).left.obj ⟶ G.obj ξₙ.left.obj)
    (h₁ : F.map (b.ξ.obj ⟨i, Set.mem_Iic.mpr le_rfl⟩).hom ≫ E.hom = ψ ≫ G.map ξₙ.hom)
    (h₂ : ∀ (j : Λ) (hj : j < i), F.map (b.ξ.map <| homOfLE hj.le).left.hom ≫ ψ =
      b.ψ j i hj le_rfl ≫ G.map ν.left.hom) :
    PositetskiInductionDataUpTo κ Λ E (Order.succ i) :=
  let ξ' := extendToSucc (not_isMax _) b.ξ ν
  -- TODO: figure out how to remove the helper
  have grind_helper {x y : CostructuredArrow (isCardinalPresentable K κ).ι E.obj} (f : x ⟶ y) :
      f.left.hom ≫ y.hom = x.hom := by simp
  let ψ' (j k : Λ) (hjk : j < k) (hk : k ≤ Order.succ i) :
    F.obj (ξ'.obj ⟨j, Set.mem_Iic.mpr <| hjk.le.trans hk⟩).left.obj ⟶
      G.obj (ξ'.obj ⟨k, by simpa⟩).left.obj :=
    if hk' : k ≤ i then
      F.map (extendToSuccObjIso (not_isMax _) b.ξ ν j (by valid)).hom.left.hom ≫
        b.ψ j k (by valid) hk' ≫
        G.map (extendToSuccObjIso (not_isMax _) b.ξ ν k hk').inv.left.hom
    else
      --letI hki : k = Order.succ i := le_antisymm (by simpa) (by simpa using hk')
      F.map (ξ'.map <| homOfLE (by valid)).left.hom ≫
        (F.map (extendToSuccObjIso (not_isMax _) b.ξ ν _ _).hom.left.hom ≫ ψ ≫
        G.map (extendToSuccObjSuccIso (not_isMax _) b.ξ ν).inv.left.hom) ≫
        G.map (ξ'.map <| homOfLE (by valid)).left.hom
  { ξ := ξ'
    ψ := ψ'
    sq₁ j hj := by
      dsimp [ψ', ξ']
      split_ifs with h
      · simp at h
      · simp only [homOfLE_leOfHom, Functor.map_id, CostructuredArrow.id_left,
          ObjectProperty.FullSubcategory.id_hom, Category.comp_id, Category.assoc]
        simp_rw [← G.map_comp, grind_helper, ← h₁, ← F.map_comp_assoc]
        simp
    t₁ j k l hjk hkl hl := by
      dsimp [ψ', ξ']
      split_ifs with h
      · have bt₁ := b.t₁ j k l (by valid) (by valid) (by valid)
        have := congr(F.map
          $(extendToSuccObjIso_hom_naturality (not_isMax _) b.ξ ν j k hjk (by valid)).left.hom)
        simp only [homOfLE_leOfHom, CostructuredArrow.comp_left,
          ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at this
        simp [bt₁, reassoc_of% this]
      · obtain rfl : l = Order.succ i := le_antisymm (by simpa) (by simpa using h)
        by_cases hh : k = i
        · subst hh
          simp
        have := (extendToSucc (not_isMax _) b.ξ ν).map_comp
          (X := ⟨j, by valid⟩) (Y := ⟨k, by valid⟩) (Z := ⟨i, by valid⟩)
          (homOfLE <| by valid) (homOfLE <| by valid)
        grind
    t₂ j k l hjk hkl hl := by
      dsimp [ψ', ξ']
      split_ifs with h'' h'
      · have := b.t₂ j k l (by valid) (by valid) (by valid) -- should reduce to t₂ in d
        simp only [this, homOfLE_leOfHom, Category.assoc, ← G.map_comp]
        congr 3
        have := congr($(extendToSuccObjIso_inv_naturality (not_isMax _)
          b.ξ ν k l (by valid) h'').left.hom)
        simp only [homOfLE_leOfHom, CostructuredArrow.comp_left,
          ObjectProperty.FullSubcategory.comp_hom] at this
        simp [this]
      · obtain rfl : l = Order.succ i := le_antisymm (by simpa) (by valid)
        simp at h''
      · obtain rfl : l = Order.succ i := le_antisymm (by simpa) (by simpa using h'')
        by_cases hh : k = i
        · subst hh
          simp only [homOfLE_leOfHom, homOfLE_refl, Functor.map_id, CostructuredArrow.id_left,
            ObjectProperty.FullSubcategory.id_hom, Category.comp_id, Category.assoc]
          simp_rw [← F.map_comp_assoc,
            ← ObjectProperty.FullSubcategory.comp_hom, ← CostructuredArrow.comp_left]
          simp_rw [← G.map_comp,
            ← ObjectProperty.FullSubcategory.comp_hom, ← CostructuredArrow.comp_left]
          rw [extendToSuccObjIso_hom_naturality (not_isMax _) b.ξ ν j k (by valid) le_rfl,
            extendToSucc_map_le_succ]
          simp [reassoc_of% h₂ j (by valid)]
        have := (extendToSucc (not_isMax _) b.ξ ν).map_comp
          (X := ⟨k, by valid⟩) (Y := ⟨i, by valid⟩) (Z := ⟨Order.succ i, by valid⟩)
          (homOfLE <| by valid) (homOfLE <| by valid)
        have sq2 := b.t₂ j k i (by valid) (by valid) (by valid)
        simp only [homOfLE_leOfHom, homOfLE_comp, CostructuredArrow.hom_eq_iff,
          CostructuredArrow.comp_left] at this
        simp_rw [Category.assoc, ← G.map_comp,
          ← ObjectProperty.FullSubcategory.comp_hom, this, ← CostructuredArrow.comp_left]
        rw [reassoc_of% extendToSuccObjIso_inv_naturality (not_isMax _) b.ξ ν k i (by valid) le_rfl]
        simp only [homOfLE_leOfHom, homOfLE_refl, Functor.map_id, Category.comp_id,
          extendToSucc_map_le_succ, Iso.inv_hom_id_assoc, CostructuredArrow.comp_left,
          ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, ← reassoc_of% sq2]
        simp_rw [← F.map_comp_assoc,
          ← ObjectProperty.FullSubcategory.comp_hom, ← CostructuredArrow.comp_left]
        rw [extendToSuccObjIso_hom_naturality (not_isMax _) b.ξ ν j i (by valid) le_rfl]
        simp [reassoc_of% h₂ j (by valid)]
      · obtain rfl : l = Order.succ i := le_antisymm (by simpa) (by simpa using h'')
        simp
        sorry}

attribute [local grind =] Subtype.mk_le_mk Order.lt_succ_iff homOfLE_comp in
attribute [local grind =] CostructuredArrow.comp_left ObjectProperty.FullSubcategory.comp_hom in
-- TODO: make this better
theorem trunc_extend
    {E : Inserter F G} {i : Λ} (b : PositetskiInductionDataUpTo κ Λ E i)
    (ξₙ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν : b.ξ.obj ⟨i, Set.mem_Iic.mpr le_rfl⟩ ⟶ ξₙ)
    (ψ : F.obj (b.ξ.obj ⟨i, Set.mem_Iic.mpr le_rfl⟩).left.obj ⟶ G.obj ξₙ.left.obj)
    (h₁ : F.map (b.ξ.obj ⟨i, Set.mem_Iic.mpr le_rfl⟩).hom ≫ E.hom = ψ ≫ G.map ξₙ.hom)
    (h₂ : ∀ (j : Λ) (hj : j < i), F.map (b.ξ.map <| homOfLE hj.le).left.hom ≫ ψ =
      b.ψ j i hj le_rfl ≫ G.map ν.left.hom) :
    (b.extend κ Λ ξₙ ν ψ h₁ h₂).trunc κ Λ E (Order.le_succ i) = b := by
  fapply eqToHom_ext
  · intro j
    simp [trunc, extend, SmallObject.SuccStruct.extendToSucc, SmallObject.restrictionLE,
      SmallObject.SuccStruct.extendToSucc.obj]
    grind
  · intro j k hjk hki
    simp [trunc, extend, SmallObject.SuccStruct.extendToSucc, SmallObject.restrictionLE,
      SmallObject.SuccStruct.extendToSucc.obj, SmallObject.SuccStruct.extendToSucc.map]
    sorry
  · sorry

attribute [local grind .] Order.le_succ
set_option backward.isDefEq.respectTransparency false in
theorem surjective_trunc (hΛ : HasCardinalLT Λ κ) (E : Inserter F G) (i : Λ) :
    Function.Surjective (PositetskiInductionDataUpTo.trunc κ Λ E (Order.le_succ i)) := by
  intro b
  -- The hard work is done in exists_succ_of_hasCardinalLT, but we have to spend some time
  -- to repackage the output here
  obtain ⟨ξ₂, ν, ψ, h₁, h₂⟩ := exists_succ_of_hasCardinalLT b hΛ
  use b.extend _ _ ξ₂ ν ψ h₁ (fun _ _ ↦ (h₂ ..).symm)
  exact trunc_extend ..

-- Now, we must extend a cocone

section limit

@[implicit_reducible]
def ISeg (E : Inserter F G) (j : Λ) : Type _ :=
  ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
      PositetskiInductionDataUpTo.functor κ Λ E).sections

namespace ISeg

variable {κ Λ} {E : Inserter F G} {j : Λ}

abbrev ξ' (S : ISeg κ Λ E j) (t : Set.Iio j) :
   CostructuredArrow (isCardinalPresentable K κ).ι E.obj :=
  (S.val (Opposite.op t)).ξ.obj ⟨t.1, le_rfl⟩

abbrev ξ'ObjIso (S : ISeg κ Λ E j) (i k : Λ) (hi : i ≤ k) (hij : k < j) :
    S.ξ' ⟨i, by valid⟩ ≅ (S.val (Opposite.op ⟨k, by valid⟩)).ξ.obj ⟨i, hi⟩ :=
  eqToIso <| congr($(S.2 (homOfLE hi : ⟨i, by valid⟩ ⟶ ⟨k, by valid⟩).op).ξ.obj ⟨i, le_rfl⟩).symm

open Opposite in
set_option backward.isDefEq.respectTransparency false in
@[implicit_reducible]
def ξ (S : ISeg κ Λ E j) :
    Set.Iio j ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj where
  obj t := S.ξ' t
  map {s t} f :=
    (S.ξ'ObjIso s.1 t.1 (leOfHom f) t.property).hom ≫
      (S.val (Opposite.op t)).ξ.map (homOfLE (leOfHom f)) ≫
      (S.ξ'ObjIso t.1 t.1 le_rfl t.property).inv
  map_id x := by simp
  map_comp {u v w} f g := by
    have := (S.val (Opposite.op w)).ξ.map_comp
      (homOfLE (leOfHom f : ⟨u, by simpa using (leOfHom (f ≫ g))⟩ ≤ ⟨v, by simpa using leOfHom g⟩))
      (homOfLE (leOfHom g : (⟨v, by simpa using (leOfHom g)⟩ : Set.Iic w.1) ≤ ⟨w, le_rfl⟩))
    simp at this
    dsimp [ξ'ObjIso, ξ']
    simp only [Functor.op_obj, Monotone.functor_obj, homOfLE_leOfHom, Category.comp_id,
      Category.assoc, CostructuredArrow.hom_eq_iff, CostructuredArrow.comp_left,
      CostructuredArrow.eqToHom_left, this]
    simp_rw [← Category.assoc]
    congr 1
    have := congr($(S.2 (homOfLE (leOfHom g) :
      (⟨v, by simpa using (leOfHom g)⟩ : Set.Iic w) ⟶ ⟨w, by valid⟩).op).ξ).symm
    simp [Functor.congr_hom this]
    rfl

def ξObjIso (S : ISeg κ Λ E j) (i k : Λ) (hi : i ≤ k) (hij : k < j) :
    S.ξ.obj ⟨i, by valid⟩ ≅ (S.val (Opposite.op ⟨k, by valid⟩)).ξ.obj ⟨i, hi⟩ :=
  eqToIso <| congr($(S.2 (homOfLE hi : ⟨i, by valid⟩ ⟶ ⟨k, by valid⟩).op).ξ.obj ⟨i, le_rfl⟩).symm

theorem ξObjIso_hom_natural (S : ISeg κ Λ E j) (i i' i'' : Λ) (hi' : i ≤ i') (hii'' : i' < i'')
      (hij : i'' < j) :
      (S.ξObjIso i i'' (hi'.trans hii''.le) hij).hom ≫
          (S.1 <| Opposite.op ⟨i'', Set.mem_Iio.mpr hij⟩).ξ.map
        (homOfLE hi' : (⟨i, (hi'.trans_lt hii'')⟩ : Set.Iio i'') ⟶ ⟨i', hii''⟩) =
      S.ξ.map (homOfLE hi') ≫ (S.ξObjIso i' i'' hii''.le (by valid)).hom :=
    sorry

theorem ξObjIso_hom_natural' (S : ISeg κ Λ E j) (i i' : Λ) (hi' : i ≤ i') (hij : i' < j) :
      (S.ξObjIso i i' hi' hij).hom ≫
          (S.1 <| Opposite.op ⟨i', Set.mem_Iio.mpr hij⟩).ξ.map
        (homOfLE hi' : (⟨i, _⟩ : Set.Iic i') ⟶ ⟨i', le_rfl⟩) =
      S.ξ.map (homOfLE hi') ≫ (S.ξObjIso i' i' le_rfl hij).hom :=
    sorry

theorem ξObjIso_inv_natural' (S : ISeg κ Λ E j) (i i' : Λ) (hi' : i ≤ i') (hij : i' < j) :
      (S.1 <| Opposite.op ⟨i', Set.mem_Iio.mpr hij⟩).ξ.map
        (homOfLE hi' : (⟨i, _⟩ : Set.Iic i') ⟶ ⟨i', le_rfl⟩) ≫ (S.ξObjIso i' i' le_rfl hij).inv  =
     (S.ξObjIso i i' hi' hij).inv ≫ S.ξ.map (homOfLE hi') :=
    sorry

theorem ξObjIso_inv_natural (S : ISeg κ Λ E j) (i i' i'' : Λ) (hi' : i ≤ i') (hii'' : i' < i'')
      (hij : i'' < j) :
      (S.1 <| Opposite.op ⟨i'', Set.mem_Iio.mpr hij⟩).ξ.map
        (homOfLE hi' : (⟨i, (hi'.trans_lt hii'')⟩ : Set.Iio i'') ⟶ ⟨i', hii''⟩) ≫
        (S.ξObjIso i' i'' hii''.le hij).inv =
      (S.ξObjIso i i'' (hi'.trans hii''.le) hij).inv ≫ S.ξ.map (homOfLE hi') :=
    sorry

section
open Opposite

variable (S : ISeg κ Λ E j)

def ψ (u v : Λ) (huv : u < v) (hv : v < j) :
    F.obj (S.ξ.obj ⟨u, huv.trans hv⟩).left.obj ⟶ G.obj (S.ξ.obj ⟨v, hv⟩).left.obj :=
  F.map (S.ξObjIso u v huv.le hv).hom.left.hom ≫
    (S.val (op _)).ψ u v huv le_rfl ≫
    G.map (S.ξObjIso v v le_rfl hv).inv.left.hom

lemma sq₁ (k k' : Λ) (hk₁ : k < k') (hk₂ : k' < j) :
    S.ψ k k' hk₁ hk₂ ≫ G.map (S.ξ.obj ⟨k', Set.mem_Iio.mpr hk₂⟩).hom =
    F.map (S.ξ.obj ⟨k, Set.mem_Iio.mpr (hk₁.trans hk₂)⟩).hom ≫ E.hom := by
  dsimp [ψ, ξ]
  simp only [Category.assoc, ← G.map_comp, grind_helper]
  have ψ' : (S.1 (op ⟨k', hk₂⟩)).ψ k k' hk₁ _ ≫
      G.map ((S.1 (op ⟨k', hk₂⟩)).ξ.obj ⟨k', _⟩).hom = _ :=
    dsimp% (S.1 (Opposite.op ⟨k', hk₂⟩)).sq₁ k hk₁
  simp [ψ', ← F.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
lemma t₁ (k₁ k₂ k₃ : Λ) (h₁₂ : k₁ ≤ k₂) (h₂₃ : k₂ < k₃) (h₃ : k₃ < j) :
    S.ψ k₁ k₃ (by valid) h₃ =
    F.map (S.ξ.map (homOfLE h₁₂)).left.hom ≫ S.ψ k₂ k₃ h₂₃ (by valid) := by
  dsimp [ψ, ξ, ξ]
  have :=
    Functor.congr_hom
      congr($(S.2 (homOfLE h₂₃.le : (⟨k₂, by valid⟩ : Set.Iio j) ⟶ ⟨k₃, by valid⟩).op).ξ).symm
        (homOfLE h₁₂ : ⟨k₁, h₁₂⟩ ⟶ ⟨k₂, le_rfl⟩)
  simp [dsimp% (S.1 (Opposite.op ⟨k₃, h₃⟩)).t₁ k₁ k₂ k₃ h₁₂ h₂₃ le_rfl, this, ξObjIso, eqToIso,
    trunc]

set_option backward.isDefEq.respectTransparency false in
lemma t₂ (k₁ k₂ k₃ : Λ) (h₁₂ : k₁ < k₂) (h₂₃ : k₂ ≤ k₃) (h₃ : k₃ < j) :
    S.ψ k₁ k₃ (by valid) h₃ =
    S.ψ k₁ k₂ h₁₂ (by valid) ≫ G.map (S.ξ.map (homOfLE h₂₃)).left.hom := by
  have h' := dsimp% (S.1 <| op ⟨k₃, h₃⟩).t₂ k₁ k₂ k₃ h₁₂ h₂₃ le_rfl
  have := congr($(S.2 (homOfLE h₂₃ : (⟨k₂, by valid⟩ : Set.Iio j) ⟶ ⟨k₃, by valid⟩).op)).symm
  simp [h', ψ, ISeg.ξ, congr_ψ _ _ this, trunc, ← Functor.map_comp,
    ← Functor.map_comp_assoc, ξObjIso]

end

open Opposite in
set_option backward.isDefEq.respectTransparency false in
noncomputable def extend (E : Inserter F G) (j : Λ) (hj : Order.IsSuccLimit j)
      (S : ISeg κ Λ E j) (hΛ : HasCardinalLT Λ κ) :
      PositetskiInductionDataUpTo κ Λ E j :=
  let c : Limits.Cocone S.ξ :=
    IsCardinalFiltered.cocone (κ := κ) S.ξ (by
      rw [hasCardinalLT_arrow_iff_of_isThin, hasCardinalLT_iff_cardinal_mk_lt]
      · grw [Cardinal.mk_le_of_injective (Subtype.val_injective), ←
        hasCardinalLT_iff_cardinal_mk_lt]
        assumption
      · exact Cardinal.IsRegular.aleph0_le <| Fact.out)
  let ξ := SmallObject.SuccStruct.ofCocone c
  let ψ (j' k : Λ) (hj' : j' < k) (hk : k ≤ j) :
    F.obj (ξ.obj ⟨j', (by valid)⟩).left.obj ⟶ G.obj (ξ.obj ⟨k, hk⟩).left.obj :=
    if hk' : k = j then
      F.map (SmallObject.SuccStruct.ofCoconeObjIso c _ (by valid)).hom.left.hom ≫
      S.ψ j' (Order.succ j') (by valid) (by valid) ≫
        G.map (c.ι.app ⟨Order.succ j', by valid⟩).left.hom ≫
        G.map (SmallObject.SuccStruct.ofCoconeObjIsoPt c).inv.left.hom ≫
          eqToHom (by subst hk'; rfl)
        --G.map (SmallObject.SuccStruct.ofCoconeObjIsoPt c).inv.left.hom
    else
      F.map (SmallObject.SuccStruct.ofCoconeObjIso c _ (by valid)).hom.left.hom ≫
      S.ψ j' k (hj') (by valid) ≫
        G.map (SmallObject.SuccStruct.ofCoconeObjIso c _ (by valid)).inv.left.hom
  { ξ
    ψ
    sq₁ i i' := by
      dsimp [ψ, ξ]
      split_ifs with hj
      · simp [← Functor.map_comp, grind_helper, S.sq₁ _ _, ← Functor.map_comp_assoc]
      · simp at hj
    t₁ i i' i'' hi hi' hi'' := by
      dsimp [ψ, ξ]
      split_ifs with h₀
      · subst h₀
        simp
        sorry
      · simp_rw [S.t₁ i i' i'' (by valid) (by valid) (by valid),
          ← Category.assoc, ← F.map_comp]
        congr 3
        simp_rw [← ObjectProperty.FullSubcategory.comp_hom, ← CostructuredArrow.comp_left,
          SmallObject.SuccStruct.ofCoconeObjIso_hom_naturality]
    t₂ i i' i'' hi hi' hi'' := by
      dsimp [ψ, ξ]
      split_ifs with h₀ h₁ h₂
      · subst h₀ h₁
        simp
      · subst h₀
        have hh : i' < i'' := by valid
        have := (SmallObject.SuccStruct.ofCoconeObjIso c (Order.succ i) (by valid)).inv ≫=
          SmallObject.SuccStruct.ofCocone_map_to_top c (Order.succ i) (by valid)
        simp only [homOfLE_leOfHom, Functor.const_obj_obj, Iso.inv_hom_id_assoc,
          CostructuredArrow.hom_eq_iff, CostructuredArrow.comp_left] at this
        simp_rw [Category.assoc, ← G.map_comp_assoc, ← G.map_comp,
          ← ObjectProperty.FullSubcategory.comp_hom,
          ← this]
        simp only [homOfLE_leOfHom, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp,
          eqToHom_refl, Category.comp_id]
        by_cases hii : i' = Order.succ i
        · subst hii
          simp
        have hii' : Order.succ i < i'' := by valid
        have := S.t₂ i (Order.succ i) i' (by valid) (by simpa) (by valid)
        simp only [homOfLE_leOfHom, this, Category.assoc]
        congr 2
        simp_rw [← Functor.map_comp,
          ← ObjectProperty.FullSubcategory.comp_hom, ← CostructuredArrow.comp_left]
        congr 2
        rw [SmallObject.SuccStruct.ofCocone_map_to_top]
        · have := SmallObject.SuccStruct.ofCoconeObjIso_inv_naturality c (Order.succ i) i'
            (by valid) (by valid)
          simp at this
          simp only [Functor.const_obj_obj, Iso.inv_hom_id_assoc, CostructuredArrow.comp_left,
            homOfLE_leOfHom, reassoc_of% this.symm]
          simp_rw [← CostructuredArrow.comp_left, ← Functor.map_comp, homOfLE_comp]
          rw [SmallObject.SuccStruct.ofCocone_map_to_top]
          · simp
          · sorry
        · sorry
        -- rw [SmallObject.SuccStruct.ofCoconeObjIso_inv_naturality]
      · subst h₂
        grind
      · have hh : i'' < j := by valid
        have := S.t₂ i i' i'' (by valid) (by valid) (by valid)
        simp_rw [this, Category.assoc, ← Functor.map_comp, ← Category.assoc]
        congr 2
        have :=
          congr($(SmallObject.SuccStruct.ofCoconeObjIso_inv_naturality c i' i'' (by valid) (by valid)).left.hom)
        simp at this
        rw [this] }

open Opposite in
theorem exists_extension (E : Inserter F G) (j : Λ) (hj : Order.IsSuccLimit j)
      (S : ISeg κ Λ E j) (hΛ : HasCardinalLT Λ κ) :
      ∃ (y : (PositetskiInductionDataUpTo.functor ..).obj (op j)), ∀ (i : Λ) (hi : i < j),
        (PositetskiInductionDataUpTo.functor κ Λ E).map (homOfLE hi.le).op y =
          S.val (op ⟨i, hi⟩) := by
    use S.extend E j hj hΛ
    intro i hi
    dsimp [extend]
    fapply eqToHom_ext
    · sorry
    · sorry
    · sorry


end ISeg

@[implicit_reducible]
def Seg (E : Inserter F G) : Type _ := (PositetskiInductionDataUpTo.functor κ Λ E).sections

namespace Seg

variable {κ Λ} {E : Inserter F G} {j : Λ}

section

open Opposite

variable (S : Seg κ Λ E)

@[implicit_reducible]
def ξ (i : Λ) :
    CostructuredArrow (isCardinalPresentable K κ).ι E.obj :=
  (S.val (op i)).ξ.obj ⟨i, le_rfl⟩

def ξObjIso (i k : Λ) (hi : i ≤ k) :
    S.ξ i ≅ (S.val (op k)).ξ.obj ⟨i, hi⟩ :=
  eqToIso <| congr($(S.2 (homOfLE hi : i ⟶ k).op).ξ.obj ⟨i, le_rfl⟩).symm

set_option backward.isDefEq.respectTransparency false in
def functor :
    Λ ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj where
  obj := S.ξ
  map {s t} f :=
    (S.ξObjIso s t (leOfHom f)).hom ≫
      (S.val (op t)).ξ.map (homOfLE (leOfHom f)) ≫
      (S.ξObjIso t t le_rfl).inv
  map_id x := by simp
  map_comp {u v w} f g := by
    have := (S.val (Opposite.op w)).ξ.map_comp
      (homOfLE (leOfHom f : ⟨u, by simpa using (leOfHom (f ≫ g))⟩ ≤ ⟨v, by simpa using leOfHom g⟩))
      (homOfLE (leOfHom g : (⟨v, by simpa using (leOfHom g)⟩ : Set.Iic w) ≤ ⟨w, le_rfl⟩))
    simp at this
    dsimp [ξObjIso, ξ]
    simp only [homOfLE_leOfHom, Category.comp_id,
      Category.assoc, CostructuredArrow.hom_eq_iff, CostructuredArrow.comp_left,
      CostructuredArrow.eqToHom_left, this]
    simp_rw [← Category.assoc]
    congr 1
    have := congr($(S.2 (homOfLE (leOfHom g) :
      (⟨v, by simpa using (leOfHom g)⟩ : Set.Iic w) ⟶ ⟨w, by grind⟩).op).ξ).symm
    simp [Functor.congr_hom this]
    rfl

def ψ (u v : Λ) (huv : u < v) :
    F.obj (S.functor.obj u).left.obj ⟶ G.obj (S.functor.obj v).left.obj :=
  F.map (S.ξObjIso u v huv.le).hom.left.hom ≫
    (S.val (op _)).ψ u v huv le_rfl ≫
    G.map (S.ξObjIso v v le_rfl).inv.left.hom

lemma sq₁ (k k' : Λ) (hk₁ : k < k') :
    S.ψ k k' hk₁ ≫ G.map (S.functor.obj k').hom =
    F.map (S.functor.obj k).hom ≫ E.hom := by
  dsimp [ψ, functor, ξ]
  simp only [Category.assoc, ← G.map_comp, grind_helper]
  have ψ' : (S.1 (op k')).ψ k k' hk₁ _ ≫ G.map ((S.1 (op k')).ξ.obj ⟨k', _⟩).hom = _ :=
    dsimp% (S.1 (op k')).sq₁ k hk₁
  simp [ψ', ← F.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
lemma t₁ (k₁ k₂ k₃ : Λ) (h₁₂ : k₁ ≤ k₂) (h₂₃ : k₂ < k₃) :
    S.ψ k₁ k₃ (by valid) =
    F.map (S.functor.map (homOfLE h₁₂)).left.hom ≫ S.ψ k₂ k₃ h₂₃ := by
  dsimp [ψ, functor, ξ]
  have :=
    Functor.congr_hom
      congr($(S.2 (homOfLE h₂₃.le : (⟨k₂, by valid⟩ : Set.Iic k₃) ⟶ ⟨k₃, by valid⟩).op).ξ).symm
      (homOfLE h₁₂ : ⟨k₁, by valid⟩ ⟶ ⟨k₂, by valid⟩)
  simp [dsimp% (S.1 (Opposite.op k₃)).t₁ k₁ k₂ k₃ h₁₂ h₂₃ le_rfl, this, ξObjIso, eqToIso,
    trunc]

set_option backward.isDefEq.respectTransparency false in
lemma t₂ (k₁ k₂ k₃ : Λ) (h₁₂ : k₁ < k₂) (h₂₃ : k₂ ≤ k₃) :
    S.ψ k₁ k₃ (by valid) =
    S.ψ k₁ k₂ h₁₂ ≫ G.map (S.functor.map (homOfLE h₂₃)).left.hom := by
  have h' := dsimp% (S.1 <| op k₃).t₂ k₁ k₂ k₃ h₁₂ h₂₃ le_rfl
  have := congr($(S.2 (homOfLE h₂₃ : k₂ ⟶ k₃).op)).symm
  simp [h', ψ, Seg.ξ, congr_ψ _ _ this, trunc, ← Functor.map_comp,
    ← Functor.map_comp_assoc, ξObjIso, functor]

@[simps]
def ψ_nat :
    (S.functor ⋙ CostructuredArrow.proj _ _ ⋙ ObjectProperty.ι _ ⋙ F) ⟶
    (Order.succ_mono.functor ⋙ S.functor ⋙ CostructuredArrow.proj _ _ ⋙ ObjectProperty.ι _ ⋙ G)
    where
  app x := S.ψ x (Order.succ x) (Order.lt_succ x)
  naturality {i j} f := by
    simp only [Functor.comp_obj, CostructuredArrow.proj_obj, ObjectProperty.ι_obj, Monotone.functor,
      homOfLE_leOfHom, Functor.comp_map, CostructuredArrow.proj_map, ObjectProperty.ι_map]
    rw [← S.t₂, S.t₁ i j (Order.succ j)]
    rfl

end

end Seg

end limit

variable {κ} in
def mkBot [OrderBot Λ] {E : Inserter F G}
    (c : CostructuredArrow (isCardinalPresentable K κ).ι E.obj) :
    PositetskiInductionDataUpTo κ Λ E ⊥ where
  ξ := (Functor.const _).obj c
  ψ i j hij hk := False.elim <| by grind [not_lt_bot]
  t₁ j k l hjk hkl hl := False.elim <| by grind [not_lt_bot]
  t₂ j k l hjk hkl hl := False.elim <| by grind [not_lt_bot]
  sq₁ j hj := False.elim <| by grind [not_lt_bot]

lemma mkBotObjBotIso [OrderBot Λ] {E : Inserter F G}
    (c : CostructuredArrow (isCardinalPresentable K κ).ι E.obj) :
  (mkBot Λ c).ξ.obj ⟨⊥, le_rfl⟩ ≅ c := .refl _

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
