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
import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData
public import Mathlib.Tactic.CategoryTheory.Map
import Mathlib.Order.Interval.Set.InitialSeg

/-!
# Inserter categories are accessible

-/

namespace CategoryTheory.Inserter

universe w

section
-- Recall everything in the section below private.

/- The setup for accessibility of inserter categories, from Positselski’s paper:
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
as in Positselski, 4.5.
To realize the induction, we transform `j ↦ PositselskiInductionDataUpTo … j` into a
presheaf on `j` so that we can use `Functor.WellOrderInductionData`. From
a section of the presheaf, we can extract the chain out of `J` that we are looking for. -/
@[ext]
structure PositselskiInductionDataUpTo
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

namespace PositselskiInductionDataUpTo

open Order (succ)

/-- Macro for a quick discharger tactic that we will repeatedly use. This is an
optimized grind call for our use case (quick combinations of inequalities). -/
local macro "valid" : tactic =>
  `(tactic| grind (ematch := 3) (gen := 3) +order -ring +lia -inj -ac only
    [Subtype.mk_le_mk, Subtype.mk_lt_mk, Order.le_succ_iff_eq_or_le, Order.lt_succ_iff, Set.mem_Iic,
      Set.mem_Iio, Order.IsSuccLimit.succ_lt, → Order.succ_lt_succ, → bot_unique,
      not_lt_bot])

/-! In the following, we are going to move very frequently between Λ, Set.Iio _ and Set.Iic _.
Most of the time, this requires term annotations and rather boring grind-able proof obligations.

So we provide a small discharge tactic that is just a specialized `grind` call, and
elaborators iio% i j for `⟨i, …⟩ : Set.Iio j`, and iic% i j for `⟨i, _⟩ : Set.Iic j` to
write some terms more easily. -/

/-- `iio% i j` builds i as a term of Set.Iio j using the discharger to prove the
side goal. -/
local macro "iio% " i:term:max j:term:max : term => `((⟨$i, by valid⟩ : Set.Iio $j))

/-- `iic% i j` builds i as a term of Set.Iic j using the discharger to prove the
side goal. -/
local macro "iic% " i:term:max j:term:max : term => `((⟨$i, by valid⟩ : Set.Iic $j))

theorem eqToHom_ext {E : Inserter F G} {i : Λ} {b b' : PositselskiInductionDataUpTo κ Λ E i}
    (h_obj : ∀ (j : Set.Iic i), b.ξ.obj j = b'.ξ.obj j)
    (h_map : ∀ (j k : Λ) (hjk : j ≤ k) (hki : k ≤ i),
      b.ξ.map (homOfLE hjk : iic% j i ⟶ iic% k i) =
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

theorem congr_ψ {E : Inserter F G} {i : Λ} {b b' : PositselskiInductionDataUpTo κ Λ E i}
    (h : b = b') (j k : Λ) (hjk : j < k) (hki : k ≤ i) :
    b.ψ j k hjk hki = F.map (eqToHom congr((($h).ξ.obj _).left.obj)) ≫ b'.ψ j k hjk hki ≫
      G.map (eqToHom congr((($h).ξ.obj _).left.obj).symm) := by
  subst h
  simp

variable {κ} {Λ} in
omit [IsCardinalAccessibleCategory L κ] [WellFoundedLT Λ] [SuccOrder Λ]
  [NoMaxOrder Λ] in
/-- The main technical induction step from Positselski's 4.5, where we pick an index large enough
to ensure a set of properties. This crucially uses that Λ is small enough. -/
theorem exists_succ_of_hasCardinalLT {E : Inserter F G} {i : Λ}
    (b : PositselskiInductionDataUpTo κ Λ E i) (hΛ : HasCardinalLT Λ κ) :
    ∃ (ξ₂ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
      (ν : b.ξ.obj (iic% i i) ⟶ ξ₂)
      (ψ : F.obj (b.ξ.obj (iic% i i)).left.obj ⟶ G.obj ξ₂.left.obj),
      (F.map (b.ξ.obj (iic% i i)).hom ≫ E.hom = ψ ≫ G.map ξ₂.hom) ∧
      (∀ (j : Λ) (hj : j < i),
        b.ψ j i hj le_rfl ≫ G.map ν.left.hom =
        F.map (b.ξ.map <| homOfLE <| hj.le).left.hom ≫ ψ) := by
  let ξ₁ := b.ξ.obj (iic% i i)
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
  obtain ⟨ξ₂₁, v₀, v₁, hv₀⟩ := IsCardinalPresentable.exists_hom_above_of_isColimit κ hcolimGT
    (F.map ξ₁.hom ≫ E.hom) ξ₁
  -- At this point, the squares required to make that into a functor are not necessarily natural
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
        simp_rw [← Functor.map_comp]
        simp [ξ₁, b.sq₁ j j.prop, ← Functor.map_comp_assoc])
    exact ⟨uij, vij, by simpa using h⟩
  choose u ν huν using Uspec
  have h' : HasCardinalLT (Set.Iio i) κ := by
    grw [hasCardinalLT_iff_cardinal_mk_lt, Cardinal.mk_set_le, ← hasCardinalLT_iff_cardinal_mk_lt]
    assumption
  obtain ⟨ξ₂, ν₂, μ₀, h₂⟩ := IsCardinalFiltered.wideSpan ν h'
  let ξ₂₀ := IsCardinalFiltered.max (κ := κ) u h'
  -- Now, we check that we have obtained all the conditions we want:
  refine ⟨ξ₂, v₀ ≫ μ₀, v₁ ≫ G.map μ₀.left.hom, ?_, fun j hj ↦ ?_⟩
  · dsimp [ψ, ξ₁] at *
    simp only [Category.id_comp] at hv₀
    simp [← Functor.map_comp, hv₀]
  · have S1 := huν (iio% j i)
    simp [homOfLE_leOfHom, ← h₂ ⟨j, hj⟩, reassoc_of% S1]

omit [IsCardinalAccessibleCategory K κ]
  [IsCardinalAccessibleCategory L κ]
  [F.IsCardinalAccessible κ]
  [G.IsCardinalAccessible κ]
  [F.PreservesCardinalPresentable κ]
  [SuccOrder Λ]
  [WellFoundedLT Λ]
  [NoMaxOrder Λ] in
lemma sq₂ {i : Λ} {E : Inserter F G} (d : PositselskiInductionDataUpTo κ Λ E i)
    (j k l m : Λ) (hjk : j < k) (hkm : k ≤ m) (hjl : j ≤ l) (hlm : l < m) (hm : m ≤ i) :
    F.map (d.ξ.map (homOfLE hjl)).left.hom ≫ d.ψ l m hlm (by valid) =
    d.ψ j k hjk (by valid) ≫ G.map (d.ξ.map (homOfLE hkm)).left.hom := by
  rw [← d.t₂, ← d.t₁]
  all_goals grind

/-- Restricts a PositselskiInductionDataUpTo to a lower index,
turning PositselskiInductionDataUpTo into a presheaf. -/
@[implicit_reducible]
def trunc (E : Inserter F G)
    {i i' : Λ} (hii' : i ≤ i') (d : PositselskiInductionDataUpTo κ Λ E i') :
    PositselskiInductionDataUpTo κ Λ E i where
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
  obj i := PositselskiInductionDataUpTo κ Λ E i.unop
  map f := TypeCat.ofHom <| trunc κ Λ E (leOfHom f.unop)

namespace extend
open SmallObject.SuccStruct

attribute [local grind =] Subtype.mk_le_mk Order.lt_succ_iff homOfLE_comp
attribute [local grind =] CostructuredArrow.comp_left ObjectProperty.FullSubcategory.comp_hom

variable {κ} {Λ} {E : Inserter F G} {i : Λ} (b : PositselskiInductionDataUpTo κ Λ E i)
    (ξₙ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν : b.ξ.obj (iic% i i) ⟶ ξₙ)
    (ψ₀ : F.obj (b.ξ.obj <| iic% i i).left.obj ⟶ G.obj ξₙ.left.obj)
    (h₁ : F.map (b.ξ.obj <| iic% i i).hom ≫ E.hom = ψ₀ ≫ G.map ξₙ.hom)
    (h₂ : ∀ (j : Λ) (hj : j < i), F.map (b.ξ.map <| homOfLE hj.le).left.hom ≫ ψ₀ =
      b.ψ j i hj le_rfl ≫ G.map ν.left.hom)

abbrev ξ := extendToSucc (not_isMax _) b.ξ ν

lemma ξ_map_le_succ (j : Λ) (hj : j ≤ i) :
    (ξ b ξₙ ν).map (homOfLE (by valid) : iic% j (succ i) ⟶ iic% (succ i) (succ i)) =
    (extendToSuccObjIso (not_isMax _) b.ξ ν j (by valid)).hom ≫
      b.ξ.map (homOfLE hj) ≫ ν ≫ (extendToSuccObjSuccIso (not_isMax _) b.ξ ν).inv := by
  have := (extendToSucc (not_isMax _) b.ξ ν).map_comp
    (X := iic% j (succ i)) (Y := iic% i (succ i)) (Z := iic% (succ i) (succ i))
    (homOfLE <| by valid) (homOfLE <| by valid)
  dsimp at this
  simp only [this, extendToSucc_map_le_succ (not_isMax _) b.ξ ν,
    extendToSuccObjIso_hom_naturality_assoc]

abbrev ψ (j k : Λ) (hjk : j < k := by valid) (hk : k ≤ succ i := by valid) :
    F.obj ((extend.ξ b ξₙ ν).obj (iic% j (succ i))).left.obj ⟶
      G.obj ((extend.ξ b ξₙ ν).obj ⟨k, by simpa⟩).left.obj :=
  if hk' : k ≤ i then
    F.map (extendToSuccObjIso (not_isMax _) b.ξ ν j (by valid)).hom.left.hom ≫
      b.ψ j k (by valid) hk' ≫
      G.map (extendToSuccObjIso (not_isMax _) b.ξ ν k hk').inv.left.hom
  else
    F.map ((extend.ξ b ξₙ ν).map <| homOfLE (by valid)).left.hom ≫
      (F.map (extendToSuccObjIso (not_isMax _) b.ξ ν _ _).hom.left.hom ≫ ψ₀ ≫
      G.map (extendToSuccObjSuccIso (not_isMax _) b.ξ ν).inv.left.hom) ≫
      G.map ((extend.ξ b ξₙ ν).map <| homOfLE (by valid)).left.hom

lemma ψ_of_le (j k : Λ) (hjk : j < k := by valid) (hk : k ≤ i := by valid) :
    ψ b ξₙ ν ψ₀ j k =
    F.map (extendToSuccObjIso (not_isMax _) b.ξ ν j (by valid)).hom.left.hom ≫
      b.ψ j k (by valid) hk ≫
      G.map (extendToSuccObjIso (not_isMax _) b.ξ ν k hk).inv.left.hom := by
  simp [ψ, hk]

lemma ψ_succ (j : Λ) (hjk : j < succ i := by valid) :
    ψ b ξₙ ν ψ₀ j (succ i) =
      F.map ((extend.ξ b ξₙ ν).map <| homOfLE (by valid)).left.hom ≫
        (F.map (extendToSuccObjIso (not_isMax _) b.ξ ν _ _).hom.left.hom ≫ ψ₀ ≫
        G.map (extendToSuccObjSuccIso (not_isMax _) b.ξ ν).inv.left.hom) ≫
        G.map ((extend.ξ b ξₙ ν).map <| homOfLE (by valid)).left.hom := by
  simp [ψ]

include h₁ in
lemma sq₁ (j : Λ) (hj : j < succ i := by valid) :
    extend.ψ b ξₙ ν ψ₀ j (succ i) ≫
      G.map ((extend.ξ b ξₙ ν).obj (iic% (succ i) (succ i))).hom =
    F.map ((extend.ξ b ξₙ ν).obj (iic% j (succ i))).hom ≫ E.hom := by
  rw [ψ_succ b ξₙ ν ψ₀ j]
  simp only [homOfLE_leOfHom, Category.assoc, ← G.map_comp, grind_helper, ← h₁, ← F.map_comp_assoc]

lemma t₁ (j k l : Λ) (hjk : j ≤ k) (hkl : k < l) (hl : l ≤ Order.succ i) :
    extend.ψ b ξₙ ν ψ₀ j l =
    F.map ((extend.ξ b ξₙ ν).map (homOfLE hjk)).left.hom ≫ extend.ψ b ξₙ ν ψ₀ k l := by
  have : l ≤ i ∨ (k ≤ i ∧ l = succ i) := by valid
  obtain hl' | ⟨hki, rfl⟩ := this
  · have := congr(F.map
      $(extendToSuccObjIso_hom_naturality (not_isMax _) b.ξ ν j k (by valid) (by valid)).left.hom)
    simp only [homOfLE_leOfHom, CostructuredArrow.comp_left,
      ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at this
    simp [ψ_of_le b ξₙ ν ψ₀ j l (by valid), ψ_of_le b ξₙ ν ψ₀ k l (by valid),
      b.t₁ j k l (by valid) (by valid) (by valid), reassoc_of% this]
  · simp [ψ_succ b ξₙ ν ψ₀ j, ψ_succ b ξₙ ν ψ₀ k, ← CostructuredArrow.comp_left,
      ← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp_assoc]

include h₁ h₂ in
lemma t₂ (j k l : Λ) (hjk : j < k) (hkl : k ≤ l := by valid) (hl : l ≤ Order.succ i := by valid) :
    extend.ψ b ξₙ ν ψ₀ j l =
    extend.ψ b ξₙ ν ψ₀ j k ≫ G.map ((extend.ξ b ξₙ ν).map (homOfLE hkl)).left.hom := by
  obtain hl' | ⟨rfl, rfl⟩ | ⟨hk', rfl⟩ :=
    show l ≤ i ∨ (k = succ i ∧ l = succ i) ∨ (k ≤ i ∧ l = succ i) by valid
  · obtain rfl | hkl := hkl.eq_or_lt
    · simp
    have := congr(G.map
      $(extendToSuccObjIso_inv_naturality (not_isMax _) b.ξ ν k l (by valid) (by valid)).left.hom)
    simp only [homOfLE_leOfHom, CostructuredArrow.comp_left,
      ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at this
    simp [ψ_of_le b ξₙ ν ψ₀ j l (by valid), ψ_of_le b ξₙ ν ψ₀ j k (by valid),
      b.t₂ j k l (by valid) (by valid) (by valid), this]
  · simp
  · rw [ψ_succ b ξₙ ν ψ₀ j, ψ_of_le b ξₙ ν ψ₀ j k (by valid)]
    simp only [homOfLE_leOfHom, homOfLE_refl, Functor.map_id, CostructuredArrow.id_left,
      ObjectProperty.FullSubcategory.id_hom, Category.comp_id, Category.assoc]
    simp_rw [← F.map_comp_assoc, ← ObjectProperty.FullSubcategory.comp_hom,
      ← CostructuredArrow.comp_left, extendToSuccObjIso_hom_naturality]
    simp [ξ_map_le_succ (hj := hk'), reassoc_of% h₂ j (by valid),
      b.t₂ j k i (by valid) (by valid) (by valid)]

end extend

open SmallObject.SuccStruct in
@[implicit_reducible]
noncomputable def extend {E : Inserter F G} {i : Λ} (b : PositselskiInductionDataUpTo κ Λ E i)
    (ξₙ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν : b.ξ.obj (iic% i i) ⟶ ξₙ)
    (ψ : F.obj (b.ξ.obj <| iic% i i).left.obj ⟶ G.obj ξₙ.left.obj)
    (h₁ : F.map (b.ξ.obj <| iic% i i).hom ≫ E.hom = ψ ≫ G.map ξₙ.hom)
    (h₂ : ∀ (j : Λ) (hj : j < i), F.map (b.ξ.map <| homOfLE hj.le).left.hom ≫ ψ =
      b.ψ j i hj le_rfl ≫ G.map ν.left.hom) :
    PositselskiInductionDataUpTo κ Λ E (succ i) where
  ξ := extend.ξ b ξₙ ν
  ψ j k hj hk := extend.ψ b ξₙ ν ψ j k hj hk
  sq₁ j hj := extend.sq₁ b ξₙ ν ψ h₁ j hj
  t₁ j k l hjk hkl hl := extend.t₁ b ξₙ ν ψ j k l hjk hkl hl
  t₂ j k l hjk hkl hl := extend.t₂ b ξₙ ν ψ h₁ h₂ j k l hjk

theorem trunc_extend
    {E : Inserter F G} {i : Λ} (b : PositselskiInductionDataUpTo κ Λ E i)
    (ξₙ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν : b.ξ.obj ⟨i, Set.mem_Iic.mpr le_rfl⟩ ⟶ ξₙ)
    (ψ : F.obj (b.ξ.obj (iic% i i)).left.obj ⟶ G.obj ξₙ.left.obj)
    (h₁ : F.map (b.ξ.obj (iic% i i)).hom ≫ E.hom = ψ ≫ G.map ξₙ.hom)
    (h₂ : ∀ (j : Λ) (hj : j < i), F.map (b.ξ.map <| homOfLE hj.le).left.hom ≫ ψ =
      b.ψ j i hj le_rfl ≫ G.map ν.left.hom) :
    (b.extend κ Λ ξₙ ν ψ h₁ h₂).trunc κ Λ E (Order.le_succ i) = b := by
  fapply eqToHom_ext
  · intro j
    simp [trunc, extend, SmallObject.SuccStruct.extendToSucc, SmallObject.restrictionLE,
      SmallObject.SuccStruct.extendToSucc.obj]
    grind
  · intro j k hjk hki
    dsimp [trunc, extend, SmallObject.SuccStruct.extendToSucc, SmallObject.restrictionLE, extend.ξ]
    simp only [SmallObject.SuccStruct.extendToSucc.obj, Set.initialSegIicIicOfLE_toFun_coe, hki,
      SmallObject.SuccStruct.extendToSucc.map, ↓reduceDIte, homOfLE_leOfHom,
      CostructuredArrow.hom_eq_iff, CostructuredArrow.comp_left]
    rfl
  · intro j k hjk hki
    simp [trunc, extend, SmallObject.SuccStruct.extendToSucc, SmallObject.restrictionLE, extend.ξ,
      extend.ψ, hki, SmallObject.SuccStruct.extendToSuccObjIso,
      SmallObject.SuccStruct.extendToSucc.objIso]

attribute [local grind .] Order.le_succ
theorem surjective_trunc (hΛ : HasCardinalLT Λ κ) (E : Inserter F G) (i : Λ) :
    Function.Surjective (PositselskiInductionDataUpTo.trunc κ Λ E (Order.le_succ i)) := by
  intro b
  -- The hard work is done in exists_succ_of_hasCardinalLT, but we have to spend some time
  -- to repackage the output here
  obtain ⟨ξ₂, ν, ψ, h₁, h₂⟩ := exists_succ_of_hasCardinalLT b hΛ
  use b.extend _ _ ξ₂ ν ψ h₁ fun _ _ ↦ (h₂ ..).symm
  exact trunc_extend ..

section limit

@[implicit_reducible]
def ISeg (E : Inserter F G) (j : Λ) : Type _ :=
  ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
      PositselskiInductionDataUpTo.functor κ Λ E).sections

namespace ISeg

open Opposite

variable {κ Λ} {E : Inserter F G} {j : Λ}

abbrev ξ' (S : ISeg κ Λ E j) (t : Set.Iio j) :
    CostructuredArrow (isCardinalPresentable K κ).ι E.obj :=
  (S.val (op t)).ξ.obj (iic% t.1 t.1)

abbrev ξ'ObjIso (S : ISeg κ Λ E j) (i k : Λ) (hi : i ≤ k) (hij : k < j) :
    S.ξ' (iio% i j) ≅ (S.val (op (iio% k j))).ξ.obj (iic% i k) :=
  eqToIso <| congr($(S.2 (homOfLE hi : (iio% i j) ⟶ (iio% k j)).op).ξ.obj (iic% i i)).symm

set_option backward.isDefEq.respectTransparency false in
@[implicit_reducible]
def ξ (S : ISeg κ Λ E j) :
    Set.Iio j ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj where
  obj t := S.ξ' t
  map {s t} f :=
    (S.ξ'ObjIso s.1 t.1 (leOfHom f) t.property).hom ≫
      (S.val (op t)).ξ.map (homOfLE (leOfHom f)) ≫
      (S.ξ'ObjIso t.1 t.1 le_rfl t.property).inv
  map_id x := by simp
  map_comp {u v w} f g := by
    have := (S.val (op w)).ξ.map_comp
      (homOfLE (leOfHom f : ⟨u, by simpa using (leOfHom (f ≫ g))⟩ ≤ ⟨v, by simpa using leOfHom g⟩))
      (homOfLE (leOfHom g : (⟨v, by simpa using (leOfHom g)⟩ : Set.Iic w.1) ≤ iic% w.1 w.1))
    simp at this
    dsimp [ξ'ObjIso, ξ']
    simp only [Functor.op_obj, Monotone.functor_obj, homOfLE_leOfHom, Category.comp_id,
      Category.assoc, CostructuredArrow.hom_eq_iff, CostructuredArrow.comp_left,
      CostructuredArrow.eqToHom_left, this]
    simp_rw [← Category.assoc]
    congr 1
    have := congr($(S.2 (homOfLE (leOfHom g) :
      (⟨v, by simpa using (leOfHom g)⟩ : Set.Iic w) ⟶ (iic% w w)).op).ξ).symm
    simp [Functor.congr_hom this]
    rfl

lemma ξ_obj_eq (S : ISeg κ Λ E j) (i k : Λ)
    (hi : i ≤ k := by valid) (hij : k < j := by valid) :
    S.ξ.obj (iio% i j) = (S.val (op ⟨k, by valid⟩)).ξ.obj (iic% i k) :=
  congr($(S.2 (homOfLE hi : iio% i j ⟶ iio% k j).op).ξ.obj (iic% i i)).symm

def ξObjIso (S : ISeg κ Λ E j) (i k : Λ) (hi : i ≤ k := by valid) (hij : k < j := by valid) :
    S.ξ.obj (iio% i j) ≅ (S.val (op ⟨k, by valid⟩)).ξ.obj (iic% i k) :=
  eqToIso <| S.ξ_obj_eq i k hi hij

set_option backward.isDefEq.respectTransparency false in
lemma ξ_map_eq (S : ISeg κ Λ E j) (i i' i'' : Λ)
    (hi : i ≤ i' := by valid) (hi' : i' ≤ i'' := by valid)
    (hi'' : i'' < j := by valid) :
    S.ξ.map (homOfLE hi : iio% i j ⟶ iio% i' j) =
    (S.ξObjIso ..).hom ≫
      (S.val <| op ⟨i'', by valid⟩).ξ.map (homOfLE hi : iic% i i'' ⟶ iic% i' i'') ≫
      (S.ξObjIso ..).inv := by
  dsimp [ξ]
  rw [← Iso.inv_comp_eq, Iso.eq_comp_inv, Eq.comm]
  have : (S.1 (op (iio% i' j))).ξ.map (homOfLE hi) = _ := Functor.congr_hom
    congr($(S.2 (homOfLE hi' : (iio% i' j) ⟶ (iio% i'' j)).op).ξ).symm
      (homOfLE hi : iic% i i' ⟶ iic% i' i')
  dsimp at this
  simp [this, ξObjIso, eqToIso, trunc]

section
open Opposite

variable (S : ISeg κ Λ E j)

def ψ (u v : Λ) (huv : u < v := by valid) (hv : v < j := by valid) :
    F.obj (S.ξ.obj ⟨u, huv.trans hv⟩).left.obj ⟶ G.obj (S.ξ.obj ⟨v, hv⟩).left.obj :=
  F.map (S.ξObjIso u v huv.le hv).hom.left.hom ≫
    (S.val (op _)).ψ u v huv le_rfl ≫
    G.map (S.ξObjIso v v le_rfl hv).inv.left.hom

set_option backward.isDefEq.respectTransparency false in
lemma sq₁ (k k' : Λ) (hk₁ : k < k' := by valid) (hk₂ : k' < j := by valid) :
    S.ψ k k' ≫ G.map (S.ξ.obj (iio% k' j)).hom = F.map (S.ξ.obj (iio% k j)).hom ≫ E.hom := by
  dsimp [ψ, ξ]
  simp only [Category.assoc, ← G.map_comp, grind_helper]
  have ψ' : (S.1 (op (iio% k' j))).ψ k k' hk₁ _ ≫
      G.map ((S.1 (op (iio% k' j))).ξ.obj (iic% k' k')).hom = _ :=
    dsimp% (S.1 (Opposite.op ⟨k', hk₂⟩)).sq₁ k hk₁
  simp [ψ', ← F.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
lemma t₁ (k₁ k₂ k₃ : Λ)
    (h₁₂ : k₁ ≤ k₂ := by valid) (h₂₃ : k₂ < k₃ := by valid) (h₃ : k₃ < j := by valid) :
    S.ψ k₁ k₃ = F.map (S.ξ.map (homOfLE h₁₂)).left.hom ≫ S.ψ k₂ k₃ := by
  dsimp [ψ, ξ, ξ]
  have :=
    Functor.congr_hom
      congr($(S.2 (homOfLE h₂₃.le : iio% k₂ j ⟶ iio% k₃ j).op).ξ).symm
        (homOfLE h₁₂ : iic% k₁ k₂ ⟶ iic% k₂ k₂)
  simp [dsimp% (S.1 (Opposite.op ⟨k₃, h₃⟩)).t₁ k₁ k₂ k₃ h₁₂ h₂₃ le_rfl, this, ξObjIso, eqToIso,
    trunc]

set_option backward.isDefEq.respectTransparency false in
lemma t₂ (k₁ k₂ k₃ : Λ) (h₁₂ : k₁ < k₂) (h₂₃ : k₂ ≤ k₃) (h₃ : k₃ < j) :
    S.ψ k₁ k₃ (by valid) h₃ =
    S.ψ k₁ k₂ h₁₂ (by valid) ≫ G.map (S.ξ.map (homOfLE h₂₃)).left.hom := by
  have h' := dsimp% (S.1 <| op <| iio% k₃ j).t₂ k₁ k₂ k₃ h₁₂ h₂₃ le_rfl
  have := congr($(S.2 (homOfLE h₂₃ : iio% k₂ j ⟶ iio% k₃ j).op)).symm
  simp [h', ψ, ISeg.ξ, congr_ψ _ _ this, trunc, ← Functor.map_comp,
    ← Functor.map_comp_assoc, ξObjIso]

lemma sq₂ (j' k l m : Λ)
    (hjk : j' < k := by valid) (hkm : k ≤ m := by valid)
    (hjl : j' ≤ l := by valid) (hlm : l < m := by valid) (hm : m < j := by valid) :
    F.map (S.ξ.map (homOfLE hjl)).left.hom ≫ S.ψ l m hlm (by valid) =
    S.ψ j' k hjk (by valid) ≫ G.map (S.ξ.map (homOfLE hkm)).left.hom := by
  rwa [← S.t₂, ← @S.t₁]

namespace extend

noncomputable abbrev c (hΛ : HasCardinalLT Λ κ) : Limits.Cocone S.ξ :=
  IsCardinalFiltered.cocone (κ := κ) S.ξ <| by
    rw [hasCardinalLT_arrow_iff_of_isThin, hasCardinalLT_iff_cardinal_mk_lt]
    · grw [Cardinal.mk_le_of_injective (Subtype.val_injective),
        ← hasCardinalLT_iff_cardinal_mk_lt]
      assumption
    · exact Cardinal.IsRegular.aleph0_le <| Fact.out

noncomputable abbrev ξ (hΛ : HasCardinalLT Λ κ) :
    Set.Iic j ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj :=
  SmallObject.SuccStruct.ofCocone (c S hΛ)

variable (hΛ : HasCardinalLT Λ κ) (hj : Order.IsSuccLimit j)

noncomputable abbrev ψ (j' k : Λ) (hj' : j' < k := by valid) (hk : k ≤ j := by valid) :
    F.obj ((ξ S hΛ).obj (iic% j' j)).left.obj ⟶ G.obj ((ξ S hΛ).obj (iic% k j)).left.obj :=
  if hk' : k = j then
    F.map (SmallObject.SuccStruct.ofCoconeObjIso (c S hΛ) _ (by valid)).hom.left.hom ≫
    S.ψ j' (succ j') (by valid) (by valid) ≫
      G.map ((c S hΛ).ι.app (iio% (succ j') j)).left.hom ≫
      G.map (SmallObject.SuccStruct.ofCoconeObjIsoPt (c S hΛ)).inv.left.hom ≫
        eqToHom (by subst hk'; rfl)
  else
    F.map (SmallObject.SuccStruct.ofCoconeObjIso (c S hΛ) _ (by valid)).hom.left.hom ≫
    S.ψ j' k hj' (by valid) ≫
      G.map (SmallObject.SuccStruct.ofCoconeObjIso (c S hΛ) _ (by valid)).inv.left.hom

lemma sq₁ (i : Λ) (i' : i < j) :
    ψ S hΛ hj i j i' ≫ G.map ((ξ S hΛ).obj (iic% j j)).hom =
    F.map ((ξ S hΛ).obj (iic% i j)).hom ≫ E.hom := by
  dsimp [ψ, ξ]
  split_ifs with hj
  · simp [← Functor.map_comp, grind_helper, S.sq₁ i (succ i),
      ← Functor.map_comp_assoc]
  · simp at hj

lemma t₁ (i i' i'' : Λ) (hi : i ≤ i') (hi' : i' < i'') (hi'' : i'' ≤ j) :
    extend.ψ S hΛ hj i i'' =
    F.map ((extend.ξ S hΛ).map (homOfLE hi)).left.hom ≫ extend.ψ S hΛ hj i' i'' hi' := by
  dsimp [ψ, ξ]
  obtain rfl | hi'' := hi''.eq_or_lt
  · simp only [↓reduceDIte, eqToHom_refl, Category.comp_id, homOfLE_leOfHom]
    simp_rw [← Functor.map_comp_assoc, ← ObjectProperty.FullSubcategory.comp_hom,
      ← CostructuredArrow.comp_left,
      SmallObject.SuccStruct.ofCoconeObjIso_hom_naturality, CostructuredArrow.comp_left,
      ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc]
    obtain rfl | hi' := hi.eq_or_lt
    · simp
    have := S.sq₂ i (succ i) i' (succ i')
    simp_rw [reassoc_of% this, ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
      ← CostructuredArrow.comp_left, (c S hΛ).ι.naturality_assoc]
    simp
  · simp only [show ¬(i'' = j) by valid, ↓reduceDIte, homOfLE_leOfHom,
      S.t₁ i i' i'' (by valid) (by valid) (by valid), ← Category.assoc, ← F.map_comp]
    congr 3
    simp_rw [← ObjectProperty.FullSubcategory.comp_hom, ← CostructuredArrow.comp_left,
      SmallObject.SuccStruct.ofCoconeObjIso_hom_naturality]

lemma t₂ (i i' i'' : Λ) (hi : i < i') (hi' : i' ≤ i'') (hi'' : i'' ≤ j) :
    extend.ψ S hΛ hj i i'' =
    extend.ψ S hΛ hj i i' ≫ G.map ((extend.ξ S hΛ).map (homOfLE hi')).left.hom := by
  dsimp [ψ, ξ]
  obtain hi'' | ⟨rfl, hi'⟩ | ⟨rfl, rfl⟩ :=
    show i'' < j ∨ (i'' = j ∧ i' < i'') ∨ (i' = j ∧ i'' = j) by valid
  · simp [↓reduceDIte, show ¬ (i'' = j) by valid, show ¬ (i' = j) by valid,
      S.t₂ i i' i'' hi (by valid) (by valid),
      ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom, ← CostructuredArrow.comp_left,
      ← SmallObject.SuccStruct.ofCoconeObjIso_inv_naturality]
  · simp [↓reduceDIte, show ¬(i' = i'') by valid,
      S.t₂ i (succ i) i' (by valid) (by valid) (by valid),
      ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom, ← CostructuredArrow.comp_left,
      SmallObject.SuccStruct.ofCocone_map_to_top (c S hΛ) i' (by valid)]
  · simp

end extend

end

open Opposite in
@[implicit_reducible]
noncomputable def extend {E : Inserter F G} {j : Λ}
    (S : ISeg κ Λ E j) (hΛ : HasCardinalLT Λ κ) (hj : Order.IsSuccLimit j) :
    PositselskiInductionDataUpTo κ Λ E j where
  ξ := extend.ξ S hΛ
  ψ i k hi hk := extend.ψ S hΛ hj i k hi hk
  sq₁ i i' := extend.sq₁ S hΛ hj i i'
  t₁ i i' i'' hi hi' hi'' := extend.t₁ S hΛ hj i i' i'' hi hi' hi''
  t₂ i i' i'' hi hi' hi'' := extend.t₂ S hΛ hj i i' i'' hi hi' hi''

open Opposite in
set_option backward.isDefEq.respectTransparency false in
theorem exists_extension (E : Inserter F G) (j : Λ) (hj : Order.IsSuccLimit j)
    (S : ISeg κ Λ E j) (hΛ : HasCardinalLT Λ κ) :
    ∃ (y : (PositselskiInductionDataUpTo.functor ..).obj (op j)), ∀ (i : Λ) (hi : i < j),
      (PositselskiInductionDataUpTo.functor κ Λ E).map (homOfLE hi.le).op y =
        S.val (op (iio% i j)) := by
  use S.extend hΛ hj
  intro i hi
  dsimp [extend]
  fapply eqToHom_ext
  · intro j'
    change (SmallObject.SuccStruct.ofCocone (extend.c S hΛ)).obj (iic% j'.1 _) = _
    rw [SmallObject.SuccStruct.ofCocone_obj_eq _ j'.1 (by valid), S.ξ_obj_eq j' i]
  · intro j' k hj' hki
    change (extend.ξ S hΛ).map (homOfLE hj' : iic% j' j ⟶ iic% k j) = _
    simp [SmallObject.SuccStruct.ofCocone_map (extend.c S hΛ) _ _ (hj') (by valid),
      S.ξ_map_eq j' k i hj' hki,
      SmallObject.SuccStruct.ofCoconeObjIso, SmallObject.SuccStruct.ofCocone.objIso,
      ξObjIso]
  · intro j₁ k₁ hjk hki
    change extend.ψ S hΛ hj j₁ k₁ hjk = _
    simp only [extend.ψ, show k₁ ≠ j by valid, ↓reduceDIte, Functor.const_obj_obj]
    have := PositselskiInductionDataUpTo.congr_ψ κ Λ
      (S.2 (homOfLE hki : iio% k₁ j ⟶ iio% i j).op).symm j₁ k₁ hjk le_rfl
    dsimp at this
    simp only [SmallObject.SuccStruct.ofCoconeObjIso, SmallObject.SuccStruct.ofCocone.objIso,
      eqToIso.hom, CostructuredArrow.eqToHom_left, ObjectProperty.eqToHom_hom, eqToHom_map, ψ,
      Functor.op_obj, Monotone.functor_obj, Functor.comp_obj, ξObjIso, this, trunc,
      SmallObject.restrictionLE_obj, eqToIso_refl, Iso.refl_inv, CostructuredArrow.id_left,
      ObjectProperty.FullSubcategory.id_hom, Category.assoc, eqToHom_trans_assoc, eqToIso.inv]
    erw [Functor.map_id] -- urgh
    simp


end ISeg

@[implicit_reducible]
def Seg (E : Inserter F G) : Type _ := (PositselskiInductionDataUpTo.functor κ Λ E).sections

namespace Seg

variable {κ Λ} {E : Inserter F G} {j : Λ}

section

open Opposite

variable (S : Seg κ Λ E)

@[implicit_reducible]
def ξ (i : Λ) : CostructuredArrow (isCardinalPresentable K κ).ι E.obj :=
  (S.val (op i)).ξ.obj <| iic% i i

lemma ξ_obj_eq (i k : Λ) (hi : i ≤ k) :
    S.ξ i = (S.val (op k)).ξ.obj (iic% i k) :=
  congr($(S.2 (homOfLE hi : i ⟶ k).op).ξ.obj (iic% i i)).symm

def ξObjIso (i k : Λ) (hi : i ≤ k) :
    S.ξ i ≅ (S.val (op k)).ξ.obj (iic% i k) :=
  eqToIso <| S.ξ_obj_eq i k hi

@[implicit_reducible]
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
      (homOfLE (leOfHom g : (⟨v, by simpa using (leOfHom g)⟩ : Set.Iic w) ≤ iic% w w))
    simp at this
    dsimp [ξObjIso, ξ]
    simp only [homOfLE_leOfHom, Category.comp_id,
      Category.assoc, CostructuredArrow.hom_eq_iff, CostructuredArrow.comp_left,
      CostructuredArrow.eqToHom_left, this]
    simp_rw [← Category.assoc]
    congr 1
    have := congr($(S.2 (homOfLE (leOfHom g) :
      (⟨v, by simpa using (leOfHom g)⟩ : Set.Iic w) ⟶ iic% w w).op).ξ).symm
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
  have ψ' : (S.1 (op k')).ψ k k' hk₁ _ ≫ G.map ((S.1 (op k')).ξ.obj (iic% k' k')).hom = _ :=
    dsimp% (S.1 (op k')).sq₁ k hk₁
  simp [ψ', ← F.map_comp_assoc]

set_option backward.isDefEq.respectTransparency false in
lemma t₁ (k₁ k₂ k₃ : Λ) (h₁₂ : k₁ ≤ k₂) (h₂₃ : k₂ < k₃) :
    S.ψ k₁ k₃ (by valid) =
    F.map (S.functor.map (homOfLE h₁₂)).left.hom ≫ S.ψ k₂ k₃ h₂₃ := by
  dsimp [ψ, functor, ξ]
  have :=
    Functor.congr_hom
      congr($(S.2 (homOfLE h₂₃.le : iic% k₂ k₃ ⟶ iic% k₃ k₃).op).ξ).symm
      (homOfLE h₁₂ : iic% k₁ k₂ ⟶ iic% k₂ k₂)
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
def ψNatTrans :
    (S.functor ⋙ CostructuredArrow.proj _ _ ⋙ ObjectProperty.ι _ ⋙ F) ⟶
    (Order.succ_mono.functor ⋙ S.functor ⋙ CostructuredArrow.proj _ _ ⋙ ObjectProperty.ι _ ⋙ G)
    where
  app x := S.ψ x (succ x) (Order.lt_succ x)
  naturality {i j} f := by
    simp only [Functor.comp_obj, CostructuredArrow.proj_obj, ObjectProperty.ι_obj, Monotone.functor,
      homOfLE_leOfHom, Functor.comp_map, CostructuredArrow.proj_map, ObjectProperty.ι_map]
    rw [← S.t₂, S.t₁ i j (succ j)]
    rfl

end

end Seg

end limit

section constructor

variable {κ} in
/-- Construct a `PositselskiInductionDataUpTo κ Λ E (Order.succ ⊥)` from the data
of ξ₀ ⟶ ξ₁ equipped with a map F.obj ξ₀ ⟶ G.map ξ₁ -/
noncomputable def mkBot [OrderBot Λ] {E : Inserter F G}
    (ξ₀ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj) :
    --(ν₀ : ξ₀ ⟶ ξ₁) (ψ₀ : F.obj ξ₀.left.obj ⟶ G.obj ξ₁.left.obj) :
    PositselskiInductionDataUpTo κ Λ E ⊥ where
  ξ := (Functor.const _ |>.obj ξ₀)
  ψ i j hij hk := False.elim <| by valid
  t₁ j k l hjk hkl hl := False.elim <| by valid
  t₂ j k l hjk hkl hl := False.elim <| by valid
  sq₁ j hj := False.elim <| by valid

variable {κ} in
noncomputable def mkBotObjBotIso [OrderBot Λ] {E : Inserter F G}
    (c : CostructuredArrow (isCardinalPresentable K κ).ι E.obj) :
  (mkBot Λ c).ξ.obj ⟨⊥, le_rfl⟩ ≅ c := .refl _

variable {κ} in
noncomputable def mkSuccBot [OrderBot Λ] {E : Inserter F G}
    (ξ₀ ξ₁ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν₀ : ξ₀ ⟶ ξ₁) (ψ₀ : F.obj ξ₀.left.obj ⟶ G.obj ξ₁.left.obj)
    (h : F.map ξ₀.hom ≫ E.hom = ψ₀ ≫ G.map ξ₁.hom) :
    PositselskiInductionDataUpTo κ Λ E (Order.succ ⊥) :=
  (mkBot Λ ξ₀).extend κ Λ ξ₁ ν₀ ψ₀ h (by valid)

section

variable {κ} [OrderBot Λ] {E : Inserter F G}
    (ξ₀ ξ₁ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν₀ : ξ₀ ⟶ ξ₁) (ψ₀ : F.obj ξ₀.left.obj ⟶ G.obj ξ₁.left.obj)
    (h : F.map ξ₀.hom ≫ E.hom = ψ₀ ≫ G.map ξ₁.hom)

lemma mkSuccBot_bot_eq : (mkSuccBot Λ ξ₀ ξ₁ ν₀ ψ₀ h).ξ.obj ⟨⊥, Order.le_succ _⟩ = ξ₀ :=
  SmallObject.SuccStruct.extendToSucc_obj_eq (hi := le_rfl) ..

lemma mkSuccBot_succ_bot_eq : (mkSuccBot Λ ξ₀ ξ₁ ν₀ ψ₀ h).ξ.obj ⟨Order.succ ⊥, le_rfl⟩ = ξ₁ :=
  SmallObject.SuccStruct.extendToSucc_obj_succ_eq ..

lemma mkSuccBot_map_homOfLE_eq :
    (mkSuccBot Λ ξ₀ ξ₁ ν₀ ψ₀ h).ξ.map
      (homOfLE (Order.le_succ _) : iic% ⊥ (succ ⊥) ⟶ iic% (succ ⊥) (succ ⊥)) =
    eqToHom (mkSuccBot_bot_eq ..) ≫ ν₀ ≫ eqToHom (mkSuccBot_succ_bot_eq ..).symm :=
  SmallObject.SuccStruct.extendToSucc_map_le_succ ..

lemma mkSuccBot_ψ :
    (mkSuccBot Λ ξ₀ ξ₁ ν₀ ψ₀ h).ψ ⊥ (succ ⊥) (by valid) (by valid) =
      F.map (eqToHom (mkSuccBot_bot_eq ..)).left.hom ≫ ψ₀ ≫
      G.map (eqToHom (mkSuccBot_succ_bot_eq ..).symm).left.hom := by
  dsimp [mkSuccBot, extend]
  rw [extend.ψ_succ (mkBot Λ ξ₀) ξ₁ ν₀ ψ₀ _]
  simp only [homOfLE_refl, Functor.map_id, CostructuredArrow.id_left,
    ObjectProperty.FullSubcategory.id_hom, Category.comp_id, Category.id_comp]
  rfl

end

end constructor

end PositselskiInductionDataUpTo

open PositselskiInductionDataUpTo Order Limits in
lemma positselski_4_5 [OrderBot Λ] (hΛ : HasCardinalLT Λ κ)
    (E : Inserter F G) (S T : K)
    [IsCardinalPresentable S κ] [IsCardinalPresentable T κ]
    [HasColimitsOfShape Λ K] [HasColimitsOfShape Λ L]
    [PreservesColimitsOfShape Λ F] [PreservesColimitsOfShape Λ G]
    (σ : F.obj S ⟶ G.obj T)
    (u : S ⟶ T) (v : T ⟶ E.obj)
    (h : σ ≫ G.map v = F.map u ≫ F.map v ≫ E.hom) :
    ∃ (B : Inserter F G) (_ : IsCardinalPresentable B.obj κ) (f : B ⟶ E) (g : T ⟶ B.obj),
      σ ≫ G.map g = F.map u ≫ F.map g ≫ B.hom ∧
      g ≫ f.hom = v := by
  -- First, we summon a diagram to write T as a κ-filtered colimits of κ-filtered objects.
  let O₀ := isCardinalPresentable K κ -- shorthand to make things a bit more compact.
  have : IsFiltered (CostructuredArrow O₀.ι E.obj) := isFiltered_of_isCardinalFiltered _ κ
  let hcolimT := O₀.ι.denseAt E.obj -- E.obj ≅ colim_ξ T_ξ
  have (X : K) : PreservesColimitsOfShape (CostructuredArrow O₀.ι X) G :=
    G.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _
  let hcolimGT := isColimitOfPreserves G (O₀.ι.denseAt E.obj) -- G(E.obj) ≅ colim_ξ G(T_ξ)
  -- Now we get a first factorization for σ
  obtain ⟨ξ₀, v₀, hv₀⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimT v
  dsimp at v₀ hv₀
  simp only [Category.id_comp] at hv₀
  -- local grind helper :
  have help {x y : CostructuredArrow O₀.ι E.obj} (f : x ⟶ y) :
      f.left.hom ≫ y.hom = x.hom := by
    simp
  obtain ⟨ξ₁₀, ψ₀₀, hψ₀₀⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimGT
    (F.map ξ₀.hom ≫ E.hom)
  dsimp at ψ₀₀ hψ₀₀
  -- let’s continue : we want to have...
  obtain ⟨ξ₁, ψ₀₁, hψ₀₁⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolimGT
    (F.map u ≫ F.map v₀ ≫ ψ₀₀ ≫ G.map (IsFiltered.rightToMax ξ₀ ξ₁₀).left.hom)
    (σ ≫ G.map v₀ ≫ G.map (IsFiltered.leftToMax ξ₀ ξ₁₀).left.hom)
    (by dsimp; grind)
  dsimp at ψ₀₀ hψ₀₁
  let u₀ : ξ₀ ⟶ ξ₁ := IsFiltered.leftToMax _ _ ≫ ψ₀₁
  let ψ₀ : F.obj ξ₀.left.obj ⟶ G.obj ξ₁.left.obj :=
    ψ₀₀ ≫ G.map (IsFiltered.rightToMax ξ₀ ξ₁₀).left.hom ≫ G.map ψ₀₁.left.hom
  -- "Then, the heptagonal diagram commutes"
  have he1 : σ ≫ G.map v₀ ≫ G.map u₀.left.hom = F.map u ≫ F.map v₀ ≫ ψ₀ := by
    dsimp [u₀, ψ₀]
    grind
  -- "Notice that the pentagonal diagram commutes"
  have he2 : ψ₀ ≫ G.map ξ₁.hom = F.map u₀.left.hom ≫ F.map ξ₁.hom ≫ E.hom := by
    dsimp [u₀, ψ₀]
    grind
  have : NoMaxOrder κ.ord.ToType := Cardinal.noMaxOrder (Cardinal.IsRegular.aleph0_le Fact.out)
  -- Anyway, we now construct the thing, let’s take bot
  let data : CategoryTheory.Functor.WellOrderInductionData
      (functor κ Λ E) :=
    Functor.WellOrderInductionData.ofExists
      (fun i hi ↦ surjective_trunc κ Λ hΛ E i)
      (fun j hj S ↦ ISeg.exists_extension E j hj S hΛ)
  let D₀ : PositselskiInductionDataUpTo κ Λ E (succ ⊥) := .mkSuccBot Λ ξ₀ ξ₁ u₀ ψ₀ (by
    rwa [← dsimp% CostructuredArrow.w u₀, Functor.map_comp, Category.assoc, Eq.comm])
  let S : Seg κ Λ E :=
    (data.surjective' (succ ⊥) (not_isSuccLimit_succ ⊥) D₀).choose
  have S_val : S.val (Opposite.op <| succ ⊥) = D₀ :=
    (data.surjective' (succ ⊥) (not_isSuccLimit_succ ⊥) D₀).choose_spec
  let Ξ₀ : Λ ⥤ CostructuredArrow O₀.ι E.obj := S.functor
  have e₀ : Ξ₀.obj ⊥ = ξ₀ :=
    (S.ξ_obj_eq ⊥ (succ ⊥) (le_succ _)).trans <|
      (congr($(S_val).ξ.obj ⟨⊥, le_succ ⊥⟩)).trans <|
        mkSuccBot_bot_eq ..
  have e₁ : Ξ₀.obj (succ ⊥) = ξ₁ :=
    (S.ξ_obj_eq (succ ⊥) (succ ⊥) le_rfl).trans <|
      (congr($(S_val).ξ.obj ⟨succ ⊥, le_rfl⟩)).trans <|
        mkSuccBot_succ_bot_eq ..
  have e₂ : Ξ₀.map (homOfLE <| le_succ ⊥) = eqToHom e₀ ≫ u₀ ≫ eqToHom e₁.symm := by
    dsimp [Ξ₀, Seg.functor]
    rw [Functor.congr_hom (congr($(S_val).ξ)), mkSuccBot_map_homOfLE_eq]
    simp [Seg.ξObjIso, Seg.ξ]
  let Θ :
      Ξ₀ ⋙ CostructuredArrow.proj (isCardinalPresentable K κ).ι E.obj ⋙
          (isCardinalPresentable K κ).ι ⋙ F ⟶
        _ ⋙ Ξ₀ ⋙ CostructuredArrow.proj (isCardinalPresentable K κ).ι E.obj ⋙
          (isCardinalPresentable K κ).ι ⋙ G :=
    S.ψNatTrans
  have e₁ : Θ.app ⊥ = F.map (eqToHom e₀).left.hom ≫ ψ₀ ≫ G.map (eqToHom e₁.symm).left.hom := by
    dsimp [Θ, Seg.ψNatTrans, Seg.ψ]
    rw [congr_ψ _ _ S_val, mkSuccBot_ψ]
    simp [Seg.ξObjIso, Seg.ξ]
  -- need to work out that colimit but should be ok
  have : O₀.IsClosedUnderColimitsOfShape Λ :=
    CategoryTheory.isClosedUnderColimitsOfShape_isCardinalPresentable K (by
      rwa [hasCardinalLT_arrow_iff_of_isThin _ κ (Cardinal.IsRegular.aleph0_le Fact.out)])
  have : HasColimitsOfShape Λ O₀.FullSubcategory := hasColimitsOfShape_of_closedUnderColimits ..
  have : (succ_mono (α := Λ)).functor.Final :=
    (Monotone.final_functor_iff _).mpr fun j ↦ ⟨j, le_succ j⟩
  let U := colimit Ξ₀
  let t := colimMap Θ
  let t1 : F.obj U.left.obj ⟶ G.obj U.left.obj :=
    (preservesColimitIso (CostructuredArrow.proj O₀.ι E.obj ⋙ O₀.ι ⋙ F) Ξ₀).hom ≫ t ≫
    (Functor.Final.colimitIso (succ_mono.functor) _).hom ≫ (preservesColimitIso _ _).inv
  let UU : Inserter F G := ⟨t1⟩
  refine ⟨UU, ?_, ⟨U.hom, ?_⟩,
    v₀ ≫ (eqToHom e₀.symm).left.hom ≫ (colimit.ι Ξ₀ ⊥).left.hom, ?_, ?_⟩
  · dsimp [U, UU, t1]
    infer_instance
  · dsimp [U, UU, t1]
    apply isColimitOfPreserves (CostructuredArrow.proj O₀.ι E.obj ⋙ O₀.ι ⋙ F)
      (colimit.isColimit Ξ₀) |>.hom_ext
    intro j
    have e₁ := ι_preservesColimitIso_hom (CostructuredArrow.proj O₀.ι E.obj ⋙ O₀.ι ⋙ F) Ξ₀ j
    dsimp at e₁
    simp [← Functor.map_comp_assoc, reassoc_of% e₁, t, ← G.map_comp, Θ, Ξ₀,
      (S.sq₁ j (succ j) (lt_succ j)).symm]
  · have := ι_preservesColimitIso_hom (CostructuredArrow.proj O₀.ι E.obj ⋙ O₀.ι ⋙ F) Ξ₀ ⊥
    dsimp at this
    simp [UU, t1, t, reassoc_of% this]
    simp [e₁, ← reassoc_of% he1, ← colimit.w Ξ₀ (homOfLE (le_succ ⊥) : ⊥ ⟶ _),
      -colimit.w, e₂]
  · simp only [Functor.comp_obj, CostructuredArrow.proj_obj, ObjectProperty.ι_obj,
      Category.assoc, UU, t1, t, ← colimit.w Ξ₀ (homOfLE (le_succ ⊥) : ⊥ ⟶ _), e₂]
    simp [-CostructuredArrow.eqToHom_left, -ObjectProperty.eqToHom_hom, U, hv₀]

abbrev O₁ (F G : K ⥤ L) : ObjectProperty (Inserter F G) :=
  (isCardinalPresentable K κ).inverseImage (Inserter.proj F G)

abbrev Δ (E : Inserter F G) := CostructuredArrow ((O₁ κ F G).ι) E

open Limits

lemma isCardinalFiltered_Δ [OrderBot Λ] (hΛ : HasCardinalLT Λ κ) (E : Inserter F G)
    [HasColimitsOfShape Λ K] [HasColimitsOfShape Λ L]
    [PreservesColimitsOfShape Λ F] [PreservesColimitsOfShape Λ G] :
    IsCardinalFiltered (Δ κ E) κ := by
  rw [isCardinalFiltered_iff']
  -- first, represent the object underlying E as a κ-filtered colimit of κ-presentable objects
  let O₀ := isCardinalPresentable K κ -- shorthand to make the writing more compact
  have : IsFiltered (CostructuredArrow O₀.ι E.obj) := isFiltered_of_isCardinalFiltered _ κ
  have (X : K) : PreservesColimitsOfShape (CostructuredArrow O₀.ι X) G :=
    G.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _
  let hcolimG := isColimitOfPreserves G (O₀.ι.denseAt E.obj) -- G(E.obj) ≅ colim_ξ G(T_ξ)
  have cp (x : (CostructuredArrow (O₁ κ F G).ι E)) :
    IsCardinalPresentable ((O₁ κ F G).ι.obj x.left).obj κ := by
    have := (CostructuredArrow.left x).property
    simpa using this
  -- FIXME. shouldn’t be needed
  have cp (x : (CostructuredArrow (O₁ κ F G).ι E)) :
    IsCardinalPresentable (F.obj (CostructuredArrow.left x).obj.obj) κ := by
    have := (CostructuredArrow.left x).property
    simp only [O₁, ObjectProperty.prop_inverseImage_iff, proj_obj] at this
    infer_instance
  let hcolimS := O₀.ι.denseAt E.obj -- E.obj ≅ colim_ξ S_ξ
  refine ⟨fun ι v hι ↦ ?_, fun ι r p f hι hι' ↦ ?_⟩
  · -- There exists an index ξ₀ such that all the v_j factorizes through the index in K
    -- TODO: extract the part where we take an index and advance it by one.
    have b (j : ι) := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimS (v j).hom.hom
    dsimp at b
    simp only [Category.id_comp] at b
    choose s0 f0 hf0 using b
    let ξ₀ := IsCardinalFiltered.max s0 hι
    let t0 (j : ι) : (v j).left.obj.obj ⟶ ξ₀.left.obj :=
     (f0 j) ≫ (IsCardinalFiltered.toMax s0 hι j).left.hom
    have he (j : ι) :
        F.map (t0 j) ≫ F.map ξ₀.hom ≫ E.hom = (v j).left.obj.hom ≫ G.map (t0 j) ≫ G.map ξ₀.hom := by
      simp [t0, ← Functor.map_comp_assoc, ← Functor.map_comp, ξ₀, grind_helper, hf0]
    -- Following Positselski we also find a u : ξ₀ ⟶ ξ₁ with σ : F.obj ξ₀ ⟶ G.obj ξ₁ such that
    -- `F.map ξ₀.hom ≫ E.hom = σ ≫ G.map ξ₁.hom` and
    -- `F.map (t0 j) ≫ σ = (v j).hom.hom ≫ G.map (t0 j) ≫ G.map u`
    obtain ⟨ξ₁, u, σ, h1, h2⟩ : ∃ (ξ₁ : CostructuredArrow O₀.ι E.obj) (u : ξ₀ ⟶ ξ₁)
      (σ : F.obj ξ₀.left.obj ⟶ G.obj ξ₁.left.obj),
      F.map ξ₀.hom ≫ E.hom = σ ≫ G.map ξ₁.hom ∧
      ∀ (j : ι), F.map (t0 j) ≫ σ = (v j).left.obj.hom ≫ G.map (t0 j) ≫ G.map u.left.hom := by
        obtain ⟨ξ₁, ν₁, σ, hξ₁₀⟩ := IsCardinalPresentable.exists_hom_above_of_isColimit κ hcolimG
          (F.map ξ₀.hom ≫ E.hom) ξ₀
        dsimp at hξ₁₀ ν₁ σ
        simp only [Category.id_comp] at hξ₁₀
        have (j : ι) := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolimG
          (F.map (t0 j) ≫ σ) ((v j).left.obj.hom ≫ G.map (t0 j) ≫ G.map ν₁.left.hom) (by
            simp [hξ₁₀, t0, ξ₀, hf0, ← Functor.map_comp_assoc, ← Functor.map_comp])
        choose p1 p2 p3 using this
        simp only [Functor.comp_obj, CostructuredArrow.proj_obj, ObjectProperty.ι_obj,
          Functor.comp_map, CostructuredArrow.proj_map, ObjectProperty.ι_map, Category.assoc] at p3
        obtain ⟨ξ₁', ν₁', u', h'⟩ := IsCardinalFiltered.wideSpan p2 hι
        -- let ξ₁' := IsCardinalFiltered.coeq (fun i ↦ p2 i ≫ IsCardinalFiltered.toMax p1 hι i) hι
        -- let ν₁' : ξ₀ ⟶ ξ₁' := ν₁ ≫ IsCardinalFiltered.toCoeq _ hι
        let σ' : F.obj ξ₀.left.obj ⟶ G.obj ξ₁'.left.obj := σ ≫ G.map u'.left.hom
        refine ⟨ξ₁', ν₁ ≫ u', σ', ?_, fun i ↦ ?_⟩
        · simp [σ', ← G.map_comp, hξ₁₀]
        · simp [← h' i, reassoc_of% p3, σ']
    -- Then, we use the main lemma with ξ₀ and ξ₁
    obtain ⟨b, _, f, g, h₁, h₂⟩ :=
      positselski_4_5 κ Λ hΛ E (S := ξ₀.left.obj) (T := ξ₁.left.obj) σ u.left.hom ξ₁.hom
        (by simp [← h1, ← F.map_comp_assoc])
    let b' : (O₁ κ F G).FullSubcategory := ⟨b, by simpa [O₁]⟩
    let f' : b'.obj ⟶ E := f
    refine ⟨CostructuredArrow.mk (Y := b') f', fun i ↦
        ⟨⟨⟨⟨(t0 i) ≫ u.left.hom ≫ g, ?_⟩⟩, ⟨rfl⟩, ?_⟩⟩⟩
    · simp [← reassoc_of% h2 i, b', h₁]
    · ext
      simp [f', b', h₂, ξ₀, t0, hf0]
  · -- first, be pick an index ξ₀ that coequalizes all the components of f
    obtain ⟨ξ₀, u, hu⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimS p.hom.hom
    dsimp at u hu
    simp only [Category.id_comp] at hu
    have : IsCardinalPresentable r.left.obj.obj κ := by
      have := r.left.property
      simp at this
      infer_instance
    obtain ⟨ξ₀', v, hv⟩ :=
      IsCardinalPresentable.exists_eq_of_isColimit'_of_hasCardinalLT κ hcolimS hι
        (fun i ↦ (f i).left.hom.hom ≫ u) (fun i i' ↦ by
          simp [hu, dsimp% congr($((f i').w).hom), dsimp% congr($((f i).w).hom)])
    obtain ⟨ξ₁₀, ν₁₀, σ₀, hξ₁₀⟩ := IsCardinalPresentable.exists_hom_above_of_isColimit κ hcolimG
      (F.map ξ₀.hom ≫ E.hom) ξ₀'
    dsimp at hξ₁₀ σ₀
    simp only [Category.id_comp] at hξ₁₀ σ₀
    obtain ⟨ξ₁, ν₁, hν₁⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolimG
      (F.map u ≫ σ₀) (p.left.obj.hom ≫ G.map u ≫ G.map v.left.hom ≫ G.map ν₁₀.left.hom) (by
        simp [hξ₁₀, ← Functor.map_comp, ← Functor.map_comp_assoc, hu])
    simp at hν₁
    -- Then, we use the main lemma with ξ₀ and ξ₁
    obtain ⟨b, _, f', g, h₁, h₂⟩ :=
      positselski_4_5 κ Λ hΛ E ξ₀.left.obj ξ₁.left.obj
        (σ₀ ≫ G.map ν₁.left.hom) (v ≫ ν₁₀ ≫ ν₁).left.hom ξ₁.hom
        (by simp [← Functor.map_comp, ← Functor.map_comp_assoc, hξ₁₀])
    dsimp [CostructuredArrow.left] at h₁ h₂ hν₁ hv ⊢
    simp only [Category.assoc, Functor.map_comp] at hv hν₁ h₁ h₂
    let b' : (O₁ κ F G).FullSubcategory := ⟨b, by simpa [O₁]⟩
    let f'' : b'.obj ⟶ E := f'
    use CostructuredArrow.mk (Y := b') f''
    let pt : ι := hι'.some
    use ⟨⟨⟨u ≫ (v ≫ ν₁₀ ≫ ν₁).left.hom ≫ g, ?_⟩⟩, ⟨rfl⟩, ?_⟩,
      ⟨⟨⟨(f pt).left.hom.hom ≫ u ≫ (v ≫ ν₁₀ ≫ ν₁).left.hom ≫ g, ?_⟩⟩, ⟨rfl⟩, ?_⟩
    · intro i
      ext
      simp [reassoc_of% hv i pt]
    · simp only [CostructuredArrow.mk_left, CostructuredArrow.comp_left,
        ObjectProperty.FullSubcategory.comp_hom, Category.assoc, Functor.map_comp, b']
      grind
    · ext
      simp [f'', h₂, hu]
    · simp only [CostructuredArrow.mk_left, CostructuredArrow.comp_left,
        ObjectProperty.FullSubcategory.comp_hom, Category.assoc, Functor.map_comp]
      grind
    · ext
      have := congr($(CostructuredArrow.w (f pt)).hom)
      simp only [ObjectProperty.ι_obj, ObjectProperty.ι_map, comp_hom] at this
      simp [f'', h₂, hu, this]

/-- A shorthand for the forgetful functor from Δ κ E to κ-presentable objects mapping to E.obj.
We will show below that this functor is final, which will prove that every inserter
is a filtered colimit of κ-presentable inserters. -/
@[implicit_reducible, simps!]
def U (E : Inserter F G) :
    Δ κ E ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj :=
  CostructuredArrow.map₂
    (F := ObjectProperty.lift _ ((O₁ _ _ _).ι ⋙ Inserter.proj F G)
      (by intro x; simpa [O₁] using x.property))
    (G := Inserter.proj F G)
    { app X := 𝟙 _ }
    (𝟙 _)

lemma final (E : Inserter F G) [OrderBot Λ] (hΛ : HasCardinalLT Λ κ) (E : Inserter F G)
    [HasColimitsOfShape Λ K] [HasColimitsOfShape Λ L]
    [PreservesColimitsOfShape Λ F] [PreservesColimitsOfShape Λ G] : (U κ E).Final := by
  sorry

end

/-- Let `Λ < κ` be a pair of infinite cardinals such that `κ` is regular. Assume that
- `K` and `L` are `κ`-accessible categories with colimits of `Λ`-chains.
- `F G : C ⥤ D` are `κ`-accessible functors preserving colimits of `Λ`-chains
- `F` preserves `κ`-presentable objects.

Then the category `Inserter F G` is `κ`-accessible.
This theorem appears as [4.1, Positselski]

Note that if `K` and `L` are `κ`-accessible, and `F`, `G` are `κ`-accessible with `F` preserving
`κ`-presentable objects then since `κ` is sharply less than `κ⁺`, one can show that the pair
`κ < κ⁺` satisfies the conditions above, and hence `Inserter F G` is `κ⁺`-accessible in
this situation. -/
public theorem isCardinalAccessibleCategory
    {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalAccessibleCategory K κ] [IsCardinalAccessibleCategory L κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ]
    (Λ : Type w) [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ)
    [Limits.HasColimitsOfShape Λ K] [Limits.HasColimitsOfShape Λ L]
    [Limits.PreservesColimitsOfShape Λ F] [Limits.PreservesColimitsOfShape Λ G] :
    IsCardinalAccessibleCategory (Inserter F G) κ :=
  -- Using that the functor `U : Δ κ E ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj` is
  -- final, any inserter is the κ-filtered colimit of its projection from Δ κ E,
  -- as one can postcompose with U to check this, and the canonical cocone for E.obj is a
  -- colimit diagram.
  sorry

end CategoryTheory.Inserter
