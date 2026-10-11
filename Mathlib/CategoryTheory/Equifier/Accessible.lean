/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Equifier.Basic
public import Mathlib.CategoryTheory.Presentable.PreservesCardinalPresentable
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable

import Mathlib.CategoryTheory.ObjectProperty.FullSubcategoryInf
import Mathlib.CategoryTheory.Presentable.Dense
import Mathlib.CategoryTheory.Presentable.StrongGenerator
import Mathlib.CategoryTheory.Presentable.Uniformization
import Mathlib.Order.Interval.Set.InitialSeg
import Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc
import Mathlib.CategoryTheory.SmallObject.Iteration.FunctorOfCocone
import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData

/-! # Equifier categories are accessible

In this file, we show that categories of equifiers are accessible in good situations.

More precisely, given `F G : K ⥤ L` two `κ`-accessible functors between two κ-accessible categories,
such that `F` preserves `κ`-presentable objects. Assuming there exists an ordinal `Λ < κ` such that
`K` and `L` admits Λ-indexed colimits and such that `F` and `G` preserve `Λ`-indexed colimits,
then for every parralel natural transforations `Φ Ψ : F ⟶ G`, we show that the category
`Equifier Φ Ψ` remains κ-accessible, and that its κ-presentable objects
are exactly objects `E : Equifier F G` such that `E.obj` is a κ-presentable object of `K`.

This result appears as Theorem 3.1 in [positselski2014]. We follow the proof from this reference.

Using the uniformization theorem, this implies that if `F G : K ⥤ L` are accessible functors between
accessible categories, then `Equifier Φ Ψ` is an accessible category for every pair of natural
transformations `Φ Ψ : F ⟶ G`.

-/

namespace CategoryTheory.Equifier

universe w

public instance {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular] {Φ Ψ : F ⟶ G} (X : Equifier Φ Ψ)
    [IsCardinalPresentable X.obj κ] [IsCardinalAccessibleCategory K κ]
    [IsCardinalAccessibleCategory L κ] [F.IsCardinalAccessible κ]
    [G.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ] :
    IsCardinalPresentable X κ := by
  have : IsCardinalPresentable (ι _ _ |>.obj X) κ := by assumption
  apply IsCardinalPresentable.mk
  intro I _ _ B b hb
  have : Limits.HasColimitsOfShape I K := HasCardinalFilteredColimits.hasColimitsOfShape _ κ I
  have : Limits.PreservesColimitsOfShape I F :=
    Functor.IsCardinalAccessible.preservesColimitOfShape κ I
  let hcolim := Limits.isColimitOfPreserves (ι _ _) hb
  refine ⟨fun f ↦ ?_, fun i f₁ f₂ h ↦ ?_⟩
  · obtain ⟨i, f', hf'⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolim f.hom
    dsimp at f' hf'
    exact ⟨i, ⟨f'⟩, by ext; simp [hf']⟩
  · obtain ⟨j, u, hu⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolim
      (f₁ := f₁.hom) (f₂ := f₂.hom) congr($(h).hom)
    exact ⟨j, u, by ext; simpa using hu⟩

namespace Accessible
-- Recall everything in the section below is private.

/- The setup for accessibility of equifier categories, from Positselski’s paper:
`F G : K ⥤ L` are a parallel pair of κ-accessible functors between κ-accessible categories
where `F` in addition preserves κ-presentable objects. A given infinite ordinal Λ < κ such
that `K` has colimits of Λ-chains is given, and we assume that `F` preserve these colimits.

Throughout this file, this setup is realized as
```
variable {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalAccessibleCategory K κ] [IsCardinalAccessibleCategory L κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ]
    (Λ : Type*) [Nonempty Λ] [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ)
    [Limits.HasColimitsOfShape Λ K] [Limits.HasColimitsOfShape Λ L]
    [Limits.PreservesColimitsOfShape Λ F] [Limits.PreservesColimitsOfShape Λ G]
    (Φ Ψ : F ⟶ G)
```
-/

section factors

variable {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular] {Φ Ψ : F ⟶ G}

/- The goal of this section is to prove the following intermediate result, which
is the lamma `factors` below:
for every morphism `f : S ⟶ E.obj` from a κ-presentable object to the object
in `Equifier Φ Ψ`, the morphism `f` factorizes through an object `U` that is both
in `Equifier Φ Ψ` and that is `κ`-presentable as an object of `K`.

Compare to the similar strategy used in `CategoryTheory/Inserter/Accessible.lean`: the
case of the equifiers is much easier as we do not have to bookkeep an extra morphism.

This is Lemma 3.2 in [positselski2014].

This lemma requires inductively building a chain of indices satisfying some property
in a diagram used to write `E.obj` as a κ-filtered colimit of κ-presentable object.

Setting up the induction is the main technical content of this section.
Compare with similar material in `CategoryTheory/Inserter/Accessible.lean`.

-/

open Order (succ)

/-- Macro for a quick discharger tactic that we will repeatedly use. This is an
optimized grind call for our use case (quick combinations of inequalities). -/
local macro "valid" : tactic =>
  `(tactic| grind (ematch := 3) (gen := 3)
    +order -ext -etaStruct -extAll -ring +lia -inj -ac -funCC -linarith -mbtc only
      [Subtype.mk_le_mk, Subtype.mk_lt_mk, Order.le_succ_iff_eq_or_le, Order.lt_succ_iff,
        Set.mem_Iic, Set.mem_Iio, Order.IsSuccLimit.succ_lt, → Order.succ_lt_succ, → bot_unique,
        not_lt_bot])

/- In the following, we are going to move very frequently between `Λ`, `Set.Iio _` and `Set.Iic _`.
Most of the time, this requires term annotations and rather boring grind-able proof obligations,
so we provide a small discharge tactic that is just a specialized `grind` call handling these, an
elaborator `iio% i j` for `⟨i, …⟩ : Set.Iio j`, and an elaborator
`iic% i j` for `⟨i, _⟩ : Set.Iic j` in order to write some terms more easily. -/

/-- `iio% i j` builds i as a term of `Set.Iio j` using the discharger to prove the side goal. -/
local macro "iio% " i:term:max j:term:max : term => `((⟨$i, by valid⟩ : Set.Iio $j))

/-- `iic% i j` builds i as a term of `Set.Iic j` using the discharger to prove the side goal. -/
local macro "iic% " i:term:max j:term:max : term => `((⟨$i, by valid⟩ : Set.Iic $j))

/-- The structure of a partial induction for constructing the chain as in
Prop. 3.2 of [positselski2014].

To realize the induction, we transform `j ↦ PartialChainUpTo … j` into a
presheaf on `j` so that we can use `Functor.WellOrderInductionData`.
From a section of the presheaf, we can extract the chain out of `Λ` that we are looking for. -/
@[ext]
structure PartialChainUpTo (Λ : Type*) [Preorder Λ] [SuccOrder Λ]
    (E : Equifier Φ Ψ) (i : Λ) where
  /-- Corresponds to all the previously constructed ξᵢ's -/
  ξ : Set.Iic i ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj
  h (j k : Λ) (hjk : j < k) (hk : k ≤ i) :
    Φ.app (ξ.obj (iic% j i)).left.obj ≫
      G.map (ξ.map (homOfLE (by valid) : iic% j i ⟶ iic% k i)).left.hom =
    Ψ.app (ξ.obj (iic% j i)).left.obj ≫
      G.map (ξ.map (homOfLE (by valid) : iic% j i ⟶ iic% k i)).left.hom

namespace PartialChainUpTo
variable (Λ : Type*) [LinearOrder Λ] [SuccOrder Λ]

/-- Restricts a PartialChainUpTo to a lower index, turning PartialChainUpTo into a presheaf. -/
@[implicit_reducible]
def trunc (E : Equifier Φ Ψ) {i i' : Λ} (hii' : i ≤ i') (d : PartialChainUpTo κ Λ E i') :
    PartialChainUpTo κ Λ E i where
  ξ := SmallObject.restrictionLE d.ξ hii'
  h j k hjk hk := by simpa using d.h j k hjk (by valid)

/-- Turning `i ↦ PartialChainUpTo κ Λ E i` into a functor. A section of this functor bundles an
extension of the ξ and ψ fields to all indices in Λ. -/
abbrev functor (E : Equifier Φ Ψ) : Λᵒᵖ ⥤ Type _ where
  obj i := PartialChainUpTo κ Λ E i.unop
  map f := TypeCat.ofHom <| trunc κ Λ E (leOfHom f.unop)

section successor

/- This section deals with the successor case of the transfinite induction that constructs
a chain in the proof of Prop. 3.2 of [positselski2014]. -/

namespace extend

open SmallObject.SuccStruct

variable [NoMaxOrder Λ] {κ} {Λ} {E : Equifier Φ Ψ} {i : Λ}
    (b : PartialChainUpTo κ Λ E i)
    (ξₙ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν : b.ξ.obj (iic% i i) ⟶ ξₙ)
    (hν : Φ.app (b.ξ.obj (iic% i i)).left.obj ≫ G.map ν.left.hom =
      Ψ.app (b.ξ.obj (iic% i i)).left.obj ≫ G.map ν.left.hom)

/-- The to-be ξ field of the extension -/
abbrev ξ := extendToSucc (not_isMax _) b.ξ ν

lemma ξ_map_le_succ (j : Λ) (hj : j ≤ i) :
    (ξ b ξₙ ν).map (homOfLE (by valid) : iic% j (succ i) ⟶ iic% (succ i) (succ i)) =
    (extendToSuccObjIso (not_isMax _) b.ξ ν j (by valid)).hom ≫
      b.ξ.map (homOfLE hj) ≫ ν ≫ (extendToSuccObjSuccIso (not_isMax _) b.ξ ν).inv := by
  have := (extendToSucc (not_isMax _) b.ξ ν).map_comp
    (X := iic% j (succ i)) (Y := iic% i (succ i)) (Z := iic% (succ i) (succ i))
    (homOfLE <| by valid) (homOfLE <| by valid)
  simp [dsimp% this, extendToSucc_map_le_succ (not_isMax _) b.ξ ν,
    extendToSuccObjIso_hom_naturality_assoc]

end extend

open Opposite in
/-- Extend a `PartialChainUpTo κ Λ E i` to a `PartialChainUpTo κ Λ E (succ i)` from the data of
compatible objects and maps -/
@[implicit_reducible]
noncomputable def extend [NoMaxOrder Λ] {E : Equifier Φ Ψ} {i : Λ}
    (b : PartialChainUpTo κ Λ E i)
    (ξₙ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν : b.ξ.obj (iic% i i) ⟶ ξₙ)
    (hν : Φ.app (b.ξ.obj (iic% i i)).left.obj ≫ G.map ν.left.hom =
      Ψ.app (b.ξ.obj (iic% i i)).left.obj ≫ G.map ν.left.hom) :
    PartialChainUpTo κ Λ E (succ i) where
  ξ := extend.ξ b ξₙ ν
  h j k hj hk := by
    obtain ⟨h, rfl⟩ | h :
        (j ≤ i ∧ k = succ i) ∨ k ≤ i := by valid
    · simp (discharger := valid) only [homOfLE_leOfHom, extend.ξ_map_le_succ,
        CostructuredArrow.comp_left, ObjectProperty.FullSubcategory.comp_hom,
        Functor.map_comp]
      rw [← Φ.naturality_assoc, ← Φ.naturality_assoc, reassoc_of% hν,
        Ψ.naturality_assoc, Ψ.naturality_assoc]
    · dsimp [extend.ξ]
      simp (discharger := valid) only [homOfLE_leOfHom, SmallObject.SuccStruct.extendToSucc_map,
        CostructuredArrow.comp_left, ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
      rw [← Φ.naturality_assoc, reassoc_of% b.h j k hj h, Ψ.naturality_assoc]

lemma trunc_extend [NoMaxOrder Λ] {E : Equifier Φ Ψ} {i : Λ}
    (b : PartialChainUpTo κ Λ E i)
    (ξₙ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν : b.ξ.obj (iic% i i) ⟶ ξₙ)
    (hν : Φ.app (b.ξ.obj (iic% i i)).left.obj ≫ G.map ν.left.hom =
      Ψ.app (b.ξ.obj (iic% i i)).left.obj ≫ G.map ν.left.hom) :
    (b.extend κ Λ ξₙ ν hν).trunc κ Λ E (Order.le_succ i) = b := by
  ext
  fapply Functor.ext
  · intro j
    simp [trunc, extend, SmallObject.SuccStruct.extendToSucc, SmallObject.restrictionLE,
      SmallObject.SuccStruct.extendToSucc.obj]
    grind
  · intro u v f
    simp [trunc, extend, extend.ξ,
      SmallObject.SuccStruct.extendToSucc_map (not_isMax _) b.ξ ν u.1 v.1 f.le v.2,
      SmallObject.SuccStruct.extendToSuccObjIso,
        SmallObject.SuccStruct.extendToSucc.objIso]
    rfl

open Limits in
lemma exists_succ [NoMaxOrder Λ] [IsCardinalAccessibleCategory K κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ]
    [F.PreservesCardinalPresentable κ]
    {E : Equifier Φ Ψ} {i : Λ} (b : PartialChainUpTo κ Λ E i) :
    ∃ (ξₙ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
      (ν : b.ξ.obj (iic% i i) ⟶ ξₙ),
      Φ.app (b.ξ.obj (iic% i i)).left.obj ≫ G.map ν.left.hom =
        Ψ.app (b.ξ.obj (iic% i i)).left.obj ≫ G.map ν.left.hom := by
  -- first pick any index
  have : IsFiltered (CostructuredArrow (isCardinalPresentable K κ).ι E.obj) :=
    isFiltered_of_isCardinalFiltered _ κ
  let hcolimT := (isCardinalPresentable K κ).ι.denseAt E.obj
  have (X : K) : PreservesColimitsOfShape (CostructuredArrow (isCardinalPresentable K κ).ι X) G :=
    G.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _
  let hcolimGT := isColimitOfPreserves G ((isCardinalPresentable K κ).ι.denseAt E.obj)
  -- Pick a first factorization of `S ⟶ E.obj` through some `T_ξ₀`.
  obtain ⟨ξ₀, ν₀, h₀⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimT
    (b.ξ.obj (iic% i i)).hom
  dsimp at ν₀ h₀
  simp only [Category.id_comp] at h₀
  obtain ⟨ξₙ, ν₁, h₁⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolimGT
    (Φ.app (b.ξ.obj (iic% i i)).left.obj ≫ G.map ν₀)
    (Ψ.app (b.ξ.obj (iic% i i)).left.obj ≫ G.map ν₀)
    (by simp [← NatTrans.naturality, E.prop])
  dsimp at h₁
  exact ⟨ξₙ, CostructuredArrow.homMk ⟨ν₀ ≫ ν₁.left.hom⟩
    (by simp [dsimp% CostructuredArrow.w ν₁, h₀]), by simpa using h₁⟩

theorem surjective_trunc [NoMaxOrder Λ] [IsCardinalAccessibleCategory K κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ]
    [F.PreservesCardinalPresentable κ] (E : Equifier Φ Ψ) (i : Λ) :
    Function.Surjective (PartialChainUpTo.trunc κ Λ E (Order.le_succ i)) := by
  intro b
  obtain ⟨ξ₂, ν, h₁⟩ := exists_succ κ Λ b
  use b.extend _ _ ξ₂ ν h₁
  exact trunc_extend ..

end successor

section limit

/- This section deals with the limit case of the transfinite induction that constructs
a chain in the proof of Prop. 3.2 of [positselski2014]. -/

/-- A wrapper around restricted sections of `PartialChainUpTo.functor`. -/
@[implicit_reducible]
def ISeg (E : Equifier Φ Ψ) (j : Λ) : Type _ :=
  ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
      PartialChainUpTo.functor κ Λ E).sections

namespace ISeg

open Opposite
variable {κ Λ} {E : Equifier Φ Ψ} {j : Λ}

/-- Wrapper around the first projection of an `ISeg`, with better typing. -/
nonrec def val (S : ISeg κ Λ E j) (t : Λ) (ht : t < j := by valid) : PartialChainUpTo κ Λ E t :=
  S.val (op <| iio% t j)

nonrec lemma prop (S : ISeg κ Λ E j) (t t' : Λ) (ht : t ≤ t') (ht' : t' < j) :
    PartialChainUpTo.trunc κ Λ E ht (S.val t') = S.val t :=
  S.2 (homOfLE ht : (iio% t j) ⟶ (iio% t' j)).op

/-- Extract the indices of the `PartialChainUpTo` constituting an `ISeg`,
to get indices for all `i < j`. -/
abbrev ξ' (S : ISeg κ Λ E j) (t : Set.Iio j) :
    CostructuredArrow (isCardinalPresentable K κ).ι E.obj :=
  (S.val t).ξ.obj (iic% t.1 t.1)

/-- Isomorphism (in fact equality) between `ξ` and the `ξ` field of any component
of the `ISeg` (provided the indices make sense). -/
abbrev ξ'ObjIso (S : ISeg κ Λ E j) (i k : Λ) (hi : i ≤ k) (hij : k < j) :
    S.ξ' (iio% i j) ≅ (S.val k).ξ.obj (iic% i k) :=
  eqToIso <| congr($(S.prop i k hi hij).ξ.obj _).symm

/-- Repackage the `ξ` fields of all the `PartialChainUpTo` constituting an `ISeg κ Λ E j`
into a functor out of `Set.Iio j`. -/
@[implicit_reducible]
def ξ (S : ISeg κ Λ E j) :
    Set.Iio j ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj where
  obj t := S.ξ' t
  map {s t} f :=
    (S.ξ'ObjIso s.1 t.1 (leOfHom f) t.property).hom ≫
      (S.val t).ξ.map (homOfLE (leOfHom f)) ≫
      (S.ξ'ObjIso t.1 t.1 le_rfl t.property).inv
  map_id x := by simp
  map_comp {u v w} f g := by
    have := (S.val w).ξ.map_comp
      (homOfLE (leOfHom f : ⟨u, by simpa using (leOfHom (f ≫ g))⟩ ≤ ⟨v, by simpa using leOfHom g⟩))
      (homOfLE (leOfHom g : (⟨v, by simpa using (leOfHom g)⟩ : Set.Iic w.1) ≤ iic% w.1 w.1))
    simp only [homOfLE_leOfHom, homOfLE_comp, CostructuredArrow.hom_eq_iff,
      CostructuredArrow.comp_left] at this
    simp [ξ'ObjIso, ξ', Set.Iio, this,
      Functor.congr_hom congr($(S.prop v.1 w.1 (leOfHom g) w.prop).ξ).symm, trunc]

lemma ξ_obj_eq (S : ISeg κ Λ E j) (i k : Λ)
    (hi : i ≤ k := by valid) (hij : k < j := by valid) :
    S.ξ.obj (iio% i j) = (S.val k).ξ.obj (iic% i k) :=
  congr($(S.2 (homOfLE hi : iio% i j ⟶ iio% k j).op).ξ.obj (iic% i i)).symm

/-- Characterizing isomorphism of the extracted functor out of `Set.Iio j`. -/
def ξObjIso (S : ISeg κ Λ E j) (i k : Λ) (hi : i ≤ k := by valid) (hij : k < j := by valid) :
    S.ξ.obj (iio% i j) ≅ (S.val k).ξ.obj (iic% i k) :=
  eqToIso <| S.ξ_obj_eq i k hi hij

lemma ξ_map_eq (S : ISeg κ Λ E j) (i i' i'' : Λ)
    (hi : i ≤ i' := by valid) (hi' : i' ≤ i'' := by valid)
    (hi'' : i'' < j := by valid) :
    S.ξ.map (homOfLE hi : iio% i j ⟶ iio% i' j) =
    (S.ξObjIso ..).hom ≫
      (S.val i'').ξ.map (homOfLE hi : iic% i i'' ⟶ iic% i' i'') ≫
      (S.ξObjIso ..).inv := by
  rw [← Iso.inv_comp_eq, Iso.eq_comp_inv, Eq.comm]
  have := Functor.congr_hom
    congr($(S.prop i' i'' hi' hi'').ξ).symm (homOfLE hi : iic% i i' ⟶ iic% i' i')
  simp [ξ, this, ξObjIso, eqToIso, trunc]

lemma h (S : ISeg κ Λ E j) (i₁ i₂ : Λ) (hjk : i₁ < i₂ := by valid) (hk : i₂ < j := by valid) :
    Φ.app (S.ξ.obj (iio% i₁ j)).left.obj ≫
      G.map (S.ξ.map (homOfLE (by valid) : iio% i₁ j ⟶ iio% i₂ j)).left.hom =
    Ψ.app (S.ξ.obj (iio% i₁ j)).left.obj ≫
      G.map (S.ξ.map (homOfLE (by valid) : iio% i₁ j ⟶ iio% i₂ j)).left.hom := by
  simp (discharger := valid) [ξ, ← NatTrans.naturality_assoc, (S.val i₂ _).h]

namespace extend

variable (S : ISeg κ Λ E j) [IsCardinalAccessibleCategory K κ]

/-- An arbitrary cocone over `S.ξ`, which exists as the diagram is small enough with
value in a κ-filtered category. -/
noncomputable def c (hΛ : HasCardinalLT Λ κ) : Limits.Cocone S.ξ :=
  IsCardinalFiltered.cocone (κ := κ) S.ξ <| by
    rw [hasCardinalLT_arrow_iff_of_isThin]
    exacts [hΛ.of_injective _ Subtype.val_injective,
      Cardinal.IsRegular.aleph0_le <| Fact.out]

/-- Extend `S.ξ : Set.Iio j ⥤  CostructuredArrow (isCardinalPresentable K κ).ι E.obj` to
a functor out of `Set.Iic j` by using an arbitrary cocone. -/
noncomputable def ξ (hΛ : HasCardinalLT Λ κ) :
    Set.Iic j ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj :=
  SmallObject.SuccStruct.ofCocone (c S hΛ)

section

/- To avoid running into transparency issue we have to provide a thin wrapper around the
SmallObject.SuccStruct.ofCocone API, with the correct prescribed types -/
variable (hΛ : HasCardinalLT Λ κ)

lemma ξ_obj_of_lt (i : Λ) (hi : i < j := by valid) :
    (extend.ξ S hΛ).obj (iic% i j) = S.ξ.obj (iio% i j) :=
  SmallObject.SuccStruct.ofCocone_obj_eq ..

lemma ξ_obj_top :
    (extend.ξ S hΛ).obj (iic% j j) = (c S hΛ).pt :=
  SmallObject.SuccStruct.ofCocone_obj_eq_pt ..

/-- Isomorphism characterizing extend.ξ on values less than the limit element. -/
noncomputable def ξObjIso (i : Λ) (hi : i < j := by valid) :
   (extend.ξ S hΛ).obj (iic% i j) ≅ S.ξ.obj (iio% i j) :=
  eqToIso <| extend.ξ_obj_of_lt S hΛ i hi

/-- Isomorphism characterizing extend.ξ on the limit element. -/
noncomputable def ξObjTopIso :
   (extend.ξ S hΛ).obj (iic% j j) ≅ (c S hΛ).pt :=
  eqToIso <| extend.ξ_obj_top S hΛ

@[reassoc]
lemma ξ_map (i₁ i₂ : Λ)
    (hi : i₁ ≤ i₂ := by valid) (hi₂ : i₂ < j := by valid) :
    (ξ S hΛ).map (homOfLE hi : iic% i₁ j ⟶ iic% i₂ j) =
    (ξObjIso S hΛ i₁).hom ≫ S.ξ.map (homOfLE (by valid)) ≫ (ξObjIso S hΛ i₂).inv :=
  SmallObject.SuccStruct.ofCocone_map ..

lemma ξ_map_to_top (i : Λ) (hi : i < j := by valid) :
    (ξ S hΛ).map (homOfLE hi.le) =
      (ξObjIso S hΛ i).hom ≫ (c S hΛ).ι.app (iio% i j) ≫ (ξObjTopIso S hΛ).inv :=
  SmallObject.SuccStruct.ofCocone_map_to_top ..

@[reassoc]
lemma ξObjIso_hom_naturality (i₁ i₂ : Λ) (hi : i₁ ≤ i₂ := by valid) (hi₂ : i₂ < j := by valid) :
    (ξ S hΛ).map (homOfLE hi : iic% i₁ j ⟶ iic% i₂ j) ≫
      (ξObjIso S hΛ i₂ hi₂).hom =
    (ξObjIso S hΛ i₁).hom ≫ S.ξ.map (homOfLE hi) :=
  SmallObject.SuccStruct.ofCoconeObjIso_hom_naturality ..

@[reassoc]
lemma ξObjIso_inv_naturality (i₁ i₂ : Λ) (hi : i₁ ≤ i₂ := by valid) (hi₂ : i₂ < j := by valid) :
    (ξObjIso S hΛ i₁).inv ≫ (ξ S hΛ).map (homOfLE hi : iic% i₁ j ⟶ iic% i₂ j) =
    S.ξ.map (homOfLE hi) ≫ (ξObjIso S hΛ i₂).inv :=
  SmallObject.SuccStruct.ofCoconeObjIso_inv_naturality ..

end

end extend

open Opposite in
/-- Extend an `ISeg κ Λ E j` (for a limit element j) into a `PartialChainUpTo κ Λ E j`. -/
@[implicit_reducible]
noncomputable def extend [NoMaxOrder Λ] [IsCardinalAccessibleCategory K κ]
    {E : Equifier Φ Ψ} {j : Λ}
    (S : ISeg κ Λ E j) (hΛ : HasCardinalLT Λ κ) (hj : Order.IsSuccLimit j) :
    PartialChainUpTo κ Λ E j where
  ξ := extend.ξ S hΛ
  h i k hi hk := by
    obtain rfl | hk := hk.eq_or_lt
    · have :=
        (extend.ξ S hΛ).map_comp
          (homOfLE (by valid) : iic% i k ⟶ iic% (succ i) k)
          (homOfLE (by valid) : iic% (succ i) k ⟶ iic% k k)
      simp at this
      simp (discharger := valid) only [homOfLE_leOfHom, this, extend.ξ_map,
        CostructuredArrow.comp_left, Category.assoc,
        ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp]
      rw [← NatTrans.naturality_assoc, reassoc_of% S.h i (succ i)]
      simp
    · simp (discharger := valid) only [homOfLE_leOfHom, extend.ξ_map,
        CostructuredArrow.comp_left, ObjectProperty.FullSubcategory.comp_hom,
        Functor.map_comp]
      rw [← NatTrans.naturality_assoc, reassoc_of% S.h i k]
      simp

open Opposite in
lemma exists_extension [NoMaxOrder Λ] [IsCardinalAccessibleCategory K κ]
    (E : Equifier Φ Ψ) (j : Λ) (hj : Order.IsSuccLimit j)
    (S : ISeg κ Λ E j) (hΛ : HasCardinalLT Λ κ) :
    ∃ (y : (PartialChainUpTo.functor ..).obj (op j)), ∀ (i : Λ) (hi : i < j),
      (PartialChainUpTo.functor κ Λ E).map (homOfLE hi.le).op y = S.val i hi := by
  use S.extend hΛ hj
  intro i hi
  dsimp [extend, trunc]
  ext
  fapply Functor.ext
  · intro j'
    change (extend.ξ _ _).obj (iic% j'.1 _) = _
    rw [extend.ξ_obj_of_lt _ _ j'.1 (by valid), S.ξ_obj_eq j' i]
  · intro j' k f
    have := f.le
    change (extend.ξ S hΛ).map (homOfLE f.le : iic% j' j ⟶ iic% k j) = _
    simp (discharger := valid) only [homOfLE_leOfHom, extend.ξ_map, extend.ξObjIso, eqToIso.hom,
      S.ξ_map_eq j' k i, ξObjIso, eqToIso.inv, Category.assoc, eqToHom_trans, eqToHom_trans_assoc,
      CostructuredArrow.hom_eq_iff, CostructuredArrow.comp_left, CostructuredArrow.eqToHom_left]
    rfl

end ISeg

end limit

section constructor

variable {κ} in
/-- Construct a `PartialChainUpTo κ Λ E ⊥` from the data of an object `ξ₀`. -/
noncomputable def mkBot [OrderBot Λ] {E : Equifier Φ Ψ}
    (ξ₀ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj) :
    PartialChainUpTo κ Λ E ⊥ where
  ξ := Functor.const _ |>.obj ξ₀
  h i j hij hk := False.elim <| by valid

lemma mkBot_bot_eq [OrderBot Λ] {E : Equifier Φ Ψ}
    (ξ₀ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj) :
    (mkBot Λ ξ₀).ξ.obj (iic% ⊥ ⊥) = ξ₀ :=
  rfl

end constructor

/-- A wrapper around sections of `PartialChainUpTo.functor`. -/
@[implicit_reducible]
def Seg (E : Equifier Φ Ψ) : Type _ := (PartialChainUpTo.functor κ Λ E).sections

namespace Seg

variable {κ Λ} {E : Equifier Φ Ψ} {j : Λ}

open Opposite

variable (S : Seg κ Λ E)

/-- Extract the `ξ` fields of all the `PartialChainUpTo` making up a section of
`PartialChainUpTo.functor`. -/
@[implicit_reducible]
def ξ (i : Λ) : CostructuredArrow (isCardinalPresentable K κ).ι E.obj :=
  (S.val (op i)).ξ.obj <| iic% i i

lemma ξ_obj_eq (i k : Λ) (hi : i ≤ k) :
    S.ξ i = (S.val (op k)).ξ.obj (iic% i k) :=
  congr($(S.2 (homOfLE hi : i ⟶ k).op).ξ.obj (iic% i i)).symm

/-- Characterizing isomorphism for `Seg.ξ`. -/
def ξObjIso (i k : Λ) (hi : i ≤ k) :
    S.ξ i ≅ (S.val (op k)).ξ.obj (iic% i k) :=
  eqToIso <| S.ξ_obj_eq i k hi

/-- Extract the `ξ` fields of all the `PartialChainUpTo` making up a section of
`PartialChainUpTo.functor` into a functor out of Λ.
This is eventually going to be the chains that we use for the proof of [positselski2014], 4.5. -/
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
    have e := (S.val (Opposite.op w)).ξ.map_comp
      (homOfLE (leOfHom f : ⟨u, by simpa using (leOfHom (f ≫ g))⟩ ≤ ⟨v, by simpa using leOfHom g⟩))
      (homOfLE (leOfHom g : (⟨v, by simpa using (leOfHom g)⟩ : Set.Iic w) ≤ iic% w w))
    simp only [homOfLE_leOfHom, homOfLE_comp, CostructuredArrow.hom_eq_iff,
      CostructuredArrow.comp_left] at e
    have := congr($(S.2 (homOfLE (leOfHom g) :
      (⟨v, by simpa using (leOfHom g)⟩ : Set.Iic w) ⟶ iic% w w).op).ξ).symm
    simp [ξObjIso, ξ, e, Functor.congr_hom this, trunc]

lemma h (i₁ i₂ : Λ) (hjk : i₁ < i₂ := by valid) :
    Φ.app (S.functor.obj i₁).left.obj ≫
      G.map (S.functor.map (homOfLE (by valid) : i₁ ⟶ i₂)).left.hom =
    Ψ.app (S.functor.obj i₁).left.obj ≫
      G.map (S.functor.map (homOfLE (by valid) :  i₁ ⟶ i₂)).left.hom := by
  simp (discharger := valid) [functor, ξ, ← NatTrans.naturality_assoc,
    reassoc_of% (S.val (op i₂)).h i₁ i₂ hjk]

end Seg

end PartialChainUpTo

variable (Φ Ψ) in
/-- Shorthand for the object property that we will eventually prove to be equal to
the class of κ-presentable objects of the equifier category -/
abbrev O₁ : ObjectProperty (Equifier Φ Ψ) :=
  (isCardinalPresentable K κ).inverseImage (Equifier.ι Φ Ψ)

/-- Shorthand for the index type of the canonical diagram to write any
equifier as a κ-filtered colimit of κ-presentable inserters. -/
abbrev Δ (E : Equifier Φ Ψ) := CostructuredArrow ((O₁ κ Φ Ψ).ι) E

instance {E : Equifier Φ Ψ} (x : Δ κ E) : IsCardinalPresentable x.left.obj.obj κ :=
  x.left.property

instance {E : Equifier Φ Ψ} (x : Δ κ E) :
    IsCardinalPresentable ((O₁ κ Φ Ψ).ι.obj x.left).obj κ :=
  x.left.property

open PartialChainUpTo Order Limits in
lemma factors (Λ : Type*)
    [LinearOrder Λ] [OrderBot Λ] [SuccOrder Λ] [NoMaxOrder Λ] [WellFoundedLT Λ]
    (hΛ : HasCardinalLT Λ κ)
    [IsCardinalAccessibleCategory K κ] [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ]
    [F.PreservesCardinalPresentable κ] [HasColimitsOfShape Λ K] [PreservesColimitsOfShape Λ F]
    {E : Equifier Φ Ψ} {S : K} [IsCardinalPresentable S κ] (f : S ⟶ E.obj) :
    ∃ (U : Δ κ E) (g : S ⟶ U.left.obj.obj), (g ≫ U.hom.hom = f) := by
  let O₀ := isCardinalPresentable K κ -- shorthand to make things a bit more compact.
  -- First, we summon a diagram to write T as a κ-filtered colimits of κ-filtered objects.
  have : IsFiltered (CostructuredArrow O₀.ι E.obj) := isFiltered_of_isCardinalFiltered _ κ
  let hcolimT := O₀.ι.denseAt E.obj -- E.obj ≅ colim_ξ T_ξ
  -- Pick a first factorization of `S ⟶ E.obj` through some `T_ξ₀`.
  obtain ⟨ξ₀, u, v⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimT f
  -- Now, we build a chain of morphisms from T_ξ₀: at the colimit it will give an equifier
  dsimp at u v
  simp only [Category.id_comp] at v
  -- Now, we construct a chain by iterating.
  -- This requires some amount of setup: first the induction data
  let data : CategoryTheory.Functor.WellOrderInductionData (functor κ Λ E) :=
    Functor.WellOrderInductionData.ofExists
      (fun i hi ↦ surjective_trunc κ Λ E i)
      (fun j hj S ↦ ISeg.exists_extension E j hj S hΛ)
  -- The initial segment from which we build the chain, corresponding to ξ₀ already constructed.
  let D₀ : PartialChainUpTo κ Λ E ⊥ := .mkBot Λ ξ₀
  -- The extension
  let Se : Seg κ Λ E := (data.surjective D₀).choose
  -- Now some shorthands around Se with pinned types to ease automation
  let ξ : Λ ⥤ CostructuredArrow O₀.ι E.obj := Se.functor
  have e₀ : ξ.obj ⊥ = ξ₀ :=
    congr($((data.surjective D₀).choose_spec).ξ.obj (iic% ⊥ ⊥)).trans <| mkBot_bot_eq ..
  -- The colimit of the constructed chain becomes an equifier
  have : O₀.IsClosedUnderColimitsOfShape Λ :=
    have : Small.{w} Λ := hΛ.small
    CategoryTheory.isClosedUnderColimitsOfShape_isCardinalPresentable K (by
      rwa [hasCardinalLT_arrow_iff_of_isThin _ κ (Cardinal.IsRegular.aleph0_le Fact.out)])
  have : HasColimitsOfShape Λ O₀.FullSubcategory := hasColimitsOfShape_of_closedUnderColimits ..
  let U₀ : Equifier Φ Ψ := ⟨(colimit ξ).left.obj, by
    apply (isColimitOfPreserves (CostructuredArrow.proj O₀.ι E.obj ⋙ O₀.ι ⋙ F)
      (colimit.isColimit ξ)).hom_ext
    intro i
    have : Φ.app (ξ.obj i).left.obj ≫ G.map (ξ.map (homOfLE (le_succ i))).left.hom =
        Ψ.app (ξ.obj i).left.obj ≫ G.map (ξ.map (homOfLE (le_succ i))).left.hom :=
      Se.h i (succ i) (lt_succ i)
    simp [← colimit.w ξ (homOfLE (le_succ i)), -colimit.w, reassoc_of% this]⟩
  let U₁ : (O₁ κ Φ Ψ).FullSubcategory :=
    ⟨U₀, by
      simp only [ObjectProperty.prop_inverseImage_iff, ObjectProperty.ι_obj, U₀]
      infer_instance⟩
  let U : Δ κ E := CostructuredArrow.mk (Y := U₁) ⟨(colimit ξ).hom⟩
  refine ⟨U, u ≫ (eqToHom e₀.symm).left.hom ≫ (colimit.ι ξ ⊥).left.hom, ?_⟩
  have := (eqToHom e₀.symm ≫ colimit.ι ξ ⊥).w
  dsimp at this
  simp only [CostructuredArrow.eqToHom_left, ObjectProperty.eqToHom_hom, Category.assoc,
    Category.comp_id] at this
  simp [U, U₁, U₀, this, ← v]

end factors

section

/- In this section, we use the lemma `factors` above to prove that

- the category `Δ κ E` (of equifiers with κ-presentable underlying object mapping to E) is
  κ-filtered.
- The functor `Δ κ E ⥤ CostructuredArrow (isCardinalPresentable K κ) E.obj` is final.

As in the file `Mathlib/CategoryTheory/Inserter/Accessible.lean`, this implies formally that the
category `Equifier Φ Ψ` is κ-accessible, with κ-presentable objects being exactly those such that
the underlying object is κ-presentable in K. -/

open Limits

variable {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular] (Φ Ψ : F ⟶ G) (Λ : Type*)
    [LinearOrder Λ] [OrderBot Λ] [SuccOrder Λ] [NoMaxOrder Λ] [WellFoundedLT Λ]
    (hΛ : HasCardinalLT Λ κ)
    [IsCardinalAccessibleCategory K κ] [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ]
    [F.PreservesCardinalPresentable κ] [HasColimitsOfShape Λ K] [PreservesColimitsOfShape Λ F]

include hΛ in
lemma isCardinalFiltered_Δ (E : Equifier Φ Ψ) :
    IsCardinalFiltered (Δ κ E) κ := by
  rw [isCardinalFiltered_iff']
  -- first, represent the object underlying E as a κ-filtered colimit of κ-presentable objects
  let O₀ := isCardinalPresentable K κ -- shorthand to make the writing more compact
  have : IsFiltered (CostructuredArrow O₀.ι E.obj) := isFiltered_of_isCardinalFiltered _ κ
  let hcolimS := O₀.ι.denseAt E.obj -- E.obj ≅ colim_ξ S_ξ
  refine ⟨fun ι v hι ↦ ?_, fun ι r p f hι hι' ↦ ?_⟩
  · -- There exists an index ξ₀ such that all the v_j factorizes through the index in K
    obtain ⟨ξ₀, t0, hf0⟩ :
        ∃ (ξ₀ : CostructuredArrow O₀.ι E.obj)
          (t : (i : ι) → ((v i).left.obj.obj ⟶ ξ₀.left.obj)),
          (∀ i : ι, t i ≫ ξ₀.hom = (v i).hom.hom) := by
      have b (j : ι) := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimS (v j).hom.hom
      dsimp at b
      simp only [Category.id_comp] at b
      choose s0 f0 hf0 using b
      let ξ₀ := IsCardinalFiltered.max s0 hι
      let t0 (j : ι) : (v j).left.obj.obj ⟶ ξ₀.left.obj :=
       (f0 j) ≫ (IsCardinalFiltered.toMax s0 hι j).left.hom
      exact ⟨IsCardinalFiltered.max s0 hι, fun j ↦
        (f0 j) ≫ (IsCardinalFiltered.toMax s0 hι j).left.hom,
        by simp [hf0, (dsimp% IsCardinalFiltered.toMax s0 hι · |>.w)]⟩
    -- then, use the lemma
    obtain ⟨ξ₁, p, hf1⟩ := factors κ Λ hΛ ξ₀.hom
    refine ⟨ξ₁, fun i ↦ ⟨CostructuredArrow.homMk ⟨⟨t0 i ≫ p⟩⟩ ?_⟩⟩
    ext
    simp [hf1, hf0]
  · -- first, we pick an index ξ₀ that coequalizes all the components of f
    obtain ⟨ξ₀, u, hu, hv⟩ :
        ∃ (ξ₀ : CostructuredArrow O₀.ι E.obj)
          (u : p.left.obj.obj ⟶ ξ₀.left.obj),
          u ≫ ξ₀.hom = (CostructuredArrow.hom p).hom ∧
          ∀ (i₀ i₁ : ι), (f i₀).left.hom.hom ≫ u = (f i₁).left.hom.hom ≫ u := by
      obtain ⟨ξ₀, u, hu⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimS p.hom.hom
      dsimp at u hu
      simp only [Category.id_comp] at hu
      have : IsCardinalPresentable r.left.obj.obj κ := by
        have := r.left.property
        simp only [ObjectProperty.prop_inverseImage_iff] at this
        infer_instance
      obtain ⟨ξ₀', v, hv⟩ :=
        IsCardinalPresentable.exists_eq_of_isColimit'_of_hasCardinalLT κ hcolimS hι
          (fun i ↦ (f i).left.hom.hom ≫ u) (fun i i' ↦ by
            simp [hu, dsimp% congr($((f i').w).hom), dsimp% congr($((f i).w).hom)])
      exact ⟨ξ₀', u ≫ v.left.hom, by simp [dsimp% v.w, hu], by simpa using hv⟩
    obtain ⟨ξ₀', v', hv'⟩ := factors κ Λ hΛ ξ₀.hom
    simp only [ObjectProperty.ι_obj] at v' hv'
    let pt : ι := hι'.some -- we need some arbitrary element of ι
    refine ⟨ξ₀', CostructuredArrow.homMk ⟨⟨u ≫ v'⟩⟩ (by cat_disch),
      CostructuredArrow.homMk ⟨⟨(f pt).left.hom.hom ≫ u ≫ v'⟩⟩ (by
        ext; simp [hv', hu, dsimp% congr($((f pt).w).hom)]), ?_⟩
    intro i
    ext
    simp [reassoc_of% hv i pt]

variable {Φ Ψ}

/-- A shorthand for the forgetful functor from Δ κ E to κ-presentable objects mapping to E.obj.
We will show below that this functor is final, which will prove that every inserter
is a filtered colimit of κ-presentable inserters. -/
@[implicit_reducible, simps!]
def U (E : Equifier Φ Ψ) :
    Δ κ E ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj :=
  CostructuredArrow.map₂
    (F := ObjectProperty.lift _ ((O₁ _ _ _).ι ⋙ Equifier.ι _ _)
      (by intro x; simpa [O₁] using x.property))
    (G := Equifier.ι _ _)
    { app X := 𝟙 _ }
    (𝟙 _)

include hΛ in
lemma final.nonempty_structured_arrow (E : Equifier Φ Ψ)
    (p : CostructuredArrow (isCardinalPresentable K κ).ι E.obj) :
    Nonempty (StructuredArrow p (U κ E)) := by
  -- first, represent the object underlying E as a κ-filtered colimit of κ-presentable objects
  let O₀ := isCardinalPresentable K κ -- shorthand to make the writing more compact
  have : IsFiltered (CostructuredArrow O₀.ι E.obj) := isFiltered_of_isCardinalFiltered _ κ
  let hcolimT := O₀.ι.denseAt E.obj -- E.obj ≅ colim_ξ S_ξ
  obtain ⟨ξ₀, u, hu⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimT p.hom
  dsimp at u hu
  simp only [Category.id_comp] at hu
  obtain ⟨ξ₀', v', hv'⟩ := factors κ Λ hΛ ξ₀.hom
  exact ⟨StructuredArrow.mk <| CostructuredArrow.homMk ⟨u ≫ v'⟩ (by simp [hv', hu])⟩

include hΛ in
lemma final (E : Equifier Φ Ψ) :
    (U κ E).Final := by
  constructor
  intro p
  have : Nonempty (StructuredArrow p (U κ E)) := final.nonempty_structured_arrow κ Λ hΛ E p
  apply CategoryTheory.zigzag_isConnected
  -- by
  intro j₁ j₂
  suffices H :
      ∃ (u : Δ κ E) (f1 : j₁.right ⟶ u) (f2 : j₂.right ⟶ u),
       f1.left.hom.hom ≫ u.hom.hom = j₁.right.hom.hom ∧
       f2.left.hom.hom ≫ u.hom.hom = j₂.right.hom.hom ∧
       j₁.hom.left.hom ≫ f1.left.hom.hom = j₂.hom.left.hom ≫ f2.left.hom.hom by
    obtain ⟨u, f1, f2, h1, h2, h3⟩ := H
    let u' : StructuredArrow p (U κ E) := StructuredArrow.mk (T := U κ E)
      (CostructuredArrow.homMk ⟨j₁.hom.left.hom ≫ f1.left.hom.hom⟩ (by
        simp only [ObjectProperty.ι_obj, U_obj_left_obj, ObjectProperty.ι_map, U_obj_hom,
          Category.assoc]
        have := congr($(f1.w).hom)
        have := j₁.hom.w
        simp_all))
    calc
      Zigzag j₁ u' := .of_zag <| .of_hom <| StructuredArrow.homMk f1
      Zigzag u' j₂ := .of_zag <| .of_inv <| StructuredArrow.homMk f2
  obtain ⟨ξ₀, f₀, f₁, hf₀, hf₁, hsq⟩ :
      ∃ (ξ₀ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
        (f₀ : j₁.right.left.obj.obj ⟶ ξ₀.left.obj)
        (f₁ : j₂.right.left.obj.obj ⟶ ξ₀.left.obj),
        f₀ ≫ ξ₀.hom = j₁.right.hom.hom ∧ f₁ ≫ ξ₀.hom = j₂.right.hom.hom ∧
        j₁.hom.left.hom ≫ f₀ = j₂.hom.left.hom ≫ f₁ := by
    have : IsFiltered (CostructuredArrow (isCardinalPresentable K κ).ι E.obj) :=
      isFiltered_of_isCardinalFiltered _ κ
    let hcolimT := (isCardinalPresentable K κ).ι.denseAt E.obj -- E.obj ≅ colim_ξ T_ξ
    obtain ⟨ξ₀₀, u₀₀, v₀₀, hu₀₀⟩ :=
      IsCardinalPresentable.exists_hom_above_of_isColimit κ hcolimT j₁.right.hom.hom p
    obtain ⟨ξ₀₁, u₀₁, v₀₁, hu₀₁⟩ :=
      IsCardinalPresentable.exists_hom_above_of_isColimit κ hcolimT j₂.right.hom.hom p
    dsimp at u₀₀ v₀₀ hu₀₀ u₀₁ v₀₁ hu₀₁
    simp only [Category.id_comp] at hu₀₀ hu₀₁
    obtain ⟨ξ₀, u, v, h₁, h₂⟩ := IsFiltered.bowtie u₀₀ u₀₁
      (j₁.hom ≫ CostructuredArrow.homMk ⟨v₀₀⟩) (j₂.hom ≫ CostructuredArrow.homMk ⟨v₀₁⟩)
    exact ⟨ξ₀, v₀₀ ≫ u.left.hom, v₀₁ ≫ v.left.hom,
      by simp [hu₀₀, dsimp% u.w], by simp [hu₀₁, dsimp% v.w], by simpa using congr($(h₂).left.hom)⟩
  obtain ⟨ξ₀', u, hu⟩ := factors κ Λ hΛ ξ₀.hom
  exact ⟨ξ₀', CostructuredArrow.homMk ⟨⟨f₀ ≫ u⟩⟩, CostructuredArrow.homMk ⟨⟨f₁ ≫ u⟩⟩, by
    simp [hu, hf₀, hf₁, reassoc_of% hsq]⟩

end

section
open Limits

variable {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular] (Φ Ψ : F ⟶ G) (Λ : Type*)
    [LinearOrder Λ] [OrderBot Λ] [SuccOrder Λ] [NoMaxOrder Λ] [WellFoundedLT Λ]
    (hΛ : HasCardinalLT Λ κ)
    [IsCardinalAccessibleCategory K κ] [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ]
    [F.PreservesCardinalPresentable κ] [HasColimitsOfShape Λ K] [PreservesColimitsOfShape Λ F]

open Equifier in
instance :
    ObjectProperty.EssentiallySmall.{w} (O₁ κ Φ Ψ) := by
  dsimp [O₁]
  have : ObjectProperty.EssentiallySmall.{w} (isCardinalPresentable K κ ⊓ (equifier Φ Ψ)) :=
    .of_le inf_le_left
  have :
      (isCardinalPresentable K κ ⊓ (equifier Φ Ψ)).FullSubcategory ≌ (O₁ κ Φ Ψ).FullSubcategory :=
    ObjectProperty.infEquivalence ..
  exact (ObjectProperty.exists_equivalence_iff _).mp ⟨_, _,
    ⟨this.symm.trans
      (equivSmallModel.{w} ((isCardinalPresentable K κ ⊓ (equifier Φ Ψ)).FullSubcategory))⟩⟩

end

end Accessible

section

variable {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular] (Φ Ψ : F ⟶ G) (Λ : Type*)
    [LinearOrder Λ] [Nonempty Λ] [SuccOrder Λ] [NoMaxOrder Λ] [WellFoundedLT Λ]
    (hΛ : HasCardinalLT Λ κ)
    [IsCardinalAccessibleCategory K κ] [IsCardinalAccessibleCategory L κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ]
    [F.PreservesCardinalPresentable κ]
    [Limits.HasColimitsOfShape Λ K] [Limits.PreservesColimitsOfShape Λ F]

open Limits Accessible

include Λ hΛ in
public theorem isCardinalFilteredGenerator_inverseImage_isCardinalPresentable :
    ((isCardinalPresentable K κ).inverseImage
      (Equifier.ι Φ Ψ)).IsCardinalFilteredGenerator κ := by
  have (X : Equifier Φ Ψ) : IsCardinalFiltered (CostructuredArrow (O₁ κ Φ Ψ).ι X) κ := by
    have : OrderBot Λ := WellFoundedLT.toOrderBot Λ
    exact isCardinalFiltered_Δ κ Φ Ψ Λ hΛ ..
  apply +allowSynthFailures IsCardinalFilteredGenerator.of_isDense_ι
  · constructor
    intro E
    /- Using that the functor `U : Δ κ E ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj`
    is final, any equifier is the κ-filtered colimit of its projection from Δ κ E:
    This can be checked after postcomposition with `ι F G` and extension through `U`,
    and the cocone obtained this way identifies to the canonical cocone for E.obj,
    which is a colimit diagram as `K` is κ-accessible. -/
    dsimp [Functor.isDenseAt]
    -- The canonical cocone making E.hom a κ-filtered colimit of κ-presentable objects
    let hcolimT := (isCardinalPresentable K κ).ι.denseAt E.obj -- E.obj ≅ colim_ξ S_ξ
    have : OrderBot Λ := WellFoundedLT.toOrderBot Λ
    have : (U κ E).Final := final κ Λ hΛ E
    let t1 := (Functor.Final.isColimitWhiskerEquiv (U κ E) _).symm hcolimT
    apply Limits.ReflectsColimit.reflects (F := Equifier.ι Φ Ψ)
      (K := CostructuredArrow.proj (O₁ κ Φ Ψ).ι E ⋙ (O₁ κ Φ Ψ).ι)
    let e₁ :
      (U κ E ⋙ CostructuredArrow.proj (isCardinalPresentable K κ).ι E.obj ⋙
        (isCardinalPresentable K κ).ι) ≅
      (CostructuredArrow.proj (O₁ κ Φ Ψ).ι E ⋙ (O₁ κ Φ Ψ).ι) ⋙ ι _ _ := .refl _
    exact Limits.IsColimit.equivOfNatIsoOfIso e₁
      (Limits.Cocone.whisker (U κ E) _)
      ((ι _ _).mapCocone
        ((Functor.LeftExtension.mk (𝟭 _) (O₁ κ Φ Ψ).ι.rightUnitor.inv).coconeAt E))
      (Limits.Cocone.ext (.refl _) (by intros; simp [e₁])) t1
  · intro x hx
    simp only [ObjectProperty.prop_inverseImage_iff, ObjectProperty.ι_obj] at hx
    infer_instance

include Λ hΛ in
/-- Let `Λ < κ` be a pair of infinite cardinals such that `κ` is regular. Assume that
- `K` and `L` are `κ`-accessible categories with colimits of `Λ`-chains.
- `F G : C ⥤ D` are `κ`-accessible functors preserving colimits of `Λ`-chains
- `F` preserves `κ`-presentable objects.

Then the category `Inserter F G` is `κ`-accessible.

This theorem appears as Theorem 4.1 in [positselski2014].

Note that if `K` and `L` are `κ`-accessible, and `F`, `G` are `κ`-accessible with `F` preserving
`κ`-presentable objects then since `κ` is sharply less than `κ⁺`, one can show that the pair
`κ < κ⁺` satisfies the conditions above, and hence `Inserter F G` is `κ⁺`-accessible in
this situation. -/
public theorem isCardinalAccessibleCategory :
    IsCardinalAccessibleCategory (Equifier Φ Ψ) κ where
  exists_generator := ⟨O₁ κ Φ Ψ, inferInstance,
      isCardinalFilteredGenerator_inverseImage_isCardinalPresentable κ Φ Ψ Λ hΛ⟩
  hasColimitsOfShape J _ _ := by
    have : Limits.PreservesColimitsOfShape J F :=
      Functor.IsCardinalAccessible.preservesColimitOfShape κ J
    have : Limits.HasColimitsOfShape J K :=
      HasCardinalFilteredColimits.hasColimitsOfShape _ κ _
    infer_instance

include Λ hΛ in
public lemma isCardinalPresentable_eq :
    isCardinalPresentable (Equifier Φ Ψ) κ =
      (isCardinalPresentable K κ).inverseImage (Equifier.ι Φ Ψ) := by
  have := isCardinalFilteredGenerator_inverseImage_isCardinalPresentable κ Φ Ψ Λ hΛ
  rw [this.isPresentable_eq_retractClosure]
  apply ObjectProperty.retractClosure_eq_self

omit [IsCardinalAccessibleCategory L κ]
  [G.IsCardinalAccessible κ]
  [F.PreservesCardinalPresentable κ] in
public instance isCardinalAccessible_ι :
    (ι Φ Ψ).IsCardinalAccessible κ := by
  constructor
  intro J _ _
  have : Limits.PreservesColimitsOfShape J F :=
    Functor.IsCardinalAccessible.preservesColimitOfShape κ J
  have : Limits.HasColimitsOfShape J K :=
    HasCardinalFilteredColimits.hasColimitsOfShape _ κ _
  infer_instance

end

public instance {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (Φ Ψ : F ⟶ G)
    [IsAccessibleCategory.{w} K] [IsAccessibleCategory.{w} L]
    [F.IsAccessible.{w}] [G.IsAccessible.{w}] : IsAccessibleCategory.{w} (Equifier Φ Ψ) := by
  obtain ⟨κ, _, _, _, _, _, _, _, _, _⟩ := IsCardinalAccessibleCategory.uniformization_pair F G
  -- To apply the theorem `isCardinalAccessibleCategory`, `κ` must be at least uncountable,
  -- So we fix this by picking an arbitrary cardinal κ' such that κ is sharply less that κ
  obtain ⟨κ', _, h⟩ := Cardinal.SharplyLT.exists_single κ
  have : IsCardinalAccessibleCategory K κ' := h.isCardinalAccessibleCategory K
  have : IsCardinalAccessibleCategory L κ' := h.isCardinalAccessibleCategory L
  have : F.IsCardinalAccessible κ' := Functor.isCardinalAccessible_of_le _ h.le
  have : G.IsCardinalAccessible κ' := Functor.isCardinalAccessible_of_le _ h.le
  have : F.PreservesCardinalPresentable κ' := F.preservesCardinalPresentable_of_sharplyLT h
  have : G.PreservesCardinalPresentable κ' := G.preservesCardinalPresentable_of_sharplyLT h
  have : Nonempty κ.ord.ToType := Cardinal.nonempty_ord_toType (Cardinal.IsRegular.ne_zero Fact.out)
  have : NoMaxOrder κ.ord.ToType := Cardinal.noMaxOrder (Cardinal.IsRegular.aleph0_le Fact.out)
  have hCard: HasCardinalLT κ.ord.ToType κ' := by
    rw [hasCardinalLT_iff_cardinal_mk_lt]
    simpa using h.lt
  have : Limits.HasColimitsOfShape κ.ord.ToType K :=
    HasCardinalFilteredColimits.hasColimitsOfShape _ κ _
  have : Limits.PreservesColimitsOfShape κ.ord.ToType F :=
    Functor.IsCardinalAccessible.preservesColimitOfShape κ _
  exact ⟨κ', inferInstance, isCardinalAccessibleCategory κ' _ _ κ.ord.ToType hCard⟩

public instance {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (Φ Ψ : F ⟶ G)
    [IsAccessibleCategory.{w} K] [IsAccessibleCategory.{w} L]
    [F.IsAccessible.{w}] [G.IsAccessible.{w}] : (Equifier.ι Φ Ψ).IsAccessible.{w} := by
  obtain ⟨κ, _, _, _, _, _, _, _, _, _⟩ := IsCardinalAccessibleCategory.uniformization_pair F G
  exact ⟨κ, inferInstance, inferInstance⟩

end CategoryTheory.Equifier
