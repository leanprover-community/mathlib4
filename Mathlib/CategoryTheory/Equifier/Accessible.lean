/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Equifier.Basic
public import Mathlib.CategoryTheory.Presentable.PreservesCardinalPresentable
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable

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
    (Λ : Type w) [Nonempty Λ] [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
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
structure PartialChainUpTo (Λ : Type w) [Preorder Λ] [SuccOrder Λ]
    (E : Equifier Φ Ψ) (i : Λ) where
  /-- Corresponds to all the previously constructed ξᵢ's -/
  ξ : Set.Iic i ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj
  h (j k : Λ) (hjk : j < k) (hk : k ≤ i) :
    Φ.app (ξ.obj (iic% j i)).left.obj ≫
      G.map (ξ.map (homOfLE (by valid) : iic% j i ⟶ iic% k i)).left.hom =
    Ψ.app (ξ.obj (iic% j i)).left.obj ≫
      G.map (ξ.map (homOfLE (by valid) : iic% j i ⟶ iic% k i)).left.hom

namespace PartialChainUpTo
variable (Λ : Type w) [LinearOrder Λ] [SuccOrder Λ]

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
    rw [hasCardinalLT_arrow_iff_of_isThin, hasCardinalLT_iff_cardinal_mk_lt]
    · grw [Cardinal.mk_le_of_injective (Subtype.val_injective),
        ← hasCardinalLT_iff_cardinal_mk_lt]
      assumption
    · exact Cardinal.IsRegular.aleph0_le <| Fact.out

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

lemma mkSuccBot_bot_eq [OrderBot Λ] {E : Equifier Φ Ψ}
    (ξ₀ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj) :
    (mkBot Λ ξ₀).ξ.obj (iic% ⊥ ⊥) = ξ₀ :=
  rfl

end constructor

end PartialChainUpTo

open PartialChainUpTo Order Limits in
lemma factors [IsCardinalAccessibleCategory K κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ]
    [F.PreservesCardinalPresentable κ]
    {E : Equifier Φ Ψ} {S : K} [IsCardinalPresentable S κ] (f : S ⟶ E.obj) :
    ∃ (U : Equifier Φ Ψ) (g : S ⟶ U.obj) (h : U ⟶ E),
      IsCardinalPresentable U.obj κ ∧ (g ≫ h.hom = f) := by
  let O₀ := isCardinalPresentable K κ -- shorthand to make things a bit more compact.
  -- local grind helper : having this in context helps
  have _ {x y : CostructuredArrow O₀.ι E.obj} (f : x ⟶ y) :
      f.left.hom ≫ y.hom = x.hom := by
    simpa using f.w
  -- First, we summon a diagram to write T as a κ-filtered colimits of κ-filtered objects.
  have : IsFiltered (CostructuredArrow O₀.ι E.obj) := isFiltered_of_isCardinalFiltered _ κ
  let hcolimT := O₀.ι.denseAt E.obj -- E.obj ≅ colim_ξ T_ξ
  have (X : K) : Limits.PreservesColimitsOfShape (CostructuredArrow O₀.ι X) G :=
    G.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _
  have (X : K) : Limits.PreservesColimitsOfShape (CostructuredArrow O₀.ι X) F :=
    F.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _
  let hcolimGT := Limits.isColimitOfPreserves G (O₀.ι.denseAt E.obj) -- G(E.obj) ≅ colim_ξ G(T_ξ)
  -- Pick a first factorization of `S ⟶ E.obj` through some `T_ξ₀`.
  obtain ⟨ξ₀, u, v⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimT f
  -- Now, we build a chain of morphisms.
  dsimp at u v
  simp only [Category.id_comp] at v
  -- Now, we construct a chain by iterating.
  -- This requires a fair amount of setup: first the induction data
  let data : CategoryTheory.Functor.WellOrderInductionData (functor κ Λ E) :=
    Functor.WellOrderInductionData.ofExists
      (fun i hi ↦ surjective_trunc κ Λ hΛ E i)
      (fun j hj S ↦ ISeg.exists_extension E j hj S hΛ)
  -- The initial segment from which we build the chain, corresponding to ξ₀ ⟶ ξ₁ already built.
  let D₀ : PartialChainUpTo κ Λ E (succ ⊥) := .mkSuccBot Λ ξ₀ ξ₁ u₀ ψ₀ (by
    have he2 : ψ₀ ≫ G.map ξ₁.hom = F.map u₀.left.hom ≫ F.map ξ₁.hom ≫ E.hom := by grind
    rwa [← dsimp% CostructuredArrow.w u₀, Functor.map_comp, Category.assoc, Eq.comm])
  -- The extension
  let S : Seg κ Λ E := (data.surjective' (succ ⊥) (not_isSuccLimit_succ ⊥) D₀).choose
  have S_val : S.val (Opposite.op <| succ ⊥) = D₀ :=
    (data.surjective' (succ ⊥) (not_isSuccLimit_succ ⊥) D₀).choose_spec
  -- Now some shorthands around S_val with pinned types to ease automation
  let ξ : Λ ⥤ CostructuredArrow O₀.ι E.obj := S.functor
  have e₀ : ξ.obj ⊥ = ξ₀ :=
    (S.ξ_obj_eq ⊥ (succ ⊥) (le_succ _)).trans <|
      congr($(S_val).ξ.obj ⟨⊥, le_succ ⊥⟩).trans <| mkSuccBot_bot_eq ..
  have e₁ : ξ.obj (succ ⊥) = ξ₁ :=
    (S.ξ_obj_eq (succ ⊥) (succ ⊥) le_rfl).trans <|
      congr($(S_val).ξ.obj ⟨succ ⊥, le_rfl⟩).trans <| mkSuccBot_succ_bot_eq ..
  have e₂ : ξ.map (homOfLE <| le_succ ⊥) = eqToHom e₀ ≫ u₀ ≫ eqToHom e₁.symm := by
    dsimp [ξ, Seg.functor]
    rw [Functor.congr_hom (congr($(S_val).ξ)), mkSuccBot_map_homOfLE_eq]
    simp [Seg.ξObjIso, Seg.ξ]
  let Θ :
      ξ ⋙ CostructuredArrow.proj (isCardinalPresentable K κ).ι E.obj ⋙
          (isCardinalPresentable K κ).ι ⋙ F ⟶
        _ ⋙ ξ ⋙ CostructuredArrow.proj (isCardinalPresentable K κ).ι E.obj ⋙
          (isCardinalPresentable K κ).ι ⋙ G :=
    S.ψNatTrans

  sorry

end factors

end Accessible

end CategoryTheory.Equifier
