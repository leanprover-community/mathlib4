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

Compare to the similar strategy used in `CategoryTheory/Inserter/Accessible`: the
case of the equifiers is much easier as we do not have to bookkeep an extra morphism.

This is Lemma 3.2 in [positselski2014].

This lemma requires inductively building a chain of indices satisfying some property
in a diagram used to write `E.obj` as a κ-filtered colimit of κ-presentable object.

Setting up the induction is the main technical content of this section.
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
  h (j k : Λ) (hjk : j ≤ k) (hk : k < i) :
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

namespace extend

end extend


end PartialChainUpTo

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
  sorry

end factors

end Accessible

end CategoryTheory.Equifier
