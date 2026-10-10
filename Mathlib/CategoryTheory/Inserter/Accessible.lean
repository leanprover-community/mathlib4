/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Inserter.Basic
public import Mathlib.CategoryTheory.Presentable.PreservesCardinalPresentable
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable

import Mathlib.CategoryTheory.Inserter.Limits
import Mathlib.CategoryTheory.Inserter.LocallySmall
import Mathlib.CategoryTheory.Presentable.Dense
import Mathlib.CategoryTheory.Presentable.StrongGenerator
import Mathlib.CategoryTheory.Presentable.Uniformization
import Mathlib.Order.Interval.Set.InitialSeg
import Mathlib.CategoryTheory.SmallObject.Iteration.ExtendToSucc
import Mathlib.CategoryTheory.SmallObject.Iteration.FunctorOfCocone
import Mathlib.CategoryTheory.SmallObject.WellOrderInductionData

/-! # Inserter categories are accessible

In this file, we show that categories of inserters are accessible in good situations.

More precisely, given `F G : K ⥤ L` two `κ`-accessible functors between two κ-accessible categories,
such that `F` preserves `κ`-presentable objects. Assuming there exists an ordinal `Λ < κ` such that
`K` and `L` admits Λ-indexed colimits and such that `F` and `G` preserve `Λ`-indexed colimits,
we show that the category `Inserter F G` remains κ-accessible, and that its κ-presentable objects
are exactly objects `E : Inserter F G` such that `E.obj` is a κ-presentable object of `K`.

This result appears as Theorem 4.1 in [positselski2014]. We follow the proof from this reference.

Using the uniformization theorem, this implies that if `F G : K ⥤ L` are accessible functors between
accessible categories, then `Inserter F G` is an accessible category.

Notice that in the case `K = L`, `G = 𝟭 K`, this shows that the category of algebras for the
endofunctor `F` is accessible. This result can be combined with (TODO) result that categories
of equifiers are accessible to show that the category of algebras for an accessible monad
is also accessible.

-/

namespace CategoryTheory.Inserter

universe w

namespace Accessible
-- Recall everything in the section below is private.

/- The setup for accessibility of inserter categories, from Positselski’s paper:
`F G : K ⥤ L` are a parallel pair of κ-accessible functors between κ-accessible categories
where `F` in addition preserves κ-presentable objects. A given infinite ordinal Λ < κ such
that both `K` and `L` have colimits of Λ-chains is given, and we assume that `F` and `G` preserve
these colimits.

Throughout this file, this setup is realized as
```
variable {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalAccessibleCategory K κ] [IsCardinalAccessibleCategory L κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ]
    (Λ : Type*) [Nonempty Λ] [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ)
    [Limits.HasColimitsOfShape Λ K] [Limits.HasColimitsOfShape Λ L]
    [Limits.PreservesColimitsOfShape Λ F] [Limits.PreservesColimitsOfShape Λ G]
```
-/

/-- A small helper that powers up some `simp` and `grind` calls troughout the file -/
@[simp, grind =]
private lemma helper {K : Type*} [Category* K] (κ : Cardinal.{w}) [Fact κ.IsRegular] {X : K}
    {x y : CostructuredArrow (isCardinalPresentable K κ).ι X} (f : x ⟶ y) :
    f.left.hom ≫ y.hom = x.hom := by
  simpa using f.w

variable {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular]

public instance (X : Inserter F G)
    [IsCardinalPresentable X.obj κ]
    [IsCardinalAccessibleCategory K κ] [IsCardinalAccessibleCategory L κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ] :
    IsCardinalPresentable X κ := by
  have : IsCardinalPresentable (proj F G |>.obj X) κ := by assumption
  apply IsCardinalPresentable.mk
  intro I _ _ B b hb
  have : Limits.HasColimitsOfShape I K := HasCardinalFilteredColimits.hasColimitsOfShape _ κ I
  have : Limits.HasColimitsOfShape I L := HasCardinalFilteredColimits.hasColimitsOfShape _ κ I
  have : Limits.PreservesColimitsOfShape I F :=
    Functor.IsCardinalAccessible.preservesColimitOfShape κ I
  have : Limits.PreservesColimitsOfShape I G :=
    Functor.IsCardinalAccessible.preservesColimitOfShape κ I
  let hcolimG := Limits.isColimitOfPreserves (proj F G ⋙ G) hb
  let hcolim := Limits.isColimitOfPreserves (proj F G) hb
  refine ⟨fun f ↦ ?_, fun i f₁ f₂ h ↦ ?_⟩
  · obtain ⟨i, f', hf'⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolim f.hom
    dsimp at f' hf'
    obtain ⟨j, u, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolimG
      (f₁ := F.map f' ≫ (B.obj i).hom) (f₂ := X.hom ≫ G.map f') (by dsimp; grind)
    refine ⟨j, ⟨f' ≫ (B.map u).hom, by grind⟩, ?_⟩
    · ext
      have := congr($(b.ι.naturality u).hom)
      dsimp at this ⊢
      grind
  · obtain ⟨j, u, hu⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolim
      (f₁ := f₁.hom) (f₂ := f₂.hom) congr($(h).hom)
    exact ⟨j, u, by grind⟩

variable (Λ : Type*)

/-
Below, we prove one of the main lemma to prove the main theorem:
this is Lemma 4.5 in [positselski2014].

The lemma says that given a diagram,
```
     F(u)      F(v)
F(S) --> F(T) ---> F(K)
 |                  | Φ
 v                  v
G(T) ------------> G(K)
        G(v)
```

where u : S → T and v : T ⟶ K are maps of κ-presentable objects, one can find a factorization

```
F(S) --> F(T) ---> F(U) --> F(K)
 |          F(v')   | σ      | Φ
 v                  v        v
G(T) ------------> G(U) --> F(K)
         G(v')
```

The main technical ingredient is that if one uses κ-presentability naively, one
only produces a diagram of shape

```
F(S) --> F(T) ---> F(ξ₀) --> F(K)
 |          F(v')   | ψ₀       | Φ
 v                  v          v
G(T) ------------> G(ξ₁) --> F(K)
```

One must iterate the construction of such diagrams to construct a chain `U₀ ⟶ U₁ ⟶ …` by transfinite
induction, equipped with structure maps `ψᵢ : F(ξᵢ) ⟶ G(ξᵢ₊₁)`.
Once the chain becomes long enough, one can take its colimit to stabilize those maps:
this is the relevance of the ordinal Λ that appears in the hypothesis of the main theorem.

Setting up and carrying out this transfinite induction occupies most of the material below,
the strategy is to encode the partial stages of the induction as a presheaf of type
(`PartialChainUpTo.functor` below) and to record the induction
steps as a `Functor.WellOrderInductionData`, which will let us extract a section
of the presheaf from which we can extract the desired chain.
-/

/-- The structure of a partial induction for constructing the chain as in
Lemma 4.5 of [positselski2014].

To realize the induction, we transform `j ↦ PartialChainUpTo … j` into a
presheaf on `j` so that we can use `Functor.WellOrderInductionData`.
From a section of the presheaf, we can extract the chain out of `Λ` that we are looking for. -/
@[ext]
structure PartialChainUpTo [Preorder Λ] [SuccOrder Λ]
    (E : Inserter F G) (i : Λ) where
  /-- Corresponds to all the previously constructed ξᵢ's -/
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

namespace PartialChainUpTo

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

variable [LinearOrder Λ] [SuccOrder Λ]

lemma eqToHom_ext {E : Inserter F G} {i : Λ} {b b' : PartialChainUpTo κ Λ E i}
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

lemma congr_ψ {E : Inserter F G} {i : Λ} {b b' : PartialChainUpTo κ Λ E i}
    (h : b = b') (j k : Λ) (hjk : j < k) (hki : k ≤ i) :
    b.ψ j k hjk hki = F.map (eqToHom congr((($h).ξ.obj _).left.obj)) ≫ b'.ψ j k hjk hki ≫
      G.map (eqToHom congr((($h).ξ.obj _).left.obj).symm) := by
  subst h
  simp

variable {κ} {Λ} in
/-- The main technical induction step from Positselski's 4.5, where we pick an index large enough
to ensure a set of properties. This crucially uses that Λ is small enough. -/
lemma exists_succ_of_hasCardinalLT [IsCardinalAccessibleCategory K κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ]
    [F.PreservesCardinalPresentable κ]
    {E : Inserter F G} {i : Λ}
    (b : PartialChainUpTo κ Λ E i) (hΛ : HasCardinalLT Λ κ) :
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
  obtain ⟨ξ₂₁, v₀, v₁, hv₀⟩ := IsCardinalPresentable.exists_hom_above_of_isColimit κ hcolimGT
    (F.map ξ₁.hom ≫ E.hom) ξ₁
  /- At this point, the squares required to make the (to-be) ψ into a natural transformation are not
  necessarily commutative, so we must pick a new index large enough to coequalize everything. -/
  have Uspec (j : Set.Iio i) :
    ∃ (uji : CostructuredArrow O₀.ι E.obj) (vji : ξ₂₁ ⟶ uji),
      b.ψ j.1 i j.property le_rfl ≫ G.map v₀.left.hom ≫ G.map vji.left.hom =
      F.map (b.ξ.map <| homOfLE <| j.property.le).left.hom ≫ v₁ ≫
        G.map vji.left.hom := by
    obtain ⟨uij, vij, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolimGT
      (b.ψ j.1 i j.property le_rfl ≫ G.map v₀.left.hom)
      (F.map (b.ξ.map <| homOfLE <| j.property.le).left.hom ≫ v₁)
      (by
        dsimp at hv₀
        simp only [Category.id_comp] at hv₀
        simp [hv₀, ← Functor.map_comp, ξ₁, b.sq₁ j j.prop, ← Functor.map_comp_assoc])
    exact ⟨uij, vij, by simpa using h⟩
  choose u ν huν using Uspec
  have h' : HasCardinalLT (Set.Iio i) κ := hΛ.of_injective _ Subtype.val_injective
  obtain ⟨ξ₂, ν₂, μ₀, h₂⟩ := IsCardinalFiltered.wideSpan ν h'
  let ξ₂₀ := IsCardinalFiltered.max (κ := κ) u h'
  -- Now, we check that we have obtained all the conditions we want:
  refine ⟨ξ₂, v₀ ≫ μ₀, v₁ ≫ G.map μ₀.left.hom, ?_, fun j hj ↦ ?_⟩
  · dsimp [ψ, ξ₁] at *
    simp only [Category.id_comp] at hv₀
    simp [← Functor.map_comp, hv₀]
  · have S1 := huν (iio% j i)
    simp [homOfLE_leOfHom, ← h₂ ⟨j, hj⟩, reassoc_of% S1]

lemma sq₂ {i : Λ} {E : Inserter F G} (d : PartialChainUpTo κ Λ E i)
    (j k l m : Λ) (hjk : j < k) (hkm : k ≤ m) (hjl : j ≤ l) (hlm : l < m) (hm : m ≤ i) :
    F.map (d.ξ.map (homOfLE hjl)).left.hom ≫ d.ψ l m hlm (by valid) =
    d.ψ j k hjk (by valid) ≫ G.map (d.ξ.map (homOfLE hkm)).left.hom := by
  rw [← d.t₂, ← d.t₁]
  all_goals grind

/-- Restricts a PartialChainUpTo to a lower index, turning PartialChainUpTo into a presheaf. -/
@[implicit_reducible]
def trunc (E : Inserter F G)
    {i i' : Λ} (hii' : i ≤ i') (d : PartialChainUpTo κ Λ E i') :
    PartialChainUpTo κ Λ E i where
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

/-- Turning `i ↦ PartialChainUpTo κ Λ E i` into a functor. A section of this functor bundles an
extension of the ξ and ψ fields to all indices in Λ. -/
abbrev functor (E : Inserter F G) : Λᵒᵖ ⥤ Type _ where
  obj i := PartialChainUpTo κ Λ E i.unop
  map f := TypeCat.ofHom <| trunc κ Λ E (leOfHom f.unop)

namespace extend

/- This section setups the "successor case" of the transfinite induction extending a partial
chain to a section of `PartialChainUpTo`. -/

open SmallObject.SuccStruct

variable [NoMaxOrder Λ] {κ} {Λ} {E : Inserter F G} {i : Λ} (b : PartialChainUpTo κ Λ E i)
    (ξₙ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν : b.ξ.obj (iic% i i) ⟶ ξₙ)
    (ψ₀ : F.obj (b.ξ.obj <| iic% i i).left.obj ⟶ G.obj ξₙ.left.obj)
    (h₁ : F.map (b.ξ.obj <| iic% i i).hom ≫ E.hom = ψ₀ ≫ G.map ξₙ.hom)
    (h₂ : ∀ (j : Λ) (hj : j < i), F.map (b.ξ.map <| homOfLE hj.le).left.hom ≫ ψ₀ =
      b.ψ j i hj le_rfl ≫ G.map ν.left.hom)

/-- The to-be ξ field of the extension -/
abbrev ξ := extendToSucc (not_isMax _) b.ξ ν

lemma ξ_map_le_succ (j : Λ) (hj : j ≤ i) :
    (ξ b ξₙ ν).map (homOfLE (by valid) : iic% j (succ i) ⟶ iic% (succ i) (succ i)) =
    (extendToSuccObjIso (not_isMax _) b.ξ ν j (by valid)).hom ≫
      b.ξ.map (homOfLE hj) ≫ ν ≫ (extendToSuccObjSuccIso (not_isMax _) b.ξ ν).inv := by
  have := (extendToSucc (not_isMax _) b.ξ ν).map_comp
    (X := iic% j (succ i)) (Y := iic% i (succ i)) (Z := iic% (succ i) (succ i))
    (homOfLE <| by valid) (homOfLE <| by valid)
  dsimp at this
  simp [this, extendToSucc_map_le_succ (not_isMax _) b.ξ ν,
    extendToSuccObjIso_hom_naturality_assoc]

/-- The to-be ψ field of the extension -/
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
  simp (discharger := valid) only [ψ_succ, homOfLE_leOfHom, Category.assoc,
    ← G.map_comp, helper, ← h₁, ← F.map_comp_assoc]

lemma t₁ (j k l : Λ) (hjk : j ≤ k) (hkl : k < l) (hl : l ≤ succ i) :
    extend.ψ b ξₙ ν ψ₀ j l =
    F.map ((extend.ξ b ξₙ ν).map (homOfLE hjk)).left.hom ≫ extend.ψ b ξₙ ν ψ₀ k l := by
  have : l ≤ i ∨ (k ≤ i ∧ l = succ i) := by valid
  obtain hl' | ⟨hki, rfl⟩ := this
  · have := congr(F.map
      $(extendToSuccObjIso_hom_naturality (not_isMax _) b.ξ ν j k (by valid) (by valid)).left.hom)
    simp only [homOfLE_leOfHom, CostructuredArrow.comp_left,
      ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp] at this
    simp (discharger := valid) [ψ_of_le, b.t₁ j k l, reassoc_of% this]
  · simp [ψ_succ b ξₙ ν ψ₀ j, ψ_succ b ξₙ ν ψ₀ k, ← CostructuredArrow.comp_left,
      ← ObjectProperty.FullSubcategory.comp_hom, ← Functor.map_comp_assoc]

include h₂ in
lemma t₂ (j k l : Λ) (hjk : j < k) (hkl : k ≤ l := by valid) (hl : l ≤ succ i := by valid) :
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
    simp (discharger := valid) [ψ_of_le, b.t₂ j k l, this]
  · simp
  · simp (discharger := valid) only [homOfLE_leOfHom, homOfLE_refl,
      Functor.map_id, CostructuredArrow.id_left, ψ_succ, ψ_of_le,
      ObjectProperty.FullSubcategory.id_hom, Category.comp_id, Category.assoc]
    simp_rw [← F.map_comp_assoc, ← ObjectProperty.FullSubcategory.comp_hom,
      ← CostructuredArrow.comp_left, extendToSuccObjIso_hom_naturality]
    simp (discharger := valid) [ξ_map_le_succ, reassoc_of% h₂ j, b.t₂ j k i]

end extend

open SmallObject.SuccStruct in
/-- Extend a `PartialChainUpTo κ Λ E i` to a `PartialChainUpTo κ Λ E (succ i)` from the data of
compatible objects and maps -/
@[implicit_reducible]
noncomputable def extend [NoMaxOrder Λ] {E : Inserter F G} {i : Λ}
    (b : PartialChainUpTo κ Λ E i)
    (ξₙ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν : b.ξ.obj (iic% i i) ⟶ ξₙ)
    (ψ : F.obj (b.ξ.obj <| iic% i i).left.obj ⟶ G.obj ξₙ.left.obj)
    (h₁ : F.map (b.ξ.obj <| iic% i i).hom ≫ E.hom = ψ ≫ G.map ξₙ.hom)
    (h₂ : ∀ (j : Λ) (hj : j < i), F.map (b.ξ.map <| homOfLE hj.le).left.hom ≫ ψ =
      b.ψ j i hj le_rfl ≫ G.map ν.left.hom) :
    PartialChainUpTo κ Λ E (succ i) where
  ξ := extend.ξ b ξₙ ν
  ψ j k hj hk := extend.ψ b ξₙ ν ψ j k hj hk
  sq₁ j hj := extend.sq₁ b ξₙ ν ψ h₁ j hj
  t₁ j k l hjk hkl hl := extend.t₁ b ξₙ ν ψ j k l hjk hkl hl
  t₂ j k l hjk hkl hl := extend.t₂ b ξₙ ν ψ h₂ j k l hjk

lemma trunc_extend [NoMaxOrder Λ]
    {E : Inserter F G} {i : Λ} (b : PartialChainUpTo κ Λ E i)
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
    simp [trunc, extend, SmallObject.SuccStruct.extendToSucc, SmallObject.restrictionLE,
      extend.ψ, hki, SmallObject.SuccStruct.extendToSuccObjIso,
      SmallObject.SuccStruct.extendToSucc.objIso]

theorem surjective_trunc [NoMaxOrder Λ] [IsCardinalAccessibleCategory K κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ]
    [F.PreservesCardinalPresentable κ]
    (hΛ : HasCardinalLT Λ κ) (E : Inserter F G) (i : Λ) :
    Function.Surjective (PartialChainUpTo.trunc κ Λ E (Order.le_succ i)) := by
  intro b
  obtain ⟨ξ₂, ν, ψ, h₁, h₂⟩ := exists_succ_of_hasCardinalLT b hΛ
  use b.extend _ _ ξ₂ ν ψ h₁ fun _ _ ↦ (h₂ ..).symm
  exact trunc_extend ..

section limit

/- This section setups the limit of the transfinite induction extending a partial
chain to a section of `PartialChainUpTo`. -/

/-- A wrapper around restricted sections of `PartialChainUpTo.functor`. -/
@[implicit_reducible]
def ISeg (E : Inserter F G) (j : Λ) : Type _ :=
  ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙
      PartialChainUpTo.functor κ Λ E).sections

namespace ISeg

open Opposite

variable {κ Λ} {E : Inserter F G} {j : Λ}

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

section
open Opposite

variable (S : ISeg κ Λ E j)

/-- Repackage the `ψ` fields of all the `PartialChainUpTo` constituting an `ISeg κ Λ E j`
into a (natural) map defined for all pairs of indices `u < v`. -/
def ψ (u v : Λ) (huv : u < v := by valid) (hv : v < j := by valid) :
    F.obj (S.ξ.obj ⟨u, huv.trans hv⟩).left.obj ⟶ G.obj (S.ξ.obj ⟨v, hv⟩).left.obj :=
  F.map (S.ξObjIso u v huv.le hv).hom.left.hom ≫
    (S.val _).ψ u v huv le_rfl ≫
    G.map (S.ξObjIso v v le_rfl hv).inv.left.hom

lemma sq₁ (k k' : Λ) (hk₁ : k < k' := by valid) (hk₂ : k' < j := by valid) :
    S.ψ k k' ≫ G.map (S.ξ.obj (iio% k' j)).hom = F.map (S.ξ.obj (iio% k j)).hom ≫ E.hom := by
  dsimp [ψ, ξ]
  simp only [Category.assoc, ← G.map_comp, helper]
  have ψ' : (S.val k').ψ k k' hk₁ _ ≫ G.map ((S.val k').ξ.obj (iic% k' k')).hom = _ :=
    dsimp% (S.val k').sq₁ k hk₁
  simp [ψ', ← F.map_comp_assoc]

lemma t₁ (k₁ k₂ k₃ : Λ)
    (h₁₂ : k₁ ≤ k₂ := by valid) (h₂₃ : k₂ < k₃ := by valid) (h₃ : k₃ < j := by valid) :
    S.ψ k₁ k₃ = F.map (S.ξ.map (homOfLE h₁₂)).left.hom ≫ S.ψ k₂ k₃ := by
  have := Functor.congr_hom congr($(S.prop k₂ k₃ h₂₃.le h₃).ξ).symm
    (homOfLE h₁₂ : iic% k₁ k₂ ⟶ iic% k₂ k₂)
  simp (discharger := valid) [ψ, ξ, (S.val k₃).t₁ k₁ k₂ k₃, this, ξObjIso, eqToIso, trunc]

lemma t₂ (k₁ k₂ k₃ : Λ) (h₁₂ : k₁ < k₂) (h₂₃ : k₂ ≤ k₃) (h₃ : k₃ < j) :
    S.ψ k₁ k₃ (by valid) h₃ =
    S.ψ k₁ k₂ h₁₂ (by valid) ≫ G.map (S.ξ.map (homOfLE h₂₃)).left.hom := by
  simp [(S.val k₃).t₂ k₁ k₂ k₃ h₁₂ h₂₃ le_rfl, ψ, ISeg.ξ,
    congr_ψ _ _ congr($(S.prop k₂ k₃ h₂₃ h₃)).symm, trunc, ← Functor.map_comp,
    ← Functor.map_comp_assoc, ξObjIso]

lemma sq₂ (j' k l m : Λ)
    (hjk : j' < k := by valid) (hkm : k ≤ m := by valid)
    (hjl : j' ≤ l := by valid) (hlm : l < m := by valid) (hm : m < j := by valid) :
    F.map (S.ξ.map (homOfLE hjl)).left.hom ≫ S.ψ l m hlm (by valid) =
    S.ψ j' k hjk (by valid) ≫ G.map (S.ξ.map (homOfLE hkm)).left.hom := by
  rwa [← S.t₂, ← @S.t₁]

namespace extend
variable [IsCardinalAccessibleCategory K κ]

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

variable [NoMaxOrder Λ] (hΛ : HasCardinalLT Λ κ) (hj : Order.IsSuccLimit j)

/-- Extend `S.ψ` for a limit element. -/
noncomputable abbrev ψ
    (j' k : Λ) (hj' : j' < k := by valid) (hk : k ≤ j := by valid) :
    F.obj ((ξ S hΛ).obj (iic% j' j)).left.obj ⟶ G.obj ((ξ S hΛ).obj (iic% k j)).left.obj :=
  if hk' : k = j then
    F.map (ξObjIso S hΛ j').hom.left.hom ≫
    S.ψ j' (succ j') (by valid) (by valid) ≫
      G.map ((c S hΛ).ι.app (iio% (succ j') j)).left.hom ≫
      G.map (ξObjTopIso S hΛ).inv.left.hom ≫
        eqToHom (by subst hk'; rfl)
  else
    F.map (ξObjIso S hΛ _).hom.left.hom ≫
    S.ψ j' k hj' (by valid) ≫ G.map (ξObjIso S hΛ _).inv.left.hom

lemma sq₁ (i : Λ) (i' : i < j) :
    ψ S hΛ hj i j i' ≫ G.map ((ξ S hΛ).obj (iic% j j)).hom =
    F.map ((ξ S hΛ).obj (iic% i j)).hom ≫ E.hom := by
  dsimp [ψ, ξ]
  split_ifs with hj
  · simp [← Functor.map_comp, helper, S.sq₁ i (succ i),
      ← Functor.map_comp_assoc]
  · simp at hj

lemma t₁ (i i' i'' : Λ) (hi : i ≤ i') (hi' : i' < i'') (hi'' : i'' ≤ j) :
    extend.ψ S hΛ hj i i'' =
    F.map ((extend.ξ S hΛ).map (homOfLE hi)).left.hom ≫ extend.ψ S hΛ hj i' i'' hi' := by
  dsimp [ψ]
  obtain rfl | hi'' := hi''.eq_or_lt
  · simp only [↓reduceDIte, eqToHom_refl, Category.comp_id, homOfLE_leOfHom]
    simp (discharger := valid) only [homOfLE_leOfHom, ← Functor.map_comp_assoc,
      ← ObjectProperty.FullSubcategory.comp_hom, ← CostructuredArrow.comp_left,
      ξObjIso_hom_naturality]
    simp only [homOfLE_leOfHom, CostructuredArrow.comp_left,
      ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp, Category.assoc]
    obtain rfl | hi' := hi.eq_or_lt
    · simp
    simp [reassoc_of% S.sq₂ i (succ i) i' (succ i'),
      ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
      ← CostructuredArrow.comp_left, (c S hΛ).ι.naturality_assoc]
  · simp only [show ¬(i'' = j) by valid, ↓reduceDIte, homOfLE_leOfHom,
      S.t₁ i i' i'' (by valid) (by valid) (by valid), ← Category.assoc, ← F.map_comp]
    congr 3
    simp_rw [← ObjectProperty.FullSubcategory.comp_hom, ← CostructuredArrow.comp_left,
      ξObjIso_hom_naturality]

lemma t₂ (i i' i'' : Λ) (hi : i < i') (hi' : i' ≤ i'') (hi'' : i'' ≤ j) :
    extend.ψ S hΛ hj i i'' =
    extend.ψ S hΛ hj i i' ≫ G.map ((extend.ξ S hΛ).map (homOfLE hi')).left.hom := by
  dsimp [ψ]
  obtain hi'' | ⟨rfl, hi'⟩ | ⟨rfl, rfl⟩ :
      i'' < j ∨ (i'' = j ∧ i' < i'') ∨ (i' = j ∧ i'' = j) := by valid
  · simp (discharger := valid) [↓reduceDIte, show ¬ (i'' = j) by valid, show ¬ (i' = j) by valid,
      S.t₂ i i' i'',
      ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom, ← CostructuredArrow.comp_left,
      ← ξObjIso_inv_naturality]
  · simp (discharger := valid) [↓reduceDIte, show ¬(i' = i'') by valid,
      S.t₂ i (succ i) i', ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
      ← CostructuredArrow.comp_left, ξ_map_to_top]
  · simp

end extend

end

open Opposite in
/-- Extend an `ISeg κ Λ E j` (for a limit element j) into a `PartialChainUpTo κ Λ E j`. -/
@[implicit_reducible]
noncomputable def extend [NoMaxOrder Λ] [IsCardinalAccessibleCategory K κ]
    {E : Inserter F G} {j : Λ}
    (S : ISeg κ Λ E j) (hΛ : HasCardinalLT Λ κ) (hj : Order.IsSuccLimit j) :
    PartialChainUpTo κ Λ E j where
  ξ := extend.ξ S hΛ
  ψ i k hi hk := extend.ψ S hΛ hj i k hi hk
  sq₁ i i' := extend.sq₁ S hΛ hj i i'
  t₁ i i' i'' hi hi' hi'' := extend.t₁ S hΛ hj i i' i'' hi hi' hi''
  t₂ i i' i'' hi hi' hi'' := extend.t₂ S hΛ hj i i' i'' hi hi' hi''

open Opposite in
lemma exists_extension [NoMaxOrder Λ] [IsCardinalAccessibleCategory K κ]
    (E : Inserter F G) (j : Λ) (hj : Order.IsSuccLimit j)
    (S : ISeg κ Λ E j) (hΛ : HasCardinalLT Λ κ) :
    ∃ (y : (PartialChainUpTo.functor ..).obj (op j)), ∀ (i : Λ) (hi : i < j),
      (PartialChainUpTo.functor κ Λ E).map (homOfLE hi.le).op y = S.val i hi := by
  use S.extend hΛ hj
  intro i hi
  dsimp [extend]
  fapply eqToHom_ext
  · intro j'
    change (extend.ξ _ _).obj (iic% j'.1 _) = _
    rw [extend.ξ_obj_of_lt _ _ j'.1 (by valid), S.ξ_obj_eq j' i]
  · intro j' k hj' hki
    change (extend.ξ S hΛ).map (homOfLE hj' : iic% j' j ⟶ iic% k j) = _
    simp (discharger := valid) [trunc, S.ξ_map_eq j' k i, extend.ξ_map, extend.ξObjIso, ξObjIso]
  · intro j₁ k₁ hjk hki
    have := PartialChainUpTo.congr_ψ κ Λ (S.prop k₁ i hki hi) j₁ k₁ hjk le_rfl
    simp [trunc] at this
    simp [trunc, extend.ψ, show k₁ ≠ j by valid, ↓reduceDIte, extend.ξObjIso, this, ψ, ξObjIso, ξ]

end ISeg

/-- A wrapper around sections of `PartialChainUpTo.functor`. -/
@[implicit_reducible]
def Seg (E : Inserter F G) : Type _ := (PartialChainUpTo.functor κ Λ E).sections

namespace Seg

variable {κ Λ} {E : Inserter F G} {j : Λ}

section

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

/-- Extract the `ψ` fields of all the `PartialChainUpTo` making up a section of
`PartialChainUpTo.functor` into something defined for all indices. -/
def ψ (u v : Λ) (huv : u < v) :
    F.obj (S.functor.obj u).left.obj ⟶ G.obj (S.functor.obj v).left.obj :=
  F.map (S.ξObjIso u v huv.le).hom.left.hom ≫
    (S.val (op _)).ψ u v huv le_rfl ≫
    G.map (S.ξObjIso v v le_rfl).inv.left.hom

lemma sq₁ (k k' : Λ) (hk₁ : k < k') :
    S.ψ k k' hk₁ ≫ G.map (S.functor.obj k').hom =
    F.map (S.functor.obj k).hom ≫ E.hom := by
  have ψ' : (S.1 (op k')).ψ k k' hk₁ _ ≫ G.map ((S.1 (op k')).ξ.obj (iic% k' k')).hom = _ :=
    dsimp% (S.1 (op k')).sq₁ k hk₁
  simp [ψ, functor, ξ, ← G.map_comp, ψ', ← F.map_comp_assoc]

lemma t₁ (k₁ k₂ k₃ : Λ) (h₁₂ : k₁ ≤ k₂) (h₂₃ : k₂ < k₃) :
    S.ψ k₁ k₃ (by valid) =
    F.map (S.functor.map (homOfLE h₁₂)).left.hom ≫ S.ψ k₂ k₃ h₂₃ := by
  have :=
    Functor.congr_hom
      congr($(S.2 (homOfLE h₂₃.le : iic% k₂ k₃ ⟶ iic% k₃ k₃).op).ξ).symm
      (homOfLE h₁₂ : iic% k₁ k₂ ⟶ iic% k₂ k₂)
  simp [ψ, functor, ξ, dsimp% (S.1 (Opposite.op k₃)).t₁ k₁ k₂ k₃ h₁₂ h₂₃ le_rfl, this,
    ξObjIso, eqToIso, trunc]

lemma t₂ (k₁ k₂ k₃ : Λ) (h₁₂ : k₁ < k₂) (h₂₃ : k₂ ≤ k₃) :
    S.ψ k₁ k₃ (by valid) =
    S.ψ k₁ k₂ h₁₂ ≫ G.map (S.functor.map (homOfLE h₂₃)).left.hom := by
  have h' := dsimp% (S.1 <| op k₃).t₂ k₁ k₂ k₃ h₁₂ h₂₃ le_rfl
  have := congr($(S.2 (homOfLE h₂₃ : k₂ ⟶ k₃).op)).symm
  simp [h', ψ, Seg.ξ, congr_ψ _ _ this, trunc, ← Functor.map_comp,
    ← Functor.map_comp_assoc, ξObjIso, functor]

/-- Repackage the `ψ` fields of all the `PartialChainUpTo` in a `Seg` as a
natural transformation. -/
@[simps]
def ψNatTrans [NoMaxOrder Λ] :
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
/-- Construct a `PartialChainUpTo κ Λ E ⊥` from the data of an object `ξ₀`. -/
noncomputable def mkBot [OrderBot Λ] {E : Inserter F G}
    (ξ₀ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj) :
    PartialChainUpTo κ Λ E ⊥ where
  ξ := Functor.const _ |>.obj ξ₀
  ψ i j hij hk := False.elim <| by valid
  t₁ j k l hjk hkl hl := False.elim <| by valid
  t₂ j k l hjk hkl hl := False.elim <| by valid
  sq₁ j hj := False.elim <| by valid

variable {κ} in
/-- Characterization of `mkBot`. -/
noncomputable def mkBotObjBotIso [OrderBot Λ] {E : Inserter F G}
    (c : CostructuredArrow (isCardinalPresentable K κ).ι E.obj) :
  (mkBot Λ c).ξ.obj (iic% ⊥ ⊥) ≅ c := .refl _

variable {κ} in
/-- Construct a `PartialChainUpTo κ Λ E (succ ⊥)` from the data
of `ξ₀ ⟶ ξ₁` equipped with a map `F.obj ξ₀ ⟶ G.map ξ₁` -/
noncomputable def mkSuccBot [NoMaxOrder Λ] [OrderBot Λ] {E : Inserter F G}
    (ξ₀ ξ₁ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν₀ : ξ₀ ⟶ ξ₁) (ψ₀ : F.obj ξ₀.left.obj ⟶ G.obj ξ₁.left.obj)
    (h : F.map ξ₀.hom ≫ E.hom = ψ₀ ≫ G.map ξ₁.hom) :
    PartialChainUpTo κ Λ E (succ ⊥) :=
  (mkBot Λ ξ₀).extend κ Λ ξ₁ ν₀ ψ₀ h (by valid)

section

variable {κ} [NoMaxOrder Λ] [OrderBot Λ] {E : Inserter F G}
    (ξ₀ ξ₁ : CostructuredArrow (isCardinalPresentable K κ).ι E.obj)
    (ν₀ : ξ₀ ⟶ ξ₁) (ψ₀ : F.obj ξ₀.left.obj ⟶ G.obj ξ₁.left.obj)
    (h : F.map ξ₀.hom ≫ E.hom = ψ₀ ≫ G.map ξ₁.hom)

lemma mkSuccBot_bot_eq : (mkSuccBot Λ ξ₀ ξ₁ ν₀ ψ₀ h).ξ.obj (iic% ⊥ (succ ⊥)) = ξ₀ :=
  SmallObject.SuccStruct.extendToSucc_obj_eq (hi := le_rfl) ..

lemma mkSuccBot_succ_bot_eq : (mkSuccBot Λ ξ₀ ξ₁ ν₀ ψ₀ h).ξ.obj (iic% (succ ⊥) (succ ⊥)) = ξ₁ :=
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

end PartialChainUpTo

/-- Shorthand for the object property that we will eventually prove to be equal to
the class of κ-presentable objects of the Inserter category -/
abbrev O₁ (F G : K ⥤ L) : ObjectProperty (Inserter F G) :=
  (isCardinalPresentable K κ).inverseImage (Inserter.proj F G)

/-- Shorthand for the index type of the canonical diagram to write any
inserter as a κ-filtered colimit of κ-presentable inserters. -/
abbrev Δ (E : Inserter F G) := CostructuredArrow ((O₁ κ F G).ι) E

instance {E : Inserter F G} (x : Δ κ E) : IsCardinalPresentable x.left.obj.obj κ :=
  x.left.property

instance {E : Inserter F G} (x : Δ κ E) : IsCardinalPresentable ((O₁ κ F G).ι.obj x.left).obj κ :=
  x.left.property

open PartialChainUpTo Order Limits in
/--
The key technical ingredient in the proof that inserters are accessible: given a diagram,
```
     F(u)      F(v)
F(S) --> F(T) ---> F(K)
 |                  | Φ
 v                  v
G(T) ------------> G(K)
        G(v)
```
where u : S → T and v : T ⟶ K are maps of κ-presentable objects,
one can find a factorization
```
F(S) --> F(T) ---> F(U) --> F(K)
 |          F(v')   | σ      | Φ
 v                  v        v
G(T) ------------> G(U) --> F(K)
         G(v')
```
-/
lemma exists_Δ_of_pentagon
    [IsCardinalAccessibleCategory K κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ]
    [F.PreservesCardinalPresentable κ]
    [LinearOrder Λ] [OrderBot Λ] [SuccOrder Λ] [NoMaxOrder Λ] [WellFoundedLT Λ]
    (hΛ : HasCardinalLT Λ κ) (E : Inserter F G) (S T : K)
    [IsCardinalPresentable S κ] [IsCardinalPresentable T κ]
    [HasColimitsOfShape Λ K] [HasColimitsOfShape Λ L]
    [PreservesColimitsOfShape Λ F] [PreservesColimitsOfShape Λ G]
    (σ : F.obj S ⟶ G.obj T)
    (u : S ⟶ T) (v : T ⟶ E.obj)
    (h : σ ≫ G.map v = F.map u ≫ F.map v ≫ E.hom) :
    ∃ (B : Δ κ E) (g : T ⟶ B.left.obj.obj),
      σ ≫ G.map g = F.map u ≫ F.map g ≫ B.left.obj.hom ∧
      g ≫ B.hom.hom = v := by
  let O₀ := isCardinalPresentable K κ -- shorthand to make things a bit more compact.
  -- local grind helper : having this in context helps
  have _ {x y : CostructuredArrow O₀.ι E.obj} (f : x ⟶ y) : f.left.hom ≫ y.hom = x.hom := by simp
  -- First, we summon a diagram to write T as a κ-filtered colimits of κ-filtered objects.
  have : IsFiltered (CostructuredArrow O₀.ι E.obj) := isFiltered_of_isCardinalFiltered _ κ
  let hcolimT := O₀.ι.denseAt E.obj -- E.obj ≅ colim_ξ T_ξ
  have (X : K) : PreservesColimitsOfShape (CostructuredArrow O₀.ι X) G :=
    G.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _
  let hcolimGT := isColimitOfPreserves G (O₀.ι.denseAt E.obj) -- G(E.obj) ≅ colim_ξ G(T_ξ)
  -- Now we get a first factorization for σ
  obtain ⟨ξ₀, v₀, hv₀⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimT v
  dsimp at v₀ hv₀
  simp only [Category.id_comp] at hv₀
  obtain ⟨ξ₁₀, ψ₀₀, hψ₀₀⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimGT
    (F.map ξ₀.hom ≫ E.hom)
  dsimp at ψ₀₀ hψ₀₀
  obtain ⟨ξ₁, u₀, ψ₀, hψ₀₁⟩ := IsCardinalPresentable.exists_of_hexagon κ hcolimGT
    (F.map u ≫ F.map v₀) (F.map ξ₀.hom) σ (G.map v₀) E.hom (by dsimp; grind)
  dsimp at u₀ ψ₀ hψ₀₁
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
  have e₁ : Θ.app ⊥ = F.map (eqToHom e₀).left.hom ≫ ψ₀ ≫ G.map (eqToHom e₁.symm).left.hom := by
    dsimp [Θ, Seg.ψNatTrans, Seg.ψ]
    rw [congr_ψ _ _ S_val, mkSuccBot_ψ]
    simp [Seg.ξObjIso, Seg.ξ]
  -- Finally, we can use ξ : its colimit exists and is κ-presentable.
  have : O₀.IsClosedUnderColimitsOfShape Λ :=
    have : Small.{w} Λ := hΛ.small
    CategoryTheory.isClosedUnderColimitsOfShape_isCardinalPresentable K (by
      rwa [hasCardinalLT_arrow_iff_of_isThin _ κ (Cardinal.IsRegular.aleph0_le Fact.out)])
  have : HasColimitsOfShape Λ O₀.FullSubcategory := hasColimitsOfShape_of_closedUnderColimits ..
  let U := colimit ξ
  -- the map t := colim_i (ψ : F ξ_i ⟶ G ξᵢ₊₁) identifies to a map t1 : F (colim ξᵢ) ⟶ G (colim ξᵢ)
  let t := colimMap Θ
  have : (succ_mono (α := Λ)).functor.Final :=
    (Monotone.final_functor_iff _).mpr fun j ↦ ⟨j, le_succ j⟩
  let t1 : F.obj U.left.obj ⟶ G.obj U.left.obj :=
    (preservesColimitIso (CostructuredArrow.proj O₀.ι E.obj ⋙ O₀.ι ⋙ F) ξ).hom ≫ t ≫
    (Functor.Final.colimitIso succ_mono.functor _).hom ≫ (preservesColimitIso _ _).inv
  let B₀ : (O₁ κ F G).FullSubcategory :=
    ⟨⟨t1⟩, by simp only [ObjectProperty.prop_inverseImage_iff, proj_obj]; infer_instance⟩
  let B : Δ κ E :=
    CostructuredArrow.mk (Y := B₀) ⟨U.hom, by
      apply isColimitOfPreserves (CostructuredArrow.proj O₀.ι E.obj ⋙ O₀.ι ⋙ F)
        (colimit.isColimit ξ) |>.hom_ext
      intro j
      have e₁ := ι_preservesColimitIso_hom (CostructuredArrow.proj O₀.ι E.obj ⋙ O₀.ι ⋙ F) ξ j
      dsimp at e₁
      simp [U, B₀, t1, ← Functor.map_comp_assoc, reassoc_of% e₁, t, ← G.map_comp, Θ, ξ,
        (S.sq₁ j (succ j) (lt_succ j)).symm]⟩
  refine ⟨B, v₀ ≫ (eqToHom e₀.symm).left.hom ≫ (colimit.ι ξ ⊥).left.hom, ?_, ?_⟩
  · have := ι_preservesColimitIso_hom (CostructuredArrow.proj O₀.ι E.obj ⋙ O₀.ι ⋙ F) ξ ⊥
    have he1 : σ ≫ G.map v₀ ≫ G.map u₀.left.hom = F.map u ≫ F.map v₀ ≫ ψ₀ := by grind
    dsimp at this
    simp [B, B₀, U, t1, t, reassoc_of% this]
    simp [e₁, ← reassoc_of% he1, ← colimit.w ξ (homOfLE (le_succ ⊥) : ⊥ ⟶ _),
      -colimit.w, e₂]
  · simp only [B, B₀, U, Functor.comp_obj, CostructuredArrow.proj_obj, ObjectProperty.ι_obj,
      Category.assoc, t1, t, ← colimit.w ξ (homOfLE (le_succ ⊥) : ⊥ ⟶ _), e₂]
    simp [-CostructuredArrow.eqToHom_left, -ObjectProperty.eqToHom_hom, hv₀]

open Limits

variable [IsCardinalAccessibleCategory K κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ]
    [F.PreservesCardinalPresentable κ]
    [LinearOrder Λ] [OrderBot Λ] [SuccOrder Λ] [NoMaxOrder Λ] [WellFoundedLT Λ]
    (hΛ : HasCardinalLT Λ κ) (E : Inserter F G)
    [HasColimitsOfShape Λ K] [HasColimitsOfShape Λ L]
    [PreservesColimitsOfShape Λ F] [PreservesColimitsOfShape Λ G]

include hΛ in
lemma isCardinalFiltered_Δ (E : Inserter F G) :
    IsCardinalFiltered (Δ κ E) κ := by
  rw [isCardinalFiltered_iff']
  -- first, represent the object underlying E as a κ-filtered colimit of κ-presentable objects
  let O₀ := isCardinalPresentable K κ -- shorthand to make the writing more compact
  have : IsFiltered (CostructuredArrow O₀.ι E.obj) := isFiltered_of_isCardinalFiltered _ κ
  let hcolimS := O₀.ι.denseAt E.obj -- E.obj ≅ colim_ξ S_ξ
  have (X : K) : PreservesColimitsOfShape (CostructuredArrow O₀.ι X) G :=
    G.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _
  let hcolimG := isColimitOfPreserves G (O₀.ι.denseAt E.obj) -- G(E.obj) ≅ colim_ξ G(T_ξ)
  refine ⟨fun ι v hι ↦ ?_, fun ι r p f hι hι' ↦ ?_⟩
  · -- There exists an index ξ₀ such that all the v_j factorizes through the index in K
    obtain ⟨ξ₀, t0, hf0, he⟩ :
        ∃ (ξ₀ : CostructuredArrow O₀.ι E.obj)
          (t : (i : ι) → ((v i).left.obj.obj ⟶ ξ₀.left.obj)),
          (∀ i : ι, t i ≫ ξ₀.hom = (v i).hom.hom) ∧
          (∀ i : ι, F.map (t i) ≫ F.map ξ₀.hom ≫ E.hom =
            (v i).left.obj.hom ≫ G.map (t i) ≫ G.map ξ₀.hom) := by
      have b (j : ι) := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimS (v j).hom.hom
      dsimp at b
      simp only [Category.id_comp] at b
      choose s0 f0 hf0 using b
      let ξ₀ := IsCardinalFiltered.max s0 hι
      let t0 (j : ι) : (v j).left.obj.obj ⟶ ξ₀.left.obj :=
       (f0 j) ≫ (IsCardinalFiltered.toMax s0 hι j).left.hom
      exact ⟨IsCardinalFiltered.max s0 hι, fun j ↦
        (f0 j) ≫ (IsCardinalFiltered.toMax s0 hι j).left.hom,
        by simp [hf0],
        by simp [← Functor.map_comp_assoc, ← Functor.map_comp, hf0]⟩
    -- Following Positselski we also find a u : ξ₀ ⟶ ξ₁ with σ : F.obj ξ₀ ⟶ G.obj ξ₁ such that
    -- `F.map ξ₀.hom ≫ E.hom = σ ≫ G.map ξ₁.hom` and
    -- `F.map (t0 j) ≫ σ = (v j).hom.hom ≫ G.map (t0 j) ≫ G.map u`
    obtain ⟨ξ₁, u, σ, h1, h2⟩ :
        ∃ (ξ₁ : CostructuredArrow O₀.ι E.obj) (u : ξ₀ ⟶ ξ₁)
        (σ : F.obj ξ₀.left.obj ⟶ G.obj ξ₁.left.obj),
        F.map ξ₀.hom ≫ E.hom = σ ≫ G.map ξ₁.hom ∧
        ∀ (j : ι), F.map (t0 j) ≫ σ = (v j).left.obj.hom ≫ G.map (t0 j) ≫ G.map u.left.hom := by
      obtain ⟨ξ₁, ν₁, σ, hξ₁₀⟩ := IsCardinalPresentable.exists_hom_above_of_isColimit κ hcolimG
        (F.map ξ₀.hom ≫ E.hom) ξ₀
      dsimp at hξ₁₀ ν₁ σ
      simp only [Category.id_comp] at hξ₁₀
      have (j : ι) := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolimG
        (F.map (t0 j) ≫ σ) ((v j).left.obj.hom ≫ G.map (t0 j) ≫ G.map ν₁.left.hom) (by
          simp [hξ₁₀, hf0, ← Functor.map_comp_assoc, ← Functor.map_comp])
      choose p1 p2 p3 using this
      simp only [Functor.comp_obj, CostructuredArrow.proj_obj, ObjectProperty.ι_obj,
        Functor.comp_map, CostructuredArrow.proj_map, ObjectProperty.ι_map, Category.assoc] at p3
      obtain ⟨ξ₁', ν₁', u', h'⟩ := IsCardinalFiltered.wideSpan p2 hι
      let σ' : F.obj ξ₀.left.obj ⟶ G.obj ξ₁'.left.obj := σ ≫ G.map u'.left.hom
      refine ⟨ξ₁', ν₁ ≫ u', σ', ?_, fun i ↦ ?_⟩
      · simp [σ', ← G.map_comp, hξ₁₀]
      · simp [← h' i, reassoc_of% p3, σ']
    -- Then, we use the main lemma with ξ₀ and ξ₁
    obtain ⟨b, g, h₁, h₂⟩ :=
      exists_Δ_of_pentagon κ Λ hΛ E (S := ξ₀.left.obj) (T := ξ₁.left.obj) σ u.left.hom ξ₁.hom
        (by simp [← h1, ← F.map_comp_assoc])
    refine ⟨b, fun i ↦ ⟨CostructuredArrow.homMk ⟨t0 i ≫ u.left.hom ≫ g, ?_⟩ ?_⟩⟩
    · simp [← reassoc_of% h2 i, h₁]
    · ext
      simp [h₂, hf0]
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
        simp only [ObjectProperty.prop_inverseImage_iff, proj_obj] at this
        infer_instance
      obtain ⟨ξ₀', v, hv⟩ :=
        IsCardinalPresentable.exists_eq_of_isColimit'_of_hasCardinalLT κ hcolimS hι
          (fun i ↦ (f i).left.hom.hom ≫ u) (fun i i' ↦ by
            simp [hu, dsimp% congr($((f i').w).hom), dsimp% congr($((f i).w).hom)])
      exact ⟨ξ₀', u ≫ v.left.hom, by simp [hu], by simpa using hv⟩
    /- Then pick ξ₁ above u, such that such that F.map ξ₀.hom ≫ E.hom factorizes through
    ξ₁ while remaining compatible with p. -/
    obtain ⟨ξ₁, v₁, σ, hv₁, hv₂⟩ :=
      IsCardinalPresentable.exists_of_hexagon κ hcolimG
        (F.map u) (F.map ξ₀.hom) p.left.obj.hom (G.map u) E.hom
        (by simp [← Functor.map_comp_assoc, hu, ← Functor.map_comp])
    dsimp at hv₁ hv₂ hv
    simp only [Category.id_comp] at hv₁ hv₂ hv
    -- Then, we use the main lemma with ξ₀ and ξ₁
    obtain ⟨b', g, h₁, h₂⟩ :=
      exists_Δ_of_pentagon κ Λ hΛ E ξ₀.left.obj ξ₁.left.obj
        σ v₁.left.hom ξ₁.hom (by simp [← hv₂, ← Functor.map_comp_assoc])
    let pt : ι := hι'.some -- we need some arbitrary element of ι
    have := congr($(CostructuredArrow.w (f pt)).hom)
    simp only [ObjectProperty.ι_obj, ObjectProperty.ι_map, comp_hom] at this
    use
      b',
      CostructuredArrow.homMk ⟨⟨u ≫ v₁.left.hom ≫ g, by
        grind [CostructuredArrow.mk_left]⟩⟩ (by ext; simp [h₂, hu]),
      CostructuredArrow.homMk ⟨⟨(f pt).left.hom.hom ≫ u ≫ v₁.left.hom ≫ g,
        by grind [CostructuredArrow.mk_left]⟩⟩ (by ext; simp [h₂, hu, this])
    intro i
    ext
    simp [reassoc_of% hv i pt]

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

include hΛ in
lemma final.nonempty_structured_arrow (E : Inserter F G)
    (p : CostructuredArrow (isCardinalPresentable K κ).ι E.obj) :
    Nonempty (StructuredArrow p (U κ E)) := by
  -- first, represent the object underlying E as a κ-filtered colimit of κ-presentable objects
  let O₀ := isCardinalPresentable K κ -- shorthand to make the writing more compact
  have : IsFiltered (CostructuredArrow O₀.ι E.obj) := isFiltered_of_isCardinalFiltered _ κ
  let hcolimT := O₀.ι.denseAt E.obj -- E.obj ≅ colim_ξ S_ξ
  have (X : K) : PreservesColimitsOfShape (CostructuredArrow O₀.ι X) G :=
    G.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _
  let hcolimG := isColimitOfPreserves G (O₀.ι.denseAt E.obj) -- G(E.obj) ≅ colim_ξ G(T_ξ)
  obtain ⟨ξ₀, u, hu⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolimT p.hom
  dsimp at u hu
  simp only [Category.id_comp] at hu
  obtain ⟨ξ₁, u', v', hu'⟩ := IsCardinalPresentable.exists_hom_above_of_isColimit κ hcolimG
    (F.map p.hom ≫ E.hom) ξ₀
  dsimp at u' v' hu'
  simp only [Category.id_comp] at hu'
  obtain ⟨b, g, h₁, h₂⟩ :=
    exists_Δ_of_pentagon κ Λ hΛ E p.left.obj ξ₁.left.obj v' (u ≫ u'.left.hom) ξ₁.hom
      (by simp [← Functor.map_comp_assoc, hu, hu'])
  exact ⟨StructuredArrow.mk (Y := b) <|
    CostructuredArrow.homMk ⟨u ≫ u'.left.hom ≫ g⟩ (by simp [h₂, hu])⟩

include hΛ in
lemma final (E : Inserter F G) : (U κ E).Final := by
  constructor
  intro p
  have : Nonempty (StructuredArrow p (U κ E)) := final.nonempty_structured_arrow κ Λ hΛ E p
  apply CategoryTheory.zigzag_isConnected
  intro r' r''
  -- It’s useful to have this in context to help simp_all
  have r'w := r''.hom.w
  have r''w := r'.hom.w
  dsimp at r'w r''w
  simp only [U_obj_hom, Category.comp_id] at r'w r''w
  -- Reformulate the goal in a more unbundled way:
  suffices H :
      ∃ (u : Δ κ E) (f1 : r'.right ⟶ u) (f2 : r''.right ⟶ u),
       f1.left.hom.hom ≫ u.hom.hom = r'.right.hom.hom ∧
       f2.left.hom.hom ≫ u.hom.hom = r''.right.hom.hom ∧
       r'.hom.left.hom ≫ f1.left.hom.hom = r''.hom.left.hom ≫ f2.left.hom.hom by
    obtain ⟨u, f1, f2, h1, h2, h3⟩ := H
    let u' : StructuredArrow p (U κ E) := StructuredArrow.mk (T := U κ E)
      (CostructuredArrow.homMk ⟨r'.hom.left.hom ≫ f1.left.hom.hom⟩ (by simp_all))
    calc
      Zigzag r' u' := .of_zag <| .of_hom <| StructuredArrow.homMk f1
      Zigzag u' r'' := .of_zag <| .of_inv <| StructuredArrow.homMk f2
  -- As usual: write E.obj as a colimit, and G (E.obj) as well
  let O₀ := isCardinalPresentable K κ -- shorthand to make the writing more compact
  have : IsFiltered (CostructuredArrow O₀.ι E.obj) := isFiltered_of_isCardinalFiltered _ κ
  let hcolimT := O₀.ι.denseAt E.obj -- E.obj ≅ colim_ξ T_ξ
  have (X : K) : PreservesColimitsOfShape (CostructuredArrow O₀.ι X) G :=
    G.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ _
  let hcolimG := isColimitOfPreserves G (O₀.ι.denseAt E.obj) -- G(E.obj) ≅ colim_ξ G(T_ξ)
  obtain ⟨ξ₀, f₀, f₁, hf₀, hf₁, hsq⟩ :
      ∃ (ξ₀ : CostructuredArrow O₀.ι E.obj)
        (f₀ : r'.right.left.obj.obj ⟶ ξ₀.left.obj)
        (f₁ : r''.right.left.obj.obj ⟶ ξ₀.left.obj),
        f₀ ≫ ξ₀.hom = r'.right.hom.hom ∧ f₁ ≫ ξ₀.hom = r''.right.hom.hom ∧
        r'.hom.left.hom ≫ f₀ = r''.hom.left.hom ≫ f₁ := by
    obtain ⟨ξ₀₀, u₀₀, v₀₀, hu₀₀⟩ :=
      IsCardinalPresentable.exists_hom_above_of_isColimit κ hcolimT r'.right.hom.hom p
    obtain ⟨ξ₀₁, u₀₁, v₀₁, hu₀₁⟩ :=
      IsCardinalPresentable.exists_hom_above_of_isColimit κ hcolimT r''.right.hom.hom p
    dsimp at u₀₀ v₀₀ hu₀₀ u₀₁ v₀₁ hu₀₁
    simp only [Category.id_comp] at hu₀₀ hu₀₁
    obtain ⟨ξ₀, u, v, h₁, h₂⟩ := IsFiltered.bowtie u₀₀ u₀₁
      (r'.hom ≫ CostructuredArrow.homMk ⟨v₀₀⟩) (r''.hom ≫ CostructuredArrow.homMk ⟨v₀₁⟩)
    exact ⟨ξ₀, v₀₀ ≫ u.left.hom, v₀₁ ≫ v.left.hom,
      by simp [hu₀₀], by simp [hu₀₁], by simpa using congr($(h₂).left.hom)⟩
  obtain ⟨ξ₁, u, σ, hsq', hl, hr⟩ :
      ∃ (ξ₁ : CostructuredArrow O₀.ι E.obj)
        (u : ξ₀ ⟶ ξ₁)
        (σ : F.obj ξ₀.left.obj ⟶ G.obj ξ₁.left.obj),
        F.map ξ₀.hom ≫ E.hom = σ ≫ G.map ξ₁.hom ∧
        (F.map f₀ ≫ σ = r'.right.left.obj.hom ≫ G.map f₀ ≫ G.map u.left.hom) ∧
        (F.map f₁ ≫ σ = r''.right.left.obj.hom ≫ G.map f₁ ≫ G.map u.left.hom) := by
    obtain ⟨ξ₁₀, u₁₀, σ₁₀, hu₁₀, hu₁₀'⟩ :=
      IsCardinalPresentable.exists_of_hexagon κ hcolimG (F.map f₀) (F.map ξ₀.hom)
        r'.right.left.obj.hom (G.map f₀) E.hom
        (by simp [← F.map_comp_assoc, hf₀, ← G.map_comp])
    obtain ⟨ξ₁₁, u₁₁, σ₁₁, hu₁₁, hu₁₁'⟩ :=
      IsCardinalPresentable.exists_of_hexagon κ hcolimG (F.map f₁) (F.map ξ₀.hom)
        r''.right.left.obj.hom (G.map f₁) E.hom
        (by simp [← F.map_comp_assoc, ← G.map_comp, hf₁])
    dsimp at u₁₀ σ₁₀ u₁₁ σ₁₁ hu₁₀ hu₁₀' hu₁₁ hu₁₁'
    simp only [Category.id_comp] at hu₁₀ hu₁₀' hu₁₁ hu₁₁'
    obtain ⟨ξ₁₂, u₁₂, v₁₂, hsq''⟩ := IsFiltered.span u₁₀ u₁₁
    obtain ⟨ξ₁, u₁, h⟩ :=
      IsCardinalPresentable.exists_eq_of_isColimit' κ hcolimG
        (σ₁₀ ≫ G.map u₁₂.left.hom) (σ₁₁ ≫ G.map v₁₂.left.hom)
        (by simp [← Functor.map_comp, ← hu₁₀', ← hu₁₁'])
    simp only [Functor.comp_obj, CostructuredArrow.proj_obj, ObjectProperty.ι_obj, Functor.comp_map,
      CostructuredArrow.proj_map, ObjectProperty.ι_map, Category.assoc] at h
    exact ⟨ξ₁, u₁₀ ≫ u₁₂ ≫ u₁, σ₁₀ ≫ G.map u₁₂.left.hom ≫ G.map u₁.left.hom,
      by simp_rw [Category.assoc, reassoc_of% h, ← G.map_comp, helper, ← hu₁₁'],
      by simp [← reassoc_of% hu₁₀],
      by simp [reassoc_of% hsq'', ← reassoc_of% hu₁₁, h]⟩
  obtain ⟨b, v₁, hu₁, hv₁⟩ :=
    exists_Δ_of_pentagon κ Λ hΛ E ξ₀.left.obj ξ₁.left.obj σ u.left.hom ξ₁.hom (by
      simp [← hsq', ← F.map_comp_assoc])
  use b
  exact
    ⟨ CostructuredArrow.homMk ⟨⟨f₀ ≫ u.left.hom ≫ v₁, by simp [← hu₁, reassoc_of% hl]⟩⟩,
      CostructuredArrow.homMk ⟨⟨f₁ ≫ u.left.hom ≫ v₁, by simp [← hu₁, reassoc_of% hr]⟩⟩,
      by simp [hv₁, hf₀], by simp [hv₁, hf₁], by simp [reassoc_of% hsq]⟩

attribute [local ext] Inserter in
instance [LocallySmall.{w} L] :
    ObjectProperty.EssentiallySmall.{w} (O₁ κ F G) := by
  dsimp [O₁]
  have : ObjectProperty.EssentiallySmall.{w}
      (((isCardinalPresentable K κ).inverseImage (proj F G)).map (proj F G)) :=
    ObjectProperty.EssentiallySmall.of_le (ObjectProperty.map_inverseImage_le _ (proj F G))
  apply ObjectProperty.EssentiallySmall.of_functor _ (proj F G) this
  · intro y
    suffices h : ObjectProperty.EssentiallySmall.{w}
        (fun (x : Inserter F G) ↦ Nonempty ((proj F G).obj x ≅ y)) by
      exact ObjectProperty.EssentiallySmall.of_le.{w} (inf_le_right)
    dsimp
    let Q : ObjectProperty (Inserter F G) := fun x : Inserter F G ↦ x.obj = y
    have : ObjectProperty.Small.{w} Q := by
      let f (x : Subtype Q) : (F.obj y ⟶ G.obj y) :=
        eqToHom (by rw [x.2]) ≫ x.1.hom ≫ eqToHom (by rw [x.2])
      apply small_of_injective.{w} (f := f)
      intro u v huv
      ext
      · rw [u.2, v.2]
      · rwa [← heq_iff_eq, eqToHom_comp_heq_iff, heq_comm, eqToHom_comp_heq_iff,
          comp_eqToHom_heq_iff, heq_comm, comp_eqToHom_heq_iff] at huv
    exact ⟨Q, this, fun x ⟨e⟩ ↦
      (ObjectProperty.prop_isoClosure_iff ..).mpr
      ⟨⟨F.map e.inv ≫ x.hom ≫ G.map e.hom⟩, rfl, ⟨Inserter.mkIso e⟩⟩⟩

end Accessible

section

open Accessible
variable {K L : Type*} [Category* K] [Category* L] (F G : K ⥤ L) (κ : Cardinal.{w})
    [Fact κ.IsRegular] [IsCardinalAccessibleCategory K κ] [IsCardinalAccessibleCategory L κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ]
    (Λ : Type*) [Nonempty Λ] [LinearOrder Λ] [SuccOrder Λ] [WellFoundedLT Λ] [NoMaxOrder Λ]
    (hΛ : HasCardinalLT Λ κ)
    [Limits.HasColimitsOfShape Λ K] [Limits.HasColimitsOfShape Λ L]
    [Limits.PreservesColimitsOfShape Λ F] [Limits.PreservesColimitsOfShape Λ G]

include Λ hΛ in
public theorem isCardinalFiltered_generator_inverseImage_isCardinalPresentable :
    ((isCardinalPresentable K κ).inverseImage
      (Inserter.proj F G)).IsCardinalFilteredGenerator κ := by
  have (X : Inserter F G) : IsCardinalFiltered (CostructuredArrow (O₁ κ F G).ι X) κ := by
    have : OrderBot Λ := WellFoundedLT.toOrderBot Λ
    exact isCardinalFiltered_Δ κ Λ hΛ X
  apply +allowSynthFailures IsCardinalFilteredGenerator.of_isDense_ι
  · constructor
    intro E
    /- Using that the functor `U : Δ κ E ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj`
    is final, any inserter is the κ-filtered colimit of its projection from Δ κ E:
    This can be checked after postcomposition with `proj F G` and extension through `U`,
    and the cocone obtained this way identifies to the canonical cocone for E.obj,
    which is a colimit diagram as `K` is κ-accessible. -/
    dsimp [Functor.isDenseAt]
    -- The canonical cocone making E.hom a κ-filtered colimit of κ-presentable objects
    let hcolimT := (isCardinalPresentable K κ).ι.denseAt E.obj -- E.obj ≅ colim_ξ S_ξ
    have : OrderBot Λ := WellFoundedLT.toOrderBot Λ
    have : (U κ E).Final := final κ Λ hΛ E
    let t1 := (Functor.Final.isColimitWhiskerEquiv (U κ E) _).symm hcolimT
    have : Limits.PreservesColimitsOfShape (CostructuredArrow (O₁ κ F G).ι E) F :=
      Functor.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall _ κ _
    have : Limits.PreservesColimitsOfShape (CostructuredArrow (O₁ κ F G).ι E) G :=
      Functor.preservesColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall _ κ _
    have : Limits.HasColimitsOfShape (CostructuredArrow (O₁ κ F G).ι E) L :=
      hasColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ ..
    have : Limits.HasColimitsOfShape (CostructuredArrow (O₁ κ F G).ι E) K :=
      hasColimitsOfShape_of_isCardinalAccessible_of_essentiallySmall κ ..
    apply Limits.ReflectsColimit.reflects (F := Inserter.proj F G)
      (K := CostructuredArrow.proj (O₁ κ F G).ι E ⋙ (O₁ κ F G).ι)
    let e₁ :
      (U κ E ⋙ CostructuredArrow.proj (isCardinalPresentable K κ).ι E.obj ⋙
        (isCardinalPresentable K κ).ι) ≅
      (CostructuredArrow.proj (O₁ κ F G).ι E ⋙ (O₁ κ F G).ι) ⋙ proj F G := .refl _
    exact Limits.IsColimit.equivOfNatIsoOfIso e₁
      (Limits.Cocone.whisker (U κ E) _)
      ((proj F G).mapCocone
        ((Functor.LeftExtension.mk (𝟭 _) (O₁ κ F G).ι.rightUnitor.inv).coconeAt E))
      (Limits.Cocone.ext (.refl _) (by intros; simp [e₁])) t1
  · intro x hx
    simp only [ObjectProperty.prop_inverseImage_iff, proj_obj] at hx
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
    IsCardinalAccessibleCategory (Inserter F G) κ where
  exists_generator := ⟨O₁ κ F G, inferInstance,
      isCardinalFiltered_generator_inverseImage_isCardinalPresentable F G κ Λ hΛ ..⟩
  hasColimitsOfShape J _ _ := by
    have : Limits.PreservesColimitsOfShape J F :=
      Functor.IsCardinalAccessible.preservesColimitOfShape κ J
    have : Limits.HasColimitsOfShape J K :=
      HasCardinalFilteredColimits.hasColimitsOfShape _ κ _
    have : Limits.HasColimitsOfShape J L :=
      HasCardinalFilteredColimits.hasColimitsOfShape _ κ _
    infer_instance

include Λ hΛ in
public lemma isCardinalPresentable_eq :
    isCardinalPresentable (Inserter F G) κ =
      (isCardinalPresentable K κ).inverseImage (Inserter.proj F G) := by
  have := isCardinalFiltered_generator_inverseImage_isCardinalPresentable F G κ Λ hΛ
  rw [this.isPresentable_eq_retractClosure]
  apply ObjectProperty.retractClosure_eq_self

end

instance {K L : Type*} [Category* K] [Category* L] (F G : K ⥤ L)
    [IsAccessibleCategory.{w} K] [IsAccessibleCategory.{w} L]
    [F.IsAccessible.{w}] [G.IsAccessible.{w}] : IsAccessibleCategory.{w} (Inserter F G) := by
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
  have : Limits.HasColimitsOfShape κ.ord.ToType L :=
    HasCardinalFilteredColimits.hasColimitsOfShape _ κ _
  have : Limits.PreservesColimitsOfShape κ.ord.ToType F :=
    Functor.IsCardinalAccessible.preservesColimitOfShape κ _
  have : Limits.PreservesColimitsOfShape κ.ord.ToType G :=
    Functor.IsCardinalAccessible.preservesColimitOfShape κ _
  exact ⟨κ', inferInstance, isCardinalAccessibleCategory F G κ' κ.ord.ToType hCard⟩

end CategoryTheory.Inserter
