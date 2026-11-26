/-
Copyright (c) 2026 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.CategoryTheory.Inserter.Basic
public import Mathlib.CategoryTheory.Presentable.LocallyPresentable
public import Mathlib.CategoryTheory.Presentable.PreservesCardinalPresentable

import Mathlib.CategoryTheory.Inserter.Limits
import Mathlib.CategoryTheory.SmallObject.Iteration.FunctorOfCocone

/-! # Inserter categories are accessible

In this file, we show that categories of inserters are accessible in good situations.

More precisely, let `F G : K ⥤ L` be two `κ`-accessible functors between two κ-accessible
categories, such that `F` preserves `κ`-presentable objects.
Assuming there exists an ordinal `Λ < κ` such that `K` and `L` admit Λ-indexed colimits and such
that `F` and `G` preserve `Λ`-indexed colimits, we show that the category `Inserter F G`
is κ-accessible and that its κ-presentable objects are exactly objects `E : Inserter F G` such that
`E.obj` is a κ-presentable object of `K`.

This is [L. Positselski, *Notes On Limits of Accessible Categories*, Theorem 4.1][positselski2024].
We follow the proof from this reference.

## References

- [L. Positselski, *Notes On Limits of Accessible Categories*][positselski2024]

## TODOs

This file is still in active WIP

-/

namespace CategoryTheory.Inserter

universe w

open Limits

namespace Accessible

variable {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular]

/-- If the underlying object of an inserter `X` is κ-presentable, then `X` is κ-presentable. -/
public instance (X : Inserter F G)
    [IsCardinalPresentable X.obj κ] [HasCardinalFilteredColimits K κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ] :
    IsCardinalPresentable X κ := by
  refine IsCardinalPresentable.mk fun I _ _ B b hb ↦ ?_
  have : HasColimitsOfShape I K := HasCardinalFilteredColimits.hasColimitsOfShape _ κ I
  have : PreservesColimitsOfShape I F := F.preservesColimitsOfShape_of_isCardinalAccessible κ I
  have : PreservesColimitsOfShape I G := G.preservesColimitsOfShape_of_isCardinalAccessible κ I
  let hcolimG := isColimitOfPreserves (proj F G ⋙ G) hb
  let hcolim := isColimitOfPreserves (proj F G) hb
  refine ⟨fun f ↦ ?_, fun i f₁ f₂ h ↦ ?_⟩
  · obtain ⟨i, f', hf'⟩ := IsCardinalPresentable.exists_hom_of_isColimit κ hcolim f.hom
    dsimp at f' hf'
    obtain ⟨j, u, h⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolimG
      (f₁ := F.map f' ≫ (B.obj i).hom) (f₂ := X.hom ≫ G.map f') (by dsimp; grind)
    refine ⟨j, ⟨f' ≫ (B.map u).hom, by grind⟩, ?_⟩
    ext
    simp [dsimp% congr($(b.ι.naturality u).hom), hf']
  · obtain ⟨j, u, hu⟩ := IsCardinalPresentable.exists_eq_of_isColimit' κ hcolim
      (f₁ := f₁.hom) (f₂ := f₂.hom) congr($(h).hom)
    exact ⟨j, u, by grind⟩

/-
Below, we prove one of the main lemma to prove the main theorem:
this is Lemma 4.5 in [positselski2024].

The lemma says that given a diagram,
```
     F(u)      F(v)
F(S) --> F(T) ---> F(K)
 |                  | Φ
 v                  v
G(T) ------------> G(K)
        G(v)
```
where S and T are κ-presentable objects and u : S → T and v : T ⟶ K are morphisms,
one can find a factorization
```
F(S) --> F(T) ---> F(U) --> F(K)
 |          F(v')   | σ      | Φ
 v                  v        v
G(T) ------------> G(U) --> F(K)
         G(v')
```
where U is κ-presentable.

The main technical difficulty is that if one uses κ-presentability naively, one
only produces a diagram of shape
```
F(S) --> F(T) ---> F(ξ₀) --> F(K)
 |          F(v')   | ψ₀       | Φ
 v                  v          v
G(T) ------------> G(ξ₁) --> F(K)
```
where `ξ₀` and `ξ₁` are not necessarily the same object.

To turn the middle vertical map into an inserter, one must iterate the construction of such diagrams
to construct a chain `ξ₀ ⟶ ξ₁ ⟶ …` by transfinite induction, equipped with natural structure maps
`ψᵢ : F(ξᵢ) ⟶ G(ξᵢ₊₁)`.
Once the chain becomes long enough, one can take its colimit to stabilize those maps:
the ordinal Λ that appears in the hypothesis of the main theorem quantifies this "long enough".

Setting up and carrying out this transfinite induction occupies most of the material below,
the strategy is to encode the partial stages of the induction as a presheaf of types
(`PartialChainUpTo.functor` below) and to record the induction
steps as a `Functor.WellOrderInductionData`, which will let us extract a section
of the presheaf from which we can extract the desired chain. -/

/- In the following, we are going to move very frequently between `Λ`, `Set.Iio _` and `Set.Iic _`.
Most of the time, this requires term annotations and rather boring grind-able proof obligations
so we provide a small discharge tactic that handle all of these and
elaborators to write terms more easily
- `iio% i j` for `⟨i, …⟩ : Set.Iio j`,
- `iic% i j` for `⟨i, _⟩ : Set.Iic j`. -/

/-- Macro for a quick discharger tactic that we will repeatedly use. This is an
optimized grind call for our use case. -/
local macro "valid" : tactic =>
  `(tactic| grind (ematch := 3) (gen := 3)
    +order -ext -etaStruct -extAll -ring +lia -inj -ac -funCC -linarith -mbtc only
      [Subtype.mk_le_mk, Subtype.mk_lt_mk, Order.le_succ_iff_eq_or_le, Order.lt_succ_iff,
        Set.mem_Iic, Set.mem_Iio, Order.IsSuccLimit.succ_lt, → Order.succ_lt_succ, → bot_unique,
        not_lt_bot])

/-- `iio% i j` builds i as a term of `Set.Iio j` using `valid` to discharge the side goal. -/
local macro "iio% " i:term:max j:term:max : term => `((⟨$i, by valid⟩ : Set.Iio $j))

/-- `iic% i j` builds i as a term of `Set.Iic j` using `valid` to discharge the side goal. -/
local macro "iic% " i:term:max j:term:max : term => `((⟨$i, by valid⟩ : Set.Iic $j))

/-- A structure that partially encodes the chain to be constructed for the proof of
Lemma 4.5 from [positselski2024], with its requirements.

Given an inserter `F(E) ⟶ G(E)`, a regular cardinal κ and an element `i` in a `SuccOrder Λ`,
the structure `PartialChainUpTo κ Λ E j` encodes the data of a
functorial assignment `j ↦ ξⱼ` (for `j ≤ i`) of κ-presentable objects of `K`
equipped with a structure map to `E`.

This assignment is equipped with a structure map `ψⱼₖ : F(ξⱼ) ⟶ G(ξₖ)` for all
`j < k ≤ i`, such that

- the square
  ```
    F(ξⱼ) --> F(E)
  ψⱼᵢ |        |
      v        v
    G(ξᵢ) --> G(E)
  ```
  commutes for all `j < i`;
- the triangle
  ```
          ψⱼₖ
    F(ξⱼ) --> G(ξₖ)
      \      /
    ψⱼₗ\    / ψₖₗ
        v  v
        G(ξₗ)
  ```
  commutes for all `j ≤ k < l ≤ i`;
- the triangle
  ```
          ψⱼₖ
    F(ξⱼ) --> G(ξₖ)
      \      /
    ψⱼₗ\    / G(ξ(k ≤ l))
        v  v
        G(ξₗ)
  ```
  commutes for all `j < k ≤ l ≤ i`.

Later, we transform the assignment `j ↦ PartialChainUpTo κ Λ E j` into a
presheaf of types on `Λ` so that we can use `Functor.WellOrderInductionData`.
From a section of that presheaf, we will extract the chain out of `Λ`. -/
@[ext]
structure PartialChainUpTo (Λ : Type*) [Preorder Λ] [SuccOrder Λ]
    (E : Inserter F G) (i : Λ) where
  /-- A functorial assignment `j ↦ ξⱼ` (for `j ≤ i`) of κ-presentable objects of `K`
  equipped with a structure map to the underlying object of the inserter `E`. -/
  ξ : Set.Iic i ⥤ CostructuredArrow (isCardinalPresentable K κ).ι E.obj
  /-- A structure map `ψⱼₖ : F(ξⱼ) ⟶ G(ξₖ) for all `j < k ≤ i`.
  In particular, this bundles a map `F(ξᵢ₋₁) ⟶ G(ξᵢ)` when indices allow it. -/
  ψ (j k : Λ) (hj : j < k := by valid) (hk : k ≤ i := by valid) :
    F.obj (ξ.obj (iic% j i)).left.obj ⟶ G.obj (ξ.obj (iic% k i)).left.obj
  sq₁ (j : Λ) (hj : j < i := by valid) :
    ψ j i ≫ G.map (ξ.obj (iic% i i)).hom = F.map (ξ.obj (iic% j i)).hom ≫ E.hom
  t₁ (j k l : Λ) (hjk : j ≤ k := by valid) (hkl : k < l := by valid) (hl : l ≤ i := by valid) :
    ψ j l = F.map (ξ.map (homOfLE hjk)).left.hom ≫ ψ k l
  t₂ (j k l : Λ) (hjk : j < k := by valid) (hkl : k ≤ l := by valid) (hl : l ≤ i := by valid) :
    ψ j l = ψ j k ≫ G.map (ξ.map (homOfLE hkl)).left.hom

variable (Λ : Type*)

namespace PartialChainUpTo

open Order (succ)

variable [LinearOrder Λ] [SuccOrder Λ]

lemma eqToHom_ext {E : Inserter F G} {i : Λ} {b b' : PartialChainUpTo κ Λ E i}
    (h_obj : ∀ (j : Set.Iic i), b.ξ.obj j = b'.ξ.obj j)
    (h_map : ∀ (j k : Λ) (hjk : j ≤ k) (hki : k ≤ i),
      b.ξ.map (homOfLE hjk : iic% j i ⟶ iic% k i) =
      eqToHom (h_obj _) ≫ b'.ξ.map (homOfLE hjk) ≫ eqToHom (h_obj _).symm)
    (h_ψ : ∀ (j k : Λ) (hjk : j < k) (hki : k ≤ i),
      b.ψ j k = F.map (eqToHom (congr($(h_obj _).left.obj))) ≫ b'.ψ j k ≫
        G.map (eqToHom (congr($(h_obj _).left.obj)).symm)) :
    b = b' := by
  ext
  · exact Functor.ext h_obj (fun j k f ↦ h_map j.val k.val (leOfHom f) k.property)
  · refine Function.hfunext rfl fun a a' haa' ↦
      Function.hfunext rfl fun b b' hbb' ↦  ?_
    rw [heq_iff_eq] at haa' hbb'
    subst haa' hbb'
    refine Function.hfunext rfl fun _ _ _ ↦ Function.hfunext rfl fun _ _ _ ↦ ?_
    simp (discharger := valid) [h_ψ, eqToHom_map]

lemma congr_ψ {E : Inserter F G} {i : Λ} {b b' : PartialChainUpTo κ Λ E i}
    (h : b = b') (j k : Λ) (hjk : j < k := by valid) (hki : k ≤ i := by valid) :
    b.ψ j k = F.map (eqToHom congr((($h).ξ.obj _).left.obj)) ≫ b'.ψ j k hjk hki ≫
      G.map (eqToHom congr((($h).ξ.obj _).left.obj).symm) := by
  subst h
  simp

lemma sq₂ {i : Λ} {E : Inserter F G} (d : PartialChainUpTo κ Λ E i)
    (j k l m : Λ)
    (hjk : j < k := by valid) (hkm : k ≤ m := by valid) (hjl : j ≤ l := by valid)
    (hlm : l < m := by valid) (hm : m ≤ i := by valid) :
    F.map (d.ξ.map (homOfLE hjl)).left.hom ≫ d.ψ l m =
    d.ψ j k ≫ G.map (d.ξ.map (homOfLE hkm)).left.hom := by
  rw [← d.t₂ j k m, ← d.t₁ j l m]

/-- Restricts a PartialChainUpTo to a lower index, turning PartialChainUpTo into a presheaf. -/
@[implicit_reducible]
def trunc (E : Inserter F G)
    {i i' : Λ} (hii' : i ≤ i') (d : PartialChainUpTo κ Λ E i') :
    PartialChainUpTo κ Λ E i where
  ξ := SmallObject.restrictionLE d.ξ hii'
  ψ j k hjk hk := d.ψ j k
  sq₁ j hj := by
    have := d.sq₁ j |>.symm
    obtain rfl | hii' := hii'.eq_or_lt
    · exact this.symm
    · dsimp
      rw [this]
      grind [→ @d.t₂]
  t₁ j k l hjk hkl hl := d.t₁ j k l
  t₂ j k l hjk hkl hl := d.t₂ j k l

/-- Turning `i ↦ PartialChainUpTo κ Λ E i` into a functor. A section of this functor bundles an
extension of the ξ and ψ fields to all indices in Λ. -/
abbrev functor (E : Inserter F G) : Λᵒᵖ ⥤ Type _ where
  obj i := PartialChainUpTo κ Λ E i.unop
  map f := TypeCat.ofHom <| trunc κ Λ E (leOfHom f.unop)

/- TODOs (@robin-carlier):
  - Provide lemmas to satisfy `Functor.WellOrderInductionData.ofExists` for functor above.
  - Prove Lemma 4.5 of [positselski2024] using this
  - Use the lemma to show that given an inserter E, the canonical functor
    ```
      CostructuredArrow ((isCardinalPresentable K κ).inverseImage (Inserter.proj F G)).ι E ⥤
        CostructuredArrow (isCardinalPresentable K κ).ι E.obj
    ```
    is final and that its source category is κ-filtered
-/

end PartialChainUpTo

end CategoryTheory.Inserter.Accessible
