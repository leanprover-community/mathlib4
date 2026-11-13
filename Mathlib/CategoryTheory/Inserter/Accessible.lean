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

namespace Accessible

variable {K L : Type*} [Category* K] [Category* L] {F G : K ⥤ L} (κ : Cardinal.{w})
    [Fact κ.IsRegular]

/-- If the underlying object of an inserter `X` is κ-presentable, then `X` is κ-presentable. -/
public instance (X : Inserter F G)
    [IsCardinalPresentable X.obj κ]
    [IsCardinalAccessibleCategory K κ] [IsCardinalAccessibleCategory L κ]
    [F.IsCardinalAccessible κ] [G.IsCardinalAccessible κ] [F.PreservesCardinalPresentable κ] :
    IsCardinalPresentable X κ := by
  apply IsCardinalPresentable.mk
  intro I _ _ B b hb
  have : Limits.HasColimitsOfShape I K := HasCardinalFilteredColimits.hasColimitsOfShape _ κ I
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
where u : S → T and v : T ⟶ K are maps of κ-presentable objects, one can find a factorization
```
F(S) --> F(T) ---> F(U) --> F(K)
 |          F(v')   | σ      | Φ
 v                  v        v
G(T) ------------> G(U) --> F(K)
         G(v')
```

The main technical ingredient is that if one uses κ-presentability naively, one
only produces a diagram of the shape

```
F(S) --> F(T) ---> F(ξ₀) --> F(K)
 |          F(v')   | ψ₀       | Φ
 v                  v          v
G(T) ------------> G(ξ₁) --> F(K)
```

To turn the middle vertical map into an inserter, one must iterate the construction of such diagrams
to construct a chain `U₀ ⟶ U₁ ⟶ …` by transfinite induction, equipped with natural structure maps
`ψᵢ : F(ξᵢ) ⟶ G(ξᵢ₊₁)`.
Once the chain becomes long enough, one can take its colimit to stabilize those maps:
the ordinal Λ that appears in the hypothesis of the main theorem quantifies this "long enough".

Setting up and carrying out this transfinite induction occupies most of the material below,
the strategy is to encode the partial stages of the induction as a presheaf of type
(`PartialChainUpTo.functor` below) and to record the induction
steps as a `Functor.WellOrderInductionData`, which will let us extract a section
of the presheaf from which we can extract the desired chain. -/

/-- A structure that encodes the chain to be constructed
Lemma 4.5 of [positselski2024].

To realize the induction, we transform `j ↦ PartialChainUpTo … j` into a
presheaf on `j` so that we can use `Functor.WellOrderInductionData`.
From a section of the presheaf, we can extract the chain out of `Λ` that we are looking for. -/
@[ext]
structure PartialChainUpTo (Λ : Type*) [Preorder Λ] [SuccOrder Λ]
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


/-- A small helper that powers up some `simp` and `grind` calls troughout the file -/
@[simp, grind =]
lemma helper {K : Type*} [Category* K] {P : ObjectProperty K} {X : K}
    {x y : CostructuredArrow P.ι X} (f : x ⟶ y) :
    f.left.hom ≫ y.hom = x.hom := by
  simpa using f.w

variable (Λ : Type*)

namespace PartialChainUpTo

open Order (succ)

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

lemma sq₂ {i : Λ} {E : Inserter F G} (d : PartialChainUpTo κ Λ E i)
    (j k l m : Λ) (hjk : j < k) (hkm : k ≤ m) (hjl : j ≤ l) (hlm : l < m) (hm : m ≤ i) :
    F.map (d.ξ.map (homOfLE hjl)).left.hom ≫ d.ψ l m hlm (by valid) =
    d.ψ j k hjk (by valid) ≫ G.map (d.ξ.map (homOfLE hkm)).left.hom := by
  rw [← d.t₂, ← d.t₁]
  grind

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
