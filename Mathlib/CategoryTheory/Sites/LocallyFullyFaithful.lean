/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Locally fully faithful functors into sites

## Main results

- `CategoryTheory.Functor.IsLocallyFull`:
  A functor `G : C ⥤ D` is locally full w.r.t. a topology on `D` if for every
  `f : G.obj U ⟶ G.obj V`, the set of `G.map fᵢ : G.obj Wᵢ ⟶ G.obj U` such that `G.map fᵢ ≫ f` is
  in the image of `G` is a coverage of the topology on `D`.
- `CategoryTheory.Functor.IsLocallyFaithful`:
  A functor `G : C ⥤ D` is locally faithful w.r.t. a topology on `D` if for every `f₁ f₂ : U ⟶ V`
  whose images in `D` are equal, the set of `G.map gᵢ : G.obj Wᵢ ⟶ G.obj U` such that
  `gᵢ ≫ f₁ = gᵢ ≫ f₂` is a coverage of the topology on `D`.

## References

* [caramello2020]: Olivia Caramello, *Denseness conditions, morphisms and equivalences of toposes*

-/

universe w vC vD uC uD

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D] (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/--
For a functor `G : C ⥤ D`, and a morphism `f : G.obj U ⟶ G.obj V`,
`Functor.imageSieve G f` is the sieve of `U`
consisting of those arrows whose composition with `f` has a lift in `G`.

This is the image sieve of `f` under `yonedaMap G V` and hence the name.
See `Functor.imageSieve_eq_imageSieve`.
-/
def Functor.imageSieve {U V : C} (f : G.obj U ⟶ G.obj V) : Sieve U where
  arrows _ i := ∃ l, G.map l = G.map i ≫ f
  downward_closed := by
    rintro Y₁ Y₂ i₁ ⟨l, hl⟩ i₂
    exact ⟨i₂ ≫ l, by simp [hl]⟩

@[simp]
lemma Functor.imageSieve_map {U V : C} (f : U ⟶ V) : G.imageSieve (G.map f) = ⊤ := by
  ext W g; simpa using ⟨g ≫ f, by simp⟩

/--
For two arrows `f₁ f₂ : U ⟶ V`, the arrows `i` such that `i ≫ f₁ = i ≫ f₂` forms a sieve.
-/
@[simps]
def Sieve.equalizer {U V : C} (f₁ f₂ : U ⟶ V) : Sieve U where
  arrows _ i := i ≫ f₁ = i ≫ f₂
  downward_closed := by aesop

@[simp]
lemma Sieve.equalizer_self {U V : C} (f : U ⟶ V) : equalizer f f = ⊤ := by ext; simp

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
lemma Sieve.equalizer_eq_equalizerSieve {U V : C} (f₁ f₂ : U ⟶ V) :
    Sieve.equalizer f₁ f₂ = Presheaf.equalizerSieve (F := yoneda.obj _) f₁ f₂ := rfl

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
lemma Functor.imageSieve_eq_imageSieve {D : Type uD} [Category.{vC} D] (G : C ⥤ D) {U V : C}
    (f : G.obj U ⟶ G.obj V) :
    G.imageSieve f = Presheaf.imageSieve (yonedaMap G V) f := rfl

open Presieve Opposite

namespace Functor

/--
A functor `G : C ⥤ D` is locally full w.r.t. a topology on `D` if for every `f : G.obj U ⟶ G.obj V`,
the set of `G.map fᵢ : G.obj Wᵢ ⟶ G.obj U` such that `G.map fᵢ ≫ f` is
in the image of `G` is a coverage of the topology on `D`.
-/
class IsLocallyFull : Prop where
  functorPushforward_imageSieve_mem : ∀ {U V} (f : G.obj U ⟶ G.obj V),
    (G.imageSieve f).functorPushforward G ∈ K _

/--
A functor `G : C ⥤ D` is locally faithful w.r.t. a topology on `D` if for every `f₁ f₂ : U ⟶ V`
whose images in `D` are equal, the set of `G.map gᵢ : G.obj Wᵢ ⟶ G.obj U` such that
`gᵢ ≫ f₁ = gᵢ ≫ f₂` is a coverage of the topology on `D`.
-/
class IsLocallyFaithful : Prop where
  functorPushforward_equalizer_mem : ∀ {U V : C} (f₁ f₂ : U ⟶ V), G.map f₁ = G.map f₂ →
    (Sieve.equalizer f₁ f₂).functorPushforward G ∈ K _

lemma functorPushforward_imageSieve_mem [G.IsLocallyFull K] {U V} (f : G.obj U ⟶ G.obj V) :
    (G.imageSieve f).functorPushforward G ∈ K _ :=
  Functor.IsLocallyFull.functorPushforward_imageSieve_mem _

lemma functorPushforward_equalizer_mem
    [G.IsLocallyFaithful K] {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂) :
      (Sieve.equalizer f₁ f₂).functorPushforward G ∈ K _ :=
  Functor.IsLocallyFaithful.functorPushforward_equalizer_mem _ _ e

variable {K}
variable {A : Type*} [Category A] (G : C ⥤ D)

theorem IsLocallyFull.ext [G.IsLocallyFull K]
    (ℱ : Sheaf K (Type _)) {X Y : C} (i : G.obj X ⟶ G.obj Y)
    {s t : ℱ.val.obj (op (G.obj X))}
    (h : ∀ ⦃Z : C⦄ (j : Z ⟶ X) (f : Z ⟶ Y), G.map f = G.map j ≫ i →
      ℱ.1.map (G.map j).op s = ℱ.1.map (G.map j).op t) : s = t := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.cond) _
    (G.functorPushforward_imageSieve_mem K i)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, ⟨iWY, e⟩, rfl⟩
  simp [h iWX iWY e]

theorem IsLocallyFaithful.ext [G.IsLocallyFaithful K] (ℱ : Sheaf K (Type _))
    {X Y : C} (i₁ i₂ : X ⟶ Y) (e : G.map i₁ = G.map i₂)
    {s t : ℱ.val.obj (op (G.obj X))}
    (h : ∀ ⦃Z : C⦄ (j : Z ⟶ X), j ≫ i₁ = j ≫ i₂ →
      ℱ.1.map (G.map j).op s = ℱ.1.map (G.map j).op t) : s = t := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).1 ℱ.cond) _
    (G.functorPushforward_equalizer_mem K i₁ i₂ e)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, hiWX, rfl⟩
  simp [h iWX hiWX]

instance (priority := 900) IsLocallyFull.of_full [G.Full] : G.IsLocallyFull K where
  functorPushforward_imageSieve_mem f := by
    rw [← G.map_preimage f]
    simp only [Functor.imageSieve_map, Sieve.functorPushforward_top, GrothendieckTopology.top_mem]

instance (priority := 900) IsLocallyFaithful.of_faithful [G.Faithful] : G.IsLocallyFaithful K where
  functorPushforward_equalizer_mem f₁ f₂ e := by obtain rfl := G.map_injective e; simp

end CategoryTheory.Functor
