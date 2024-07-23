/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-!
# Locally fully faithful functors into sites

## Main results

- `CategoryTheory.Functor.IsLocallyFull`:
  A functor `G : C ⥤ D` is locally full wrt a topology on `D` if for every `f : G.obj U ⟶ G.obj V`,
  the set of `G.map fᵢ : G.obj Wᵢ ⟶ G.obj U` such that `G.map fᵢ ≫ f` is
  in the image of `G` is a coverage of the topology on `D`.
- `CategoryTheory.Functor.IsLocallyFaithful`:
  A functor `G : C ⥤ D` is locally faithful wrt a topology on `D` if for every `f₁ f₂ : U ⟶ V` whose
  image in `D` are equal, the set of `G.map gᵢ : G.obj Wᵢ ⟶ G.obj U` such that `gᵢ ≫ f₁ = gᵢ ≫ f₂`
  is a coverage of the topology on `D`.

## References

* https://arxiv.org/pdf/1906.08737

-/

universe w v u

namespace CategoryTheory

variable {C : Type*} [Category C] {D : Type*} [Category D] {E : Type*} [Category E] (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)
variable {L : GrothendieckTopology E}

/--
For a functor `G : C ⥤ D`, and an morphism `f : G.obj U ⟶ G.obj V`,
`Sieve.hasLift G f` is the sieve of `U`
consisting of those arrows whose composition with `f` has a lift in `G`.
-/
def Sieve.hasLift {U V : C} (f : G.obj U ⟶ G.obj V) : Sieve U where
  arrows Y i := ∃ l, G.map l = G.map i ≫ f
  downward_closed := by
    rintro Y₁ Y₂ i₁ ⟨l, hl⟩ i₂
    exact ⟨i₂ ≫ l, by simp [hl]⟩

@[simp]
lemma Sieve.hasLift_map {U V : C} (f : U ⟶ V) : hasLift G (G.map f) = ⊤ := by
  ext W g; simpa using ⟨g ≫ f, by simp⟩

/--
For two arrows `f₁ f₂ : U ⟶ V`, the arrows `i` such that `i ≫ f₁ = i ≫ f₂` forms a sieve.
-/
@[simps]
def Sieve.equalizer {U V : C} (f₁ f₂ : U ⟶ V) : Sieve U where
  arrows Y i := i ≫ f₁ = i ≫ f₂
  downward_closed := by aesop

@[simp]
lemma Sieve.equalizer_self {U V : C} (f : U ⟶ V) : equalizer f f = ⊤ := by ext; simp

open Presieve Opposite

namespace Functor

/--
A functor `G : C ⥤ D` is locally full wrt a topology on `D` if for every `f : G.obj U ⟶ G.obj V`,
the set of `G.map fᵢ : G.obj Wᵢ ⟶ G.obj U` such that `G.map fᵢ ≫ f` is
in the image of `G` is a coverage of the topology on `D`.
-/
class IsLocallyFull : Prop where
  functorPushforward_hasLift_mem : ∀ {U V} (f : G.obj U ⟶ G.obj V),
    (Sieve.hasLift G f).functorPushforward G ∈ K _

/--
A functor `G : C ⥤ D` is locally faithful wrt a topology on `D` if for every `f₁ f₂ : U ⟶ V` whose
image in `D` are equal, the set of `G.map gᵢ : G.obj Wᵢ ⟶ G.obj U` such that `gᵢ ≫ f₁ = gᵢ ≫ f₂`
is a coverage of the topology on `D`.
-/
class IsLocallyFaithful : Prop where
  functorPushforward_equalizer_mem : ∀ {U V : C} (f₁ f₂ : U ⟶ V), G.map f₁ = G.map f₂ →
    (Sieve.equalizer f₁ f₂).functorPushforward G ∈ K _

lemma functorPushforward_hasLift_mem [G.IsLocallyFull K] {U V} (f : G.obj U ⟶ G.obj V) :
    (Sieve.hasLift G f).functorPushforward G ∈ K _ :=
  Functor.IsLocallyFull.functorPushforward_hasLift_mem _

lemma functorPushforward_equalizer_mem
    [G.IsLocallyFaithful K] {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = G.map f₂) :
      (Sieve.equalizer f₁ f₂).functorPushforward G ∈ K _ :=
  Functor.IsLocallyFaithful.functorPushforward_equalizer_mem _ _ e

variable {K}
variable {A : Type*} [Category A] (G : C ⥤ D)

theorem IsLocallyFull.ext [G.IsLocallyFull K]
    (ℱ : SheafOfTypes K) {X Y : C} (i : G.obj X ⟶ G.obj Y)
    {s t : ℱ.val.obj (op (G.obj X))}
    (h : ∀ ⦃Z : C⦄ (j : Z ⟶ X) (f : Z ⟶ Y), G.map f = G.map j ≫ i →
      ℱ.1.map (G.map j).op s = ℱ.1.map (G.map j).op t) : s = t := by
  apply (ℱ.cond _ (G.functorPushforward_hasLift_mem K i)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, ⟨iWY, e⟩, rfl⟩
  simp [h iWX iWY e]

theorem IsLocallyFaithful.ext [G.IsLocallyFaithful K] (ℱ : SheafOfTypes K)
    {X Y : C} (i₁ i₂ : X ⟶ Y) (e : G.map i₁ = G.map i₂)
    {s t : ℱ.val.obj (op (G.obj X))}
    (h : ∀ ⦃Z : C⦄ (j : Z ⟶ X), j ≫ i₁ = j ≫ i₂ →
      ℱ.1.map (G.map j).op s = ℱ.1.map (G.map j).op t) : s = t := by
  apply (ℱ.cond _ (G.functorPushforward_equalizer_mem K i₁ i₂ e)).isSeparatedFor.ext
  rintro Z _ ⟨W, iWX, iZW, hiWX, rfl⟩
  simp [h iWX hiWX]

instance (priority := 900) IsLocallyFull.of_full [G.Full] : G.IsLocallyFull K where
  functorPushforward_hasLift_mem f := by
    rw [← G.map_preimage f]
    simp only [Sieve.hasLift_map, Sieve.functorPushforward_top, GrothendieckTopology.top_mem]

instance (priority := 900) IsLocallyFaithful.of_faithful [G.Faithful] : G.IsLocallyFaithful K where
  functorPushforward_equalizer_mem f₁ f₂ e := by obtain rfl := G.map_injective e; simp

end CategoryTheory.Functor
