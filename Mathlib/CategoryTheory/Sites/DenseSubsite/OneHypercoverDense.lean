/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Equivalence of categories of sheaves with a dense subsite that is 1-hypercover dense

Let `F : C₀ ⥤ C` be a functor equipped with Grothendieck topologies `J₀` and `J`.
Assume that `F` is a dense subsite. We introduce a typeclass
`IsOneHypercoverDense.{w} F J₀ J` which roughly says that objects in `C`
admit a `1`-hypercover consisting of objects in `C₀`.

-/

@[expose] public section

universe w v₀ v v' u₀ u u'

namespace CategoryTheory

open Category Limits Opposite

variable {C₀ : Type u₀} {C : Type u} [Category.{v₀} C₀] [Category.{v} C]

namespace Functor

variable (F : C₀ ⥤ C) (J₀ : GrothendieckTopology C₀)
  (J : GrothendieckTopology C) {A : Type u'} [Category.{v'} A]

/-- Given a functor `F : C₀ ⥤ C` and an object `S : C`, this structure roughly
contains the data of a pre-`1`-hypercover of `S` consisting of objects in `C₀`. -/
structure PreOneHypercoverDenseData (S : C) where
  /-- the index type of the covering of `S` -/
  I₀ : Type w
  /-- the objects in the covering of `S` -/
  X (i : I₀) : C₀
  /-- the morphisms in the covering of `S` -/
  f (i : I₀) : F.obj (X i) ⟶ S
  /-- the index type of the coverings of the fibre products -/
  I₁ (i₁ i₂ : I₀) : Type w
  /-- the objects in the coverings of the fibre products -/
  Y ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : C₀
  /-- the first projection `Y j ⟶ X i₁` -/
  p₁ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
  /-- the second projection `Y j ⟶ X i₂` -/
  p₂ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
  w ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : F.map (p₁ j) ≫ f i₁ = F.map (p₂ j) ≫ f i₂

namespace PreOneHypercoverDenseData

attribute [reassoc] w

variable {F} {X : C} (data : PreOneHypercoverDenseData.{w} F X)

/-- The pre-`1`-hypercover induced by a `PreOneHypercoverDenseData` structure. -/
@[simps]
def toPreOneHypercover : PreOneHypercover X where
  I₀ := data.I₀
  X i := F.obj (data.X i)
  f i := data.f i
  I₁ := data.I₁
  Y _ _ j := F.obj (data.Y j)
  p₁ _ _ j := F.map (data.p₁ j)
  p₂ _ _ j := F.map (data.p₂ j)
  w := data.w

/-- The sigma type of all `data.I₁ i₁ i₂` for `⟨i₁, i₂⟩ : data.I₀ × data.I₀`. -/
abbrev I₁' : Type w := Sigma (fun (i : data.I₀ × data.I₀) ↦ data.I₁ i.1 i.2)

/-- The shape of the multiforks attached to `data : F.PreOneHypercoverDenseData X`. -/
@[simps]
def multicospanShape : MulticospanShape where
  L := data.I₀
  R := data.I₁'
  fst j := j.1.1
  snd j := j.1.2

/-- The diagram of the multiforks attached to `data : F.PreOneHypercoverDenseData X`. -/
@[simps]
def multicospanIndex (P : C₀ᵒᵖ ⥤ A) : MulticospanIndex data.multicospanShape A where
  left i := P.obj (Opposite.op (data.X i))
  right j := P.obj (Opposite.op (data.Y j.2))
  fst j := P.map ((data.p₁ j.2).op)
  snd j := P.map ((data.p₂ j.2).op)

/-- The functoriality of the diagrams attached to `data : F.PreOneHypercoverDenseData X`
with respect to morphisms in `C₀ᵒᵖ ⥤ A`. -/
@[simps]
def multicospanMap {P Q : C₀ᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (data.multicospanIndex P).multicospan ⟶ (data.multicospanIndex Q).multicospan where
  app x := match x with
    | WalkingMulticospan.left i => f.app _
    | WalkingMulticospan.right j => f.app _
  naturality := by
    rintro (i₁|j₁) (i₂|j₂) (_|_)
    all_goals simp

/-- The natural isomorphism between the diagrams attached to `data : F.PreOneHypercoverDenseData X`
that are induced by isomorphisms in `C₀ᵒᵖ ⥤ A`. -/
@[simps]
def multicospanMapIso {P Q : C₀ᵒᵖ ⥤ A} (e : P ≅ Q) :
    (data.multicospanIndex P).multicospan ≅ (data.multicospanIndex Q).multicospan where
  hom := data.multicospanMap e.hom
  inv := data.multicospanMap e.inv

/-- Given `data : F.PreOneHypercoverDenseData X`, an object `W₀ : C₀` and two
morphisms `p₁ : W₀ ⟶ data.X i₁` and `p₂ : W₀ ⟶ data.X i₂`, this is the sieve of `W₀`
consisting of morphisms `g : Z₀ ⟶ W₀` such that there exists a morphism `Z₀ ⟶ data.Y j`
such that `g ≫ p₁ = h ≫ data.p₁ j` and `g ≫ p₂ = h ≫ data.p₂ j`. -/
@[simps]
def sieve₁₀ {i₁ i₂ : data.I₀} {W₀ : C₀} (p₁ : W₀ ⟶ data.X i₁) (p₂ : W₀ ⟶ data.X i₂) :
    Sieve W₀ where
  arrows Z₀ g := ∃ (j : data.I₁ i₁ i₂) (h : Z₀ ⟶ data.Y j),
    g ≫ p₁ = h ≫ data.p₁ j ∧ g ≫ p₂ = h ≫ data.p₂ j
  downward_closed := by
    rintro Z Z' g ⟨j, h, fac₁, fac₂⟩ φ
    exact ⟨j, φ ≫ h, by simpa using φ ≫= fac₁, by simpa using φ ≫= fac₂⟩

end PreOneHypercoverDenseData

/-- Given a functor `F : C₀ ⥤ C`, Grothendieck topologies `J₀` on `C₀` and `J`
on `C`, an object `S. : C`, this structure roughly contains the data of a `1`-hypercover
of `S` consisting of objects in `C₀`. -/
structure OneHypercoverDenseData (S : C) extends PreOneHypercoverDenseData.{w} F S where
  mem₀ : toPreOneHypercoverDenseData.toPreOneHypercover.sieve₀ ∈ J S
  mem₁₀ (i₁ i₂ : I₀) ⦃W₀ : C₀⦄ (p₁ : W₀ ⟶ X i₁) (p₂ : W₀ ⟶ X i₂)
    (w : F.map p₁ ≫ f i₁ = F.map p₂ ≫ f i₂) :
    toPreOneHypercoverDenseData.sieve₁₀ p₁ p₂ ∈ J₀ W₀

/-- Given a functor `F : C₀ ⥤ C`, Grothendieck topologies `J₀` on `C₀`, this is
the property that any object in `C` has a `1`-hypercover consisting of objects in `C₀`. -/
class IsOneHypercoverDense : Prop where
  nonempty_oneHypercoverDenseData (X : C) :
    Nonempty (OneHypercoverDenseData.{w} F J₀ J X)

section

variable [IsOneHypercoverDense.{w} F J₀ J]

/-- A choice of a `OneHypercoverDenseData` structure when `F` is `1`-hypercover dense. -/
noncomputable def oneHypercoverDenseData (X : C) : F.OneHypercoverDenseData J₀ J X :=
  (IsOneHypercoverDense.nonempty_oneHypercoverDenseData X).some

lemma isDenseSubsite_of_isOneHypercoverDense [F.IsLocallyFull J] [F.IsLocallyFaithful J]
    (h : ∀ {X₀ : C₀} {S₀ : Sieve X₀},
      Sieve.functorPushforward F S₀ ∈ J.sieves (F.obj X₀) ↔ S₀ ∈ J₀.sieves X₀) :
    IsDenseSubsite J₀ J F where
  isCoverDense' := ⟨fun X ↦ by
    refine J.superset_covering ?_ (F.oneHypercoverDenseData J₀ J X).mem₀
    rintro Y _ ⟨_, a, _, h, rfl⟩
    cases h
    exact ⟨{ fac := rfl, ..}⟩⟩
  functorPushforward_mem_iff := h

end

end Functor

end CategoryTheory
