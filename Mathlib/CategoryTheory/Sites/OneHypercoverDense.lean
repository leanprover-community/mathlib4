/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.DenseSubsite

/-!
# Equivalence of category of sheaves with a dense subsite that is 1-hypercover dense

-/

universe w v₀ v v' u₀ u u'

namespace CategoryTheory

open Category Limits Opposite

variable {C₀ : Type u₀} {C : Type u} [Category.{v₀} C₀] [Category.{v} C]

namespace Sieve

variable {I : Type*} {X : C} {Y : I → C} {f : ∀ i, Y i ⟶ X} {W : C} {g : W ⟶ X}
  (hg : ofArrows Y f g)

include hg in
lemma ofArrows.exists : ∃ (i : I) (h : W ⟶ Y i), g = h ≫ f i := by
  obtain ⟨_, h, _, H, rfl⟩ := hg
  cases' H with i
  exact ⟨i, h, rfl⟩

noncomputable def ofArrows.i : I := (ofArrows.exists hg).choose
noncomputable def ofArrows.h : W ⟶ Y (i hg) := (ofArrows.exists hg).choose_spec.choose
@[reassoc]
lemma ofArrows.fac : g = h hg ≫ f (i hg) :=
  (ofArrows.exists hg).choose_spec.choose_spec

end Sieve

namespace Functor

variable (F : C₀ ⥤ C) (J₀ : GrothendieckTopology C₀)
  (J : GrothendieckTopology C) {A : Type u'} [Category.{v'} A]

structure PreOneHypercoverDenseData (S : C) where
  I₀ : Type w
  X (i : I₀) : C₀
  f (i : I₀) : F.obj (X i) ⟶ S
  I₁ (i₁ i₂ : I₀) : Type w
  Y ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : C₀
  p₁ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
  p₂ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
  w ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : F.map (p₁ j) ≫ f i₁ = F.map (p₂ j) ≫ f i₂

namespace PreOneHypercoverDenseData

attribute [reassoc] w

variable {F}

variable {X : C} (data : F.PreOneHypercoverDenseData X)

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
abbrev I₁' : Type w := Sigma (fun (i : data.I₀ × data.I₀) => data.I₁ i.1 i.2)

@[simps]
def multicospanIndex (P : C₀ᵒᵖ ⥤ A) : MulticospanIndex A where
  L := data.I₀
  R := data.I₁'
  fstTo j := j.1.1
  sndTo j := j.1.2
  left i := P.obj (Opposite.op (data.X i))
  right j := P.obj (Opposite.op (data.Y j.2))
  fst j := P.map ((data.p₁ j.2).op)
  snd j := P.map ((data.p₂ j.2).op)

@[simps]
def multicospanMap {P Q : C₀ᵒᵖ ⥤ A} (f : P ⟶ Q) :
    (data.multicospanIndex P).multicospan ⟶ (data.multicospanIndex Q).multicospan where
  app x := match x with
    | WalkingMulticospan.left i => f.app _
    | WalkingMulticospan.right j => f.app _
  naturality := by
    rintro (i₁|j₁) (i₂|j₂) (_|_)
    all_goals simp

@[simps]
def multicospanMapIso {P Q : C₀ᵒᵖ ⥤ A} (e : P ≅ Q) :
    (data.multicospanIndex P).multicospan ≅ (data.multicospanIndex Q).multicospan where
  hom := data.multicospanMap e.hom
  inv := data.multicospanMap e.inv

@[simps]
def sieve₁₀ {i₁ i₂ : data.I₀} {W₀ : C₀} (p₁ : W₀ ⟶ data.X i₁) (p₂ : W₀ ⟶ data.X i₂) :
    Sieve W₀ where
  arrows Z₀ g := ∃ (j : data.I₁ i₁ i₂) (h : Z₀ ⟶ data.Y j),
    g ≫ p₁ = h ≫ data.p₁ j ∧ g ≫ p₂ = h ≫ data.p₂ j
  downward_closed := by
    rintro Z Z' g ⟨j, h, fac₁, fac₂⟩ φ
    exact ⟨j, φ ≫ h, by simpa using φ ≫= fac₁, by simpa using φ ≫= fac₂⟩

end PreOneHypercoverDenseData

structure OneHypercoverDenseData (S : C) extends PreOneHypercoverDenseData.{w} F S where
  mem₀ : toPreOneHypercoverDenseData.toPreOneHypercover.sieve₀ ∈ J S
  mem₁₀ (i₁ i₂ : I₀) ⦃W₀ : C₀⦄ (p₁ : W₀ ⟶ X i₁) (p₂ : W₀ ⟶ X i₂)
    (w : F.map p₁ ≫ f i₁ = F.map p₂ ≫ f i₂) :
    toPreOneHypercoverDenseData.sieve₁₀ p₁ p₂ ∈ J₀ W₀

class IsOneHypercoverDense : Prop where
  nonempty_oneHypercoverDenseData (X : C) :
    Nonempty (OneHypercoverDenseData.{w} F J₀ J X)

section

variable [IsOneHypercoverDense.{w} F J₀ J]

noncomputable def oneHypercoverDenseData (X : C) : F.OneHypercoverDenseData J₀ J X :=
  (IsOneHypercoverDense.nonempty_oneHypercoverDenseData X).some

lemma isDenseSubsite_of_isOneHypercoverDense [F.IsLocallyFull J] [F.IsLocallyFaithful J]
    (h : ∀ {X₀ : C₀} {S₀ : Sieve X₀},
      Sieve.functorPushforward F S₀ ∈ J.sieves (F.obj X₀) ↔ S₀ ∈ J₀.sieves X₀) :
    IsDenseSubsite J₀ J F where
  isCoverDense' := ⟨fun X ↦ by
    refine J.superset_covering ?_ ((F.oneHypercoverDenseData J₀ J X).mem₀)
    rintro Y _ ⟨_, a, _, h, rfl⟩
    cases' h with i
    exact ⟨{ fac := rfl}⟩⟩
  functorPushforward_mem_iff := h

end

variable [IsDenseSubsite J₀ J F]

namespace OneHypercoverDenseData

variable {F J₀ J}

section

variable {X : C} (data : F.OneHypercoverDenseData J₀ J X)

lemma mem₁ (i₁ i₂ : data.I₀) {W : C} (p₁ : W ⟶ F.obj (data.X i₁)) (p₂ : W ⟶ F.obj (data.X i₂))
    (w : p₁ ≫ data.f i₁ = p₂ ≫ data.f i₂) : data.toPreOneHypercover.sieve₁ p₁ p₂ ∈ J W := by
  have := IsDenseSubsite.isCoverDense J₀ J F
  let S := Sieve.bind (Sieve.coverByImage F W).arrows
    (fun Y f hf ↦ ((F.imageSieve (hf.some.map ≫ p₁) ⊓
        F.imageSieve (hf.some.map ≫ p₂)).functorPushforward F).pullback hf.some.lift)
  let T := Sieve.bind S.arrows (fun Z g hg ↦ by
    letI str := Presieve.getFunctorPushforwardStructure (Presieve.bindStruct hg).hg
    exact Sieve.pullback str.lift
      (Sieve.functorPushforward F (data.sieve₁₀ str.cover.1.choose str.cover.2.choose)))
  have hS : S ∈ J W := by
    apply J.bind_covering
    · apply is_cover_of_isCoverDense
    · intro Y f hf
      apply J.pullback_stable
      rw [Functor.functorPushforward_mem_iff J₀]
      apply J₀.intersection_covering
      all_goals apply IsDenseSubsite.imageSieve_mem J₀ J
  have hT : T ∈ J W := J.bind_covering hS (fun Z g hg ↦ by
    apply J.pullback_stable
    rw [Functor.functorPushforward_mem_iff J₀]
    let str := Presieve.getFunctorPushforwardStructure (Presieve.bindStruct hg).hg
    apply data.mem₁₀
    simp only [str.cover.1.choose_spec, str.cover.2.choose_spec, assoc, w])
  refine J.superset_covering ?_ hT
  rintro U f ⟨V, a, b, hb, h, _, rfl⟩
  let str := Presieve.getFunctorPushforwardStructure (Presieve.bindStruct hb).hg
  obtain ⟨W₀, c : _ ⟶ _, d, ⟨j, e, h₁, h₂⟩, fac⟩ := h
  dsimp
  refine ⟨j, d ≫ F.map e, ?_, ?_⟩
  · rw [assoc, assoc, ← F.map_comp, ← h₁, F.map_comp, ← reassoc_of% fac,
      str.cover.1.choose_spec, ← reassoc_of% str.fac,
      Presieve.CoverByImageStructure.fac_assoc,
      Presieve.BindStruct.fac_assoc]
  · rw [assoc, assoc, ← F.map_comp, ← h₂, F.map_comp, ← reassoc_of% fac,
      str.cover.2.choose_spec, ← reassoc_of% str.fac,
      Presieve.CoverByImageStructure.fac_assoc,
      Presieve.BindStruct.fac_assoc]

@[simps toPreOneHypercover]
def toOneHypercover {X : C} (data : F.OneHypercoverDenseData J₀ J X) :
    J.OneHypercover X where
  toPreOneHypercover := data.toPreOneHypercover
  mem₀ := data.mem₀
  mem₁ := data.mem₁

variable {X : C} (data : F.OneHypercoverDenseData J₀ J X) {X₀ : C₀} (f : F.obj X₀ ⟶ X)

structure SieveStruct {Y₀ : C₀} (g : Y₀ ⟶ X₀) where
  i₀ : data.I₀
  q : Y₀ ⟶ data.X i₀
  fac : F.map q ≫ data.f i₀ = F.map g ≫ f := by simp

attribute [reassoc (attr := simp)] SieveStruct.fac

@[simps]
def sieve : Sieve X₀ where
  arrows Y₀ g := Nonempty (SieveStruct data f g)
  downward_closed := by
    rintro Y₀ Z₀ g ⟨h⟩ p
    exact ⟨{ i₀ := h.i₀, q := p ≫ h.q}⟩

lemma sieve_mem : sieve data f ∈ J₀ X₀ := by
  rw [← functorPushforward_mem_iff J₀ J F]
  let S := Sieve.pullback f data.toOneHypercover.sieve₀
  let R : ⦃W : C⦄ → ⦃p : W ⟶ F.obj X₀⦄ → S.arrows p → Sieve W := fun W p hp ↦
    { arrows := fun W' q ↦ ∃ (Y₀ : C₀) (b : W' ⟶ F.obj Y₀) (r : F.obj Y₀ ⟶ W)
          (g : Y₀ ⟶ X₀) (c : Y₀ ⟶ data.X (Sieve.ofArrows.i hp)),
          b ≫ r = q ∧ r ≫ p = F.map g ∧ r ≫ Sieve.ofArrows.h hp = F.map c
      downward_closed := by
        rintro W' W'' q ⟨Y₀, b, r, g, c, fac₁, fac₂, fac₃⟩ a
        exact ⟨Y₀, a ≫ b, r, g, c, by rw [assoc, fac₁], fac₂, fac₃⟩ }
  refine J.superset_covering ?_
    (J.bind_covering (J.pullback_stable f (data.toOneHypercover.mem₀)) (R := R) ?_)
  · rintro W' _ ⟨W, q, p, hp, ⟨Y₀, b, r, g, c, fac₁, fac₂, fac₃⟩, rfl⟩
    have := Sieve.ofArrows.fac hp
    dsimp at this
    exact ⟨Y₀, g, b,
      ⟨⟨Sieve.ofArrows.i hp, c, by rw [← reassoc_of% fac₃, ← this, reassoc_of% fac₂]⟩⟩,
      by rw [← reassoc_of% fac₁, fac₂]⟩
  · have := IsDenseSubsite.isCoverDense J₀ J F
    -- use a covering of `W` by objects in C₀
    sorry

end

section

variable (data : ∀ X, F.OneHypercoverDenseData J₀ J X)
  [HasLimitsOfSize.{w, w} A]

namespace EssSurj

variable (G₀ : Sheaf J₀ A)

noncomputable def presheafObj (X : C) : A :=
  multiequalizer ((data X).multicospanIndex G₀.val)

variable {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X)

structure PresheafSieveStruct {Y₀ : C₀} (g : Y₀ ⟶ X₀) where
  i₀ : (data X).I₀
  q : Y₀ ⟶ (data X).X i₀
  fac : F.map q ≫ (data X).f i₀ =
    F.map g ≫ f := by simp

attribute [reassoc (attr := simp)] PresheafSieveStruct.fac

noncomputable def restriction {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) :
    presheafObj data G₀ X ⟶ G₀.val.obj (op X₀) :=
  G₀.2.amalgamate ⟨_, (data X).sieve_mem f⟩ (fun ⟨Y₀, g, hg⟩ ↦
    Multiequalizer.ι _ _ ≫ G₀.val.map hg.some.q.op) sorry

noncomputable def presheafMap {X Y : C} (f : X ⟶ Y) :
    presheafObj data G₀ Y ⟶ presheafObj data G₀ X :=
  Multiequalizer.lift _ _ (fun i₀ ↦ restriction data G₀ ((data X).f i₀ ≫ f))
    sorry

noncomputable def presheaf : Cᵒᵖ ⥤ A where
  obj X := presheafObj data G₀ X.unop
  map f := presheafMap data G₀ f.unop
  map_id := sorry
  map_comp := sorry

lemma isSheaf : Presheaf.IsSheaf J (presheaf data G₀) := sorry

noncomputable def sheaf : Sheaf J A := ⟨presheaf data G₀, isSheaf data G₀⟩

def sheafIso : (sheafPushforwardContinuous F A J₀ J).obj (sheaf data G₀) ≅ G₀ := sorry

end EssSurj

include data in
lemma essSurj : EssSurj (sheafPushforwardContinuous F A J₀ J) where
  mem_essImage G₀ := ⟨_, ⟨EssSurj.sheafIso data G₀⟩⟩

include data in
lemma isEquivalence : IsEquivalence (sheafPushforwardContinuous F A J₀ J) where
  essSurj := essSurj data

end

end OneHypercoverDenseData

variable (data : ∀ X, F.OneHypercoverDenseData J₀ J X) [HasLimitsOfSize.{w, w} A]

variable [IsOneHypercoverDense.{w} F J₀ J]

lemma isEquivalence_of_IsOneHypercoverDense :
    IsEquivalence (sheafPushforwardContinuous F A J₀ J) :=
  OneHypercoverDenseData.isEquivalence.{w} (oneHypercoverDenseData F J₀ J)

-- TODO: deduce `Has(Weak)Sheafify` for `J` from `J₀`

end Functor

end CategoryTheory
