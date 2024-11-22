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

lemma _root_.CategoryTheory.Functor.functorPushforward_imageSieve_inter_mem
    {C D : Type*} [Category C] [Category D] (G : C ⥤ D) (K : GrothendieckTopology D)
    [G.IsLocallyFull K] {U V₁ V₂} (f₁ : G.obj U ⟶ G.obj V₁) (f₂ : G.obj U ⟶ G.obj V₂) :
    (G.imageSieve f₁ ⊓ G.imageSieve f₂).functorPushforward G ∈ K _ := by
  refine K.superset_covering ?_
    (K.bind_covering (G.functorPushforward_imageSieve_mem K f₁)
      (R := fun W p hp ↦ by
        letI str := Presieve.getFunctorPushforwardStructure hp
        exact ((G.imageSieve (G.map str.premap ≫ f₂)).functorPushforward G).pullback
          str.lift)
      (fun W p hp ↦ by
        apply K.pullback_stable
        apply G.functorPushforward_imageSieve_mem))
  rintro W _ ⟨T, a, b, hb, ⟨P, c, d, ⟨x, w⟩, fac⟩, rfl⟩
  let str := Presieve.getFunctorPushforwardStructure hb
  refine ⟨P, c ≫ str.premap, d, ⟨⟨c ≫ str.cover.choose, ?_⟩, ⟨x, ?_⟩⟩, ?_⟩
  · rw [G.map_comp, G.map_comp_assoc, str.cover.choose_spec]
  · rw [G.map_comp_assoc, w]
  · rw [G.map_comp, ← reassoc_of% fac]
    conv_lhs => rw [str.fac]

lemma sieve_mem : sieve data f ∈ J₀ X₀ := by
  have := IsDenseSubsite.isCoverDense J₀ J F
  have := IsDenseSubsite.isLocallyFull J₀ J F
  rw [← functorPushforward_mem_iff J₀ J F]
  let R : ⦃W : C⦄ → ⦃p : W ⟶ F.obj X₀⦄ →
    (Sieve.pullback f data.toOneHypercover.sieve₀).arrows p → Sieve W := fun W p hp ↦
      Sieve.bind (Sieve.coverByImage F W).arrows (fun U π hπ ↦
        Sieve.pullback hπ.some.lift
          (Sieve.functorPushforward F (F.imageSieve (hπ.some.map ≫ p) ⊓
            F.imageSieve (hπ.some.map ≫ Sieve.ofArrows.h hp))))
  refine J.superset_covering ?_
    (J.bind_covering (J.pullback_stable f (data.toOneHypercover.mem₀)) (R := R)
    (fun W p hp ↦ J.bind_covering (F.is_cover_of_isCoverDense J W) ?_))
  · rintro W' _ ⟨W, _, p, hp, ⟨Y₀, a, b, hb, ⟨U, c, d, ⟨⟨x₁, w₁⟩, ⟨x₂, w₂⟩⟩, fac⟩, rfl⟩, rfl⟩
    refine ⟨U, x₁, d, ⟨⟨Sieve.ofArrows.i hp, x₂, ?_⟩⟩, ?_⟩
    · simp only [reassoc_of% w₁, Sieve.ofArrows.fac hp, reassoc_of% w₂]
      dsimp
    · rw [assoc, w₁, ← reassoc_of% fac, Presieve.CoverByImageStructure.fac_assoc]
  · intro U π hπ
    apply J.pullback_stable
    apply Functor.functorPushforward_imageSieve_inter_mem

end

section

variable (data : ∀ X, F.OneHypercoverDenseData J₀ J X) (G : Cᵒᵖ ⥤ A)

lemma isSheaf_iff :
    Presheaf.IsSheaf J G ↔
      Presheaf.IsSheaf J₀ (F.op ⋙ G) ∧
        ∀ (X : C), Nonempty (IsLimit ((data X).toOneHypercover.multifork G)) := by
  refine ⟨fun hG ↦ ⟨op_comp_isSheaf F J₀ J ⟨_, hG⟩,
    fun X ↦ ⟨(data X).toOneHypercover.isLimitMultifork ⟨G, hG⟩⟩⟩, fun ⟨hG₀, hG⟩ ↦ ?_⟩
  sorry

end

section

variable (data : ∀ X, F.OneHypercoverDenseData J₀ J X)
  [HasLimitsOfSize.{w, w} A]

namespace EssSurj

variable (G₀ : Sheaf J₀ A)

noncomputable def presheafObj (X : C) : A :=
  multiequalizer ((data X).multicospanIndex G₀.val)

noncomputable def presheafObjπ (X : C) (i : (data X).I₀) :
    presheafObj data G₀ X ⟶ G₀.val.obj (op ((data X).X i)) :=
  Multiequalizer.ι ((data X).multicospanIndex G₀.val) i

omit [IsDenseSubsite J₀ J F] in
variable {data G₀} in
@[ext]
lemma presheafObj_hom_ext {X : C} {Z : A} {f g : Z ⟶ presheafObj data G₀ X}
    (h : ∀ (i : (data X).I₀), f ≫ presheafObjπ data G₀ X i = g ≫ presheafObjπ data G₀ X i) :
    f = g :=
  Multiequalizer.hom_ext _ _ _ h

omit [IsDenseSubsite J₀ J F] in
@[reassoc]
lemma presheafObj_condition (X : C) (i i' : (data X).I₀) (j : (data X).I₁ i i') :
    presheafObjπ data G₀ X i ≫ G₀.val.map ((data X).p₁ j).op =
    presheafObjπ data G₀ X i' ≫ G₀.val.map ((data X).p₂ j).op :=
  Multiequalizer.condition ((data X).multicospanIndex G₀.val) ⟨⟨i, i'⟩, j⟩

noncomputable abbrev presheafObjMultifork (X : C) :
    Multifork ((data X).multicospanIndex G₀.val) :=
  Multifork.ofι _ (presheafObj data G₀ X) (presheafObjπ data G₀ X)
    (fun _ ↦ presheafObj_condition _ _ _ _ _ _)

def _root_.CategoryTheory.Limits.Multifork.isoMk {C : Type*} [Category C]
    {I : MulticospanIndex C} {c₁ c₂ : Multifork I} (e : c₁.pt ≅ c₂.pt)
    (h : ∀ (i : I.L), c₁.ι i = e.hom ≫ c₂.ι i := by aesop_cat) : c₁ ≅ c₂ :=
  Cones.ext e (by rintro (_ | _) <;> simp [h])

noncomputable def presheafObjIsLimit (X : C) :
    IsLimit (presheafObjMultifork data G₀ X) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Multifork.isoMk (Iso.refl _))

namespace restriction

noncomputable def res {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀}
    (h : SieveStruct (data X) f g) :
    presheafObj data G₀ X ⟶ G₀.val.obj (op Y₀) :=
    presheafObjπ data G₀ X h.i₀ ≫ G₀.val.map h.q.op

noncomputable def res_eq_res {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀}
    (h₁ h₂ : SieveStruct (data X) f g) :
    res data G₀ h₁ = res data G₀ h₂ :=
  Presheaf.IsSheaf.hom_ext G₀.cond
    ⟨_, (data X).mem₁₀ h₁.i₀ h₂.i₀ h₁.q h₂.q (by rw [h₁.fac, h₂.fac])⟩ _ _ (by
      rintro ⟨Z₀, a, ⟨j, b, fac₁, fac₂⟩⟩
      dsimp [res]
      rw [assoc, assoc, ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
        fac₁, fac₂, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
      apply presheafObj_condition_assoc)

end restriction

noncomputable def restriction {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) :
    presheafObj data G₀ X ⟶ G₀.val.obj (op X₀) :=
  G₀.2.amalgamate ⟨_, (data X).sieve_mem f⟩
    (fun ⟨Y₀, g, hg⟩ ↦ restriction.res data G₀ hg.some) (by
      rintro ⟨Z₁, g₁, ⟨h₁⟩⟩ ⟨Z₂, g₂, ⟨h₂⟩⟩ ⟨T₀, p₁, p₂, w⟩
      dsimp at g₁ g₂ p₁ p₂ w ⊢
      rw [restriction.res_eq_res data G₀ _ h₁, restriction.res_eq_res data G₀ _ h₂]
      refine Presheaf.IsSheaf.hom_ext G₀.cond
        ⟨_, (data X).mem₁₀ h₁.i₀ h₂.i₀ (p₁ ≫ h₁.q) (p₂ ≫ h₂.q) (by
          rw [map_comp, map_comp, assoc, assoc, SieveStruct.fac, SieveStruct.fac,
            ← map_comp_assoc, ← map_comp_assoc, w])⟩ _ _ ?_
      rintro ⟨U₀, a, j, b, fac₁, fac₂⟩
      dsimp [restriction.res]
      rw [assoc, assoc, assoc, assoc, ← Functor.map_comp, ← Functor.map_comp,
        ← Functor.map_comp, ← Functor.map_comp, ← op_comp_assoc, ← op_comp, fac₁,
        ← op_comp_assoc, ← op_comp, fac₂, op_comp, op_comp, Functor.map_comp,
        Functor.map_comp, ]
      apply presheafObj_condition_assoc)

lemma restriction_map {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) {Y₀ : C₀}
    (g : Y₀ ⟶ X₀) {i : (data X).I₀} (p : Y₀ ⟶ (data X).X i)
    (fac : F.map p ≫ (data X).f i = F.map g ≫ f) :
    restriction data G₀ f ≫ G₀.val.map g.op =
      presheafObjπ data G₀ X i ≫ G₀.val.map p.op := by
  have hg : (data X).sieve f g := ⟨⟨i, p, fac⟩⟩
  exact (G₀.2.amalgamate_map _ _ _ ⟨_, _, hg⟩).trans
    (restriction.res_eq_res data G₀ hg.some ⟨i, p, fac⟩)

noncomputable def presheafMap {X Y : C} (f : X ⟶ Y) :
    presheafObj data G₀ Y ⟶ presheafObj data G₀ X :=
  Multiequalizer.lift _ _ (fun i₀ ↦ restriction data G₀ ((data X).f i₀ ≫ f)) (by
    have : Full F := sorry -- use `IsLocallyFull`...
    rintro ⟨⟨i₁, i₂⟩, j⟩
    dsimp at j ⊢
    obtain ⟨a, h₁, h₂⟩ : ∃ a, a = F.map ((data X).p₁ j) ≫ (data X).f i₁ ≫ f ∧
        a = F.map ((data X).p₂ j) ≫ (data X).f i₂ ≫ f := ⟨_, rfl, (data X).w_assoc j _⟩
    refine Presheaf.IsSheaf.hom_ext G₀.cond
      ⟨_, cover_lift F J₀ _ (J.pullback_stable a (data Y).mem₀)⟩ _ _ ?_
    rintro ⟨W₀, b, ⟨_, c, _, h, w⟩⟩
    cases' h with i
    dsimp at i c w ⊢
    rw [assoc, assoc, ← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
    rw [restriction_map data G₀ _ _ (F.preimage c),
      restriction_map data G₀ _ _ (F.preimage c)]
    · rw [map_preimage, map_comp, assoc, w, h₂]
    · rw [map_preimage, map_comp, assoc, w, h₁])

@[reassoc (attr := simp)]
lemma presheafMap_π {X Y : C} (f : X ⟶ Y) (i : (data X).I₀) :
    presheafMap data G₀ f ≫ presheafObjπ data G₀ X i =
      restriction data G₀ ((data X).f i ≫ f) :=
  Multiequalizer.lift_ι _ _ _ _ _

lemma presheafMap_id (X : C) :
    presheafMap data G₀ (𝟙 X) = 𝟙 _ := by
  ext i
  rw [presheafMap_π, comp_id, id_comp]
  simpa only [op_id, map_id, comp_id] using
    restriction_map data G₀ ((data X).f i) (𝟙 _) (𝟙 _) (by simp)

lemma presheafMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    presheafMap data G₀ (f ≫ g) = presheafMap data G₀ g ≫ presheafMap data G₀ f := by
  sorry

@[simps]
noncomputable def presheaf : Cᵒᵖ ⥤ A where
  obj X := presheafObj data G₀ X.unop
  map f := presheafMap data G₀ f.unop
  map_id X := presheafMap_id data G₀ X.unop
  map_comp f g := presheafMap_comp data G₀ g.unop f.unop

namespace presheafObjObjIso

variable (X₀ : C₀)

noncomputable def hom : (presheaf data G₀).obj (op (F.obj X₀)) ⟶ G₀.val.obj (op X₀) :=
  G₀.2.amalgamate ⟨_, cover_lift F J₀ _ (data (F.obj X₀)).mem₀⟩ (fun ⟨Y₀, a, ha⟩ ↦ by
    have : Full F := sorry
    exact presheafObjπ data G₀ _ (Sieve.ofArrows.i ha) ≫
      G₀.val.map (F.preimage (Sieve.ofArrows.h ha)).op) sorry

noncomputable def inv : G₀.val.obj (op X₀) ⟶ (presheaf data G₀).obj (op (F.obj X₀)) :=
  Multiequalizer.lift _ _ (fun i ↦ G₀.val.map (by
    have : Full F := sorry
    exact (F.preimage ((data (F.obj X₀)).f i)).op)) sorry

end presheafObjObjIso

noncomputable def presheafObjObjIso (X₀ : C₀) :
    (presheaf data G₀).obj (op (F.obj X₀)) ≅ G₀.val.obj (op X₀) where
  hom := presheafObjObjIso.hom data G₀ X₀
  inv := presheafObjObjIso.inv data G₀ X₀
  hom_inv_id := sorry
  inv_hom_id := sorry

@[reassoc (attr := simp)]
lemma presheafMap_presheafObjObjIso_hom (X : C) (i : (data X).I₀) :
    presheafMap data G₀ ((data X).f i) ≫ (presheafObjObjIso data G₀ ((data X).X i)).hom =
      presheafObjπ data G₀ X i := sorry

@[reassoc]
lemma presheafObjObjIso_hom_naturality {X₀ Y₀ : C₀} (f : X₀ ⟶ Y₀) :
    presheafMap data G₀ (F.map f) ≫ (presheafObjObjIso data G₀ X₀).hom =
      (presheafObjObjIso data G₀ Y₀).hom ≫ G₀.val.map f.op := by
  sorry

noncomputable def compPresheafIso : F.op ⋙ presheaf data G₀ ≅ G₀.val :=
  NatIso.ofComponents (fun X₀ ↦ presheafObjObjIso data G₀ X₀.unop)
    (fun f ↦ presheafObjObjIso_hom_naturality data G₀ f.unop)

@[simps!]
def _root_.CategoryTheory.Limits.multicospanIsoMk {L R : Type*} {fst snd : L → R}
    {C : Type*} [Category C] {G₁ G₂ : WalkingMulticospan fst snd ⥤ C}
    (e : ∀ (i : L), G₁.obj (.right i) ≅ G₂.obj (.right i))
    (e' : ∀ (j : R), G₁.obj (.left j) ≅ G₂.obj (.left j))
    (h₁ : ∀ (i : L), G₁.map (WalkingMulticospan.Hom.fst i) ≫ (e i).hom =
      (e' (fst i)).hom ≫ G₂.map (WalkingMulticospan.Hom.fst i))
    (h₂ : ∀ (i : L), G₁.map (WalkingMulticospan.Hom.snd i) ≫ (e i).hom =
      (e' (snd i)).hom ≫ G₂.map (WalkingMulticospan.Hom.snd i)) :
    G₁ ≅ G₂ :=
  NatIso.ofComponents (fun x ↦ match x with
    | .left j => e' j
    | .right i => e i) (by
        rintro _ _ (_ | _ | _)
        · simp
        · exact h₁ _
        · exact h₂ _)

lemma isSheaf : Presheaf.IsSheaf J (presheaf data G₀) := by
  rw [isSheaf_iff data]
  constructor
  · exact (Presheaf.isSheaf_of_iso_iff (compPresheafIso data G₀)).2 G₀.cond
  · intro X
    refine ⟨(IsLimit.postcomposeHomEquiv
      (Limits.multicospanIsoMk (fun _ ↦ presheafObjObjIso _ _ _)
          (fun _ ↦ presheafObjObjIso _ _ _) (fun j ↦ ?_) (fun j ↦ ?_)) _).1
      (IsLimit.ofIsoLimit (presheafObjIsLimit data G₀ X)
        (Multifork.isoMk (Iso.refl _) (fun i ↦ ?_)))⟩
    · apply presheafObjObjIso_hom_naturality
    · apply presheafObjObjIso_hom_naturality
    · simp [Multifork.ι, PreOneHypercover.multifork]

noncomputable def sheaf : Sheaf J A := ⟨presheaf data G₀, isSheaf data G₀⟩

noncomputable def sheafIso : (sheafPushforwardContinuous F A J₀ J).obj (sheaf data G₀) ≅ G₀ :=
  (fullyFaithfulSheafToPresheaf J₀ A).preimageIso (compPresheafIso data G₀)

end EssSurj

variable (A)

include data in
lemma essSurj : EssSurj (sheafPushforwardContinuous F A J₀ J) where
  mem_essImage G₀ := ⟨_, ⟨EssSurj.sheafIso data G₀⟩⟩

include data in
lemma isEquivalence : IsEquivalence (sheafPushforwardContinuous F A J₀ J) where
  essSurj := essSurj A data

end

end OneHypercoverDenseData

variable (A) [HasLimitsOfSize.{w, w} A] [IsOneHypercoverDense.{w} F J₀ J]

lemma isEquivalence_of_isOneHypercoverDense :
    IsEquivalence (sheafPushforwardContinuous F A J₀ J) :=
  OneHypercoverDenseData.isEquivalence.{w} A (oneHypercoverDenseData F J₀ J)

section

variable [HasWeakSheafify J₀ A]

noncomputable def sheafifyOfIsOneHypercoverDense :
    (Cᵒᵖ ⥤ A) ⥤ Sheaf J A :=
  have := isEquivalence_of_isOneHypercoverDense.{w} F J₀ J A
  (whiskeringLeft _ _ _).obj F.op ⋙ presheafToSheaf J₀ A ⋙
    inv (F.sheafPushforwardContinuous A J₀ J)

variable {A}

noncomputable def sheafifyHomEquivOfIsOneHypercoverDense {P : Cᵒᵖ ⥤ A} {Q : Sheaf J A} :
    ((sheafifyOfIsOneHypercoverDense.{w} F J₀ J A).obj P ⟶ Q) ≃ (P ⟶ Q.val) :=
  have := isEquivalence_of_isOneHypercoverDense.{w} F J₀ J A
  have := IsDenseSubsite.isLocallyFull J₀ J F
  have := IsDenseSubsite.isCoverDense J₀ J F
  ((F.sheafPushforwardContinuous A J₀ J).asEquivalence.symm.toAdjunction.homEquiv _ _).trans
    (((sheafificationAdjunction J₀ A).homEquiv _ _).trans IsCoverDense.restrictHomEquivHom)

lemma sheafifyHomEquivOfIsOneHypercoverDense_naturality_left
    {P₁ P₂ : Cᵒᵖ ⥤ A} (f : P₁ ⟶ P₂) {Q : Sheaf J A}
    (g : (F.sheafifyOfIsOneHypercoverDense J₀ J A).obj P₂ ⟶ Q)  :
      sheafifyHomEquivOfIsOneHypercoverDense.{w} F J₀ J
        ((F.sheafifyOfIsOneHypercoverDense J₀ J A).map f ≫ g) =
        f ≫ sheafifyHomEquivOfIsOneHypercoverDense.{w} F J₀ J g := by
  have := isEquivalence_of_isOneHypercoverDense.{w} F J₀ J A
  have := IsDenseSubsite.isLocallyFull J₀ J F
  have := IsDenseSubsite.isCoverDense J₀ J F
  let adj₁ := (F.sheafPushforwardContinuous A J₀ J).asEquivalence.symm.toAdjunction
  let adj₂ := sheafificationAdjunction J₀ A
  change IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _
    ((F.sheafifyOfIsOneHypercoverDense J₀ J A).map f ≫ g))) =
      f ≫ IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ g))
  erw [← IsCoverDense.restrictHomEquivHom_naturality_left]
  erw [adj₁.homEquiv_naturality_left, adj₂.homEquiv_naturality_left]
  rfl

lemma sheafifyHomEquivOfIsOneHypercoverDense_naturality_right
    {P : Cᵒᵖ ⥤ A} {Q₁ Q₂ : Sheaf J A}
    (f : (F.sheafifyOfIsOneHypercoverDense J₀ J A).obj P ⟶ Q₁) (g : Q₁ ⟶ Q₂) :
      sheafifyHomEquivOfIsOneHypercoverDense.{w} F J₀ J (f ≫ g) =
        sheafifyHomEquivOfIsOneHypercoverDense.{w} F J₀ J f ≫ g.val := by
  have := isEquivalence_of_isOneHypercoverDense.{w} F J₀ J A
  have := IsDenseSubsite.isLocallyFull J₀ J F
  have := IsDenseSubsite.isCoverDense J₀ J F
  let adj₁ := (F.sheafPushforwardContinuous A J₀ J).asEquivalence.symm.toAdjunction
  let adj₂ := sheafificationAdjunction J₀ A
  change IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ (f ≫ g))) =
    IsCoverDense.restrictHomEquivHom (adj₂.homEquiv _ _ (adj₁.homEquiv _ _ f)) ≫ g.val
  rw [adj₁.homEquiv_naturality_right, adj₂.homEquiv_naturality_right]
  apply IsCoverDense.restrictHomEquivHom_naturality_right

variable (A)

noncomputable def sheafifyAdjunctionOfIsOneHypercoverDense :
    sheafifyOfIsOneHypercoverDense.{w} F J₀ J A ⊣ sheafToPresheaf J A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun P Q ↦ sheafifyHomEquivOfIsOneHypercoverDense.{w} F J₀ J
      homEquiv_naturality_left_symm := fun {P₁ P₂ Q} f g ↦
        (F.sheafifyHomEquivOfIsOneHypercoverDense J₀ J).injective (by
          simp only [sheafToPresheaf_obj, Equiv.apply_symm_apply,
            sheafifyHomEquivOfIsOneHypercoverDense_naturality_left _ _ _ f])
      homEquiv_naturality_right :=
        sheafifyHomEquivOfIsOneHypercoverDense_naturality_right F J₀ J }

include F J₀ in
lemma hasWeakSheafify_of_isOneHypercoverDense :
    HasWeakSheafify J A := ⟨_, ⟨sheafifyAdjunctionOfIsOneHypercoverDense.{w} F J₀ J A⟩⟩

end

include F in
lemma hasSheafify_of_isOneHypercoverDense [HasSheafify J₀ A] [HasFiniteLimits A] :
    HasSheafify J A := by
  have := isEquivalence_of_isOneHypercoverDense.{w} F J₀ J A
  have : PreservesFiniteLimits ((whiskeringLeft _ _ A).obj F.op) := ⟨fun _ _ _ ↦ inferInstance⟩
  have : PreservesFiniteLimits (presheafToSheaf J₀ A ⋙
    (F.sheafPushforwardContinuous A J₀ J).inv) := by
    apply comp_preservesFiniteLimits
  have : PreservesFiniteLimits (F.sheafifyOfIsOneHypercoverDense J₀ J A) := by
    apply comp_preservesFiniteLimits
  exact HasSheafify.mk' _ _ (sheafifyAdjunctionOfIsOneHypercoverDense.{w} F J₀ J A)

end Functor

end CategoryTheory
