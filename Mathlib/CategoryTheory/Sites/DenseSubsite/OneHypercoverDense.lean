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

variable [IsDenseSubsite J₀ J F]

variable {F J₀ J} in
/-- Constructor for `IsOneHypercoverDense.{w} F J₀ J` for a dense subsite
when the functor `F : C₀ ⥤ C` is fully faithful, `C` has pullbacks, and
any object in `C` admits a `w`-small covering family consisting of objects in `C₀`. -/
lemma IsOneHypercoverDense.of_hasPullbacks [HasPullbacks C] [F.Full] [F.Faithful]
    (hF : ∀ (S : C), ∃ (ι : Type w) (U : ι → C₀) (f : ∀ i, F.obj (U i) ⟶ S),
      Sieve.ofArrows _ f ∈ J S) :
    IsOneHypercoverDense.{w} F J₀ J where
  nonempty_oneHypercoverDenseData S := by
    choose ι U f hf using hF
    exact ⟨{
      I₀ := ι S
      X := U S
      f := f S
      I₁ i j := ι (pullback (f _ i) (f _ j))
      Y i j := U (pullback (f _ i) (f _ j))
      p₁ i j k := F.preimage (f _ k ≫ pullback.fst _ _)
      p₂ i j k := F.preimage (f _ k ≫ pullback.snd _ _)
      w i j k := by simp [pullback.condition]
      mem₀ := hf S
      mem₁₀ i j W₀ p₁ p₂ hp := by
        have := IsDenseSubsite.isCoverDense J₀ J F
        rw [← functorPushforward_mem_iff J₀ J F]
        refine J.superset_covering ?_
          (IsCoverDense.functorPullback_pushforward_covering
            ⟨_, J.pullback_stable (pullback.lift _ _ hp) (hf (pullback (f _ i) (f _ j)))⟩)
        rintro T _ ⟨Z, q, r, ⟨_, s, _, ⟨k⟩, fac⟩, rfl⟩
        have fac₁ := fac =≫ pullback.fst _ _
        have fac₂ := fac =≫ pullback.snd _ _
        simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at fac₁ fac₂
        exact ⟨Z, q, r, ⟨k, F.preimage s, F.map_injective (by simp [fac₁]),
          F.map_injective (by simp [fac₂])⟩, rfl⟩ }⟩

namespace OneHypercoverDenseData

variable {F J₀ J}

section

variable {X : C} (data : OneHypercoverDenseData.{w} F J₀ J X)

set_option backward.isDefEq.respectTransparency false in
lemma mem₁ (i₁ i₂ : data.I₀) {W : C} (p₁ : W ⟶ F.obj (data.X i₁)) (p₂ : W ⟶ F.obj (data.X i₂))
    (w : p₁ ≫ data.f i₁ = p₂ ≫ data.f i₂) : data.toPreOneHypercover.sieve₁ p₁ p₂ ∈ J W := by
  have := IsDenseSubsite.isCoverDense J₀ J F
  let S := Sieve.bind (Sieve.coverByImage F W).arrows
    (fun Y f hf ↦ ((F.imageSieve (hf.some.map ≫ p₁) ⊓
        F.imageSieve (hf.some.map ≫ p₂)).functorPushforward F).pullback hf.some.lift)
  let T := Sieve.bind S.arrows (fun Z g hg ↦ by
    letI str := Presieve.getFunctorPushforwardStructure hg.bindStruct.hg
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
    let str := Presieve.getFunctorPushforwardStructure hg.bindStruct.hg
    apply data.mem₁₀
    simp only [str.cover.1.choose_spec, str.cover.2.choose_spec, assoc, w])
  refine J.superset_covering ?_ hT
  rintro U f ⟨V, a, b, hb, h, _, rfl⟩
  let str := Presieve.getFunctorPushforwardStructure hb.bindStruct.hg
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

/-- The `1`-hypercover associated to a `OneHypercoverDenseData` structure. -/
@[simps toPreOneHypercover]
def toOneHypercover {X : C} (data : F.OneHypercoverDenseData J₀ J X) :
    J.OneHypercover X where
  toPreOneHypercover := data.toPreOneHypercover
  mem₀ := data.mem₀
  mem₁ := data.mem₁

variable {X : C} (data : OneHypercoverDenseData.{w} F J₀ J X) {X₀ : C₀} (f : F.obj X₀ ⟶ X)

/-- Auxiliary structure for the definition `OneHypercoverDenseData.sieve`. -/
structure SieveStruct {Y₀ : C₀} (g : Y₀ ⟶ X₀) where
  /-- the index of the intermediate object -/
  i₀ : data.I₀
  /-- the morphism that is part of the factorization `fac`. -/
  q : F.obj Y₀ ⟶ F.obj (data.X i₀)
  fac : q ≫ data.f i₀ = F.map g ≫ f := by simp

attribute [reassoc (attr := simp)] SieveStruct.fac

/-- Given `data : OneHypercoverDenseData F J₀ J X` and a morphism `f : F.obj X₀ ⟶ X`,
this is the sieve of `X₀` consisting of morphisms `g : Y₀ ⟶ X₀` such that there
exists `i₀ : data.I₀`, `q : F.obj Y₀ ⟶ F.obj (data.X i₀)` such that
we have a factorization `q ≫ data.f i₀ = F.map g ≫ f`. -/
@[simps]
def sieve : Sieve X₀ where
  arrows Y₀ g := Nonempty (SieveStruct data f g)
  downward_closed := by
    rintro Y₀ Z₀ g ⟨h⟩ p
    exact ⟨{ i₀ := h.i₀, q := F.map p ≫ h.q, fac := by rw [assoc, h.fac, map_comp_assoc]}⟩

set_option backward.isDefEq.respectTransparency false in
lemma sieve_mem : sieve data f ∈ J₀ X₀ := by
  have := IsDenseSubsite.isCoverDense J₀ J F
  have := IsDenseSubsite.isLocallyFull J₀ J F
  rw [← functorPushforward_mem_iff J₀ J F]
  let R : ⦃W : C⦄ → ⦃p : W ⟶ F.obj X₀⦄ →
    (Sieve.pullback f data.toOneHypercover.sieve₀).arrows p → Sieve W := fun W p hp ↦
      Sieve.bind (Sieve.coverByImage F W).arrows (fun U π hπ ↦
        Sieve.pullback hπ.some.lift
          (Sieve.functorPushforward F (F.imageSieve (hπ.some.map ≫ p))))
  refine J.superset_covering ?_
    (J.bind_covering (J.pullback_stable f (data.toOneHypercover.mem₀)) (R := R)
    (fun W p hp ↦ J.bind_covering (F.is_cover_of_isCoverDense J W) ?_))
  · rintro W' _ ⟨W, _, p, hp, ⟨Y₀, a, b, hb, ⟨U, c, d, ⟨x₁, w₁⟩, fac⟩, rfl⟩, rfl⟩
    have hp' := Sieve.ofArrows.fac hp
    dsimp at hp'
    refine ⟨U, x₁, d, ⟨Sieve.ofArrows.i hp,
      F.map c ≫ (Nonempty.some hb).map ≫ Sieve.ofArrows.h hp, ?_⟩, ?_⟩
    · rw [w₁, assoc, assoc, assoc, assoc, hp']
    · rw [w₁, assoc, ← reassoc_of% fac, hb.some.fac_assoc]
  · intro U π hπ
    apply J.pullback_stable
    apply functorPushforward_imageSieve_mem

end

section

namespace isSheaf_iff

variable {data : ∀ X, F.OneHypercoverDenseData J₀ J X} {G : Cᵒᵖ ⥤ A}
  (hG₀ : Presheaf.IsSheaf J₀ (F.op ⋙ G))
  (hG : ∀ (X : C), IsLimit ((data X).toOneHypercover.multifork G))
  {X : C} (S : J.Cover X)

section

variable {S} (s : Multifork (S.index G))

/-- Auxiliary definition for `lift`. -/
noncomputable def liftAux (i : (data X).I₀) : s.pt ⟶ G.obj (op (F.obj ((data X).X i))) :=
  hG₀.amalgamate ⟨_, cover_lift F J₀ _ (J.pullback_stable ((data X).f i) S.2)⟩
    (fun ⟨W₀, a, ha⟩ ↦ s.ι ⟨_, F.map a ≫ (data X).f i, ha⟩) (by
      rintro ⟨W₀, a, ha⟩ ⟨Z₀, b, hb⟩ ⟨U₀, p₁, p₂, fac⟩
      exact s.condition
        { fst := ⟨_, _, ha⟩
          snd := ⟨_, _, hb⟩
          r := ⟨_, F.map p₁, F.map p₂, by
              simp only [← Functor.map_comp_assoc, fac]⟩ })

lemma liftAux_fac {i : (data X).I₀} {W₀ : C₀} (a : W₀ ⟶ (data X).X i)
    (ha : S (F.map a ≫ (data X).f i)) :
    liftAux hG₀ s i ≫ G.map (F.map a).op = s.ι ⟨_, F.map a ≫ (data X).f i, ha⟩ :=
  hG₀.amalgamate_map _ _ _ ⟨W₀, a, ha⟩

/-- Auxiliary definition for the lemma `OneHypercoverDenseData.isSheaf_iff`. -/
noncomputable def lift : s.pt ⟶ G.obj (op X) :=
  Multifork.IsLimit.lift (hG X) (fun i ↦ liftAux hG₀ s i) (by
    rintro ⟨⟨i₁, i₂⟩, j⟩
    dsimp at i₁ i₂ j ⊢
    refine Presheaf.IsSheaf.hom_ext
      hG₀ ⟨_, cover_lift F J₀ _
        (J.pullback_stable (F.map ((data X).p₁ j) ≫ (data X).f i₁) S.2)⟩ _ _ ?_
    rintro ⟨W₀, a, ha⟩
    dsimp
    simp only [assoc, ← Functor.map_comp, ← op_comp]
    have ha₁ : S (F.map (a ≫ (data X).p₁ j) ≫ (data X).f i₁) := by simpa using ha
    have ha₂ : S (F.map (a ≫ (data X).p₂ j) ≫ (data X).f i₂) := by
      rwa [Functor.map_comp_assoc, ← (data X).w j]
    rw [liftAux_fac _ _ _ ha₁, liftAux_fac _ _ _ ha₂]
    congr 2
    rw [map_comp_assoc, map_comp_assoc, (data X).w j])

@[reassoc]
lemma lift_map (i : (data X).I₀) :
    lift hG₀ hG s ≫ G.map ((data X).f i).op = liftAux hG₀ s i :=
  Multifork.IsLimit.fac _ _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma fac (a : S.Arrow) :
    lift hG₀ hG s ≫ G.map a.f.op = s.ι a :=
  Multifork.IsLimit.hom_ext (hG _) (fun i ↦
    Presheaf.IsSheaf.hom_ext hG₀
      ⟨_, cover_lift F J₀ _
        (J.pullback_stable ((data a.Y).f i ≫ a.f) (data X).mem₀)⟩ _ _ (by
        rintro ⟨X₀, b, ⟨_, c, _, h, fac₁⟩⟩
        obtain ⟨j⟩ := h
        refine Presheaf.IsSheaf.hom_ext hG₀
          ⟨_, IsDenseSubsite.imageSieve_mem J₀ J F c⟩ _ _ ?_
        rintro ⟨Y₀, d, e, fac₂⟩
        dsimp at i j c fac₁ ⊢
        have he : S (F.map e ≫ (data X).f j) := by
          rw [fac₂, assoc, fac₁]
          simpa only [assoc] using S.1.downward_closed a.hf (F.map d ≫ F.map b ≫ (data a.Y).f i)
        simp only [assoc, ← Functor.map_comp, ← op_comp, ← fac₁]
        conv_lhs => simp only [op_comp, Functor.map_comp, assoc, lift_map_assoc]
        rw [← Functor.map_comp, ← op_comp, ← fac₂, liftAux_fac _ _ _ he]
        simpa using s.condition
          { fst := { hf := he, .. }
            snd := a
            r := ⟨_, 𝟙 _, F.map d ≫ F.map b ≫ (data a.Y).f i, by
              simp only [fac₁, fac₂, assoc, id_comp]⟩ }))

set_option backward.isDefEq.respectTransparency false in
variable {s} in
include hG hG₀ in
lemma hom_ext {f₁ f₂ : s.pt ⟶ G.obj (op X)}
    (h : ∀ (a : S.Arrow), f₁ ≫ G.map a.f.op = f₂ ≫ G.map a.f.op) : f₁ = f₂ :=
  Multifork.IsLimit.hom_ext (hG X) (fun i ↦ by
    refine Presheaf.IsSheaf.hom_ext hG₀
      ⟨_, cover_lift F J₀ _ (J.pullback_stable ((data X).f i) S.2)⟩ _ _ ?_
    rintro ⟨X₀, a, ha⟩
    dsimp
    simp only [assoc, ← Functor.map_comp, ← op_comp]
    exact h ⟨_, _, ha⟩)

end

/-- Auxiliary definition for the lemma `OneHypercoverDenseData.isSheaf_iff`. -/
noncomputable def isLimit : IsLimit (S.multifork G) :=
  Multifork.IsLimit.mk _
    (lift hG₀ hG ) (fac hG₀ hG) (fun s _ hm ↦
      hom_ext hG₀ hG (fun a ↦ (hm a).trans (fac hG₀ hG s a).symm))

end isSheaf_iff

/-- Let `F : C₀ ⥤ C` be a dense subsite, and assume we have a family
`data : ∀ X, F.OneHypercoverDenseData J₀ J X`.
This lemma shows that `G : Cᵒᵖ ⥤ A` is a sheaf iff `F.op F.op ⋙ G : C₀ᵒᵖ ⥤ A`
is a sheaf and for any `X : C`, the multifork for `G` and the `1`-hypercover
given by `data X` is a limit. -/
lemma isSheaf_iff (data : ∀ X, F.OneHypercoverDenseData J₀ J X) (G : Cᵒᵖ ⥤ A) :
    Presheaf.IsSheaf J G ↔
      Presheaf.IsSheaf J₀ (F.op ⋙ G) ∧
        ∀ (X : C), Nonempty (IsLimit ((data X).toOneHypercover.multifork G)) := by
  refine ⟨fun hG ↦ ⟨op_comp_isSheaf F J₀ J ⟨_, hG⟩,
    fun X ↦ ⟨(data X).toOneHypercover.isLimitMultifork ⟨G, hG⟩⟩⟩, fun ⟨hG₀, hG⟩ ↦ ?_⟩
  rw [Presheaf.isSheaf_iff_multifork]
  replace hG := fun X ↦ (hG X).some
  exact fun X S ↦ ⟨isSheaf_iff.isLimit hG₀ hG S⟩

end

section

variable (data : ∀ X, OneHypercoverDenseData.{w} F J₀ J X)
  [HasLimitsOfSize.{w, w} A]

namespace essSurj

variable (G₀ : Sheaf J₀ A)

/-- Given a dense subsite `F : C₀ ⥤ C` and a family
`data : ∀ X, OneHypercoverDenseData F J₀ J X` and a sheaf `G₀` on `J₀`,
this is the value on an object `X : C` of the "extension" of `G₀`
as a sheaf on `J` (see `OneHypercoverDenseData.essSurj.presheaf` for the
construction of this extension as a presheaf): it is defined as
a multiequalizer using `data X`. -/
noncomputable def presheafObj (X : C) : A :=
  multiequalizer ((data X).multicospanIndex G₀.val)

/-- The projection `presheafObj data G₀ X ⟶ G₀.val.obj (op ((data X).X i))`. -/
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

lemma presheafObj_mapPreimage_condition
    (X : C) (i₁ i₂ : (data X).I₀) {Y₀ : C₀}
    (p₁ : F.obj Y₀ ⟶ F.obj ((data X).X i₁)) (p₂ : F.obj Y₀ ⟶ F.obj ((data X).X i₂))
    (fac : p₁ ≫ (data X).f i₁ = p₂ ≫ (data X).f i₂) :
    presheafObjπ data G₀ X i₁ ≫ IsDenseSubsite.mapPreimage J F G₀ p₁ =
      presheafObjπ data G₀ X i₂ ≫ IsDenseSubsite.mapPreimage J F G₀ p₂ := by
  refine Presheaf.IsSheaf.hom_ext G₀.cond ⟨_,
    J₀.intersection_covering (IsDenseSubsite.imageSieve_mem J₀ J F p₁)
      (IsDenseSubsite.imageSieve_mem J₀ J F p₂)⟩ _ _ ?_
  intro ⟨W₀, a, ⟨b₁, h₁⟩, ⟨b₂, h₂⟩⟩
  refine Presheaf.IsSheaf.hom_ext G₀.cond
    ⟨_, (data X).mem₁₀ i₁ i₂ b₁ b₂ (by simp only [h₁, h₂, assoc, fac])⟩ _ _ ?_
  intro ⟨U₀, c, ⟨j, t, fac₁, fac₂⟩⟩
  simp only [assoc, ← Functor.map_comp, ← op_comp,
    IsDenseSubsite.mapPreimage_map_of_fac J F G₀ p₁ (c ≫ a) (c ≫ b₁) (by simp [← h₁]),
    IsDenseSubsite.mapPreimage_map_of_fac J F G₀ p₂ (c ≫ a) (c ≫ b₂) (by simp [← h₂])]
  simpa [fac₁, fac₂] using presheafObj_condition_assoc _ _ _ _ _ _ _

/-- The (limit) multifork with point `presheafObjπ data G₀ X` for
the diagram given by `G₀` and `data X`. -/
noncomputable abbrev presheafObjMultifork (X : C) :
    Multifork ((data X).multicospanIndex G₀.val) :=
  Multifork.ofι _ (presheafObj data G₀ X) (presheafObjπ data G₀ X)
    (fun _ ↦ presheafObj_condition _ _ _ _ _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The multifork `presheafObjMultifork` is a limit. -/
noncomputable def presheafObjIsLimit (X : C) :
    IsLimit (presheafObjMultifork data G₀ X) :=
  IsLimit.ofIsoLimit (limit.isLimit _) (Multifork.ext (Iso.refl _))

namespace restriction

/-- Auxiliary definition for `OneHypercoverDenseData.essSurj.restriction`. -/
noncomputable def res {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀}
    (h : SieveStruct (data X) f g) :
    presheafObj data G₀ X ⟶ G₀.val.obj (op Y₀) :=
  presheafObjπ data G₀ X h.i₀ ≫ IsDenseSubsite.mapPreimage J F G₀ h.q

lemma res_eq_res {X : C} {X₀ Y₀ : C₀} {f : F.obj X₀ ⟶ X} {g : Y₀ ⟶ X₀}
    (h₁ h₂ : SieveStruct (data X) f g) :
    res data G₀ h₁ = res data G₀ h₂ := by
  refine Presheaf.IsSheaf.hom_ext G₀.cond
    ⟨_, J₀.intersection_covering (IsDenseSubsite.imageSieve_mem J₀ J F h₁.q)
      (IsDenseSubsite.imageSieve_mem J₀ J F h₂.q)⟩ _ _ ?_
  rintro ⟨Z₀, a, ⟨b₁, w₁⟩, ⟨b₂, w₂⟩⟩
  refine Presheaf.IsSheaf.hom_ext G₀.cond
    ⟨_, (data X).mem₁₀ h₁.i₀ h₂.i₀ b₁ b₂ (by rw [w₁, w₂, assoc, assoc, h₁.fac, h₂.fac])⟩ _ _ ?_
  rintro ⟨W₀, c, hc⟩
  dsimp [res]
  simp only [assoc, IsDenseSubsite.mapPreimage_comp_map]
  apply presheafObj_mapPreimage_condition
  simp

end restriction

/-- Let `F : C₀ ⥤ C` be a dense subsite and `data : ∀ X, F.OneHypercoverDenseData J₀ J X`
be a family. Let `G₀` be a sheaf on `C₀`. Let `f : F.obj X₀ ⟶ X`.
This is the canonical morphism
`presheafObj data G₀ X ⟶ G₀.val.obj (op X₀)` (where `presheafObj data G₀ X`
is the value on `X` of the extension to `C` of the sheaf `G₀`,
see `OneHypercoverDenseData.essSurj.presheaf` and
`OneHypercoverDenseData.essSurj.isSheaf`). -/
noncomputable def restriction {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) :
    presheafObj data G₀ X ⟶ G₀.val.obj (op X₀) :=
  G₀.2.amalgamate ⟨_, (data X).sieve_mem f⟩
    (fun ⟨Y₀, g, hg⟩ ↦ restriction.res data G₀ hg.some) (by
      rintro ⟨Z₁, g₁, ⟨h₁⟩⟩ ⟨Z₂, g₂, ⟨h₂⟩⟩ ⟨T₀, p₁, p₂, w⟩
      dsimp at g₁ g₂ p₁ p₂ w ⊢
      rw [restriction.res_eq_res data G₀ _ h₁, restriction.res_eq_res data G₀ _ h₂]
      refine Presheaf.IsSheaf.hom_ext G₀.cond
        ⟨_, J₀.intersection_covering
          (IsDenseSubsite.imageSieve_mem J₀ J F (F.map p₁ ≫ h₁.q))
          (IsDenseSubsite.imageSieve_mem J₀ J F (F.map p₂ ≫ h₂.q))⟩ _ _ ?_
      rintro ⟨W₀, a, ⟨q₁, w₁⟩, ⟨q₂, w₂⟩⟩
      refine Presheaf.IsSheaf.hom_ext G₀.cond
        ⟨_, (data X).mem₁₀ h₁.i₀ h₂.i₀ q₁ q₂ (by
        simp only [w₁, w₂, assoc, h₁.fac, h₂.fac, ← Functor.map_comp_assoc, w])⟩ _ _ ?_
      rintro ⟨U₀, b, hb⟩
      dsimp
      simp only [assoc, restriction.res, IsDenseSubsite.mapPreimage_comp_map]
      apply presheafObj_mapPreimage_condition
      simp only [assoc, h₁.fac, h₂.fac, ← Functor.map_comp_assoc, w])

lemma restriction_map {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) {Y₀ : C₀}
    (g : Y₀ ⟶ X₀) {i : (data X).I₀} (p : F.obj Y₀ ⟶ F.obj ((data X).X i))
    (fac : p ≫ (data X).f i = F.map g ≫ f) :
    restriction data G₀ f ≫ G₀.val.map g.op =
      presheafObjπ data G₀ X i ≫ IsDenseSubsite.mapPreimage J F G₀ p := by
  have hg : (data X).sieve f g := ⟨i, p, fac⟩
  dsimp only [restriction]
  rw [G₀.2.amalgamate_map _ _ _ ⟨_, g, hg⟩]
  apply presheafObj_mapPreimage_condition
  rw [hg.some.fac, fac]

lemma restriction_eq_of_fac {X : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X)
    {i : (data X).I₀} (p : F.obj X₀ ⟶ F.obj ((data X).X i))
    (fac : p ≫ (data X).f i = f) :
    restriction data G₀ f =
      presheafObjπ data G₀ X i ≫ IsDenseSubsite.mapPreimage J F G₀ p := by
  simpa using restriction_map data G₀ f (𝟙 _) p (by simpa using fac)

/-- Auxiliary definition for `OneHypercoverDenseData.essSurj.presheaf`. -/
noncomputable def presheafMap {X Y : C} (f : X ⟶ Y) :
    presheafObj data G₀ Y ⟶ presheafObj data G₀ X :=
  Multiequalizer.lift _ _ (fun i₀ ↦ restriction data G₀ ((data X).f i₀ ≫ f)) (by
    rintro ⟨⟨i₁, i₂⟩, j⟩
    obtain ⟨a, h₁, h₂⟩ : ∃ a, a = F.map ((data X).p₁ j) ≫ (data X).f i₁ ≫ f ∧
        a = F.map ((data X).p₂ j) ≫ (data X).f i₂ ≫ f := ⟨_, rfl, (data X).w_assoc j _⟩
    refine Presheaf.IsSheaf.hom_ext G₀.cond
      ⟨_, cover_lift F J₀ _ (J.pullback_stable a (data Y).mem₀)⟩ _ _ ?_
    rintro ⟨W₀, b, ⟨_, p, _, ⟨i⟩, fac⟩⟩
    dsimp at fac ⊢
    simp only [assoc, ← map_comp, ← op_comp]
    rw [restriction_map (p := p), restriction_map (p := p)]
    all_goals simp_all)

@[reassoc (attr := simp)]
lemma presheafMap_π {X Y : C} (f : X ⟶ Y) (i : (data X).I₀) :
    presheafMap data G₀ f ≫ presheafObjπ data G₀ X i =
      restriction data G₀ ((data X).f i ≫ f) :=
  Multiequalizer.lift_ι _ _ _ _ _

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
lemma presheafMap_restriction {X Y : C} {X₀ : C₀} (f : F.obj X₀ ⟶ X) (g : X ⟶ Y) :
    presheafMap data G₀ g ≫ restriction data G₀ f = restriction data G₀ (f ≫ g) := by
  refine Presheaf.IsSheaf.hom_ext G₀.cond ⟨_, GrothendieckTopology.bind_covering
    (hS := cover_lift F J₀ J (J.pullback_stable f (data X).mem₀)) (hR := fun Y₀ a ha ↦
      cover_lift F J₀ J (J.pullback_stable
        (Sieve.ofArrows.h ha ≫ (data X).f (Sieve.ofArrows.i ha) ≫ g) (data Y).mem₀))⟩ _ _ ?_
  rintro ⟨U₀, _, Y₀, c, d, hd, hc, rfl⟩
  have hc' := Sieve.ofArrows.fac hc
  have hd' := Sieve.ofArrows.fac hd
  dsimp at hc hd hc' hd' ⊢
  rw [assoc, ← op_comp, restriction_map (i := Sieve.ofArrows.i hd)
    (p := F.map c ≫ Sieve.ofArrows.h hd) (fac := by grind),
    restriction_map (i := Sieve.ofArrows.i hc) (p := Sieve.ofArrows.h hc) (fac := by grind),
    presheafMap_π_assoc]
  dsimp
  have := J₀.intersection_covering (IsDenseSubsite.imageSieve_mem J₀ J F (Sieve.ofArrows.h hc))
    (J₀.pullback_stable c (IsDenseSubsite.imageSieve_mem J₀ J F (Sieve.ofArrows.h hd)))
  refine Presheaf.IsSheaf.hom_ext G₀.cond ⟨_, this⟩ _ _ ?_
  rintro ⟨V₀, a, ⟨x₁, fac₁⟩, ⟨x₂, fac₂⟩⟩
  dsimp
  rw [assoc, assoc,
    IsDenseSubsite.mapPreimage_map_of_fac J F G₀ _ _ x₂ (by simpa using fac₂.symm),
    IsDenseSubsite.mapPreimage_map_of_fac J F G₀ _ _ x₁ fac₁.symm,
    restriction_map data G₀ _ _ (F.map x₁) (by grind), IsDenseSubsite.mapPreimage_map]

lemma presheafMap_id (X : C) :
    presheafMap data G₀ (𝟙 X) = 𝟙 _ := by
  ext i
  rw [presheafMap_π, comp_id, id_comp,
    restriction_eq_of_fac data G₀ ((data X).f i) (𝟙 _) (by simp),
    IsDenseSubsite.mapPreimage_id, comp_id]

@[reassoc]
lemma presheafMap_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    presheafMap data G₀ (f ≫ g) = presheafMap data G₀ g ≫ presheafMap data G₀ f := by
  ext i
  dsimp
  rw [assoc, presheafMap_π, presheafMap_π, presheafMap_restriction, assoc]

/-- Let `F : C₀ ⥤ C` be a dense subsite and `data : ∀ X, F.OneHypercoverDenseData J₀ J X`
be a family. Let `G₀` be a sheaf on `C₀`. This is a presheaf on `C` which
extends `G₀`, and we shall also show that it is a sheaf (TODO). -/
@[simps]
noncomputable def presheaf : Cᵒᵖ ⥤ A where
  obj X := presheafObj data G₀ X.unop
  map f := presheafMap data G₀ f.unop
  map_id X := presheafMap_id data G₀ X.unop
  map_comp f g := presheafMap_comp data G₀ g.unop f.unop

end essSurj

end

end OneHypercoverDenseData

end Functor

end CategoryTheory
