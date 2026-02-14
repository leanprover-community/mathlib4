/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Hypercover.Zero

/-!
# 1-hypercovers

Given a Grothendieck topology `J` on a category `C`, we define the type of
`1`-hypercovers of an object `S : C`. They consist of a covering family
of morphisms `X i ⟶ S` indexed by a type `I₀` and, for each tuple `(i₁, i₂)`
of elements of `I₀`, a "covering `Y j` of the fibre product of `X i₁` and
`X i₂` over `S`", a condition which is phrased here without assuming that
the fibre product actually exists.

The definition `OneHypercover.isLimitMultifork` shows that if `E` is a
`1`-hypercover of `S`, and `F` is a sheaf, then `F.obj (op S)`
identifies to the multiequalizer of suitable maps
`F.obj (op (E.X i)) ⟶ F.obj (op (E.Y j))`.

-/

@[expose] public section

universe w'' w' w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {A : Type*} [Category* A]

/-- The categorical data that is involved in a `1`-hypercover of an object `S`. This
consists of a family of morphisms `f i : X i ⟶ S` for `i : I₀`, and for each
tuple `(i₁, i₂)` of elements in `I₀`, a family of objects `Y j` indexed by
a type `I₁ i₁ i₂`, which are equipped with a map to the fibre product of `X i₁`
and `X i₂`, which is phrased here as the data of the two projections
`p₁ : Y j ⟶ X i₁`, `p₂ : Y j ⟶ X i₂` and the relation `p₁ j ≫ f i₁ = p₂ j ≫ f i₂`.
(See `GrothendieckTopology.OneHypercover` for the topological conditions.) -/
structure PreOneHypercover (S : C) extends PreZeroHypercover.{w} S where
  /-- the index type of the coverings of the fibre products -/
  I₁ (i₁ i₂ : I₀) : Type w
  /-- the objects in the coverings of the fibre products -/
  Y ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : C
  /-- the first projection `Y j ⟶ X i₁` -/
  p₁ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₁
  /-- the second projection `Y j ⟶ X i₂` -/
  p₂ ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : Y j ⟶ X i₂
  w ⦃i₁ i₂ : I₀⦄ (j : I₁ i₁ i₂) : p₁ j ≫ f i₁ = p₂ j ≫ f i₂

namespace PreOneHypercover

variable {S : C} (E : PreOneHypercover.{w} S)

/-- Given an object `W` equipped with morphisms `p₁ : W ⟶ E.X i₁`, `p₂ : W ⟶ E.X i₂`,
this is the sieve of `W` which consists of morphisms `g : Z ⟶ W` such that there exists `j`
and `h : Z ⟶ E.Y j` such that `g ≫ p₁ = h ≫ E.p₁ j` and `g ≫ p₂ = h ≫ E.p₂ j`.
See lemmas `sieve₁_eq_pullback_sieve₁'` and `sieve₁'_eq_sieve₁` for equational lemmas
regarding this sieve. -/
@[simps]
def sieve₁ {i₁ i₂ : E.I₀} {W : C} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂) : Sieve W where
  arrows Z g := ∃ (j : E.I₁ i₁ i₂) (h : Z ⟶ E.Y j), g ≫ p₁ = h ≫ E.p₁ j ∧ g ≫ p₂ = h ≫ E.p₂ j
  downward_closed := by
    rintro Z Z' g ⟨j, h, fac₁, fac₂⟩ φ
    exact ⟨j, φ ≫ h, by simpa using φ ≫= fac₁, by simpa using φ ≫= fac₂⟩

section

variable {i₁ i₂ : E.I₀} [HasPullback (E.f i₁) (E.f i₂)]

/-- The obvious morphism `E.Y j ⟶ pullback (E.f i₁) (E.f i₂)` given by `E : PreOneHypercover S`. -/
noncomputable abbrev toPullback (j : E.I₁ i₁ i₂) [HasPullback (E.f i₁) (E.f i₂)] :
    E.Y j ⟶ pullback (E.f i₁) (E.f i₂) :=
  pullback.lift (E.p₁ j) (E.p₂ j) (E.w j)

variable (i₁ i₂) in
/-- The sieve of `pullback (E.f i₁) (E.f i₂)` given by `E : PreOneHypercover S`. -/
noncomputable def sieve₁' : Sieve (pullback (E.f i₁) (E.f i₂)) :=
  Sieve.ofArrows _ (fun (j : E.I₁ i₁ i₂) => E.toPullback j)

lemma sieve₁_eq_pullback_sieve₁' {W : C} (p₁ : W ⟶ E.X i₁) (p₂ : W ⟶ E.X i₂)
    (w : p₁ ≫ E.f i₁ = p₂ ≫ E.f i₂) :
    E.sieve₁ p₁ p₂ = (E.sieve₁' i₁ i₂).pullback (pullback.lift _ _ w) := by
  ext Z g
  constructor
  · rintro ⟨j, h, fac₁, fac₂⟩
    exact ⟨_, h, _, ⟨j⟩, by cat_disch⟩
  · rintro ⟨_, h, w, ⟨j⟩, fac⟩
    exact ⟨j, h, by simpa using fac.symm =≫ pullback.fst _ _,
      by simpa using fac.symm =≫ pullback.snd _ _⟩

variable (i₁ i₂) in
lemma sieve₁'_eq_sieve₁ : E.sieve₁' i₁ i₂ = E.sieve₁ (pullback.fst _ _) (pullback.snd _ _) := by
  rw [← Sieve.pullback_id (S := E.sieve₁' i₁ i₂),
    sieve₁_eq_pullback_sieve₁' _ _ _ pullback.condition]
  congr
  cat_disch

end

/-- The sigma type of all `E.I₁ i₁ i₂` for `⟨i₁, i₂⟩ : E.I₀ × E.I₀`. -/
abbrev I₁' : Type w := Sigma (fun (i : E.I₀ × E.I₀) => E.I₁ i.1 i.2)

/-- The `1`-components as a function from the sigma type over `E.I₁ i₁ i₂`. -/
def Y' (i : E.I₁') : C := E.Y i.2

@[simp]
lemma Y'_apply (i : E.I₁') : E.Y' i = E.Y i.2 := rfl

/-- The shape of the multiforks attached to `E : PreOneHypercover S`. -/
@[simps]
def multicospanShape : MulticospanShape where
  L := E.I₀
  R := E.I₁'
  fst j := j.1.1
  snd j := j.1.2

/-- The diagram of the multifork attached to a presheaf
`F : Cᵒᵖ ⥤ A`, `S : C` and `E : PreOneHypercover S`. -/
@[simps]
def multicospanIndex (F : Cᵒᵖ ⥤ A) : MulticospanIndex E.multicospanShape A where
  left i := F.obj (Opposite.op (E.X i))
  right j := F.obj (Opposite.op (E.Y j.2))
  fst j := F.map ((E.p₁ j.2).op)
  snd j := F.map ((E.p₂ j.2).op)

/-- The multifork attached to a presheaf `F : Cᵒᵖ ⥤ A`, `S : C` and `E : PreOneHypercover S`. -/
def multifork (F : Cᵒᵖ ⥤ A) :
    Multifork (E.multicospanIndex F) :=
  Multifork.ofι _ (F.obj (Opposite.op S)) (fun i₀ => F.map (E.f i₀).op) (by
    rintro ⟨⟨i₁, i₂⟩, (j : E.I₁ i₁ i₂)⟩
    dsimp
    simp only [← F.map_comp, ← op_comp, E.w])

lemma multifork_ι (F : Cᵒᵖ ⥤ A) (i : E.I₀) : (E.multifork F).ι i = F.map (E.f i).op := rfl

/-- The fork associated to a pre-`0`-hypercover induced by taking the coproduct of the
components. -/
@[simps! pt]
def forkOfIsColimit {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
    (F : Cᵒᵖ ⥤ A) :
    Fork (F.map (Cofan.IsColimit.desc hd fun _ ↦ E.p₁ _ ≫ c.inj _).op)
      (F.map (Cofan.IsColimit.desc hd fun _ ↦ E.p₂ _ ≫ c.inj _).op) :=
  .ofι (F.map (Cofan.IsColimit.desc hc E.f).op) <| by
    simp_rw [← Functor.map_comp, ← op_comp]
    congr 2
    exact Cofan.IsColimit.hom_ext hd _ _ (by simp [E.w])

@[reassoc (attr := simp)]
lemma forkOfIsColimit_ι_map_inj {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'}
    (hd : IsColimit d) (F : Cᵒᵖ ⥤ A) (i : E.I₀) :
    (E.forkOfIsColimit hc hd F).ι ≫ F.map (c.inj i).op = F.map (E.f i).op := by
  simp [forkOfIsColimit, ← Functor.map_comp, ← op_comp]

open Opposite

/-- The multifork associated to a pre-`1`-hypercover is limiting if and only if
the fork induced by taking the coproduct of the components is limiting. -/
noncomputable def isLimitMultiforkEquivIsLimitFork
    {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d) (F : Cᵒᵖ ⥤ A)
    [PreservesLimit (Discrete.functor fun i ↦ Opposite.op (E.X i)) F]
    [PreservesLimit (Discrete.functor fun i ↦ Opposite.op (E.Y' i)) F] :
    IsLimit (E.multifork F) ≃ IsLimit (E.forkOfIsColimit hc hd F) := by
  letI c' : Fan (E.multicospanIndex F).left := Fan.mk _ fun i ↦ F.map (c.inj i).op
  letI hc' : IsLimit c' := isLimitFanMkObjOfIsLimit _ _ (fun i : E.I₀ ↦ _) (Cofan.IsColimit.op hc)
  letI d' : Fan (E.multicospanIndex F).right := Fan.mk _ fun i ↦ F.map (d.inj i).op
  letI hd' : IsLimit d' := isLimitFanMkObjOfIsLimit _ _ (fun i : E.I₁' ↦ _) (Cofan.IsColimit.op hd)
  refine (IsLimit.ofConeEquiv <|
    (E.multicospanIndex F).multiforkEquivPiForkOfIsLimit hc' hd').symm.trans ?_
  refine Fork.isLimitEquivOfIsos _ _ (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · refine Fan.IsLimit.hom_ext hd' _ _ fun i ↦ ?_
    simp only [multicospanShape_L, multicospanIndex_right, multicospanShape_R, Iso.refl_hom,
      Y'_apply, id_comp, comp_id]
    rw [MulticospanIndex.fstPiMapOfIsLimit_proj]
    simp [c', d', ← F.map_comp, ← op_comp]
  · refine Fan.IsLimit.hom_ext hd' _ _ fun i ↦ ?_
    simp only [multicospanShape_L, multicospanIndex_right, multicospanShape_R, Iso.refl_hom,
      Y'_apply, id_comp, comp_id]
    rw [MulticospanIndex.sndPiMapOfIsLimit_proj]
    simp [c', d', ← F.map_comp, ← op_comp]
  · refine Fan.IsLimit.hom_ext hc' _ _ fun i ↦ ?_
    simp
    simp [c', multifork_ι]

/-- The single object pre-`1`-hypercover obtained from taking coproducts of the components. -/
@[simps toPreZeroHypercover Y]
def sigmaOfIsColimit {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d) :
    PreOneHypercover.{w} S where
  __ := E.toPreZeroHypercover.sigmaOfIsColimit hc
  I₁ _ _ := PUnit
  Y _ _ _ := d.pt
  p₁ _ _ _ := Cofan.IsColimit.desc hd fun i ↦ E.p₁ _ ≫ c.inj _
  p₂ _ _ _ := Cofan.IsColimit.desc hd fun i ↦ E.p₂ _ ≫ c.inj _
  w _ _ _ := Cofan.IsColimit.hom_ext hd _ _ (by simp [E.w])

@[reassoc (attr := simp)]
lemma p₁_sigmaOfIsColimit {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
    (i : E.I₁') {a b : PUnit} (r : (E.sigmaOfIsColimit hc hd).I₁ a b) :
    d.inj i ≫ (E.sigmaOfIsColimit hc hd).p₁ r = E.p₁ _ ≫ c.inj _ := by
  simp [sigmaOfIsColimit]

@[reassoc (attr := simp)]
lemma p₂_sigmaOfIsColimit {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d)
    (i : E.I₁') {a b : PUnit} (r : (E.sigmaOfIsColimit hc hd).I₁ a b) :
    d.inj i ≫ (E.sigmaOfIsColimit hc hd).p₂ r = E.p₂ _ ≫ c.inj _ := by
  simp [sigmaOfIsColimit]

instance {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d) :
    Unique (E.sigmaOfIsColimit hc hd).multicospanShape.L :=
  inferInstanceAs <| Unique PUnit

instance {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'} (hd : IsColimit d) :
    Unique (E.sigmaOfIsColimit hc hd).multicospanShape.R where
  default := ⟨(⟨⟩, ⟨⟩), ⟨⟩⟩
  uniq _ := rfl

/-- If `E` is a pre-`1`-hypercover and `F` a presheaf, the induced equalizer of
the single object covering obtained from `E` by taking coproducts is limiting
if and only if the induced multiequalizer of `E` is limiting. -/
noncomputable
def isLimitSigmaOfIsColimitEquiv {c : Cofan E.X} (hc : IsColimit c) {d : Cofan E.Y'}
    (hd : IsColimit d) (F : Cᵒᵖ ⥤ A)
    [PreservesLimit (Discrete.functor fun i ↦ Opposite.op (E.X i)) F]
    [PreservesLimit (Discrete.functor fun i ↦ Opposite.op (E.Y' i)) F] :
    IsLimit ((E.sigmaOfIsColimit hc hd).multifork F) ≃ IsLimit (E.multifork F) := by
  refine (Multifork.isLimitEquivOfIsos _ _ ?_ ?_ ?_ ?_ ?_ ?_).trans
    (IsLimit.ofConeEquiv <| (MulticospanIndex.multiforkOfParallelHomsEquivFork
      (E.sigmaOfIsColimit hc hd).multicospanShape _ _).symm) |>.trans
      (E.isLimitMultiforkEquivIsLimitFork hc hd F).symm
  · exact .refl _
  · exact fun _ ↦ .refl _
  · exact fun _ ↦ .refl _
  all_goals cat_disch

/-- The trivial pre-`1`-hypercover of `S` with a single component `S`. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
def trivial (S : C) : PreOneHypercover.{w} S where
  __ := PreZeroHypercover.singleton (𝟙 S)
  I₁ _ _ := PUnit
  Y _ _ _ := S
  p₁ _ _ _ := 𝟙 _
  p₂ _ _ _ := 𝟙 _
  w _ _ _ := by simp

lemma sieve₀_trivial (S : C) : (trivial S).sieve₀ = ⊤ := by
  rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, ← PreZeroHypercover.presieve₀]
  simp

@[simp]
lemma sieve₁_trivial {S : C} {W : C} {p : W ⟶ S} :
    (trivial S).sieve₁ (i₁ := ⟨⟩) (i₂ := ⟨⟩) p p = ⊤ := by ext; simp

instance : Nonempty (PreOneHypercover.{w} S) := ⟨trivial S⟩

section

/-- Intersection of two pre-`1`-hypercovers. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
noncomputable
def inter (E F : PreOneHypercover S) [∀ i j, HasPullback (E.f i) (F.f j)]
    [∀ (i j : E.I₀) (k : E.I₁ i j) (a b : F.I₀) (l : F.I₁ a b),
      HasPullback (E.p₁ k ≫ E.f i) (F.p₁ l ≫ F.f a)] :
    PreOneHypercover S where
  __ := E.toPreZeroHypercover.inter F.toPreZeroHypercover
  I₁ i j := E.I₁ i.1 j.1 × F.I₁ i.2 j.2
  Y i j k := pullback (E.p₁ k.1 ≫ E.f _) (F.p₁ k.2 ≫ F.f _)
  p₁ i j k := pullback.map _ _ _ _ (E.p₁ _) (F.p₁ _) (𝟙 S) (by simp) (by simp)
  p₂ i j k := pullback.map _ _ _ _ (E.p₂ _) (F.p₂ _) (𝟙 S) (by simp [E.w]) (by simp [F.w])
  w := by simp [E.w]

variable {E} {F : PreOneHypercover S}

lemma sieve₁_inter [HasPullbacks C] {i j : E.I₀ × F.I₀} {W : C}
    {p₁ : W ⟶ pullback (E.f i.1) (F.f i.2)}
    {p₂ : W ⟶ pullback (E.f j.1) (F.f j.2)}
    (w : p₁ ≫ pullback.fst _ _ ≫ E.f _ = p₂ ≫ pullback.fst _ _ ≫ E.f _) :
    (inter E F).sieve₁ p₁ p₂ = Sieve.bind
      (E.sieve₁ (p₁ ≫ pullback.fst _ _) (p₂ ≫ pullback.fst _ _))
      (fun _ f _ ↦ (F.sieve₁ (p₁ ≫ pullback.snd _ _) (p₂ ≫ pullback.snd _ _)).pullback f) := by
  ext Y f
  let p : W ⟶ pullback ((inter E F).f i) ((inter E F).f j) :=
    pullback.lift p₁ p₂ w
  refine ⟨fun ⟨k, a, h₁, h₂⟩ ↦ ?_, fun ⟨Z, a, b, ⟨k, e, h₁, h₂⟩, ⟨l, u, u₁, u₂⟩, hab⟩ ↦ ?_⟩
  · refine ⟨pullback p ((E.inter F).toPullback k), pullback.lift f a ?_,
        pullback.fst _ _, ?_, ?_, ?_⟩
    · apply pullback.hom_ext
      · apply pullback.hom_ext <;> simp [p, h₁, toPullback]
      · apply pullback.hom_ext <;> simp [p, h₂, toPullback]
    · refine ⟨k.1, pullback.snd _ _ ≫ pullback.fst _ _, ?_, ?_⟩
      · have : p₁ ≫ pullback.fst (E.f i.1) (F.f i.2) = p ≫ pullback.fst _ _ ≫ pullback.fst _ _ := by
          simp [p]
        simp [this, pullback.condition_assoc, toPullback]
      · have : p₂ ≫ pullback.fst (E.f j.1) (F.f j.2) = p ≫ pullback.snd _ _ ≫ pullback.fst _ _ := by
          simp [p]
        simp [this, pullback.condition_assoc, toPullback]
    · exact ⟨k.2, a ≫ pullback.snd _ _, by simp [reassoc_of% h₁], by simp [reassoc_of% h₂]⟩
    · simp
  · subst hab
    refine ⟨(k, l), pullback.lift (a ≫ e) u ?_, ?_, ?_⟩
    · simp only [Category.assoc] at u₁
      simp [← reassoc_of% h₁, w, ← reassoc_of% u₁, ← pullback.condition]
    · apply pullback.hom_ext
      · simp [h₁]
      · simpa using u₁
    · apply pullback.hom_ext
      · simp [h₂]
      · simpa using u₂

end

section Category

/-- A morphism of pre-`1`-hypercovers of `S` is a family of refinement morphisms commuting
with the structure morphisms of `E` and `F`. -/
@[ext]
structure Hom (E F : PreOneHypercover S) extends
    E.toPreZeroHypercover.Hom F.toPreZeroHypercover where
  /-- The map between indexing types of the coverings of the fibre products over `S`. -/
  s₁ {i j : E.I₀} (k : E.I₁ i j) : F.I₁ (s₀ i) (s₀ j)
  /-- The refinement morphisms between objects in the coverings of the fibre products over `S`. -/
  h₁ {i j : E.I₀} (k : E.I₁ i j) : E.Y k ⟶ F.Y (s₁ k)
  w₁₁ {i j : E.I₀} (k : E.I₁ i j) : h₁ k ≫ F.p₁ (s₁ k) = E.p₁ k ≫ h₀ i := by cat_disch
  w₁₂ {i j : E.I₀} (k : E.I₁ i j) : h₁ k ≫ F.p₂ (s₁ k) = E.p₂ k ≫ h₀ j := by cat_disch

attribute [reassoc] Hom.w₁₁ Hom.w₁₂

/-- The identity refinement of a pre-`1`-hypercover. -/
@[simps!]
def Hom.id (E : PreOneHypercover S) : Hom E E where
  __ := PreZeroHypercover.Hom.id _
  s₁ := _root_.id
  h₁ _ := 𝟙 _

variable {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S}
  {G : PreOneHypercover S}

/-- Composition of refinement morphisms of pre-`1`-hypercovers. -/
@[simps!]
def Hom.comp (f : E.Hom F) (g : F.Hom G) : E.Hom G where
  __ := PreZeroHypercover.Hom.comp _ _
  s₁ := g.s₁ ∘ f.s₁
  h₁ i := f.h₁ i ≫ g.h₁ _
  w₁₁ := by simp [w₁₁, w₁₁_assoc]
  w₁₂ := by simp [w₁₂, w₁₂_assoc]

/-- The induced index map `E.I₁' → F.I₁'` from a refinement morphism `E ⟶ F`. -/
@[simp]
def Hom.s₁' (f : E.Hom F) (k : E.I₁') : F.I₁' :=
  ⟨⟨f.s₀ k.1.1, f.s₀ k.1.2⟩, f.s₁ k.2⟩

@[simps! id_s₀ id_s₁ id_h₀ id_h₁ comp_s₀ comp_s₁ comp_h₀ comp_h₁]
instance : Category (PreOneHypercover S) where
  Hom := Hom
  id E := Hom.id E
  comp f g := f.comp g

/-- The forgetful functor from pre-`1`-hypercovers to pre-`0`-hypercovers. -/
@[simps]
def oneToZero : PreOneHypercover.{w} S ⥤ PreZeroHypercover.{w} S where
  obj f := f.1
  map f := f.1

/-- A refinement morphism `E ⟶ F` induces a morphism on associated multiequalizers. -/
def Hom.mapMultiforkOfIsLimit (f : E.Hom F) (P : Cᵒᵖ ⥤ A) {c : Multifork (E.multicospanIndex P)}
    (hc : IsLimit c) (d : Multifork (F.multicospanIndex P)) :
    d.pt ⟶ c.pt :=
  Multifork.IsLimit.lift hc (fun a ↦ d.ι (f.s₀ a) ≫ P.map (f.h₀ a).op) <| by
    intro (k : E.I₁')
    simp only [multicospanIndex_right, multicospanShape_fst, multicospanIndex_left,
      multicospanIndex_fst, assoc, multicospanShape_snd, multicospanIndex_snd]
    have heq := d.condition (f.s₁' k)
    simp only [Hom.s₁', multicospanIndex_right, multicospanShape_fst, multicospanIndex_left,
      multicospanIndex_fst, multicospanShape_snd, multicospanIndex_snd] at heq
    rw [← Functor.map_comp, ← op_comp, ← Hom.w₁₁, ← Functor.map_comp, ← op_comp, ← Hom.w₁₂]
    rw [op_comp, Functor.map_comp, reassoc_of% heq, op_comp, Functor.map_comp]

@[reassoc (attr := simp)]
lemma Hom.mapMultiforkOfIsLimit_ι {E F : PreOneHypercover.{w} S}
    (f : E.Hom F) (P : Cᵒᵖ ⥤ A) {c : Multifork (E.multicospanIndex P)} (hc : IsLimit c)
    (d : Multifork (F.multicospanIndex P)) (a : E.I₀) :
    f.mapMultiforkOfIsLimit P hc d ≫ c.ι a = d.ι (f.s₀ a) ≫ P.map (f.h₀ a).op := by
  simp [mapMultiforkOfIsLimit]

end Category

section

variable (F : PreOneHypercover.{w'} S) {G : PreOneHypercover.{w''} S}
  [∀ (i : E.I₀) (j : F.I₀), HasPullback (E.f i) (F.f j)]
  [∀ (i j : E.I₀) (k : E.I₁ i j) (a b : F.I₀) (l : F.I₁ a b),
    HasPullback (E.p₁ k ≫ E.f i) (F.p₁ l ≫ F.f a)]

/-- First projection from the intersection of two pre-`1`-hypercovers. -/
@[simps toHom s₁]
noncomputable
def interFst : (E.inter F).Hom E where
  __ := E.toPreZeroHypercover.interFst F.toPreZeroHypercover
  s₁ {i j} k := k.1
  h₁ _ := pullback.fst _ _

/-- Second projection from the intersection of two pre-`1`-hypercovers. -/
@[simps toHom s₁]
noncomputable
def interSnd : (E.inter F).Hom F where
  __ := E.toPreZeroHypercover.interSnd F.toPreZeroHypercover
  s₁ {i j} k := k.2
  h₁ _ := pullback.snd _ _

variable {E F} in
/-- Universal property of the intersection of two pre-`1`-hypercovers. -/
noncomputable
def interLift {G : PreOneHypercover.{w''} S} (f : G.Hom E) (g : G.Hom F) :
    G.Hom (E.inter F) where
  __ := PreZeroHypercover.interLift f.toHom g.toHom
  s₁ {i j} k := ⟨f.s₁ k, g.s₁ k⟩
  h₁ k := pullback.lift (f.h₁ k) (g.h₁ k) <| by
    rw [f.w₁₁_assoc k, g.w₁₁_assoc k]
    simp
  w₀ := by simp
  w₁₁ k := by
    apply pullback.hom_ext
    · simpa using f.w₁₁ k
    · simpa using g.w₁₁ k
  w₁₂ k := by
    apply pullback.hom_ext
    · simpa using f.w₁₂ k
    · simpa using g.w₁₂ k

end

end PreOneHypercover

namespace GrothendieckTopology

variable (J : GrothendieckTopology C)

/-- The type of `1`-hypercovers of an object `S : C` in a category equipped with a
Grothendieck topology `J`. This can be constructed from a covering of `S` and
a covering of the fibre products of the objects in this covering (see `OneHypercover.mk'`). -/
structure OneHypercover (S : C) extends PreOneHypercover.{w} S where
  mem₀ : toPreOneHypercover.sieve₀ ∈ J S
  mem₁ (i₁ i₂ : I₀) ⦃W : C⦄ (p₁ : W ⟶ X i₁) (p₂ : W ⟶ X i₂) (w : p₁ ≫ f i₁ = p₂ ≫ f i₂) :
    toPreOneHypercover.sieve₁ p₁ p₂ ∈ J W

variable {J}

lemma OneHypercover.mem_sieve₁' {S : C} (E : J.OneHypercover S)
    (i₁ i₂ : E.I₀) [HasPullback (E.f i₁) (E.f i₂)] :
    E.sieve₁' i₁ i₂ ∈ J _ := by
  rw [E.sieve₁'_eq_sieve₁]
  exact mem₁ _ _ _ _ _ pullback.condition

namespace OneHypercover

/-- In order to check that a certain data is a `1`-hypercover of `S`, it suffices to
check that the data provides a covering of `S` and of the fibre products. -/
@[simps toPreOneHypercover]
def mk' {S : C} (E : PreOneHypercover S) [E.HasPullbacks]
    (mem₀ : E.sieve₀ ∈ J S) (mem₁' : ∀ (i₁ i₂ : E.I₀), E.sieve₁' i₁ i₂ ∈ J _) :
    J.OneHypercover S where
  toPreOneHypercover := E
  mem₀ := mem₀
  mem₁ i₁ i₂ W p₁ p₂ w := by
    rw [E.sieve₁_eq_pullback_sieve₁' _ _ w]
    exact J.pullback_stable' _ (mem₁' i₁ i₂)

section

variable {S : C} (E : J.OneHypercover S) (F : Sheaf J A)

section

variable {E F}
variable (c : Multifork (E.multicospanIndex F.val))

/-- Auxiliary definition of `isLimitMultifork`. -/
noncomputable def multiforkLift : c.pt ⟶ F.val.obj (Opposite.op S) :=
  F.cond.amalgamateOfArrows _ E.mem₀ c.ι (fun W i₁ i₂ p₁ p₂ w => by
    apply F.cond.hom_ext ⟨_, E.mem₁ _ _ _ _ w⟩
    rintro ⟨T, g, j, h, fac₁, fac₂⟩
    dsimp
    simp only [assoc, ← Functor.map_comp, ← op_comp, fac₁, fac₂]
    simp only [op_comp, Functor.map_comp]
    simpa using c.condition ⟨⟨i₁, i₂⟩, j⟩ =≫ F.val.map h.op)

@[reassoc]
lemma multiforkLift_map (i₀ : E.I₀) : multiforkLift c ≫ F.val.map (E.f i₀).op = c.ι i₀ := by
  simp [multiforkLift]

end

/-- If `E : J.OneHypercover S` and `F : Sheaf J A`, then `F.obj (op S)` is
a multiequalizer of suitable maps `F.obj (op (E.X i)) ⟶ F.obj (op (E.Y j))`
induced by `E.p₁ j` and `E.p₂ j`. -/
noncomputable def isLimitMultifork : IsLimit (E.multifork F.1) :=
  Multifork.IsLimit.mk _ (fun c => multiforkLift c) (fun c => multiforkLift_map c) (by
    intro c m hm
    apply F.cond.hom_ext_ofArrows _ E.mem₀
    intro i₀
    dsimp only
    rw [multiforkLift_map]
    exact hm i₀)

end

section

variable {S : C}

/-- Forget the `1`-components of a `OneHypercover`. -/
@[simps toPreZeroHypercover]
def toZeroHypercover (E : OneHypercover.{w} J S) : J.toPrecoverage.ZeroHypercover S where
  __ := E.toPreZeroHypercover
  mem₀ := E.mem₀

variable (J) in
/-- The trivial `1`-hypercover of `S` where a single component `S`. -/
@[simps toPreOneHypercover]
def trivial (S : C) : OneHypercover.{w} J S where
  __ := PreOneHypercover.trivial S
  mem₀ := by simp only [PreOneHypercover.sieve₀_trivial, J.top_mem]
  mem₁ _ _ _ _ _ h := by
    simp only [PreOneHypercover.trivial_toPreZeroHypercover, PreZeroHypercover.singleton_X,
      PreZeroHypercover.singleton_f, Category.comp_id] at h
    subst h
    simp

instance (S : C) : Nonempty (J.OneHypercover S) := ⟨trivial J S⟩

/-- Intersection of two `1`-hypercovers. -/
@[simps toPreOneHypercover]
noncomputable
def inter [HasPullbacks C] (E F : J.OneHypercover S)
    [∀ (i : E.I₀) (j : F.I₀), HasPullback (E.f i) (F.f j)]
    [∀ (i j : E.I₀) (k : E.I₁ i j) (a b : F.I₀) (l : F.I₁ a b),
      HasPullback (E.p₁ k ≫ E.f i) (F.p₁ l ≫ F.f a)] : J.OneHypercover S where
  __ := E.toPreOneHypercover.inter F.toPreOneHypercover
  mem₀ := (E.toZeroHypercover.inter F.toZeroHypercover).mem₀
  mem₁ i₁ i₂ W p₁ p₂ h := by
    rw [PreOneHypercover.sieve₁_inter h]
    refine J.bind_covering (E.mem₁ _ _ _ _ (by simpa using h)) fun _ _ _ ↦ ?_
    exact J.pullback_stable _
      (F.mem₁ _ _ _ _ (by simpa [Category.assoc, ← pullback.condition]))

end

section Category

variable {S : C} {E : OneHypercover.{w} J S} {F : OneHypercover.{w'} J S}

/-- A morphism of `1`-hypercovers is a morphism of the underlying pre-`1`-hypercovers. -/
abbrev Hom (E : OneHypercover.{w} J S) (F : OneHypercover.{w'} J S) :=
  E.toPreOneHypercover.Hom F.toPreOneHypercover

@[simps! id_s₀ id_s₁ id_h₀ id_h₁ comp_s₀ comp_s₁ comp_h₀ comp_h₁]
instance : Category (J.OneHypercover S) where
  Hom := Hom
  id E := PreOneHypercover.Hom.id E.toPreOneHypercover
  comp f g := f.comp g

/-- An isomorphism of `1`-hypercovers is an isomorphism of pre-`1`-hypercovers. -/
@[simps]
def isoMk {E F : J.OneHypercover S} (f : E.toPreOneHypercover ≅ F.toPreOneHypercover) :
    E ≅ F where
  __ := f

end Category

section

open Opposite
variable {C : Type*} [Category* C] {K : GrothendieckTopology C} {P : Cᵒᵖ ⥤ Type*}
   {S : C} (E : K.OneHypercover S)

lemma isSheafFor_presieve₀ (h : Presieve.IsSheaf K P) : E.presieve₀.IsSheafFor P := by
  rw [Presieve.isSheafFor_iff_generate]
  exact h _ E.mem₀

lemma arrowsCompatible (h : Presieve.IsSeparated K P) (x : ∀ i, P.obj (op <| E.X i))
    (hc : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), P.map (E.p₁ k).op (x i) = P.map (E.p₂ k).op (x j)) :
    Presieve.Arrows.Compatible _ E.f x := by
  rintro i₁ i₂ Z g₁ g₂ heq
  refine (h _ (E.mem₁ _ _ _ _ heq)).ext fun W f ⟨T, u, h₁, h₂⟩ ↦ ?_
  rw [← FunctorToTypes.map_comp_apply, ← op_comp, h₁]
  conv_rhs => rw [← FunctorToTypes.map_comp_apply, ← op_comp, h₂]
  simp [hc]

/-- Glue sections of a `Type`-valued sheaf over a `1`-hypercover. -/
noncomputable def amalgamate (h : Presieve.IsSheaf K P) (x : ∀ i, P.obj (op <| E.X i))
    (hc : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), P.map (E.p₁ k).op (x i) = P.map (E.p₂ k).op (x j)) :
    P.obj (op S) :=
  (E.isSheafFor_presieve₀ h).amalgamate _
    ((E.arrowsCompatible h.isSeparated x hc).familyOfElements_compatible)

@[simp]
lemma map_amalgamate (h : Presieve.IsSheaf K P) (x : ∀ i, P.obj (op <| E.X i))
    (hc : ∀ ⦃i j : E.I₀⦄ (k : E.I₁ i j), P.map (E.p₁ k).op (x i) = P.map (E.p₂ k).op (x j))
    (i : E.I₀) :
    P.map (E.f i).op (E.amalgamate h x hc) = x i := by
  rw [amalgamate, Presieve.IsSheafFor.valid_glue _ _ _ ⟨i⟩]
  simp

end

end OneHypercover

namespace Cover

variable {X : C} (S : J.Cover X)

/-- The tautological 1-pre-hypercover induced by `S : J.Cover X`. Its index type `I₀`
is given by `S.Arrow` (i.e. all the morphisms in the sieve `S`), while `I₁` is given
by all possible pullback cones. -/
@[simps]
def preOneHypercover : PreOneHypercover.{max u v} X where
  I₀ := S.Arrow
  X f := f.Y
  f f := f.f
  I₁ f₁ f₂ := f₁.Relation f₂
  Y _ _ r := r.Z
  p₁ _ _ r := r.g₁
  p₂ _ _ r := r.g₂
  w _ _ r := r.w

@[simp]
lemma preOneHypercover_sieve₀ : S.preOneHypercover.sieve₀ = S.1 := by
  ext Y f
  constructor
  · rintro ⟨_, _, _, ⟨g⟩, rfl⟩
    exact S.1.downward_closed g.hf _
  · intro hf
    exact Sieve.ofArrows_mk _ _ ({ hf := hf, .. } : S.Arrow)

lemma preOneHypercover_sieve₁ (f₁ f₂ : S.Arrow) {W : C} (p₁ : W ⟶ f₁.Y) (p₂ : W ⟶ f₂.Y)
    (w : p₁ ≫ f₁.f = p₂ ≫ f₂.f) :
    S.preOneHypercover.sieve₁ p₁ p₂ = ⊤ := by
  ext Y f
  simp only [Sieve.top_apply, iff_true]
  exact ⟨{ w := w, .. }, f, rfl, rfl⟩

/-- The tautological 1-hypercover induced by `S : J.Cover X`. Its index type `I₀`
is given by `S.Arrow` (i.e. all the morphisms in the sieve `S`), while `I₁` is given
by all possible pullback cones. -/
@[simps toPreOneHypercover]
def oneHypercover : J.OneHypercover X where
  toPreOneHypercover := S.preOneHypercover
  mem₀ := by simp
  mem₁ f₁ f₂ _ p₁ p₂ w := by simp [S.preOneHypercover_sieve₁ f₁ f₂ p₁ p₂ w]

end Cover

end GrothendieckTopology

lemma PreZeroHypercover.ext_of_isSeparatedFor {P : Cᵒᵖ ⥤ Type*} {S : C} (E : PreZeroHypercover S)
    (h : E.presieve₀.IsSeparatedFor P) {x y : P.obj (.op S)}
    (hi : ∀ i, P.map (E.f i).op x = P.map (E.f i).op y) :
    x = y :=
  h.ext fun _ _ ⟨i⟩ ↦ hi i

/-- If the pairwise pullbacks exist, this is the pre-`1`-hypercover where the covers
by the pullbacks are given by the pullbacks themselves. -/
@[simps toPreZeroHypercover I₁ Y p₁ p₂]
noncomputable def PreZeroHypercover.toPreOneHypercover {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] :
    PreOneHypercover S where
  __ := E
  I₁ _ _ := PUnit
  Y i j _ := pullback (E.f i) (E.f j)
  p₁ _ _ _ := pullback.fst _ _
  p₂ _ _ _ := pullback.snd _ _
  w _ _ _ := pullback.condition

instance {S : C} (E : PreZeroHypercover S) [E.HasPullbacks] :
    E.toPreOneHypercover.HasPullbacks := by
  dsimp
  infer_instance

@[simp]
lemma sieve₁'_toPreOneHypercover_eq_top {S : C} (E : PreZeroHypercover S) [E.HasPullbacks]
    (i j : E.I₀) :
    E.toPreOneHypercover.sieve₁' i j = ⊤ := by
  rw [eq_top_iff]
  intro Y f _
  refine ⟨pullback (E.f i) (E.f j), f, 𝟙 _, ?_, by simp⟩
  refine Presieve.ofArrows.mk' ⟨⟩ rfl ?_
  apply pullback.hom_ext <;> simp [PreOneHypercover.toPullback]

/-- If the pairwise pullbacks exist, this is the pre-`1`-hypercover where the covers
by the pullbacks are given by the pullbacks themselves. -/
@[simps! toPreOneHypercover]
noncomputable def Precoverage.ZeroHypercover.toOneHypercover {J : Precoverage C}
    {S : C} (E : J.ZeroHypercover S) [E.HasPullbacks] :
    (J.toGrothendieck).OneHypercover S :=
  .mk' E.toPreZeroHypercover.toPreOneHypercover (J.generate_mem_toGrothendieck E.mem₀) (by simp)

end CategoryTheory
