/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.ZeroHypercover

/-!
# 1-hypercovers

Given a Grothendieck topology `J` on a category `C`, we define the type of
`1`-hypercovers of an object `S : C`. They consists of a covering family
of morphisms `X i ⟶ S` indexed by a type `I₀` and, for each tuple `(i₁, i₂)`
of elements of `I₀`, a "covering `Y j` of the fibre product of `X i₁` and
`X i₂` over `S`", a condition which is phrased here without assuming that
the fibre product actually exist.

The definition `OneHypercover.isLimitMultifork` shows that if `E` is a
`1`-hypercover of `S`, and `F` is a sheaf, then `F.obj (op S)`
identifies to the multiequalizer of suitable maps
`F.obj (op (E.X i)) ⟶ F.obj (op (E.Y j))`.

-/

universe w' w v u

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {A : Type*} [Category A]

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

variable (i₁ i₂) in
@[simps]
noncomputable
def cover₀ : PreZeroHypercover (Limits.pullback (E.f i₁) (E.f i₂)) where
  I₀ := E.I₁ i₁ i₂
  X k := E.Y k
  f k := E.toPullback k

end

/-- The sigma type of all `E.I₁ i₁ i₂` for `⟨i₁, i₂⟩ : E.I₀ × E.I₀`. -/
abbrev I₁' : Type w := Sigma (fun (i : E.I₀ × E.I₀) => E.I₁ i.1 i.2)

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

noncomputable
def toMultiequalizer (F : Cᵒᵖ ⥤ A) [HasMultiequalizer (E.multicospanIndex F)] :
    F.obj (Opposite.op S) ⟶ multiequalizer (E.multicospanIndex F) :=
  limit.lift _ (E.multifork F)

-- if we don't have it, generalise this accordingly
lemma nonempty_isLimit_multifork_iff_isIso (F : Cᵒᵖ ⥤ A)
    [HasMultiequalizer (E.multicospanIndex F)] :
    Nonempty (IsLimit (E.multifork F)) ↔ IsIso (E.toMultiequalizer F) := by
  refine ⟨fun ⟨h⟩ ↦ ?_, fun h ↦ ?_⟩
  · let c : E.multifork F ⟶ limit.cone _ := (limit.isLimit _).liftConeMorphism _
    have : IsIso c := h.hom_isIso (limit.isLimit _) _
    exact (Cones.forget _).map_isIso c
  · constructor
    have : IsIso ((limit.isLimit (E.multicospanIndex F).multicospan).lift (E.multifork F)) := h
    apply IsLimit.ofPointIso (limit.isLimit _)

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

lemma Hom.ext' {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S}
    {f g : E.Hom F} (h : f.toHom = g.toHom)
    (hs₁ : ∀ {i j} (k : E.I₁ i j), f.s₁ k = h ▸ g.s₁ k)
    (hh₁ : ∀ {i j} (k : E.I₁ i j),
      f.h₁ k = g.h₁ k ≫ eqToHom (by rw [hs₁]; congr 1 <;> simp [h])) :
    f = g := by
  cases f
  cases g
  simp at h
  subst h
  simp only [mk.injEq, heq_eq_eq, true_and]
  simp at hs₁
  simp at hh₁
  refine ⟨?_, ?_⟩
  · ext k
    apply hs₁
  · apply Function.hfunext rfl
    intro i j hij
    simp at hij
    subst hij
    apply Function.hfunext rfl
    intro j j' hjj'
    simp at hjj'
    subst hjj'
    apply Function.hfunext rfl
    intro k k' hkk'
    simp at hkk'
    subst hkk'
    rw [hh₁ k]
    simp

lemma Hom.ext'' {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S}
    {f g : E.Hom F} (hs₀ : f.s₀ = g.s₀) (hh₀ : ∀ i, f.h₀ i = g.h₀ i ≫ eqToHom (by rw [hs₀]))
    (hs₁ : ∀ {i j} (k : E.I₁ i j), f.s₁ k = hs₀ ▸ g.s₁ k)
    (hh₁ : ∀ {i j} (k : E.I₁ i j),
      f.h₁ k = g.h₁ k ≫ eqToHom (by rw [hs₁]; congr 1 <;> simp [hs₀])) :
    f = g := by
  have : f.toHom = g.toHom := PreZeroHypercover.Hom.ext' hs₀ hh₀
  cases f
  cases g
  simp at this
  subst this
  simp only [mk.injEq, heq_eq_eq, true_and]
  simp at hs₁
  simp at hh₁
  refine ⟨?_, ?_⟩
  · ext k
    apply hs₁
  · apply Function.hfunext rfl
    intro i j hij
    simp at hij
    subst hij
    apply Function.hfunext rfl
    intro j j' hjj'
    simp at hjj'
    subst hjj'
    apply Function.hfunext rfl
    intro k k' hkk'
    simp at hkk'
    subst hkk'
    rw [hh₁ k]
    simp

/-- The forgetful functor from pre-`1`-hypercovers to pre-`0`-hypercovers. -/
@[simps]
def oneToZero : PreOneHypercover.{w} S ⥤ PreZeroHypercover.{w} S where
  obj f := f.1
  map f := f.1

/-- A homotopy of refinements `E ⟶ F` is a family of morphisms `Xᵢ ⟶ Yₐ` where
`Yₐ` is a component of the cover of `X_{f(i)} ×[S] X_{g(i)}`. -/
structure Homotopy (f g : E.Hom F) where
  /-- The index map sending `i : E.I₀` to `a` above `(f(i), g(i))`. -/
  H (i : E.I₀) : F.I₁ (f.s₀ i) (g.s₀ i)
  /-- The morphism `Xᵢ ⟶ Yₐ`. -/
  a (i : E.I₀) : E.X i ⟶ F.Y (H i)
  wl (i : E.I₀) : a i ≫ F.p₁ (H i) = f.h₀ i
  wr (i : E.I₀) : a i ≫ F.p₂ (H i) = g.h₀ i

attribute [reassoc (attr := simp)] Homotopy.wl Homotopy.wr

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

/-- Homotopic refinements induce the same map on multiequalizers. -/
lemma Homotopy.mapMultiforkOfIsLimit_eq {E F : PreOneHypercover.{w} S}
    {f g : E.Hom F} (H : Homotopy f g)
    (P : Cᵒᵖ ⥤ A) {c : Multifork (E.multicospanIndex P)} (hc : IsLimit c)
    (d : Multifork (F.multicospanIndex P)) :
    f.mapMultiforkOfIsLimit P hc d = g.mapMultiforkOfIsLimit P hc d := by
  refine Multifork.IsLimit.hom_ext hc fun a ↦ ?_
  have heq := d.condition ⟨⟨(f.s₀ a), (g.s₀ a)⟩, H.H a⟩
  simp only [multicospanIndex_right, multicospanShape_fst, multicospanIndex_left,
    multicospanIndex_fst, multicospanShape_snd, multicospanIndex_snd] at heq
  simp [-Homotopy.wl, -Homotopy.wr, ← H.wl, ← H.wr, reassoc_of% heq]

noncomputable
def Hom.mapMultifork {E : PreOneHypercover.{w} S} {F : PreOneHypercover.{w'} S}
    (f : E.Hom F) (P : Cᵒᵖ ⥤ A) [HasMultiequalizer (E.multicospanIndex P)]
    [HasMultiequalizer (F.multicospanIndex P)] :
    multiequalizer (F.multicospanIndex P) ⟶ multiequalizer (E.multicospanIndex P) :=
  f.mapMultiforkOfIsLimit P (limit.isLimit _) (Multiequalizer.multifork (F.multicospanIndex P))

lemma Homotopy.mapMultifork {E F : PreOneHypercover.{w} S} {f g : E.Hom F} (H : Homotopy f g)
    (P : Cᵒᵖ ⥤ A) [HasMultiequalizer (E.multicospanIndex P)]
    [HasMultiequalizer (F.multicospanIndex P)] : f.mapMultifork P = g.mapMultifork P :=
  H.mapMultiforkOfIsLimit_eq P _ _

@[reassoc (attr := simp)]
lemma Hom.mapMultifork_ι {E F : PreOneHypercover.{w} S} (f : E.Hom F) (P : Cᵒᵖ ⥤ A)
    [HasMultiequalizer (E.multicospanIndex P)] [HasMultiequalizer (F.multicospanIndex P)]
    (a : E.I₀) :
    f.mapMultifork P ≫ Multiequalizer.ι (E.multicospanIndex P) a =
      Multiequalizer.ι (F.multicospanIndex P) (f.s₀ a) ≫ P.map (f.h₀ a).op :=
  f.mapMultiforkOfIsLimit_ι _ _ _ a

@[simp]
lemma Hom.mapMultifork_id (P : Cᵒᵖ ⥤ A) [HasMultiequalizer (E.multicospanIndex P)] :
    (𝟙 E : E ⟶ E).mapMultifork P = 𝟙 _ := by
  apply Multiequalizer.hom_ext
  simp

@[simp]
lemma Hom.mapMultifork_comp {E F : PreOneHypercover.{w} S} (f : E ⟶ F) (g : F ⟶ G) (P : Cᵒᵖ ⥤ A)
    [HasMultiequalizer (E.multicospanIndex P)] [HasMultiequalizer (F.multicospanIndex P)]
    [HasMultiequalizer (G.multicospanIndex P)] :
    (f ≫ g).mapMultifork P = g.mapMultifork P ≫ f.mapMultifork P := by
  apply Multiequalizer.hom_ext
  simp

variable (f g : E.Hom F) [HasPullbacks C]

/-- (Implementation): The covering object of `cylinder f g`. -/
noncomputable
abbrev cylinderX {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i)) : C :=
  pullback (pullback.lift (f.h₀ i) (g.h₀ i) (by simp)) (F.toPullback k)

/-- (Implementation): The structure morphisms of the covering objects of `cylinder f g`. -/
noncomputable
abbrev cylinderf {i : E.I₀} (k : F.I₁ (f.s₀ i) (g.s₀ i)) : cylinderX f g k ⟶ S :=
  pullback.fst _ _ ≫ E.f _

/-- Given two refinement morphisms `f, g : E ⟶ F`, this is a (pre-)`1`-hypercover `W` that
admits a morphism `h : W ⟶ E` such that `h ≫ f` and `h ≫ g` are homotopic. Hence
they become equal after quotienting out by homotopy.
This is a `1`-hypercover, if `E` and `F` are (see `OneHypercover.cylinder`). -/
@[simps]
noncomputable def cylinder (f g : E.Hom F) : PreOneHypercover.{max w w'} S where
  I₀ := Σ (i : E.I₀), F.I₁ (f.s₀ i) (g.s₀ i)
  X p := cylinderX f g p.2
  f p := cylinderf f g p.2
  I₁ p q := ULift.{max w w'} (E.I₁ p.1 q.1)
  Y {p q} k :=
    pullback
      (pullback.map (cylinderf f g p.2)
        (cylinderf f g q.2) _ _ (pullback.fst _ _) (pullback.fst _ _) (𝟙 S) (by simp)
        (by simp))
      (pullback.lift _ _ (E.w k.down))
  p₁ {p q} k := pullback.fst _ _ ≫ pullback.fst _ _
  p₂ {p q} k := pullback.fst _ _ ≫ pullback.snd _ _
  w {_ _} k := by simp [pullback.condition]

lemma toPullback_cylinder {i j : (cylinder f g).I₀} (k : (cylinder f g).I₁ i j) :
    (cylinder f g).toPullback k = pullback.fst _ _ := by
  apply pullback.hom_ext <;> simp [toPullback]

lemma sieve₀_cylinder :
    (cylinder f g).sieve₀ =
      Sieve.generate
        (Presieve.bindOfArrows _ E.f <| fun i ↦
          (Sieve.pullback (pullback.lift (f.h₀ _) (g.h₀ _) (by simp))
            (F.sieve₁' _ _)).arrows) := by
  refine le_antisymm ?_ ?_
  · rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    refine ⟨_, 𝟙 _, (cylinder f g).f _, ⟨_, _, ?_⟩, by simp⟩
    simp only [Sieve.pullback_apply, pullback.condition]
    exact Sieve.downward_closed _ (Sieve.ofArrows_mk _ _ _) _
  · rw [Sieve.generate_le_iff, PreZeroHypercover.sieve₀]
    rintro Z u ⟨i, v, ⟨W, o, o', ⟨j⟩, hoo'⟩⟩
    exact ⟨_, pullback.lift v o hoo'.symm, (cylinder f g).f ⟨i, j⟩, Presieve.ofArrows.mk _,
      by simp⟩

lemma sieve₁'_cylinder (i j : Σ (i : E.I₀), F.I₁ (f.s₀ i) (g.s₀ i)) :
    (cylinder f g).sieve₁' i j =
      Sieve.pullback
        (pullback.map _ _ _ _ (pullback.fst _ _) (pullback.fst _ _) (𝟙 S) (by simp) (by simp))
        (E.sieve₁' i.1 j.1) := by
  refine le_antisymm ?_ ?_
  · rw [sieve₁', Sieve.ofArrows, Sieve.generate_le_iff]
    rintro - - ⟨k⟩
    refine ⟨E.Y k.down, pullback.snd _ _, E.toPullback k.down, Presieve.ofArrows.mk k.down, ?_⟩
    simp only [cylinder_Y, cylinder_f, toPullback_cylinder, pullback.condition]
  · rw [sieve₁', Sieve.ofArrows, ← Sieve.pullbackArrows_comm, Sieve.generate_le_iff]
    rintro Z u ⟨W, v, ⟨k⟩⟩
    simp_rw [← pullbackSymmetry_inv_comp_fst]
    apply (((cylinder f g).sieve₁' i j)).downward_closed
    rw [sieve₁']
    convert Sieve.ofArrows_mk _ _ (ULift.up k)
    simp [toPullback_cylinder f g ⟨k⟩]

/-- (Implementation): The refinement morphism `cylinder f g ⟶ E`. -/
@[simps]
noncomputable def cylinderHom : (cylinder f g).Hom E where
  s₀ p := p.1
  s₁ k := k.down
  h₀ p := pullback.fst _ _
  h₁ {p q} k := pullback.snd _ _
  w₁₁ k := by
    have : E.p₁ k.down = pullback.lift _ _ (E.w k.down) ≫ pullback.fst _ _ := by simp
    nth_rw 2 [this]
    rw [← pullback.condition_assoc]
    simp
  w₁₂ {p q} k := by
    have : E.p₂ k.down = pullback.lift _ _ (E.w k.down) ≫ pullback.snd _ _ := by simp
    nth_rw 2 [this]
    rw [← pullback.condition_assoc]
    simp
  w₀ := by simp

/-- (Implementation): The homotopy of the morphisms `cylinder f g ⟶ E ⟶ F`. -/
noncomputable def cylinderHomotopy :
    Homotopy ((cylinderHom f g).comp f) ((cylinderHom f g).comp g) where
  H p := p.2
  a p := pullback.snd _ _
  wl p := by
    have : F.p₁ p.snd = pullback.lift _ _ (F.w p.2) ≫ pullback.fst _ _ := by simp
    nth_rw 1 [this]
    rw [← pullback.condition_assoc]
    simp
  wr p := by
    have : g.h₀ p.fst = pullback.lift (f.h₀ p.fst) (g.h₀ p.fst) (by simp) ≫
        pullback.snd (F.f _) (F.f _) := by simp
    dsimp only [cylinder_X, Hom.comp_s₀, cylinder_I₀, Function.comp_apply, cylinderHom_s₀,
      Hom.comp_h₀, cylinderHom_h₀]
    nth_rw 3 [this]
    rw [pullback.condition_assoc]
    simp

/-- Up to homotopy, the category of (pre-)`1`-hypercovers is cofiltered. -/
lemma exists_nonempty_homotopy (f g : E.Hom F) :
    ∃ (W : PreOneHypercover.{max w w'} S) (h : W.Hom E),
      Nonempty (Homotopy (h.comp f) (h.comp g)) :=
  ⟨cylinder f g, PreOneHypercover.cylinderHom f g, ⟨cylinderHomotopy f g⟩⟩

end Category

variable {S : C} {E F G : PreOneHypercover S}

@[simps! toPreZeroHypercover p₁ p₂ I₁ Y]
noncomputable
def pullback₁ {T : C} (f : T ⟶ S) (E : PreOneHypercover S) [∀ (i : E.I₀), HasPullback f (E.f i)]
    [∀ (i j : E.I₀) (k : E.I₁ i j), HasPullback f (E.p₁ k ≫ E.f i)] :
    PreOneHypercover T where
  __ := E.toPreZeroHypercover.pullback₁ f
  I₁ := E.I₁
  Y i _ k := pullback f (E.p₁ k ≫ E.f i)
  p₁ _ _ k := pullback.map _ _ _ _ (𝟙 T) (E.p₁ k) (𝟙 S) (by simp) (by simp)
  p₂ _ _ k := pullback.map _ _ _ _ (𝟙 T) (E.p₂ k) (𝟙 S) (by simp) (by simp [E.w])
  w := by simp

section

variable [HasPullbacks C]
  {W T : C} (g : W ⟶ T) (f : T ⟶ S) (E : PreOneHypercover S)

@[simps!]
noncomputable
def pullback₁IdInv : E ⟶ E.pullback₁ (𝟙 S) where
  __ := E.toPreZeroHypercover.pullback₁Id.inv
  s₁ := id
  h₁ k := pullback.lift (E.p₁ k ≫ E.f _) (𝟙 _) (by simp)
  w₁₁ {i j} k := by apply pullback.hom_ext <;> simp
  w₁₂ {i j} k := by apply pullback.hom_ext <;> simp [E.w]

@[simps!]
noncomputable
def pullback₁Id : E.pullback₁ (𝟙 S) ≅ E where
  hom.toHom := E.toPreZeroHypercover.pullback₁Id.hom
  hom.s₁ := id
  hom.h₁ k := pullback.snd _ _
  inv := pullback₁IdInv E
  hom_inv_id := by
    apply Hom.ext'' (by rfl)
    · intro
      apply pullback.hom_ext <;> simp [← pullback.condition]
    · intro i j k
      apply pullback.hom_ext <;> simp [← pullback.condition]
    · simp
  inv_hom_id := Hom.ext'' (by rfl) (by simp) (by simp) (by simp)

@[simps!]
noncomputable
def pullback₁CompHom [HasPullbacks C] : E.pullback₁ (g ≫ f) ⟶ (E.pullback₁ f).pullback₁ g where
  __ := (E.toPreZeroHypercover.pullback₁Comp _ _).hom
  s₁ := id
  h₁ {i j} k := (pullbackRightPullbackFstIso _ _ _).inv ≫ (pullback.congrHom rfl (by simp)).hom
  w₁₁ {i j} k := by
    apply pullback.hom_ext
    · simp
    · apply pullback.hom_ext <;> simp
  w₁₂ {i j} k := by
    apply pullback.hom_ext
    · simp
    · apply pullback.hom_ext <;> simp

@[simps!]
noncomputable
def pullback₁CompInv [HasPullbacks C] : (E.pullback₁ f).pullback₁ g ⟶ E.pullback₁ (g ≫ f) where
  __ := (E.toPreZeroHypercover.pullback₁Comp _ _).inv
  s₁ := id
  h₁ {i j} k := (pullback.congrHom rfl (by simp)).inv ≫ (pullbackRightPullbackFstIso _ _ _).hom

@[simps!]
noncomputable
def pullback₁Comp [HasPullbacks C] : E.pullback₁ (g ≫ f) ≅ (E.pullback₁ f).pullback₁ g where
  hom := pullback₁CompHom g f E
  inv := pullback₁CompInv g f E
  hom_inv_id := by
    apply Hom.ext'' (by rfl) (by simp) (by simp)
    intros
    apply pullback.hom_ext <;> simp
  inv_hom_id := by
    apply Hom.ext'' (by rfl) (by simp) (by simp)
    intros
    apply pullback.hom_ext <;> simp

end

lemma sieve₁_pullback₁ {T : C} (f : T ⟶ S) (E : PreOneHypercover S)
    [∀ (i : E.I₀), HasPullback f (E.f i)]
    [∀ (i j : E.I₀) (k : E.I₁ i j), HasPullback f (E.p₁ k ≫ E.f i)]
    {i j : E.I₀} {W : C} (p₁ : W ⟶ pullback f (E.f i)) (p₂ : W ⟶ pullback f (E.f j))
    (w : p₁ ≫ pullback.fst _ _ = p₂ ≫ pullback.fst _ _) :
    (E.pullback₁ f).sieve₁ p₁ p₂ = E.sieve₁ (p₁ ≫ pullback.snd _ _) (p₂ ≫ pullback.snd _ _) := by
  ext U g
  refine ⟨fun ⟨k, a, h₁, h₂⟩ ↦ ?_, fun ⟨k, a, h₁, h₂⟩ ↦ ?_⟩
  · refine ⟨k, a ≫ pullback.snd _ _, ?_, ?_⟩
    · simpa using congr($(h₁) ≫ pullback.snd f (E.f i))
    · simpa using congr($(h₂) ≫ pullback.snd f (E.f j))
  · refine ⟨k, pullback.lift (g ≫ p₁ ≫ pullback.fst _ _) a
      (by simp [pullback.condition, reassoc_of% h₁]), ?_, ?_⟩
    · apply pullback.hom_ext <;> simp [h₁]
    · apply pullback.hom_ext
      · simp [w]
      · simp [h₂]

@[simps toHom s₁ h₁]
noncomputable
def Hom.pullback₁ {T : C} (g : T ⟶ S) (f : E ⟶ F) [∀ (i : E.I₀), HasPullback g (E.f i)]
    [∀ (i : F.I₀), HasPullback g (F.f i)]
    [∀ (i j : E.I₀) (k : E.I₁ i j), HasPullback g (E.p₁ k ≫ E.f i)]
    [∀ (i j : F.I₀) (k : F.I₁ i j), HasPullback g (F.p₁ k ≫ F.f i)] :
    E.pullback₁ g ⟶ F.pullback₁ g where
  s₀ := f.s₀
  h₀ i := pullback.map _ _ _ _ (𝟙 T) (f.h₀ i) (𝟙 S) (by simp) (by simp)
  s₁ {i j} k := f.s₁ k
  h₁ {i j} k := pullback.map _ _ _ _ (𝟙 T) (f.h₁ k) (𝟙 S) (by simp)
    (by rw [f.w₁₁_assoc, Category.assoc, Category.comp_id, f.w₀])
  w₀ i := by simp
  w₁₁ {i j} k := by
    apply pullback.hom_ext
    · simp
    · simp only [PreOneHypercover.pullback₁_Y,
        PreOneHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.pullback₁_X,
        PreOneHypercover.pullback₁_p₁, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
        PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_right]
      rw [f.w₁₁ k]
  w₁₂ {i j} k := by
    apply pullback.hom_ext
    · simp
    · simp only [PreOneHypercover.pullback₁_Y,
        PreOneHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.pullback₁_X,
        PreOneHypercover.pullback₁_p₂, Category.assoc, limit.lift_π, PullbackCone.mk_pt,
        PullbackCone.mk_π_app, limit.lift_π_assoc, cospan_right]
      rw [f.w₁₂ k]

section

variable {T : C} (g : T ⟶ S) (f : E ⟶ F) (h : F ⟶ G)
    [∀ (i : E.I₀), HasPullback g (E.f i)] [∀ (i : F.I₀), HasPullback g (F.f i)]
    [∀ (i j : E.I₀) (k : E.I₁ i j), HasPullback g (E.p₁ k ≫ E.f i)]
    [∀ (i j : F.I₀) (k : F.I₁ i j), HasPullback g (F.p₁ k ≫ F.f i)]

lemma Hom.pullback₁_id : (𝟙 E : E ⟶ E).pullback₁ g = 𝟙 (E.pullback₁ g) :=
  Hom.ext'' (by rfl) (by simp) (by simp) (by simp)

variable [∀ (i : G.I₀), HasPullback g (G.f i)]
  [∀ (i j : G.I₀) (k : G.I₁ i j), HasPullback g (G.p₁ k ≫ G.f i)]

lemma Hom.pullback₁_comp : (f ≫ h).pullback₁ g = f.pullback₁ g ≫ h.pullback₁ g :=
  Hom.ext'' (by rfl) (fun _ ↦ by apply pullback.hom_ext <;> simp) (by simp)
    (fun _ ↦ by apply pullback.hom_ext <;> simp)

end

noncomputable
def Homotopy.pullback₁ {T : C} (g : T ⟶ S) {u v : E.Hom F} (H : Homotopy u v)
    [∀ (i : E.I₀), HasPullback g (E.f i)] [∀ (i : F.I₀), HasPullback g (F.f i)]
    [∀ (i j : E.I₀) (k : E.I₁ i j), HasPullback g (E.p₁ k ≫ E.f i)]
    [∀ (i j : F.I₀) (k : F.I₁ i j), HasPullback g (F.p₁ k ≫ F.f i)] :
    Homotopy (u.pullback₁ g) (v.pullback₁ g) where
  H := H.H
  a i := pullback.map _ _ _ _ (𝟙 T) (H.a i) (𝟙 S) (by simp) (by simp)
  wl i := by apply pullback.hom_ext <;> simp
  wr i := by apply pullback.hom_ext <;> simp

@[simps toPreZeroHypercover I₁ Y p₁ p₂]
def bind₁ (E : PreOneHypercover.{w} S)
    (F : ∀ {i j : E.I₀} (k : E.I₁ i j), PreZeroHypercover.{w} (E.Y k)) :
    PreOneHypercover S where
  __ := E.toPreZeroHypercover
  I₁ {i j : E.I₀} := Σ (k : E.I₁ i j), (F k).I₀
  Y {i j : E.I₀} p := (F p.1).X p.2
  p₁ {i j : E.I₀} p := (F p.1).f p.2 ≫ E.p₁ _
  p₂ {i j : E.I₀} p := (F p.1).f p.2 ≫ E.p₂ _
  w {i j : E.I₀} p := by simp [E.w]

@[simps]
noncomputable
def sum (E : PreOneHypercover.{w} S) (F : PreOneHypercover.{w} S)
    [∀ i j, HasPullback (E.f i) (F.f j)]
    (G : ∀ (i : E.I₀) (j : F.I₀), PreZeroHypercover.{w} (pullback (E.f i) (F.f j))) :
    PreOneHypercover.{w} S where
  I₀ := E.I₀ ⊕ F.I₀
  X := Sum.elim E.X F.X
  f
    | .inl i => E.f i
    | .inr i => F.f i
  I₁
    | .inl i, .inl j => E.I₁ i j
    | .inr i, .inr j => F.I₁ i j
    | .inl i, .inr j => (G i j).I₀
    | .inr i, .inl j => (G j i).I₀
  Y
    | .inl i, .inl j, k => E.Y k
    | .inr i, .inr j, k => F.Y k
    | .inl i, .inr j, k => (G i j).X k
    | .inr i, .inl j, k => (G j i).X k
  p₁
    | .inl i, .inl j, k => E.p₁ k
    | .inr i, .inr j, k => F.p₁ k
    | .inl i, .inr j, k => (G i j).f _ ≫ pullback.fst _ _
    | .inr i, .inl j, k => (G j i).f _ ≫ pullback.snd _ _
  p₂
    | .inl i, .inl j, k => E.p₂ k
    | .inr i, .inr j, k => F.p₂ k
    | .inl i, .inr j, k => (G i j).f _ ≫ pullback.snd _ _
    | .inr i, .inl j, k => (G j i).f _ ≫ pullback.fst _ _
  w
    | .inl i, .inl j, k => E.w k
    | .inr i, .inr j, k => F.w k
    | .inl i, .inr j, k => by simp [pullback.condition]
    | .inr i, .inl j, k => by simp [pullback.condition]

@[simps toPreZeroHypercover I₁ Y p₁ p₂]
def mk' (E : PreZeroHypercover.{w} S) (I₁' : Type w) (Y : I₁' → C)
    (i₁ i₂ : I₁' → E.I₀)
    (p₁ : ∀ i : I₁', Y i ⟶ E.X (i₁ i))
    (p₂ : ∀ i : I₁', Y i ⟶ E.X (i₂ i))
    (w : ∀ i, p₁ i ≫ E.f _ = p₂ i ≫ E.f _) :
    PreOneHypercover.{w} S where
  __ := E
  I₁ i j := { x : I₁' // i₁ x = i ∧ i₂ x = j }
  Y i j k := Y k.1
  p₁ i j k := p₁ k.1 ≫ eqToHom (by rw [k.2.1])
  p₂ i j k := p₂ k.1 ≫ eqToHom (by rw [k.2.2])
  w i j := fun ⟨k, h₁, h₂⟩ ↦ by
    subst h₁ h₂
    simp [w]

/-- A refinement data of a pre-`1`-hypercover `{Uᵢ} is a pre-`0`-hypercover for every `Uᵢ`
and coverings of the intersections. -/
structure Refinement' (E : PreOneHypercover.{w} S) where
  cover (i : E.I₀) : PreOneHypercover.{w} (E.X i)
  I {i j : E.I₀} (k : E.I₁ i j) (a : (cover i).I₀) (b : (cover j).I₀) : Type w
  Z {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) : C
  s {i : E.I₀} {a b : (cover i).I₀} (c : (cover i).I₁ a b) : E.I₁ i i
  p {i : E.I₀} {a b : (cover i).I₀} (c : (cover i).I₁ a b) : (cover i).Y c ⟶ E.Y (s c)
  --p {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) :
  --  Z k l ⟶ E.Y k
  q₁ {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) :
    Z k l ⟶ (cover i).X a
  q₂ {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) :
    Z k l ⟶ (cover j).X b
  w {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) :
    q₁ k l ≫ (cover _).f _ ≫ E.f _ = q₂ k l ≫ (cover _).f _ ≫ E.f _
  --w_self {i : E.I₀} (k : E.I₁ i i) {a : (cover i).I₀} {b : (cover i).I₀} (l : I k a b) :
  --  q₁ k l ≫ (cover _).f _ = q₂ k l ≫ (cover _).f _
  --w₁ {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) :
  --  p k l ≫ E.p₁ k = q₁ k l ≫ (cover i).f a
  --w₂ {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) :
  --  p k l ≫ E.p₂ k = q₂ k l ≫ (cover j).f b

namespace Refinement'

attribute [reassoc (attr := grind _=_)] w

variable {E : PreOneHypercover.{w} S}

@[simps!]
def bind (R : E.Refinement') :
    PreOneHypercover.{w} S :=
  .mk' (E.toPreZeroHypercover.bind (fun i ↦ (R.cover i).toPreZeroHypercover))
    ((Σ (i : E.I₀) (a b : (R.cover i).I₀), (R.cover i).I₁ a b) ⊕
      Σ (k : E.I₁') (a : (R.cover k.1.1).I₀) (b : (R.cover k.1.2).I₀), R.I k.2 a b)
    (Sum.elim (fun p ↦ (R.cover p.1).Y p.2.2.2) (fun k ↦ R.Z _ k.2.2.2))
    (Sum.elim (fun p ↦ ⟨p.1, p.2.1⟩) (fun k ↦ ⟨k.1.1.1, k.2.1⟩)) 
    (Sum.elim (fun p ↦ ⟨p.1, p.2.2.1⟩) (fun k ↦ ⟨k.1.1.2, k.2.2.1⟩)) 
    (fun i ↦ match i with
      | .inl ⟨i, a, b, l⟩ => (R.cover _).p₁ _
      | .inr k => R.q₁ _ _)
    (fun i ↦ match i with
      | .inl ⟨i, a, b, l⟩ => (R.cover _).p₂ _
      | .inr k => R.q₂ _ _)
    (fun i ↦ match i with
      | .inl p => by simp [reassoc_of% (R.cover p.1).w]
      | .inr k => R.w _ _)

@[simps]
def toBase (R : E.Refinement') : R.bind ⟶ E where
  s₀ i := i.1
  h₀ i := (R.cover i.1).f i.2
  s₁ {i j} := fun ⟨p, hp⟩ ↦ match p with
    | .inl p => by
      dsimp at hp
      rw [← hp.1, ← hp.2]
      exact R.s p.2.2.2
    | .inr k => hp.1 ▸ hp.2 ▸ k.1.2
  h₁ {i j} := fun ⟨p, hp1, hp2⟩ ↦ match p with
    | .inl p => by
        dsimp at hp1 hp2 ⊢
        subst hp1 hp2
        dsimp
        exact R.p _
    | .inr p => by dsimp; sorry
  w₀ _ := sorry
  w₁₁ _ := sorry
  w₁₂ _ := sorry

attribute [local grind =] Category.assoc Category.id_comp

end Refinement'

/-- A refinement data of a pre-`1`-hypercover `{Uᵢ} is a pre-`0`-hypercover for every `Uᵢ`
and coverings of the intersections. -/
structure Refinement (E : PreOneHypercover.{w} S) where
  cover (i : E.I₀) : PreZeroHypercover.{w} (E.X i)
  I {i j : E.I₀} (k : E.I₁ i j) (a : (cover i).I₀) (b : (cover j).I₀) : Type w
  Z {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) : C
  p {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) :
    Z k l ⟶ E.Y k
  q₁ {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) :
    Z k l ⟶ (cover i).X a
  q₂ {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) :
    Z k l ⟶ (cover j).X b
  w {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) :
    q₁ k l ≫ (cover _).f _ ≫ E.f _ = q₂ k l ≫ (cover _).f _ ≫ E.f _
  w_self {i : E.I₀} (k : E.I₁ i i) {a : (cover i).I₀} {b : (cover i).I₀} (l : I k a b) :
    q₁ k l ≫ (cover _).f _ = q₂ k l ≫ (cover _).f _
  w₁ {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) :
    p k l ≫ E.p₁ k = q₁ k l ≫ (cover i).f a
  w₂ {i j : E.I₀} (k : E.I₁ i j) {a : (cover i).I₀} {b : (cover j).I₀} (l : I k a b) :
    p k l ≫ E.p₂ k = q₂ k l ≫ (cover j).f b

attribute [reassoc (attr := grind _=_)] Refinement.w Refinement.w_self Refinement.w₁ Refinement.w₂

namespace Refinement

variable {E : PreOneHypercover.{w} S}

@[simps! toPreZeroHypercover I₁ Y p₁ p₂]
def cover₁ (R : E.Refinement) (i : E.I₀) : PreOneHypercover.{w} (E.X i) where
  __ := R.cover i
  I₁ a b := Σ (k : E.I₁ i i), R.I k a b
  Y _ _ p := R.Z p.1 p.2
  p₁ _ _ _ := R.q₁ _ _
  p₂ _ _ _ := R.q₂ _ _
  w _ _ _ := R.w_self _ _

@[simps!]
def bind (R : E.Refinement) : PreOneHypercover.{w} S where
  __ := E.toPreZeroHypercover.bind
    fun i ↦ (R.cover i)
  I₁ i j := Σ (k : E.I₁ i.1 j.1), R.I k i.2 j.2
  Y _ _ p := R.Z p.1 p.2
  p₁ _ _ p := R.q₁ p.1 p.2
  p₂ _ _ p := R.q₂ p.1 p.2
  w _ _ p := R.w p.1 p.2

-- TODO: move this close to PreZeroHypercover.bind
lemma presieve₀_bind (R : E.Refinement) :
    R.bind.presieve₀ = Presieve.bindOfArrows E.X E.f fun i ↦ (R.cover i).presieve₀ := by
  refine le_antisymm ?_ ?_
  · intro X f ⟨i⟩
    exact Presieve.bindOfArrows.mk i.1 _ ⟨i.2⟩
  · rintro X f ⟨i, g, ⟨j⟩⟩
    exact .mk (Sigma.mk _ _)

def sieve₁ (R : E.Refinement) {i j : E.I₀} {a : (R.cover i).I₀} {b : (R.cover j).I₀} {W : C}
    (v₁ : W ⟶ (R.cover i).X a) (v₂ : W ⟶ (R.cover j).X b) : Sieve W :=
  R.bind.sieve₁ (W := W) (i₁ := ⟨i, a⟩) (i₂ := ⟨j, b⟩) v₁ v₂

@[simps]
def toBase (R : E.Refinement) : R.bind ⟶ E where
  s₀ i := i.1
  h₀ i := (R.cover i.1).f i.2
  s₁ p := p.1
  h₁ p := R.p p.1 p.2
  w₀ _ := rfl
  w₁₁ _ := R.w₁ _ _
  w₁₂ _ := R.w₂ _ _

attribute [local grind =] Category.assoc Category.id_comp

@[simps]
noncomputable
def homPullback₁ [HasPullbacks C] (R : E.Refinement) (i : E.I₀) :
    R.cover₁ i ⟶ R.bind.pullback₁ (E.f i) where
  s₀ a := ⟨i, a⟩
  h₀ a := pullback.lift ((R.cover i).f a) (𝟙 _)
  s₁ := id
  h₁ {a b} p := pullback.lift (R.p _ _ ≫ E.p₁ _) (𝟙 _) <| by simp [w_self_assoc, w₁_assoc]
  w₁₁ {a b} p := by apply pullback.hom_ext <;> simp [w₁, w_self]
  w₁₂ {a b} p := by apply pullback.hom_ext <;> simp [w₁, w_self]

end Refinement

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

section Category

variable {S : C} {E : OneHypercover.{w} J S} {F : OneHypercover.{w'} J S}

/-- A morphism of `1`-hypercovers is a morphism of the underlying pre-`1`-hypercovers. -/
abbrev Hom (E : OneHypercover.{w} J S) (F : OneHypercover.{w'} J S) :=
  E.toPreOneHypercover.Hom F.toPreOneHypercover

variable [HasPullbacks C]

/-- Given two refinement morphism `f, g : E ⟶ F`, this is a `1`-hypercover `W` that
admits a morphism `h : W ⟶ E` such that `h ≫ f` and `h ≫ g` are homotopic. Hence
they become equal after quotienting out by homotopy. -/
@[simps! toPreOneHypercover]
noncomputable def cylinder (f g : E.Hom F) : J.OneHypercover S :=
  mk' (PreOneHypercover.cylinder f g)
    (by
      rw [PreOneHypercover.sieve₀_cylinder]
      refine J.bindOfArrows E.mem₀ fun i ↦ ?_
      rw [Sieve.generate_sieve]
      exact J.pullback_stable _ (mem_sieve₁' F _ _))
    (fun i j ↦ by
      rw [PreOneHypercover.sieve₁'_cylinder]
      exact J.pullback_stable _ (mem_sieve₁' E _ _))

/-- Up to homotopy, the category of `1`-hypercovers is cofiltered. -/
lemma exists_nonempty_homotopy (f g : E.Hom F) :
    ∃ (W : OneHypercover.{max w w'} J S) (h : W.Hom E),
      Nonempty (PreOneHypercover.Homotopy (h.comp f) (h.comp g)) :=
  ⟨cylinder f g, PreOneHypercover.cylinderHom f g, ⟨PreOneHypercover.cylinderHomotopy f g⟩⟩

end Category

@[simps! toPreOneHypercover]
noncomputable
def pullback₁ {S T : C} (f : T ⟶ S) (E : J.OneHypercover S) [∀ (i : E.I₀), HasPullback f (E.f i)]
    [∀ (i j : E.I₀) (k : E.I₁ i j), HasPullback f (E.p₁ k ≫ E.f i)] :
    J.OneHypercover T where
  __ := E.toPreOneHypercover.pullback₁ f
  mem₀ := by
    simp only [PreOneHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.sieve₀_pullback₁]
    exact J.pullback_stable _ E.mem₀
  mem₁ i₁ i₂ W p₁ p₂ h := by
    simp only [PreOneHypercover.pullback₁_toPreZeroHypercover, PreZeroHypercover.pullback₁_X,
      PreZeroHypercover.pullback₁_f] at h
    rw [PreOneHypercover.sieve₁_pullback₁ _ _ _ _ h]
    apply E.mem₁
    rw [Category.assoc, Category.assoc, ← pullback.condition, ← pullback.condition, reassoc_of% h]

variable {S : C}

structure Refinement (E : OneHypercover.{w} J S) extends E.toPreOneHypercover.Refinement where
  mem₀ (i : E.I₀) : (cover i).sieve₀ ∈ J (E.X i)
  mem₁ {i j : E.I₀} {a : (cover i).I₀} {b : (cover j).I₀} {W : C} (v₁ : W ⟶ (cover i).X a)
    (v₂ : W ⟶ (cover j).X b) (h : v₁ ≫ (cover i).f _ ≫ E.f _ = v₂ ≫ (cover j).f _ ≫ E.f _) :
    toRefinement.sieve₁ v₁ v₂ ∈ J W

namespace Refinement

variable {E : OneHypercover.{w} J S}

@[simps toPreOneHypercover]
def cover₁ (R : E.Refinement) (i : E.I₀) : J.OneHypercover (E.X i) where
  __ := R.toRefinement.cover₁ i
  mem₀ := R.mem₀ i
  mem₁ i₁ i₂ W v₁ v₂ hv₁₂ := by
    apply R.mem₁
    simp only [PreOneHypercover.Refinement.cover₁_toPreZeroHypercover] at hv₁₂
    rw [reassoc_of% hv₁₂]

@[simps toPreOneHypercover]
def bind (R : E.Refinement) : J.OneHypercover S where
  __ := R.toRefinement.bind
  mem₀ := by
    rw [PreZeroHypercover.sieve₀, Sieve.ofArrows, ← PreZeroHypercover.presieve₀,
      PreOneHypercover.Refinement.presieve₀_bind]
    exact J.bindOfArrows E.mem₀ R.mem₀
  mem₁ i₁ i₂ W v₁ v₂ hv₁₂ := R.mem₁ v₁ v₂ hv₁₂

end Refinement

lemma _root_.CategoryTheory.GrothendieckTopology.ofArrows_sumElim_mem
    {α β : Type*} {X : α → C} {Y : β → C} (f : ∀ a, X a ⟶ S) (g : ∀ b, Y b ⟶ S)
    (hf : Sieve.ofArrows X f ∈ J S) :
    Sieve.ofArrows (Sum.elim X Y) (fun i ↦ match i with | .inl a => f a | .inr b => g b) ∈ J S := by
  let p (i : α ⊕ β) : Sum.elim X Y i ⟶ S := match i with
    | .inl a => f a
    | .inr b => g b
  have : Sieve.ofArrows _ f ≤ Sieve.ofArrows _ p := by
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro W w ⟨i⟩
    rw [Sieve.ofArrows]
    apply Sieve.le_generate
    exact ⟨Sum.inl i⟩
  exact superset_covering J this hf

noncomputable
nonrec def sum
    [HasPullbacks C] -- TODO: remove this after updating mathlib
    (E : OneHypercover.{w} J S) (F : OneHypercover.{w} J S)
    [∀ i j, HasPullback (E.f i) (F.f j)]
    (G : ∀ (i : E.I₀) (j : F.I₀), Coverage.ZeroHypercover.{w} (.ofGrothendieck _ J)
      (Limits.pullback (E.f i) (F.f j))) :
    OneHypercover J S where
  __ := E.toPreOneHypercover.sum F.toPreOneHypercover (fun i j ↦ (G i j).toPreZeroHypercover)
  mem₀ := by
    simp only [PreZeroHypercover.sieve₀, PreOneHypercover.sum]
    convert J.ofArrows_sumElim_mem E.f F.f E.mem₀
    grind
  mem₁
    | .inl i, .inl j, W, p₁, p₂, h => E.mem₁ i j p₁ p₂ h
    | .inr i, .inr j, W, p₁, p₂, h => F.mem₁ i j p₁ p₂ h
    | .inl i, .inr j, W, p₁, p₂, h => by
      have : HasPullback
          ((E.sum F.toPreOneHypercover (fun i j ↦ (G i j).toPreZeroHypercover)).f (Sum.inl i))
          ((E.sum F.toPreOneHypercover (fun i j ↦ (G i j).toPreZeroHypercover)).f (Sum.inr j)) :=
        inferInstanceAs <| HasPullback (E.f i) (F.f j)
      rw [PreOneHypercover.sieve₁_eq_pullback_sieve₁' _ _ _ h]
      apply J.pullback_stable
      rw [PreOneHypercover.sieve₁']
      rw [Sieve.ofArrows]
      rw [← Coverage.ofGrothendieck_iff]
      -- have : J = Coverage.toGrothendieck _ (Coverage.ofGrothendieck _ J) := sorry
      have := (G i j).mem₀
      rw [PreZeroHypercover.presieve₀] at this
      simp only [PreOneHypercover.sum_X, Sum.elim_inl, Sum.elim_inr, PreOneHypercover.sum_f,
        PreOneHypercover.sum_I₁]
      convert this using 2
      ext k <;> simp [PreOneHypercover.toPullback]
    | .inr j, .inl i, W, p₁, p₂, h => by
      have : HasPullback
          ((E.sum F.toPreOneHypercover (fun i j ↦ (G i j).toPreZeroHypercover)).f (Sum.inr j))
          ((E.sum F.toPreOneHypercover (fun i j ↦ (G i j).toPreZeroHypercover)).f (Sum.inl i)) :=
        --inferInstanceAs <| HasPullback (E.f j) (F.f i)
        sorry
      rw [PreOneHypercover.sieve₁_eq_pullback_sieve₁' _ _ _ h]
      apply J.pullback_stable
      dsimp
      rw [← pullback_mem_iff_of_isIso (i := (pullbackSymmetry _ _).hom)]
      rw [PreOneHypercover.sieve₁']
      rw [Sieve.ofArrows]
      rw [← Sieve.pullbackArrows_comm]
      rw [← Coverage.ofGrothendieck_iff]
      -- have : J = Coverage.toGrothendieck _ (Coverage.ofGrothendieck _ J) := sorry
      have := (G i j).mem₀
      rw [PreZeroHypercover.presieve₀] at this
      simp only [PreOneHypercover.sum_X, Sum.elim_inl, Sum.elim_inr, PreOneHypercover.sum_f,
        PreOneHypercover.sum_I₁]
      rw [← Presieve.ofArrows_pullback]
      convert this using 1
      --ext k <;> simp [PreOneHypercover.toPullback]
      sorry

@[simps! id_s₀ id_s₁ id_h₀ id_h₁ comp_s₀ comp_s₁ comp_h₀ comp_h₁]
instance : Category (J.OneHypercover S) where
  Hom := Hom
  id E := PreOneHypercover.Hom.id E.toPreOneHypercover
  comp f g := f.comp g

@[simps]
def isoMk {E F : J.OneHypercover S} (f : E.toPreOneHypercover ≅ F.toPreOneHypercover) :
    E ≅ F where
  __ := f

variable (J) in
@[simps]
noncomputable
def pullback [HasPullbacks C] {T : C} (f : S ⟶ T) : J.OneHypercover T ⥤ J.OneHypercover S where
  obj E := E.pullback₁ f
  map g := g.pullback₁ f
  map_id _ := PreOneHypercover.Hom.pullback₁_id f
  map_comp _ _ := PreOneHypercover.Hom.pullback₁_comp f _ _

variable (J) in
@[simps!]
noncomputable
def pullbackId [HasPullbacks C] (S : C) : pullback J (𝟙 S) ≅ 𝟭 _ :=
  NatIso.ofComponents (fun E ↦ isoMk E.pullback₁Id) fun {X Y} f ↦
    PreOneHypercover.Hom.ext'' (by rfl) (by simp) (by simp) (by simp)

variable (J) in
@[simps!]
noncomputable
def pullbackComp [HasPullbacks C] {S T W : C} (f : S ⟶ T) (g : T ⟶ W) :
    pullback J (f ≫ g) ≅ pullback J g ⋙ pullback J f :=
  NatIso.ofComponents (fun E ↦ isoMk (E.pullback₁Comp f g)) fun {X Y} f ↦ by
    apply PreOneHypercover.Hom.ext'' (by rfl)
    · intros
      apply pullback.hom_ext
      · simp
      · apply pullback.hom_ext <;> simp
    · intros
      apply pullback.hom_ext
      · simp
      · apply pullback.hom_ext <;> simp
    · simp

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

end CategoryTheory
