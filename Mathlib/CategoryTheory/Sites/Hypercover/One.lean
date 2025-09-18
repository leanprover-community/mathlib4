/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.Hypercover.Zero

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

end Category

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
