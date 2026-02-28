/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Sites.BigZariski
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import Mathlib.AlgebraicGeometry.Cover.Sigma
public import Mathlib.CategoryTheory.Sites.Preserves
public import Mathlib.CategoryTheory.Sites.Hypercover.SheafOfTypes
public import Mathlib.CategoryTheory.Sites.Hypercover.Homotopy

/-!
# The quasi-compact topology of a scheme

The `qc`-pretopology of a scheme wrt. to a morphism property `P` is the pretopology
given by quasi compact covers satisfying `P`.

We show that a presheaf is a sheaf in this topology if and only if it is a sheaf
in the Zariski topology and a sheaf on single object `P`-coverings of affine schemes.
-/

@[expose] public section

universe w' w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

open Limits

variable {C : Type*} [Category C] {X : C}
variable {A : Type*} [Category* A]

structure PreZeroHypercover.Relation {S : C} (E : PreZeroHypercover S) (i j : E.I₀) where
  obj : C
  fst : obj ⟶ E.X i
  snd : obj ⟶ E.X j
  w : fst ≫ E.f i = snd ≫ E.f j

@[simps toPreZeroHypercover I₁ Y p₁ p₂ w]
def PreZeroHypercover.saturate {S : C} (E : PreZeroHypercover S) : PreOneHypercover S where
  __ := E
  I₁ := E.Relation
  Y _ _ r := r.obj
  p₁ _ _ r := r.fst
  p₂ _ _ r := r.snd
  w _ _ r := r.w

@[simps]
def PreZeroHypercover.sectionsSaturateEquiv {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ Type*) :
    (E.saturate.multicospanIndex F).sections ≃ Subtype (Presieve.Arrows.Compatible F E.f) where
  toFun s := ⟨s.val, fun i j _ _ _ hgij ↦ s.property ⟨(i, j), ⟨_, _, _, hgij⟩⟩⟩
  invFun s := ⟨s.val, fun r ↦ s.property _ _ _ _ _ r.snd.w⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simps]
def PreZeroHypercover.sectionsEquivOfHasPullbacks {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] (F : Cᵒᵖ ⥤ Type*) :
    (E.toPreOneHypercover.multicospanIndex F).sections ≃
      Subtype (Presieve.Arrows.Compatible F E.f) where
  toFun s :=
    ⟨s.val, fun i j W gi gj hgij ↦ by
      have heq := s.property ⟨(i, j), ⟨⟩⟩
      dsimp at heq
      rw [← pullback.lift_fst _ _ hgij]
      conv_rhs => rw [← pullback.lift_snd _ _ hgij]
      rw [op_comp, Functor.map_comp, op_comp, Functor.map_comp]
      simp [heq]⟩
  invFun s := ⟨s.val, fun r ↦ s.property _ _ _ _ _ pullback.condition⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma isLimit_saturate_type_iff {S : C} (E : PreZeroHypercover S) (F : Cᵒᵖ ⥤ Type*) :
    Nonempty (IsLimit <| E.saturate.multifork F) ↔ E.presieve₀.IsSheafFor F := by
  rw [Multifork.isLimit_types_iff, Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible,
    ← Function.Bijective.of_comp_iff' (E.sectionsSaturateEquiv F).symm.bijective]
  rfl

@[simps]
noncomputable
def PreZeroHypercover.toSaturateOfHasPullbacks {S : C} (E : PreZeroHypercover S) [E.HasPullbacks] :
    E.toPreOneHypercover ⟶ E.saturate where
  s₀ i := i
  h₀ i := 𝟙 _
  s₁ {i j} k := ⟨pullback (E.f i) (E.f j), _, _, pullback.condition⟩
  h₁ {i j} k := 𝟙 _

@[simps]
noncomputable
def PreZeroHypercover.fromSaturateOfHasPullbacks {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] : E.saturate ⟶ E.toPreOneHypercover where
  s₀ i := i
  h₀ i := 𝟙 _
  s₁ {i j} k := ⟨⟩
  h₁ {i j} k := pullback.lift k.fst k.snd k.w

namespace PreZeroHypercover

variable {S : C} (E : PreZeroHypercover S) [E.HasPullbacks]

@[simp]
lemma toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks :
    E.toSaturateOfHasPullbacks.comp E.fromSaturateOfHasPullbacks = .id _ := by
  refine PreOneHypercover.Hom.ext' rfl (by simp) (by simp) (by simp)

noncomputable
def fromSaturateToSaturateHomotopy : PreOneHypercover.Homotopy
    (E.fromSaturateOfHasPullbacks.comp E.toSaturateOfHasPullbacks) (.id _) where
  H i := ⟨pullback (E.f i) (E.f i), pullback.fst _ _, pullback.snd _ _, pullback.condition⟩
  a i := pullback.diagonal (E.f i)
  wl i := by simp
  wr i := by simp

end PreZeroHypercover

namespace PreOneHypercover

/-- If `f : E ⟶ F` and `g : F ⟶ E` are refinement morphisms of pre-`1`-hypercovers such that
the composition `g ≫ f` is homotopic to the identity, then if the multifork associated
to `E` is exact also the multifork associated to `F` is exact. -/
def Homotopy.isLimitMultifork {S : C} {E F : PreOneHypercover S} (f : E.Hom F) (g : F.Hom E)
    (hgf : Homotopy (g.comp f) (.id F))
    {G : Cᵒᵖ ⥤ A} (hE : IsLimit (E.multifork G)) :
    IsLimit (F.multifork G) := by
  refine Multifork.IsLimit.mk _ ?_ ?_ ?_
  · intro t
    refine Multifork.IsLimit.lift hE (fun a ↦ t.ι (f.s₀ a) ≫ G.map (f.h₀ a).op) ?_
    intro b
    dsimp
    simp only [Category.assoc, ← Functor.map_comp, ← op_comp]
    rw [← f.w₁₁, ← f.w₁₂]
    simp only [op_comp, Functor.map_comp]
    exact t.condition_assoc ⟨(f.s₀ b.1.1, f.s₀ b.1.2), f.s₁ b.2⟩ _
  · intro t i
    simp only [multicospanIndex_left, multicospanShape_L, multifork_ι]
    have h1 := hgf.wl i
    dsimp at h1
    have h2 := t.condition ⟨⟨_, _⟩, hgf.H i⟩
    dsimp at h2
    rw [← g.w₀, op_comp, Functor.map_comp, ← E.multifork_ι, Multifork.IsLimit.fac_assoc,
      Category.assoc, ← Functor.map_comp, ← op_comp, ← h1, op_comp, Functor.map_comp,
      reassoc_of% h2, ← Functor.map_comp, ← op_comp, hgf.wr i]
    simp
  · intro t m hm
    refine Multifork.IsLimit.hom_ext hE fun i ↦ ?_
    rw [Multifork.IsLimit.fac, multifork_ι, ← f.w₀, op_comp, Functor.map_comp, ← F.multifork_ι,
      reassoc_of% hm]

/-- `E` and `F` are homotopy equivalent, then the multifork associated
to `E` is exact if and only if the multifork associated to `F` is exact. -/
def Homotopy.isLimitMultiforkEquiv {S : C} {E F : PreOneHypercover S} (f : E.Hom F) (g : F.Hom E)
    (hfg : Homotopy (f.comp g) (.id E)) (hgf : Homotopy (g.comp f) (.id F)) {G : Cᵒᵖ ⥤ A} :
    IsLimit (E.multifork G) ≃ IsLimit (F.multifork G) where
  toFun h := hgf.isLimitMultifork _ _ h
  invFun h := hfg.isLimitMultifork _ _ h
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end PreOneHypercover

noncomputable
def PreZeroHypercover.toPreOneHypercoverHomotopy {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] :
    PreOneHypercover.Homotopy (.id E.toPreOneHypercover) (.id E.toPreOneHypercover) where
  H _ := ⟨⟩
  a i := pullback.diagonal (E.f i)
  wl := by simp
  wr := by simp

/-- If the pre-`0`-hypercover `E` has pairwise pullbacks, then the multifork associated to the
full saturated pre-`1`-hypercover is exact if and only if the minimal one given by taking
the pairwise pullbacks is exact. -/
noncomputable
def PreZeroHypercover.isLimitSaturateEquivOfHasPullbacks {S : C} (E : PreZeroHypercover S)
    [E.HasPullbacks] (F : Cᵒᵖ ⥤ A) :
    IsLimit (E.saturate.multifork F) ≃ IsLimit (E.toPreOneHypercover.multifork F) :=
  PreOneHypercover.Homotopy.isLimitMultiforkEquiv E.fromSaturateOfHasPullbacks
    E.toSaturateOfHasPullbacks E.fromSaturateToSaturateHomotopy
    (by
      rw [toSaturateOfHasPullbacks_fromSaturateOfHasPullbacks]
      exact E.toPreOneHypercoverHomotopy)

lemma PreZeroHypercover.isLimit_toPreOneHypercover_type_iff {S : C} (E : PreZeroHypercover.{w} S)
    [E.HasPullbacks] (F : Cᵒᵖ ⥤ Type*) :
    Nonempty (IsLimit <| E.toPreOneHypercover.multifork F) ↔ E.presieve₀.IsSheafFor F := by
  rw [Multifork.isLimit_types_iff, Presieve.isSheafFor_ofArrows_iff_bijective_toCompabible,
    ← Function.Bijective.of_comp_iff' (E.sectionsEquivOfHasPullbacks F).symm.bijective]
  rfl

@[ext (iff := false)]
def PreOneHypercover.I₁'.ext {S : C} {E : PreOneHypercover.{w} S} {a b : E.I₁'}
    (left : a.1.1 = b.1.1) (right : a.1.2 = b.1.2)
    (h : E.congrIndexOneOfEq left right a.2 = b.2) :
    a = b := by
  obtain ⟨⟨i, j⟩, k⟩ := a
  obtain ⟨⟨i', j'⟩, k'⟩ := b
  dsimp at left right
  subst left right
  simpa using h

@[simp]
lemma PreOneHypercover.hom_inv_s₀_apply {S : C} {E F : PreOneHypercover.{w} S} (e : E ≅ F)
    (i : E.I₀) :
    e.inv.s₀ (e.hom.s₀ i) = i :=
  congr($(e.hom_inv_id).s₀ i)

@[simp]
lemma PreOneHypercover.inv_hom_s₀_apply {S : C} {E F : PreOneHypercover.{w} S} (e : E ≅ F)
    (i : F.I₀) :
    e.hom.s₀ (e.inv.s₀ i) = i :=
  congr($(e.inv_hom_id).s₀ i)

@[simp]
lemma PreOneHypercover.congrIndexOneOfEq_trans {S : C} {E : PreOneHypercover.{w} S}
    {i i' i'' j j' j'' : E.I₀} (hii' : i = i') (hjj' : j = j') (hii'' : i' = i'')
    (hjj'' : j' = j'') (k : E.I₁ i j) :
    E.congrIndexOneOfEq hii'' hjj'' (E.congrIndexOneOfEq hii' hjj' k) =
      E.congrIndexOneOfEq (hii'.trans hii'') (hjj'.trans hjj'') k := by
  subst hii' hjj'
  simp

lemma PreOneHypercover.Hom.ext'_iff {S : C} {E F : PreOneHypercover S} {f g : E.Hom F} :
    f = g ↔ ∃ (hs₀ : f.s₀ = g.s₀) (_ : ∀ i, f.h₀ i = g.h₀ i ≫ eqToHom (by simp [hs₀]))
      (hs₁ : ∀ (i j : E.I₀) (k : E.I₁ i j),
        f.s₁ k = F.congrIndexOneOfEq (by simp [hs₀]) (by simp [hs₀]) (g.s₁ k)),
      ∀ (i j : E.I₀) (k : E.I₁ i j),
        f.h₁ k = g.h₁ k ≫
          (F.congrIndexOneOfEqIso (congrFun hs₀.symm i) (congrFun hs₀.symm j) (g.s₁ k)).inv ≫
          eqToHom (by rw [PreOneHypercover.congrIndexOneOfEq_congrFun hs₀ hs₁]) := by
  refine ⟨fun h ↦ ?_, fun ⟨hs₀, hh₀, hs₁, hh₁⟩ ↦ Hom.ext' hs₀ hh₀ hs₁ hh₁⟩
  subst h
  simp [congrIndexOneOfEq]

@[simp]
lemma PreOneHypercover.hom_inv_s₁_apply {S : C} {E F : PreOneHypercover.{w} S} (e : E ≅ F)
    {i j : E.I₀} (k : E.I₁ i j) :
    e.inv.s₁ (e.hom.s₁ k) = E.congrIndexOneOfEq (by simp) (by simp) k := by
  obtain ⟨hs₀, hh₀, hs₁, hh₁⟩ := PreOneHypercover.Hom.ext'_iff.mp e.hom_inv_id
  simpa using hs₁ i j k

@[simp]
lemma PreOneHypercover.inv_hom_s₁_apply {S : C} {E F : PreOneHypercover.{w} S} (e : E ≅ F)
    {i j : F.I₀} (k : F.I₁ i j) :
    e.hom.s₁ (e.inv.s₁ k) = F.congrIndexOneOfEq (by simp) (by simp) k := by
  obtain ⟨hs₀, hh₀, hs₁, hh₁⟩ := PreOneHypercover.Hom.ext'_iff.mp e.inv_hom_id
  simpa using hs₁ i j k

@[reassoc (attr := simp)]
lemma PreOneHypercover.hom_inv_h₀ {S : C} {E F : PreOneHypercover.{w} S} (e : E ≅ F) (i : E.I₀) :
    e.hom.h₀ i ≫ e.inv.h₀ (e.hom.s₀ i) = eqToHom (by simp) := by
  obtain ⟨hs, hh, _⟩ := Hom.ext'_iff.mp e.hom_inv_id
  simpa using hh i

@[reassoc (attr := simp)]
lemma PreOneHypercover.inv_hom_h₀ {S : C} {E F : PreOneHypercover.{w} S} (e : E ≅ F) (i : F.I₀) :
    e.inv.h₀ i ≫ e.hom.h₀ (e.inv.s₀ i) = eqToHom (by simp) := by
  obtain ⟨hs, hh, _⟩ := Hom.ext'_iff.mp e.inv_hom_id
  simpa using hh i

@[reassoc (attr := simp)]
lemma PreOneHypercover.hom_inv_h₁ {S : C} {E F : PreOneHypercover.{w} S} (e : E ≅ F)
    {i j : E.I₀} (k : E.I₁ i j) :
    e.hom.h₁ k ≫ e.inv.h₁ (e.hom.s₁ k) =
      (E.congrIndexOneOfEqIso (hom_inv_s₀_apply e i).symm (hom_inv_s₀_apply e j).symm k).inv ≫
      eqToHom (by congr 1; simp) := by
  obtain ⟨hs, _, _, hh⟩ := Hom.ext'_iff.mp e.hom_inv_id
  simpa using hh i j k

@[reassoc (attr := simp)]
lemma PreOneHypercover.inv_hom_h₁ {S : C} {E F : PreOneHypercover.{w} S} (e : E ≅ F)
    {i j : F.I₀} (k : F.I₁ i j) :
    e.inv.h₁ k ≫ e.hom.h₁ (e.inv.s₁ k) =
      (F.congrIndexOneOfEqIso (inv_hom_s₀_apply e i).symm (inv_hom_s₀_apply e j).symm k).inv ≫
      eqToHom (by congr 1; simp) := by
  obtain ⟨hs, _, _, hh⟩ := Hom.ext'_iff.mp e.inv_hom_id
  simpa using hh i j k

instance {S : C} {E F : PreOneHypercover.{w} S} (e : E ≅ F) (i : E.I₀) : IsIso (e.hom.h₀ i) := by
  use e.inv.h₀ (e.hom.s₀ i) ≫ eqToHom (by simp)
  rw [PreOneHypercover.hom_inv_h₀_assoc, eqToHom_trans, eqToHom_refl, Category.assoc,
    ← eqToHom_naturality _ (by simp), PreOneHypercover.inv_hom_h₀_assoc]
  simp

instance {S : C} {E F : PreOneHypercover.{w} S} (e : E ≅ F) (i : F.I₀) : IsIso (e.inv.h₀ i) :=
  .of_isIso_fac_right (PreOneHypercover.inv_hom_h₀ e i)

instance {S : C} {E F : PreOneHypercover.{w} S} (e : E ≅ F) {i j : E.I₀} (k : E.I₁ i j) :
    IsIso (e.hom.h₁ k) := by
  use e.inv.h₁ _ ≫ eqToHom (by congr 1; simp) ≫ (E.congrIndexOneOfEqIso (by simp) (by simp) k).hom
  simp only [PreOneHypercover.hom_inv_h₁_assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
    Iso.inv_hom_id, Category.assoc, true_and, PreOneHypercover.congrIndexOneOfEqIso_hom_naturality]
  rw [← eqToHom_naturality_assoc _ (by simp)]
  simp

instance {S : C} {E F : PreOneHypercover.{w} S} (e : E ≅ F) {i j : F.I₀} (k : F.I₁ i j) :
    IsIso (e.inv.h₁ k) :=
  .of_isIso_fac_right (PreOneHypercover.inv_hom_h₁ e k)

@[simps]
def PreOneHypercover.Hom.mapMulticospan {S : C} {E : PreOneHypercover.{w} S}
    {F : PreOneHypercover.{w'} S} (f : E.Hom F) :
    WalkingMulticospan E.multicospanShape ⥤ WalkingMulticospan F.multicospanShape where
  obj
    | .left i => .left (f.s₀ i)
    | .right i => .right (f.s₁' i)
  map
    | .id _ => .id _
    | .fst i => WalkingMulticospan.Hom.fst (J := F.multicospanShape) (f.s₁' i)
    | .snd i => WalkingMulticospan.Hom.snd (J := F.multicospanShape) (f.s₁' i)
  map_id := by simp
  map_comp
    | .id _, _ => by simp
    | .fst _, .id _ => by simp
    | .snd _, .id _ => by simp

/-- Isomorphic pre-`1`-hypercovers have equivalent mutifork index categories. -/
@[simps! functor inverse]
def PreOneHypercover.equivalenceMulticospanOfIso {S : C} {E F : PreOneHypercover.{w} S}
    (f : E ≅ F) :
    WalkingMulticospan E.multicospanShape ≌ WalkingMulticospan F.multicospanShape := by
  refine .mk f.hom.mapMulticospan f.inv.mapMulticospan ?_ ?_
  · refine WalkingMulticospan.functorExt (fun i ↦ eqToIso (by simp)) (fun i ↦ eqToIso ?_) ?_ ?_
    · dsimp
      rw [WalkingMulticospan.right.injEq]
      apply PreOneHypercover.I₁'.ext <;> simp
    · intro i
      dsimp
      rw [eqToHom_naturality]
      apply PreOneHypercover.I₁'.ext <;> simp
    · intro i
      dsimp
      rw [eqToHom_naturality]
      apply PreOneHypercover.I₁'.ext <;> simp
  · refine WalkingMulticospan.functorExt (fun i ↦ eqToIso (by simp)) (fun i ↦ eqToIso ?_) ?_ ?_
    · dsimp
      rw [WalkingMulticospan.right.injEq]
      apply PreOneHypercover.I₁'.ext <;> simp
    · intro i
      dsimp
      rw [eqToHom_naturality]
      apply PreOneHypercover.I₁'.ext <;> simp
    · intro i
      dsimp
      rw [eqToHom_naturality]
      apply PreOneHypercover.I₁'.ext <;> simp

/-- If `E` and `F` are isomorphic pre-`1`-hypercovers and `G` is a presheaf,
the multifork for `E` is exact if and only if the multifork for `E` is exact. -/
noncomputable
def PreOneHypercover.isLimitEquivOfIso {S : C} {E : PreOneHypercover.{w} S}
    {F : PreOneHypercover.{w} S} (f : E ≅ F)
    (G : Cᵒᵖ ⥤ A) :
    IsLimit (E.multifork G) ≃ IsLimit (F.multifork G) := by
  refine Equiv.trans ?_
    (IsLimit.whiskerEquivalenceEquiv <| PreOneHypercover.equivalenceMulticospanOfIso f).symm
  refine IsLimit.equivOfNatIsoOfIso ?_ _ _ ?_
  · refine WalkingMulticospan.functorExt ?_ ?_ ?_ ?_
    · intro i
      exact G.mapIso (asIso (f.hom.h₀ i)).symm.op
    · intro i
      dsimp
      exact G.mapIso (asIso (f.hom.h₁ i.2)).symm.op
    · intro i
      simp [← Functor.map_comp_assoc, ← Functor.map_comp, ← op_comp, f.hom.w₁₁]
    · intro i
      simp [← Functor.map_comp_assoc, ← Functor.map_comp, ← op_comp, f.hom.w₁₂]
  · refine Cones.ext (Iso.refl _) fun i ↦ ?_
    induction i with
    | left _ => simp [← Functor.map_comp, ← op_comp]
    | right _ => simp [← Functor.map_comp, ← op_comp, f.hom.w₁₁_assoc]

/-- Being a colimiting cofan is stable under equivalences in the index type. -/
def Limits.Cofan.isColimitEquivOfEquiv {ι ι' : Type*} {X : ι → C} (c : Cofan X) (e : ι' ≃ ι) :
    IsColimit c ≃ IsColimit (Cofan.mk _ fun i : ι' ↦ c.inj (e i)) :=
  IsColimit.whiskerEquivalenceEquiv (Discrete.equivalence e)

/-- Being a limiting fan is stable under equivalences in the index type. -/
def Limits.Fan.isLimitEquivOfEquiv {ι ι' : Type*} {X : ι → C} (c : Fan X) (e : ι' ≃ ι) :
    IsLimit c ≃ IsLimit (Fan.mk _ fun i : ι' ↦ c.proj (e i)) :=
  IsLimit.whiskerEquivalenceEquiv (Discrete.equivalence e)

/--
If
- `F` contravariantly maps (suitable) coproducts to products,
- (suitable) coproducts exist in `C`, and
- (suitable) coproducts distribute over pullbacks, then:

`F` is a sheaf for the single object covering `{ ∐ᵢ Yᵢ ⟶ X }`
if and only if it is a presieve for `{ fᵢ : Yᵢ ⟶ X }ᵢ`.

Note: The second two conditions are satisfied if `C` is (finitary) extensive.
-/
noncomputable
def PreZeroHypercover.isLimitSigmaOfIsColimitEquiv {X : C}
    (E : PreZeroHypercover.{w} X) [E.HasPullbacks]
    {c : Cofan E.X} (hc : IsColimit c) (huniv : IsUniversalColimit c)
    [(E.sigmaOfIsColimit hc).HasPullbacks]
    [∀ i, HasPullback (E.f i) ((E.sigmaOfIsColimit hc).f PUnit.unit)]
    (F : Cᵒᵖ ⥤ A)
    [PreservesLimit (Discrete.functor fun i ↦ op (E.toPreOneHypercover.X i)) F]
    [PreservesLimit (Discrete.functor fun i ↦ op (E.toPreOneHypercover.Y' i)) F] :
    IsLimit ((E.sigmaOfIsColimit hc).toPreOneHypercover.multifork F) ≃
      IsLimit (E.toPreOneHypercover.multifork F) := by
  have : HasPullback (Cofan.IsColimit.desc hc E.f) (Cofan.IsColimit.desc hc E.f) :=
    inferInstanceAs <| HasPullback
      ((E.sigmaOfIsColimit hc).f ⟨⟩) ((E.sigmaOfIsColimit hc).f ⟨⟩)
  let c' : Cofan E.toPreOneHypercover.Y' :=
    Cofan.mk
      ((E.sigmaOfIsColimit hc).toPreOneHypercover.Y (i₁ := ⟨⟩) (i₂ := ⟨⟩) ⟨⟩)
      fun b ↦ pullback.map _ _ _ _ (c.inj _) (c.inj _) (𝟙 _) (by simp) (by simp)
  let equiv : E.toPreOneHypercover.I₁' ≃ E.I₀ × E.I₀ :=
    Equiv.sigmaPUnit (E.toPreOneHypercover.I₀ × E.toPreOneHypercover.I₀)
  have hc' : IsColimit c' := by
    refine (c'.isColimitEquivOfEquiv equiv.symm).symm (Nonempty.some ?_)
    exact IsUniversalColimit.nonempty_isColimit_prod_of_isPullback
      huniv huniv E.f E.f ((E.sigmaOfIsColimit hc).f ⟨⟩) ((E.sigmaOfIsColimit hc).f ⟨⟩)
      (fun i j ↦ .of_hasPullback _ _) (.of_hasPullback _ _) (.refl _) (by simp) (by simp)
      (by simp [c', equiv, Equiv.sigmaPUnit]) (by simp [c', equiv, Equiv.sigmaPUnit])
  refine .trans ?_ (E.toPreOneHypercover.isLimitSigmaOfIsColimitEquiv hc hc' F)
  apply PreOneHypercover.isLimitEquivOfIso
  refine PreOneHypercover.isoMk (.refl _) (fun _ ↦ .refl _) (fun _ _ ↦ .refl _)
      (fun _ _ _ ↦ Iso.refl _) (by cat_disch) ?_ ?_
  · intro ⟨⟩ ⟨⟩ k
    refine Cofan.IsColimit.hom_ext hc' _ _ fun k ↦ ?_
    congr 1
    exact Cofan.IsColimit.hom_ext hc' _ _ fun a ↦ by simp; simp [c']
  · intro ⟨⟩ ⟨⟩ k
    exact Cofan.IsColimit.hom_ext hc' _ _ fun a ↦ by simp; simp [c']

@[simp]
lemma PreZeroHypercover.presieve₀_sigmaOfIsColimit {S : C} (E : PreZeroHypercover.{w} S)
    {c : Cofan E.X} (hc : IsColimit c) :
    (E.sigmaOfIsColimit hc).presieve₀ = Presieve.singleton (Cofan.IsColimit.desc hc E.f) :=
  Presieve.ofArrows_pUnit _

open PreZeroHypercover in
/--
Let `{ fᵢ : Yᵢ ⟶ X }` be a family of morphisms. If `∐ᵢ Yᵢ` is a universal coproduct
and the presheaf `F` preserves products, then `F` is a sheaf for the single object covering
`{ ∐ᵢ Yᵢ ⟶ X }` if and only if it is a sheaf for `{ fᵢ : Yᵢ ⟶ X }ᵢ`.
-/
lemma Presieve.isSheafFor_sigmaDesc_iff {F : Cᵒᵖ ⥤ Type v} {X : C} {ι : Type*} {Y : ι → C}
    (f : ∀ i, Y i ⟶ X) [(ofArrows Y f).HasPairwisePullbacks]
    (c : Cofan Y) (hc : IsColimit c) (hc' : IsUniversalColimit c)
    [HasPullback (Cofan.IsColimit.desc hc f) (Cofan.IsColimit.desc hc f)]
    [∀ i, HasPullback (f i) (Cofan.IsColimit.desc hc f)]
    [PreservesLimit (Discrete.functor <| fun i ↦ op (Y i)) F]
    [PreservesLimit (Discrete.functor fun (ij : ι × ι) ↦ op (pullback (f ij.1) (f ij.2))) F] :
    Presieve.IsSheafFor F (.singleton <| Cofan.IsColimit.desc hc f) ↔
      Presieve.IsSheafFor F (.ofArrows Y f) := by
  let E := PreZeroHypercover.mk _ _ f
  have : (E.sigmaOfIsColimit hc).HasPullbacks :=
    fun i j ↦ by dsimp [sigmaOfIsColimit]; infer_instance
  have (i : E.I₀) : HasPullback (E.f i) ((E.sigmaOfIsColimit hc).f PUnit.unit) := by
    dsimp [sigmaOfIsColimit]; infer_instance
  have : PreservesLimit (Discrete.functor fun i ↦ op (E.toPreOneHypercover.X i)) F := by
    dsimp [E]; infer_instance
  have : PreservesLimit (Discrete.functor fun i ↦ op (E.toPreOneHypercover.Y' i)) F := by
    convert Functor.Initial.preservesLimit_of_comp (Discrete.equivalence <| .sigmaPUnit _).inverse
    assumption
  let equiv := (E.isLimitSigmaOfIsColimitEquiv hc hc' F).nonempty_congr
  rwa [isLimit_toPreOneHypercover_type_iff, isLimit_toPreOneHypercover_type_iff,
    presieve₀_sigmaOfIsColimit] at equiv

end CategoryTheory

namespace AlgebraicGeometry

open Scheme

variable {P : MorphismProperty Scheme.{u}}

-- This holds more generally if `𝒰.J` is `u`-small, but we don't need that for now.
lemma Scheme.Cover.isSheafFor_sigma_iff {F : Scheme.{u}ᵒᵖ ⥤ Type w} [IsZariskiLocalAtSource P]
    (hF : Presieve.IsSheaf Scheme.zariskiTopology F)
    {S : Scheme.{u}} (𝒰 : S.Cover (precoverage P)) [Finite 𝒰.I₀] :
    Presieve.IsSheafFor F (.ofArrows 𝒰.sigma.X 𝒰.sigma.f) ↔
      Presieve.IsSheafFor F (.ofArrows 𝒰.X 𝒰.f) := by
  have : PreservesLimitsOfShape (Discrete (𝒰.I₀ × 𝒰.I₀)) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  have : PreservesLimitsOfShape (Discrete 𝒰.I₀) F :=
    preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hF
  let c : Cofan 𝒰.X := Cofan.mk _ (Sigma.ι 𝒰.X)
  rw [← Presieve.isSheafFor_sigmaDesc_iff 𝒰.f _ (coproductIsCoproduct _)
    (FinitaryExtensive.isVanKampen_finiteCoproducts (coproductIsCoproduct _)).isUniversal]
  congr!
  rw [← PreZeroHypercover.presieve₀, 𝒰.presieve₀_sigma]
  rfl

variable (P : MorphismProperty Scheme.{u})

lemma zariskiTopology_le_propqcTopology [P.IsMultiplicative] [IsZariskiLocalAtSource P] :
    zariskiTopology ≤ propQCTopology P := by
  apply Precoverage.toGrothendieck_mono
  rw [le_inf_iff]
  refine ⟨?_, ?_⟩
  · apply zariskiPrecoverage_le_qcPrecoverage
  · rw [precoverage, precoverage]
    gcongr
    apply MorphismProperty.precoverage_monotone
    intro X Y f hf
    apply IsZariskiLocalAtSource.of_isOpenImmersion

open Opposite

variable {P} [P.IsStableUnderBaseChange]

lemma Scheme.Cover.Hom.isSheafFor {F : Scheme.{u}ᵒᵖ ⥤ Type*} {S : Scheme.{u}}
    {𝒰 𝒱 : S.Cover (precoverage P)}
    (f : 𝒰 ⟶ 𝒱)
    (H₁ : Presieve.IsSheafFor F (.ofArrows _ 𝒰.f))
    (H₂ : ∀ {X : Scheme.{u}} (f : X ⟶ S),
      Presieve.IsSeparatedFor F (.ofArrows (𝒰.pullback₂ f).X (𝒰.pullback₂ f).f)) :
    Presieve.IsSheafFor F (.ofArrows 𝒱.X 𝒱.f) := by
  rw [Presieve.isSheafFor_iff_generate]
  apply Presieve.isSheafFor_subsieve_aux (S := .generate (.ofArrows 𝒰.X 𝒰.f))
  · change Sieve.generate _ ≤ Sieve.generate _
    rw [Sieve.generate_le_iff]
    rintro - - ⟨i⟩
    rw [← f.w₀]
    exact ⟨_, f.h₀ i, 𝒱.f _, ⟨_⟩, rfl⟩
  · rwa [← Presieve.isSheafFor_iff_generate]
  · intro Y f hf
    rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
    rw [← Presieve.ofArrows_pullback]
    apply H₂

instance {S : Scheme.{u}} (𝒰 : S.AffineCover P) (i : 𝒰.I₀) : IsAffine (𝒰.cover.X i) :=
  inferInstanceAs <| IsAffine (Spec _)

instance {S : Scheme.{u}} [IsAffine S] (𝒰 : S.AffineCover P) [Finite 𝒰.I₀] :
    QuasiCompactCover 𝒰.cover.toPreZeroHypercover :=
  haveI : Finite 𝒰.cover.I₀ := ‹_›
  .of_finite

/-- A Zariski-`1`-hypercover of a scheme where all components are affine. -/
@[simps! toPreOneHypercover_toPreZeroHypercover]
noncomputable
def Scheme.affineOneHypercover (X : Scheme.{u}) : zariskiTopology.OneHypercover X :=
  .mk'
    (X.affineCover.refineOneHypercover fun i j ↦
      (pullback (X.affineCover.f i) (X.affineCover.f j)).affineCover.toPreZeroHypercover)
    X.affineCover.mem_grothendieckTopology
    fun i j ↦ by simpa using Cover.mem_grothendieckTopology _

/-- A pre-sheaf is a sheaf for the `P`-qc topology if and only if it is a sheaf
for the Zariski topology and satisfies the sheaf property for all single object coverings
`{ f : Spec S ⟶ Spec R }` where `f` satisifies `P`. -/
@[stacks 022H]
nonrec lemma isSheaf_propqcTopology_iff [P.IsMultiplicative] (F : Scheme.{u}ᵒᵖ ⥤ Type*)
    [IsZariskiLocalAtSource P] :
    Presieve.IsSheaf (propQCTopology P) F ↔
      Presieve.IsSheaf Scheme.zariskiTopology F ∧
        ∀ {R S : CommRingCat.{u}} (f : R ⟶ S), P (Spec.map f) → Surjective (Spec.map f) →
          Presieve.IsSheafFor F (.singleton (Spec.map f)) := by
  refine ⟨fun hF ↦ ⟨?_, fun {R S} f hf hs ↦ ?_⟩, fun ⟨hzar, hff⟩ ↦ ?_⟩
  · exact Presieve.isSheaf_of_le _ (zariskiTopology_le_propqcTopology P) hF
  · apply hF.isSheafFor
    rw [← Hom.presieve₀_cover _ hf]
    exact Cover.mem_propQCTopology _
  · rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange_of_small.{u}]
    intro T (𝒰 : Scheme.Cover _ _)
    wlog hT : ∃ (R : CommRingCat.{u}), T = Spec R generalizing T
    · refine T.affineOneHypercover.isSheafFor_of_pullback hzar ?_ ?_
      · intro i
        rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
          ← Presieve.isSheafFor_iff_generate]
        exact this (𝒰.pullback₂ (T.affineCover.f i)) ⟨_, rfl⟩
      · intro i j k
        rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
        apply Presieve.IsSheafFor.isSeparatedFor
        rw [← Presieve.ofArrows_pullback]
        exact this (𝒰.pullback₂ _) ⟨_, rfl⟩
    obtain ⟨R, rfl⟩ := hT
    wlog h𝒰 : (∀ i, IsAffine (𝒰.X i)) ∧ Finite 𝒰.I₀ generalizing R 𝒰
    · obtain ⟨𝒱, f, hfin, ho⟩ := QuasiCompactCover.exists_hom 𝒰.forgetQc
      have H (V : Scheme.{u}) (f : V ⟶ Spec R) : Presieve.IsSheafFor F
          (.ofArrows (𝒱.cover.pullback₂ f).X (𝒱.cover.pullback₂ f).f) := by
        refine V.affineOneHypercover.isSheafFor_of_pullback hzar ?_ ?_
        · intro i
          rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
            ← Presieve.isSheafFor_iff_generate]
          let 𝒰' := (𝒱.cover.pullback₂ f).pullback₂ (V.affineCover.f i)
          exact this _ (.ofQuasiCompactCover 𝒰' (qc := by dsimp [𝒰']; infer_instance))
            ⟨fun j ↦ .of_isIso (pullbackLeftPullbackSndIso (𝒱.f j) f (V.affineCover.f i)).hom, hfin⟩
        · intro i j k
          rw [← Sieve.pullbackArrows_comm, ← Presieve.ofArrows_pullback,
            ← Presieve.isSeparatedFor_iff_generate]
          exact (this _ (.ofQuasiCompactCover ((𝒱.cover.pullback₂ f).pullback₂ _)
              (qc := by dsimp; infer_instance))
            ⟨fun l ↦ .of_isIso (pullbackLeftPullbackSndIso (𝒱.f l) f _).hom, hfin⟩).isSeparatedFor
      refine Scheme.Cover.Hom.isSheafFor f ?_ fun f ↦ (H _ f).isSeparatedFor
      exact this _ (.ofQuasiCompactCover 𝒱.cover)
        ⟨fun i ↦ inferInstanceAs <| IsAffine (Spec _), hfin⟩
    obtain ⟨_, _⟩ := h𝒰
    let 𝒰' := 𝒰.forgetQc.sigma
    rw [← Scheme.Cover.forgetQc_toPreZeroHypercover,
      ← Scheme.Cover.isSheafFor_sigma_iff hzar, Presieve.ofArrows_of_unique]
    have : IsAffine (𝒰.forgetQc.sigma.X default) := by dsimp; infer_instance
    let f : Spec _ ⟶ Spec R := (𝒰.forgetQc.sigma.X default).isoSpec.inv ≫ 𝒰.forgetQc.sigma.f default
    obtain ⟨φ, hφ⟩ := Spec.map_surjective f
    rw [Presieve.isSheafFor_singleton_iff_of_iso _ (Spec.map φ)
      (𝒰.forgetQc.sigma.X default).isoSpec (by simp [hφ, f])]
    refine hff _ ?_ ?_
    · simpa only [hφ, f] using IsZariskiLocalAtSource.comp (𝒰.forgetQc.sigma.map_prop _) _
    · simp only [hφ, f, Cover.sigma_I₀, PUnit.default_eq_unit, Cover.sigma_X, Cover.sigma_f, f]
      have : Surjective (Sigma.desc 𝒰.f) := inferInstanceAs <| Surjective (Sigma.desc 𝒰.forgetQc.f)
      infer_instance

end AlgebraicGeometry
