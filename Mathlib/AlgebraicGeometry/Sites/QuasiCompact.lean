/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.AlgebraicGeometry.Cover.QuasiCompact

/-!

-/

universe w' w v u

open CategoryTheory Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace PreZeroHypercover

variable {S : C}

@[ext (iff := false)]
lemma Hom.ext' {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{w'} S}
    {f g : E.Hom F} (hs : f.s₀ = g.s₀) (hh : ∀ i, f.h₀ i = g.h₀ i ≫ eqToHom (by rw [hs])) :
    f = g := by
  cases f
  cases g
  simp only at hs
  subst hs
  simp only [eqToHom_refl, Category.comp_id] at hh
  simp only [PreZeroHypercover.Hom.mk.injEq, heq_eq_eq, true_and]
  ext
  apply hh

lemma Hom.ext'_iff {E : PreZeroHypercover.{w} S} {F : PreZeroHypercover.{w'} S}
    {f g : E.Hom F} :
    f = g ↔ ∃ (hs : f.s₀ = g.s₀), ∀ i, f.h₀ i = g.h₀ i ≫ eqToHom (by rw [hs]) :=
  ⟨fun h ↦ h ▸ by simp, fun ⟨hs, hh⟩ ↦ Hom.ext' hs hh⟩

/-- Constructor for isomorphisms of pre-`0`-hypercovers. -/
@[simps]
def isoMk {S : C} {E F : PreZeroHypercover.{w} S}
    (s₀ : E.I₀ ≃ F.I₀) (h₀ : ∀ i, E.X i ≅ F.X (s₀ i))
    (w₀ : ∀ i, (h₀ i).hom ≫ F.f _ = E.f _ := by cat_disch) :
    E ≅ F where
  hom.s₀ := s₀
  hom.h₀ i := (h₀ i).hom
  inv.s₀ := s₀.symm
  inv.h₀ i := eqToHom (by simp) ≫ (h₀ _).inv
  inv.w₀ i := by
    obtain ⟨i, rfl⟩ := s₀.surjective i
    simp only [← cancel_epi (h₀ i).hom, w₀, Category.assoc, Equiv.symm_apply_apply,
      eqToHom_iso_hom_naturality_assoc, Iso.hom_inv_id_assoc]
    rw [← CategoryTheory.eqToHom_naturality _ (by simp)]
    simp
  hom_inv_id := Hom.ext' (by ext; simp) (fun i ↦ by simp)
  inv_hom_id := Hom.ext' (by ext; simp) (fun i ↦ by simp)

@[simp]
lemma hom_inv_s₀_apply {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : E.I₀) :
    e.inv.s₀ (e.hom.s₀ i) = i :=
  congr($(e.hom_inv_id).s₀ i)

@[simp]
lemma inv_hom_s₀_apply {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : F.I₀) :
    e.hom.s₀ (e.inv.s₀ i) = i :=
  congr($(e.inv_hom_id).s₀ i)

@[reassoc (attr := simp)]
lemma hom_inv_h₀ {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : E.I₀) :
    e.hom.h₀ i ≫ e.inv.h₀ (e.hom.s₀ i) = eqToHom (by simp) := by
  obtain ⟨hs, hh⟩ := Hom.ext'_iff.mp e.hom_inv_id
  simpa using hh i

@[reassoc (attr := simp)]
lemma inv_hom_h₀ {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : F.I₀) :
    e.inv.h₀ i ≫ e.hom.h₀ (e.inv.s₀ i) = eqToHom (by simp) := by
  obtain ⟨hs, hh⟩ := Hom.ext'_iff.mp e.inv_hom_id
  simpa using hh i

instance {S : C} {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : E.I₀) :
    IsIso (e.hom.h₀ i) := by
  use e.inv.h₀ (e.hom.s₀ i) ≫ eqToHom (by simp)
  rw [hom_inv_h₀_assoc, eqToHom_trans, eqToHom_refl, Category.assoc,
    ← eqToHom_naturality _ (by simp), inv_hom_h₀_assoc]
  simp

instance {S : C} {E F : PreZeroHypercover.{w} S} (e : E ≅ F) (i : F.I₀) :
    IsIso (e.inv.h₀ i) :=
  .of_isIso_fac_right (inv_hom_h₀ e i)

end PreZeroHypercover

/-- The pre-`0`-hypercover associated to a presieve `R`. It is indexed by the morphisms in `R`. -/
@[simps -isSimp]
def Presieve.preZeroHypercover {S : C} (R : Presieve S) : PreZeroHypercover.{max u v} S where
  I₀ := R.uncurry
  X i := i.1.1
  f i := i.1.2

@[simp]
lemma Presieve.presieve₀_preZeroHypercover {S : C} (R : Presieve S) :
    R.preZeroHypercover.presieve₀ = R := by
  refine le_antisymm ?_ ?_
  · rintro - - ⟨i⟩
    exact i.2
  · intro Y f h
    let i : R.uncurry := ⟨⟨Y, f⟩, h⟩
    exact .mk i

lemma Presieve.exists_eq_preZeroHypercover {S : C} (R : Presieve S) :
    ∃ (E : PreZeroHypercover.{max u v} S), R = E.presieve₀ :=
  ⟨R.preZeroHypercover, by simp⟩

@[simps! -isSimp]
def PreZeroHypercover.shrink {S : C} (E : PreZeroHypercover.{w} S) :
    PreZeroHypercover.{max u v} S :=
  E.presieve₀.preZeroHypercover

@[simp]
lemma PreZeroHypercover.presieve₀_shrink {S : C} (E : PreZeroHypercover.{w} S) :
    E.shrink.presieve₀ = E.presieve₀ :=
  E.presieve₀.presieve₀_preZeroHypercover

lemma PreZeroHypercover.shrink_eq_shrink_of_presieve₀_eq_presieve₀ {S : C}
    {E F : PreZeroHypercover.{w} S} (h : E.presieve₀ = F.presieve₀) :
    E.shrink = F.shrink := by
  rw [shrink, shrink, h]

def PreZeroHypercover.toShrink {S : C} (E : PreZeroHypercover.{w} S) : E.Hom E.shrink where
  s₀ i := ⟨⟨_, E.f i⟩, .mk i⟩
  h₀ i := 𝟙 _

noncomputable
def PreZeroHypercover.fromShrink {S : C} (E : PreZeroHypercover.{w} S) : E.shrink.Hom E where
  s₀ i := (Presieve.ofArrows_surj _ _ i.2).choose
  h₀ i := eqToHom (Presieve.ofArrows_surj _ _ i.2).choose_spec.1.symm
  w₀ i := (Presieve.ofArrows_surj _ _ i.2).choose_spec.2.symm

instance {X Y : C} (f : X ⟶ Y) : Unique (PreZeroHypercover.singleton f).I₀ :=
  inferInstanceAs <| Unique PUnit

variable (C) in
@[ext]
structure PreZeroHypercoverFamily where
  property ⦃X : C⦄ : ObjectProperty (PreZeroHypercover.{max u v} X)
  iff_shrink {X : C} {E : PreZeroHypercover.{max u v} X} : property E ↔ property E.shrink

instance : CoeFun (PreZeroHypercoverFamily C)
    fun _ ↦ ⦃X : C⦄ → (E : PreZeroHypercover.{max u v} X) → Prop where
  coe P := P.property

inductive PreZeroHypercoverFamily.presieve (P : PreZeroHypercoverFamily C) {X : C} :
    Presieve X → Prop where
  | mk (E : PreZeroHypercover.{max u v} X) : P E → presieve P E.presieve₀

def PreZeroHypercoverFamily.precoverage (P : PreZeroHypercoverFamily C) :
    Precoverage C where
  coverings _ R := P.presieve R

lemma PreZeroHypercoverFamily.mem_precoverage_iff {P : PreZeroHypercoverFamily C} {X : C}
    {R : Presieve X} :
    R ∈ P.precoverage X ↔ ∃ (E : PreZeroHypercover.{max u v} X), P E ∧ R = E.presieve₀ :=
  ⟨fun ⟨E, hE⟩ ↦ ⟨E, hE, rfl⟩, fun ⟨_, hE, h⟩ ↦ h ▸ ⟨_, hE⟩⟩

@[simp]
lemma PreZeroHypercover.presieve₀_mem_precoverage_iff {P : PreZeroHypercoverFamily C} {X : C}
    {E : PreZeroHypercover.{max u v} X} :
    E.presieve₀ ∈ P.precoverage X ↔ P E := by
  refine ⟨fun h ↦ ?_, fun h ↦ .mk _ h⟩
  rw [PreZeroHypercoverFamily.mem_precoverage_iff] at h
  obtain ⟨F, h, heq⟩ := h
  rw [P.iff_shrink] at h ⊢
  rwa [PreZeroHypercover.shrink_eq_shrink_of_presieve₀_eq_presieve₀ heq]

@[simps]
def Precoverage.preZeroHypercoverFamily (K : Precoverage C) :
    PreZeroHypercoverFamily C where
  property X E := E.presieve₀ ∈ K X
  iff_shrink {X} E := by simp

variable (C) in
/-- Giving a precoverage on a category is the same as giving a predicate
on every pre-`0`-hypercover that is stable under deduplication. -/
def Precoverage.equivPreZeroHypercoverFamily :
    Precoverage C ≃ PreZeroHypercoverFamily C where
  toFun K := K.preZeroHypercoverFamily
  invFun P := P.precoverage
  left_inv K := by
    ext X R
    obtain ⟨E, rfl⟩ := R.exists_eq_preZeroHypercover
    simp
  right_inv P := by cat_disch

lemma Precoverage.HasIsos.of_preZeroHypercoverFamily {P : PreZeroHypercoverFamily C}
    (h : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) [IsIso f], P (.singleton f)) :
    P.precoverage.HasIsos where
  mem_coverings_of_isIso {S T} f hf := by
    rw [← PreZeroHypercover.presieve₀_singleton.{_, _, max u v}]
    refine .mk _ (h _)

lemma Precoverage.IsStableUnderBaseChange.of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms
    {P : PreZeroHypercoverFamily C}
    (h₁ : ∀ {X : C}, (P (X := X)).IsClosedUnderIsomorphisms)
    (h₂ : ∀ {X Y : C} (f : X ⟶ Y) (E : PreZeroHypercover.{max u v} Y)
      [∀ (i : E.I₀), HasPullback f (E.f i)], P E → P (E.pullback₁ f)) :
    Precoverage.IsStableUnderBaseChange.{max u v} P.precoverage where
  mem_coverings_of_isPullback {ι} S X f hf Y g Z p₁ p₂ h := by
    let E : PreZeroHypercover S := ⟨ι, X, f⟩
    have (i : E.I₀) : HasPullback g (E.f i) := (h i).hasPullback
    let F : PreZeroHypercover Y := ⟨_, _, p₁⟩
    let e : F ≅ E.pullback₁ g :=
      PreZeroHypercover.isoMk (Equiv.refl _) (fun i ↦ (h i).isoPullback)
    change F.presieve₀ ∈ _
    rw [F.presieve₀_mem_precoverage_iff, (P (X := Y)).prop_iff_of_iso e]
    refine h₂ _ _ ?_
    rwa [← E.presieve₀_mem_precoverage_iff]

lemma Precoverage.IsStableUnderComposition.of_preZeroHypercoverFamily
    {P : PreZeroHypercoverFamily C}
    (h : ∀ {X : C} (E : PreZeroHypercover.{max u v} X)
      (F : ∀ i, PreZeroHypercover.{max u v} (E.X i)),
      P E → (∀ i, P (F i)) → P (E.bind F)) :
    Precoverage.IsStableUnderComposition.{max u v, max u v} P.precoverage where
  comp_mem_coverings {ι} S X f hf σ Y g hg := by
    let E : PreZeroHypercover S := ⟨_, _, f⟩
    let F (i : ι) : PreZeroHypercover (E.X i) := ⟨_, _, g i⟩
    refine (E.bind F).presieve₀_mem_precoverage_iff.mpr (h _ _ ?_ fun i ↦ ?_)
    · rwa [← E.presieve₀_mem_precoverage_iff]
    · rw [← (F i).presieve₀_mem_precoverage_iff]
      exact hg i

end CategoryTheory

namespace AlgebraicGeometry
open AlgebraicGeometry

variable {S : Scheme.{u}}

@[simp]
lemma CategoryTheory.PreZeroHypercover.quasiCompact_shrink_iff (E : PreZeroHypercover.{w} S) :
    E.shrink.QuasiCompact ↔ E.QuasiCompact :=
  ⟨fun _ ↦ .of_hom E.fromShrink, fun _ ↦ .of_hom E.toShrink⟩

@[simps]
def qcCoverFamily : PreZeroHypercoverFamily Scheme.{u} where
  property X := X.quasiCompactCover
  iff_shrink {_} E := E.quasiCompact_shrink_iff.symm

/--
The quasi-compact precoverage on the category of schemes is the precoverage
given by quasi-compact covers. The intersection of this precoverage
with the precoverage defined by jointly surjective families of flat morphisms is
the fpqc-precoverage.
-/
def qcPrecoverage : Precoverage Scheme.{u} :=
  qcCoverFamily.precoverage

@[simp]
lemma CategoryTheory.PreZeroHypercover.presieve₀_mem_qcPrecoverage_iff
    {E : PreZeroHypercover.{w} S} : E.presieve₀ ∈ qcPrecoverage S ↔ E.QuasiCompact := by
  rw [← PreZeroHypercover.presieve₀_shrink, qcPrecoverage, E.shrink.presieve₀_mem_precoverage_iff]
  exact E.quasiCompact_shrink_iff

instance : qcPrecoverage.HasIsos := .of_preZeroHypercoverFamily <| by
  intro X Y f hf
  rw [qcCoverFamily_property, Scheme.quasiCompactCover_iff]
  infer_instance

instance : Precoverage.IsStableUnderBaseChange.{u + 1} qcPrecoverage.{u} := by
  refine .of_preZeroHypercoverFamily_of_isClosedUnderIsomorphisms ?_ ?_
  · intro X
    exact X.isClosedUnderIsomorphisms_quasiCompactCover
  · intro X Y f E h hE
    simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE ⊢
    infer_instance

instance : Precoverage.IsStableUnderComposition.{u + 1, u + 1} qcPrecoverage.{u} := by
  refine .of_preZeroHypercoverFamily ?_
  intro X E F hE hF
  simp only [qcCoverFamily_property, Scheme.quasiCompactCover_iff] at hE hF ⊢
  infer_instance

lemma foo (P : MorphismProperty Scheme.{u}) (hP : P ≤ fun _ _ f ↦ IsOpenMap f.base) :
    Scheme.precoverage P ≤ qcPrecoverage :=
  sorry

end AlgebraicGeometry
