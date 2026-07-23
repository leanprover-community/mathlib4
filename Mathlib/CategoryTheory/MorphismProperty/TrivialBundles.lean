/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Trivial bundles

Let `p : E ⟶ B` be a morphism in a category `C` and `F : C`. We introduce
a structure `TrivialBundleWithFiber F p` which contains the data
of a morphism `r : E ⟶ F` such `(p, r)` makes `E` the binary product of `B` and `F`.
The corresponding property of morphisms in `C` is `trivialBundleWithFiber F`.

-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D : Type*} [Category* C] [Category* D]

namespace MorphismProperty

/-- Given `F : C`, we say that `p : E ⟶ B` is a trivial bundle with fiber `F`
if we have a morphism `r : E ⟶ F` such `(p, r)` identify `E` to the binary
product of `B` and `F`. -/
structure TrivialBundleWithFiber (F : C) {E B : C} (p : E ⟶ B) where
  /-- the projection to the fiber -/
  r : E ⟶ F
  /-- `E` identifies to the binary product of `B` and `F`. -/
  isLimit : IsLimit (BinaryFan.mk p r)

initialize_simps_projections TrivialBundleWithFiber (-isLimit)

namespace TrivialBundleWithFiber

variable {F E B : C} {p : E ⟶ B} (h : TrivialBundleWithFiber F p)

lemma ext_iff {h₁ h₂ : TrivialBundleWithFiber F p} :
    h₁ = h₂ ↔ h₁.r = h₂.r := by
  constructor
  · rintro rfl
    rfl
  · obtain ⟨r₁, h₁⟩ := h₁
    obtain ⟨r₂, h₂⟩ := h₂
    rintro rfl
    obtain rfl : h₁ = h₂ := by subsingleton
    rfl

@[ext]
lemma ext {h₁ h₂ : TrivialBundleWithFiber F p} (eq : h₁.r = h₂.r) : h₁ = h₂ := by
  rwa [ext_iff]

set_option backward.defeqAttrib.useBackward true in
/-- If `p : E ⟶ B` is a trivial bundle with fiber `F`, and `F' ≅ F`,
then `p` is also a trivial bundle with fiber `F'`. -/
@[simps]
def chgFiber {F' : C} (e : F' ≅ F) : TrivialBundleWithFiber F' p where
  r := h.r ≫ e.inv
  isLimit := by
    let e' : pair B F' ≅ pair B F := mapPairIso (Iso.refl _) e
    refine (IsLimit.equivOfNatIsoOfIso e' _ _ ?_).2 h.isLimit
    refine BinaryFan.ext (Iso.refl _) ?_ ?_
    all_goals simp [BinaryFan.fst, BinaryFan.snd, e']

set_option backward.defeqAttrib.useBackward true in
/-- If `p : E ⟶ B` is a trivial bundle with fiber `F`, then so is any pullback of `p`. -/
@[simps]
noncomputable def pullback {E' B' : C} {p' : E' ⟶ B'} {f : B' ⟶ B} {f' : E' ⟶ E}
    (sq : IsPullback f' p' p f) :
    TrivialBundleWithFiber F p' where
  r := f' ≫ h.r
  isLimit :=
    BinaryFan.isLimitMk
      (fun s ↦ sq.lift (BinaryFan.IsLimit.lift' h.isLimit (s.fst ≫ f) s.snd).val s.fst
        (BinaryFan.IsLimit.lift' _ _ _).2.1)
      (fun s ↦ by simp)
      (fun s ↦ by simpa using (BinaryFan.IsLimit.lift' h.isLimit (s.fst ≫ f) s.snd).2.2)
      (fun s m hm₁ hm₂ ↦ by
        apply sq.hom_ext
        · apply BinaryFan.IsLimit.hom_ext h.isLimit
          · dsimp
            rw [Category.assoc, IsPullback.lift_fst, sq.w, reassoc_of% hm₁]
            exact (BinaryFan.IsLimit.lift' h.isLimit (s.fst ≫ f) s.snd).2.1.symm
          · dsimp
            rw [Category.assoc, IsPullback.lift_fst, hm₂]
            exact (BinaryFan.IsLimit.lift' h.isLimit (s.fst ≫ f) s.snd).2.2.symm
        · simp [hm₁])

variable (p) in
/-- If `p : E ⟶ B` is a morphism with `B` a terminal object, then `p` is a trivial
bundle with fiber `E`. -/
@[simps]
def ofIsTerminal (hB : IsTerminal B) : TrivialBundleWithFiber E p where
  r := 𝟙 E
  isLimit :=
    BinaryFan.isLimitMk (fun s ↦ s.snd) (fun s ↦ hB.hom_ext _ _)
      (fun s ↦ by simp)
      (fun s m _ hm ↦ by simpa using hm)

set_option backward.defeqAttrib.useBackward true in
/-- If `p : E ⟶ B` is a trivial bundle with fiber `F` and `B` is a terminal object,
then `E` is isomorphic to `F`. -/
@[simps hom]
def isoOfIsTerminal (h : TrivialBundleWithFiber F p) (hB : IsTerminal B) : E ≅ F where
  hom := h.r
  inv := (BinaryFan.IsLimit.lift' h.isLimit (hB.from _) (𝟙 _)).1
  hom_inv_id := by
    apply BinaryFan.IsLimit.hom_ext h.isLimit
    · apply hB.hom_ext
    · simp [dsimp% (BinaryFan.IsLimit.lift' h.isLimit (hB.from _) (𝟙 _)).2.2]
  inv_hom_id := (BinaryFan.IsLimit.lift' h.isLimit (hB.from _) (𝟙 _)).2.2

lemma isPullback_of_isTerminal {T : C} (hT : IsTerminal T) :
    IsPullback h.r p (hT.from _) (hT.from _) where
  w := by simp
  isLimit' :=
    ⟨PullbackCone.IsLimit.mk _
      (fun s ↦ (BinaryFan.IsLimit.lift' h.isLimit s.snd s.fst).1)
      (fun s ↦ (BinaryFan.IsLimit.lift' h.isLimit s.snd s.fst).2.2)
      (fun s ↦ (BinaryFan.IsLimit.lift' h.isLimit s.snd s.fst).2.1)
      (fun s m hm₁ hm₂ ↦ by
        apply BinaryFan.IsLimit.hom_ext h.isLimit
        · exact hm₂.trans (BinaryFan.IsLimit.lift' h.isLimit s.snd s.fst).2.1.symm
        · exact hm₁.trans (BinaryFan.IsLimit.lift' h.isLimit s.snd s.fst).2.2.symm)⟩

set_option backward.defeqAttrib.useBackward true in
/-- Two trivial bundles with the same fiber `F` are isomorphic. -/
lemma exists_iso {E' : C} {p' : E' ⟶ B} (h' : TrivialBundleWithFiber F p') :
    ∃ (e : E ≅ E'), e.hom ≫ p' = p ∧ e.hom ≫ h'.r = h.r := by
  obtain ⟨hom, h₁, h₂⟩ := BinaryFan.IsLimit.exists_lift h'.isLimit p h.r
  obtain ⟨inv, h₃, h₄⟩ := BinaryFan.IsLimit.exists_lift h.isLimit p' h'.r
  dsimp at h₁ h₂ h₃ h₄
  refine ⟨
    { hom := hom
      inv := inv
      hom_inv_id := ?_
      inv_hom_id := ?_ }, ?_, ?_⟩
  · apply BinaryFan.IsLimit.hom_ext h.isLimit <;> cat_disch
  · apply BinaryFan.IsLimit.hom_ext h'.isLimit <;> cat_disch
  · cat_disch
  · cat_disch

/-- If two morphism `p : E ⟶ B` and `p' : E' ⟶ B` are isomorphic over `B`,
and `p` is a trivial bundle with fiber `F`, then so is `p'`. -/
@[simps]
def ofIso {E' : C} (e : E' ≅ E) {p' : E' ⟶ B} (hp' : e.hom ≫ p = p') :
    TrivialBundleWithFiber F p' where
  r := e.hom ≫ h.r
  isLimit := IsLimit.ofIsoLimit h.isLimit (BinaryFan.ext e (by cat_disch) (by cat_disch)).symm

set_option backward.defeqAttrib.useBackward true in
lemma isPullback {E' B' : C} {p' : E' ⟶ B'} (h' : TrivialBundleWithFiber F p')
    (t : E' ⟶ E) (b : B' ⟶ B) (h₁ : t ≫ p = p' ≫ b) (h₂ : t ≫ h.r = h'.r) :
    IsPullback t p' p b where
  isLimit' :=
    ⟨Limits.PullbackCone.IsLimit.mk _
      (fun s ↦ BinaryFan.IsLimit.lift h'.isLimit s.snd (s.fst ≫ h.r))
      (fun s ↦ by
        have h₃ := BinaryFan.IsLimit.lift_fst h'.isLimit s.snd (s.fst ≫ h.r)
        have h₄ := BinaryFan.IsLimit.lift_snd h'.isLimit s.snd (s.fst ≫ h.r)
        dsimp at h₃ h₄
        apply BinaryFan.IsLimit.hom_ext h.isLimit
        · simp [h₁, reassoc_of% h₃, s.condition]
        · simp [h₂, h₄])
      (fun s ↦ BinaryFan.IsLimit.lift_fst h'.isLimit s.snd (s.fst ≫ h.r))
      (fun s m hm₁ hm₂ ↦ by
        have h₃ := BinaryFan.IsLimit.lift_fst h'.isLimit s.snd (s.fst ≫ h.r)
        have h₄ := BinaryFan.IsLimit.lift_snd h'.isLimit s.snd (s.fst ≫ h.r)
        dsimp at h₃ h₄
        apply BinaryFan.IsLimit.hom_ext h'.isLimit
        · dsimp
          rw [hm₂, h₃]
        · dsimp
          rw [h₄, ← h₂, reassoc_of% hm₁])⟩

/-- If `p : E ⟶ B` is a trivial bundle with fiber `F` in a category `C`,
then `G.map p` is a trivial bundle with fiber `G.obj F` in the category `D`
if `G : C ⥤ D` is a functor which commutes with the binary product of `B` and `F`. -/
@[simps]
noncomputable def map (G : C ⥤ D) [PreservesLimit (pair B F) G] :
    TrivialBundleWithFiber (G.obj F) (G.map p) where
  r := G.map h.r
  isLimit := mapIsLimitOfPreservesOfIsLimit _ _ _ h.isLimit

end TrivialBundleWithFiber

/-- Given `F : C`, this is the property of morphisms `p : E ⟶ B`
such that there exists a structure `TrivialBundleWithFiber F p`,
i.e. `E` identifies to the binary product of `B` and `F`. -/
def trivialBundlesWithFiber (F : C) : MorphismProperty C :=
  fun _ _ p ↦ Nonempty (TrivialBundleWithFiber F p)

instance (F : C) : (trivialBundlesWithFiber F).IsStableUnderBaseChange where
  of_isPullback sq h := ⟨h.some.pullback sq⟩

/-- In a category `C`, this is the property of morphisms which identify to
the projection from a binary product. -/
def trivialBundles : MorphismProperty C :=
  ⨆ F, trivialBundlesWithFiber F
deriving IsStableUnderBaseChange

lemma trivialBundlesWithFiber_le_trivialBundles (F : C) :
    trivialBundlesWithFiber F ≤ trivialBundles :=
  le_iSup _ _

lemma mem_trivialBundles_iff {X Y : C} (p : X ⟶ Y) :
    trivialBundles p ↔ ∃ F, Nonempty (TrivialBundleWithFiber F p) := by
  simp [trivialBundles]
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma trivialBundles.of_isPullback_of_fac {E E' B B' : C} {p' : E' ⟶ B'} {p : E ⟶ B}
    {f : B' ⟶ B} {f' : E' ⟶ E} (sq : IsPullback f' p' p f)
    {T : C} (hT : IsTerminal T) (a : B' ⟶ T) (b : T ⟶ B) (fac : a ≫ b = f)
    [HasPullback p b] :
    trivialBundles p' := by
  have sq :
      IsPullback (pullback.lift f' (p' ≫ a) (by simp [fac, sq.w])) p' (pullback.snd p b) a :=
    .of_right (by simpa [fac]) (by simp) (.of_hasPullback p b)
  refine MorphismProperty.of_isPullback sq ?_
  simp only [mem_trivialBundles_iff]
  exact ⟨_, ⟨TrivialBundleWithFiber.ofIsTerminal (pullback.snd p b) hT⟩⟩

instance (F : C) : (trivialBundlesWithFiber F).IsStableUnderBaseChange where
  of_isPullback {X₁ X₂ X₃ X₄ t f' f b} sq := by
    rintro ⟨hf⟩
    exact ⟨hf.pullback sq⟩

end MorphismProperty

end CategoryTheory
