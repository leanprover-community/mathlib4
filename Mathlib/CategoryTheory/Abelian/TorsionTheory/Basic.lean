/-
Copyright (c) 2026 Blake Farman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Blake Farman
-/
module
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.CategoryTheory.Subobject.WellPowered
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Torsion Theory

A **torsion theory** on an abelian category `C` is a pair of classes `T` and `F` of objects from `C`
such that `T` is the left orthogonal of `F` and `F` is the right orthogonal of `T`. We call `T`
the *torsion class* and its objects *torsion objects*.  We call `F` the *torsion-free class*
and its objects *torsion-free objects*.

## Main definitions

* `TorsionTheory C`: The type of a torsion theory on `C`.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category theory, preradical, torsion theory
-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory.Abelian

open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- In an abelian category, given a kernel `k` of `q` and a mono `m : B ⟶ Q`,
the short complex `K ⟶ pullback q m ⟶ B` (where the left leg is `pullback.lift k 0`
and the right leg is `pullback.snd`) is short exact.

This captures the general fact that pulling back an extension along a monomorphism
yields an extension. -/
lemma shortExact_pullbackSnd_of_isLimit_kernelFork
    {K X Q B : C} {k : K ⟶ X} {q : X ⟶ Q} {m : B ⟶ Q} [Mono m] [Epi q]
    (w : k ≫ q = 0) (hk : IsLimit (KernelFork.ofι k w)) [HasPullback q m] :
    (ShortComplex.mk (pullback.lift k 0 (by simp [w]))
      (pullback.snd q m) (pullback.lift_snd k 0 (by simp [w]))).ShortExact := by
  have w' : k ≫ q = 0 ≫ m := by simp [w]
  have hg_fst : pullback.lift k 0 (by simp [w]) ≫ pullback.fst q m = k :=
    pullback.lift_fst k 0 w'
  haveI : Mono (pullback.lift k 0 w') :=
    (mono_comp_iff_of_mono _ (pullback.fst q m)).mp
      (by simpa [hg_fst] using mono_of_isLimit_fork hk)
  exact {
    exact := by
      refine ShortComplex.exact_of_f_is_kernel _ ?_
      refine KernelFork.IsLimit.ofι' _ (pullback.lift_snd k 0 w') ?_
      intro A a ha
      have : (a ≫ pullback.fst q m) ≫ q = 0 := by
        simpa [Category.assoc' m (pullback.snd q m) a, ha, zero_comp] using
          congrArg (a ≫ ·) pullback.condition
      exact ⟨hk.lift (KernelFork.ofι (a ≫ pullback.fst q m) this), by
        apply (cancel_mono (pullback.fst q m)).mp
        simpa [Category.assoc, hg_fst] using
          hk.fac (KernelFork.ofι _ this) WalkingParallelPair.zero⟩
    mono_f := by infer_instance
    epi_g := by infer_instance
  }

/-- If `C` is locally small, well-powered, and has coproducts, then every object `X : C` has a
subobject with property `P` that is maximal amongst all such subobjects. -/
noncomputable
abbrev sSup (P : ObjectProperty C) (X : C)
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] :
    Subobject X :=
  CategoryTheory.Subobject.sSup {A : Subobject X | P (A : C)}

lemma le_sSup_of_prop (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C]
    {X' X : C} (i : X' ⟶ X) (hi : P (Abelian.image i)) :
    Subobject.mk (Abelian.image.ι i) ≤ sSup P X :=
  Subobject.le_sSup _ _
    (P.prop_of_iso (Subobject.underlyingIso (Abelian.image.ι i)).symm hi)

lemma sSup_prop (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C]
    (X : C) : P (sSup P X) :=
  P.prop_of_iso (Subobject.underlyingIso
    (Limits.image.ι (Subobject.smallCoproductDesc _))).symm
      (P.prop_of_epi (factorThruImage _)
        ((ObjectProperty.prop_colimit _ _ (fun ⟨j⟩ ↦ by
          dsimp
          obtain ⟨S, hS, hj⟩ := j.2
          simpa [← hj] using hS))))

lemma gc_rightOrthogonal_leftOrthogonal :
    GaloisConnection (OrderDual.toDual (α := ObjectProperty C) ∘ ObjectProperty.rightOrthogonal)
  (ObjectProperty.leftOrthogonal ∘ OrderDual.ofDual) :=
  fun _ _ ↦ ⟨fun h _ hX _ _ hY ↦ h _ hY _ hX, fun h _ hX _ _ hY ↦ h _ hY _ hX⟩

@[simp]
lemma leftOrthogonal_rightOrthogonal_leftOrthogonal_eq_leftOrthogonal (P : ObjectProperty C) :
    P.leftOrthogonal.rightOrthogonal.leftOrthogonal = P.leftOrthogonal := by
  simpa [Function.comp] using
    gc_rightOrthogonal_leftOrthogonal.u_l_u_eq_u (OrderDual.toDual P)

@[simp]
lemma leftOrthogonal_rightOrthogonal_leftOrthogonal_eq_rightOrthogonal (P : ObjectProperty C) :
    P.rightOrthogonal.leftOrthogonal.rightOrthogonal = P.rightOrthogonal := by
  simpa [Function.comp] using
    gc_rightOrthogonal_leftOrthogonal.l_u_l_eq_l (OrderDual.toDual P)

lemma le_rightOrthogonal_leftOrthogonal (P : ObjectProperty C) :
    P ≤ P.rightOrthogonal.leftOrthogonal := by
  simpa [Function.comp] using gc_rightOrthogonal_leftOrthogonal.le_u_l P

lemma le_leftOrthogonal_rightOrthogonal (P : ObjectProperty C) :
    P ≤ P.leftOrthogonal.rightOrthogonal := by
  simpa [Function.comp] using gc_rightOrthogonal_leftOrthogonal.l_u_le (OrderDual.toDual P)

/-- If `P` is closed under quotients, extensions, and coproducts, then for any `X`,
the cokernel of the maximal `P`-subobject's arrow is `P.rightOrthogonal`. -/
lemma rightOrthogonal_cokernel_sSup (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C]
    (X : C) : P.rightOrthogonal (cokernel (sSup P X).arrow) := by
  let Y : Subobject X := sSup P X
  rw [ObjectProperty.rightOrthogonal_iff]
  intro Z f hPZ
  let A := pullback (cokernel.π Y.arrow) (Abelian.image.ι f)
  let i := pullback.fst (cokernel.π Y.arrow) (Abelian.image.ι f)
  let p := pullback.snd (cokernel.π Y.arrow) (Abelian.image.ι f)
  have hSES : (ShortComplex.mk
      (pullback.lift Y.arrow 0 (by simp) : (Y : C) ⟶ A) p
      (pullback.lift_snd Y.arrow 0 (by simp))).ShortExact :=
    let s : ShortComplex C := ShortComplex.cokernelSequence Y.arrow
    have hs: s.ShortExact := {
      exact := ShortComplex.cokernelSequence_exact _
      mono_f := by dsimp [s]; infer_instance
      epi_g := inferInstance}
    shortExact_pullbackSnd_of_isLimit_kernelFork (cokernel.condition Y.arrow)
      hs.fIsKernel
  have hPimi : P (Abelian.image i) :=
    P.prop_of_epi (Abelian.factorThruImage i) --hPA
      ((ObjectProperty.prop_X₂_of_shortExact P hSES (sSup_prop P X)
          (P.prop_of_epi (Abelian.factorThruImage f) hPZ)))
  have himg_le_Y : Subobject.mk (Abelian.image.ι i) ≤ Y :=
    le_sSup_of_prop P i hPimi
  let g' : Abelian.image i ⟶ (Y : C) := Subobject.ofMkLE (Abelian.image.ι i) Y himg_le_Y
  have hg' : g' ≫ Y.arrow = image.ι i := Subobject.ofMkLE_arrow himg_le_Y
  have hi_cokernel : i ≫ cokernel.π Y.arrow = 0 := by
    simp [← Abelian.image.fac i, ← hg']
  have hp : p = 0 := by
    rw [← cancel_mono (Abelian.image.ι f), zero_comp, ← pullback.condition, hi_cokernel]
  have himf_zero : Abelian.image.ι f = 0 :=
    IsZero.eq_zero_of_src (IsZero.of_epi_eq_zero p hp) (Abelian.image.ι f)
  simp [← Abelian.image.fac f, himf_zero]

lemma rightOrthogonal_leftOrthogonal_le (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] :
    P.rightOrthogonal.leftOrthogonal ≤ P :=
  fun X hX ↦
    haveI : Epi (sSup P X).arrow :=
      Preadditive.epi_of_cokernel_zero (hX (cokernel.π _) (rightOrthogonal_cokernel_sSup P X))
    P.prop_of_epi (sSup P X).arrow (sSup_prop P X)

/-- If an object property `P` in an abelian category is closed under quotients, extensions,
and coproducts, then `P = P.rightOrthogonal.leftOrthogonal`. -/
theorem eq_rightOrthogonal_leftOrthogonal (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] :
    P = P.rightOrthogonal.leftOrthogonal := by
  exact le_antisymm (le_rightOrthogonal_leftOrthogonal P) (rightOrthogonal_leftOrthogonal_le P)

/-- The left orthogonal of property `P` is closed under quotients. -/
instance (P : ObjectProperty C) : (P.leftOrthogonal).IsClosedUnderQuotients where
  prop_of_epi :=
    fun f _ hX ↦
      (ObjectProperty.leftOrthogonal_iff P _).mpr
        fun _ g hZ ↦ Limits.zero_of_epi_comp f (hX (f ≫ g) hZ)

/-- The left orthogonal of property `P` is closed under extensions. -/
instance (P : ObjectProperty C) : (P.leftOrthogonal).IsClosedUnderExtensions where
  prop_X₂_of_shortExact := by
    intro s hs hX₁ hX₃ Z k hZ
    let t : Limits.CokernelCofork s.f :=
      Limits.CokernelCofork.ofπ k (hX₁ (s.f ≫ k) hZ)
    let l : s.X₃ ⟶ Z := hs.gIsCokernel.desc t
    have hl : l = 0 := hX₃ l hZ
    have hfac : s.g ≫ l = k :=
      hs.gIsCokernel.fac t Limits.WalkingParallelPair.one
    simp [← hfac, hl]

/-- The left orthogonal of property `P` is closed under colimits. -/
instance (P : ObjectProperty C) {J : Type u'} [Category.{v'} J] :
    ObjectProperty.IsClosedUnderColimitsOfShape (P.leftOrthogonal) J where
  colimitsOfShape_le := by
    intro X ⟨hX⟩ Y f hY
    apply hX.isColimit.hom_ext
    intro j
    simpa [comp_zero] using (hX.prop_diag_obj j) (hX.ι.app j ≫ f) hY

/-- A Torsion Theory in an abelian category consists of two classes, `T` and `F`, of
torsion and torsion-free objects, respectively, such that `T` is the left orthogonal
of `F` and `F` is the right orthogonal of `T`. -/
structure TorsionTheory (T F : ObjectProperty C) : Prop where
  torsion_eq_leftOrthogonal : T = F.leftOrthogonal
  free_eq_rightOrthogonal : F = T.rightOrthogonal

namespace TorsionTheory

/- lemma mem_torsion_iff {X : C} {T F : ObjectProperty C} (hTF : TorsionTheory T F) :
    T X ↔ F.leftOrthogonal X := by
  simp [hTF.torsion_eq_leftOrthogonal]

lemma mem_free_iff {X : C} (T F : ObjectProperty C) (hTF : TorsionTheory T F) :
    F X ↔ T.rightOrthogonal X := by
  simp [hTF.free_eq_rightOrthogonal] -/

example (T F : ObjectProperty C) (hTF : TorsionTheory T F) (X : C) :
    T X ↔ (∀ {Y : C}, ∀ f : X ⟶ Y, F Y → f = 0) := by
  simpa [hTF.torsion_eq_leftOrthogonal] using ObjectProperty.leftOrthogonal_iff F X

example (T F : ObjectProperty C) (hTF : TorsionTheory T F) (Y : C) :
    F Y ↔  (∀ {X : C}, ∀ f : X ⟶ Y, T X → f = 0) := by
  simpa [hTF.free_eq_rightOrthogonal] using ObjectProperty.rightOrthogonal_iff T Y

lemma torsionTheoryGeneratedBy (P : ObjectProperty C) :
    TorsionTheory P.rightOrthogonal.leftOrthogonal P.rightOrthogonal where
      torsion_eq_leftOrthogonal := rfl
      free_eq_rightOrthogonal := by simp

lemma torsionTheoryCogeneratedBy (P : ObjectProperty C) :
    TorsionTheory P.leftOrthogonal P.leftOrthogonal.rightOrthogonal where
      torsion_eq_leftOrthogonal := by simp
      free_eq_rightOrthogonal := rfl

-- I think these will likely get removed once things are cleand up.
lemma isClosedUnderQuotients_of_torsionTheory {T F : ObjectProperty C} (hTF : TorsionTheory T F) :
    T.IsClosedUnderQuotients := by
  rw [hTF.torsion_eq_leftOrthogonal]
  infer_instance

lemma isClosedUnderExtensions_of_torsionTheory {T F : ObjectProperty C} (hTF : TorsionTheory T F) :
    T.IsClosedUnderExtensions := by
  rw [hTF.torsion_eq_leftOrthogonal]
  infer_instance

lemma isClosedUnderCoproducts_of_torsionTheory {T F : ObjectProperty C} (hTF : TorsionTheory T F) :
    ∀ {J : Type w}, T.IsClosedUnderColimitsOfShape (Discrete J) := by
  intro J
  rw [hTF.torsion_eq_leftOrthogonal]
  infer_instance

example (P : ObjectProperty C) [P.IsClosedUnderQuotients] {X Y : C} (hX : P X) (f : X ⟶ Y) :
    P (image f) :=
  ObjectProperty.IsClosedUnderQuotients.prop_of_epi (factorThruImage f) hX

theorem isTorsionClass_iff {P : ObjectProperty C} [LocallySmall.{w} C] [WellPowered.{w} C]
    [HasCoproducts.{w} C] : (∃ F : ObjectProperty C, TorsionTheory P F) ↔
    (P.IsClosedUnderQuotients ∧ P.IsClosedUnderExtensions ∧
    ∀ {J : Type w}, P.IsClosedUnderColimitsOfShape (Discrete J)) := by
  refine ⟨fun ⟨F, hPF⟩ ↦ ⟨hPF.torsion_eq_leftOrthogonal ▸ inferInstance,
      hPF.torsion_eq_leftOrthogonal ▸ inferInstance,
      hPF.torsion_eq_leftOrthogonal ▸ inferInstance⟩, ?_⟩
  rintro ⟨hquot, hext, hcoprod⟩
  exact ⟨P.rightOrthogonal,
    { torsion_eq_leftOrthogonal := eq_rightOrthogonal_leftOrthogonal P,
      free_eq_rightOrthogonal := rfl }⟩

end TorsionTheory

end CategoryTheory.Abelian
