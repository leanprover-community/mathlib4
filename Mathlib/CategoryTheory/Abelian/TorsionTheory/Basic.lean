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
public import Mathlib.CategoryTheory.Subobject.Limits

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

section GaloisConnection
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
end GaloisConnection

section PullbackCokernel
variable {X : C} {A : Subobject X} (B : Subobject (cokernel A.arrow))

/-- For `A : Subobject X`, the pullback of `B : Subobject (cokernel A.arrow)` is a subobject of `X`
that contains `A`. -/
lemma le_pullback_cokernel_π :
     A ≤ (Subobject.pullback (cokernel.π A.arrow)).obj B := by
  let g : (A : C) ⟶ ((Subobject.pullback (cokernel.π A.arrow)).obj B : C) :=
    (Subobject.isPullback (cokernel.π A.arrow) B).lift 0 A.arrow (by simp)
  have w : g ≫ ((Subobject.pullback (cokernel.π A.arrow)).obj B).arrow = A.arrow :=
    (Subobject.isPullback (cokernel.π A.arrow) B).lift_snd 0 A.arrow (by simp)
  haveI : Mono g :=
    (mono_comp_iff_of_mono _ ((Subobject.pullback (cokernel.π A.arrow)).obj B).arrow).mp
      (by rw [w]; infer_instance)
  exact Subobject.le_of_comm g w

/-- Given a subobject `A` of `X` and a subobject `B` of the cokernel of `A.arrow`, the canonical
inclusion of `A` into the pullback `A' = (Subobject.pullback (cokernel.π A.arrow)).obj B`
is a kernel fork for `Subobject.pullbackπ (cokernel.π A.arrow) B`. -/
noncomputable
def kernelForkPullbackπCokernelπ :
    KernelFork (Subobject.pullbackπ (cokernel.π A.arrow) B) := by
  let A' := (Subobject.pullback (cokernel.π A.arrow)).obj B
  let g : (A : C) ⟶ (A' : C) := (Subobject.ofLE A _ (le_pullback_cokernel_π B))
  let p := cokernel.π A.arrow
  refine KernelFork.ofι g ?_
  apply (cancel_mono B.arrow).mp
  calc
    _ = g ≫ ((Subobject.pullback p).obj B).arrow ≫ p := by
      rw [Category.assoc, (Subobject.isPullback p B).toCommSq.w]
    _ = A.arrow ≫ p := by
      rw [← Category.assoc, Subobject.ofLE_arrow (le_pullback_cokernel_π B)]
    _ = 0 ≫ B.arrow := by
      rw [zero_comp, cokernel.condition A.arrow]

/-- `kernelFork_pullbackπ_cokernel_π A B` is a limit cone. -/
noncomputable
def isLimit_kernelFork_pullbackπ_cokernel_π : IsLimit (kernelForkPullbackπCokernelπ B) := by
  let A' := (Subobject.pullback (cokernel.π A.arrow)).obj B
  let i : (A : C) ⟶ (A' : C) := (Subobject.ofLE A _ (le_pullback_cokernel_π B))
  let hPB := (Subobject.isPullback (cokernel.π A.arrow) B)
  have hA := Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ (cokernel.π A.arrow) (cokernel.condition A.arrow))
      (cokernelIsCokernel A.arrow)
  apply KernelFork.IsLimit.ofι' i (kernelForkPullbackπCokernelπ B).condition
  intro Z f hf
  let s : KernelFork (cokernel.π A.arrow) := KernelFork.ofι (f ≫ A'.arrow)
    (by rw [Category.assoc, ← hPB.toCommSq.w, ← Category.assoc, hf, zero_comp])
  refine ⟨hA.lift s, ?_⟩
  apply (cancel_mono A'.arrow).mp
  rw [Category.assoc, Subobject.ofLE_arrow (le_pullback_cokernel_π B)]
  exact hA.fac s WalkingParallelPair.zero

/-- Given a subobject `A` of `X` and a subobject `B` of `cokernel A.arrow`, the short complex
`A ⟶ (Subobject.pullback (cokernel.π A.arrow)).obj B ⟶ B` with first map induced by
`A.arrow ≫ cokernel.π A.arrow = 0 ≫ B.arrow` and second map `Subobject.pullbackπ`. -/
noncomputable
def shortComplexPullbackπCokernelπ : ShortComplex C :=
  ShortComplex.mk
    (Subobject.ofLE A _ (le_pullback_cokernel_π B))
    (Subobject.pullbackπ (cokernel.π A.arrow) B)
    (kernelForkPullbackπCokernelπ B).condition

lemma shortExact_shortComplexPullbackπCokernelπ :
    ShortComplex.ShortExact (shortComplexPullbackπCokernelπ B) := by
  refine {
    exact := by
      refine ShortComplex.exact_of_f_is_kernel _ ?_
      simpa [shortComplexPullbackπCokernelπ, kernelForkPullbackπCokernelπ] using
        isLimit_kernelFork_pullbackπ_cokernel_π B
    mono_f := by change Mono (Subobject.ofLE A _ (le_pullback_cokernel_π B)); infer_instance
    epi_g := by
      simpa [(Subobject.isPullback (cokernel.π A.arrow) B).isoPullback_hom_fst] using
        epi_comp
          (Subobject.isPullback (cokernel.π A.arrow) B).isoPullback.hom
          (pullback.fst B.arrow (cokernel.π A.arrow))
  }
end PullbackCokernel

lemma le_sSup_of_prop (P : ObjectProperty C)
    [P.IsClosedUnderIsomorphisms]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C]
    {X' X : C} (i : X' ⟶ X) (hi : P (Abelian.image i)) :
    Subobject.mk (Abelian.image.ι i) ≤ Subobject.sSup {A : Subobject X | P (A : C)} :=
  Subobject.le_sSup _ _
    (P.prop_of_iso (Subobject.underlyingIso (Abelian.image.ι i)).symm hi)

lemma sSup_prop (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C]
    (X : C) : P (CategoryTheory.Subobject.sSup {A : Subobject X | P (A : C)}) :=
  P.prop_of_iso (Subobject.underlyingIso
    (Limits.image.ι (Subobject.smallCoproductDesc _))).symm
      (P.prop_of_epi (factorThruImage _)
        ((ObjectProperty.prop_colimit _ _ (fun ⟨j⟩ ↦ by
          dsimp
          obtain ⟨S, hS, hj⟩ := j.2
          simpa [← hj] using hS))))

/-- If `P` is closed under quotients, extensions, and coproducts, then for any `X`,
the cokernel of the maximal `P`-subobject's arrow is `P.rightOrthogonal`. -/
lemma rightOrthogonal_cokernel_sSup (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C]
    (X : C) :
    P.rightOrthogonal (cokernel (Subobject.sSup {A : Subobject X | P (A : C)}).arrow) := by
  let A := CategoryTheory.Subobject.sSup {A : Subobject X | P (A : C)}
  rw [ObjectProperty.rightOrthogonal_iff]
  intro Z f hPZ
  let B := Subobject.mk (Abelian.image.ι f)
  let A':= ((Subobject.pullback
    (cokernel.π (Subobject.sSup {A : Subobject X | P (A : C)}).arrow))).obj B
  haveI : Epi (Subobject.pullbackπ (cokernel.π A.arrow) B) := by
    simpa [(Subobject.isPullback (cokernel.π A.arrow) B).isoPullback_hom_fst] using
      epi_comp (Subobject.isPullback (cokernel.π A.arrow) B).isoPullback.hom
        (pullback.fst B.arrow (cokernel.π A.arrow))
  have hSES := shortExact_shortComplexPullbackπCokernelπ B
  let f' : (A' : C) ⟶ A :=
    Subobject.ofLE _ _
      (Subobject.le_sSup {A | P (Subobject.underlying.obj A)} A'
        (P.prop_X₂_of_shortExact hSES (sSup_prop P X)
          (P.prop_of_iso
            (Subobject.underlyingIso (Abelian.image.ι f)).symm
              (P.prop_of_epi (Abelian.factorThruImage f) hPZ))))
  have hf' : f' ≫ A.arrow = A'.arrow := Subobject.ofLE_arrow _
  have hzero : A'.arrow ≫ cokernel.π (A.arrow) = 0 := by
    simp [← hf']
  have hpullbackπ : (Subobject.pullbackπ (cokernel.π A.arrow) B) = 0 := by
    apply (cancel_mono B.arrow).mp
    rw [(Subobject.isPullback (cokernel.π A.arrow) B).toCommSq.w, hzero, zero_comp]
  have himf: IsZero (Abelian.image f) :=
    IsZero.of_iso (IsZero.of_epi_eq_zero (Subobject.pullbackπ (cokernel.π A.arrow) B) hpullbackπ)
      (id (Subobject.underlyingIso (Abelian.image.ι f)).symm)
  simp [← Abelian.image.fac f, IsZero.eq_zero_of_src himf]

lemma rightOrthogonal_leftOrthogonal_le (P : ObjectProperty C)
    [P.IsClosedUnderQuotients] [P.IsClosedUnderExtensions]
    [∀ J : Type w, P.IsClosedUnderColimitsOfShape (Discrete J)]
    [LocallySmall.{w} C] [WellPowered.{w} C] [HasCoproducts.{w} C] :
    P.rightOrthogonal.leftOrthogonal ≤ P :=
  fun X hX ↦
    haveI : Epi (Subobject.sSup {A : Subobject X | P (A : C)}).arrow :=
      Preadditive.epi_of_cokernel_zero (hX (cokernel.π _) (rightOrthogonal_cokernel_sSup P X))
    P.prop_of_epi (Subobject.sSup {A : Subobject X | P (A : C)}).arrow (sSup_prop P X)

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
