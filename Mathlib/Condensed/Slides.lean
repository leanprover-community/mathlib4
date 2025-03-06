import Mathlib.Condensed.Defence

set_option pp.funBinderTypes true
set_option pp.universes false
set_option linter.unusedVariables false

noncomputable section

universe u

open CategoryTheory Functor Condensed Limits Monoidal MonoidalCategory MonoidalClosed


















/-!

# Towards a formalized theory of solid modules

Dagur Asgeirsson

PhD defence, University of Copenhagen, March 7th 2025

-/



















/-!

# Introduction

* What you're looking at is a Lean file that I've created with the
  goal to illustrate the main results of my PhD thesis.

* We are inside Mathlib, which is a unified library of formalized
  mathematics written in Lean.

* It strives to formalize everything in the highest generality
  possible.

* The goal of my research has been to formalize condensed
  mathematics *for mathlib*, to eventually establish a formalized
  theory of solid abelian groups / modules.

-/


















/-!

# Background

* Condensed mathematics is a convenient framework for mixing
  topology and algebra.

* Say we want to study algebraic objects with a topology, e.g.
  topological abelian groups, vector spaces, etc.

* Problem: `TopAb` is not a nice category (it's not **abelian**).

* Solution: Introduce **condensed abelian groups**.

-/


















section CondAb

/-

# Condensed abelian groups

Condensed abelian groups form an abelian category satisfying
Grothendieck's axioms AB3, AB3*, AB4, AB4*, AB5 (and AB6, which
has not been implemented in mathlib).

-/

#check CondensedAb.{u}

#synth Category CondensedAb.{u}

#synth Abelian CondensedAb.{u}

#synth HasColimits CondensedAb.{u}

#synth HasLimits CondensedAb.{u}

#synth AB4 CondensedAb.{u}

#synth AB4Star CondensedAb.{u}

#synth AB5 CondensedAb.{u}

end CondAb

















/-!

# Solid abelian groups

* Condensed abelian groups are defined as sheaves on a
  certain site of compact Hausdorff spaces, e.g. profinite
  sets w/ jointly surjective finite families as covers.

* `CondensedAb` has a closed symmetric monoidal structure.

* We "tame" the tensor product using a process called
  **solidification**.

* For a profinite set `S = lim Sᵢ`, let `ℤ[S]◾ := lim ℤ[Sᵢ]`.
  A condensed abelian group `M` is **solid** if for every
  `S ⟶ M`, the canonical map `ℤ[S] ⟶ ℤ[S]◾` lifts uniquely.

* To get the solid theory off the ground, it is important
  to show that the generators `ℤ[S]◾` can be written as products
  of copies of the discrete condensed abelian group `ℤ`.

-/



















section Paper2

/-

# Paper 2: Categorical foundations of formalized condensed mathematics

Joint with: R. Brasca, N. Kuhn, F. A. E. Nuccio, A. Topaz

Let's first back up a bit and see how to implement condensed objects in
full mathlib generality:

-/

section CoherentTopology

/-
Condensed sets are defined in mathlib as sheaves for the "coherent
topology" on the category of compact Hausdorff spaces.
-/
example : CondensedSet.{u} =
  Sheaf (coherentTopology CompHaus.{u}) (Type (u+1)) := rfl


#check coherentTopology
#check coherentTopology.mem_sieves_iff_hasEffectiveEpiFamily
#check Precoherent
#check Precoherent.pullback

end CoherentTopology

















section Equivalence

/-
Condensed sets can equivalently be defined as sheaves for the
coherent topology on the category of profinite sets or Stonean
spaces (extremally disconnected compact Hausdorff spaces).
-/

example : CondensedSet.{u} ≌
    Sheaf (coherentTopology Profinite.{u}) (Type (u+1)) :=
  (coherentTopology.equivalence profiniteToCompHaus _).symm

example : CondensedSet.{u} ≌
    Sheaf (coherentTopology Stonean.{u}) (Type (u+1)) :=
  (coherentTopology.equivalence Stonean.toCompHaus _).symm

/-
The abstract equivalence of categories that the above
equivalences come from.
-/
#check coherentTopology.equivalence

end Equivalence



















section Explicit

variable (X : CompHaus.{u}ᵒᵖ ⥤ Type (u+1))

open Presheaf regularTopology

/-
The explicit sheaf condition for condensed sets on `CompHaus`
(the same holds for `Profinite`)

The property `EqualizerCondition F` says that for any
effective epi `X ⟶ B` (continuous surjection),
the diagram `F(B) → F(X) ⇉ F(X ×_B X)` is an equalizer.
-/
example : IsSheaf (coherentTopology CompHaus) X ↔
    PreservesFiniteProducts X ∧ EqualizerCondition X :=
  isSheaf_iff_preservesFiniteProducts_and_equalizerCondition X

#check isSheaf_iff_preservesFiniteProducts_and_equalizerCondition

section

example : EqualizerCondition X ↔
    ∀ {S T} (π : S ⟶ T) [EffectiveEpi π] (c : PullbackCone π π)
      (_ : IsLimit c), Nonempty
        (IsLimit (Fork.ofι (X.map π.op) (equalizerCondition_w X c))) :=
  Iff.rfl

#check equalizerCondition_w
#check Fork.ofι

end




















variable (Y : Stonean.{u}ᵒᵖ ⥤ Type (u+1))

/-
The explicit sheaf condition for condensed sets on `Stonean`
-/
example :
    IsSheaf (coherentTopology Stonean) Y ↔ PreservesFiniteProducts Y :=
  isSheaf_iff_preservesFiniteProducts_of_projective Y

#check isSheaf_iff_preservesFiniteProducts_of_projective

end Explicit

end Paper2




















section Paper1

/-

# Paper 1: A formal proof of Nöbeling's theorem

An important result about the structure of the abelian group
of continuous maps (locally constant maps) from a profinite
set `S` to `ℤ`.

This is key to the development of the solid
theory, but the statement and proof have nothing to do with
condensed mathematics proper.

-/

variable (S : Profinite.{0})

/-
Nöbeling's theorem: the abelian group of continuous maps from
a profinite set `S` to `ℤ` is free (`LocallyConstant S ℤ` is an
implementation detail to avoid introducing the discrete topology
on `ℤ`).
-/
instance : Module.Free ℤ (LocallyConstant S ℤ) := LocallyConstant.freeOfProfinite S

/-
We need a slightly modified version,
lifting the ring `ℤ` to a higher universe.
-/
instance : Module.Free (ULift.{1} ℤ) (ULift (LocallyConstant S ℤ)) := by
  apply (config := {allowSynthFailures := true}) Module.Free.ulift
  let e : ℤ ≃+* (ULift.{1} ℤ) := ULift.ringEquiv.symm
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.of_ringEquiv e.symm
  exact Module.Free.of_ringEquiv (M := LocallyConstant S ℤ) e {
    toLinearMap := ⟨⟨id, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩
    invFun := id
    left_inv := congrFun rfl
    right_inv := congrFun rfl }


















section Coproduct

/-
In other words, there exists a set `I` such that `LocallyConstant S ℤ`
is a direct sum (i.e. coproduct) of `I` copies of `ℤ`.

The following is the Lean way to say this,
define a cofan (cocone on a discrete diagram) and
prove that it is a colimit:
-/

def index : Type 1 := Module.Free.ChooseBasisIndex
  (ULift.{1} ℤ) (ULift.{1} (LocallyConstant S ℤ))

def freeCofan : Cofan (fun i : index S ↦
    ModuleCat.of (ULift.{1} ℤ) (ULift.{1} ℤ)) where
  pt := ModuleCat.of (ULift.{1} ℤ) (ULift.{1} (LocallyConstant S ℤ))
  ι := sorry

def isColimitFreeCofan : IsColimit (freeCofan S) := sorry

/-
The sorries above are just some missing API for categories of modules.
-/

end Coproduct

end Paper1



















section Paper3

/-

# Paper 3: A formal characterization of discrete condensed objects

Condensed sets are suppposed to generalize topology,
and so we need a sensible way to talk about discreteness.

This paper characterizes discrete condensed objects in
various ways, important for the development of the solid theory.

-/

























#check CondensedMod.isDiscrete_tfae

variable (M : CondensedAb)

/-
Notation for the functor mapping an abelian
group to the corresponding discrete abelian group
-/
notation3 "δ" => discrete (ModuleCat (ULift.{1} ℤ))

/-
Being discrete is equivalent to the counit inducing an
isomorphism `δ M(*) ⟶ M`.
-/
def isoUnderlyingOfDiscrete [M.IsDiscrete] :
    M ≅ (δ).obj (M.val.obj (*)) :=
  haveI : IsIso ((discreteUnderlyingAdj _).counit.app M) := by
    rwa [((CondensedMod.isDiscrete_tfae _ M).out 1 0:)]
  (asIso ((discreteUnderlyingAdj _).counit.app _)).symm



















variable (S : Profinite)

def discreteCocone :
    Cocone (S.diagram.op ⋙ profiniteToCompHaus.op ⋙ M.val) :=
  (profiniteToCompHaus.op ⋙ M.val).mapCocone S.asLimitCone.op

#check S.diagram
#check profiniteToCompHaus
#check M.val

/-
This is the Lean way of saying:
`M` is discrete if and only if for every profinite set
`S = limᵢSᵢ`, the canonical map
`colimᵢX(Sᵢ) ⟶ X(S)` is an isomorphism.
-/
lemma discreteness_characterization : M.IsDiscrete ↔
    ∀ S, Nonempty (IsColimit (discreteCocone M S)) :=
  (CondensedMod.isDiscrete_tfae _ M).out 0 6

section

/-
In fact, the discreteness characterization has an internal version.
-/

def discreteInternalCocone :
    Cocone (S.diagram.op ⋙ (profiniteFree _).op ⋙ (internalHom.flip.obj M)) :=
  ((profiniteFree _).op ⋙ (internalHom.flip.obj M)).mapCocone S.asLimitCone.op

def isColimitDiscreteInternal [M.IsDiscrete] :
  IsColimit (discreteInternalCocone M S) := sorry

end

end Paper3




















section Application

/-

We give an outline of the promised isomorphism `ℤ[S]◾ ≅ ∏ ℤ`.

More precisely, we reduce the definition of an isomorphism
`ℤ[S]◾ ≅ ∏ᶜ (fun i : index S ↦ of ℤ)` to a few "sorries"

These sorries are not trivial, but the hard work of proving
Nöbeling's theorem and the discreteness characterization is done.

-/















open CondensedAb

variable  (S : Profinite.{0})

section

variable (M : CondensedAb)

example : M.IsSolid ↔ ∀ S : Profinite,
    IsIso ((yoneda.obj M).map (ε S : ℤ[S] ⟶ ℤ[S]◾).op) :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

variable (S : Profinite.{0})

example : ℤ[S]◾ ≅
  (rightKanExtension
    FintypeCat.toProfinite
    (finFree (ULift.{1} ℤ))).obj S := Iso.refl _

def solidIso : ℤ[S]◾ ≅ limit (S.diagram ⋙ profiniteFree (ULift.{1} ℤ)) :=
  haveI : Initial <| Profinite.Extend.functor S.asLimitCone :=
    Profinite.Extend.functor_initial S.asLimitCone S.asLimit
  (profiniteSolidIsPointwiseRightKanExtension _ _).isoLimit ≪≫
    (Initial.limitIso (Profinite.Extend.functor S.asLimitCone)
      (S.fintypeDiagram' ⋙ finFree (ULift ℤ))).symm

end



















section

/-
This is the key observation, and can be proved using the
discreteness characterization from paper 3, and a bit
of abstract nonsense.
-/
instance : (ℤ[S] ⟶[CondensedAb] of ℤ).IsDiscrete := by sorry

def isoInternalLocConst : (ℤ[S] ⟶[CondensedAb] of ℤ) ≅ of (LocallyConstant S ℤ) :=
  let i : (ℤ[S] ⟶[CondensedAb] of ℤ).val.obj (*) ≅
    ModuleCat.of (ULift ℤ) (ULift (LocallyConstant S ℤ)) := sorry
  (isoUnderlyingOfDiscrete _) ≪≫ (δ).mapIso i


def internalHomIntIso : (of ℤ ⟶[CondensedAb] of ℤ) ≅ of ℤ := sorry

end



















section

/-
`internalHom.flip.obj X` is the functor `(_ ⟶[CondensedAb] X)`
(internal hom into the condensed abelian group `X`). This functor
preserves limits in any closed monoidal category (it's a
contravariant functor, so "preserving limits" means taking colimits
to limits).
-/
instance (X : CondensedAb) :
    PreservesLimits (internalHom.flip.obj X) :=
  sorry -- missing API

instance (X : CondensedAb) :
    PreservesLimitsOfSize.{0, 0} (internalHom.flip.obj X) :=
  sorry -- missing API

def locallyConstantCocone :
    Cocone (S.diagram.op ⋙ profiniteToCompHaus.op ⋙
      ((CondensedMod.LocallyConstant.functor (ULift.{1} ℤ)).obj
        (ModuleCat.of _ (ULift.{1} ℤ))).val) := discreteCocone
          ((CondensedMod.LocallyConstant.functor (ULift.{1} ℤ)).obj
            (ModuleCat.of _ (ULift.{1} ℤ))) S

def isColimitLocallyConstantCocone : IsColimit (locallyConstantCocone S) := by
  have : ((CondensedMod.LocallyConstant.functor (ULift.{1} ℤ)).obj
      (ModuleCat.of _ (ULift.{1} ℤ))).IsDiscrete := by
    rw [((CondensedMod.isDiscrete_tfae (ULift.{1} ℤ) _).out 0 3:)]
    exact
      obj_mem_essImage (CondensedMod.LocallyConstant.functor (ULift ℤ))
        (ModuleCat.of (ULift ℤ) (ULift ℤ))
  rw [discreteness_characterization] at this
  exact (this S).some

def isoAux : (δ).obj (locallyConstantCocone S).pt ≅ of (LocallyConstant S ℤ) := by
  refine (δ).mapIso ?_
  refine LinearEquiv.toModuleIso ?_
  refine {
    toLinearMap := ⟨⟨fun x ↦ ⟨fun s ↦ (x s).down, ?_⟩, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩
    invFun := fun x ↦ ⟨fun s ↦ x.down s, ?_⟩
    left_inv := congrFun rfl
    right_inv := congrFun rfl }
  · intro U
    let U' : Set (ULift.{1} ℤ) := ULift.up '' U
    convert x.2 U' using 1
    ext s
    simp only [Cone.op_pt, Set.mem_preimage, LocallyConstant.toFun_eq_coe, Set.mem_image, U']
    refine ⟨fun h ↦ ⟨(x s).down, h, rfl⟩, fun h ↦ ?_⟩
    obtain ⟨y, hy⟩ := h
    rw [← hy.2]
    exact hy.1
  · intro U
    let U' : Set ℤ := ULift.down '' U
    convert x.down.2 U' using 1
    ext s
    simp [U']
    rfl

example : of (LocallyConstant S ℤ) = (δ).obj (ModuleCat.of (ULift.{1} ℤ)
    (ULift.{1} (LocallyConstant S ℤ))) := rfl

end



section

/-
The strategy is to prove that `ℤ[S]◾` and `∏ ℤ` are both
isomorphic to `(ℤ[S] ⟶[CondensedAb] ℤ) ⟶[CondensedAb] ℤ`
(where `⟶[CondensedAb]` denotes the internal hom in
condensed abelian groups).
-/

def iso₁ : ℤ[S]◾ ≅ ((ℤ[S] ⟶[CondensedAb] (of ℤ)) ⟶[CondensedAb] of ℤ) := by
  refine solidIso _ ≪≫ ?_
  change _ ≅ (internalHom.flip.obj _).obj _
  refine ?_ ≪≫ (internalHom.flip.obj _).mapIso (isoInternalLocConst _).op
  refine ?_ ≪≫ (internalHom.flip.obj _).mapIso (isoAux S).symm.op
  have : (δ).IsLeftAdjoint := (discreteUnderlyingAdj _).isLeftAdjoint
  let h : IsColimit ((δ).mapCocone (locallyConstantCocone S)) := by
    apply isColimitOfPreserves
    exact isColimitLocallyConstantCocone S
  let hh : IsLimit ((internalHom.flip.obj (of ℤ)).mapCone
      ((δ).mapCocone (locallyConstantCocone S)).op) := by
    apply isLimitOfPreserves
    exact h.op
  refine ?_ ≪≫ (limit.isLimit _).conePointUniqueUpToIso hh
  dsimp
  let e : ((DiscreteQuotient S)ᵒᵖ)ᵒᵖ ≌ DiscreteQuotient S :=
    opOpEquivalence (DiscreteQuotient _)
  refine ?_ ≪≫ (Functor.Initial.limitIso e.inverse _)
  refine lim.mapIso ?_
  let F := ((CondensedMod.LocallyConstant.functor (ULift.{1} ℤ)).obj
        (ModuleCat.of _ (ULift.{1} ℤ))).val
  let i : e.inverse ⋙ (S.diagram.op ⋙ profiniteToCompHaus.op ⋙ F ⋙ (δ)).op ⋙
      internalHom.flip.obj (of ℤ) ≅
      S.diagram ⋙ profiniteToCompHaus ⋙ F.rightOp ⋙ (δ).op
        ⋙ internalHom.flip.obj (of ℤ) := Iso.refl _
  refine ?_ ≪≫ i.symm
  change (S.fintypeDiagram ⋙ _) ⋙ _ ≅ (S.fintypeDiagram ⋙ _) ⋙ _
  refine Functor.associator _ _ _ ≪≫ ?_ ≪≫ (Functor.associator _ _ _).symm
  refine isoWhiskerLeft S.fintypeDiagram ?_
  refine NatIso.ofComponents (fun X ↦ ?_) sorry
  dsimp [e]
  change ℤ[FintypeCat.toProfinite.obj X] ≅
    (_ ⟶[CondensedAb] of ℤ)
  refine ?_ ≪≫ (internalHom.flip.obj _).mapIso (isoAux _).op
  change _ ≅ (of (LocallyConstant (FintypeCat.toProfinite.obj X) _))
      ⟶[CondensedAb] (of ℤ)
  sorry
/-!
We're reduced to showing that the free condensed abelian group on a
finite set `X` is isomorphic to the internal hom
`(LocallyConstant X ℤ) ⟶[CondensedAb] ℤ`,
naturally in `X`.
-/


def iso₂ : ((ℤ[S] ⟶[CondensedAb] (of ℤ)) ⟶[CondensedAb] of ℤ) ≅
    ∏ᶜ (fun i : index S ↦ of ℤ) := by
  refine (internalHom.mapIso (isoInternalLocConst S).op).symm.app _ ≪≫ ?_
  change (((δ).mapCocone (freeCofan S)).pt ⟶[CondensedAb] _) ≅ _
  change ((internalHom.flip.obj _).mapCone
    ((δ).mapCocone (freeCofan S)).op).pt ≅ _
  have : (δ).IsLeftAdjoint :=
    (discreteUnderlyingAdj _).isLeftAdjoint
  let h : IsColimit ((δ).mapCocone (freeCofan S)) := by
    apply isColimitOfPreserves
    exact isColimitFreeCofan S
  let hh : IsLimit ((internalHom.flip.obj (of ℤ)).mapCone
      ((discrete (ModuleCat (ULift.{1} ℤ))).mapCocone (freeCofan S)).op) := by
    apply isLimitOfPreserves
    exact h.op
  refine hh.conePointUniqueUpToIso (limit.isLimit _) ≪≫ ?_
  let F := (Discrete.opposite (index S)).inverse
  refine (Functor.Initial.limitIso F _).symm ≪≫ ?_
  refine (Pi.isoLimit _).symm ≪≫ ?_
  refine lim.mapIso ?_
  exact NatIso.ofComponents (fun _ ↦ internalHomIntIso) (fun _ ↦ rfl)

def iso : ℤ[S]◾ ≅ ∏ᶜ (fun i : index S ↦ of ℤ) :=
  iso₁ S ≪≫ iso₂ S

end

end Application
























/-!

**Thanks for listening!**

-/
