/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.OneHypercoverDense

/-!
# Étale sheafification

If `S : Scheme.{u}`, the type of objects in the small étale site `SmallEtaleSite S` of `S`
is in `Type (u + 1)` (this is a large category), so that a priori, we may only get
sheafification for étale sheaves only with values in categories like `Type (u + 1)`.

In this file, we obtain the instance `HasSheafify (smallEtaleTopology S) (Type u)`
by showing that the is a "very small étale site" given by a small category
(whose objects consist of a certain packaging of schemes `X ⟶ S` which are étale
and finitely presented over an open subset of `S`)

-/

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Sieve

@[simp]
lemma ofArrows_le {C : Type*} [Category C] {I : Type*} {X₀ : C} {X : I → C} (f : ∀ i, X i ⟶ X₀)
    (S : Sieve X₀) : ofArrows _ f ≤ S ↔ ∀ (i : I), S (f i) := by
  constructor
  · intro h i
    exact h _ (ofArrows_mk _ f i)
  · rintro h Y _ ⟨_, b, _, h, rfl⟩
    cases' h with i
    exact S.downward_closed (h i) _

end CategoryTheory.Sieve

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})

abbrev SmallEtaleSite := MorphismProperty.Over @IsEtale ⊤ S

variable {S}

structure IsEtaleCovering
    {I : Type v} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S) : Prop where
  isEtale (i : I) : IsEtale (f i) := by infer_instance
  jointly_surjective (s : S) : ∃ i x, (f i).base x = s

namespace IsEtaleCovering

variable {I : Type v} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}
  (h : IsEtaleCovering f)

noncomputable def liftIndex (s : S) : I := (h.jointly_surjective s).choose

noncomputable def lift (s : S) : X (h.liftIndex s) :=
  (h.jointly_surjective s).choose_spec.choose

@[simp]
lemma base_lift (s : S) : (f _).base (h.lift s) = s :=
  (h.jointly_surjective s).choose_spec.choose_spec

def sieve
    {X : S.SmallEtaleSite} {I : Type v} {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X.left)
    (h : IsEtaleCovering f) :
    Sieve X :=
  Sieve.ofArrows (fun i ↦ MorphismProperty.Over.mk ⊤ (f i ≫ X.hom)
    (MorphismProperty.comp_mem _ _ _ (h.isEtale i) X.prop))
      (fun i ↦ MorphismProperty.Over.homMk (f i))

/-- Variant of `IsEtaleCovering.sieve` where we do not assume that the target scheme
is given by an object in `S.SmallEtaleSite`. -/
def sieve'
    {X : Scheme.{u}}
    {I : Type v} {Y : I → Scheme.{u}} {f : ∀ i, Y i ⟶ X}
    (h : IsEtaleCovering f) (a : X ⟶ S) [IsEtale a] :
    Sieve (MorphismProperty.Over.mk _ a inferInstance : SmallEtaleSite S) :=
  IsEtaleCovering.sieve f h

end IsEtaleCovering

variable (S) in
-- we should have this in some form after #19096 and #18945 by Christian Merten
def smallEtaleTopology : GrothendieckTopology (SmallEtaleSite S) where
  sieves X U := ∃ (I : Type u) (Y : I → Scheme.{u}) (f : ∀ i, Y i ⟶ X.left)
      (hf : IsEtaleCovering f), hf.sieve ≤ U
  top_mem' := sorry
  pullback_stable' := sorry
  transitive' := sorry

lemma IsEtaleCovering.sieve_mem
    {X : S.SmallEtaleSite} {I : Type v} {Y : I → Scheme.{u}} (f : ∀ i, Y i ⟶ X.left)
    (h : IsEtaleCovering f) : h.sieve ∈ smallEtaleTopology S X := by
    refine ⟨X.left, fun x ↦ Y (h.liftIndex x), fun x ↦ f (h.liftIndex x),
      ⟨fun _ ↦ h.isEtale _, fun x ↦ ⟨x, h.lift x, by simp⟩⟩, ?_⟩
    dsimp [sieve]
    simp only [Sieve.ofArrows_le]
    intro x
    apply Sieve.ofArrows_mk

lemma IsEtaleCovering.sieve'_mem
    {X : Scheme.{u}}
    {I : Type v} {Y : I → Scheme.{u}} {f : ∀ i, Y i ⟶ X}
    (h : IsEtaleCovering f) (a : X ⟶ S) [IsEtale a] :
    h.sieve' a ∈ smallEtaleTopology S _ := by
  apply sieve_mem

variable (S) in
structure FinitelyPresentedOverAffineOpen : Type u where
  U : Opens S
  hU : IsAffineOpen U
  g : ℕ
  r : ℕ
  var (x : Fin r) : MvPolynomial (Fin g) Γ(S, U)

namespace FinitelyPresentedOverAffineOpen

variable (P : FinitelyPresentedOverAffineOpen S)

noncomputable def scheme : Scheme.{u} :=
  Spec (.of (MvPolynomial (Fin P.g) Γ(S, P.U) ⧸ Ideal.span (Set.range P.var)))

instance : IsAffine P.scheme := by
  dsimp [scheme]
  infer_instance

noncomputable abbrev ringHom :
    Γ(S, P.U) →+* MvPolynomial (Fin P.g) Γ(S, P.U) ⧸ Ideal.span (Set.range P.var) :=
  Algebra.toRingHom

noncomputable def π : P.scheme ⟶ P.U :=
  Spec.map P.ringHom ≫ P.hU.isoSpec.inv

noncomputable def a : P.scheme ⟶ S := P.π ≫ P.U.ι

@[reassoc (attr := simp)]
lemma fac : P.π ≫ P.U.ι = P.a := rfl

end FinitelyPresentedOverAffineOpen

variable (S) in
structure VerySmallEtaleSite extends FinitelyPresentedOverAffineOpen S : Type u where
  isEtale_π : IsEtale toFinitelyPresentedOverAffineOpen.π

namespace VerySmallEtaleSite

attribute [instance] isEtale_π

section

variable (X : VerySmallEtaleSite S)

instance isEtale_a : IsEtale X.a := by
  rw [← X.fac]
  infer_instance

@[simps! left hom]
noncomputable def toSmallEtaleSite : SmallEtaleSite S :=
  MorphismProperty.Over.mk ⊤ X.a inferInstance

end

noncomputable instance : Category (VerySmallEtaleSite S) :=
  InducedCategory.category toSmallEtaleSite

noncomputable def homMk {X Y : VerySmallEtaleSite S} (f : X.scheme ⟶ Y.scheme)
    (hf : f ≫ Y.a = X.a := by aesop_cat) : X ⟶ Y :=
  MorphismProperty.Over.homMk f hf (by simp)

end VerySmallEtaleSite

variable (S)
noncomputable def fromVerySmallEtaleSiteFunctor :
    VerySmallEtaleSite S ⥤ SmallEtaleSite S :=
  inducedFunctor _

noncomputable def fullyFaithfulFromVerySmallEtaleSiteFunctor :
    (fromVerySmallEtaleSiteFunctor S).FullyFaithful :=
  fullyFaithfulInducedFunctor _

instance : (fromVerySmallEtaleSiteFunctor S).Full :=
  (fullyFaithfulFromVerySmallEtaleSiteFunctor S).full

instance : (fromVerySmallEtaleSiteFunctor S).Faithful :=
  (fullyFaithfulFromVerySmallEtaleSiteFunctor S).faithful

variable {S}

@[simp]
lemma fromVerySmallEtaleSiteFunctor_obj_left (X : VerySmallEtaleSite S) :
    ((fromVerySmallEtaleSiteFunctor S).obj X).left = X.scheme := rfl

@[simp]
lemma fromVerySmallEtaleSiteFunctor_obj_hom (X : VerySmallEtaleSite S) :
    ((fromVerySmallEtaleSiteFunctor S).obj X).hom = X.a := rfl

@[simp]
lemma fromVerySmallEtaleSiteFunctor_map_homMk_left
    {X Y : VerySmallEtaleSite S} (f : X.scheme ⟶ Y.scheme)
    (hf : f ≫ Y.a = X.a := by aesop_cat) :
    ((fromVerySmallEtaleSiteFunctor S).map (VerySmallEtaleSite.homMk f hf)).left = f :=
  rfl

variable (S) in
def verySmallEtaleTopology : GrothendieckTopology (VerySmallEtaleSite S) where
  sieves X U := Sieve.functorPushforward (fromVerySmallEtaleSiteFunctor S) U
    ∈ smallEtaleTopology S _
  top_mem' X := by
    dsimp [Membership.mem, Set.Mem]
    simp only [Sieve.functorPushforward_top]
    exact (smallEtaleTopology (S := S)).top_mem X.toSmallEtaleSite
  pullback_stable' := sorry
  transitive' := sorry

namespace fromVerySmallEtaleSiteFunctor_isOneHypercoverDense

variable {X : Scheme.{u}} (f : X ⟶ S)

lemma exists_etale_neighborhood [IsEtale f] (x : X) :
    ∃ (U : VerySmallEtaleSite S) (π : U.scheme ⟶ X) (hπ : IsEtale π)
      (fac : π ≫ f = U.a) (u : U.scheme), π.base u = x := sorry
  -- hπ is automatic, but does mathlib already know?

variable [IsEtale f]

section

variable (x : X)

noncomputable def nbd : VerySmallEtaleSite S :=
  (exists_etale_neighborhood f x).choose

noncomputable def nbdπ : (nbd f x).scheme ⟶ X :=
  (exists_etale_neighborhood f x).choose_spec.choose

instance : IsEtale (nbdπ f x) :=
  (exists_etale_neighborhood f x).choose_spec.choose_spec.choose

@[reassoc (attr := simp)]
lemma fac : nbdπ f x ≫ f = (nbd f x).a :=
  (exists_etale_neighborhood f x).choose_spec.choose_spec.choose_spec.choose

noncomputable def liftNbd : (nbd f x).scheme :=
  (exists_etale_neighborhood f x).choose_spec.choose_spec.choose_spec.choose_spec.choose

@[simp]
lemma liftNbd_fac :
    (nbdπ f x).base (liftNbd f x) = x :=
  (exists_etale_neighborhood f x).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec

end

lemma isEtaleCovering : IsEtaleCovering (nbdπ f) where
  isEtale i := inferInstance
  jointly_surjective x := ⟨x, liftNbd f x, by simp⟩

section

instance (X Y S : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S) [IsEtale g] :
    IsEtale (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance (X Y S : Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S) [IsEtale f] :
    IsEtale (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

end

@[simps]
noncomputable def preOneHypercoverDenseData :
    (S.fromVerySmallEtaleSiteFunctor.PreOneHypercoverDenseData
      (MorphismProperty.Over.mk _ f inferInstance)) where
  I₀ := X
  X x := nbd f x
  f x := MorphismProperty.Over.homMk (nbdπ f x)
  I₁ x₁ x₂ := (pullback (nbdπ f x₁) (nbdπ f x₂) : Scheme.{u})
  Y x₁ x₂ x₁₂ := nbd (pullback.fst _ _ ≫ (nbd f x₁).a) x₁₂
  p₁ x₁ x₂ x₁₂ := MorphismProperty.Over.homMk (nbdπ _ _ ≫ pullback.fst _ _)
  p₂ x₁ x₂ x₁₂ := MorphismProperty.Over.homMk (nbdπ _ _ ≫ pullback.snd _ _) (by
    have := pullback.condition (f := nbdπ f x₁) (g := nbdπ f x₂) =≫ f
    simp only [Category.assoc, fac] at this
    dsimp
    rw [Category.assoc, ← this, fac])
  w x₁ x₂ x₁₂ := by
    dsimp
    ext : 2
    · dsimp [fromVerySmallEtaleSiteFunctor]
      simp only [Category.assoc, pullback.condition]
    · dsimp

noncomputable def oneHypercoverDenseData :
    (S.fromVerySmallEtaleSiteFunctor.OneHypercoverDenseData (verySmallEtaleTopology S)
      (smallEtaleTopology S) (MorphismProperty.Over.mk _ f inferInstance)) where
  toPreOneHypercoverDenseData := preOneHypercoverDenseData f
  mem₀ := by
    refine GrothendieckTopology.superset_covering _ ?_ ((isEtaleCovering f).sieve'_mem f)
    dsimp [IsEtaleCovering.sieve', IsEtaleCovering.sieve]
    simp only [Sieve.ofArrows_le]
    intro x
    refine ⟨(nbd f x).toSmallEtaleSite, MorphismProperty.Over.homMk (by exact 𝟙 _), _, ⟨x⟩,
      by aesop_cat⟩
  mem₁₀ := by
    -- reduce to the case of the pullback and proceed as above
    sorry

end fromVerySmallEtaleSiteFunctor_isOneHypercoverDense

instance fromVerySmallEtaleSiteFunctor_isOneHypercoverDense :
    Functor.IsOneHypercoverDense.{u} (fromVerySmallEtaleSiteFunctor S)
      (verySmallEtaleTopology S) (smallEtaleTopology S) where
  nonempty_oneHypercoverDenseData X := by
    have := X.prop
    exact ⟨fromVerySmallEtaleSiteFunctor_isOneHypercoverDense.oneHypercoverDenseData X.hom⟩


instance : Functor.IsDenseSubsite (verySmallEtaleTopology S) (smallEtaleTopology S)
    (fromVerySmallEtaleSiteFunctor S) :=
  Functor.isDenseSubsite_of_isOneHypercoverDense _ _ _ (by rfl)

example : HasSheafify (smallEtaleTopology S) (Type (u + 1)) := inferInstance

example : HasSheafify (verySmallEtaleTopology S) (Type u) := inferInstance

-- the main result
instance : HasSheafify (smallEtaleTopology S) (Type u) :=
  Functor.hasSheafify_of_isOneHypercoverDense.{u}
    (fromVerySmallEtaleSiteFunctor S)
      (verySmallEtaleTopology S) (smallEtaleTopology S) (Type u)

end AlgebraicGeometry.Scheme
