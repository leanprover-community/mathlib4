/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Sites.Sieves

/-!
# The sheaf condition for a presieve

We define what it means for a presheaf `P : Cᵒᵖ ⥤ Type v` to be a sheaf *for* a particular
presieve `R` on `X`:
* A *family of elements* `x` for `P` at `R` is an element `x_f` of `P Y` for every `f : Y ⟶ X` in
  `R`. See `FamilyOfElements`.
* The family `x` is *compatible* if, for any `f₁ : Y₁ ⟶ X` and `f₂ : Y₂ ⟶ X` both in `R`,
  and any `g₁ : Z ⟶ Y₁` and `g₂ : Z ⟶ Y₂` such that `g₁ ≫ f₁ = g₂ ≫ f₂`, the restriction of
  `x_f₁` along `g₁` agrees with the restriction of `x_f₂` along `g₂`.
  See `FamilyOfElements.Compatible`.
* An *amalgamation* `t` for the family is an element of `P X` such that for every `f : Y ⟶ X` in
  `R`, the restriction of `t` on `f` is `x_f`.
  See `FamilyOfElements.IsAmalgamation`.

We then say `P` is *separated* for `R` if every compatible family has at most one amalgamation,
and it is a *sheaf* for `R` if every compatible family has a unique amalgamation.
See `IsSeparatedFor` and `IsSheafFor`.

In the special case where `R` is a sieve, the compatibility condition can be simplified:
* The family `x` is *compatible* if, for any `f : Y ⟶ X` in `R` and `g : Z ⟶ Y`, the restriction of
  `x_f` along `g` agrees with `x_(g ≫ f)` (which is well defined since `g ≫ f` is in `R`).
  See `FamilyOfElements.SieveCompatible` and `compatible_iff_sieveCompatible`.

In the special case where `C` has pullbacks, the compatibility condition can be simplified:
* The family `x` is *compatible* if, for any `f : Y ⟶ X` and `g : Z ⟶ X` both in `R`,
  the restriction of `x_f` along `π₁ : pullback f g ⟶ Y` agrees with the restriction of `x_g`
  along `π₂ : pullback f g ⟶ Z`.
  See `FamilyOfElements.PullbackCompatible` and `pullbackCompatible_iff`.

We also provide equivalent conditions to satisfy alternate definitions given in the literature.

* Stacks: The condition of https://stacks.math.columbia.edu/tag/00Z8 is virtually identical to the
  statement of `isSheafFor_iff_yonedaSheafCondition` (since the bijection described there carries
  the same information as the unique existence.)

* Maclane-Moerdijk [MM92]: Using `compatible_iff_sieveCompatible`, the definitions of `IsSheaf`
  are equivalent. There are also alternate definitions given:
  - Yoneda condition: Defined in `yonedaSheafCondition` and equivalence in
    `isSheafFor_iff_yonedaSheafCondition`.
  - Matching family for presieves with pullback: `pullbackCompatible_iff`.

## Implementation

The sheaf condition is given as a proposition, rather than a subsingleton in `Type (max u₁ v)`.
This doesn't seem to make a big difference, other than making a couple of definitions noncomputable,
but it means that equivalent conditions can be given as `↔` statements rather than `≃` statements,
which can be convenient.

## References

* [MM92]: *Sheaves in geometry and logic*, Saunders MacLane, and Ieke Moerdijk:
  Chapter III, Section 4.
* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.1.
* https://stacks.math.columbia.edu/tag/00VL (sheaves on a pretopology or site)
* https://stacks.math.columbia.edu/tag/00ZB (sheaves on a topology)

-/

@[expose] public section


universe w w' v₁ v₂ u₁ u₂

namespace CategoryTheory

open Opposite CategoryTheory Category Limits Sieve

namespace Presieve

variable {C : Type u₁} [Category.{v₁} C]
variable {P Q U : Cᵒᵖ ⥤ Type w}
variable {X Y : C} {S : Sieve X} {R : Presieve X}

/-- A family of elements for a presheaf `P` given a collection of arrows `R` with fixed codomain `X`
consists of an element of `P Y` for every `f : Y ⟶ X` in `R`.
A presheaf is a sheaf (resp, separated) if every *compatible* family of elements has exactly one
(resp, at most one) amalgamation.

This data is referred to as a `family` in [MM92], Chapter III, Section 4. It is also a concrete
version of the elements of the middle object in the Stacks entry which is
more useful for direct calculations. It is also used implicitly in Definition C2.1.2 in [Elephant].
-/
@[stacks 00VM "This is a concrete version of the elements of the middle object there."]
def FamilyOfElements (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) :=
  ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → P.obj (op Y)

instance : Inhabited (FamilyOfElements P (⊥ : Presieve X)) :=
  ⟨fun _ _ => False.elim⟩

@[ext]
lemma FamilyOfElements.ext {R : Presieve X} {x y : R.FamilyOfElements P}
    (H : ∀ {Y : C} (f : Y ⟶ X) (hf : R f), x f hf = y f hf) :
    x = y := by
  funext Z f hf
  exact H f hf

/-- A family of elements for a presheaf on the presieve `R₂` can be restricted to a smaller presieve
`R₁`.
-/
def FamilyOfElements.restrict {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂) :
    FamilyOfElements P R₂ → FamilyOfElements P R₁ := fun x _ f hf => x f (h _ _ hf)

/-- The image of a family of elements by a morphism of presheaves. -/
def FamilyOfElements.map (p : FamilyOfElements P R) (φ : P ⟶ Q) :
    FamilyOfElements Q R :=
  fun _ f hf => φ.app _ (p f hf)

@[simp]
lemma FamilyOfElements.map_apply
    (p : FamilyOfElements P R) (φ : P ⟶ Q) {Y : C} (f : Y ⟶ X) (hf : R f) :
    p.map φ f hf = φ.app _ (p f hf) := rfl

lemma FamilyOfElements.restrict_map
    (p : FamilyOfElements P R) (φ : P ⟶ Q) {R' : Presieve X} (h : R' ≤ R) :
    (p.restrict h).map φ = (p.map φ).restrict h := rfl

variable (P) in
/-- A family of elements on `{ f : X ⟶ Y }` is an element of `F(X)`. -/
@[simps apply, simps -isSimp symm_apply]
def FamilyOfElements.singletonEquiv {X Y : C} (f : X ⟶ Y) :
    (singleton f).FamilyOfElements P ≃ P.obj (op X) where
  toFun x := x f (by simp)
  invFun x Z g hg := P.map (eqToHom <| by cases hg; rfl).op x
  left_inv x := by ext _ _ ⟨rfl⟩; simp
  right_inv x := by simp

@[simp]
lemma FamilyOfElements.singletonEquiv_symm_apply_self {X Y : C} (f : X ⟶ Y) (x : P.obj (op X)) :
    (singletonEquiv P f).symm x f ⟨⟩ = x := by
  simp [singletonEquiv_symm_apply]

/-- A family of elements for the arrow set `R` is *compatible* if for any `f₁ : Y₁ ⟶ X` and
`f₂ : Y₂ ⟶ X` in `R`, and any `g₁ : Z ⟶ Y₁` and `g₂ : Z ⟶ Y₂`, if the square `g₁ ≫ f₁ = g₂ ≫ f₂`
commutes then the elements of `P Z` obtained by restricting the element of `P Y₁` along `g₁` and
restricting the element of `P Y₂` along `g₂` are the same.

In special cases, this condition can be simplified, see `pullbackCompatible_iff` and
`compatible_iff_sieveCompatible`.

This is referred to as a "compatible family" in Definition C2.1.2 of [Elephant], and on nlab:
https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents

For a more explicit version in the case where `R` is of the form `Presieve.ofArrows`, see
`CategoryTheory.Presieve.Arrows.Compatible`.
-/
def FamilyOfElements.Compatible (x : FamilyOfElements P R) : Prop :=
  ∀ ⦃Y₁ Y₂ Z⦄ (g₁ : Z ⟶ Y₁) (g₂ : Z ⟶ Y₂) ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
    g₁ ≫ f₁ = g₂ ≫ f₂ → P.map g₁.op (x f₁ h₁) = P.map g₂.op (x f₂ h₂)

/--
If the category `C` has pullbacks, this is an alternative condition for a family of elements to be
compatible: For any `f : Y ⟶ X` and `g : Z ⟶ X` in the presieve `R`, the restriction of the
given elements for `f` and `g` to the pullback agree.
This is equivalent to being compatible (provided `C` has pullbacks), shown in
`pullbackCompatible_iff`.

This is the definition for a "matching" family given in [MM92], Chapter III, Section 4,
Equation (5). Viewing the type `FamilyOfElements` as the middle object of the fork in
https://stacks.math.columbia.edu/tag/00VM, this condition expresses that `pr₀* (x) = pr₁* (x)`,
using the notation defined there.

For a more explicit version in the case where `R` is of the form `Presieve.ofArrows`, see
`CategoryTheory.Presieve.Arrows.PullbackCompatible`.
-/
def FamilyOfElements.PullbackCompatible (x : FamilyOfElements P R) [R.HasPairwisePullbacks] :
    Prop :=
  ∀ ⦃Y₁ Y₂⦄ ⦃f₁ : Y₁ ⟶ X⦄ ⦃f₂ : Y₂ ⟶ X⦄ (h₁ : R f₁) (h₂ : R f₂),
    haveI := HasPairwisePullbacks.has_pullbacks h₁ h₂
    P.map (pullback.fst f₁ f₂).op (x f₁ h₁) = P.map (pullback.snd f₁ f₂).op (x f₂ h₂)

theorem pullbackCompatible_iff (x : FamilyOfElements P R) [R.HasPairwisePullbacks] :
    x.Compatible ↔ x.PullbackCompatible := by
  constructor
  · intro t Y₁ Y₂ f₁ f₂ hf₁ hf₂
    apply t
    haveI := HasPairwisePullbacks.has_pullbacks hf₁ hf₂
    apply pullback.condition
  · intro t Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    haveI := HasPairwisePullbacks.has_pullbacks hf₁ hf₂
    rw [← pullback.lift_fst _ _ comm, op_comp, Functor.map_comp, comp_apply,
      t hf₁ hf₂, ← comp_apply, ← Functor.map_comp, ← op_comp, pullback.lift_snd]

/-- The restriction of a compatible family is compatible. -/
theorem FamilyOfElements.Compatible.restrict {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂)
    {x : FamilyOfElements P R₂} : x.Compatible → (x.restrict h).Compatible :=
  fun q _ _ _ g₁ g₂ _ _ h₁ h₂ comm => q g₁ g₂ (h _ _ h₁) (h _ _ h₂) comm

/-- Extend a family of elements to the sieve generated by an arrow set.
This is the construction described as "easy" in Lemma C2.1.3 of [Elephant].
-/
noncomputable def FamilyOfElements.sieveExtend (x : FamilyOfElements P R) :
    FamilyOfElements P (generate R : Presieve X) := fun _ _ hf =>
  P.map hf.choose_spec.choose.op (x _ hf.choose_spec.choose_spec.choose_spec.1)

/-- The extension of a compatible family to the generated sieve is compatible. -/
theorem FamilyOfElements.Compatible.sieveExtend {x : FamilyOfElements P R} (hx : x.Compatible) :
    x.sieveExtend.Compatible := by
  intro _ _ _ _ _ _ _ h₁ h₂ comm
  iterate 2 erw [← comp_apply, ← Functor.map_comp]; rw [← op_comp]
  apply hx
  simp [comm, h₁.choose_spec.choose_spec.choose_spec.2, h₂.choose_spec.choose_spec.choose_spec.2]

/-- The extension of a family agrees with the original family. -/
theorem extend_agrees {x : FamilyOfElements P R} (t : x.Compatible) {f : Y ⟶ X} (hf : R f) :
    x.sieveExtend f (le_generate R Y _ hf) = x f hf := by
  have h := (le_generate R Y _ hf).choose_spec
  unfold FamilyOfElements.sieveExtend
  rw [t h.choose (𝟙 _) _ hf _]
  · simp
  · rw [id_comp]
    exact h.choose_spec.choose_spec.2

/-- The restriction of an extension is the original. -/
@[simp]
theorem restrict_extend {x : FamilyOfElements P R} (t : x.Compatible) :
    x.sieveExtend.restrict (le_generate R) = x := by
  funext Y f hf
  exact extend_agrees t hf

/--
If the arrow set for a family of elements is actually a sieve (i.e. it is downward closed) then the
consistency condition can be simplified.
This is an equivalent condition, see `compatible_iff_sieveCompatible`.

This is the notion of "matching" given for families on sieves given in [MM92], Chapter III,
Section 4, Equation 1, and nlab: https://ncatlab.org/nlab/show/matching+family.
See also the discussion before Lemma C2.1.4 of [Elephant].
-/
def FamilyOfElements.SieveCompatible (x : FamilyOfElements P (S : Presieve X)) : Prop :=
  ∀ ⦃Y Z⦄ (f : Y ⟶ X) (g : Z ⟶ Y) (hf), x (g ≫ f) (S.downward_closed hf g) = P.map g.op (x f hf)

theorem compatible_iff_sieveCompatible (x : FamilyOfElements P (S : Presieve X)) :
    x.Compatible ↔ x.SieveCompatible := by
  constructor
  · intro h Y Z f g hf
    simpa using h (𝟙 _) g (S.downward_closed hf g) hf (id_comp _)
  · intro h Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ k
    simp_rw [← h f₁ g₁ h₁, ← h f₂ g₂ h₂]
    congr

theorem FamilyOfElements.Compatible.to_sieveCompatible {x : FamilyOfElements P (S : Presieve X)}
    (t : x.Compatible) : x.SieveCompatible :=
  (compatible_iff_sieveCompatible x).1 t

/--
Given a family of elements `x` for the sieve `S` generated by a presieve `R`, if `x` is restricted
to `R` and then extended back up to `S`, the resulting extension equals `x`.
-/
@[simp]
theorem extend_restrict {x : FamilyOfElements P (generate R).arrows} (t : x.Compatible) :
    (x.restrict (le_generate R)).sieveExtend = x := by
  rw [compatible_iff_sieveCompatible] at t
  funext _ _ h
  apply (t _ _ _).symm.trans
  congr
  exact h.choose_spec.choose_spec.choose_spec.2

/--
Two compatible families on the sieve generated by a presieve `R` are equal if and only if they are
equal when restricted to `R`.
-/
theorem restrict_inj {x₁ x₂ : FamilyOfElements P (generate R).arrows} (t₁ : x₁.Compatible)
    (t₂ : x₂.Compatible) : x₁.restrict (le_generate R) = x₂.restrict (le_generate R) → x₁ = x₂ :=
  fun h => by
  rw [← extend_restrict t₁, ← extend_restrict t₂]
  congr

/-- Compatible families of elements for a presheaf of types `P` and a presieve `R`
are in 1-1 correspondence with compatible families for the same presheaf and
the sieve generated by `R`, through extension and restriction. -/
@[simps]
noncomputable def compatibleEquivGenerateSieveCompatible :
    { x : FamilyOfElements P R // x.Compatible } ≃
      { x : FamilyOfElements P (generate R : Presieve X) // x.Compatible } where
  toFun x := ⟨x.1.sieveExtend, x.2.sieveExtend⟩
  invFun x := ⟨x.1.restrict (le_generate R), x.2.restrict _⟩
  left_inv x := Subtype.ext (restrict_extend x.2)
  right_inv x := Subtype.ext (extend_restrict x.2)

theorem FamilyOfElements.comp_of_compatible (S : Sieve X) {x : FamilyOfElements P S}
    (t : x.Compatible) {f : Y ⟶ X} (hf : S f) {Z} (g : Z ⟶ Y) :
    x (g ≫ f) (S.downward_closed hf g) = P.map g.op (x f hf) := by
  simpa using t (𝟙 _) g (S.downward_closed hf g) hf (id_comp _)

lemma FamilyOfElements.compatible_singleton_iff
    {X Y : C} (f : X ⟶ Y) (x : (singleton f).FamilyOfElements P) :
    x.Compatible ↔ ∀ {Z : C} (p₁ p₂ : Z ⟶ X), p₁ ≫ f = p₂ ≫ f →
      P.map p₁.op (x f ⟨⟩) = P.map p₂.op (x f ⟨⟩) := by
  refine ⟨fun H Z p₁ p₂ h ↦ H _ _ _ _ h, fun H Y₁ Y₂ Z g₁ g₂ f₁ f₂ ↦ ?_⟩
  rintro ⟨rfl⟩ ⟨rfl⟩ h
  exact H _ _ h

section FunctorPullback

variable {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C) {Z : D}
variable {T : Presieve (F.obj Z)} {x : FamilyOfElements P T}

/--
Given a family of elements of a sieve `S` on `F(X)`, we can realize it as a family of elements of
`S.functorPullback F`.
-/
def FamilyOfElements.functorPullback (x : FamilyOfElements P T) :
    FamilyOfElements (F.op ⋙ P) (T.functorPullback F) := fun _ f hf => x (F.map f) hf

theorem FamilyOfElements.Compatible.functorPullback (h : x.Compatible) :
    (x.functorPullback F).Compatible := by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq
  exact h (F.map g₁) (F.map g₂) h₁ h₂ (by simp only [← F.map_comp, eq])

end FunctorPullback

/-- Given a family of elements of a sieve `S` on `X` whose values factors through `F`, we can
realize it as a family of elements of `S.functorPushforward F`. Since the preimage is obtained by
choice, this is not well-defined generally.
-/
noncomputable def FamilyOfElements.functorPushforward {D : Type u₂} [Category.{v₂} D] (F : D ⥤ C)
    {X : D} {T : Presieve X} (x : FamilyOfElements (F.op ⋙ P) T) :
    FamilyOfElements P (T.functorPushforward F) := fun Y f h => by
  obtain ⟨Z, g, h, h₁, _⟩ := getFunctorPushforwardStructure h
  exact P.map h.op (x g h₁)

section Pullback

/-- Given a family of elements of a sieve `S` on `X`, and a map `Y ⟶ X`, we can obtain a
family of elements of `S.pullback f` by taking the same elements.
-/
def FamilyOfElements.pullback (f : Y ⟶ X) (x : FamilyOfElements P (S : Presieve X)) :
    FamilyOfElements P (S.pullback f : Presieve Y) := fun _ g hg => x (g ≫ f) hg

theorem FamilyOfElements.Compatible.pullback (f : Y ⟶ X) {x : FamilyOfElements P S.arrows}
    (h : x.Compatible) : (x.pullback f).Compatible := by
  simp only [compatible_iff_sieveCompatible] at h ⊢
  intro W Z f₁ f₂ hf
  unfold FamilyOfElements.pullback
  rw [← h (f₁ ≫ f) f₂ hf]
  congr 1
  simp only [assoc]

end Pullback

/-- Given a morphism of presheaves `f : P ⟶ Q`, we can take a family of elements valued in `P` to a
family of elements valued in `Q` by composing with `f`.
-/
@[deprecated map (since := "2025-09-25")]
def FamilyOfElements.compPresheafMap (f : P ⟶ Q) (x : FamilyOfElements P R) :
    FamilyOfElements Q R := fun Y g hg => f.app (op Y) (x g hg)

@[simp]
lemma FamilyOfElements.map_id (x : FamilyOfElements P R) :
    x.map (𝟙 _) = x :=
  rfl

@[simp]
lemma FamilyOfElements.map_comp (x : FamilyOfElements P R) (f : P ⟶ Q) (g : Q ⟶ U) :
    (x.map f).map g = x.map (f ≫ g) := by
  rfl

theorem FamilyOfElements.Compatible.map (f : P ⟶ Q) {x : FamilyOfElements P R}
    (h : x.Compatible) : (x.map f).Compatible := by
  intro Z₁ Z₂ W g₁ g₂ f₁ f₂ h₁ h₂ eq
  unfold FamilyOfElements.map
  rwa [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, h]

@[deprecated (since := "2025-09-25")] alias FamilyOfElements.compPresheafMap_id :=
  FamilyOfElements.map_id

@[deprecated (since := "2025-09-25")] alias FamilyOfElements.compPresheafMap_comp :=
  FamilyOfElements.map_comp

@[deprecated (since := "2025-09-25")] alias FamilyOfElements.Compatible.compPresheafMap :=
  FamilyOfElements.Compatible.map

/--
The given element `t` of `P.obj (op X)` is an *amalgamation* for the family of elements `x` if every
restriction `P.map f.op t = x_f` for every arrow `f` in the presieve `R`.

This is the definition given in https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents,
and https://ncatlab.org/nlab/show/matching+family, as well as [MM92], Chapter III, Section 4,
equation (2).
-/
def FamilyOfElements.IsAmalgamation (x : FamilyOfElements P R) (t : P.obj (op X)) : Prop :=
  ∀ ⦃Y : C⦄ (f : Y ⟶ X) (h : R f), P.map f.op t = x f h

theorem FamilyOfElements.IsAmalgamation.map {x : FamilyOfElements P R} {t} (f : P ⟶ Q)
    (h : x.IsAmalgamation t) : (x.map f).IsAmalgamation (f.app (op X) t) := by
  intro Y g hg
  dsimp [FamilyOfElements.map]
  change (f.app _ ≫ Q.map _) _ = _
  rw [← f.naturality, comp_apply, h g hg]

@[deprecated (since := "2025-09-25")] alias FamilyOfElements.IsAmalgamation.compPresheafMap :=
  FamilyOfElements.IsAmalgamation.map

theorem is_compatible_of_exists_amalgamation (x : FamilyOfElements P R)
    (h : ∃ t, x.IsAmalgamation t) : x.Compatible := by
  obtain ⟨t, ht⟩ := h
  intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ comm
  rw [← ht _ h₁, ← ht _ h₂, ← comp_apply, ← Functor.map_comp, ← op_comp, comm]
  simp

theorem isAmalgamation_restrict {R₁ R₂ : Presieve X} (h : R₁ ≤ R₂) (x : FamilyOfElements P R₂)
    (t : P.obj (op X)) (ht : x.IsAmalgamation t) : (x.restrict h).IsAmalgamation t := fun Y f hf =>
  ht f (h Y _ hf)

theorem isAmalgamation_sieveExtend {R : Presieve X} (x : FamilyOfElements P R) (t : P.obj (op X))
    (ht : x.IsAmalgamation t) : x.sieveExtend.IsAmalgamation t := by
  intro Y f hf
  dsimp [FamilyOfElements.sieveExtend]
  rw [← ht _, ← comp_apply, ← Functor.map_comp, ← op_comp, hf.choose_spec.choose_spec.choose_spec.2]

@[simp]
lemma FamilyOfElements.isAmalgamation_singleton_iff {X Y : C} (f : X ⟶ Y)
    (x : (singleton f).FamilyOfElements P) (y : P.obj (op Y)) :
    x.IsAmalgamation y ↔ P.map f.op y = x f ⟨⟩ := by
  refine ⟨fun H ↦ H _ _, ?_⟩
  rintro H Y g ⟨rfl⟩
  exact H

/-- A presheaf is separated for a presieve if there is at most one amalgamation. -/
def IsSeparatedFor (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) : Prop :=
  ∀ (x : FamilyOfElements P R) (t₁ t₂), x.IsAmalgamation t₁ → x.IsAmalgamation t₂ → t₁ = t₂

theorem IsSeparatedFor.ext {R : Presieve X} (hR : IsSeparatedFor P R) {t₁ t₂ : P.obj (op X)}
    (h : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : R f), P.map f.op t₁ = P.map f.op t₂) : t₁ = t₂ :=
  hR (fun _ f _ => P.map f.op t₂) t₁ t₂ (fun _ _ hf => h hf) fun _ _ _ => rfl

theorem isSeparatedFor_iff_generate :
    IsSeparatedFor P R ↔ IsSeparatedFor P (generate R : Presieve X) := by
  constructor
  · intro h x t₁ t₂ ht₁ ht₂
    apply h (x.restrict (le_generate R)) t₁ t₂ _ _
    · exact isAmalgamation_restrict _ x t₁ ht₁
    · exact isAmalgamation_restrict _ x t₂ ht₂
  · intro h x t₁ t₂ ht₁ ht₂
    apply h x.sieveExtend
    · exact isAmalgamation_sieveExtend x t₁ ht₁
    · exact isAmalgamation_sieveExtend x t₂ ht₂

theorem isSeparatedFor_top (P : Cᵒᵖ ⥤ Type w) : IsSeparatedFor P (⊤ : Presieve X) :=
  fun x t₁ t₂ h₁ h₂ => by
  have q₁ := h₁ (𝟙 X) (by tauto)
  have q₂ := h₂ (𝟙 X) (by tauto)
  simp only [op_id, Functor.map_id, id_apply] at q₁ q₂
  rw [q₁, q₂]

/-- We define `P` to be a sheaf for the presieve `R` if every compatible family has a unique
amalgamation.

This is the definition of a sheaf for the given presieve given in C2.1.2 of [Elephant], and
https://ncatlab.org/nlab/show/sheaf#GeneralDefinitionInComponents.
Using `compatible_iff_sieveCompatible`,
this is equivalent to the definition of a sheaf in [MM92], Chapter III, Section 4.
-/
def IsSheafFor (P : Cᵒᵖ ⥤ Type w) (R : Presieve X) : Prop :=
  ∀ x : FamilyOfElements P R, x.Compatible → ∃! t, x.IsAmalgamation t

/-- This is an equivalent condition to be a sheaf, which is useful for the abstraction to local
operators on elementary toposes. However this definition is defined only for sieves, not presieves.
The equivalence between this and `IsSheafFor` is given in `isSheafFor_iff_yonedaSheafCondition`.
This version is also useful to establish that being a sheaf is preserved under isomorphism of
presheaves.

See the discussion before Equation (3) of [MM92], Chapter III, Section 4. See also C2.1.4 of
[Elephant]. -/
@[stacks 00Z8 "Direct reformulation"]
def YonedaSheafCondition (P : Cᵒᵖ ⥤ Type v₁) (S : Sieve X) : Prop :=
  ∀ f : S.functor ⟶ P, ∃! g, S.functorInclusion ≫ g = f

-- TODO: We can generalize the universe parameter v₁ above by composing with
-- appropriate `ulift_functor`s.
/-- (Implementation). This is a (primarily internal) equivalence between natural transformations
and compatible families.

Cf the discussion after Lemma 7.47.10 in <https://stacks.math.columbia.edu/tag/00YW>. See also
the proof of C2.1.4 of [Elephant], and the discussion in [MM92], Chapter III, Section 4.
-/
def natTransEquivCompatibleFamily {P : Cᵒᵖ ⥤ Type v₁} :
    (S.functor ⟶ P) ≃ { x : FamilyOfElements P (S : Presieve X) // x.Compatible } where
  toFun α := by
    refine ⟨fun Y f hf => ?_, ?_⟩
    · apply α.app (op Y) ⟨_, hf⟩
    · rw [compatible_iff_sieveCompatible]
      intro Y Z f g hf
      rw [← NatTrans.naturality_apply α g.op]
      rfl
  invFun t :=
    { app _ := TypeCat.ofHom ⟨fun f => t.1 _ f.2⟩
      naturality := fun Y Z g => by
        ext ⟨f, hf⟩
        apply t.2.to_sieveCompatible _ }
  left_inv α := by
    ext X ⟨_, _⟩
    rfl
  right_inv := by
    rintro ⟨x, hx⟩
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- (Implementation). A lemma useful to prove `isSheafFor_iff_yonedaSheafCondition`. -/
theorem extension_iff_amalgamation {P : Cᵒᵖ ⥤ Type v₁} (x : S.functor ⟶ P)
    (g : yoneda.obj X ⟶ P) :
    S.functorInclusion ≫ g = x ↔
      (natTransEquivCompatibleFamily x).1.IsAmalgamation (yonedaEquiv g) := by
  change _ ↔ ∀ ⦃Y : C⦄ (f : Y ⟶ X) (h : S f), P.map f.op (yonedaEquiv g) = x.app (op Y) ⟨f, h⟩
  constructor
  · rintro rfl Y f hf
    rw [yonedaEquiv_naturality]
    simp [yonedaEquiv_apply]
  · intro h
    ext Y ⟨f, hf⟩
    convert h f hf
    rw [yonedaEquiv_naturality]
    simp [yonedaEquiv]

/-- The yoneda version of the sheaf condition is equivalent to the sheaf condition.

C2.1.4 of [Elephant].
-/
theorem isSheafFor_iff_yonedaSheafCondition {P : Cᵒᵖ ⥤ Type v₁} :
    IsSheafFor P (S : Presieve X) ↔ YonedaSheafCondition P S := by
  rw [IsSheafFor, YonedaSheafCondition]
  simp_rw [extension_iff_amalgamation]
  rw [Equiv.forall_congr_left natTransEquivCompatibleFamily]
  rw [Subtype.forall]
  exact forall₂_congr fun x hx ↦ by simp [Equiv.existsUnique_congr_right]

/--
If `P` is a sheaf for the sieve `S` on `X`, a natural transformation from `S` (viewed as a functor)
to `P` can be (uniquely) extended to all of `yoneda.obj X`.
```
      f
   S  →  P
   ↓  ↗
   yX
```
-/
noncomputable def IsSheafFor.extend {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P (S : Presieve X))
    (f : S.functor ⟶ P) : yoneda.obj X ⟶ P :=
  (isSheafFor_iff_yonedaSheafCondition.1 h f).exists.choose

/--
Show that the extension of `f : S.functor ⟶ P` to all of `yoneda.obj X` is in fact an extension,
i.e. that the triangle below commutes, provided `P` is a sheaf for `S`
```
      f
   S  →  P
   ↓  ↗
   yX
```
-/
@[reassoc (attr := simp)]
theorem IsSheafFor.functorInclusion_comp_extend {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P S.arrows)
    (f : S.functor ⟶ P) : S.functorInclusion ≫ h.extend f = f :=
  (isSheafFor_iff_yonedaSheafCondition.1 h f).exists.choose_spec

/-- The extension of `f` to `yoneda.obj X` is unique. -/
theorem IsSheafFor.unique_extend {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P S.arrows)
    {f : S.functor ⟶ P} (t : yoneda.obj X ⟶ P) (ht : S.functorInclusion ≫ t = f) :
    t = h.extend f :=
  (isSheafFor_iff_yonedaSheafCondition.1 h f).unique ht (h.functorInclusion_comp_extend f)

/--
If `P` is a sheaf for the sieve `S` on `X`, then if two natural transformations from `yoneda.obj X`
to `P` agree when restricted to the subfunctor given by `S`, they are equal.
-/
theorem IsSheafFor.hom_ext {P : Cᵒᵖ ⥤ Type v₁} (h : IsSheafFor P (S : Presieve X))
    (t₁ t₂ : yoneda.obj X ⟶ P) (ht : S.functorInclusion ≫ t₁ = S.functorInclusion ≫ t₂) :
    t₁ = t₂ :=
  (h.unique_extend t₁ ht).trans (h.unique_extend t₂ rfl).symm

/-- `P` is a sheaf for `R` iff it is separated for `R` and there exists an amalgamation. -/
theorem isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor :
    (IsSeparatedFor P R ∧ ∀ x : FamilyOfElements P R, x.Compatible → ∃ t, x.IsAmalgamation t) ↔
      IsSheafFor P R := by
  rw [IsSeparatedFor, ← forall_and]
  apply forall_congr'
  intro x
  constructor
  · intro z hx
    exact existsUnique_of_exists_of_unique (z.2 hx) z.1
  · intro h
    refine ⟨?_, ExistsUnique.exists ∘ h⟩
    intro t₁ t₂ ht₁ ht₂
    apply (h _).unique ht₁ ht₂
    exact is_compatible_of_exists_amalgamation x ⟨_, ht₂⟩

/-- If `P` is separated for `R` and every family has an amalgamation, then `P` is a sheaf for `R`.
-/
theorem IsSeparatedFor.isSheafFor (t : IsSeparatedFor P R) :
    (∀ x : FamilyOfElements P R, x.Compatible → ∃ t, x.IsAmalgamation t) → IsSheafFor P R := by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  exact And.intro t

/-- If `P` is a sheaf for `R`, it is separated for `R`. -/
theorem IsSheafFor.isSeparatedFor : IsSheafFor P R → IsSeparatedFor P R := fun q =>
  (isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor.2 q).1

/-- Get the amalgamation of the given compatible family, provided we have a sheaf. -/
noncomputable def IsSheafFor.amalgamate (t : IsSheafFor P R) (x : FamilyOfElements P R)
    (hx : x.Compatible) : P.obj (op X) :=
  (t x hx).exists.choose

theorem IsSheafFor.isAmalgamation (t : IsSheafFor P R) {x : FamilyOfElements P R}
    (hx : x.Compatible) : x.IsAmalgamation (t.amalgamate x hx) :=
  (t x hx).exists.choose_spec

@[simp]
theorem IsSheafFor.valid_glue (t : IsSheafFor P R) {x : FamilyOfElements P R} (hx : x.Compatible)
    (f : Y ⟶ X) (Hf : R f) : P.map f.op (t.amalgamate x hx) = x f Hf :=
  t.isAmalgamation hx f Hf

/-- C2.1.3 in [Elephant] -/
theorem isSheafFor_iff_generate (R : Presieve X) :
    IsSheafFor P R ↔ IsSheafFor P (generate R : Presieve X) := by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  rw [← isSeparatedFor_iff_generate]
  apply and_congr (Iff.refl _)
  constructor
  · intro q x hx
    apply Exists.imp _ (q _ (hx.restrict (le_generate R)))
    intro t ht
    simpa [hx] using isAmalgamation_sieveExtend _ _ ht
  · intro q x hx
    apply Exists.imp _ (q _ hx.sieveExtend)
    intro t ht
    simpa [hx] using isAmalgamation_restrict (le_generate R) _ _ ht

/-- Every presheaf is a sheaf for the family {𝟙 X}.

[Elephant] C2.1.5(i)
-/
theorem isSheafFor_singleton_iso (P : Cᵒᵖ ⥤ Type w) :
    IsSheafFor P (Presieve.singleton (𝟙 X)) := by
  intro x _
  refine ⟨x _ (Presieve.singleton_self _), ?_, ?_⟩
  · rintro _ _ ⟨rfl, rfl⟩
    simp
  · intro t ht
    simpa using ht _ (Presieve.singleton_self _)

/-- Every presheaf is a sheaf for the maximal sieve.

[Elephant] C2.1.5(ii)
-/
theorem isSheafFor_top (P : Cᵒᵖ ⥤ Type w) : IsSheafFor P (⊤ : Presieve X) := by
  rw [← arrows_top, ← generate_of_singleton_isSplitEpi (𝟙 X)]
  rw [← isSheafFor_iff_generate]
  apply isSheafFor_singleton_iso

@[deprecated (since := "2026-01-22")]
alias isSheafFor_top_sieve := isSheafFor_top

/-- If `P₁ : Cᵒᵖ ⥤ Type w` and `P₂  : Cᵒᵖ ⥤ Type w` are two naturally equivalent
presheaves, and `P₁` is a sheaf for a presieve `R`, then `P₂` is also a sheaf for `R`. -/
lemma isSheafFor_of_nat_equiv {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'}
    (e : ∀ ⦃X : C⦄, P₁.obj (op X) ≃ P₂.obj (op X))
    (he : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₁.obj (op Y)),
      e (P₁.map f.op x) = P₂.map f.op (e x))
    {X : C} {R : Presieve X} (hP₁ : IsSheafFor P₁ R) :
    IsSheafFor P₂ R := fun x₂ hx₂ ↦ by
  have he' : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₂.obj (op Y)),
    e.symm (P₂.map f.op x) = P₁.map f.op (e.symm x) := fun X Y f x ↦
      e.injective (by simp only [Equiv.apply_symm_apply, he])
  let x₁ : FamilyOfElements P₁ R := fun Y f hf ↦ e.symm (x₂ f hf)
  have hx₁ : x₁.Compatible := fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ fac ↦ e.injective
    (by simp only [he, Equiv.apply_symm_apply, hx₂ g₁ g₂ h₁ h₂ fac, x₁])
  have : ∀ (t₂ : P₂.obj (op X)),
      x₂.IsAmalgamation t₂ ↔ x₁.IsAmalgamation (e.symm t₂) := fun t₂ ↦ by
    simp only [FamilyOfElements.IsAmalgamation, x₁,
      ← he', EmbeddingLike.apply_eq_iff_eq]
  refine ⟨e (hP₁.amalgamate x₁ hx₁), ?_, ?_⟩
  · dsimp
    simp only [this, Equiv.symm_apply_apply]
    exact IsSheafFor.isAmalgamation hP₁ hx₁
  · intro t₂ ht₂
    refine e.symm.injective ?_
    simp only [Equiv.symm_apply_apply]
    exact hP₁.isSeparatedFor x₁ _ _ (by simpa only [this] using ht₂)
      (IsSheafFor.isAmalgamation hP₁ hx₁)

lemma isSheafFor_iff_of_nat_equiv {P₁ : Cᵒᵖ ⥤ Type w} {P₂ : Cᵒᵖ ⥤ Type w'}
    (e : ∀ ⦃X : C⦄, P₁.obj (op X) ≃ P₂.obj (op X))
    (he : ∀ ⦃X Y : C⦄ (f : X ⟶ Y) (x : P₁.obj (op Y)),
      e (P₁.map f.op x) = P₂.map f.op (e x))
    {X : C} {R : Presieve X} :
    IsSheafFor P₁ R ↔ IsSheafFor P₂ R := by
  refine ⟨fun h ↦ isSheafFor_of_nat_equiv _ he h,
      fun h ↦ isSheafFor_of_nat_equiv (fun _ ↦ (@e _).symm) ?_ h⟩
  intro X Y f x
  obtain ⟨y, rfl⟩ := e.surjective x
  refine e.injective ?_
  simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply, he]

/-- If `P` is a sheaf for `S`, and it is iso to `P'`, then `P'` is a sheaf for `S`. This shows that
"being a sheaf for a presieve" is a mathematical or hygienic property.
-/
theorem isSheafFor_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (hP : IsSheafFor P R) :
    IsSheafFor P' R :=
  isSheafFor_of_nat_equiv (fun X ↦ (i.app (op X)).toEquiv)
    (fun _ _ f x ↦ ConcreteCategory.congr_hom (i.hom.naturality f.op) x) hP

theorem isSheafFor_iff_of_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') :
    IsSheafFor P R ↔ IsSheafFor P' R :=
  ⟨isSheafFor_iso i, isSheafFor_iso i.symm⟩

/-- The property of being separated for some presieve is preserved under isomorphisms. -/
theorem isSeparatedFor_iso {P' : Cᵒᵖ ⥤ Type w} (i : P ≅ P') (hP : IsSeparatedFor P R) :
    IsSeparatedFor P' R := by
  intro x t₁ t₂ ht₁ ht₂
  simpa using congrArg (i.hom.app _) <| hP (x.map i.inv) _ _ (ht₁.map i.inv) (ht₂.map i.inv)

/-- If a presieve `R` on `X` has a subsieve `S` such that:

* `P` is a sheaf for `S`.
* For every `f` in `R`, `P` is separated for the pullback of `S` along `f`,

then `P` is a sheaf for `R`.

This is closely related to [Elephant] C2.1.6(i).
-/
theorem isSheafFor_subsieve_aux (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X}
    (h : (S : Presieve X) ≤ R) (hS : IsSheafFor P (S : Presieve X))
    (trans : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, R f → IsSeparatedFor P (S.pullback f : Presieve Y)) :
    IsSheafFor P R := by
  rw [← isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  constructor
  · intro x t₁ t₂ ht₁ ht₂
    exact
      hS.isSeparatedFor _ _ _ (isAmalgamation_restrict h x t₁ ht₁)
        (isAmalgamation_restrict h x t₂ ht₂)
  · intro x hx
    use hS.amalgamate _ (hx.restrict h)
    intro W j hj
    apply (trans hj).ext
    intro Y f hf
    rw [← comp_apply, ← Functor.map_comp, ← op_comp, hS.valid_glue (hx.restrict h) _ hf,
      FamilyOfElements.restrict, ← hx (𝟙 _) f (h _ _ hf) _ (id_comp _)]
    simp

/--
If `P` is a sheaf for every pullback of the sieve `S`, then `P` is a sheaf for any presieve which
contains `S`.
This is closely related to [Elephant] C2.1.6.
-/
theorem isSheafFor_subsieve (P : Cᵒᵖ ⥤ Type w) {S : Sieve X} {R : Presieve X}
    (h : (S : Presieve X) ≤ R) (trans : ∀ ⦃Y⦄ (f : Y ⟶ X),
      IsSheafFor P (S.pullback f : Presieve Y)) :
    IsSheafFor P R :=
  isSheafFor_subsieve_aux P h (by simpa using trans (𝟙 _)) fun _ f _ => (trans f).isSeparatedFor

section Arrows

variable {B : C} {I : Type*} {X : I → C} (π : (i : I) → X i ⟶ B) (P)

/--
A more explicit version of `FamilyOfElements.Compatible` for a `Presieve.ofArrows`.
-/
def Arrows.Compatible (x : (i : I) → P.obj (op (X i))) : Prop :=
  ∀ i j Z (gi : Z ⟶ X i) (gj : Z ⟶ X j), gi ≫ π i = gj ≫ π j →
    P.map gi.op (x i) = P.map gj.op (x j)

lemma FamilyOfElements.isAmalgamation_iff_ofArrows (x : FamilyOfElements P (ofArrows X π))
    (t : P.obj (op B)) :
    x.IsAmalgamation t ↔ ∀ (i : I), P.map (π i).op t = x _ (ofArrows.mk i) :=
  ⟨fun h i ↦ h _ (ofArrows.mk i), fun h _ f ⟨i⟩ ↦ h i⟩

namespace Arrows.Compatible

variable {x : (i : I) → P.obj (op (X i))}
variable {P π}

theorem exists_familyOfElements (hx : Compatible P π x) :
    ∃ (x' : FamilyOfElements P (ofArrows X π)), ∀ (i : I), x' _ (ofArrows.mk i) = x i := by
  choose i h h' using @ofArrows_surj _ _ _ _ _ π
  exact ⟨fun Y f hf ↦ P.map (eqToHom (h f hf).symm).op (x _),
    fun j ↦ (hx _ j (X j) _ (𝟙 _) <| by rw [← h', id_comp]).trans <| by simp⟩

variable (hx : Compatible P π x)

/--
A `FamilyOfElements` associated to an explicit family of elements.
-/
noncomputable
def familyOfElements : FamilyOfElements P (ofArrows X π) :=
  (exists_familyOfElements hx).choose

@[simp]
theorem familyOfElements_ofArrows_mk (i : I) :
    hx.familyOfElements _ (ofArrows.mk i) = x i :=
  (exists_familyOfElements hx).choose_spec _

theorem familyOfElements_compatible : hx.familyOfElements.Compatible := by
  rintro Y₁ Y₂ Z g₁ g₂ f₁ f₂ ⟨i⟩ ⟨j⟩ hgf
  simp [hx i j Z g₁ g₂ hgf]

end Arrows.Compatible

theorem isSheafFor_arrows_iff : (ofArrows X π).IsSheafFor P ↔
    (∀ (x : (i : I) → P.obj (op (X i))), Arrows.Compatible P π x →
    ∃! t, ∀ i, P.map (π i).op t = x i) := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩
  · obtain ⟨t, ht₁, ht₂⟩ := h _ hx.familyOfElements_compatible
    refine ⟨t, fun i ↦ ?_, fun t' ht' ↦ ht₂ _ fun _ _ ⟨i⟩ ↦ ?_⟩
    · rw [ht₁ _ (ofArrows.mk i), hx.familyOfElements_ofArrows_mk]
    · rw [ht', hx.familyOfElements_ofArrows_mk]
  · obtain ⟨t, hA, ht⟩ := h (fun i ↦ x (π i) (ofArrows.mk _))
      (fun i j Z gi gj ↦ hx gi gj (ofArrows.mk _) (ofArrows.mk _))
    exact ⟨t, fun Y f ⟨i⟩ ↦ hA i, fun y hy ↦ ht y (fun i ↦ hy (π i) (ofArrows.mk _))⟩

/-- If `P` is a presheaf of types and `π : (i : I) → X i ⟶ B` is a family
of morphisms, this is the map from `P.obj (op B)` to the subtype of compatible
families in `P.obj (op (X i))`. -/
@[simps]
def Arrows.toCompatible (s : P.obj (op B)) :
    Subtype (Arrows.Compatible P π) where
  val i := P.map (π i).op s
  property i j Z gi gj h := by
    simp [← comp_apply, ← Functor.map_comp, ← op_comp, h]

theorem isSheafFor_ofArrows_iff_bijective_toCompabible :
    IsSheafFor P (ofArrows X π) ↔
      Function.Bijective (Arrows.toCompatible P π) := by
  rw [isSheafFor_arrows_iff]
  refine ⟨fun h ↦ ⟨fun x₁ x₂ hx ↦
      (h _ (Arrows.toCompatible P π x₁).property).unique (fun _ ↦ rfl)
        (congr_fun (congr_arg Subtype.val hx.symm)),
      fun ⟨y, hy⟩ ↦ ?_⟩, fun h x hx ↦ ?_⟩
  · obtain ⟨x, hx, _⟩ := h y hy
    exact ⟨x, by ext; apply hx⟩
  · obtain ⟨y, hy⟩ := h.2 ⟨x, hx⟩
    rw [Subtype.ext_iff] at hy
    dsimp at hy
    subst hy
    exact ⟨y, fun _ ↦ rfl, fun y' hy' ↦ h.1 (by ext; apply hy')⟩

@[simp]
lemma isSheafFor_pullback_iff (P : Cᵒᵖ ⥤ Type w) {X : C} (R : Sieve X)
    {Y : C} (f : Y ⟶ X) [IsIso f] :
    IsSheafFor P (Sieve.pullback f R).arrows ↔ IsSheafFor P R.arrows := by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  have := Sieve.pullback_ofArrows_of_iso _ g (asIso f)
  dsimp at this
  let e : Subtype (Arrows.Compatible P g) ≃
    Subtype (Arrows.Compatible P (fun i ↦ g i ≫ inv f)) :=
    { toFun s := ⟨fun i ↦ s.val i, fun i₁ i₂ W g₁ g₂ h ↦ by
        simp only [← cancel_mono f, assoc, IsIso.inv_hom_id, comp_id] at h
        exact s.property _ _ _ _ _ h⟩
      invFun s := ⟨fun i ↦ s.val i, fun i₁ i₂ W g₁ g₂ h ↦ by
        replace h := h =≫ inv f
        simp only [Category.assoc] at h
        exact s.property _ _ _ _ _ h⟩ }
  simp only [this, ← isSheafFor_iff_generate,
    isSheafFor_ofArrows_iff_bijective_toCompabible, ← e.bijective.of_comp_iff',
    ← Function.Bijective.of_comp_iff _ (P.mapIso (asIso f).symm.op).toEquiv.bijective]
  convert Iff.rfl using 2
  ext
  simp [e]

set_option backward.isDefEq.respectTransparency false in
lemma isSheafFor_over_map_op_comp_ofArrows_iff
    {B B' : C} (p : B ⟶ B') (P : (Over B')ᵒᵖ ⥤ Type w)
    {X : Over B} {Y : I → Over B} (f : ∀ i, Y i ⟶ X) :
    IsSheafFor ((Over.map p).op ⋙ P) (Presieve.ofArrows _ f) ↔
      IsSheafFor P (Presieve.ofArrows _ (fun i ↦ (Over.map p).map (f i))) := by
  let e : Subtype (Arrows.Compatible ((Over.map p).op ⋙ P) f) ≃
      Subtype (Arrows.Compatible P (fun i ↦ (Over.map p).map (f i))) :=
    { toFun s := ⟨fun i ↦ s.val i, fun i₁ i₂ Z g₁ g₂ h ↦ by
        replace h := (Over.forget _).congr_map h
        dsimp at h
        have := s.property i₁ i₂ (Over.mk (g₁.left ≫ (f i₁).left ≫ X.hom))
          (Over.homMk g₁.left) (Over.homMk g₂.left (by
            have := Over.w (f i₂)
            dsimp at this ⊢
            rw [reassoc_of% h, this])) (by cat_disch)
        let φ : Z ⟶ (Over.map p).obj (Over.mk (g₁.left ≫ (f i₁).left ≫ X.hom)) :=
          Over.homMk (𝟙 _) (by simpa using Over.w g₁)
        replace this := congr_arg (P.map φ.op) this
        dsimp at this
        simp only [← comp_apply, ← Functor.map_comp, ← op_comp] at this
        convert this <;> cat_disch⟩
      invFun s := ⟨fun i ↦ s.val i, fun i₁ i₂ Z g₁ g₂ h ↦
        s.property i₁ i₂ _ ((Over.map p).map g₁) ((Over.map p).map g₂)
          (by simp only [← Functor.map_comp, h])⟩ }
  simp only [isSheafFor_ofArrows_iff_bijective_toCompabible,
    ← e.bijective.of_comp_iff']
  rfl

set_option backward.isDefEq.respectTransparency false in
lemma isSheafFor_over_map_op_comp_iff
    {B B' : C} (p : B ⟶ B') (P : (Over B')ᵒᵖ ⥤ Type w)
    {X : Over B} (R : Sieve X) {X' : Over B'}
    (e : (Over.map p).obj X ≅ X') :
    IsSheafFor ((Over.map p).op ⋙ P) R.arrows ↔
      IsSheafFor P (Sieve.pullback e.inv (Sieve.functorPushforward (Over.map p) R)).arrows := by
  obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
  rw [← isSheafFor_iff_generate, isSheafFor_pullback_iff,
    isSheafFor_over_map_op_comp_ofArrows_iff, isSheafFor_iff_generate]
  convert Iff.rfl
  refine le_antisymm ?_ ?_
  · rintro W _ ⟨T, _, a, ⟨_, b, _, ⟨i⟩, rfl⟩, rfl⟩
    refine ⟨(Over.map p).obj (Z i), Over.homMk (a.left ≫ b.left) ?_, _, ⟨i⟩, ?_⟩
    · simpa [(Over.w_assoc b)] using Over.w a
    · cat_disch
  · rintro W _ ⟨_, a, _, ⟨i⟩, rfl⟩
    exact ⟨_, _, _, Sieve.ofArrows_mk _ _ i, rfl⟩

variable [(ofArrows X π).HasPairwisePullbacks]

/--
A more explicit version of `FamilyOfElements.PullbackCompatible` for a `Presieve.ofArrows`.
-/
def Arrows.PullbackCompatible (x : (i : I) → P.obj (op (X i))) : Prop :=
  ∀ i j, P.map (pullback.fst (π i) (π j)).op (x i) =
    P.map (pullback.snd (π i) (π j)).op (x j)

theorem Arrows.pullbackCompatible_iff (x : (i : I) → P.obj (op (X i))) :
    Compatible P π x ↔ PullbackCompatible P π x := by
  refine ⟨fun t i j ↦ ?_, fun t i j Z gi gj comm ↦ ?_⟩
  · apply t
    exact pullback.condition
  · rw [← pullback.lift_fst _ _ comm, op_comp, Functor.map_comp, comp_apply, t i j,
      ← comp_apply, ← Functor.map_comp, ← op_comp, pullback.lift_snd]

theorem isSheafFor_arrows_iff_pullbacks : (ofArrows X π).IsSheafFor P ↔
    (∀ (x : (i : I) → P.obj (op (X i))), Arrows.PullbackCompatible P π x →
    ∃! t, ∀ i, P.map (π i).op t = x i) := by
  simp_rw [← Arrows.pullbackCompatible_iff, isSheafFor_arrows_iff]

end Arrows

@[simp]
lemma isSeparatedFor_singleton {X Y : C} {f : X ⟶ Y} :
    Presieve.IsSeparatedFor P (.singleton f) ↔
      Function.Injective (P.map f.op) := by
  rw [IsSeparatedFor, Equiv.forall_congr_left (Presieve.FamilyOfElements.singletonEquiv P f)]
  simp_rw [FamilyOfElements.isAmalgamation_singleton_iff,
    FamilyOfElements.singletonEquiv_symm_apply_self, Function.Injective]
  aesop

lemma isSheafFor_singleton {X Y : C} {f : X ⟶ Y} :
    Presieve.IsSheafFor P (.singleton f) ↔
      ∀ (x : P.obj (op X)),
        (∀ {Z : C} (p₁ p₂ : Z ⟶ X), p₁ ≫ f = p₂ ≫ f → P.map p₁.op x = P.map p₂.op x) →
        ∃! y, P.map f.op y = x := by
  rw [IsSheafFor, Equiv.forall_congr_left (Presieve.FamilyOfElements.singletonEquiv P f)]
  simp_rw [FamilyOfElements.compatible_singleton_iff,
    FamilyOfElements.isAmalgamation_singleton_iff, FamilyOfElements.singletonEquiv_symm_apply_self]

/--
To show `P` is a sheaf for the binding of `U` with `B`, it suffices to show that `P` is a sheaf for
`U`, that `P` is a sheaf for each sieve in `B`, and that it is separated for any pullback of any
sieve in `B`.

This is mostly an auxiliary lemma to show `Presieve.isSheafFor_trans`.
Adapted from [Elephant], Lemma C2.1.7(i) with suggestions as mentioned in
https://math.stackexchange.com/a/358709/
-/
theorem isSheafFor_bind (P : Cᵒᵖ ⥤ Type*) (U : Sieve X)
    (B : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄, U f → Sieve Y)
    (hU : Presieve.IsSheafFor P (U : Presieve X))
    (hB : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), Presieve.IsSheafFor P (B hf : Presieve Y))
    (hB' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (h : U f) ⦃Z⦄ (g : Z ⟶ Y),
      Presieve.IsSeparatedFor P (((B h).pullback g) : Presieve Z)) :
    Presieve.IsSheafFor P (Sieve.bind (U : Presieve X) B : Presieve X) := by
  intro s hs
  let y : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), Presieve.FamilyOfElements P (B hf : Presieve Y) :=
    fun Y f hf Z g hg => s _ (Presieve.bind_comp _ _ hg)
  have hy : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).Compatible := by
    intro Y f H Y₁ Y₂ Z g₁ g₂ f₁ f₂ hf₁ hf₂ comm
    apply hs
    apply reassoc_of% comm
  let t : Presieve.FamilyOfElements P (U : Presieve X) :=
    fun Y f hf => (hB hf).amalgamate (y hf) (hy hf)
  have ht : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (hf : U f), (y hf).IsAmalgamation (t f hf) := fun Y f hf =>
    (hB hf).isAmalgamation _
  have hT : t.Compatible := by
    rw [Presieve.compatible_iff_sieveCompatible]
    intro Z W f h hf
    apply (hB (U.downward_closed hf h)).isSeparatedFor.ext
    intro Y l hl
    apply (hB' hf (l ≫ h)).ext
    intro M m hm
    have : Sieve.bind U B (m ≫ l ≫ h ≫ f) := by simpa using (bind_comp f hf hm : Sieve.bind U B _)
    trans s (m ≫ l ≫ h ≫ f) this
    · have := ht (U.downward_closed hf h) _ ((B _).downward_closed hl m)
      simp only [op_comp, Functor.map_comp, comp_apply] at this
      grind
    · have h : s _ _ = _ := (ht hf _ hm).symm
      -- Porting note: this was done by `simp only [assoc] at`
      conv_lhs at h => congr; rw [assoc, assoc]
      simp [h]
  refine ⟨hU.amalgamate t hT, ?_, ?_⟩
  · rintro Z _ ⟨Y, f, g, hg, hf, rfl⟩
    rw [op_comp, Functor.map_comp, comp_apply, Presieve.IsSheafFor.valid_glue _ _ _ hg]
    apply ht hg _ hf
  · intro y hy
    apply hU.isSeparatedFor.ext
    intro Y f hf
    apply (hB hf).isSeparatedFor.ext
    intro Z g hg
    rw [← comp_apply, ← Functor.map_comp, ← op_comp, hy _ (Presieve.bind_comp _ _ hg),
      hU.valid_glue _ _ hf, ht hf _ hg]

/-- Given two sieves `R` and `S`, to show that `P` is a sheaf for `S`, we can show:
* `P` is a sheaf for `R`
* `P` is a sheaf for the pullback of `S` along any arrow in `R`
* `P` is separated for the pullback of `R` along any arrow in `S`.

This is mostly an auxiliary lemma to construct `Sheaf.finestTopology`.
Adapted from [Elephant], Lemma C2.1.7(ii) with suggestions as mentioned in
https://math.stackexchange.com/a/358709
-/
theorem isSheafFor_trans (P : Cᵒᵖ ⥤ Type*) (R S : Sieve X)
    (hR : Presieve.IsSheafFor P (R : Presieve X))
    (hR' : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : S f), Presieve.IsSeparatedFor P (R.pullback f : Presieve Y))
    (hS : ∀ ⦃Y⦄ ⦃f : Y ⟶ X⦄ (_ : R f), Presieve.IsSheafFor P (S.pullback f : Presieve Y)) :
    Presieve.IsSheafFor P (S : Presieve X) := by
  have : (Sieve.bind R fun Y f _ => S.pullback f : Presieve X) ≤ S := by
    rintro Z f ⟨W, f, g, hg, hf : S _, rfl⟩
    apply hf
  apply Presieve.isSheafFor_subsieve_aux P this
  · apply isSheafFor_bind _ _ _ hR hS
    intro Y f hf Z g
    rw [← pullback_comp]
    apply (hS (R.downward_closed hf _)).isSeparatedFor
  · intro Y f hf
    have : Sieve.pullback f (Sieve.bind R fun T (k : T ⟶ X) (_ : R k) => pullback k S) =
        R.pullback f := by
      ext Z g
      constructor
      · rintro ⟨W, k, l, hl, _, comm⟩
        rw [pullback_apply, ← comm]
        simp [hl]
      · intro a
        refine ⟨Z, 𝟙 Z, _, a, ?_⟩
        simp [hf]
    rw [this]
    apply hR' hf

end Presieve

end CategoryTheory
