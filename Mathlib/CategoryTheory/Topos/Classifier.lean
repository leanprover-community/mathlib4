/-
Copyright (c) 2024 Charlie Conneen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Conneen, Pablo Donato
-/
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.CategoryTheory.Limits.Shapes.RegularMono
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.CategoryTheory.Subobject.Presheaf

/-!

# Subobject Classifier

We define what it means for a morphism in a category to be a subobject classifier as
`CategoryTheory.HasClassifier`.

c.f. the following Lean 3 code, where similar work was done:
https://github.com/b-mehta/topos/blob/master/src/subobject_classifier.lean

## Main definitions

Let `C` refer to a category with a terminal object.

* `CategoryTheory.Classifier C` is the data of a subobject classifier in `C`.

* `CategoryTheory.HasClassifier C` says that there is at least one subobject classifier.
  `Ω C` denotes a choice of subobject classifier.

* `CategoryTheory.Classifier.cmap` sends every subobject of `X` to its characteristic map of type
  `X ⟶ Ω C`.

* `CategoryTheory.Classifier.compr` sends every map `φ : X ⟶ Ω C` to the subobject of `X` whose
  characteristic map is `φ` by pulling back the truth morphism along `φ`. This generalizes the
  construction of a subset "by comprehension" from its characteristic function in set theory.

## Main results

* It is a theorem that the truth morphism `⊤_ C ⟶ Ω C` is a (split, and therefore regular)
  monomorphism, simply because its source is the terminal object.

* An instance of `IsRegularMonoCategory C` is exhibited for any category with a subobject
  classifier.

* `CategoryTheory.Classifier.representableBy`: any subobject classifier `Ω` in `C` represents the
  subobjects functor `CategoryTheory.Subobject.presheaf C`.

* `CategoryTheory.Classifier.fromRepresentation`: any representation `Ω` of
  `CategoryTheory.Subobject.presheaf C` is a subobject classifier in `C`.

* `CategoryTheory.hasClassifier_isRepresentable_iff`: from the two above mappings, we get that a
  category `C` has a subobject classifier if and only if the subobjects presheaf
  `CategoryTheory.Subobject.presheaf C` is representable (Proposition 1 in Section I.3 of [MM92]).

## References

* [S. MacLane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]

## TODO

* Make API for constructing a subobject classifier without reference to limits (replacing `⊤_ C`
  with an arbitrary `Ω₀ : C` and including the assumption `mono truth`)

-/

universe u v u₀ v₀

open CategoryTheory Category Limits Functor

variable (C : Type u) [Category.{v} C] [HasTerminal C]

namespace CategoryTheory

/-- A morphism `truth : ⊤_ C ⟶ Ω` from the terminal object of a category `C`
is a subobject classifier if, for every monomorphism `m : U ⟶ X` in `C`,
there is a unique map `χ : X ⟶ Ω` such that the following square is a pullback square:
```
      U ---------m----------> X
      |                       |
terminal.from U               χ
      |                       |
      v                       v
    ⊤_ C ------truth--------> Ω
```
An equivalent formulation replaces the object `⊤_ C` with an arbitrary object, and instead
includes the assumption that `truth` is a monomorphism.
-/
structure Classifier where
  /-- The target of the truth morphism -/
  Ω : C
  /-- the truth morphism for a subobject classifier -/
  truth : ⊤_ C ⟶ Ω
  /-- For any monomorphism `U ⟶ X`, there is an associated characteristic map `X ⟶ Ω`. -/
  χ {U X : C} (m : U ⟶ X) [Mono m] : X ⟶ Ω
  /-- `χ m` forms the appropriate pullback square. -/
  isPullback {U X : C} (m : U ⟶ X) [Mono m] : IsPullback m (terminal.from U) (χ m) truth
  /-- `χ m` is the only map `X ⟶ Ω` which forms the appropriate pullback square. -/
  uniq {U X : C} (m : U ⟶ X) [Mono m] (χ' : X ⟶ Ω)
      (hχ' : IsPullback m (terminal.from U) χ' truth) :
    χ' = χ m

/-- A category `C` has a subobject classifier if there is at least one subobject classifier. -/
class HasClassifier : Prop where
  /-- There is some classifier. -/
  exists_classifier : Nonempty (Classifier C)

namespace HasClassifier

variable [HasClassifier C]

noncomputable section

/-- Notation for the object in an arbitrary choice of a subobject classifier -/
abbrev Ω : C := HasClassifier.exists_classifier.some.Ω

/-- Notation for the "truth arrow" in an arbitrary choice of a subobject classifier -/
abbrev truth : ⊤_ C ⟶ Ω C := HasClassifier.exists_classifier.some.truth

variable {C}
variable {U X : C} (m : U ⟶ X) [Mono m]

/-- returns the characteristic morphism of the subobject `(m : U ⟶ X) [Mono m]` -/
def χ : X ⟶ Ω C :=
  HasClassifier.exists_classifier.some.χ m

/-- The diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ m
      |                       |
      v                       v
    ⊤_ C -----truth C-------> Ω
```
is a pullback square.
-/
lemma isPullback_χ : IsPullback m (terminal.from U) (χ m) (truth C) :=
  HasClassifier.exists_classifier.some.isPullback m

/-- The diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ m
      |                       |
      v                       v
    ⊤_ C -----truth C-------> Ω
```
commutes.
-/
@[reassoc]
lemma comm : m ≫ χ m = terminal.from _ ≫ truth C := (isPullback_χ m).w

/-- `χ m` is the only map for which the associated square
is a pullback square.
-/
lemma unique (χ' : X ⟶ Ω C) (hχ' : IsPullback m (terminal.from _) χ' (truth C)) : χ' = χ m :=
  HasClassifier.exists_classifier.some.uniq m χ' hχ'

/-- `truth C` is a regular monomorphism (because it is split). -/
noncomputable instance truthIsRegularMono : RegularMono (truth C) :=
  RegularMono.ofIsSplitMono (truth C)

/-- The following diagram
```
      U ---------m----------> X
      |                       |
terminal.from U              χ m
      |                       |
      v                       v
    ⊤_ C -----truth C-------> Ω
```
being a pullback for any monic `m` means that every monomorphism
in `C` is the pullback of a regular monomorphism; since regularity
is stable under base change, every monomorphism is regular.
Hence, `C` is a regular mono category.
It also follows that `C` is a balanced category.
-/
instance isRegularMonoCategory : IsRegularMonoCategory C where
  regularMonoOfMono :=
    fun m => ⟨regularOfIsPullbackFstOfRegular (isPullback_χ m).w (isPullback_χ m).isLimit⟩

/-- If the source of a faithful functor has a subobject classifier, the functor reflects
  isomorphisms. This holds for any balanced category.
-/
instance reflectsIsomorphisms (D : Type u₀) [Category.{v₀} D] (F : C ⥤ D) [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

/-- If the source of a faithful functor is the opposite category of one with a subobject classifier,
  the same holds -- the functor reflects isomorphisms.
-/
instance reflectsIsomorphismsOp (D : Type u₀) [Category.{v₀} D] (F : Cᵒᵖ ⥤ D)
    [Functor.Faithful F] :
    Functor.ReflectsIsomorphisms F :=
  reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms F

end
end HasClassifier

/-! ### The representability theorem of subobject classifiers -/

section Representability

/-! #### Lemmas about pullbacks and subobjects -/

section SubobjectIsPullback

open Subobject

variable {C : Type u} [Category.{v} C]

lemma eqOfIsPullback {X Y Z : C} {x x' : Subobject X}
    {f : X ⟶ Z} {g : Y ⟶ Z} {k : (x : C) ⟶ Y} {k' : (x' : C) ⟶ Y}
    (h : IsPullback k x.arrow g f) (h' : IsPullback k' x'.arrow g f) :
    x = x' :=
  eq_of_comm (IsPullback.isoIsPullback _ _ h h') (by simp)

lemma arrow_isPullback {X Y Z : C}
    (f : Y ⟶ Z) (g : X ⟶ Z) [HasPullback f g] [Mono f] :
    IsPullback ((underlyingIso _).hom ≫ pullback.fst f g) (mk (pullback.snd f g)).arrow f g :=
  IsPullback.of_iso (IsPullback.of_hasPullback f g)
    (underlyingIso _).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

end SubobjectIsPullback

namespace Classifier

open Subobject HasClassifier

variable {C : Type u} [Category.{v} C] [HasTerminal C] {𝒞 : Classifier C}

/-! #### From classifiers to representations -/

section RepresentableBy

/-- `x.cmap` is the unique characteristic map of subobject `x` given by the `IsClassifier` property.
-/
noncomputable def cmap {X : C} (x : Subobject X) : X ⟶ 𝒞.Ω :=
  𝒞.χ x.arrow

variable [HasPullbacks C]

/-- `compr χ` builds the subobject whose characteristic map is `φ` by pulling back `truth` along
    `φ`. This generalizes the construction of a subset "by comprehension" from its characteristic
    function in set theory. -/
noncomputable def compr {X : C} (φ : X ⟶ 𝒞.Ω) : Subobject X :=
  (Subobject.pullback φ).obj (Subobject.mk 𝒞.truth)

lemma compr_isPullback {X : C} (φ : X ⟶ 𝒞.Ω) :
    IsPullback (compr φ).arrow (terminal.from (compr φ : C)) φ 𝒞.truth := by
  have h := IsPullback.of_hasPullback 𝒞.truth φ
  let i : (compr φ : C) ≅ Limits.pullback 𝒞.truth φ := underlyingIso _
  apply IsPullback.flip
  apply IsPullback.of_iso h
    (underlyingIso _).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    <;> try aesop_cat
  have heq : (compr φ).arrow = (Subobject.mk (pullback.snd 𝒞.truth φ)).arrow := by rfl
  simp [heq]

lemma compr_cmap {X : C} (x : Subobject X) :
    compr (𝒞 := 𝒞) (cmap x) = x := by
  have h : IsPullback x.arrow (terminal.from (x : C)) (cmap x) 𝒞.truth :=
    𝒞.isPullback x.arrow
  have h' : IsPullback (compr (𝒞 := 𝒞) (cmap x)).arrow (terminal.from (compr (cmap x) : C))
                       (cmap x) 𝒞.truth := by
    apply compr_isPullback
  apply IsPullback.flip at h
  apply IsPullback.flip at h'
  exact eqOfIsPullback h' h

lemma cmap_compr {X : C} (φ : X ⟶ 𝒞.Ω) :
    cmap (compr φ) = φ := by
  have h := compr_isPullback φ
  conv => rhs; rw [𝒞.uniq (compr φ).arrow φ h]
  simp [cmap]

variable {C : Type u} [Category.{v} C] [HasTerminal C] [HasPullbacks C]

/-- Any subobject classifier `Ω` represents the subobjects functor `sub`. -/
noncomputable def representableBy (𝒞 : Classifier C) :
    (Subobject.presheaf C).RepresentableBy 𝒞.Ω := by
  exact {
    /- The correspondence `compr` sending each map `φ : X ⟶ Ω` to the corresponding subobject is a
       bijection with `cmap` as inverse. -/
    homEquiv := {
      toFun := compr
      invFun := cmap
      left_inv := cmap_compr
      right_inv := compr_cmap
    }
    /- Furthermore, this bijection is natural by the fact that two pullback squares placed side by
       side yield a pullback rectangle (lemma `Subobject.pullback_comp`). -/
    homEquiv_comp := by
      intro X X' f g
      dsimp
      simp [compr, pullback_comp]
  }

end RepresentableBy

/-! #### From representations to classifiers -/

section FromRepresentation

variable {C : Type u} [Category.{v} C] [HasPullbacks C]

abbrev SubobjectRepresentableBy X := (Subobject.presheaf C).RepresentableBy X

variable {Ω : C} (h : SubobjectRepresentableBy Ω)

namespace SubobjectRepresentableBy

/-- Representability of `Subobject.presheaf C` by `Ω` gives us a natural bijection `θ`. -/
def θ {X : C} : (X ⟶ Ω) ≃ Subobject X :=
  h.homEquiv
lemma hθ {X X' : C} (f : X ⟶ X') (g : X' ⟶ Ω) :
    θ h (f ≫ g) = (Subobject.presheaf C).map f.op (θ h g) :=
  h.homEquiv_comp f g

/-- Each subobject `x` of `X` corresponds to a morphism `φₓ : X ⟶ Ω` through `θ`. -/
def φ {X : C} (x : Subobject X) : X ⟶ Ω := (θ h).symm x
lemma hφ {X : C} (χ : X ⟶ Ω) : χ = φ h (θ h χ) := by simp [φ]

/-- Some subobject `Ω₀` of `Ω` corresponds to the identity `𝟙 Ω` through `θ`. -/
def Ω₀ : Subobject Ω := θ h (𝟙 Ω)

/-- Let `t₀` be the underlying monomorphism of `Ω₀` (this requires the axiom of choice). -/
noncomputable def t₀ : (Ω₀ h : C) ⟶ Ω := (Ω₀ h).arrow
instance t₀_mono : Mono (t₀ h) := arrow_mono (Ω₀ h)

/-- The naturality of `θ` (hypothesis `hθ`) states that `x = φₓ⋆ Ω₀` for any `x`. -/
lemma hx_pullback {X : C} (x : Subobject X) :
    x = (Subobject.pullback (φ h x)).obj (Ω₀ h) := by
  have := hθ h ((θ h).symm x) (𝟙 _)
  simp only [Category.comp_id, Equiv.apply_symm_apply] at this
  rw (occs := .pos [1]) [this]
  simp [Subobject.presheaf, φ, Ω₀]

/-- More explicitly, `x` is the canonical representative of the pullback of `t₀` along `φₓ`. -/
lemma hx_mk {X : C} (x : Subobject X) :
    x = Subobject.mk (pullback.snd (t₀ h) (φ h x)) := by
  rw (occs := .pos [1]) [hx_pullback h x, pullback_obj]
  dsimp [t₀]

/-- Even more explicitly, we have an isomorphism `ιₓ` between the underlying object `(x : C)` of
    `x` in `C` (obtained through the axiom of choice) and the pullback of `t₀` and `φₓ`. -/
noncomputable def ι {X : C} (x : Subobject X) :
    (x : C) ≅ Limits.pullback (t₀ h) (φ h x) := by
  rw (occs := .pos [1]) [hx_mk h x]
  exact (underlyingIso (pullback.snd (t₀ h) (φ h x)))

/-- Let `πₓ : x ⟶ Ω₀` be the first projection of the pullback of `t₀` and `φₓ` modulo `ιₓ`. -/
noncomputable def π {X : C} (x : Subobject X) :=
  (ι h x).hom ≫ pullback.fst (t₀ h) (φ h x)

instance {X : C} (x : Subobject X) : Mono (pullback.snd (t₀ h) (φ h x)) := inferInstance

/-- We can finally state that the corresponding pullback square commutes (diagram (5) in [MM92]).

    Implementation note: Here we need to deal with the usual "transport hell" of dependent types,
    which materializes in Lean under the guise of the heterogenous equality type `HEq`. This is
    because the types of morphisms are *propositionally* equal rather than *definitionally* equal,
    which in turn is caused by the need to explicitly manipulate isomorphisms. Univalence would
    probably make things much easier.
-/
lemma isPullback_φ {X : C} (x : Subobject X) :
    IsPullback (π h x) x.arrow (t₀ h) (φ h x) := by
  have hx := hx_mk h x
  rw (occs := .pos [1,2,3]) [hx]
  have h1 : ((underlyingIso (pullback.snd (t₀ h) (φ h x))).hom ≫ pullback.fst (t₀ h) (φ h x)) =
            (π h (Subobject.mk (pullback.snd (t₀ h) (φ h x)))) := by
    congr; try exact hx
    dsimp [ι]
    set hc := Eq.symm (congrArg (fun _a ↦ underlying.obj _a ≅ Limits.pullback (t₀ h)
                                          (φ h (Subobject.mk (pullback.snd (t₀ h) (φ h x)))))
                                (hx_mk h (Subobject.mk (pullback.snd (t₀ h) (φ h x)))))
    have := cast_heq hc ((underlyingIso (pullback.snd (t₀ h)
                                         (φ h (Subobject.mk (pullback.snd (t₀ h) (φ h x)))))))
    symm
    apply HEq.trans this
    symm
    congr
  rw [← h1]
  exact arrow_isPullback (t₀ h) (φ h x)

/-- Furthermore, `φₓ` is the unique morphism that makes this pullback square commute by
    bijectivity and naturality of `θ`.

    Note that we actually generalize `πₓ` to any morphism `ψ : x ⟶ Ω₀`, which will be necessary
    many times later on in the proof.
-/
lemma isPullback_uniq {X : C} (x : Subobject X) ψ χ (hχ : IsPullback ψ x.arrow (t₀ h) χ) :
    χ = φ h x := by
  rw [hφ h χ]
  congr
  have hθ := hθ h χ (𝟙 _)
  rw [Category.comp_id] at hθ
  rw [hθ]
  dsimp [Subobject.presheaf]
  rw [pullback_obj, eqOfIsPullback hχ (arrow_isPullback _ _)]
  rfl

/-- It remains to show that `Ω₀` is actually a terminal object in `C`. -/
noncomputable def isTerminal_Ω₀ : IsTerminal (Ω₀ h : C) := by
  have : (X : C) → Unique (X ⟶ Ω₀ h) := by
    intro X
    /- Taking `x` to be the (canonical representative of) the identity `𝟙 X`... -/
    let x := Subobject.mk (𝟙 X)
    /- ... gives a map `φ' : X ⟶ Ω₀` (modulo the canonical isomorphism `i : X ≅ x`). -/
    let i : X ≅ x := by dsimp [x]; exact (underlyingIso (𝟙 X)).symm
    let φ' := (i.hom ≫ π h x)

    /- We show that every `φ'' : X ⟶ Ω₀` is equal to `φ'`. -/
    refine { default := φ', uniq := ?_ }
    intro φ''
    dsimp [default]

    /- Since `t₀` is a monomorphism, every `ψ : X ⟶ Ω₀` forms a "trivial" pullback square. -/
    have hψ : ∀ ψ, IsPullback ψ (𝟙 X) (t₀ h) (ψ ≫ t₀ h) := by
      intro ψ
      constructor
      · constructor
        apply PullbackCone.IsLimit.mk (lift := fun c ↦ c.snd) <;> intro c
        · apply Mono.right_cancellation (f := t₀ h)
          rw [c.condition]
          simp
        · simp
        · intro m hm1 hm2
          rw [← hm2]
          simp
      · simp

    /- This applies in particular to `φ` and `φ'`. -/
    have h' := hψ φ'
    have h'' := hψ φ''

    /- This square has the same shape as (5) (modulo the iso `i`), hence by the uniqueness of
       `φₓ` in (5) we get `t₀ ∘ φ' = t₀ ∘ φ''`. -/
    have hφ' := isPullback_uniq h x (π h x) (φ' ≫ t₀ h)
    have hφ'' := isPullback_uniq h x (i.inv ≫ φ'') (φ'' ≫ t₀ h)
    have h : φ' ≫ t₀ h = φ'' ≫ t₀ h := by
      rw [hφ', hφ'']
      · exact IsPullback.of_iso h'' i (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp) (by simp [i, x]) (by simp) (by simp)
      · exact IsPullback.of_iso h' i (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by simp [φ']) (by simp [i, x]) (by simp) (by simp)
    /- As `t₀` is monic, this gives `φ' = φ''`. -/
    exact Mono.right_cancellation _ _ h.symm
  apply IsTerminal.ofUnique

/-- We need to give explicitly the iso `i` with the "canonical" terminal object `⊤_ C`. -/
noncomputable def i [HasTerminal C] : ⊤_ C ≅ Ω₀ h := by
  apply IsTerminal.uniqueUpToIso
  · exact terminalIsTerminal
  · exact isTerminal_Ω₀ h

end SubobjectRepresentableBy

open SubobjectRepresentableBy

/-- Any representation `Ω` of `Subobject.presheaf C` gives a classifier with truth values object
    `Ω`. -/
noncomputable def fromRepresentation [HasTerminal C] : Classifier C := by
  /- Finally, we can give `Ω₀` as the subobject classifier with `t₀` as truth morphism (modulo `i`)
     and `φ ⟦m⟧` as characteristic map for every monomorphism `m`.  -/
  exact {
    Ω := Ω
    truth := (i h).hom ≫ t₀ h
    χ := fun m ↦ φ h (Subobject.mk m)

    isPullback := by
      intro U X m hm
      apply IsPullback.flip
      have h' := isPullback_φ h (Subobject.mk m)
      exact IsPullback.of_iso h'
        (underlyingIso m) (i h).symm (Iso.refl _) (Iso.refl _)
        (Subsingleton.elim _ _) (by simp) (by simp) (by simp)

    uniq := by
      intro U X m hm χ' hχ'
      dsimp
      apply IsPullback.flip at hχ'
      apply isPullback_uniq h (Subobject.mk m) ((underlyingIso m).hom ≫ terminal.from U ≫ (i h).hom)
      exact IsPullback.of_iso hχ'
        (underlyingIso m).symm (i h) (Iso.refl _) (Iso.refl _)
        (by simp) (by simp) (by simp) (by simp)
  }

end FromRepresentation
end Classifier

/-- A category has a subobject classifier if and only if the subobjects functor is representable. -/
theorem isRepresentable_hasClassifier_iff [HasPullbacks C] :
    HasClassifier C ↔ (Subobject.presheaf C).IsRepresentable := by
  constructor <;> intro h
  · obtain ⟨⟨𝒞⟩⟩ := h
    apply RepresentableBy.isRepresentable
    exact 𝒞.representableBy
  · obtain ⟨Ω, ⟨h⟩⟩ := h
    constructor; constructor
    exact Classifier.fromRepresentation h

end Representability
end CategoryTheory
