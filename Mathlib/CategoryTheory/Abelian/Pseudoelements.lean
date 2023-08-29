/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathlib.Init.Align
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Over
import Mathlib.Algebra.Category.ModuleCat.EpiMono

#align_import category_theory.abelian.pseudoelements from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Pseudoelements in abelian categories

A *pseudoelement* of an object `X` in an abelian category `C` is an equivalence class of arrows
ending in `X`, where two arrows are considered equivalent if we can find two epimorphisms with a
common domain making a commutative square with the two arrows. While the construction shows that
pseudoelements are actually subobjects of `X` rather than "elements", it is possible to chase these
pseudoelements through commutative diagrams in an abelian category to prove exactness properties.
This is done using some "diagram-chasing metatheorems" proved in this file. In many cases, a proof
in the category of abelian groups can more or less directly be converted into a proof using
pseudoelements.

A classic application of pseudoelements are diagram lemmas like the four lemma or the snake lemma.

Pseudoelements are in some ways weaker than actual elements in a concrete category. The most
important limitation is that there is no extensionality principle: If `f g : X ⟶ Y`, then
`∀ x ∈ X, f x = g x` does not necessarily imply that `f = g` (however, if `f = 0` or `g = 0`,
it does). A corollary of this is that we can not define arrows in abelian categories by dictating
their action on pseudoelements. Thus, a usual style of proofs in abelian categories is this:
First, we construct some morphism using universal properties, and then we use diagram chasing
of pseudoelements to verify that is has some desirable property such as exactness.

It should be noted that the Freyd-Mitchell embedding theorem gives a vastly stronger notion of
pseudoelement (in particular one that gives extensionality). However, this theorem is quite
difficult to prove and probably out of reach for a formal proof for the time being.

## Main results

We define the type of pseudoelements of an object and, in particular, the zero pseudoelement.

We prove that every morphism maps the zero pseudoelement to the zero pseudoelement (`apply_zero`)
and that a zero morphism maps every pseudoelement to the zero pseudoelement (`zero_apply`).

Here are the metatheorems we provide:
* A morphism `f` is zero if and only if it is the zero function on pseudoelements.
* A morphism `f` is an epimorphism if and only if it is surjective on pseudoelements.
* A morphism `f` is a monomorphism if and only if it is injective on pseudoelements
  if and only if `∀ a, f a = 0 → f = 0`.
* A sequence `f, g` of morphisms is exact if and only if
  `∀ a, g (f a) = 0` and `∀ b, g b = 0 → ∃ a, f a = b`.
* If `f` is a morphism and `a, a'` are such that `f a = f a'`, then there is some
  pseudoelement `a''` such that `f a'' = 0` and for every `g` we have
  `g a' = 0 → g a = g a''`. We can think of `a''` as `a - a'`, but don't get too carried away
  by that: pseudoelements of an object do not form an abelian group.

## Notations

We introduce coercions from an object of an abelian category to the set of its pseudoelements
and from a morphism to the function it induces on pseudoelements.

These coercions must be explicitly enabled via local instances:
`attribute [local instance] objectToSort homToFun`

## Implementation notes

It appears that sometimes the coercion from morphisms to functions does not work, i.e.,
writing `g a` raises a "function expected" error. This error can be fixed by writing
`(g : X ⟶ Y) a`.

## References

* [F. Borceux, *Handbook of Categorical Algebra 2*][borceux-vol2]
-/


open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Abelian

open CategoryTheory.Preadditive

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C]

attribute [local instance] Over.coeFromHom

/-- This is just composition of morphisms in `C`. Another way to express this would be
    `(Over.map f).obj a`, but our definition has nicer definitional properties. -/
def app {P Q : C} (f : P ⟶ Q) (a : Over P) : Over Q :=
  a.hom ≫ f
#align category_theory.abelian.app CategoryTheory.Abelian.app

@[simp]
theorem app_hom {P Q : C} (f : P ⟶ Q) (a : Over P) : (app f a).hom = a.hom ≫ f := rfl
#align category_theory.abelian.app_hom CategoryTheory.Abelian.app_hom

/-- Two arrows `f : X ⟶ P` and `g : Y ⟶ P` are called pseudo-equal if there is some object
    `R` and epimorphisms `p : R ⟶ X` and `q : R ⟶ Y` such that `p ≫ f = q ≫ g`. -/
def PseudoEqual (P : C) (f g : Over P) : Prop :=
  ∃ (R : C) (p : R ⟶ f.1) (q : R ⟶ g.1) (_ : Epi p) (_ : Epi q), p ≫ f.hom = q ≫ g.hom
#align category_theory.abelian.pseudo_equal CategoryTheory.Abelian.PseudoEqual

theorem pseudoEqual_refl {P : C} : Reflexive (PseudoEqual P) :=
  fun f => ⟨f.1, 𝟙 f.1, 𝟙 f.1, inferInstance, inferInstance, by simp⟩
                                                                -- 🎉 no goals
#align category_theory.abelian.pseudo_equal_refl CategoryTheory.Abelian.pseudoEqual_refl

theorem pseudoEqual_symm {P : C} : Symmetric (PseudoEqual P) :=
  fun _ _ ⟨R, p, q, ep, Eq, comm⟩ => ⟨R, q, p, Eq, ep, comm.symm⟩
#align category_theory.abelian.pseudo_equal_symm CategoryTheory.Abelian.pseudoEqual_symm

variable [Abelian.{v} C]

section

/-- Pseudoequality is transitive: Just take the pullback. The pullback morphisms will
    be epimorphisms since in an abelian category, pullbacks of epimorphisms are epimorphisms. -/
theorem pseudoEqual_trans {P : C} : Transitive (PseudoEqual P) := by
  intro f g h ⟨R, p, q, ep, Eq, comm⟩ ⟨R', p', q', ep', eq', comm'⟩
  -- ⊢ PseudoEqual P f h
  refine' ⟨pullback q p', pullback.fst ≫ p, pullback.snd ≫ q', epi_comp _ _, epi_comp _ _, _⟩
  -- ⊢ (pullback.fst ≫ p) ≫ f.hom = (pullback.snd ≫ q') ≫ h.hom
  rw [Category.assoc, comm, ← Category.assoc, pullback.condition, Category.assoc, comm',
    Category.assoc]
#align category_theory.abelian.pseudo_equal_trans CategoryTheory.Abelian.pseudoEqual_trans

end

/-- The arrows with codomain `P` equipped with the equivalence relation of being pseudo-equal. -/
def Pseudoelement.setoid (P : C) : Setoid (Over P) :=
  ⟨_, ⟨pseudoEqual_refl, @pseudoEqual_symm _ _ _, @pseudoEqual_trans _ _ _ _⟩⟩
#align category_theory.abelian.pseudoelement.setoid CategoryTheory.Abelian.Pseudoelement.setoid

attribute [local instance] Pseudoelement.setoid

/-- A `Pseudoelement` of `P` is just an equivalence class of arrows ending in `P` by being
    pseudo-equal. -/
def Pseudoelement (P : C) : Type max u v :=
  Quotient (Pseudoelement.setoid P)
#align category_theory.abelian.pseudoelement CategoryTheory.Abelian.Pseudoelement

namespace Pseudoelement

/-- A coercion from an object of an abelian category to its pseudoelements. -/
def objectToSort : CoeSort C (Type max u v) :=
  ⟨fun P => Pseudoelement P⟩
#align category_theory.abelian.pseudoelement.object_to_sort CategoryTheory.Abelian.Pseudoelement.objectToSort

attribute [local instance] objectToSort

scoped[Pseudoelement] attribute [instance] CategoryTheory.Abelian.Pseudoelement.objectToSort

/-- A coercion from an arrow with codomain `P` to its associated pseudoelement. -/
def overToSort {P : C} : Coe (Over P) (Pseudoelement P) :=
  ⟨Quot.mk (PseudoEqual P)⟩
#align category_theory.abelian.pseudoelement.over_to_sort CategoryTheory.Abelian.Pseudoelement.overToSort

attribute [local instance] overToSort

theorem over_coe_def {P Q : C} (a : Q ⟶ P) : (a : Pseudoelement P) = ⟦↑a⟧ := rfl
#align category_theory.abelian.pseudoelement.over_coe_def CategoryTheory.Abelian.Pseudoelement.over_coe_def

/-- If two elements are pseudo-equal, then their composition with a morphism is, too. -/
theorem pseudoApply_aux {P Q : C} (f : P ⟶ Q) (a b : Over P) : a ≈ b → app f a ≈ app f b :=
  fun ⟨R, p, q, ep, Eq, comm⟩ =>
  ⟨R, p, q, ep, Eq, show p ≫ a.hom ≫ f = q ≫ b.hom ≫ f by rw [reassoc_of% comm]⟩
                                                          -- 🎉 no goals
#align category_theory.abelian.pseudoelement.pseudo_apply_aux CategoryTheory.Abelian.Pseudoelement.pseudoApply_aux

/-- A morphism `f` induces a function `pseudoApply f` on pseudoelements. -/
def pseudoApply {P Q : C} (f : P ⟶ Q) : P → Q :=
  Quotient.map (fun g : Over P => app f g) (pseudoApply_aux f)
#align category_theory.abelian.pseudoelement.pseudo_apply CategoryTheory.Abelian.Pseudoelement.pseudoApply

/-- A coercion from morphisms to functions on pseudoelements. -/
def homToFun {P Q : C} : CoeFun (P ⟶ Q) fun _ => P → Q :=
  ⟨pseudoApply⟩
#align category_theory.abelian.pseudoelement.hom_to_fun CategoryTheory.Abelian.Pseudoelement.homToFun

attribute [local instance] homToFun

scoped[Pseudoelement] attribute [instance] CategoryTheory.Abelian.Pseudoelement.homToFun

theorem pseudoApply_mk' {P Q : C} (f : P ⟶ Q) (a : Over P) : f ⟦a⟧ = ⟦↑(a.hom ≫ f)⟧ := rfl
#align category_theory.abelian.pseudoelement.pseudo_apply_mk CategoryTheory.Abelian.Pseudoelement.pseudoApply_mk'

/-- Applying a pseudoelement to a composition of morphisms is the same as composing
    with each morphism. Sadly, this is not a definitional equality, but at least it is
    true. -/
theorem comp_apply {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) (a : P) : (f ≫ g) a = g (f a) :=
  Quotient.inductionOn a fun x =>
    Quotient.sound <| by
      simp only [app]
      -- ⊢ Over.mk (x.hom ≫ f ≫ g) ≈ Over.mk ((Over.mk (x.hom ≫ f)).hom ≫ g)
      rw [← Category.assoc, Over.coe_hom]
      -- 🎉 no goals
#align category_theory.abelian.pseudoelement.comp_apply CategoryTheory.Abelian.Pseudoelement.comp_apply

/-- Composition of functions on pseudoelements is composition of morphisms. -/
theorem comp_comp {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) : g ∘ f = f ≫ g :=
  funext fun _ => (comp_apply _ _ _).symm
#align category_theory.abelian.pseudoelement.comp_comp CategoryTheory.Abelian.Pseudoelement.comp_comp

section Zero

/-!
In this section we prove that for every `P` there is an equivalence class that contains
precisely all the zero morphisms ending in `P` and use this to define *the* zero
pseudoelement.
-/


section

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

/-- The arrows pseudo-equal to a zero morphism are precisely the zero morphisms. -/
theorem pseudoZero_aux {P : C} (Q : C) (f : Over P) : f ≈ (0 : Q ⟶ P) ↔ f.hom = 0 :=
  ⟨fun ⟨R, p, q, ep, _, comm⟩ => zero_of_epi_comp p (by simp [comm]), fun hf =>
                                                        -- 🎉 no goals
    ⟨biprod f.1 Q, biprod.fst, biprod.snd, inferInstance, inferInstance, by
      rw [hf, Over.coe_hom, HasZeroMorphisms.comp_zero, HasZeroMorphisms.comp_zero]⟩⟩
      -- 🎉 no goals
#align category_theory.abelian.pseudoelement.pseudo_zero_aux CategoryTheory.Abelian.Pseudoelement.pseudoZero_aux

end

theorem zero_eq_zero' {P Q R : C} :
    (⟦((0 : Q ⟶ P) : Over P)⟧ : Pseudoelement P) = ⟦((0 : R ⟶ P) : Over P)⟧ :=
  Quotient.sound <| (pseudoZero_aux R _).2 rfl
#align category_theory.abelian.pseudoelement.zero_eq_zero' CategoryTheory.Abelian.Pseudoelement.zero_eq_zero'

/-- The zero pseudoelement is the class of a zero morphism. -/
def pseudoZero {P : C} : P :=
  ⟦(0 : P ⟶ P)⟧
#align category_theory.abelian.pseudoelement.pseudo_zero CategoryTheory.Abelian.Pseudoelement.pseudoZero

-- Porting note: in mathlib3, we couldn't make this an instance
-- as it would have fired on `coe_sort`.
-- However now that coercions are treated differently, this is a structural instance triggered by
-- the appearance of `Pseudoelement`.
instance hasZero {P : C} : Zero P :=
  ⟨pseudoZero⟩
#align category_theory.abelian.pseudoelement.has_zero CategoryTheory.Abelian.Pseudoelement.hasZero

instance {P : C} : Inhabited P :=
  ⟨0⟩

theorem pseudoZero_def {P : C} : (0 : Pseudoelement P) = ⟦↑(0 : P ⟶ P)⟧ := rfl
#align category_theory.abelian.pseudoelement.pseudo_zero_def CategoryTheory.Abelian.Pseudoelement.pseudoZero_def

@[simp]
theorem zero_eq_zero {P Q : C} : ⟦((0 : Q ⟶ P) : Over P)⟧ = (0 : Pseudoelement P) :=
  zero_eq_zero'
#align category_theory.abelian.pseudoelement.zero_eq_zero CategoryTheory.Abelian.Pseudoelement.zero_eq_zero

/-- The pseudoelement induced by an arrow is zero precisely when that arrow is zero. -/
theorem pseudoZero_iff {P : C} (a : Over P) : a = (0 : P) ↔ a.hom = 0 := by
  rw [← pseudoZero_aux P a]
  -- ⊢ Quot.mk (PseudoEqual P) a = 0 ↔ a ≈ Over.mk 0
  exact Quotient.eq'
  -- 🎉 no goals
#align category_theory.abelian.pseudoelement.pseudo_zero_iff CategoryTheory.Abelian.Pseudoelement.pseudoZero_iff

end Zero

open Pseudoelement

/-- Morphisms map the zero pseudoelement to the zero pseudoelement. -/
@[simp]
theorem apply_zero {P Q : C} (f : P ⟶ Q) : f 0 = 0 := by
  rw [pseudoZero_def, pseudoApply_mk']
  -- ⊢ Quotient.mk (setoid Q) (Over.mk ((Over.mk 0).hom ≫ f)) = 0
  simp
  -- 🎉 no goals
#align category_theory.abelian.pseudoelement.apply_zero CategoryTheory.Abelian.Pseudoelement.apply_zero

/-- The zero morphism maps every pseudoelement to 0. -/
@[simp]
theorem zero_apply {P : C} (Q : C) (a : P) : (0 : P ⟶ Q) a = 0 :=
  Quotient.inductionOn a fun a' => by
    rw [pseudoZero_def, pseudoApply_mk']
    -- ⊢ Quotient.mk (setoid Q) (Over.mk (a'.hom ≫ 0)) = Quotient.mk (setoid Q) (Over …
    simp
    -- 🎉 no goals
#align category_theory.abelian.pseudoelement.zero_apply CategoryTheory.Abelian.Pseudoelement.zero_apply

/-- An extensionality lemma for being the zero arrow. -/
theorem zero_morphism_ext {P Q : C} (f : P ⟶ Q) : (∀ a, f a = 0) → f = 0 := fun h => by
  rw [← Category.id_comp f]
  -- ⊢ 𝟙 P ≫ f = 0
  exact (pseudoZero_iff (𝟙 P ≫ f : Over Q)).1 (h (𝟙 P))
  -- 🎉 no goals
#align category_theory.abelian.pseudoelement.zero_morphism_ext CategoryTheory.Abelian.Pseudoelement.zero_morphism_ext

theorem zero_morphism_ext' {P Q : C} (f : P ⟶ Q) : (∀ a, f a = 0) → 0 = f :=
  Eq.symm ∘ zero_morphism_ext f
#align category_theory.abelian.pseudoelement.zero_morphism_ext' CategoryTheory.Abelian.Pseudoelement.zero_morphism_ext'

-- Porting note: these are no longer valid as `ext` lemmas.
-- scoped[Pseudoelement]
--   attribute [ext]
--     CategoryTheory.Abelian.Pseudoelement.zero_morphism_ext
--     CategoryTheory.Abelian.Pseudoelement.zero_morphism_ext'

theorem eq_zero_iff {P Q : C} (f : P ⟶ Q) : f = 0 ↔ ∀ a, f a = 0 :=
  ⟨fun h a => by simp [h], zero_morphism_ext _⟩
                 -- 🎉 no goals
#align category_theory.abelian.pseudoelement.eq_zero_iff CategoryTheory.Abelian.Pseudoelement.eq_zero_iff

/-- A monomorphism is injective on pseudoelements. -/
theorem pseudo_injective_of_mono {P Q : C} (f : P ⟶ Q) [Mono f] : Function.Injective f := by
  intro abar abar'
  -- ⊢ pseudoApply f abar = pseudoApply f abar' → abar = abar'
  refine' Quotient.inductionOn₂ abar abar' fun a a' ha => _
  -- ⊢ Quotient.mk (setoid P) a = Quotient.mk (setoid P) a'
  apply Quotient.sound
  -- ⊢ a ≈ a'
  have : ⟦(a.hom ≫ f : Over Q)⟧ = ⟦↑(a'.hom ≫ f)⟧ := by convert ha
  -- ⊢ a ≈ a'
  have ⟨R, p, q, ep, Eq, comm⟩ := Quotient.exact this
  -- ⊢ a ≈ a'
  exact ⟨R, p, q, ep, Eq, (cancel_mono f).1 <| by
    simp only [Category.assoc]
    exact comm⟩
#align category_theory.abelian.pseudoelement.pseudo_injective_of_mono CategoryTheory.Abelian.Pseudoelement.pseudo_injective_of_mono

/-- A morphism that is injective on pseudoelements only maps the zero element to zero. -/
theorem zero_of_map_zero {P Q : C} (f : P ⟶ Q) : Function.Injective f → ∀ a, f a = 0 → a = 0 :=
  fun h a ha => by
  rw [← apply_zero f] at ha
  -- ⊢ a = 0
  exact h ha
  -- 🎉 no goals
#align category_theory.abelian.pseudoelement.zero_of_map_zero CategoryTheory.Abelian.Pseudoelement.zero_of_map_zero

/-- A morphism that only maps the zero pseudoelement to zero is a monomorphism. -/
theorem mono_of_zero_of_map_zero {P Q : C} (f : P ⟶ Q) : (∀ a, f a = 0 → a = 0) → Mono f :=
  fun h => (mono_iff_cancel_zero _).2 fun _ g hg =>
    (pseudoZero_iff (g : Over P)).1 <|
      h _ <| show f g = 0 from (pseudoZero_iff (g ≫ f : Over Q)).2 hg
#align category_theory.abelian.pseudoelement.mono_of_zero_of_map_zero CategoryTheory.Abelian.Pseudoelement.mono_of_zero_of_map_zero

section

/-- An epimorphism is surjective on pseudoelements. -/
theorem pseudo_surjective_of_epi {P Q : C} (f : P ⟶ Q) [Epi f] : Function.Surjective f :=
  fun qbar =>
  Quotient.inductionOn qbar fun q =>
    ⟨((pullback.fst : pullback f q.hom ⟶ P) : Over P),
      Quotient.sound <|
        ⟨pullback f q.hom, 𝟙 (pullback f q.hom), pullback.snd, inferInstance, inferInstance, by
          rw [Category.id_comp, ← pullback.condition, app_hom, Over.coe_hom]⟩⟩
          -- 🎉 no goals
#align category_theory.abelian.pseudoelement.pseudo_surjective_of_epi CategoryTheory.Abelian.Pseudoelement.pseudo_surjective_of_epi

end

/-- A morphism that is surjective on pseudoelements is an epimorphism. -/
theorem epi_of_pseudo_surjective {P Q : C} (f : P ⟶ Q) : Function.Surjective f → Epi f := by
  intro h
  -- ⊢ Epi f
  have ⟨pbar, hpbar⟩ := h (𝟙 Q)
  -- ⊢ Epi f
  have ⟨p, hp⟩ := Quotient.exists_rep pbar
  -- ⊢ Epi f
  have : ⟦(p.hom ≫ f : Over Q)⟧ = ⟦↑(𝟙 Q)⟧ := by
    rw [← hp] at hpbar
    exact hpbar
  have ⟨R, x, y, _, ey, comm⟩ := Quotient.exact this
  -- ⊢ Epi f
  apply @epi_of_epi_fac _ _ _ _ _ (x ≫ p.hom) f y ey
  -- ⊢ (x ≫ p.hom) ≫ f = y
  dsimp at comm
  -- ⊢ (x ≫ p.hom) ≫ f = y
  rw [Category.assoc, comm]
  -- ⊢ y ≫ 𝟙 Q = y
  apply Category.comp_id
  -- 🎉 no goals
#align category_theory.abelian.pseudoelement.epi_of_pseudo_surjective CategoryTheory.Abelian.Pseudoelement.epi_of_pseudo_surjective

section

/-- Two morphisms in an exact sequence are exact on pseudoelements. -/
theorem pseudo_exact_of_exact {P Q R : C} {f : P ⟶ Q} {g : Q ⟶ R} (h : Exact f g) :
    (∀ a, g (f a) = 0) ∧ ∀ b, g b = 0 → ∃ a, f a = b :=
  ⟨fun a => by
    rw [← comp_apply, h.w]
    -- ⊢ pseudoApply 0 a = 0
    exact zero_apply _ _, fun b' =>
    -- 🎉 no goals
    Quotient.inductionOn b' fun b hb => by
      have hb' : b.hom ≫ g = 0 := (pseudoZero_iff _).1 hb
      -- ⊢ ∃ a, pseudoApply f a = Quotient.mk (setoid Q) b
      -- By exactness, `b` factors through `im f = ker g` via some `c`.
      obtain ⟨c, hc⟩ := KernelFork.IsLimit.lift' (isLimitImage f g h) _ hb'
      -- ⊢ ∃ a, pseudoApply f a = Quotient.mk (setoid Q) b
      -- We compute the pullback of the map into the image and `c`.
      -- The pseudoelement induced by the first pullback map will be our preimage.
      use (pullback.fst : pullback (Abelian.factorThruImage f) c ⟶ P)
      -- ⊢ pseudoApply f (Quot.mk (PseudoEqual P) (Over.mk pullback.fst)) = Quotient.mk …
      -- It remains to show that the image of this element under `f` is pseudo-equal to `b`.
      apply Quotient.sound
      -- ⊢ (fun g => app f g) (Over.mk pullback.fst) ≈ b
      -- `pullback.snd` is an epimorphism because the map onto the image is!
      refine'
        ⟨pullback (Abelian.factorThruImage f) c, 𝟙 _, pullback.snd, inferInstance, inferInstance, _⟩
      -- Now we can verify that the diagram commutes.
      calc
        𝟙 (pullback (Abelian.factorThruImage f) c) ≫ pullback.fst ≫ f = pullback.fst ≫ f :=
          Category.id_comp _
        _ = pullback.fst ≫ Abelian.factorThruImage f ≫ kernel.ι (cokernel.π f) := by
          rw [Abelian.image.fac]
        _ = (pullback.snd ≫ c) ≫ kernel.ι (cokernel.π f) := by
          rw [← Category.assoc, pullback.condition]
        _ = pullback.snd ≫ b.hom := by
          rw [Category.assoc]
          congr
        ⟩
#align category_theory.abelian.pseudoelement.pseudo_exact_of_exact CategoryTheory.Abelian.Pseudoelement.pseudo_exact_of_exact

end

theorem apply_eq_zero_of_comp_eq_zero {P Q R : C} (f : Q ⟶ R) (a : P ⟶ Q) : a ≫ f = 0 → f a = 0 :=
  fun h => by simp [over_coe_def, pseudoApply_mk', Over.coe_hom, h]
              -- 🎉 no goals
#align category_theory.abelian.pseudoelement.apply_eq_zero_of_comp_eq_zero CategoryTheory.Abelian.Pseudoelement.apply_eq_zero_of_comp_eq_zero

section

/-- If two morphisms are exact on pseudoelements, they are exact. -/
theorem exact_of_pseudo_exact {P Q R : C} (f : P ⟶ Q) (g : Q ⟶ R) :
    ((∀ a, g (f a) = 0) ∧ ∀ b, g b = 0 → ∃ a, f a = b) → Exact f g :=
  fun ⟨h₁, h₂⟩ => (Abelian.exact_iff _ _).2
    ⟨zero_morphism_ext _ fun a => by rw [comp_apply, h₁ a], by
                                     -- 🎉 no goals
      -- If we apply `g` to the pseudoelement induced by its kernel, we get 0 (of course!).
      have : g (kernel.ι g) = 0 := apply_eq_zero_of_comp_eq_zero _ _ (kernel.condition _)
      -- ⊢ kernel.ι g ≫ cokernel.π f = 0
      -- By pseudo-exactness, we get a preimage.
      obtain ⟨a', ha⟩ := h₂ _ this
      -- ⊢ kernel.ι g ≫ cokernel.π f = 0
      obtain ⟨a, ha'⟩ := Quotient.exists_rep a'
      -- ⊢ kernel.ι g ≫ cokernel.π f = 0
      rw [← ha'] at ha
      -- ⊢ kernel.ι g ≫ cokernel.π f = 0
      obtain ⟨Z, r, q, _, eq, comm⟩ := Quotient.exact ha
      -- ⊢ kernel.ι g ≫ cokernel.π f = 0
      -- Consider the pullback of `kernel.ι (cokernel.π f)` and `kernel.ι g`.
      -- The commutative diagram given by the pseudo-equality `f a = b` induces
      -- a cone over this pullback, so we get a factorization `z`.
      obtain ⟨z, _, hz₂⟩ := @pullback.lift' _ _ _ _ _ _ (kernel.ι (cokernel.π f)) (kernel.ι g) _
        (r ≫ a.hom ≫ Abelian.factorThruImage f) q (by
          simp only [Category.assoc, Abelian.image.fac]
          exact comm)
      -- Let's give a name to the second pullback morphism.
      let j : pullback (kernel.ι (cokernel.π f)) (kernel.ι g) ⟶ kernel g := pullback.snd
      -- ⊢ kernel.ι g ≫ cokernel.π f = 0
      -- Since `q` is an epimorphism, in particular this means that `j` is an epimorphism.
      haveI pe : Epi j := epi_of_epi_fac hz₂
      -- ⊢ kernel.ι g ≫ cokernel.π f = 0
      -- But it is also a monomorphism, because `kernel.ι (cokernel.π f)` is: A kernel is
      -- always a monomorphism and the pullback of a monomorphism is a monomorphism.
      -- But mono + epi = iso, so `j` is an isomorphism.
      haveI : IsIso j := isIso_of_mono_of_epi _
      -- ⊢ kernel.ι g ≫ cokernel.π f = 0
      -- But then `kernel.ι g` can be expressed using all of the maps of the pullback square, and we
      -- are done.
      rw [(Iso.eq_inv_comp (asIso j)).2 pullback.condition.symm]
      -- ⊢ ((asIso j).inv ≫ pullback.fst ≫ kernel.ι (cokernel.π f)) ≫ cokernel.π f = 0
      simp only [Category.assoc, kernel.condition, HasZeroMorphisms.comp_zero]⟩
      -- 🎉 no goals
#align category_theory.abelian.pseudoelement.exact_of_pseudo_exact CategoryTheory.Abelian.Pseudoelement.exact_of_pseudo_exact

end

/-- If two pseudoelements `x` and `y` have the same image under some morphism `f`, then we can form
    their "difference" `z`. This pseudoelement has the properties that `f z = 0` and for all
    morphisms `g`, if `g y = 0` then `g z = g x`. -/
theorem sub_of_eq_image {P Q : C} (f : P ⟶ Q) (x y : P) :
    f x = f y → ∃ z, f z = 0 ∧ ∀ (R : C) (g : P ⟶ R), (g : P ⟶ R) y = 0 → g z = g x :=
  Quotient.inductionOn₂ x y fun a a' h =>
    match Quotient.exact h with
    | ⟨R, p, q, ep, _, comm⟩ =>
      let a'' : R ⟶ P := ↑(p ≫ a.hom) - ↑(q ≫ a'.hom)
      ⟨a'',
        ⟨show ⟦(a'' ≫ f : Over Q)⟧ = ⟦↑(0 : Q ⟶ Q)⟧ by
            dsimp at comm
            -- ⊢ Quotient.mk (setoid Q) (Over.mk (a'' ≫ f)) = Quotient.mk (setoid Q) (Over.mk …
            simp [sub_eq_zero.2 comm],
            -- 🎉 no goals
          fun Z g hh => by
          obtain ⟨X, p', q', ep', _, comm'⟩ := Quotient.exact hh
          -- ⊢ pseudoApply g (Quot.mk (PseudoEqual P) (Over.mk a'')) = pseudoApply g (Quoti …
          have : a'.hom ≫ g = 0 := by
            apply (epi_iff_cancel_zero _).1 ep' _ (a'.hom ≫ g)
            simpa using comm'
          apply Quotient.sound
          -- ⊢ (fun g_1 => app g g_1) (Over.mk a'') ≈ (fun g_1 => app g g_1) a
          -- Can we prevent quotient.sound from giving us this weird `coe_b` thingy?
          change app g (a'' : Over P) ≈ app g a
          -- ⊢ app g (Over.mk a'') ≈ app g a
          exact ⟨R, 𝟙 R, p, inferInstance, ep, by simp [sub_eq_add_neg, this]⟩⟩⟩
          -- 🎉 no goals
#align category_theory.abelian.pseudoelement.sub_of_eq_image CategoryTheory.Abelian.Pseudoelement.sub_of_eq_image

variable [Limits.HasPullbacks C]

/-- If `f : P ⟶ R` and `g : Q ⟶ R` are morphisms and `p : P` and `q : Q` are pseudoelements such
    that `f p = g q`, then there is some `s : pullback f g` such that `fst s = p` and `snd s = q`.

    Remark: Borceux claims that `s` is unique, but this is false. See
    `Counterexamples/Pseudoelement` for details. -/
theorem pseudo_pullback {P Q R : C} {f : P ⟶ R} {g : Q ⟶ R} {p : P} {q : Q} :
    f p = g q →
      ∃ s, (pullback.fst : pullback f g ⟶ P) s = p ∧ (pullback.snd : pullback f g ⟶ Q) s = q :=
  Quotient.inductionOn₂ p q fun x y h => by
    obtain ⟨Z, a, b, ea, eb, comm⟩ := Quotient.exact h
    -- ⊢ ∃ s, pseudoApply pullback.fst s = Quotient.mk (setoid P) x ∧ pseudoApply pul …
    obtain ⟨l, hl₁, hl₂⟩ := @pullback.lift' _ _ _ _ _ _ f g _ (a ≫ x.hom) (b ≫ y.hom) (by
      simp only [Category.assoc]
      exact comm)
    exact ⟨l, ⟨Quotient.sound ⟨Z, 𝟙 Z, a, inferInstance, ea, by rwa [Category.id_comp]⟩,
      Quotient.sound ⟨Z, 𝟙 Z, b, inferInstance, eb, by rwa [Category.id_comp]⟩⟩⟩
#align category_theory.abelian.pseudoelement.pseudo_pullback CategoryTheory.Abelian.Pseudoelement.pseudo_pullback

section Module

/-- In the category `Module R`, if `x` and `y` are pseudoequal, then the range of the associated
morphisms is the same. -/
theorem ModuleCat.eq_range_of_pseudoequal {R : Type*} [CommRing R] {G : ModuleCat R} {x y : Over G}
    (h : PseudoEqual G x y) : LinearMap.range x.hom = LinearMap.range y.hom := by
  obtain ⟨P, p, q, hp, hq, H⟩ := h
  -- ⊢ LinearMap.range x.hom = LinearMap.range y.hom
  refine' Submodule.ext fun a => ⟨fun ha => _, fun ha => _⟩
  -- ⊢ a ∈ LinearMap.range y.hom
  · obtain ⟨a', ha'⟩ := ha
    -- ⊢ a ∈ LinearMap.range y.hom
    obtain ⟨a'', ha''⟩ := (ModuleCat.epi_iff_surjective p).1 hp a'
    -- ⊢ a ∈ LinearMap.range y.hom
    refine' ⟨q a'', _⟩
    -- ⊢ ↑y.hom (↑q a'') = a
    rw [← LinearMap.comp_apply, ← ModuleCat.comp_def, ← H, ModuleCat.comp_def, LinearMap.comp_apply,
      ha'', ha']
  · obtain ⟨a', ha'⟩ := ha
    -- ⊢ a ∈ LinearMap.range x.hom
    obtain ⟨a'', ha''⟩ := (ModuleCat.epi_iff_surjective q).1 hq a'
    -- ⊢ a ∈ LinearMap.range x.hom
    refine' ⟨p a'', _⟩
    -- ⊢ ↑x.hom (↑p a'') = a
    rw [← LinearMap.comp_apply, ← ModuleCat.comp_def, H, ModuleCat.comp_def, LinearMap.comp_apply,
      ha'', ha']
set_option linter.uppercaseLean3 false in
#align category_theory.abelian.pseudoelement.Module.eq_range_of_pseudoequal CategoryTheory.Abelian.Pseudoelement.ModuleCat.eq_range_of_pseudoequal

end Module

end Pseudoelement

end CategoryTheory.Abelian
