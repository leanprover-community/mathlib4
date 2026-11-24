import Mathlib.Tactic.Simps.Generalized
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-! # A worked example of `simps!!`: equalizers

How the attributes fit together, for `equalizer f g`. There are four kinds of registrations:

1. `simps_proj comp` on a *field-like* morphism, here `equalizer.ι f g : equalizer f g ⟶ X`. This
   registers `h ↦ h ≫ equalizer.ι f g` as a generalized projection of morphisms
   `h : W ⟶ equalizer f g`. Every term of that type that `simps!!` meets, whether the definition
   itself or one of its fields (like `e.hom` for an iso `e`), gets a lemma `h ≫ ι = …`. These are
   *recursive*: their right-hand sides are themselves inspected for further generalized
   projections (although for `ι` there are none, `X` being an arbitrary object).
2. `simps_proj precomp noRecurse` on the *universal property*, here `equalizer.lift`, which
   registers `h ↦ equalizer.lift k w ≫ h` on morphisms `h : equalizer f g ⟶ V`. Its name goes
   before the last component of the lemma name (`e_lift_hom`, not `e_hom_lift`), and `noRecurse`
   stops it from being applied to terms that already came out of another generalized projection
   (`lift ≫ e.hom ≫ ι` follows from `e_hom_ι` and `lift_ι`).
3. `simps_eta` on the η-rule `h = equalizer.lift (h ≫ ι) _`. The right-hand side of a lemma from a
   `noRecurse` projection is computed by rewriting the left-hand side with it and simplifying, so
   that `lift k w ≫ e.hom` comes out as `lift k' w'` when the target is an equalizer too.
4. `simps_proj` on functions out of the structures involved, `Fork.ι` and `Fork.IsLimit.lift`,
   which are generalized projections as they are; `initialize_simps_projections!!` declares that
   they replace the genuine projections `Cone.π` and `IsLimit.lift`.

The `rules` of a projection are added to the simp set used for the right-hand sides of its
lemmas, and `attr` is applied to those lemmas.
-/

open CategoryTheory Limits

namespace SimpsGenEqualizerTest

variable {C : Type*} [Category* C] {X Y : C} {f g : X ⟶ Y}

/-! ### Registration -/

-- 1. A field-like projection: composing a morphism into an equalizer with `equalizer.ι`.
attribute [local simps_proj comp (rules := equalizer.lift_ι) (attr := reassoc (attr := simp))]
  equalizer.ι

-- 2. The universal property: precomposing a morphism out of an equalizer with a `lift`.
attribute [local simps_proj precomp noRecurse (rules := equalizer.lift_ι)
  (attr := reassoc (attr := simp))] equalizer.lift

/-- 3. The η-rule. -/
@[simps_eta]
theorem equalizer_eta [HasEqualizer f g] {W : C} (h : W ⟶ equalizer f g) :
    h = equalizer.lift (h ≫ equalizer.ι f g)
      (by rw [Category.assoc, Category.assoc, equalizer.condition]) := by
  ext; simp

-- 4. Custom projections of forks and of limit forks.
attribute [local simps_proj] Fork.ι Fork.IsLimit.lift

initialize_simps_projections!! Fork (π → ι)
initialize_simps_projections!! Fork.IsLimit (lift → lift)

/-! ### Definitions -/

/-- A morphism into an equalizer. -/
@[simps!!]
noncomputable def toEq [HasEqualizer f g] {W : C} (k : W ⟶ X) (w : k ≫ f = k ≫ g) :
    W ⟶ equalizer f g :=
  equalizer.lift k w

/-- An isomorphism between two equalizers, given by its components. -/
@[simps!!]
noncomputable def eqSwap [HasEqualizer f g] [HasEqualizer g f] :
    equalizer f g ≅ equalizer g f where
  hom := equalizer.lift (equalizer.ι f g) (equalizer.condition f g).symm
  inv := equalizer.lift (equalizer.ι g f) (equalizer.condition g f).symm

/-- An isomorphism between an equalizer and an object that is not one, given by a Mathlib
definition (so its right-hand sides come from Mathlib's lemmas about it). -/
@[simps!!]
noncomputable def selfIso [HasEqualizer f f] : equalizer f f ≅ X :=
  equalizer.isoSourceOfSelf f

/-- A fork, and a proof that it is a limit. -/
@[simps!!]
def fork {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) : Fork f g := Fork.ofι ι w

@[simps!!]
def forkIsLimit {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g) [Mono ι]
    (lift : ∀ {W : C} (k : W ⟶ X), k ≫ f = k ≫ g → (W ⟶ P))
    (fac : ∀ {W : C} (k : W ⟶ X) (hk : k ≫ f = k ≫ g), lift k hk ≫ ι = k) :
    IsLimit (Fork.ofι ι w) :=
  Fork.IsLimit.mk _ (fun s => lift s.ι s.condition) (fun s => fac _ _)
    (fun s m hm => by rw [← cancel_mono ι, fac]; exact hm)

/-! ### The generated lemmas -/

/--
info: SimpsGenEqualizerTest.toEq_ι.{v_1, u_1} {C : Type u_1} [Category.{v_1, u_1} C] {X Y : C} {f g : X ⟶ Y}
  [HasEqualizer f g] {W : C} (k : W ⟶ X) (w : k ≫ f = k ≫ g) : toEq k w ≫ equalizer.ι f g = k
-/
#guard_msgs in #check toEq_ι

/--
info: SimpsGenEqualizerTest.eqSwap_hom_ι.{v_1, u_1} {C : Type u_1} [Category.{v_1, u_1} C] {X Y : C} {f g : X ⟶ Y}
  [HasEqualizer f g] [HasEqualizer g f] : eqSwap.hom ≫ equalizer.ι g f = equalizer.ι f g
-/
#guard_msgs in #check eqSwap_hom_ι

/--
info: SimpsGenEqualizerTest.eqSwap_lift_hom.{v_1, u_1} {C : Type u_1} [Category.{v_1, u_1} C] {X Y : C} {f g : X ⟶ Y}
  [HasEqualizer f g] [HasEqualizer g f] {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) :
  equalizer.lift k h ≫ eqSwap.hom = equalizer.lift k ⋯
-/
#guard_msgs in #check eqSwap_lift_hom

/--
info: SimpsGenEqualizerTest.eqSwap_lift_hom_assoc.{v_1, u_1} {C : Type u_1} [Category.{v_1, u_1} C] {X Y : C} {f g : X ⟶ Y}
  [HasEqualizer f g] [HasEqualizer g f] {W : C} (k : W ⟶ X) (h : k ≫ f = k ≫ g) {Z : C} (h✝ : equalizer g f ⟶ Z) :
  equalizer.lift k h ≫ eqSwap.hom ≫ h✝ = equalizer.lift k ⋯ ≫ h✝
-/
#guard_msgs in #check eqSwap_lift_hom_assoc

section
variable [HasEqualizer f g] [HasEqualizer g f] {W : C} (k : W ⟶ X)

example : eqSwap.inv ≫ equalizer.ι f g = equalizer.ι g f := eqSwap_inv_ι
example (w : k ≫ g = k ≫ f) : equalizer.lift k w ≫ eqSwap.inv = equalizer.lift k w.symm :=
  eqSwap_lift_inv k w
-- the generated lemmas are `simp` lemmas, so `simp` proves the round trips
example (w : k ≫ f = k ≫ g) :
    equalizer.lift k w ≫ eqSwap.hom ≫ eqSwap.inv = equalizer.lift k w := by
  simp

end

section
variable [HasEqualizer f f] {W : C} (k : W ⟶ X) (w : k ≫ f = k ≫ f)

example : equalizer.lift k w ≫ selfIso.hom = k := selfIso_lift_hom k w
example : selfIso.inv ≫ equalizer.ι f f = 𝟙 X := selfIso_inv_ι
end

section
variable {P : C} (ι : P ⟶ X) (w : ι ≫ f = ι ≫ g)

example : (fork ι w).pt = P := fork_pt ι w
example : (fork ι w).ι = ι := fork_ι ι w

variable [Mono ι] (lift : ∀ {W : C} (k : W ⟶ X), k ≫ f = k ≫ g → (W ⟶ P))
    (fac : ∀ {W : C} (k : W ⟶ X) (hk : k ≫ f = k ≫ g), lift k hk ≫ ι = k)

example {W : C} (k : W ⟶ X) (hk : k ≫ f = k ≫ g) :
    Fork.IsLimit.lift (forkIsLimit ι w lift fac) k hk = lift k hk :=
  forkIsLimit_lift ι w lift fac k hk
end

/-! ### Kernels: overlapping registrations

`kernel f` unfolds (reducibly) to `equalizer f 0`, so the registrations for equalizers above apply
to morphisms into and out of kernels. Registrations for kernels themselves are more specific
(`0` instead of `g`), so they take precedence over those with the same names (`ι`, `lift`), and so
does the η-rule. -/

section Kernel

variable [HasZeroMorphisms C]

attribute [local simps_proj comp (attr := reassoc (attr := simp))] kernel.ι

attribute [local simps_proj precomp noRecurse (attr := reassoc (attr := simp))] kernel.lift

@[simps_eta]
theorem kernel_eta (f : X ⟶ Y) [HasKernel f] {W : C} (h : W ⟶ kernel f) :
    h = kernel.lift f (h ≫ kernel.ι f) (by simp) := by
  ext; simp

variable {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel f] [Mono g]

@[simps!!]
noncomputable def kIso [HasKernel (f ≫ g)] : kernel (f ≫ g) ≅ kernel f := kernelCompMono f g

/--
info: SimpsGenEqualizerTest.kIso_hom_ι.{v_1, u_1} {C : Type u_1} [Category.{v_1, u_1} C] {X Y : C} [HasZeroMorphisms C]
  {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel f] [Mono g] [HasKernel (f ≫ g)] :
  (kIso f g).hom ≫ kernel.ι f = kernel.ι (f ≫ g)
-/
#guard_msgs in #check kIso_hom_ι

/--
info: SimpsGenEqualizerTest.kIso_lift_hom.{v_1, u_1} {C : Type u_1} [Category.{v_1, u_1} C] {X Y : C} [HasZeroMorphisms C]
  {Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [HasKernel f] [Mono g] [HasKernel (f ≫ g)] {W : C} (k : W ⟶ X) (h : k ≫ f ≫ g = 0) :
  kernel.lift (f ≫ g) k h ≫ (kIso f g).hom = kernel.lift f k ⋯
-/
#guard_msgs in #check kIso_lift_hom

example [HasKernel (f ≫ g)] : (kIso f g).inv ≫ kernel.ι (f ≫ g) = kernel.ι f := kIso_inv_ι f g

end Kernel

end SimpsGenEqualizerTest
