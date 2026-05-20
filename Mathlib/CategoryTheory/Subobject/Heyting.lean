/-
Copyright (c) 2026 Chris Brink. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Brink
-/
module

public import Mathlib.CategoryTheory.Subobject.Classifier.Defs
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.Order.Heyting.Basic

/-!
# Heyting algebra structure on `Subobject X` for elementary topoi

We construct the canonical Heyting-algebra structure on the lattice
`Subobject X` of subobjects of an object `X` in any category satisfying the
elementary-topos hypothesis bundle.  The implication is the *residual*
defined by an equalizer of characteristic morphisms, following Mac Lane and
Moerdijk, *Sheaves in Geometry and Logic*, IV.6 Proposition 2.

## Main construction

For `P Q : Subobject X`, the residual is
```
residual P Q := Subobject.mk (equalizer.ι (χ (P ⊓ Q).arrow) (χ P.arrow))
```
i.e. the equalizer of the characteristic morphisms of `P ⊓ Q` and `P`,
viewed as parallel arrows `X ⇉ Ω`.  Conceptually: the largest subobject of
`X` on which `P ⊓ Q` and `P` are classified by the same morphism — the part
of `X` on which `P` implies `Q`.

## Main result

* `le_residual_iff_inf_le` —
  the load-bearing Galois connection
  `R ≤ residual P Q ↔ R ⊓ P ≤ Q`.

* `heytingAlgebra` —
  the `HeytingAlgebra (Subobject X)` instance assembled from `residual` and
  the Galois connection, with `himp := residual` and the pseudo-complement
  `compl P := residual P ⊥` automatic via `himp_bot := rfl`.

## Hypothesis bundle

```
[HasSubobjectClassifier C] [HasPullbacks C] [HasEqualizers C]
[HasInitial C] [HasImages C] [HasBinaryCoproducts C] [InitialMonoClass C]
```

These together are entailed by `C` being an elementary topos.  The roles:

* `HasSubobjectClassifier C` — supplies `χ : (U ⟶ X) → (X ⟶ Ω)` and the
  Beck-Chevalley identity `(pullback f).obj S = (pullback (f ≫ χ S.arrow))
  .obj truth_as_subobject`, used in both halves of the Galois proof.
* `HasPullbacks C` — `SemilatticeInf (Subobject X)` and `OrderTop`.
* `HasInitial C` + `InitialMonoClass C` — `OrderBot (Subobject X)`.
* `HasImages C` + `HasBinaryCoproducts C` — `SemilatticeSup (Subobject X)`.
* `HasEqualizers C` — the equalizer underlying the residual.

## References

* [S. Mac Lane and I. Moerdijk, *Sheaves in Geometry and Logic*][MM92],
  Chapter IV § 6 Proposition 2.
-/

@[expose] public section

namespace CategoryTheory.Subobject

open CategoryTheory CategoryTheory.Limits HasSubobjectClassifier

universe v u

variable {C : Type u} [Category.{v} C]
  [HasSubobjectClassifier C] [HasPullbacks C] [HasEqualizers C]

variable {X : C}

/-! ### The residual `P ⇒ Q` -/

/-- The Heyting residual of two subobjects of `X`: the equalizer of the
characteristic morphisms `χ (P ⊓ Q).arrow, χ P.arrow : X ⇉ Ω`. -/
noncomputable def residual (P Q : Subobject X) : Subobject X :=
  Subobject.mk (equalizer.ι (χ (P ⊓ Q).arrow) (χ P.arrow))

/-! ### Elimination half (`R ≤ residual P Q → R ⊓ P ≤ Q`) -/

/-- From `R ≤ residual P Q`, `R.arrow` equalizes
`χ (P ⊓ Q).arrow` and `χ P.arrow`. -/
private theorem residual_E1 (R P Q : Subobject X) (h : R ≤ residual P Q) :
    R.arrow ≫ χ (P ⊓ Q).arrow = R.arrow ≫ χ P.arrow := by
  have hfac : (residual P Q).Factors R.arrow :=
    Subobject.factors_of_le R.arrow h (Subobject.factors_self R)
  change (Subobject.mk (equalizer.ι (χ (P ⊓ Q).arrow) (χ P.arrow))).Factors R.arrow at hfac
  obtain ⟨g, hg⟩ := hfac
  change g ≫ equalizer.ι (χ (P ⊓ Q).arrow) (χ P.arrow) = R.arrow at hg
  -- `congr 1` avoids a `HasEqualizer` instance-diamond
  -- that blocks a direct `rw [equalizer.condition]`.
  rw [← hg, Category.assoc, Category.assoc]
  congr 1
  exact equalizer.condition _ _

omit [HasEqualizers C] in
/-- Equal characteristic morphisms (precomposed with `R.arrow`) yield equal
pullbacks of `P ⊓ Q` and `P` in `Subobject (R : C)`. -/
private theorem residual_E2 (R P Q : Subobject X)
    (h : R.arrow ≫ χ (P ⊓ Q).arrow = R.arrow ≫ χ P.arrow) :
    (Subobject.pullback R.arrow).obj (P ⊓ Q) =
      (Subobject.pullback R.arrow).obj P := by
  -- Beck-Chevalley for the classifier: every `S : Subobject X` is recovered as
  -- `(pullback (χ S.arrow)).obj truth_as_subobject`; precomposing the
  -- classifier with `R.arrow` forces the two right-hand sides equal under `h`.
  -- The explicit `set 𝒞` (rather than `χ` from the typeclass) is required
  -- because `pullback_χ_obj_mk_truth` is stated for a specific classifier.
  set 𝒞 : Subobject.Classifier C :=
    HasSubobjectClassifier.exists_classifier.some with h𝒞
  have h' : R.arrow ≫ 𝒞.χ (P ⊓ Q).arrow = R.arrow ≫ 𝒞.χ P.arrow := h
  have key : ∀ (S : Subobject X),
      (Subobject.pullback R.arrow).obj S =
        (Subobject.pullback (R.arrow ≫ 𝒞.χ S.arrow)).obj 𝒞.truth_as_subobject := by
    intro S
    simp only [Subobject.pullback_comp,
               Subobject.Classifier.pullback_χ_obj_mk_truth, Subobject.mk_arrow]
  rw [key (P ⊓ Q), key P, h']

omit [HasSubobjectClassifier C] [HasEqualizers C] in
/-- Pullback equality `pullback R.arrow (P ⊓ Q) = pullback R.arrow P`
(in `Subobject (R : C)`) gives `R ⊓ P ≤ Q` (in `Subobject X`). -/
private theorem residual_E3 (R P Q : Subobject X)
    (h : (Subobject.pullback R.arrow).obj (P ⊓ Q) =
         (Subobject.pullback R.arrow).obj P) :
    R ⊓ P ≤ Q := by
  rw [Subobject.inf_pullback] at h
  have hPQ : (Subobject.pullback R.arrow).obj P ≤ (Subobject.pullback R.arrow).obj Q :=
    inf_eq_left.mp h
  have hRP_RQ : R ⊓ P ≤ R ⊓ Q := by
    rw [Subobject.inf_eq_map_pullback R P, Subobject.inf_eq_map_pullback R Q]
    exact leOfHom ((Subobject.map R.arrow).map (homOfLE hPQ))
  exact hRP_RQ.trans _root_.inf_le_right

/-! ### Introduction half (`R ⊓ P ≤ Q → R ≤ residual P Q`) -/

omit [HasSubobjectClassifier C] [HasEqualizers C] in
/-- Pullback distributes over meet (a thin restatement of
`Subobject.inf_pullback`, recorded here for symmetry with `residual_I2`/`I3`). -/
private theorem residual_I1 (R P Q : Subobject X) :
    (Subobject.pullback R.arrow).obj (P ⊓ Q) =
      (Subobject.pullback R.arrow).obj P ⊓
        (Subobject.pullback R.arrow).obj Q :=
  Subobject.inf_pullback _ _ _

omit [HasSubobjectClassifier C] [HasEqualizers C] in
/-- From `R ⊓ P ≤ Q`, the pullback of `P` equals the pullback of `P ⊓ Q`
along `R.arrow` (in `Subobject (R : C)`). -/
private theorem residual_I2 (R P Q : Subobject X) (h : R ⊓ P ≤ Q) :
    (Subobject.pullback R.arrow).obj P =
      (Subobject.pullback R.arrow).obj (P ⊓ Q) := by
  -- Pullback `R` along itself is `⊤`; `h` rewrites `R ⊓ P = (R ⊓ P) ⊓ Q`;
  -- `congrArg` lifts this to the pullback functor and `inf_pullback` + the
  -- `pullback_self` fact collapse the LHS to `pullback _ P`.
  have hR : (Subobject.pullback R.arrow).obj R = ⊤ := by
    have hps := Subobject.pullback_self R.arrow
    rwa [Subobject.mk_arrow] at hps
  have h1 : R ⊓ P = (R ⊓ P) ⊓ Q := (inf_eq_left.mpr h).symm
  have h2 : (Subobject.pullback R.arrow).obj (R ⊓ P) =
            (Subobject.pullback R.arrow).obj ((R ⊓ P) ⊓ Q) :=
    congrArg (Subobject.pullback R.arrow).obj h1
  simp only [Subobject.inf_pullback, hR, top_inf_eq] at h2
  rw [residual_I1]
  exact h2

/-- Pullback equality lifts to a characteristic-morphism equality (the
classifier is unique), hence `R.arrow` factors through the equalizer
underlying `residual P Q`. -/
private theorem residual_I3 (R P Q : Subobject X)
    (h : (Subobject.pullback R.arrow).obj P =
         (Subobject.pullback R.arrow).obj (P ⊓ Q)) :
    R ≤ residual P Q := by
  -- Inverse Beck-Chevalley: apply `𝒞.χ ∘ (·).arrow` to both sides of the
  -- pullback equality.  `χ_pullback_obj_mk_truth_arrow` collapses the result
  -- to `R.arrow ≫ 𝒞.χ S.arrow`, recovering the χ-equation; then
  -- `equalizer.lift` produces the factorisation realising `R ≤ residual P Q`.
  set 𝒞 : Subobject.Classifier C :=
    HasSubobjectClassifier.exists_classifier.some with h𝒞
  have hchi : R.arrow ≫ χ (P ⊓ Q).arrow = R.arrow ≫ χ P.arrow := by
    have key : ∀ (S : Subobject X),
        (Subobject.pullback R.arrow).obj S =
          (Subobject.pullback (R.arrow ≫ 𝒞.χ S.arrow)).obj 𝒞.truth_as_subobject := by
      intro S
      simp only [Subobject.pullback_comp,
                 Subobject.Classifier.pullback_χ_obj_mk_truth, Subobject.mk_arrow]
    have hpb : (Subobject.pullback (R.arrow ≫ 𝒞.χ P.arrow)).obj 𝒞.truth_as_subobject =
               (Subobject.pullback (R.arrow ≫ 𝒞.χ (P ⊓ Q).arrow)).obj 𝒞.truth_as_subobject := by
      rw [← key P, ← key (P ⊓ Q)]; exact h
    -- Spell `h2`'s type explicitly: Lean otherwise leaves the lambda's
    -- domain (subobjects of `R.underlying`, not `X`) as an unsolvable metavar.
    have h2 :
        𝒞.χ ((Subobject.pullback (R.arrow ≫ 𝒞.χ P.arrow)).obj
              𝒞.truth_as_subobject).arrow =
        𝒞.χ ((Subobject.pullback (R.arrow ≫ 𝒞.χ (P ⊓ Q).arrow)).obj
              𝒞.truth_as_subobject).arrow :=
      congrArg (fun S => 𝒞.χ S.arrow) hpb
    simp only [Subobject.Classifier.χ_pullback_obj_mk_truth_arrow] at h2
    exact h2.symm
  exact Subobject.le_mk_of_comm (equalizer.lift R.arrow hchi)
          (equalizer.lift_ι R.arrow hchi)

/-! ### Galois connection -/

/-- The load-bearing Galois connection making `residual` the right adjoint
to `(· ⊓ P)`: `R ≤ residual P Q ↔ R ⊓ P ≤ Q`.

Assembled as
elimination = `residual_E3 ∘ residual_E2 ∘ residual_E1`,
introduction = `residual_I3 ∘ residual_I2` (with `residual_I1` consumed
inside `residual_I2` and `residual_I3`). -/
theorem le_residual_iff_inf_le (R P Q : Subobject X) :
    R ≤ residual P Q ↔ R ⊓ P ≤ Q :=
  ⟨fun h => residual_E3 R P Q (residual_E2 R P Q (residual_E1 R P Q h)),
   fun h => residual_I3 R P Q (residual_I2 R P Q h)⟩

/-! ### The `HeytingAlgebra` instance -/

section HeytingInstance

variable [HasInitial C] [HasImages C] [HasBinaryCoproducts C] [InitialMonoClass C]

/-- `Subobject X` carries a canonical Heyting-algebra structure in any
category satisfying the elementary-topos hypothesis bundle.

The implication is `residual P Q`; the pseudo-complement is
`residual P ⊥`, definitionally equal to `compl P` via `himp_bot := rfl`.
Distributivity, De Morgan, and the strict containment `a ≤ aᶜᶜ` follow as
theorems of the `HeytingAlgebra` typeclass. -/
noncomputable instance heytingAlgebra : HeytingAlgebra (Subobject X) :=
  { Subobject.semilatticeInf, Subobject.semilatticeSup,
    Subobject.orderTop, Subobject.orderBot with
    himp := residual
    compl := fun P => residual P ⊥
    le_himp_iff := le_residual_iff_inf_le
    himp_bot := fun _ => rfl }

end HeytingInstance

end CategoryTheory.Subobject
