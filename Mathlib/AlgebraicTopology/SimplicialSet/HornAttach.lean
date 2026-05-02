/-
Copyright (c) 2026 Jacob Reinhold. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jacob Reinhold
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.SubcomplexAttach

/-!
# Single-cell horn attachment to a subcomplex

For a monic `σ : Δ[n + 1] ⟶ X` whose preimage of `A` equals `Λ[n + 1, i]`,
the square
```
Λ[n+1, i] ──→ A
   │          │
   ↓          ↓
Δ[n+1]    ──→ A ⊔ range σ
```
is a pushout in `SSet` (`Subcomplex.hornAttach_isPushout_of_mono`).
Injectivity off `Λ[n + 1, i]` is automatic from `Mono σ`
(`Subcomplex.injOn_compl_horn_of_mono`), so the pushout follows from
`Subcomplex.attachingMap_isPushout_of_injOn_compl`. This is the horn
analogue of single-cell boundary attachment in
`Mathlib/AlgebraicTopology/SimplicialSet/BoundaryAttach.lean`.

Two preimage characterizations identify when `A.preimage σ` equals a horn:
a basic form in terms of faces lying in `A.preimage σ`
(`Subcomplex.preimage_eq_horn_of_face_le_of_omitted_not_le`), and an
image-form variant convenient for cellular filtrations
(`Subcomplex.preimage_eq_horn_of_face_image_le_of_omitted_not_le`).

## References

* [E. Riehl and D. Verity, *Elements of ∞-Category Theory*][RiehlVerity2022],
  Section 1.1 (cellular generation by inner horn inclusions,
  Proposition 1.1.29).
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet
namespace Subcomplex

/-- If every codimension-one face except the `i`-th lands in `A` and the
omitted face does not, the preimage of `A` along `σ : Δ[n + 1] ⟶ X` is exactly
the horn `Λ[n + 1, i]`. -/
lemma preimage_eq_horn_of_face_le_of_omitted_not_le {X : SSet.{u}} {n : ℕ}
    (A : X.Subcomplex) (σ : Δ[n + 1] ⟶ X) (i : Fin (n + 2))
    (hfaces : ∀ j : Fin (n + 2), j ≠ i →
      stdSimplex.face.{u} ({j}ᶜ : Finset (Fin (n + 2))) ≤ A.preimage σ)
    (homit :
      ¬ stdSimplex.face.{u} ({i}ᶜ : Finset (Fin (n + 2))) ≤ A.preimage σ) :
    A.preimage σ = (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex) := by
  apply le_antisymm
  · rw [subcomplex_le_horn_iff]; exact homit
  · rw [horn_eq_iSup, iSup_le_iff]; exact fun j ↦ hfaces j.1 j.2

/-- Image-form variant of `preimage_eq_horn_of_face_le_of_omitted_not_le`:
the hypotheses ask that face images lie in `A` rather than that the faces
themselves lie in `A.preimage σ`. -/
lemma preimage_eq_horn_of_face_image_le_of_omitted_not_le {X : SSet.{u}} {n : ℕ}
    (A : X.Subcomplex) (σ : Δ[n + 1] ⟶ X) (i : Fin (n + 2))
    (hfaces : ∀ j : Fin (n + 2), j ≠ i →
      (stdSimplex.face.{u} ({j}ᶜ : Finset (Fin (n + 2)))).image σ ≤ A)
    (homit :
      ¬ (stdSimplex.face.{u} ({i}ᶜ : Finset (Fin (n + 2)))).image σ ≤ A) :
    A.preimage σ = (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex) := by
  apply preimage_eq_horn_of_face_le_of_omitted_not_le A σ i
  · intro j hj; rw [← image_le_iff]; exact hfaces j hj
  · intro hle; apply homit; rwa [image_le_iff]

/-- A monic classifier `σ : Δ[n] ⟶ X` is injective at every dimension on the
complement of the horn `Λ[n, i]`. -/
lemma injOn_compl_horn_of_mono {X : SSet.{u}} {n : ℕ} (σ : Δ[n] ⟶ X) [Mono σ]
    (i : Fin (n + 1)) (d : SimplexCategoryᵒᵖ) :
    Set.InjOn (σ.app d) ((Λ[n, i] : (Δ[n] : SSet.{u}).Subcomplex).obj d)ᶜ := by
  have hmono_app : Mono (σ.app d) :=
    (NatTrans.mono_iff_mono_app σ).mp inferInstance d
  exact fun _ _ _ _ h ↦ (mono_iff_injective (σ.app d)).mp hmono_app h

/-- Single-cell horn attachment as a pushout for a monic classifier. If
`σ : Δ[n + 1] ⟶ X` is monic with preimage of `A` equal to `Λ[n + 1, i]`, then
`A ⊔ range σ` is the pushout of `Λ[n + 1, i] ↪ Δ[n + 1]` along the attaching
map. -/
lemma hornAttach_isPushout_of_mono {X : SSet.{u}} {n : ℕ} (i : Fin (n + 2))
    (A : X.Subcomplex) (σ : Δ[n + 1] ⟶ X) [Mono σ]
    (hhorn : A.preimage σ = (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex)) :
    IsPushout (attachingMap A σ hhorn)
      (Λ[n + 1, i] : (Δ[n + 1] : SSet.{u}).Subcomplex).ι
      (homOfLE (show A ≤ A ⊔ range σ from le_sup_left))
      (lift σ (show range σ ≤ A ⊔ range σ from le_sup_right)) :=
  attachingMap_isPushout_of_injOn_compl A σ hhorn (injOn_compl_horn_of_mono σ i)

end Subcomplex
end SSet
