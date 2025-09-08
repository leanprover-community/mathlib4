/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Limits.Types.Shapes

/-!
# Pullback functors on `Over` categories in `Type` have right adjoints

Given a map `f : E → B`, in order to show that `Over.pullback f : Over B ⥤ Over E`
commutes with colimits, we show that it admits a right adjoint. In order to
do that, we first construct a functor `overPullback f : Over B ⥤ Over E` whose
definition involves explicit types rather than categorical pullbacks, and
we define its right adjoint `overPushforward f : Over E ⥤ Over B`.

## TODO

When this notion is defined, deduce that `Type u` is a locally cartesian closed category.

-/

universe u

namespace CategoryTheory.Types

open Limits

variable {E B : Type u} (f : E → B)

/-- The pullback functor `Over B ⥤ Over E` for a map `f : E → B` between types.
This definition uses a explicit definition of types rather than using the
categorical pullback as in `Over.pullback`, see `overPullbackIso` for
a comparison isomorphism. -/
@[simps]
def overPullback : Over B ⥤ Over E where
  obj S := Over.mk (Y := { x : S.left × E // S.hom x.1 = f x.2}) (fun x ↦ x.1.2)
  map φ := Over.homMk (fun x ↦ ⟨⟨φ.left x.1.1, x.1.2⟩, by
    simpa only [← x.2] using congr_fun (Over.w φ) x.1.1⟩)

/-- The explicit pullback functor `overPullbackIso f : Over B ⥤ Over E`
identifies to the pullback functor `Over.pullback f` defined using
categorical pullbacks. -/
noncomputable def overPullbackIso : overPullback f ≅ Over.pullback f :=
  NatIso.ofComponents (fun X ↦ Over.isoMk (Types.pullbackIsoPullback X.hom f).symm)

/-- Given a map `f : E → B` between types, this is a functor `Over E ⥤ Over B`
that is right adjoint to `overPullback f`. It sends `p : T → E` to the
sigma type which sends `b : B` to the subtype of maps
`g : f ⁻¹' {b} → T` over `E`. -/
@[simps]
def overPushforward : Over E ⥤ Over B where
  obj T := Over.mk
    (Y := Σ (b : B), { g : f ⁻¹' {b} → T.left // ∀ e, T.hom (g e) = e.1 }) Sigma.fst
  map {T T'} φ := Over.homMk (fun ⟨b, g, hg⟩ ↦ ⟨b, φ.left.comp g, fun e ↦ by
    simpa [hg] using congr_fun (Over.w φ) (g e)⟩)

variable {f} in
/-- Extensionality lemma for the types in the image of the `overPushforward f` functor. -/
@[ext (iff := false)]
lemma overPushforward_obj_left_ext {T : Over E} {t t' : ((overPushforward f).obj T).left}
    (h₁ : t.1 = t'.1) (h₂ : ∀ (e : E) (he : f e = t.1),
      t.2.1 ⟨e, he⟩ = t'.2.1 ⟨e, by simp [h₁, he]⟩) : t = t' := by
  obtain ⟨t, g, _⟩ := t
  obtain ⟨t', g', _⟩ := t'
  obtain rfl : t = t' := h₁
  obtain rfl : g = g' := by ext; apply h₂
  rfl

/-- Given a map `f : E → B`, the functor `overPullback : Over B ⥤ Over E`
admits `overPushforward` as a right adjoint. -/
def overPushforwardAdjunction : overPullback f ⊣ overPushforward f :=
  .mkOfHomEquiv
    { homEquiv S T :=
      { toFun φ :=
          Over.homMk (fun s ↦ ⟨S.hom s, fun ⟨x, hx⟩ ↦ φ.left ⟨⟨s, x⟩, by aesop⟩,
            fun _ ↦ congr_fun (Over.w φ) _⟩)
        invFun ψ :=
          Over.homMk
            (fun ⟨⟨s, e⟩, h⟩ ↦ (ψ.left s).2.1 ⟨e, h.symm.trans (congr_fun (Over.w ψ).symm _)⟩)
            (by ext ⟨⟨s, e⟩, h⟩; exact (ψ.left s).2.2 ⟨e, _⟩)
        left_inv _ := rfl
        right_inv ψ := by
          ext s
          · exact (congr_fun (Over.w ψ).symm s)
          · dsimp } }

instance : (overPullback f).IsLeftAdjoint := (overPushforwardAdjunction f).isLeftAdjoint

instance : (overPushforward f).IsRightAdjoint := (overPushforwardAdjunction f).isRightAdjoint

instance (f : E ⟶ B) : (Over.pullback f).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (overPullbackIso f)

end CategoryTheory.Types
