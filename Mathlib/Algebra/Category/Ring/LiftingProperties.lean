/-
Copyright (c) 2026 Jakob Scholbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob Scholbach
-/
module

public import Mathlib.CategoryTheory.LiftingProperties.Unique
public import Mathlib.Algebra.Category.Ring.Basic

/-!
# Unique lifting between ring maps in `CommRingCat`

The unique lifting property between two morphisms `ofHom f`, `ofHom p` of
`CommRingCat` says exactly that every commuting square of ring homomorphisms
built from `f` and `p` admits a unique diagonal filler. This file records that
translation.

## Main declarations

* `CommRingCat.hasUniqueLiftingProperty_ofHom_iff`
-/

public section

open CategoryTheory CommRingCat

universe u

namespace CommRingCat

/-- The unique lifting property between `ofHom f` and `ofHom p` in `CommRingCat` translated to a
purely ring-theoretic existence-and-uniqueness statement. -/
theorem hasUniqueLiftingProperty_ofHom_iff {A B X Y : Type u} [CommRing A] [CommRing B] [CommRing X]
    [CommRing Y] (f : A →+* B) (p : X →+* Y) :
    HasUniqueLiftingProperty (CommRingCat.ofHom f) (CommRingCat.ofHom p) ↔
    ∀ (t : A →+* X) (b : B →+* Y), p.comp t = b.comp f →
      ∃! l : B →+* X, l.comp f = t ∧ p.comp l = b := by
  rw [hasUniqueLiftingProperty_iff]
  constructor
  · intro H t b hc
    have sq : CommSq (CommRingCat.ofHom t) (CommRingCat.ofHom f) (CommRingCat.ofHom p)
        (CommRingCat.ofHom b) := ⟨by rw [← ofHom_comp, ← ofHom_comp, hc]⟩
    obtain ⟨l, ⟨hl1, hl2⟩, hu⟩ := H (CommRingCat.ofHom t) (CommRingCat.ofHom b) sq
    refine ⟨l.hom, ⟨by simpa using congrArg (·.hom) hl1, by simpa using congrArg (·.hom) hl2⟩, ?_⟩
    intro m ⟨hm1, hm2⟩
    have hml : CommRingCat.ofHom m = l :=
      hu (CommRingCat.ofHom m) ⟨by rw [← ofHom_comp, hm1], by rw [← ofHom_comp, hm2]⟩
    rw [← hom_ofHom m, hml]
  · intro H t b sq
    obtain ⟨l, ⟨hl1, hl2⟩, hu⟩ := H t.hom b.hom (by simpa using congrArg (·.hom) sq.w)
    refine ⟨CommRingCat.ofHom l, ⟨?_, ?_⟩, ?_⟩
    · rw [← ofHom_comp, hl1, ofHom_hom]
    · rw [← ofHom_comp, hl2, ofHom_hom]
    · intro m ⟨hm1, hm2⟩
      have hml : m.hom = l :=
        hu m.hom ⟨by simpa using congrArg (·.hom) hm1, by simpa using congrArg (·.hom) hm2⟩
      rw [← ofHom_hom m, hml]

end CommRingCat
