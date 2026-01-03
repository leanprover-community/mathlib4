/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Abelian

/-!
# Spectral sequences

-/

@[expose] public section

namespace ComplexShape

def spectralSequenceNat (u : ℤ × ℤ) : ComplexShape (ℕ × ℕ) where
  Rel a b := a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2
  next_eq {a b b'} := by
    rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    ext <;> lia
  prev_eq {a a' b} := by
    rintro ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    ext <;> lia

instance (u : ℤ × ℤ) : DecidableRel (spectralSequenceNat u).Rel := fun a b => by
  dsimp [spectralSequenceNat]
  infer_instance

@[simp]
lemma spectralSequenceNat_rel_iff (u : ℤ × ℤ) (a b : ℕ × ℕ) :
    (spectralSequenceNat u).Rel a b ↔ a.1 + u.1 = b.1 ∧ a.2 + u.2 = b.2 := by rfl

def spectralSequenceFin (l : ℕ) (u : ℤ × ℤ) : ComplexShape (ℤ × Fin l) where
  Rel a b := a.1 + u.1 = b.1 ∧ a.2.1 + u.2 = b.2.1
  next_eq := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨b₁, ⟨b₂, _⟩⟩⟨b₁', ⟨b₂', _⟩⟩ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    ext <;> lia
  prev_eq := by
    rintro ⟨a₁, ⟨a₂, _⟩⟩ ⟨a₁', ⟨a₂', _⟩⟩⟨b₁, ⟨b₂, _⟩⟩ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩
    ext <;> lia

end ComplexShape

namespace CategoryTheory

open Category Limits

variable (C : Type*) [Category C] [Abelian C]
  {ι : Type*} (c : ℤ → ComplexShape ι) (r₀ : ℤ)

structure SpectralSequence where
  page (r : ℤ) (hr : r₀ ≤ r := by lia) : HomologicalComplex C (c r)
  iso (r r' : ℤ) (pq : ι) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    (page r).homology pq ≅ (page r').X pq

namespace SpectralSequence

variable {C c r₀}
variable (E E' E'' : SpectralSequence C c r₀)

@[ext]
structure Hom where
  hom (r : ℤ) (hr : r₀ ≤ r := by lia) : E.page r ⟶ E'.page r
  comm (r r' : ℤ) (pq : ι) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    HomologicalComplex.homologyMap (hom r) pq ≫ (E'.iso r r' pq).hom =
      (E.iso r r' pq).hom ≫ (hom r').f pq := by aesop_cat

def pageXIsoOfEq (pq : ι) (r r' : ℤ) (h : r = r') (hr : r₀ ≤ r := by lia) :
    (E.page r).X pq ≅ (E.page r').X pq :=
  eqToIso (by subst h; rfl)

namespace Hom

attribute [reassoc] comm

@[simps]
def id : Hom E E where
  hom r hr := 𝟙 _

variable {E E' E''}

@[simps]
def comp (f : Hom E E') (g : Hom E' E'') : Hom E E'' where
  hom r hr := f.hom r ≫ g.hom r
  comm r r' hrr' pq hr := by
    dsimp
    rw [HomologicalComplex.homologyMap_comp, assoc, g.comm r r', f.comm_assoc r r']

end Hom

instance : Category (SpectralSequence C c r₀) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp

variable {E E'}

lemma hom_ext {f f' : E ⟶ E'}
    (h : ∀ (r : ℤ) (hr : r₀ ≤ r), f.hom r = f'.hom r) :
    f = f' := by
  apply Hom.ext
  ext r hr : 2
  exact h r hr

variable (E)

@[simp]
lemma id_hom (r : ℕ) (hr : r₀ ≤ r := by lia) :
    Hom.hom (𝟙 E) r = 𝟙 _ := rfl

variable {E E''}

@[reassoc, simp]
lemma comp_hom (f : E ⟶ E') (g : E' ⟶ E'') (r : ℕ) (hr : r₀ ≤ r := by lia) :
    (f ≫ g).hom r = f.hom r ≫ g.hom r := rfl

variable (C c r₀)

@[simps]
def pageFunctor (r : ℤ) (hr : r₀ ≤ r := by lia) :
    SpectralSequence C c r₀ ⥤ HomologicalComplex C (c r) where
  obj E := E.page r
  map f := f.hom r

@[simps!]
noncomputable def pageHomologyNatIso
    (r r' : ℤ) (pq : ι) (hrr' : r + 1 = r' := by lia) (hr : r₀ ≤ r := by lia) :
    pageFunctor C c r₀ r ⋙ HomologicalComplex.homologyFunctor _ _ pq ≅
      pageFunctor C c r₀ r' ⋙ HomologicalComplex.eval _ _ pq :=
  NatIso.ofComponents (fun E => E.iso r r' pq) (fun _ ↦ Hom.comm _ _ _ _ (by lia))

end SpectralSequence

abbrev CohomologicalSpectralSequence :=
  SpectralSequence C (fun r => ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ))

abbrev E₂CohomologicalSpectralSequence := CohomologicalSpectralSequence C 2

abbrev CohomologicalSpectralSequenceNat :=
  SpectralSequence C (fun r => ComplexShape.spectralSequenceNat ⟨r, 1 - r⟩)

abbrev E₂CohomologicalSpectralSequenceNat :=
  CohomologicalSpectralSequenceNat C 2

abbrev CohomologicalSpectralSequenceFin (l : ℕ) :=
  SpectralSequence C (fun r => ComplexShape.spectralSequenceFin l ⟨r, 1 - r⟩)

abbrev E₂CohomologicalSpectralSequenceFin (l : ℕ) :=
  CohomologicalSpectralSequenceFin C 2 l

end CategoryTheory
