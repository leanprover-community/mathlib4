import Mathlib.AdicSpace

universe u

open CategoryTheory GrothendieckTopology

def PreLVCRS.zariskiCoverage : Coverage (PreLVCRS.{u}) where
  covering X P := (∀ (Y : PreLVCRS) (f : Y ⟶ X), P f → IsOpenImmersion f) ∧
    ∀ x : X, ∃ (Y : PreLVCRS) (f : Y ⟶ X), P f ∧ x ∈ Set.range f.hom.base
  pullback := sorry
