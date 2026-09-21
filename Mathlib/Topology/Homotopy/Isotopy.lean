/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Topology.Homotopy.Basic

/-!
# Isotopy between homeomorphisms

In this file, we define `Homeomorph.Isotopy`, the type of isotopies between two homeomorphisms,
mirroring the API for `ContinuousMap.Homotopy`.
-/

@[expose] public section

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (f₀ f₁ f₂ : X ≃ₜ Y) (g₀ g₁ : Y ≃ₜ Z)

namespace Homeomorph

/-- An isotopy between two homeomorphisms is a homotopy through homeomorphisms. -/
structure Isotopy extends (f₀ : C(X, Y)).Homotopy f₁ where
  isHomeomorph : ∀ t, IsHomeomorph (toFun ⟨t, ·⟩)

namespace Isotopy

/-- The trivial isotopy between a homeomorphism and itself. -/
protected def refl : Isotopy f₀ f₀ where
  __ := ContinuousMap.Homotopy.refl _
  isHomeomorph _ := f₀.isHomeomorph

variable {f₀ f₁ f₂ g₀ g₁}

/-- Reversal of isotopy. -/
protected def symm (i : Isotopy f₀ f₁) : Isotopy f₁ f₀ where
  __ := i.toHomotopy.symm
  isHomeomorph t := i.isHomeomorph (unitInterval.symm t)

/-- Concatenation of isotopy. -/
protected noncomputable def trans (i₀ : Isotopy f₀ f₁) (i₁ : Isotopy f₁ f₂) : Isotopy f₀ f₂ where
  __ := i₀.toHomotopy.trans i₁.toHomotopy
  isHomeomorph t := by
    simp only [ContinuousMap.toFun_eq_coe, ContinuousMap.Homotopy.coe_toContinuousMap,
      ContinuousMap.Homotopy.trans_apply]
    split_ifs with h
    · exact i₀.isHomeomorph ⟨_, (unitInterval.mul_pos_mem_iff zero_lt_two).2 ⟨t.2.1, h⟩⟩
    · exact i₁.isHomeomorph ⟨_, unitInterval.two_mul_sub_one_mem_iff.2 ⟨(not_le.1 h).le, t.2.2⟩⟩

/-- Isotopy between compositions of homeomorphisms. -/
protected def comp (fi : Isotopy f₀ f₁) (gi : Isotopy g₀ g₁) :
    Isotopy (f₀.trans g₀) (f₁.trans g₁) where
  __ := gi.toHomotopy.comp fi.toHomotopy
  isHomeomorph t := (gi.isHomeomorph t).comp (fi.isHomeomorph t)

end Isotopy

/-- Two homeomorphisms `f₀` and `f₁` are isotopic if there exists an isotopy between them. -/
def Isotopic (f₀ f₁ : X ≃ₜ Y) : Prop :=
  Nonempty (Isotopy f₀ f₁)

namespace Isotopic

-- dot notation doesn't work for some reason
theorem homotopic {f₀ f₁ : X ≃ₜ X} (h : Isotopic f₀ f₁) : (f₀ : C(X, X)).Homotopic f₁ := by
  obtain ⟨i⟩ := h; exact ⟨i.toHomotopy⟩

@[refl]
theorem refl (f : X ≃ₜ Y) : Isotopic f f :=
  ⟨Isotopy.refl f⟩

@[symm]
theorem symm ⦃f g : X ≃ₜ Y⦄ (h : Isotopic f g) : Isotopic g f :=
  h.map Isotopy.symm

@[trans]
theorem trans ⦃f g h : X ≃ₜ Y⦄ (h₀ : Isotopic f g) (h₁ : Isotopic g h) : Isotopic f h :=
  h₀.map2 Isotopy.trans h₁

theorem comp {f₀ f₁ : X ≃ₜ Y} {g₀ g₁ : Y ≃ₜ Z} (hg : Isotopic g₀ g₁) (hf : Isotopic f₀ f₁) :
    Isotopic (f₀.trans g₀) (f₁.trans g₁) :=
  hf.map2 Isotopy.comp hg

theorem equivalence : Equivalence (@Isotopic X Y _ _) :=
  ⟨refl, by apply symm, by apply trans⟩

end Isotopic

variable (X) in
/-- Being isotopic is a congruence relation on the self-homeomorphisms of a topological space. -/
def con : Con (X ≃ₜ X) where
  r f₀ f₁ := Nonempty (f₀.Isotopy f₁)
  iseqv := Isotopic.equivalence
  mul' := fun ⟨fi⟩ ⟨gi⟩ ↦ ⟨gi.comp fi⟩

end Homeomorph

variable (X) in
/-- The mapping class group of a topological space. -/
abbrev MappingClassGroup : Type _ := (Homeomorph.con X).Quotient

open ContinuousMap.Monoid in
/-- The homomorphism from the mapping class group of a space to the monoid of continuous self-maps
up to homotopy. -/
def MappingClassGroup.toUnitsMonoid : MappingClassGroup X →* (MappingClassMonoid X)ˣ where
  toFun := Quotient.lift (fun f ↦ let u := ofHomeomorph X f
    ⟨u, ↑u⁻¹, congr($u.mul_inv), congr($u.inv_mul)⟩)
    fun f g h ↦ Units.ext ((Con.eq _).mpr <| Homeomorph.Isotopic.homotopic h)
  map_one' := rfl
  map_mul' := by rintro ⟨⟩ ⟨⟩; rfl
