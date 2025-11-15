/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Sites.Point
import Mathlib.CategoryTheory.Sites.Spaces

/-!
# Points of a topological space

-/

universe u

open CategoryTheory

namespace Opens

variable {T : Type u} [TopologicalSpace T]

def point (t : T) : GrothendieckTopology.Point.{u} (grothendieckTopology T) where
  fiber.obj U := { u : U // u = t }
  fiber.map f x := ⟨⟨x.1.1, leOfHom f x.1.2⟩, x.2⟩
  isCofiltered :=
    { nonempty := ⟨Functor.elementsMk _ ⊤ ⟨⟨t, by simp⟩, rfl⟩⟩
      cone_objs := by
        rintro ⟨U, ⟨⟨x, hx₁⟩, (hx₂ : x = t)⟩⟩ ⟨V, ⟨⟨y, hy₁⟩, (hy₂ : y = t)⟩⟩
        subst hx₂ hy₂
        exact ⟨⟨U ⊓ V, ⟨⟨y, hx₁, hy₁⟩, rfl⟩⟩,
          CategoryOfElements.homMk _ _ (homOfLE (by simp)) rfl,
          CategoryOfElements.homMk _ _ (homOfLE (by simp)) rfl, by tauto⟩
      cone_maps := by
        rintro _ _ ⟨f, _⟩ ⟨g, _⟩
        obtain rfl : f = g := by subsingleton
        exact ⟨_, 𝟙 _, rfl⟩ }
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective {U} R hR := by
    rintro ⟨⟨x, hx₁⟩, (hx₂ : x = t)⟩
    obtain ⟨V, f, hb, hx₃⟩ := hR x hx₁
    exact ⟨V, f, hb, ⟨⟨x, hx₃⟩, hx₂⟩, rfl⟩

end Opens
