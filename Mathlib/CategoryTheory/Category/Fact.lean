/-
Copyright (c) 2023 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

universe v u

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]

structure Fact {X Y : C} (f : X ⟶ Y) where
  D   : C
  ι   : X ⟶ D
  π   : D ⟶ Y
  ι_π : ι ≫ π = f := by aesop_cat

attribute [simp] Fact.ι_π

namespace Fact

variable {X Y : C} {f : X ⟶ Y}

@[ext]
protected structure Hom (d e : Fact f) : Type (max u v) where
  h : d.D ⟶ e.D
  ι_h : d.ι ≫ h = e.ι := by aesop_cat
  h_π : h ≫ e.π = d.π := by aesop_cat

attribute [simp] Fact.Hom.ι_h Fact.Hom.h_π

@[simps]
protected def Hom.id (d : Fact f) : Fact.Hom d d where
  h := 𝟙 _

@[simps]
protected def Hom.comp {d₁ d₂ d₃ : Fact f} (f : Fact.Hom d₁ d₂) (g : Fact.Hom d₂ d₃) :
    Fact.Hom d₁ d₃ where
  h := f.h ≫ g.h
  ι_h := by rw [← Category.assoc, f.ι_h, g.ι_h]
  h_π := by rw [Category.assoc, g.h_π, f.h_π]

instance : Category.{max u v} (Fact f) where
  Hom d e := Fact.Hom d e
  id d := Fact.Hom.id d
  comp f g := Fact.Hom.comp f g

variable (d : Fact f)

@[simps]
protected def initial : Fact f where
  D := X
  ι := 𝟙 _
  π := f

@[simps]
protected def initialHom (d : Fact f) : Fact.Hom (Fact.initial : Fact f) d where
  h := d.ι

instance : Unique ((Fact.initial : Fact f) ⟶ d) where
  default := Fact.initialHom d
  uniq f := by
    change Fact.Hom _ _ at f
    show f = _
    ext
    simp only [initial_D, initialHom_h, ← f.ι_h]
    simp

@[simps]
protected def terminal : Fact f where
  D := Y
  ι := f
  π := 𝟙 _

@[simps]
protected def terminalHom (d : Fact f) : Fact.Hom d (Fact.terminal : Fact f) where
  h := d.π

instance : Unique (d ⟶ (Fact.terminal : Fact f)) where
  default := Fact.terminalHom d
  uniq f := by
    change Fact.Hom _ _ at f
    show f = _
    ext
    simp only [terminal_D, terminalHom_h, ← f.h_π]
    simp

open Limits

def IsInitialId : IsInitial (Fact.initial : Fact f) := IsInitial.ofUnique _

def IsTerminalId : IsTerminal (Fact.terminal : Fact f) := IsTerminal.ofUnique _

end Fact
