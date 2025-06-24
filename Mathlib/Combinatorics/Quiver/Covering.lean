/-
Copyright (c) 2022 Antoine Labelle, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle, Rémi Bottinelli
-/
import Mathlib.Combinatorics.Quiver.Cast
import Mathlib.Combinatorics.Quiver.Symmetric
import Mathlib.Data.Sigma.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.Common

/-!
# Covering

This file defines coverings of quivers as prefunctors that are bijective on the
so-called stars and costars at each vertex of the domain.

## Main definitions

* `Quiver.Star u` is the type of all arrows with source `u`;
* `Quiver.Costar u` is the type of all arrows with target `u`;
* `Prefunctor.star φ u` is the obvious function `star u → star (φ.obj u)`;
* `Prefunctor.costar φ u` is the obvious function `costar u → costar (φ.obj u)`;
* `Prefunctor.IsCovering φ` means that `φ.star u` and `φ.costar u` are bijections for all `u`;
* `Quiver.PathStar u` is the type of all paths with source `u`;
* `Prefunctor.pathStar u` is the obvious function `PathStar u → PathStar (φ.obj u)`.

## Main statements

* `Prefunctor.IsCovering.pathStar_bijective` states that if `φ` is a covering,
  then `φ.pathStar u` is a bijection for all `u`.
  In other words, every path in the codomain of `φ` lifts uniquely to its domain.

## TODO

Clean up the namespaces by renaming `Prefunctor` to `Quiver.Prefunctor`.

## Tags

Cover, covering, quiver, path, lift
-/


open Function Quiver

universe u v w

variable {U : Type _} [Quiver.{u + 1} U] {V : Type _} [Quiver.{v + 1} V] (φ : U ⥤q V) {W : Type _}
  [Quiver.{w + 1} W] (ψ : V ⥤q W)

/-- The `Quiver.Star` at a vertex is the collection of arrows whose source is the vertex.
The type `Quiver.Star u` is defined to be `Σ (v : U), (u ⟶ v)`. -/
abbrev Quiver.Star (u : U) :=
  Σ v : U, u ⟶ v

/-- Constructor for `Quiver.Star`. Defined to be `Sigma.mk`. -/
protected abbrev Quiver.Star.mk {u v : U} (f : u ⟶ v) : Quiver.Star u :=
  ⟨_, f⟩

/-- The `Quiver.Costar` at a vertex is the collection of arrows whose target is the vertex.
The type `Quiver.Costar v` is defined to be `Σ (u : U), (u ⟶ v)`. -/
abbrev Quiver.Costar (v : U) :=
  Σ u : U, u ⟶ v

/-- Constructor for `Quiver.Costar`. Defined to be `Sigma.mk`. -/
protected abbrev Quiver.Costar.mk {u v : U} (f : u ⟶ v) : Quiver.Costar v :=
  ⟨_, f⟩

/-- A prefunctor induces a map of `Quiver.Star` at every vertex. -/
@[simps]
def Prefunctor.star (u : U) : Quiver.Star u → Quiver.Star (φ.obj u) := fun F =>
  Quiver.Star.mk (φ.map F.2)

/-- A prefunctor induces a map of `Quiver.Costar` at every vertex. -/
@[simps]
def Prefunctor.costar (u : U) : Quiver.Costar u → Quiver.Costar (φ.obj u) := fun F =>
  Quiver.Costar.mk (φ.map F.2)

@[simp]
theorem Prefunctor.star_apply {u v : U} (e : u ⟶ v) :
    φ.star u (Quiver.Star.mk e) = Quiver.Star.mk (φ.map e) :=
  rfl

@[simp]
theorem Prefunctor.costar_apply {u v : U} (e : u ⟶ v) :
    φ.costar v (Quiver.Costar.mk e) = Quiver.Costar.mk (φ.map e) :=
  rfl

theorem Prefunctor.star_comp (u : U) : (φ ⋙q ψ).star u = ψ.star (φ.obj u) ∘ φ.star u :=
  rfl

theorem Prefunctor.costar_comp (u : U) : (φ ⋙q ψ).costar u = ψ.costar (φ.obj u) ∘ φ.costar u :=
  rfl

/-- A prefunctor is a covering of quivers if it defines bijections on all stars and costars. -/
protected structure Prefunctor.IsCovering : Prop where
  star_bijective : ∀ u, Bijective (φ.star u)
  costar_bijective : ∀ u, Bijective (φ.costar u)

@[simp]
theorem Prefunctor.IsCovering.map_injective (hφ : φ.IsCovering) {u v : U} :
    Injective fun f : u ⟶ v => φ.map f := by
  rintro f g he
  have : φ.star u (Quiver.Star.mk f) = φ.star u (Quiver.Star.mk g) := by simpa using he
  simpa using (hφ.star_bijective u).left this

theorem Prefunctor.IsCovering.comp (hφ : φ.IsCovering) (hψ : ψ.IsCovering) : (φ ⋙q ψ).IsCovering :=
  ⟨fun _ => (hψ.star_bijective _).comp (hφ.star_bijective _),
   fun _ => (hψ.costar_bijective _).comp (hφ.costar_bijective _)⟩

theorem Prefunctor.IsCovering.of_comp_right (hψ : ψ.IsCovering) (hφψ : (φ ⋙q ψ).IsCovering) :
    φ.IsCovering :=
  ⟨fun _ => (Bijective.of_comp_iff' (hψ.star_bijective _) _).mp (hφψ.star_bijective _),
   fun _ => (Bijective.of_comp_iff' (hψ.costar_bijective _) _).mp (hφψ.costar_bijective _)⟩

theorem Prefunctor.IsCovering.of_comp_left (hφ : φ.IsCovering) (hφψ : (φ ⋙q ψ).IsCovering)
    (φsur : Surjective φ.obj) : ψ.IsCovering := by
  refine ⟨fun v => ?_, fun v => ?_⟩ <;> obtain ⟨u, rfl⟩ := φsur v
  exacts [(Bijective.of_comp_iff _ (hφ.star_bijective u)).mp (hφψ.star_bijective u),
    (Bijective.of_comp_iff _ (hφ.costar_bijective u)).mp (hφψ.costar_bijective u)]

/-- The star of the symmetrification of a quiver at a vertex `u` is equivalent to the sum of the
star and the costar at `u` in the original quiver. -/
def Quiver.symmetrifyStar (u : U) :
    Quiver.Star (Symmetrify.of.obj u) ≃ Quiver.Star u ⊕ Quiver.Costar u :=
  Equiv.sigmaSumDistrib _ _

/-- The costar of the symmetrification of a quiver at a vertex `u` is equivalent to the sum of the
costar and the star at `u` in the original quiver. -/
def Quiver.symmetrifyCostar (u : U) :
    Quiver.Costar (Symmetrify.of.obj u) ≃ Quiver.Costar u ⊕ Quiver.Star u :=
  Equiv.sigmaSumDistrib _ _

theorem Prefunctor.symmetrifyStar (u : U) :
    φ.symmetrify.star u =
      (Quiver.symmetrifyStar _).symm ∘ Sum.map (φ.star u) (φ.costar u) ∘
        Quiver.symmetrifyStar u := by
  rw [Equiv.eq_symm_comp (e := Quiver.symmetrifyStar (φ.obj u))]
  ext ⟨v, f | g⟩ <;>
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [Quiver.symmetrifyStar]`
    simp only [Quiver.symmetrifyStar, Function.comp_apply] <;>
    erw [Equiv.sigmaSumDistrib_apply, Equiv.sigmaSumDistrib_apply] <;>
    simp

protected theorem Prefunctor.symmetrifyCostar (u : U) :
    φ.symmetrify.costar u =
      (Quiver.symmetrifyCostar _).symm ∘
        Sum.map (φ.costar u) (φ.star u) ∘ Quiver.symmetrifyCostar u := by
  rw [Equiv.eq_symm_comp (e := Quiver.symmetrifyCostar (φ.obj u))]
  ext ⟨v, f | g⟩ <;>
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/10745): was `simp [Quiver.symmetrifyCostar]`
    simp only [Quiver.symmetrifyCostar, Function.comp_apply] <;>
    erw [Equiv.sigmaSumDistrib_apply, Equiv.sigmaSumDistrib_apply] <;>
    simp

protected theorem Prefunctor.IsCovering.symmetrify (hφ : φ.IsCovering) :
    φ.symmetrify.IsCovering := by
  refine ⟨fun u => ?_, fun u => ?_⟩ <;>
  simp [φ.symmetrifyStar, φ.symmetrifyCostar, hφ.star_bijective u, hφ.costar_bijective u]

/-- The path star at a vertex `u` is the type of all paths starting at `u`.
The type `Quiver.PathStar u` is defined to be `Σ v : U, Path u v`. -/
abbrev Quiver.PathStar (u : U) :=
  Σ v : U, Path u v

/-- Constructor for `Quiver.PathStar`. Defined to be `Sigma.mk`. -/
protected abbrev Quiver.PathStar.mk {u v : U} (p : Path u v) : Quiver.PathStar u :=
  ⟨_, p⟩

/-- A prefunctor induces a map of path stars. -/
def Prefunctor.pathStar (u : U) : Quiver.PathStar u → Quiver.PathStar (φ.obj u) := fun p =>
  Quiver.PathStar.mk (φ.mapPath p.2)

@[simp]
theorem Prefunctor.pathStar_apply {u v : U} (p : Path u v) :
    φ.pathStar u (Quiver.PathStar.mk p) = Quiver.PathStar.mk (φ.mapPath p) :=
  rfl

theorem Prefunctor.pathStar_injective (hφ : ∀ u, Injective (φ.star u)) (u : U) :
    Injective (φ.pathStar u) := by
  dsimp +unfoldPartialApp [Prefunctor.pathStar, Quiver.PathStar.mk]
  rintro ⟨v₁, p₁⟩
  induction p₁ with
  | nil =>
    rintro ⟨y₂, p₂⟩
    rcases p₂ with - | ⟨p₂, e₂⟩
    · intro; rfl -- Porting note: goal not present in lean3.
    · intro h
      -- Porting note: added `Sigma.mk.inj_iff`
      simp only [mapPath_cons, Sigma.mk.inj_iff] at h
      exfalso
      obtain ⟨h, h'⟩ := h
      rw [← Path.eq_cast_iff_heq rfl h.symm, Path.cast_cons] at h'
      exact (Path.nil_ne_cons _ _) h'
  | cons p₁ e₁ ih =>
    rename_i x₁ y₁
    rintro ⟨y₂, p₂⟩
    rcases p₂ with - | ⟨p₂, e₂⟩
    · intro h
      simp only [mapPath_cons, Sigma.mk.inj_iff] at h
      exfalso
      obtain ⟨h, h'⟩ := h
      rw [← Path.cast_eq_iff_heq rfl h, Path.cast_cons] at h'
      exact (Path.cons_ne_nil _ _) h'
    · rename_i x₂
      intro h
      simp only [mapPath_cons, Sigma.mk.inj_iff] at h
      obtain ⟨hφy, h'⟩ := h
      rw [← Path.cast_eq_iff_heq rfl hφy, Path.cast_cons, Path.cast_rfl_rfl] at h'
      have hφx := Path.obj_eq_of_cons_eq_cons h'
      have hφp := Path.heq_of_cons_eq_cons h'
      have hφe := HEq.trans (Hom.cast_heq rfl hφy _).symm (Path.hom_heq_of_cons_eq_cons h')
      have h_path_star : φ.pathStar u ⟨x₁, p₁⟩ = φ.pathStar u ⟨x₂, p₂⟩ := by
        simp only [Prefunctor.pathStar_apply, Sigma.mk.inj_iff]; exact ⟨hφx, hφp⟩
      cases ih h_path_star
      have h_star : φ.star x₁ ⟨y₁, e₁⟩ = φ.star x₁ ⟨y₂, e₂⟩ := by
        simp only [Prefunctor.star_apply, Sigma.mk.inj_iff]; exact ⟨hφy, hφe⟩
      cases hφ x₁ h_star
      rfl

theorem Prefunctor.pathStar_surjective (hφ : ∀ u, Surjective (φ.star u)) (u : U) :
    Surjective (φ.pathStar u) := by
  dsimp +unfoldPartialApp [Prefunctor.pathStar, Quiver.PathStar.mk]
  rintro ⟨v, p⟩
  induction p with
  | nil =>
    use ⟨u, Path.nil⟩
    simp only [Prefunctor.mapPath_nil, eq_self_iff_true, heq_iff_eq, and_self_iff]
  | cons p' ev ih =>
    obtain ⟨⟨u', q'⟩, h⟩ := ih
    simp only at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨⟨u'', eu⟩, k⟩ := hφ u' ⟨_, ev⟩
    simp only [star_apply, Sigma.mk.inj_iff] at k
    -- Porting note: was `obtain ⟨rfl, rfl⟩ := k`
    obtain ⟨rfl, k⟩ := k
    simp only [heq_eq_eq] at k
    subst k
    use ⟨_, q'.cons eu⟩
    simp only [Prefunctor.mapPath_cons, eq_self_iff_true, heq_iff_eq, and_self_iff]

theorem Prefunctor.pathStar_bijective (hφ : ∀ u, Bijective (φ.star u)) (u : U) :
    Bijective (φ.pathStar u) :=
  ⟨φ.pathStar_injective (fun u => (hφ u).1) _, φ.pathStar_surjective (fun u => (hφ u).2) _⟩

namespace Prefunctor.IsCovering

variable {φ}

protected theorem pathStar_bijective (hφ : φ.IsCovering) (u : U) : Bijective (φ.pathStar u) :=
  φ.pathStar_bijective hφ.1 u

end Prefunctor.IsCovering

section HasInvolutiveReverse

variable [HasInvolutiveReverse U] [HasInvolutiveReverse V]

/-- In a quiver with involutive inverses, the star and costar at every vertex are equivalent.
This map is induced by `Quiver.reverse`. -/
@[simps]
def Quiver.starEquivCostar (u : U) : Quiver.Star u ≃ Quiver.Costar u where
  toFun e := ⟨e.1, reverse e.2⟩
  invFun e := ⟨e.1, reverse e.2⟩
  left_inv e := by simp [Sigma.ext_iff]
  right_inv e := by simp [Sigma.ext_iff]

@[simp]
theorem Quiver.starEquivCostar_apply {u v : U} (e : u ⟶ v) :
    Quiver.starEquivCostar u (Quiver.Star.mk e) = Quiver.Costar.mk (reverse e) :=
  rfl

@[simp]
theorem Quiver.starEquivCostar_symm_apply {u v : U} (e : u ⟶ v) :
    (Quiver.starEquivCostar v).symm (Quiver.Costar.mk e) = Quiver.Star.mk (reverse e) :=
  rfl

variable [Prefunctor.MapReverse φ]

theorem Prefunctor.costar_conj_star (u : U) :
    φ.costar u = Quiver.starEquivCostar (φ.obj u) ∘ φ.star u ∘ (Quiver.starEquivCostar u).symm := by
  ext ⟨v, f⟩ <;> simp

theorem Prefunctor.bijective_costar_iff_bijective_star (u : U) :
    Bijective (φ.costar u) ↔ Bijective (φ.star u) := by
  rw [Prefunctor.costar_conj_star φ, EquivLike.comp_bijective, EquivLike.bijective_comp]

theorem Prefunctor.isCovering_of_bijective_star (h : ∀ u, Bijective (φ.star u)) : φ.IsCovering :=
  ⟨h, fun u => (φ.bijective_costar_iff_bijective_star u).2 (h u)⟩

theorem Prefunctor.isCovering_of_bijective_costar (h : ∀ u, Bijective (φ.costar u)) :
    φ.IsCovering :=
  ⟨fun u => (φ.bijective_costar_iff_bijective_star u).1 (h u), h⟩

end HasInvolutiveReverse
