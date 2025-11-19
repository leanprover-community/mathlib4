/-
Copyright (c) 2025 Xiangyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xiangyu Li
-/
import Mathlib.Combinatorics.SimplicialComplex.Hom
import Mathlib.Combinatorics.SimplicialComplex.Category
import Mathlib.Combinatorics.SimplicialComplex.Topology.GeomReal.Map
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Functoriality of geometric realisation

We show that geometric realisation is functorial with respect to simplicial maps and package
this as a functor `SimplicialComplexCat ⥤ TopCat`.

Besides constructing the functor, we record concrete `[simp]` lemmas for the push-forward on
barycentric coordinates, expressing that it preserves identities and compositions.

## Main definitions

* `GeomReal.geomRealFunctor` :
  the functor `SimplicialComplexCat ⥤ TopCat` sending `X` to `|X|` and a simplicial map
  `φ : X ⟶ Y` to the induced continuous map `|φ| : |X| ⟶ |Y|`.

## Main results

* `[simp] GeomReal.map_geom_real_id` :
  for the identity simplicial map, the concrete push-forward `map_geom_real` is `id`.
* `[simp] GeomReal.map_geom_real_comp` :
  `map_geom_real (ψ ∘ φ) = map_geom_real ψ ∘ map_geom_real φ`.

These concrete identities are used to verify the functor laws for `geomRealFunctor`.

## Implementation notes

* The functorial map on morphisms is the abstract colimit map `GeomReal.map`. For the functor
  laws we switch to the concrete description via `GeomReal.map_eq_map_geom_real`, then use
  function extensionality on weights (`GeomReal.ext_weight`) to close the goals.
* We freely use `ConcreteCategory.hom` to view morphisms in `TopCat` as continuous maps.

## Tags

simplicial complex, geometric realisation, functor, category theory
-/

universe u
variable {U V W : Type u} [DecidableEq U] [DecidableEq V] [DecidableEq W]
variable {X : SimplicialComplex U} {Y : SimplicialComplex V} {Z : SimplicialComplex W}

open CategoryTheory SimplicialComplex SimplicialComplex.Hom
open SimplicialComplexCat GeomReal

namespace GeomReal

/-- **Identity law for the concrete map on realisations.**

The concrete push-forward `map_geom_real` sends the identity simplicial map to the identity
continuous map on `|X|`. -/
@[simp]
lemma map_geom_real_id : map_geom_real (Hom.id X) = id := by
  funext p
  have h_weight :
      (map_geom_real (Hom.id X) p : U → ℝ) = p.weight := by
    funext y
    dsimp [map_geom_real, push_forward, Hom.id]
    by_cases hy : y ∈ p.face
    · have hfilter :
          p.face.filter (fun x : U ↦ x = y) = {y} := by
        ext x; by_cases hxy : x = y
        · subst hxy; simp [Finset.mem_filter, hy]
        · simp [Finset.mem_filter, hxy]
      rw [hfilter]; simp
    · have hfilter :
          p.face.filter (fun x : U ↦ x = y) = ∅ := by
        ext x; by_cases hxy : x = y
        · subst hxy; simp [Finset.mem_filter, hy]
        · simp [Finset.mem_filter, hxy]
      have hw0 : p.weight y = 0 := by
        by_contra hne
        exact hy ((p.support_eq y).mpr hne)
      rw [hfilter]; simp [hw0]
  exact ext_weight h_weight

omit [DecidableEq U] in
/-- **Composition law for the concrete map on realisations.**

For simplicial maps `φ : X ⟶ Y` and `ψ : Y ⟶ Z` one has
`map_geom_real (ψ ∘ φ) = map_geom_real ψ ∘ map_geom_real φ`. -/
@[simp]
lemma map_geom_real_comp (φ : Hom X Y) (ψ : Hom Y Z) :
    map_geom_real (comp ψ φ) = map_geom_real ψ ∘ map_geom_real φ := by
  funext p
  have h_face :
      (map_geom_real (comp ψ φ) p).face
        = (map_geom_real ψ (map_geom_real φ p)).face := by
    dsimp [map_geom_real, push_forward]
    simp [Finset.image_image, comp]
  have h_weight :
      (map_geom_real (comp ψ φ) p : W → ℝ)
        = (map_geom_real ψ (map_geom_real φ p) : W → ℝ) := by
    funext y
    dsimp [map_geom_real, push_forward]
    let I : Finset V := p.face.image φ.toFun
    calc
      (∑ x ∈ p.face.filter (fun x : U ↦ ψ.toFun (φ.toFun x) = y), p.weight x)
          = ∑ x ∈ p.face, (if ψ.toFun (φ.toFun x) = y then p.weight x else 0) := by
            simp [Finset.sum_filter]
      _ = ∑ x ∈ p.face,
            (∑ z ∈ I.filter (fun z : V ↦ ψ.toFun z = y),
               if φ.toFun x = z then p.weight x else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        have hxIm : φ.toFun x ∈ I := Finset.mem_image_of_mem _ hx
        by_cases hψ : ψ.toFun (φ.toFun x) = y
        · have : φ.toFun x ∈ I.filter (fun z : V ↦ ψ.toFun z = y) :=
            Finset.mem_filter.mpr ⟨hxIm, hψ⟩
          simp [this, hψ]
        · have : φ.toFun x ∉ I.filter (fun z : V ↦ ψ.toFun z = y) := by
            intro hmem; exact hψ (Finset.mem_filter.mp hmem).2
          simp [this, hψ]
      _ = ∑ z ∈ I.filter (fun z : V ↦ ψ.toFun z = y),
            ∑ x ∈ p.face, if φ.toFun x = z then p.weight x else 0 := by
        simpa using
          Finset.sum_comm
            (s := p.face)
            (t := I.filter (fun z : V ↦ ψ.toFun z = y))
            (f := fun x (z : V) => if φ.toFun x = z then p.weight x else 0)
      _ = ∑ z ∈ I.filter (fun z : V ↦ ψ.toFun z = y),
            ∑ x ∈ p.face.filter (fun x : U ↦ φ.toFun x = z), p.weight x := by
        apply Finset.sum_congr rfl
        intro z hz
        simp [Finset.sum_filter]
  exact ext_weight h_weight


/-- **Geometric realisation as a functor** `SimplicialComplexCat ⥤ TopCat`.

* On objects: `X ↦ |X|`.
* On morphisms: a simplicial map `φ : X ⟶ Y` is sent to the induced continuous map
  `|φ| : |X| ⟶ |Y|` (implemented as the abstract colimit map `GeomReal.map`).

The functor laws follow from the concrete identities
`map_geom_real_id` and `map_geom_real_comp` via `GeomReal.map_eq_map_geom_real`. -/
noncomputable def geomRealFunctor : SimplicialComplexCat ⥤ TopCat where
  obj A := TopCat.of (GeomReal A.X)
  map {A B} (f : A ⟶ B) := map f

  map_id A := by
    ext p <;>
      (suffices hEq : (ConcreteCategory.hom (map (𝟙 A))) p = p
        from by simp [hEq]
       exact
         calc
           (ConcreteCategory.hom (map (𝟙 A))) p
               = map_geom_real (Hom.id A.X) p := by
                 simpa using
                   congrArg (fun (k : GeomReal A.X → GeomReal A.X) => k p)
                            (map_eq_map_geom_real (Hom.id A.X))
           _   = p := by
                 simp
      )

  map_comp {A B C} (f : A ⟶ B) (g : B ⟶ C) := by
    ext p <;>
      (suffices hEq :
          (ConcreteCategory.hom (map (f ≫ g))) p
            = (ConcreteCategory.hom (map g)) ((ConcreteCategory.hom (map f)) p)
        from by simp [hEq]
       exact
         calc
           (ConcreteCategory.hom (map (f ≫ g))) p
               = map_geom_real (comp g f) p := by
                 simpa using
                   congrArg (fun (k : GeomReal A.X → GeomReal C.X) => k p)
                            (map_eq_map_geom_real (comp g f))
           _   = (ConcreteCategory.hom (map g)) (map_geom_real f p) := by
                 simpa using
                   congrArg (fun (k : GeomReal B.X → GeomReal C.X) =>
                     k (map_geom_real f p))
                     (map_eq_map_geom_real g).symm
           _   = (ConcreteCategory.hom (map g))
                   ((ConcreteCategory.hom (map f)) p) := by
                 simpa using
                   congrArg (fun x => (ConcreteCategory.hom (map g)) x)
                     (congrArg (fun (k : GeomReal A.X → GeomReal B.X) => k p)
                       (map_eq_map_geom_real f).symm)
      )

end GeomReal
