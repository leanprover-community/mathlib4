/-
Copyright (c) 2025 Quang Minh Nguyen, Xiangyu Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Minh Nguyen, Xiangyu Li
-/
import Mathlib.Combinatorics.SimplicialComplex.Topology.GeomReal.Colimit
import Mathlib.Combinatorics.SimplicialComplex.Topology.SimplexMap
import Mathlib.Combinatorics.SimplicialComplex.Category

/-!
# Induced map on geometric realisations

Given a simplicial map `φ : X ⟶ Y`, we construct the induced continuous map on geometric
realisations `|φ| : |X| ⟶ |Y|`.

There are two complementary constructions.

* **Abstract**: use colimit functoriality for the face diagram `δ_X : X.faces ⥤ TopCat`,
  built from standard simplices and face inclusions, to obtain a map
  `|X| ⟶ |Y|` from a natural transformation
  `δ_X ⟶ φ.face_functor ⋙ δ_Y`.
* **Concrete**: push barycentric coordinates forward along `φ` by summing weights over fibres
  `φ ⁻¹ {y}`. We prove that this map agrees with the abstract one.

## Main definitions

* `GeomReal.map_nat_trans` :
  the natural transformation `δ_X ⟶ φ.face_functor ⋙ δ_Y` whose component at a face `s`
  is `Simplex.map φ s`.
* `GeomReal.map` :
  the induced map `|φ| ⟶ |Y|` in `TopCat` obtained from colimit functoriality.
* `GeomReal.push_forward` :
  the barycentric push-forward of weights along `φ`.
* `GeomReal.map_geom_real` :
  the concrete map on geometric realisations defined via `push_forward`.

## Main results

* `GeomReal.comp_inclusion_face` :
  compatibility of `map_geom_real` with inclusions of faces.
* `GeomReal.map_comp_inclusion_concrete` :
  the abstract and concrete maps agree after precomposing with each inclusion.
* `GeomReal.map_eq_map_geom_real` :
  the abstract `map` equals the concrete `map_geom_real`.

## Implementation notes

* The abstract map is
  `(geom_real_colimit_iso X).inv ≫ colim.map (map_nat_trans φ) ≫
   colimit.pre (delta Y) φ.face_functor ≫ (geom_real_colimit_iso Y).hom`.
* Naturality on simplices is packaged in `Simplex.map_naturality`.

## Tags

simplicial complex, geometric realisation, colimit, functoriality
-/

open CategoryTheory CategoryTheory.Limits TopCat
open SimplicialComplex Simplex

universe u
variable {U V : Type u} [DecidableEq U] [DecidableEq V]
variable {X : SimplicialComplex U} {Y : SimplicialComplex V}

namespace GeomReal

/-- The natural transformation used to define `|φ| : |X| ⟶ |Y|`.

Its component at a face `s : X.faces` is the map of standard simplices
`Simplex.map φ s`, viewed as a morphism in `TopCat`. -/
noncomputable def map_nat_trans (φ : Hom X Y) :
    delta X ⟶ φ.face_functor ⋙ delta Y :=
{ app := fun s =>
    ofHom (ContinuousMap.mk (map φ s) (map_continuous φ s)),
  naturality := by
    intro A B f
    ext p
    simpa [delta_map, Functor.comp_obj, Functor.comp_map, ContinuousMap.comp_apply]
      using map_naturality φ f (p : Simplex (U := U) A.1)}

/-- The induced continuous map on geometric realisations `|φ| : |X| ⟶ |Y|`
constructed via colimit functoriality for the face diagrams. -/
noncomputable def map (φ : Hom X Y)
  [HasColimit (delta X)]
  [HasColimit (delta Y)]
  [HasColimit (φ.face_functor ⋙ delta Y)] :
  of (GeomReal X) ⟶ of (GeomReal Y) := by
  let map₁ := colim.map (map_nat_trans φ)
  let map₂ := colimit.pre (delta Y) φ.face_functor
  exact (geom_real_colimit_iso X).inv ≫ map₁ ≫ map₂ ≫ (geom_real_colimit_iso Y).hom

section ConcreteMap

/-- Barycentric push-forward of weights along a simplicial map.

Given `p : |X|` and `y : V`, `push_forward φ p y` is
`∑_{x ∈ p.face, φ x = y} p.weight x`. This is used to define the concrete
map on geometric realisations. -/
noncomputable def push_forward (φ : Hom X Y) (p : GeomReal X) (y : V) : ℝ :=
  ∑ x ∈ p.face.filter (fun x : U ↦ φ.toFun x = y), p.weight x

/-- The concrete induced map on geometric realisations:
push barycentric coordinates forward along `φ`. -/
noncomputable def map_geom_real (φ : Hom X Y) : GeomReal X → GeomReal Y := by
  intro p
  let B : Finset V := p.face.image φ.toFun
  have hB : (B : Finset V) ∈ Y.faces := by
    simpa using φ.map_faces p.face_mem
  let w : V → ℝ := push_forward φ p
  have h_support : ∀ y, y ∈ B ↔ w y ≠ 0 := by
    intro y;
    have mp : y ∈ B → w y ≠ 0 := by
      intro hy
      rcases (Finset.mem_image).1 hy with ⟨x, hx, rfl⟩
      have hx₀ : p.weight x ≠ 0 := (p.support_eq x).1 hx
      have hx_in : x ∈ p.face.filter (fun z : U ↦ φ.toFun z = φ.toFun x) := by
        exact (Finset.mem_filter).2 ⟨hx, rfl⟩
      have h_weight_pos: (0 : ℝ) < p.weight x := by
        have := (p.range_mem_Icc x).1
        exact lt_of_le_of_ne' this hx₀
      have h_w_pos : (0 : ℝ) < w (φ.toFun x) := by
        have h_le : p.weight x ≤ w (φ.toFun x) := by
          have hx_le :=
            Finset.single_le_sum
              (fun z _ ↦ (p.range_mem_Icc z).1)
              hx_in
          simpa [w, push_forward] using hx_le
        exact lt_of_lt_of_le h_weight_pos h_le
      exact (ne_of_gt h_w_pos)
    have mpr : w y ≠ 0 → y ∈ B := by
      intro hny
      by_contra hnot
      have h_card_zero : (p.face.filter (fun x : U ↦ φ.toFun x = y)).card = 0 := by
        apply Finset.card_eq_zero.2
        apply (Finset.eq_empty_iff_forall_notMem).2
        intro x hx_in
        have : y ∈ B := by
          rcases (Finset.mem_filter).1 hx_in with ⟨hx_face, hxy⟩
          exact (Finset.mem_image).2 ⟨x, hx_face, hxy⟩
        exact hnot this
      have h_wy_zero : w y = 0 := by
        have h_empty :
            (p.face.filter (fun x : U ↦ φ.toFun x = y)) = (∅ : Finset U) := by
          simpa using (Finset.card_eq_zero.1 h_card_zero)
        simp [w, push_forward, h_empty]
      exact (hny h_wy_zero).elim
    simpa using ⟨mp, mpr⟩
  have h_sum : ∑ y ∈ B, w y = 1 := by
    dsimp [w]
    let gfun := fun y => ∑ x ∈ p.face.filter (fun x => φ.toFun x = y), p.weight x
    calc
      ∑ y ∈ B, w y
        = ∑ y ∈ B, ∑ x ∈ p.face.filter (fun x => φ.toFun x = y), p.weight x := rfl
      _ = ∑ y ∈ B, ∑ x ∈ p.face, if φ.toFun x = y then p.weight x else 0 := by
        apply Finset.sum_congr rfl
        intro y hy
        rw [Finset.sum_filter]
      _ = ∑ x ∈ p.face, ∑ y ∈ B, if φ.toFun x = y then p.weight x else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ x ∈ p.face, p.weight x := by
        apply Finset.sum_congr rfl
        intro x hx
        have : φ.toFun x ∈ B := Finset.mem_image_of_mem φ.toFun hx
        simp [this]
    simpa using p.sum_eq_one
  have h_Icc : ∀ y, w y ∈ Set.Icc (0 : ℝ) 1 := by
    intro y
    have h₀ : 0 ≤ w y :=
      Finset.sum_nonneg (fun x hx => (p.range_mem_Icc x).1)
    have h₁ : w y ≤ 1 := by
      let total := h_sum
      by_cases hy : y ∈ B
      · have h_nonneg : ∀ z ∈ B, 0 ≤ w z := by
          intro z hz
          apply Finset.sum_nonneg
          intro x hx
          exact (p.range_mem_Icc x).1
        have h_le_sum : w y ≤ ∑ z ∈ B, w z :=
          Finset.single_le_sum h_nonneg hy
        simpa [total] using h_le_sum
      · have hwy0 : w y = 0 := by
          by_contra hne
          have : y ∈ B := (h_support y).mpr hne
          exact hy this
        simp [hwy0]
    exact ⟨h₀, h₁⟩
  exact
    { face          := B
      face_mem      := hB
      weight        := w
      support_eq    := h_support
      sum_eq_one    := h_sum
      range_mem_Icc := h_Icc }

/-- Compatibility of a colimit leg with the canonical isomorphism
`colimit (δ_X) ≅ |X|`.

More precisely, the morphism `colimit.ι (delta X) s` followed by
`(geom_real_colimit_iso X).hom` *is* the leg of the canonical cocone
`geom_real_cocone X` at `s`. This is a convenient rewrite when composing
morphisms landing in `|X|`. -/
@[simp, reassoc]
lemma colimit_ι_comp_geom_real_colimit_iso_hom
    (X : SimplicialComplex U) (s : X.faces) :
  colimit.ι (delta X) s ≫ (geom_real_colimit_iso X).hom
    = (geom_real_cocone X).ι.app s := by
  simp [geom_real_colimit_iso, geom_real_cocone]

/-- The inverse-direction companion to
`colimit_ι_comp_geom_real_colimit_iso_hom`.

Composing the cocone leg `(geom_real_cocone X).ι.app s` with
`(geom_real_colimit_iso X).inv` yields the canonical colimit leg
`colimit.ι (delta X) s`. This form is often what one needs when
rewriting maps **into** the abstract colimit. -/
@[simp, reassoc]
lemma geom_real_cocone_ι_comp_iso_inv
    (X : SimplicialComplex U) (s : X.faces) :
  (geom_real_cocone X).ι.app s ≫ (geom_real_colimit_iso X).inv
    = colimit.ι (delta X) s := by
  let i := geom_real_colimit_iso X
  have h :
      (geom_real_cocone X).ι.app s
        = colimit.ι (delta X) s ≫ i.hom := by
    rw[colimit_ι_comp_geom_real_colimit_iso_hom (X := X) (s := s).symm]
  calc
    (geom_real_cocone X).ι.app s ≫ i.inv
        = (colimit.ι (delta X) s ≫ i.hom) ≫ i.inv := by
          simp [h]
    _ = colimit.ι (delta X) s := by simp

/-- Compatibility on faces: on the inclusion of a face `s`, the concrete map
`map_geom_real φ` factors through the simplex-level map `Simplex.map φ s`. -/
lemma comp_inclusion_face (φ : Hom X Y) (s : X.faces) :
  (map_geom_real φ) ∘ inclusion s
    = inclusion (s := φ.image_face s) ∘ Simplex.map φ s := by
  funext p
  set lp := (map_geom_real φ) (inclusion s p)
  set rp := (inclusion (s := φ.image_face s) (Simplex.map φ s p))
  have hweight : lp.weight = rp.weight := by
    funext y
    subst lp; subst rp
    dsimp [map_geom_real, inclusion, Simplex.map]
    set SA := (Simplex.supportFinset p).filter (fun x : U => φ.toFun x = y)
    set SB := s.1.filter (fun x : U => φ.toFun x = y)
    have hsub : SA ⊆ SB := by
      intro x hx
      rcases Finset.mem_filter.1 hx with ⟨hxSupp, hxy⟩
      exact Finset.mem_filter.2 ⟨(Finset.mem_filter.1 hxSupp).1, hxy⟩
    have hzero :
        ∀ x ∈ SB, x ∉ SA → p.weight x = 0 := by
      intro x hxSB hxNot
      have hx_not_supp : x ∉ Simplex.supportFinset p := by
        intro hxSupp
        exact hxNot (Finset.mem_filter.2 ⟨hxSupp, (Finset.mem_filter.1 hxSB).2⟩)
      have : ¬ p.weight x ≠ 0 := by
        intro hne; exact hx_not_supp ((Simplex.mem_supportFinset p).mpr hne)
      exact not_not.mp this
    simpa [SA, SB] using Finset.sum_subset hsub hzero
  exact GeomReal.ext_weight hweight

private lemma concrete_side_into_colimit
    (φ : Hom X Y) (s : X.faces) :
  (geom_real_colimit_iso Y).inv ∘
    ((map_geom_real φ) ∘ inclusion s)
  = (map_nat_trans φ).app s ≫
      (geom_real_cocone Y).ι.app ((φ.face_functor).obj s) ≫
      (geom_real_colimit_iso Y).inv := by
  let iY := geom_real_colimit_iso Y
  funext p
  have h := congrArg (fun f => f p) (comp_inclusion_face φ s)
  exact congrArg (fun z => (ConcreteCategory.hom iY.inv) z) h

private lemma abstract_side_into_colimit
    (φ : Hom X Y) (s : X.faces)
    [HasColimit (delta X)]
    [HasColimit (delta Y)]
    [HasColimit (φ.face_functor ⋙ delta Y)] :
  (geom_real_colimit_iso Y).inv ∘ (map φ) ∘ inclusion s
    = (map_nat_trans φ).app s ≫
      (geom_real_cocone Y).ι.app ((φ.face_functor).obj s) ≫
      (geom_real_colimit_iso Y).inv := by
  let iX := geom_real_colimit_iso X
  let iY := geom_real_colimit_iso Y
  funext p
  have h₀' :
    (geom_real_cocone X).ι.app s ≫
      map φ
    =
    (geom_real_cocone X).ι.app s ≫ iX.inv ≫
      colim.map (map_nat_trans φ) ≫
      colimit.pre (delta (U := V) Y) φ.face_functor ≫
      iY.hom := by
    simp [map, iX, iY]
  have h₀ :
    ((geom_real_cocone X).ι.app s ≫
      map φ) ≫ iY.inv
    =
    ((geom_real_cocone X).ι.app s ≫ iX.inv) ≫
      colim.map (map_nat_trans φ) ≫
      colimit.pre (delta Y) φ.face_functor := by
    simpa [Category.assoc] using congrArg (fun f => f ≫ iY.inv) h₀'
  have h :
    ((geom_real_cocone X).ι.app s ≫
      map φ) ≫ iY.inv
    =
    ((map_nat_trans φ).app s ≫
      (geom_real_cocone (U := V) Y).ι.app ((φ.face_functor).obj s)) ≫ iY.inv := by
    calc
      ((geom_real_cocone X).ι.app s ≫ map φ) ≫ iY.inv
          =
        ((geom_real_cocone X).ι.app s ≫ iX.inv) ≫
          colim.map (map_nat_trans φ) ≫
          colimit.pre (delta (U := V) Y) φ.face_functor := h₀
      _ =
        (colimit.ι (delta X) s) ≫
          colim.map (map_nat_trans φ) ≫
          colimit.pre (delta Y) φ.face_functor := by
        rw [geom_real_cocone_ι_comp_iso_inv]
      _ =
        (map_nat_trans φ).app s ≫
          colimit.ι (delta Y) ((φ.face_functor).obj s) := by
        simp
      _ =
        (map_nat_trans φ).app s ≫
          ((geom_real_cocone Y).ι.app ((φ.face_functor).obj s) ≫ iY.inv) := by
        rw [geom_real_cocone_ι_comp_iso_inv]
  have h' := congrArg (fun f => (ConcreteCategory.hom f) p) h
  simpa [ConcreteCategory.comp_apply, Category.assoc,
         geom_real_cocone, inclusion] using h'

/-- The abstract and concrete constructions agree after precomposing with every
face inclusion. -/
lemma map_comp_inclusion_concrete (φ : Hom X Y) (s : X.faces)
    [HasColimit (delta X)]
    [HasColimit (delta Y)]
    [HasColimit (φ.face_functor ⋙ delta Y)] :
  (map φ : GeomReal X → GeomReal Y) ∘ inclusion s
    =
  map_geom_real φ ∘ inclusion s := by
  funext p
  let iX := geom_real_colimit_iso X
  let iY := geom_real_colimit_iso Y
  have h :
    iY.inv ( (map φ) ((inclusion s) p) ) = iY.inv ( (map_geom_real φ) ((inclusion s) p) ) := by
    let target_expr := ((map_nat_trans φ).app s ≫
        (geom_real_cocone Y).ι.app (φ.face_functor.obj s) ≫ iY.inv) p
    have h_abs : iY.inv (map φ (inclusion s p)) = target_expr := by
      exact congr_fun (abstract_side_into_colimit φ s) p
    have h_conc : iY.inv (map_geom_real φ (inclusion s p)) = target_expr := by
      exact congr_fun (concrete_side_into_colimit φ s) p
    rw [h_abs, h_conc]
  have h_inj : Function.Injective ⇑(iY.inv) := by
    intro _ _ hab
    replace hab := congr_arg ⇑(iY.hom) hab
    simpa [← ConcreteCategory.comp_apply] using hab
  exact h_inj h

/-- The abstract induced map on geometric realisations equals the concrete
push-forward of barycentric coordinates. -/
lemma map_eq_map_geom_real (φ : Hom X Y)
  [HasColimit (delta X)]
  [HasColimit (delta Y)]
  [HasColimit (φ.face_functor ⋙ delta Y)] :
  (map φ : GeomReal X → GeomReal Y) = map_geom_real φ := by
  apply function_ext
  intro s
  exact map_comp_inclusion_concrete φ s

end ConcreteMap

end GeomReal
