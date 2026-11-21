/-
Copyright (c) 2026 Robert Maxton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Maxton
-/
module

public import Mathlib.Topology.Gavrilovich.Space
public import Mathlib.Topology.Homeomorph.Lemmas

import Mathlib.Tactic.FinCases

/-!
# Models: existing types as Gavrilovich spaces

`Model X L E` says that the finite space `X` (an existing type, such as `Prop`) is homeomorphic to
the diagram space `Space L E`, with a list `pts` of its points in the order of `L`. Diagram spaces
stay the convenient way to make anonymous spaces on the fly; a model lets the same notation and
automation reach a space that already exists, by transport along `Model.homeo : X ≃ₜ Space L E`.

* `pt(T) : Prop` is the point named `T` of the model, as the element listed in `pts` (`True`).
* A diagram morphism whose expected type is `X ⟶ Y`, for `X` or `Y` (objects of `TopCat`) with a
  model, is conjugated by `Model.iso ↑X : of ↑X ≅ Space L E`, e.g.
  `(⌜T → F⌟ ⇢ ⌜T=F⌟ : of Prop ⟶ of PUnit)`.
* `simp` evaluates `Model.homeo x` at the elements `x` listed in `pts` (`Model.reduceApply`), and
  `Model.homeo.symm` at points `pt(…)` of the space (`Model.homeo_symm_mk`, and then
  `Model.reducePtsGetElem`), so that such a morphism is evaluated at `True` by `simp`.
* Products of models (and of diagram spaces), such as `↑(⌜a → b⌟ ⊗ of Prop)`, have models with
  literal points, by `Model.prod` (a `deferred_def`, in `Mathlib.Tactic.Gavrilovich.ModelProd`),
  built from `Model.prodOfIsProd`.
* `Model.forallPts` and `Model.existsPts` (not `simp` lemmas by default) expand quantifiers over a
  model into conjunctions and disjunctions over `pts`.
* Morphisms between models have decidable equality and are a `Fintype`, by transport
  (`Model.homEquiv`, in `Mathlib.Tactic.Gavrilovich.Relabel`). `decide` can only evaluate this when
  `Model.homeo` computes, as for `Model.ofList` with a computable `DecidableEq`; for `Prop` it
  doesn't.

Instances are built with `Model.ofList`, from the list of points, a proof that it lists every point
exactly once, and a proof that it has the specialization order of `Space L E`.

## Main definitions

* `Gavrilovich.Model`: the class.
* `Gavrilovich.Model.ofList`: its main constructor.
* `Gavrilovich.Model.iso`: the isomorphism `of X ≅ Space L E` in `TopCat`.
* Instances for `Space L E` itself, `Prop` (as `⌜T → F⌟`), `PUnit` (as `⌜*⌟`) and `ULift X`.
-/

@[expose] public section

universe w v u

open CategoryTheory Topology

namespace Gavrilovich

/-- The finite space `X` is (homeomorphic to) the diagram space `Space L E`, with `pts` listing its
points in the order of `L`: `homeo.symm` sends the `k`-th point of the space to `pts[k]`.

`L` and `E` are `outParam`s, so the diagram of `X` is found from `X` alone. Build instances with
`Model.ofList`. -/
class Model (X : Type u) [TopologicalSpace X] {α : outParam Type}
    (L : outParam (List (List α))) (E : outParam (List (ℕ × ℕ))) where
  /-- The points, in the order of `L`. -/
  pts : List X
  length_pts : pts.length = L.length
  /-- The homeomorphism with the diagram space. -/
  homeo : X ≃ₜ Space.{u} L E
  homeo_symm_mk (k : ℕ) (h : k < L.length) : homeo.symm (Space.mk k h) = pts[k]'(length_pts ▸ h)

namespace Model

variable {X : Type u} [TopologicalSpace X] {Y : Type v} [TopologicalSpace Y]
  {α β : Type} {L : List (List α)} {E : List (ℕ × ℕ)} {L' : List (List β)} {E' : List (ℕ × ℕ)}

section
variable [Model X L E]

attribute [simp] homeo_symm_mk

@[simp] lemma homeo_getElem (k : ℕ) (h : k < (pts : List X).length) :
    homeo (pts[k] : X) = (Space.mk k (length_pts (X := X) ▸ h) : Space.{u} L E) := by
  rw [← homeo_symm_mk (X := X) k (length_pts (X := X) ▸ h), Homeomorph.apply_symm_apply]

/-- `homeo_getElem` with the point given up to defeq, which is how `Model.reduceApply` uses it. -/
lemma homeo_eq_of_getElem_eq (k : ℕ) (h : k < (pts : List X).length) (x : X) (e : pts[k] = x) :
    homeo x = (Space.mk k (length_pts (X := X) ▸ h) : Space.{u} L E) := by
  rw [← e, homeo_getElem]

lemma mem_pts (x : X) : x ∈ (pts : List X) := by
  rw [← (homeo (X := X)).symm_apply_apply x]
  obtain ⟨⟨k, hk⟩⟩ := homeo (X := X) x
  rw [show (⟨⟨k, hk⟩⟩ : Space.{u} L E) = Space.mk k hk from rfl, homeo_symm_mk]
  exact List.getElem_mem _

lemma nodup_pts : (pts : List X).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j e
  have := congrArg (homeo (X := X)) e
  simp only [List.get_eq_getElem, homeo_getElem, Space.mk_inj] at this
  exact Fin.ext this

lemma forall_iff_foldr (p : X → Prop) : (∀ x, p x) ↔ ((pts : List X).map p).foldr And True := by
  suffices ∀ l : List X, (l.map p).foldr And True ↔ ∀ x ∈ l, p x by
    rw [this]; exact ⟨fun h x _ => h x, fun h x => h x (mem_pts x)⟩
  intro l; induction l <;> simp_all

lemma exists_iff_foldr (p : X → Prop) : (∃ x, p x) ↔ ((pts : List X).map p).foldr Or False := by
  suffices ∀ l : List X, (l.map p).foldr Or False ↔ ∃ x ∈ l, p x by
    rw [this]; exact ⟨fun ⟨x, h⟩ => ⟨x, mem_pts x, h⟩, fun ⟨x, _, h⟩ => ⟨x, h⟩⟩
  intro l; induction l <;> simp_all

instance : Finite X := .of_injective _ (homeo (X := X)).injective

end

/-! ### Building models -/

/-- A map out of an Alexandrov-discrete space that preserves specialization is continuous. -/
protected lemma continuous_of_specializes {X Y : Type*} [TopologicalSpace X] [AlexandrovDiscrete X]
    [TopologicalSpace Y] {f : X → Y} (hf : ∀ x y, x ⤳ y → f x ⤳ f y) : Continuous f := by
  constructor; intro s hs
  rw [isOpen_iff_forall_specializes]
  exact fun x y hxy hy => (hf x y hxy).mem_open hs hy

/-- A model of `X` from the list `pts` of its points, which lists each point exactly once and has
the specialization order of `Space L E`. For a type with a computable `DecidableEq`, `Fintype` and
specialization order, all of the conditions can be proved by `decide`. -/
@[instance_reducible]
def ofList [DecidableEq X] (pts : List X) (length_pts : pts.length = L.length)
    (nodup : pts.Nodup) (mem_pts : ∀ x, x ∈ pts)
    (specializes_iff : ∀ i j : Fin L.length,
      pts[i.val]'(i.isLt.trans_eq length_pts.symm) ⤳ pts[j.val]'(j.isLt.trans_eq length_pts.symm) ↔
        (Space.mk i i.isLt : Space.{u} L E) ⤳ Space.mk j j.isLt) :
    Model X L E :=
  have : Finite X := .of_surjective (fun i : Fin pts.length => pts[i]) fun x =>
    have ⟨i, hi, e⟩ := List.getElem_of_mem (mem_pts x); ⟨⟨i, hi⟩, e⟩
  have hlt (x : X) : pts.idxOf x < L.length :=
    (List.idxOf_lt_length_of_mem (mem_pts x)).trans_eq length_pts
  have hget (x : X) : pts[pts.idxOf x]'((hlt x).trans_eq length_pts.symm) = x :=
    List.getElem_idxOf _
  { pts, length_pts
    homeo :=
    { toFun x := Space.mk (pts.idxOf x) (hlt x)
      invFun y := pts[y.idx.val]'(y.idx.isLt.trans_eq length_pts.symm)
      left_inv := hget
      right_inv := by
        rintro ⟨⟨k, hk⟩⟩
        change (Space.mk _ _ : Space.{u} L E) = Space.mk k hk
        rw [Space.mk_inj]
        exact nodup.idxOf_getElem _ _
      continuous_toFun := Model.continuous_of_specializes fun x y h => by
        rw [← hget x, ← hget y] at h
        exact (specializes_iff ⟨_, hlt x⟩ ⟨_, hlt y⟩).1 h
      continuous_invFun := Model.continuous_of_specializes fun ⟨⟨i, hi⟩⟩ ⟨⟨j, hj⟩⟩ h =>
        (specializes_iff ⟨i, hi⟩ ⟨j, hj⟩).2 h }
    homeo_symm_mk _ _ := rfl }

/-- A model of `X` given by a homeomorphism with a diagram space, listing the points as the images
of those of the space. -/
@[instance_reducible]
def ofHomeo (e : X ≃ₜ Space.{u} L E) : Model X L E where
  pts := Space.all.map e.symm
  length_pts := by simp [Space.length_all]
  homeo := e
  homeo_symm_mk k h := by simp [Space.all]

/-! ### The isomorphism in `TopCat` -/

/-- The isomorphism `of X ≅ Space L E` in `TopCat` given by a model. It takes the type `X` rather
than an object of `TopCat`, so that its `simp` lemmas apply to `of X` (whose carrier reduces to
`X`); for an object `Z`, `Model.iso ↑Z : of ↑Z ≅ Space L E` is an isomorphism from `Z` itself. -/
def iso (X : Type u) [TopologicalSpace X] [Model X L E] : TopCat.of X ≅ Space.{u} L E :=
  TopCat.isoOfHomeo homeo

@[simp] lemma iso_hom_apply [Model X L E] (x : X) : (iso X).hom x = homeo x := rfl
@[simp] lemma iso_inv_apply [Model X L E] (y : Space.{u} L E) : (iso X).inv y = homeo.symm y := rfl

/-- `iso_hom_apply`, for `TopCat.Hom.hom` (to which `simp` unfolds `ConcreteCategory.hom`). -/
@[simp] lemma hom_iso_hom [Model X L E] :
    (iso X).hom.hom = ((homeo : X ≃ₜ Space.{u} L E) : C(X, Space.{u} L E)) := rfl
/-- `iso_inv_apply`, for `TopCat.Hom.hom` (to which `simp` unfolds `ConcreteCategory.hom`). -/
@[simp] lemma hom_iso_inv [Model X L E] :
    (iso X).inv.hom = ((homeo : X ≃ₜ Space.{u} L E).symm : C(Space.{u} L E, X)) := rfl

/-! ### Instances -/

/-- A diagram space is a model of itself. -/
instance (priority := low) instSpace : Model (Space.{u} L E) L E where
  pts := Space.all
  length_pts := Space.length_all
  homeo := .refl _
  homeo_symm_mk k h := by simp [Space.all]

/-- The homeomorphism between the same diagram space in two universes. -/
def _root_.Gavrilovich.Space.uliftHomeo : Space.{u} L E ≃ₜ Space.{v} L E where
  toFun x := Space.mk x.idx.val x.idx.isLt
  invFun x := Space.mk x.idx.val x.idx.isLt
  continuous_toFun := Topology.IsUpperSet.monotone_iff_continuous.1 fun _ _ h => h
  continuous_invFun := Topology.IsUpperSet.monotone_iff_continuous.1 fun _ _ h => h

@[simp] lemma _root_.Gavrilovich.Space.uliftHomeo_mk (k : ℕ) (h : k < L.length) :
    Space.uliftHomeo.{u, v} (E := E) (Space.mk k h) = Space.mk k h := rfl

@[simp] lemma _root_.Gavrilovich.Space.uliftHomeo_symm_mk (k : ℕ)
    (h : k < L.length) : (Space.uliftHomeo.{u, v} (E := E)).symm (Space.mk k h) = Space.mk k h :=
  rfl

instance [Model X L E] : Model (ULift.{w} X) L E where
  pts := (pts : List X).map ULift.up
  length_pts := by simp [length_pts]
  homeo := Homeomorph.ulift.trans (homeo.trans Space.uliftHomeo)
  homeo_symm_mk k h := by
    apply ULift.ext
    simp [Homeomorph.ulift, homeo_symm_mk]

open Classical in
/-- `Prop`, with the Sierpinski topology, is `⌜T → F⌟`. -/
noncomputable instance : Model Prop [["F"], ["T"]] [(1, 0)] :=
  ofList [False, True] rfl (by simp) (fun p => by by_cases p <;> simp_all)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;>
        simp only [List.getElem_cons_zero, List.getElem_cons_succ, le_Prop_eq, Std.le_refl,
          Topology.IsUpperSet.specializes_iff_le, imp_false, not_true_eq_false, false_iff,
          implies_true, true_iff] <;>
        decide)

/-- The one-point space is `⌜*⌟`. -/
instance : Model PUnit.{u + 1} [["*"]] [] :=
  ofList [PUnit.unit] rfl (by simp) (fun _ => by simp)
    (by intro i j; fin_cases i; fin_cases j; exact iff_of_true specializes_rfl specializes_rfl)

end Model

/-! ### Products -/

namespace Space

variable {α β γ : Type} {L : List (List α)} {E : List (ℕ × ℕ)} {L' : List (List β)}
  {E' : List (ℕ × ℕ)} {L'' : List (List γ)} {E'' : List (ℕ × ℕ)}

/-- `Space L'' E''` is the product of `Space L E` and `Space L' E'`, with the point `(a, b)` at
index `a * L'.length + b` (as for `finProdFinEquiv`). Both conditions are meant to be proved by
`decide`. -/
structure IsProd (L : List (List α)) (E : List (ℕ × ℕ)) (L' : List (List β))
    (E' : List (ℕ × ℕ)) (L'' : List (List γ)) (E'' : List (ℕ × ℕ)) : Prop where
  length_eq : L''.length = L.length * L'.length
  le_iff : ∀ (a b : Fin L.length) (c d : Fin L'.length),
    (mk (finProdFinEquiv (a, c)) ((finProdFinEquiv (a, c)).isLt.trans_eq length_eq.symm) :
        Space.{0} L'' E'') ≤
      mk (finProdFinEquiv (b, d)) ((finProdFinEquiv (b, d)).isLt.trans_eq length_eq.symm) ↔
    (mk a a.isLt : Space.{0} L E) ≤ mk b b.isLt ∧ (mk c c.isLt : Space.{0} L' E') ≤ mk d d.isLt

/-- The bijection between a product of two spaces and a space that is their product, sending
`(a, b)` to `a * L'.length + b`. -/
def prodEquiv (h : IsProd L E L' E' L'' E'') :
    Space.{u} L E × Space.{u} L' E' ≃ Space.{u} L'' E'' :=
  ((Pts.equivFin.prodCongr Pts.equivFin).trans finProdFinEquiv).trans
    ((finCongr h.length_eq.symm).trans Pts.equivFin.symm)

lemma prodEquiv_specializes_iff (h : IsProd L E L' E' L'' E'')
    (p q : Space.{u} L E × Space.{u} L' E') : prodEquiv h p ⤳ prodEquiv h q ↔ p ⤳ q := by
  obtain ⟨x, y⟩ := p
  obtain ⟨x', y'⟩ := q
  rw [specializes_prod, Topology.IsUpperSet.specializes_iff_le,
    Topology.IsUpperSet.specializes_iff_le, Topology.IsUpperSet.specializes_iff_le]
  exact h.le_iff x'.idx x.idx y'.idx y.idx

/-- The homeomorphism between a product of two spaces and a space that is their product
(`IsProd`). -/
def prodHomeo (h : IsProd L E L' E' L'' E'') :
    Space.{u} L E × Space.{u} L' E' ≃ₜ Space.{u} L'' E'' where
  toEquiv := prodEquiv h
  continuous_toFun := Model.continuous_of_specializes fun p q hpq =>
    (prodEquiv_specializes_iff h p q).2 hpq
  continuous_invFun := Model.continuous_of_specializes fun z z' hz => by
    rw [← (prodEquiv h).apply_symm_apply z, ← (prodEquiv h).apply_symm_apply z'] at hz
    exact (prodEquiv_specializes_iff h _ _).1 hz

end Space

namespace Model

variable {X : Type u} [TopologicalSpace X] {Y : Type u} [TopologicalSpace Y]
  {α β : Type} {L : List (List α)} {E : List (ℕ × ℕ)} {L' : List (List β)} {E' : List (ℕ × ℕ)}

variable {γ : Type} {L'' : List (List γ)} {E'' : List (ℕ × ℕ)} [Model X L E] [Model Y L' E']

/-- The model of `X × Y` given by a space `Space L'' E''` that is the product of the diagram
spaces of `X` and `Y` (`Space.IsProd`), with the points `pts` listed as `(x, y)` in the order of
`finProdFinEquiv`. The equation `hpts` is meant to be proved by `rfl`, for a literal `pts`.

`Model.prod`, a `deferred_def`, computes all of these for concrete factors; this is the
construction behind it. -/
@[instance_reducible]
def prodOfIsProd (h : Space.IsProd L E L' E' L'' E'') (pts : List (X × Y))
    (hpts : pts = List.ofFn fun k : Fin (L.length * L'.length) =>
      ((Model.pts (X := X))[(finProdFinEquiv.symm k).fst.val]'
          ((finProdFinEquiv.symm k).fst.isLt.trans_eq length_pts.symm),
        (Model.pts (X := Y))[(finProdFinEquiv.symm k).snd.val]'
          ((finProdFinEquiv.symm k).snd.isLt.trans_eq length_pts.symm))) :
    Model (X × Y) L'' E'' where
  pts := pts
  length_pts := by rw [hpts, List.length_ofFn, h.length_eq]
  homeo := (homeo.prodCongr homeo).trans (Space.prodHomeo h)
  homeo_symm_mk k hk := by
    subst hpts
    rw [List.getElem_ofFn]
    exact Prod.ext (homeo_symm_mk (X := X) _ _) (homeo_symm_mk (X := Y) _ _)

end Model

end Gavrilovich
