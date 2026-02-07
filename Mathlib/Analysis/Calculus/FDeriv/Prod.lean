/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov, Eric Wieser
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Calculus.TangentCone.Defs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Linear

/-!
# Derivative of the Cartesian product of functions

For detailed documentation of the Fréchet derivative,
see the module docstring of `Mathlib/Analysis/Calculus/FDeriv/Basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of
Cartesian products of functions, and functions into Pi-types.
-/

public section


open Filter Asymptotics ContinuousLinearMap Set Metric Topology NNReal ENNReal

noncomputable section

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {F : Type*} [AddCommGroup F] [Module 𝕜 F] [TopologicalSpace F]
variable {G : Type*} [AddCommGroup G] [Module 𝕜 G] [TopologicalSpace G]
variable {G' : Type*} [AddCommGroup G'] [Module 𝕜 G'] [TopologicalSpace G']

section CartesianProduct

/-! ### Derivative of the Cartesian product of two functions -/


section Prod

variable [ContinuousSMul 𝕜 F] [ContinuousSMul 𝕜 G]
variable {f f₀ f₁ g : E → F}
variable {f' f₀' f₁' g' : E →L[𝕜] F}
variable (e : E →L[𝕜] F)
variable {x : E}
variable {s t : Set E}
variable {L : Filter E}
variable {f₂ : E → G} {f₂' : E →L[𝕜] G}

protected theorem HasStrictFDerivAt.prodMk (hf₁ : HasStrictFDerivAt f₁ f₁' x)
    (hf₂ : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
  .of_isLittleOTVS <| hf₁.isLittleOTVS.prodMk hf₂.isLittleOTVS

theorem HasFDerivAtFilter.prodMk (hf₁ : HasFDerivAtFilter f₁ f₁' x L)
    (hf₂ : HasFDerivAtFilter f₂ f₂' x L) :
    HasFDerivAtFilter (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x L :=
  .of_isLittleOTVS <| hf₁.isLittleOTVS.prodMk hf₂.isLittleOTVS

@[fun_prop]
nonrec theorem HasFDerivWithinAt.prodMk (hf₁ : HasFDerivWithinAt f₁ f₁' s x)
    (hf₂ : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') s x :=
  hf₁.prodMk hf₂

@[fun_prop]
nonrec theorem HasFDerivAt.prodMk (hf₁ : HasFDerivAt f₁ f₁' x) (hf₂ : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₁ x, f₂ x)) (f₁'.prod f₂') x :=
  hf₁.prodMk hf₂

@[fun_prop]
theorem DifferentiableWithinAt.prodMk (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x : E => (f₁ x, f₂ x)) s x :=
  (hf₁.hasFDerivWithinAt.prodMk hf₂.hasFDerivWithinAt).differentiableWithinAt

@[simp, fun_prop]
theorem DifferentiableAt.prodMk (hf₁ : DifferentiableAt 𝕜 f₁ x) (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x : E => (f₁ x, f₂ x)) x :=
  (hf₁.hasFDerivAt.prodMk hf₂.hasFDerivAt).differentiableAt

@[fun_prop]
theorem DifferentiableOn.prodMk (hf₁ : DifferentiableOn 𝕜 f₁ s) (hf₂ : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x : E => (f₁ x, f₂ x)) s := fun x hx => (hf₁ x hx).prodMk (hf₂ x hx)

@[simp, fun_prop]
theorem Differentiable.prodMk (hf₁ : Differentiable 𝕜 f₁) (hf₂ : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x : E => (f₁ x, f₂ x) := fun x ↦
  (hf₁ x).prodMk (hf₂ x)

variable [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousAdd G]
  [T2Space F] [T2Space G]

theorem DifferentiableAt.fderiv_prodMk (hf₁ : DifferentiableAt 𝕜 f₁ x)
    (hf₂ : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x : E => (f₁ x, f₂ x)) x = (fderiv 𝕜 f₁ x).prod (fderiv 𝕜 f₂ x) :=
  (hf₁.hasFDerivAt.prodMk hf₂.hasFDerivAt).fderiv

theorem DifferentiableWithinAt.fderivWithin_prodMk (hf₁ : DifferentiableWithinAt 𝕜 f₁ s x)
    (hf₂ : DifferentiableWithinAt 𝕜 f₂ s x) (hxs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x : E => (f₁ x, f₂ x)) s x =
      (fderivWithin 𝕜 f₁ s x).prod (fderivWithin 𝕜 f₂ s x) :=
  (hf₁.hasFDerivWithinAt.prodMk hf₂.hasFDerivWithinAt).fderivWithin hxs

end Prod

@[fun_prop]
theorem hasFDerivAt_prodMk_left (e₀ : E) (f₀ : F) :
    HasFDerivAt (fun e : E => (e, f₀)) (inl 𝕜 E F) e₀ :=
  .of_isLittleOTVS <| .congr_left (.zero _ _) <| by simp

@[fun_prop]
theorem hasFDerivAt_prodMk_right (e₀ : E) (f₀ : F) :
    HasFDerivAt (fun f : F => (e₀, f)) (inr 𝕜 E F) f₀ :=
  .of_isLittleOTVS <| .congr_left (.zero _ _) <| by simp

section Fst

variable {s : Set E} {x : E} {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F} {L : Filter E}

@[fun_prop]
theorem hasStrictFDerivAt_fst : HasStrictFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  (fst 𝕜 E F).hasStrictFDerivAt

@[fun_prop]
protected theorem HasStrictFDerivAt.fst (h : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  (fst 𝕜 F G).comp_hasStrictFDerivAt h

theorem hasFDerivAtFilter_fst {L : Filter (E × F)} :
    HasFDerivAtFilter Prod.fst (fst 𝕜 E F) p L :=
  (fst 𝕜 E F).hasFDerivAtFilter

protected theorem HasFDerivAtFilter.fst (h : HasFDerivAtFilter f₂ f₂' x L) :
    HasFDerivAtFilter (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x L :=
  (fst 𝕜 F G).comp_hasFDerivAtFilter h

@[fun_prop]
theorem hasFDerivAt_fst : HasFDerivAt (@Prod.fst E F) (fst 𝕜 E F) p :=
  hasFDerivAtFilter_fst

@[fun_prop]
protected theorem HasFDerivAt.fst (h : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') x :=
  HasFDerivAtFilter.fst h

@[fun_prop]
theorem hasFDerivWithinAt_fst {s : Set (E × F)} :
    HasFDerivWithinAt Prod.fst (fst 𝕜 E F) s p :=
  hasFDerivAtFilter_fst

@[fun_prop]
protected theorem HasFDerivWithinAt.fst (h : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₂ x).1) ((fst 𝕜 F G).comp f₂') s x :=
  HasFDerivAtFilter.fst h

@[fun_prop]
theorem differentiableAt_fst : DifferentiableAt 𝕜 Prod.fst p :=
  hasFDerivAt_fst.differentiableAt

@[simp, fun_prop]
protected theorem DifferentiableAt.fst (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).1) x :=
  (fst 𝕜 F G).comp_differentiableAt h

@[fun_prop]
theorem differentiable_fst : Differentiable 𝕜 (Prod.fst : E × F → E) := fun _ =>
  differentiableAt_fst

@[simp, fun_prop]
protected theorem Differentiable.fst (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).1 :=
  (fst 𝕜 F G).comp_differentiable h

@[fun_prop]
theorem differentiableWithinAt_fst {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.fst s p :=
  differentiableAt_fst.differentiableWithinAt

@[fun_prop]
protected theorem DifferentiableWithinAt.fst (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).1) s x :=
  (fst 𝕜 F G).comp_differentiableWithinAt h

@[fun_prop]
theorem differentiableOn_fst {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.fst s :=
  differentiable_fst.differentiableOn

@[fun_prop]
protected theorem DifferentiableOn.fst (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).1) s :=
  (fst 𝕜 F G).comp_differentiableOn h

variable [ContinuousAdd E] [ContinuousSMul 𝕜 E] [ContinuousAdd F] [ContinuousSMul 𝕜 F]

theorem fderiv_fst [T2Space E] : fderiv 𝕜 Prod.fst p = fst 𝕜 E F :=
  hasFDerivAt_fst.fderiv

theorem fderiv.fst [T2Space F] (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).1) x = (fst 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.hasFDerivAt.fst.fderiv

theorem fderivWithin_fst [T2Space E] {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.fst s p = fst 𝕜 E F :=
  hasFDerivWithinAt_fst.fderivWithin hs

theorem fderivWithin.fst [T2Space F] (hs : UniqueDiffWithinAt 𝕜 s x)
    (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).1) s x = (fst 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.hasFDerivWithinAt.fst.fderivWithin hs

end Fst

section Snd

variable {f₂ : E → F × G} {f₂' : E →L[𝕜] F × G} {p : E × F}

@[fun_prop]
theorem hasStrictFDerivAt_snd : HasStrictFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  (snd 𝕜 E F).hasStrictFDerivAt

@[fun_prop]
protected theorem HasStrictFDerivAt.snd (h : HasStrictFDerivAt f₂ f₂' x) :
    HasStrictFDerivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  hasStrictFDerivAt_snd.comp x h

theorem hasFDerivAtFilter_snd {L : Filter (E × F)} :
    HasFDerivAtFilter (@Prod.snd E F) (snd 𝕜 E F) p L :=
  (snd 𝕜 E F).hasFDerivAtFilter

protected theorem HasFDerivAtFilter.snd (h : HasFDerivAtFilter f₂ f₂' x L) :
    HasFDerivAtFilter (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x L :=
  hasFDerivAtFilter_snd.comp x h tendsto_map

@[fun_prop]
theorem hasFDerivAt_snd : HasFDerivAt (@Prod.snd E F) (snd 𝕜 E F) p :=
  hasFDerivAtFilter_snd

@[fun_prop]
protected nonrec theorem HasFDerivAt.snd (h : HasFDerivAt f₂ f₂' x) :
    HasFDerivAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') x :=
  h.snd

@[fun_prop]
theorem hasFDerivWithinAt_snd {s : Set (E × F)} :
    HasFDerivWithinAt (@Prod.snd E F) (snd 𝕜 E F) s p :=
  hasFDerivAtFilter_snd

@[fun_prop]
protected nonrec theorem HasFDerivWithinAt.snd (h : HasFDerivWithinAt f₂ f₂' s x) :
    HasFDerivWithinAt (fun x => (f₂ x).2) ((snd 𝕜 F G).comp f₂') s x :=
  h.snd

@[fun_prop]
theorem differentiableAt_snd : DifferentiableAt 𝕜 Prod.snd p :=
  hasFDerivAt_snd.differentiableAt

@[simp, fun_prop]
protected theorem DifferentiableAt.snd (h : DifferentiableAt 𝕜 f₂ x) :
    DifferentiableAt 𝕜 (fun x => (f₂ x).2) x :=
  differentiableAt_snd.comp x h

@[fun_prop]
theorem differentiable_snd : Differentiable 𝕜 (Prod.snd : E × F → F) := fun _ =>
  differentiableAt_snd

@[simp, fun_prop]
protected theorem Differentiable.snd (h : Differentiable 𝕜 f₂) :
    Differentiable 𝕜 fun x => (f₂ x).2 :=
  differentiable_snd.comp h

@[fun_prop]
theorem differentiableWithinAt_snd {s : Set (E × F)} : DifferentiableWithinAt 𝕜 Prod.snd s p :=
  differentiableAt_snd.differentiableWithinAt

@[fun_prop]
protected theorem DifferentiableWithinAt.snd (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    DifferentiableWithinAt 𝕜 (fun x => (f₂ x).2) s x :=
  differentiableAt_snd.comp_differentiableWithinAt x h

@[fun_prop]
theorem differentiableOn_snd {s : Set (E × F)} : DifferentiableOn 𝕜 Prod.snd s :=
  differentiable_snd.differentiableOn

@[fun_prop]
protected theorem DifferentiableOn.snd (h : DifferentiableOn 𝕜 f₂ s) :
    DifferentiableOn 𝕜 (fun x => (f₂ x).2) s :=
  differentiable_snd.comp_differentiableOn h

theorem fderiv_snd : fderiv 𝕜 Prod.snd p = snd 𝕜 E F :=
  hasFDerivAt_snd.fderiv

theorem fderiv.snd (h : DifferentiableAt 𝕜 f₂ x) :
    fderiv 𝕜 (fun x => (f₂ x).2) x = (snd 𝕜 F G).comp (fderiv 𝕜 f₂ x) :=
  h.hasFDerivAt.snd.fderiv

theorem fderivWithin_snd {s : Set (E × F)} (hs : UniqueDiffWithinAt 𝕜 s p) :
    fderivWithin 𝕜 Prod.snd s p = snd 𝕜 E F :=
  hasFDerivWithinAt_snd.fderivWithin hs

theorem fderivWithin.snd (hs : UniqueDiffWithinAt 𝕜 s x) (h : DifferentiableWithinAt 𝕜 f₂ s x) :
    fderivWithin 𝕜 (fun x => (f₂ x).2) s x = (snd 𝕜 F G).comp (fderivWithin 𝕜 f₂ s x) :=
  h.hasFDerivWithinAt.snd.fderivWithin hs

end Snd

section prodMap

variable {f₂ : G → G'} {f₂' : G →L[𝕜] G'} {y : G} (p : E × G)

@[fun_prop]
protected theorem HasStrictFDerivAt.prodMap (hf : HasStrictFDerivAt f f' p.1)
    (hf₂ : HasStrictFDerivAt f₂ f₂' p.2) : HasStrictFDerivAt (Prod.map f f₂) (f'.prodMap f₂') p :=
  (hf.comp p hasStrictFDerivAt_fst).prodMk (hf₂.comp p hasStrictFDerivAt_snd)

@[fun_prop]
protected theorem HasFDerivWithinAt.prodMap {s : Set <| E × G}
    (hf : HasFDerivWithinAt f f' (Prod.fst '' s) p.1)
    (hf₂ : HasFDerivWithinAt f₂ f₂' (Prod.snd '' s) p.2) :
    HasFDerivWithinAt (Prod.map f f₂) (f'.prodMap f₂') s p :=
  (hf.comp _ hasFDerivWithinAt_fst mapsTo_fst_prod).prodMk
    (hf₂.comp _ hasFDerivWithinAt_snd mapsTo_snd_prod) |>.mono (by grind)

@[fun_prop]
protected theorem HasFDerivAt.prodMap (hf : HasFDerivAt f f' p.1) (hf₂ : HasFDerivAt f₂ f₂' p.2) :
    HasFDerivAt (Prod.map f f₂) (f'.prodMap f₂') p :=
  (hf.comp p hasFDerivAt_fst).prodMk (hf₂.comp p hasFDerivAt_snd)

@[simp, fun_prop]
protected theorem DifferentiableAt.prodMap (hf : DifferentiableAt 𝕜 f p.1)
    (hf₂ : DifferentiableAt 𝕜 f₂ p.2) : DifferentiableAt 𝕜 (fun p : E × G => (f p.1, f₂ p.2)) p :=
  (hf.comp p differentiableAt_fst).prodMk (hf₂.comp p differentiableAt_snd)

end prodMap

section Pi

/-!
### Derivatives of functions `f : E → Π i, F' i`

In this section we formulate `has*FDeriv*_pi` theorems as `iff`s, and provide two versions of each
theorem:

* the version without `'` deals with `φ : Π i, E → F' i` and `φ' : Π i, E →L[𝕜] F' i`
  and is designed to deduce differentiability of `fun x i ↦ φ i x` from differentiability
  of each `φ i`;
* the version with `'` deals with `Φ : E → Π i, F' i` and `Φ' : E →L[𝕜] Π i, F' i`
  and is designed to deduce differentiability of the components `fun x ↦ Φ x i` from
  differentiability of `Φ`.
-/


variable {ι : Type*} [Finite ι] {F' : ι → Type*} [∀ i, NormedAddCommGroup (F' i)]
  [∀ i, NormedSpace 𝕜 (F' i)] {φ : ∀ i, E → F' i} {φ' : ∀ i, E →L[𝕜] F' i} {Φ : E → ∀ i, F' i}
  {Φ' : E →L[𝕜] ∀ i, F' i}

@[simp]
theorem hasStrictFDerivAt_pi' :
    HasStrictFDerivAt Φ Φ' x ↔ ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x := by
  have := Fintype.ofFinite ι
  simp only [hasStrictFDerivAt_iff_isLittleO]
  exact isLittleO_pi

@[fun_prop]
theorem hasStrictFDerivAt_pi'' (hφ : ∀ i, HasStrictFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
    HasStrictFDerivAt Φ Φ' x := hasStrictFDerivAt_pi'.2 hφ

@[fun_prop]
theorem hasStrictFDerivAt_apply (i : ι) (f : ∀ i, F' i) :
    HasStrictFDerivAt (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) (proj i) f := by
  have := Fintype.ofFinite ι
  let id' := ContinuousLinearMap.id 𝕜 (∀ i, F' i)
  have h := ((hasStrictFDerivAt_pi'
             (Φ := fun (f : ∀ i, F' i) (i' : ι) => f i') (Φ' := id') (x := f))).1
  have h' : comp (proj i) id' = proj i := by ext; simp [id']
  rw [← h']; apply h; apply hasStrictFDerivAt_id

theorem hasStrictFDerivAt_pi :
    HasStrictFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasStrictFDerivAt (φ i) (φ' i) x :=
  hasStrictFDerivAt_pi'

@[simp]
theorem hasFDerivAtFilter_pi' :
    HasFDerivAtFilter Φ Φ' x L ↔
      ∀ i, HasFDerivAtFilter (fun x => Φ x i) ((proj i).comp Φ') x L := by
  have := Fintype.ofFinite ι
  simp only [hasFDerivAtFilter_iff_isLittleO]
  exact isLittleO_pi

theorem hasFDerivAtFilter_pi :
    HasFDerivAtFilter (fun x i => φ i x) (ContinuousLinearMap.pi φ') x L ↔
      ∀ i, HasFDerivAtFilter (φ i) (φ' i) x L :=
  hasFDerivAtFilter_pi'

@[simp]
theorem hasFDerivAt_pi' :
    HasFDerivAt Φ Φ' x ↔ ∀ i, HasFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x :=
  hasFDerivAtFilter_pi'

@[fun_prop]
theorem hasFDerivAt_pi'' (hφ : ∀ i, HasFDerivAt (fun x => Φ x i) ((proj i).comp Φ') x) :
    HasFDerivAt Φ Φ' x := hasFDerivAt_pi'.2 hφ

@[fun_prop]
theorem hasFDerivAt_apply (i : ι) (f : ∀ i, F' i) :
    HasFDerivAt (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) (proj i) f := by
  have := Fintype.ofFinite ι
  apply HasStrictFDerivAt.hasFDerivAt
  apply hasStrictFDerivAt_apply

theorem hasFDerivAt_pi :
    HasFDerivAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') x ↔
      ∀ i, HasFDerivAt (φ i) (φ' i) x :=
  hasFDerivAtFilter_pi

@[simp]
theorem hasFDerivWithinAt_pi' :
    HasFDerivWithinAt Φ Φ' s x ↔ ∀ i, HasFDerivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x :=
  hasFDerivAtFilter_pi'

@[fun_prop]
theorem hasFDerivWithinAt_pi''
    (hφ : ∀ i, HasFDerivWithinAt (fun x => Φ x i) ((proj i).comp Φ') s x) :
    HasFDerivWithinAt Φ Φ' s x := hasFDerivWithinAt_pi'.2 hφ

@[fun_prop]
theorem hasFDerivWithinAt_apply (i : ι) (f : ∀ i, F' i) (s' : Set (∀ i, F' i)) :
    HasFDerivWithinAt (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) (proj i) s' f := by
  have := Fintype.ofFinite ι
  let id' := ContinuousLinearMap.id 𝕜 (∀ i, F' i)
  have h := ((hasFDerivWithinAt_pi'
             (Φ := fun (f : ∀ i, F' i) (i' : ι) => f i') (Φ' := id') (x := f) (s := s'))).1
  have h' : comp (proj i) id' = proj i := by rfl
  rw [← h']; apply h; apply hasFDerivWithinAt_id

theorem hasFDerivWithinAt_pi :
    HasFDerivWithinAt (fun x i => φ i x) (ContinuousLinearMap.pi φ') s x ↔
      ∀ i, HasFDerivWithinAt (φ i) (φ' i) s x :=
  hasFDerivAtFilter_pi

@[simp]
theorem differentiableWithinAt_pi :
    DifferentiableWithinAt 𝕜 Φ s x ↔ ∀ i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x :=
  have := Fintype.ofFinite ι
  ⟨fun h i => (hasFDerivWithinAt_pi'.1 h.hasFDerivWithinAt i).differentiableWithinAt, fun h =>
    (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).differentiableWithinAt⟩

@[fun_prop]
theorem differentiableWithinAt_pi'' (hφ : ∀ i, DifferentiableWithinAt 𝕜 (fun x => Φ x i) s x) :
    DifferentiableWithinAt 𝕜 Φ s x := differentiableWithinAt_pi.2 hφ

@[fun_prop]
theorem differentiableWithinAt_apply (i : ι) (f : ∀ i, F' i) (s' : Set (∀ i, F' i)) :
    DifferentiableWithinAt (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) s' f := by
  have := Fintype.ofFinite ι
  apply HasFDerivWithinAt.differentiableWithinAt
  fun_prop

@[simp]
theorem differentiableAt_pi : DifferentiableAt 𝕜 Φ x ↔ ∀ i, DifferentiableAt 𝕜 (fun x => Φ x i) x :=
  have := Fintype.ofFinite ι
  ⟨fun h i => (hasFDerivAt_pi'.1 h.hasFDerivAt i).differentiableAt, fun h =>
    (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).differentiableAt⟩

@[fun_prop]
theorem differentiableAt_pi'' (hφ : ∀ i, DifferentiableAt 𝕜 (fun x => Φ x i) x) :
    DifferentiableAt 𝕜 Φ x := differentiableAt_pi.2 hφ

@[fun_prop]
theorem differentiableAt_apply (i : ι) (f : ∀ i, F' i) :
    DifferentiableAt (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) f := by
  have := Fintype.ofFinite ι
  have h := ((differentiableAt_pi (𝕜 := 𝕜)
             (Φ := fun (f : ∀ i, F' i) (i' : ι) => f i') (x := f))).1
  apply h; apply differentiableAt_id

theorem differentiableOn_pi : DifferentiableOn 𝕜 Φ s ↔ ∀ i, DifferentiableOn 𝕜 (fun x => Φ x i) s :=
  ⟨fun h i x hx => differentiableWithinAt_pi.1 (h x hx) i, fun h x hx =>
    differentiableWithinAt_pi.2 fun i => h i x hx⟩

@[fun_prop]
theorem differentiableOn_pi'' (hφ : ∀ i, DifferentiableOn 𝕜 (fun x => Φ x i) s) :
    DifferentiableOn 𝕜 Φ s := differentiableOn_pi.2 hφ

@[fun_prop]
theorem differentiableOn_apply (i : ι) (s' : Set (∀ i, F' i)) :
    DifferentiableOn (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) s' := by
  have := Fintype.ofFinite ι
  have h := ((differentiableOn_pi (𝕜 := 𝕜)
             (Φ := fun (f : ∀ i, F' i) (i' : ι) => f i') (s := s'))).1
  apply h; apply differentiableOn_id

theorem differentiable_pi : Differentiable 𝕜 Φ ↔ ∀ i, Differentiable 𝕜 fun x => Φ x i :=
  ⟨fun h i x => differentiableAt_pi.1 (h x) i, fun h x => differentiableAt_pi.2 fun i => h i x⟩

@[fun_prop]
theorem differentiable_pi'' (hφ : ∀ i, Differentiable 𝕜 fun x => Φ x i) :
    Differentiable 𝕜 Φ := differentiable_pi.2 hφ

@[fun_prop]
theorem differentiable_apply (i : ι) :
    Differentiable (𝕜 := 𝕜) (fun f : ∀ i, F' i => f i) := by intro x; apply differentiableAt_apply

-- TODO: find out which version (`φ` or `Φ`) works better with `rw`/`simp`
theorem fderivWithin_pi (h : ∀ i, DifferentiableWithinAt 𝕜 (φ i) s x)
    (hs : UniqueDiffWithinAt 𝕜 s x) :
    fderivWithin 𝕜 (fun x i => φ i x) s x = pi fun i => fderivWithin 𝕜 (φ i) s x :=
  have := Fintype.ofFinite ι
  (hasFDerivWithinAt_pi.2 fun i => (h i).hasFDerivWithinAt).fderivWithin hs

theorem fderiv_pi (h : ∀ i, DifferentiableAt 𝕜 (φ i) x) :
    fderiv 𝕜 (fun x i => φ i x) x = pi fun i => fderiv 𝕜 (φ i) x :=
  have := Fintype.ofFinite ι
  (hasFDerivAt_pi.2 fun i => (h i).hasFDerivAt).fderiv

end Pi

/-!
### Derivatives of tuples `f : E → Π i : Fin n.succ, F' i`

These can be used to prove results about functions of the form `fun x ↦ ![f x, g x, h x]`,
as `Matrix.vecCons` is defeq to `Fin.cons`.
-/
section PiFin

variable {n : Nat} {F' : Fin n.succ → Type*}
variable [∀ i, NormedAddCommGroup (F' i)] [∀ i, NormedSpace 𝕜 (F' i)]
variable {φ : E → F' 0} {φs : E → ∀ i, F' (Fin.succ i)}

theorem hasStrictFDerivAt_finCons {φ' : E →L[𝕜] Π i, F' i} :
    HasStrictFDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔
      HasStrictFDerivAt φ (.proj 0 ∘L φ') x ∧
      HasStrictFDerivAt φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') x := by
  rw [hasStrictFDerivAt_pi', Fin.forall_fin_succ, hasStrictFDerivAt_pi']
  dsimp [ContinuousLinearMap.comp, LinearMap.comp, Function.comp_def]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A variant of `hasStrictFDerivAt_finCons` where the derivative variables are free on the RHS
instead. -/
theorem hasStrictFDerivAt_finCons'
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)} :
    HasStrictFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x ↔
      HasStrictFDerivAt φ φ' x ∧ HasStrictFDerivAt φs φs' x :=
  hasStrictFDerivAt_finCons

@[fun_prop]
theorem HasStrictFDerivAt.finCons
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)}
    (h : HasStrictFDerivAt φ φ' x) (hs : HasStrictFDerivAt φs φs' x) :
    HasStrictFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x :=
  hasStrictFDerivAt_finCons'.mpr ⟨h, hs⟩

theorem hasFDerivAtFilter_finCons
    {φ' : E →L[𝕜] Π i, F' i} {l : Filter E} :
    HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) φ' x l ↔
      HasFDerivAtFilter φ (.proj 0 ∘L φ') x l ∧
      HasFDerivAtFilter φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') x l := by
  rw [hasFDerivAtFilter_pi', Fin.forall_fin_succ, hasFDerivAtFilter_pi']
  dsimp [ContinuousLinearMap.comp, LinearMap.comp, Function.comp_def]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A variant of `hasFDerivAtFilter_finCons` where the derivative variables are free on the RHS
instead. -/
theorem hasFDerivAtFilter_finCons'
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)} {l : Filter E} :
    HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x l ↔
      HasFDerivAtFilter φ φ' x l ∧ HasFDerivAtFilter φs φs' x l :=
  hasFDerivAtFilter_finCons

theorem HasFDerivAtFilter.finCons
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)} {l : Filter E}
    (h : HasFDerivAtFilter φ φ' x l) (hs : HasFDerivAtFilter φs φs' x l) :
    HasFDerivAtFilter (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x l :=
  hasFDerivAtFilter_finCons'.mpr ⟨h, hs⟩

theorem hasFDerivAt_finCons
    {φ' : E →L[𝕜] Π i, F' i} :
    HasFDerivAt (fun x => Fin.cons (φ x) (φs x)) φ' x ↔
      HasFDerivAt φ (.proj 0 ∘L φ') x ∧ HasFDerivAt φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') x :=
  hasFDerivAtFilter_finCons

/-- A variant of `hasFDerivAt_finCons` where the derivative variables are free on the RHS
instead. -/
theorem hasFDerivAt_finCons'
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)} :
    HasFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x ↔
      HasFDerivAt φ φ' x ∧ HasFDerivAt φs φs' x :=
  hasFDerivAt_finCons

@[fun_prop]
theorem HasFDerivAt.finCons
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)}
    (h : HasFDerivAt φ φ' x) (hs : HasFDerivAt φs φs' x) :
    HasFDerivAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') x :=
  hasFDerivAt_finCons'.mpr ⟨h, hs⟩

theorem hasFDerivWithinAt_finCons
    {φ' : E →L[𝕜] Π i, F' i} :
    HasFDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) φ' s x ↔
      HasFDerivWithinAt φ (.proj 0 ∘L φ') s x ∧
      HasFDerivWithinAt φs (Pi.compRightL 𝕜 F' Fin.succ ∘L φ') s x :=
  hasFDerivAtFilter_finCons

/-- A variant of `hasFDerivWithinAt_finCons` where the derivative variables are free on the RHS
instead. -/
theorem hasFDerivWithinAt_finCons'
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)} :
    HasFDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') s x ↔
      HasFDerivWithinAt φ φ' s x ∧ HasFDerivWithinAt φs φs' s x :=
  hasFDerivAtFilter_finCons

@[fun_prop]
theorem HasFDerivWithinAt.finCons
    {φ' : E →L[𝕜] F' 0} {φs' : E →L[𝕜] Π i, F' (Fin.succ i)}
    (h : HasFDerivWithinAt φ φ' s x) (hs : HasFDerivWithinAt φs φs' s x) :
    HasFDerivWithinAt (fun x => Fin.cons (φ x) (φs x)) (φ'.finCons φs') s x :=
  hasFDerivWithinAt_finCons'.mpr ⟨h, hs⟩

theorem differentiableWithinAt_finCons :
    DifferentiableWithinAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) s x ↔
      DifferentiableWithinAt 𝕜 φ s x ∧ DifferentiableWithinAt 𝕜 φs s x := by
  rw [differentiableWithinAt_pi, Fin.forall_fin_succ, differentiableWithinAt_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A variant of `differentiableWithinAt_finCons` where the derivative variables are free on the RHS
instead. -/
theorem differentiableWithinAt_finCons' :
    DifferentiableWithinAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) s x ↔
      DifferentiableWithinAt 𝕜 φ s x ∧ DifferentiableWithinAt 𝕜 φs s x :=
  differentiableWithinAt_finCons

@[fun_prop]
theorem DifferentiableWithinAt.finCons
    (h : DifferentiableWithinAt 𝕜 φ s x) (hs : DifferentiableWithinAt 𝕜 φs s x) :
    DifferentiableWithinAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) s x :=
  differentiableWithinAt_finCons'.mpr ⟨h, hs⟩

theorem differentiableAt_finCons :
    DifferentiableAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) x ↔
      DifferentiableAt 𝕜 φ x ∧ DifferentiableAt 𝕜 φs x := by
  rw [differentiableAt_pi, Fin.forall_fin_succ, differentiableAt_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A variant of `differentiableAt_finCons` where the derivative variables are free on the RHS
instead. -/
theorem differentiableAt_finCons' :
    DifferentiableAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) x ↔
      DifferentiableAt 𝕜 φ x ∧ DifferentiableAt 𝕜 φs x :=
  differentiableAt_finCons

@[fun_prop]
theorem DifferentiableAt.finCons
    (h : DifferentiableAt 𝕜 φ x) (hs : DifferentiableAt 𝕜 φs x) :
    DifferentiableAt 𝕜 (fun x => Fin.cons (φ x) (φs x)) x :=
  differentiableAt_finCons'.mpr ⟨h, hs⟩

theorem differentiableOn_finCons :
    DifferentiableOn 𝕜 (fun x => Fin.cons (φ x) (φs x)) s ↔
      DifferentiableOn 𝕜 φ s ∧ DifferentiableOn 𝕜 φs s := by
  rw [differentiableOn_pi, Fin.forall_fin_succ, differentiableOn_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A variant of `differentiableOn_finCons` where the derivative variables are free on the RHS
instead. -/
theorem differentiableOn_finCons' :
    DifferentiableOn 𝕜 (fun x => Fin.cons (φ x) (φs x)) s ↔
      DifferentiableOn 𝕜 φ s ∧ DifferentiableOn 𝕜 φs s :=
  differentiableOn_finCons

@[fun_prop]
theorem DifferentiableOn.finCons
    (h : DifferentiableOn 𝕜 φ s) (hs : DifferentiableOn 𝕜 φs s) :
    DifferentiableOn 𝕜 (fun x => Fin.cons (φ x) (φs x)) s :=
  differentiableOn_finCons'.mpr ⟨h, hs⟩

theorem differentiable_finCons :
    Differentiable 𝕜 (fun x => Fin.cons (φ x) (φs x)) ↔
      Differentiable 𝕜 φ ∧ Differentiable 𝕜 φs := by
  rw [differentiable_pi, Fin.forall_fin_succ, differentiable_pi]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A variant of `differentiable_finCons` where the derivative variables are free on the RHS
instead. -/
theorem differentiable_finCons' :
    Differentiable 𝕜 (fun x => Fin.cons (φ x) (φs x)) ↔
      Differentiable 𝕜 φ ∧ Differentiable 𝕜 φs :=
  differentiable_finCons

@[fun_prop]
theorem Differentiable.finCons
    (h : Differentiable 𝕜 φ) (hs : Differentiable 𝕜 φs) :
    Differentiable 𝕜 (fun x => Fin.cons (φ x) (φs x)) :=
  differentiable_finCons'.mpr ⟨h, hs⟩

-- TODO: write the `Fin.cons` versions of `fderivWithin_pi` and `fderiv_pi`

end PiFin

end CartesianProduct

end
