/-
Copyright (c) 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri
-/
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# `C^n` bundled maps

In this file we define the type `ContMDiffMap` of `n` times continuously differentiable
bundled maps.
-/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners 𝕜 E H}
  {I' : ModelWithCorners 𝕜 E' H'} (M : Type*) [TopologicalSpace M] [ChartedSpace H M] (M' : Type*)
  [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type*} [NormedAddCommGroup E'']
  [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  -- declare a manifold `N` over the pair `(F, G)`.
  {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N] (n : WithTop ℕ∞)

variable (I I') in
/-- Bundled `n` times continuously differentiable maps,
denoted as `C^n(I, M; I', M')` and `C^n(I, M; k)` (when the target is a normed space `k` with
the trivial model) in the `Manifold` namespace. -/
def ContMDiffMap :=
  { f : M → M' // ContMDiff I I' n f }

@[inherit_doc]
scoped[Manifold] notation "C^" n "⟮" I ", " M "; " I' ", " M' "⟯" => ContMDiffMap I I' M M' n

@[inherit_doc]
scoped[Manifold]
  notation "C^" n "⟮" I ", " M "; " k "⟯" => ContMDiffMap I (modelWithCornersSelf k k) M k n

open scoped Manifold ContDiff

namespace ContMDiffMap

variable {M} {M'} {n}

instance instFunLike : FunLike C^n⟮I, M; I', M'⟯ M M' where
  coe := Subtype.val
  coe_injective' := Subtype.coe_injective

protected theorem contMDiff (f : C^n⟮I, M; I', M'⟯) : ContMDiff I I' n f :=
  f.prop

-- Porting note: use generic instance instead
-- instance : Coe C^n⟮I, M; I', M'⟯ C(M, M') :=
--   ⟨fun f ↦ ⟨f, f.contMDiff.continuous⟩⟩

attribute [to_additive_ignore_args 21] ContMDiffMap ContMDiffMap.instFunLike

variable {f g : C^n⟮I, M; I', M'⟯}

@[simp]
theorem coeFn_mk (f : M → M') (hf : ContMDiff I I' n f) :
    DFunLike.coe (F := C^n⟮I, M; I', M'⟯) ⟨f, hf⟩ = f :=
  rfl

theorem coe_injective ⦃f g : C^n⟮I, M; I', M'⟯⦄ (h : (f : M → M') = g) : f = g :=
  DFunLike.ext' h

@[ext]
theorem ext (h : ∀ x, f x = g x) : f = g := DFunLike.ext _ _ h

instance : ContinuousMapClass C^n⟮I, M; I', M'⟯ M M' where
  map_continuous f := f.contMDiff.continuous

/-- The identity as a `C^n` map. -/
nonrec def id : C^n⟮I, M; I, M⟯ :=
  ⟨id, contMDiff_id⟩

/-- The composition of `C^n` maps, as a `C^n` map. -/
def comp (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) : C^n⟮I, M; I'', M''⟯ where
  val a := f (g a)
  property := f.contMDiff.comp g.contMDiff

@[simp]
theorem comp_apply (f : C^n⟮I', M'; I'', M''⟯) (g : C^n⟮I, M; I', M'⟯) (x : M) :
    f.comp g x = f (g x) :=
  rfl

instance [Inhabited M'] : Inhabited C^n⟮I, M; I', M'⟯ :=
  ⟨⟨fun _ ↦ default, contMDiff_const⟩⟩

/-- Constant map as a `C^n` map -/
def const (y : M') : C^n⟮I, M; I', M'⟯ :=
  ⟨fun _ ↦ y, contMDiff_const⟩

/-- The first projection of a product, as a `C^n` map. -/
def fst : C^n⟮I.prod I', M × M'; I, M⟯ :=
  ⟨Prod.fst, contMDiff_fst⟩

/-- The second projection of a product, as a `C^n` map. -/
def snd : C^n⟮I.prod I', M × M'; I', M'⟯ :=
  ⟨Prod.snd, contMDiff_snd⟩

/-- Given two `C^n` maps `f` and `g`, this is the `C^n` map `x ↦ (f x, g x)`. -/
def prodMk (f : C^n⟮J, N; I, M⟯) (g : C^n⟮J, N; I', M'⟯) : C^n⟮J, N; I.prod I', M × M'⟯ :=
  ⟨fun x ↦ (f x, g x), f.2.prodMk g.2⟩

end ContMDiffMap

instance ContinuousLinearMap.hasCoeToContMDiffMap :
    Coe (E →L[𝕜] E') C^n⟮𝓘(𝕜, E), E; 𝓘(𝕜, E'), E'⟯ :=
  ⟨fun f ↦ ⟨f, f.contMDiff⟩⟩
