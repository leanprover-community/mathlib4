/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.DisjointUnion
import Mathlib.Geometry.Manifold.HasNiceBoundary

/-!
# Unoriented bordism theory

In this file, we sketch the beginnings of unoriented bordism theory.
Not all of this might end up in mathlib already (depending on how many pre-requisites are missing),
but a fair number of pieces already can be upstreamed!

This file currently has about 75 sorries remaining: prove these would be very welcome.
Some particular loose ends include:
- show the disjoint union of smooth manifolds is smooth,
 and that the natural maps are smooth

- complete lemmas about BoundaryManifoldData; perhaps revise the design as needed
Currently, there is a fair amount of DTT hell... perhaps there is a better way!
- prove the boundary behaves well w.r.t. to disjoint unions

- prove reflexivity: the idea is clear; needs some DTT fighting
- prove transitivity of the bordism relation: this entails proving a number of lemmas
about attaching maps in topological spaces, and the collar neighbourhood theorem

- actually define the bordism groups (and prove it is a group, if I can):
is not hard; just need to read up on how to do this

- prove some of the easy axioms of homology... perhaps all of it?
- does mathlib have a typeclass for "extraordinary homology theory"?
  proving this is an instance could be interesting...

-/

open scoped Manifold
open Metric (sphere)
open FiniteDimensional Set

noncomputable section

-- Let M, M' and W be smooth manifolds.
variable {E E' E'' E''' H H' H'' H''' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- A **singular `n`-manifold** on a topological space `X` consists of a
closed smooth `n`-manifold `M` and a continuous map `f : M → X`. -/
structure SingularNManifold (X : Type*) [TopologicalSpace X] (n : ℕ)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (I : ModelWithCorners ℝ E H) [SmoothManifoldWithCorners I M]
    [CompactSpace M] [BoundarylessManifold I M] [FiniteDimensional ℝ E] where
  [hdim : Fact (finrank ℝ E = n)]
  /-- The underlying map `M → X` of a singular `n`-manifold `(M,f)` on `X` -/
  f : M → X
  hf : Continuous f

namespace SingularNManifold

-- We declare these variables *after* the definition above, so `SingularNManifold` can have
-- its current order of arguments.
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {I' : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners I' M'] {n : ℕ}
  [BoundarylessManifold I M] [CompactSpace M] [FiniteDimensional ℝ E]
  [BoundarylessManifold I' M'] [CompactSpace M'] [FiniteDimensional ℝ E']

/-- If `M` is `n`-dimensional and closed, it is a singular `n`-manifold over itself. -/
noncomputable def refl (hdim : finrank ℝ E = n) : SingularNManifold M n M I where
  hdim := Fact.mk hdim
  f := id
  hf := continuous_id

/-- A map of topological spaces induces a corresponding map of singular n-manifolds. -/
-- This is part of proving functoriality of the bordism groups.
noncomputable def map [Fact (finrank ℝ E = n)] (s : SingularNManifold X n M I)
    {φ : X → Y} (hφ : Continuous φ) : SingularNManifold Y n M I where
  f := φ ∘ s.f
  hf := hφ.comp s.hf

@[simp]
lemma map_f [Fact (finrank ℝ E = n)]
    (s : SingularNManifold X n M I) {φ : X → Y} (hφ : Continuous φ) : (s.map hφ).f = φ ∘ s.f :=
  rfl

/-- If `(M', f)` is a singular `n`-manifold on `X` and `M'` another `n`-dimensional smooth manifold,
a smooth map `φ : M → M'` induces a singular `n`-manifold structore on `M`. -/
noncomputable def comap [Fact (finrank ℝ E = n)] (s : SingularNManifold X n M' I')
    {φ : M → M'} (hφ : Smooth I I' φ) : SingularNManifold X n M I where
  f := s.f ∘ φ
  hf := s.hf.comp hφ.continuous

@[simp]
lemma comap_f [Fact (finrank ℝ E = n)] (s : SingularNManifold X n M' I')
    {φ : M → M'} (hφ : Smooth I I' φ) : (s.comap hφ).f = s.f ∘ φ :=
  rfl

variable (M) in
/-- The canonical singular `n`-manifold associated to the empty set (seen as an `n`-dimensional
manifold, i.e. modelled on an `n`-dimensional space). -/
def empty [Fact (finrank ℝ E = n)] [IsEmpty M] : SingularNManifold X n M I where
  f := fun x ↦ (IsEmpty.false x).elim
  hf := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (IsEmpty.false x).elim

/-- An `n`-dimensional manifold induces a singular `n`-manifold on the one-point space. -/
def trivial [Fact (finrank ℝ E = n)] : SingularNManifold PUnit n M I where
  f := fun _ ↦ PUnit.unit
  hf := continuous_const

/-- The product of a singular `n`- and a `m`-manifold into a one-point space
is a singular `n+m`-manifold. -/
-- FUTURE: prove that this observation inducess a commutative ring structure
-- on the unoriented bordism group `Ω_n^O = Ω_n^O(pt)`.
def prod {m n : ℕ} [h : Fact (finrank ℝ E = m)] [k : Fact (finrank ℝ E' = n)] :
    SingularNManifold PUnit (m + n) (M × M') (I.prod I') where
  f := fun _ ↦ PUnit.unit
  hf := continuous_const
  hdim := Fact.mk (by rw [finrank_prod, h.out, k.out])

end SingularNManifold

-- TODO: for now, assume all manifolds are modelled on the same chart and model space...
-- Is this necessary (`H` presumably is necessary for disjoint unions to work out)?
-- How would that work in practice? Post-compose with a suitable equivalence of H resp. E?

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  /-{I' : ModelWithCorners ℝ E H}-/ [SmoothManifoldWithCorners I M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  /-{I'' : ModelWithCorners ℝ E H}-/ [SmoothManifoldWithCorners I M''] {n : ℕ}
  [CompactSpace M] [BoundarylessManifold I M]
  [CompactSpace M'] [BoundarylessManifold I M'] [CompactSpace M''] [BoundarylessManifold I M'']
  [CompactSpace M] [FiniteDimensional ℝ E]
  [CompactSpace M'] [FiniteDimensional ℝ E'] [CompactSpace M''] [FiniteDimensional ℝ E'']

variable [Nonempty H]

/-- An **unoriented cobordism** between two singular `n`-manifolds `(M,f)` and `(N,g)` on `X`
is a compact smooth `n`-manifold `W` with a continuous map `F: W → X`
whose boundary is diffeomorphic to the disjoint union `M ⊔ N` such that `F` restricts to `f`
resp. `g` in the obvious way. -/
structure _root_.UnorientedCobordism (s : SingularNManifold X n M I)
    (t : SingularNManifold X n M' I) {W : Type*} [TopologicalSpace W]
    [ChartedSpace H'' W] {J : ModelWithCorners ℝ E'' H''} [SmoothManifoldWithCorners J W]
    (bd : BoundaryManifoldData W J) [HasNiceBoundary bd] where
  hW : CompactSpace W
  hW' : finrank ℝ E'' = n + 1
  F : W → X
  hF : Continuous F
  /-- The boundary of `W` is diffeomorphic to the disjoint union `M ⊔ M'`. -/
  φ : Diffeomorph bd.model I (J.boundary W) (M ⊕ M') ∞
  /-- `F` restricted to `M ↪ ∂W` equals `f`: this is formalised more nicely as
  `f = F ∘ ι ∘ φ⁻¹ : M → X`, where `ι : ∂W → W` is the inclusion. -/
  hFf : F ∘ (Subtype.val : J.boundary W → W) ∘ φ.symm ∘ Sum.inl = s.f
  /-- `F` restricted to `N ↪ ∂W` equals `g` -/
  hFg : F ∘ (Subtype.val : J.boundary W → W) ∘ φ.symm ∘ Sum.inr = t.f

namespace UnorientedCobordism

variable {s : SingularNManifold X n M I}
  {t : SingularNManifold X n M' I} {W : Type*} [TopologicalSpace W] [ChartedSpace H'' W]
  {J : ModelWithCorners ℝ E'' H''} [SmoothManifoldWithCorners J W]
  {bd : BoundaryManifoldData W J} [HasNiceBoundary bd]

section trivialCobordism

-- TODO: can I remove this `Fact`, concluding the empty set otherwise? would this be useful?
variable {x y : ℝ} [Fact (x < y)]

def _root_.boundaryData_IccManifold : BoundaryManifoldData ((Icc x y)) (𝓡∂ 1) := sorry

variable (x y M I) in
/-- The standard boundary data on a product `M × [x,y]`
of a boundaryless manifold `M` with an interval. -/
abbrev productBoundaryData : BoundaryManifoldData (M × (Icc x y)) (I.prod (𝓡∂ 1)) :=
  BoundaryManifoldData.prod_of_boundaryless_left (M := M) (I := I)
    (boundaryData_IccManifold (x := x) (y := y))

instance : HasNiceBoundary (productBoundaryData M I x y) := sorry

open IccManifold (X Y)

open ModelWithCorners
/-- A product `M × [x,y]` has boundary `M × {x,y}`. -/
lemma boundary_product : (I.prod (𝓡∂ 1)).boundary (M × (Set.Icc x y)) =
    Set.prod univ {IccManifold.X, IccManifold.Y} := by
  have : (𝓡∂ 1).boundary (Icc x y) = {X, Y} := by rw [boundary_IccManifold]
  rw [I.boundary_of_boundaryless_left]
  rw [this]

/-- Warm-up for `productInterval_sum below. -/
def warmup {X : Type*} [TopologicalSpace X] : X × ({0, 1} : Set ℝ) ≃ₜ X ⊕ X where
  toFun x := if x.2 = (0 : ℝ) then Sum.inl x.1 else Sum.inr x.1
  invFun := Sum.elim (fun x ↦ ⟨x, 0, by norm_num⟩) (fun x ↦ ⟨x, 1, by norm_num⟩)
  left_inv x := by
    by_cases h : x.2 = (0 : ℝ)
    · simp only [h, ↓reduceIte, Sum.elim_inl]
      congr
      exact h.symm
    · simp only [h, ↓reduceIte, Sum.elim_inr]
      congr
      let h := x.2.2
      simp only [mem_insert_iff, mem_singleton_iff] at h
      tauto
  right_inv x := by by_cases h : x.isLeft <;> aesop
  continuous_invFun := sorry
  continuous_toFun := sorry

variable (x y I M) in
/-- If `M` is boundaryless, `∂(M × [x,y])` is diffeomorphic to the disjoint union `M ⊔ M`. -/
-- XXX below is a definition, but that will surely *not* be nice to work with...
-- can I get something better behaved?
def Diffeomorph.productInterval_sum : Diffeomorph ((productBoundaryData M I x y).model) I
    ((I.prod (𝓡∂ 1)).boundary (M × (Icc x y))) (M ⊕ M) ∞ where
  toFun := by
    rw [boundary_product]
    -- We send M × {x} to the first factor and M × {y} to the second.
    exact fun p ↦ if p.1.2 = x then Sum.inl p.1.1 else Sum.inr p.1.1
  invFun := by
    rw [boundary_product]
    exact Sum.elim (fun p ↦ ⟨(p, IccManifold.X), trivial, by tauto⟩)
      (fun p ↦ ⟨(p, IccManifold.Y), trivial, by tauto⟩)
  left_inv := sorry
  right_inv := sorry
  contMDiff_toFun := by
    dsimp
    -- Several pieces still missing:
    -- f is C^n iff each restriction to M x {0} is C^n
    -- working with the actual terms.
    sorry
  contMDiff_invFun := by
    -- the following code errors...
    --suffices ContMDiff I (foo M I 0 1).model ∞ (Sum.elim (fun x ↦ ⟨(x, 0), trivial, by tauto⟩) (fun x ↦ ⟨(x, 1), trivial, by tauto⟩)) by
    --  sorry
    sorry

variable (I M) in
lemma Diffeomorph.productInterval_sum_toFun :
    (Diffeomorph.productInterval_sum M I x y).toFun =
  (fun p ↦ if p.1.2 = x then Sum.inl p.1.1 else Sum.inr p.1.1) := sorry

-- TODO: how to state this nicely?
-- variable (I M) in
-- lemma Diffeomorph.productInterval_sum_invFun_comp_inl :
--     (Subtype.val ∘ Sum.left) ∘ (Diffeomorph.productInterval_sum M I).invFun =
--   Sum.elim (fun p ↦ ⟨(p, IccManifold.X), trivial, by tauto⟩)
--     (fun p ↦ ⟨(p, IccManifold.Y), trivial, by tauto⟩) := sorry

--lemma api1 : fun p : M × ↑(Icc 0 1)↦ p.1 ∘ Subtype.val ∘ Diffeomorph.productInterval_sum.symm ∘ Sum.inl = id := sorry

/- theorem api_lemma1 {E : Type u_1} {H : Type u_5}
  [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] [inst_2 : TopologicalSpace H] {M : Type u_12}
  [inst_3 : TopologicalSpace M] [inst_4 : ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [inst_5 : SmoothManifoldWithCorners I M] {M' : Type u_13} [inst_6 : TopologicalSpace M'] [inst_7 : ChartedSpace H M']
  [inst_8 : SmoothManifoldWithCorners I M'] {M'' : Type u_14} [inst_9 : TopologicalSpace M'']
  [inst_10 : ChartedSpace H M''] [inst_11 : SmoothManifoldWithCorners I M''] [inst_12 : CompactSpace M]
  [inst_13 : BoundarylessManifold I M] [inst_14 : CompactSpace M'] [inst_15 : BoundarylessManifold I M']
  [inst_16 : CompactSpace M''] [inst_17 : BoundarylessManifold I M''] [inst_18 : CompactSpace M]
  [inst_19 : FiniteDimensional ℝ E] [inst_20 : CompactSpace M'] [inst_21 : CompactSpace M''] [inst_22 : Nonempty H] :
  -- sdfsdf
  (fun p ↦ p.1) ∘ Subtype.val ∘ (Diffeomorph.productInterval_sum.symm M I) ∘ Sum.inl = id := sorry -/

lemma bar {α β γ : Type*} {f f' : α → β} {g : β → γ} (h : f = f') : g ∘ f = g ∘ f' := sorry

/-- Each singular `n`-manifold `(M,f)` is cobordant to itself. -/
def refl (s : SingularNManifold X n M I) : UnorientedCobordism s s (productBoundaryData M I x y) where
  hW := by infer_instance
  hW' := by rw [finrank_prod, s.hdim.out, finrank_euclideanSpace_fin]
  F := s.f ∘ (fun p ↦ p.1)
  hF := s.hf.comp continuous_fst
  φ := Diffeomorph.productInterval_sum M I x y
  -- TODO: most of these proofs should become API lemmas about `Diffeomorph.productInterval_sum`
  hFf := sorry
    -- calc (s.f ∘ fun p ↦ p.1) ∘ Subtype.val ∘ (Diffeomorph.productInterval_sum M I).symm ∘ Sum.inl
    --   _ = s.f ∘ ((fun p ↦ p.1) ∘ Subtype.val ∘ (Diffeomorph.productInterval_sum M I).symm ∘ Sum.inl) := rfl
    --   _ = s.f ∘ @id M := by
    --     apply bar
    --     ext p
    --     -- first API lemma: writing this suffers a lot, perhaps due to the `rw` in the definition...
    --     -- mathematically, I want to rw [Sum.elim_inl], then remove the subtype.val part
    --     -- and it should be obvious...
    --   _ = s.f := rfl
  hFg := sorry -- same argument, just with inr

end trivialCobordism

-- Slight code smell, is there a better way?
-- congr solves everything; would like to use lemmas instead of defeq abuse...
-- need to repeat everything all the time -> more clever design?

/-- Being cobordant is symmetric. -/
def symm (φ : UnorientedCobordism s t bd) : UnorientedCobordism t s bd where
  hW := φ.hW
  hW' := φ.hW'
  F := φ.F
  hF := φ.hF
  φ := Diffeomorph.trans φ.φ (Diffeomorph.swap M I M')
  hFf := by
    calc φ.F ∘ Subtype.val ∘ ⇑(φ.φ.trans (Diffeomorph.swap M I M')).symm ∘ Sum.inl
      _ = φ.F ∘ Subtype.val ∘ φ.φ.symm ∘ (Diffeomorph.swap M' I M) ∘ Sum.inl := by congr
      _ = φ.F ∘ Subtype.val ∘ φ.φ.symm ∘ Sum.inr := by congr
      _ = t.f := φ.hFg
  hFg := by
      calc φ.F ∘ Subtype.val ∘ ⇑(φ.φ.trans (Diffeomorph.swap M I M')).symm ∘ Sum.inr
      _ = φ.F ∘ Subtype.val ∘ φ.φ.symm ∘ (Diffeomorph.swap M' I M) ∘ Sum.inr := by congr
      _ = φ.F ∘ Subtype.val ∘ φ.φ.symm ∘ Sum.inl := by congr
      _ = s.f := φ.hFf

/-- Suppose `W` is a cobordism between `M` and `N`.
Then a diffeomorphism `f : M'' → M` induces a cobordism between `M''` and `N`. -/
def comap_fst (φ : UnorientedCobordism s t bd) (f : Diffeomorph I I M'' M ∞) :
    UnorientedCobordism (have := s.hdim; s.comap f.contMDiff_toFun) t bd where
  hW := φ.hW
  hW' := φ.hW'
  F := φ.F
  hF := φ.hF
  φ := Diffeomorph.trans φ.φ (Diffeomorph.sum_map f.symm (Diffeomorph.refl _ M' _))
  hFf := by
    have := s.hdim
    calc φ.F ∘ Subtype.val ∘ ⇑(φ.φ.trans (f.symm.sum_map (Diffeomorph.refl I M' ⊤))).symm ∘ Sum.inl
      _ = φ.F ∘ Subtype.val ∘ φ.φ.symm ∘ (f.sum_map (Diffeomorph.refl I M' ⊤)) ∘ Sum.inl := by congr
      -- These are the interesting part.
      _ = φ.F ∘ Subtype.val ∘ φ.φ.symm ∘ Sum.inl ∘ f := by congr
      _ = (s.comap f.contMDiff_toFun).f := by rw [SingularNManifold.comap_f, ← φ.hFf]; congr
  hFg := by
    have := t.hdim
    -- Nothing interesting happens: the map is the same on this end.
    calc φ.F ∘ Subtype.val ∘ ⇑(φ.φ.trans (f.symm.sum_map (Diffeomorph.refl I M' ⊤))).symm ∘ Sum.inr
      _ = φ.F ∘ Subtype.val ∘ φ.φ.symm ∘ (f.sum_map (Diffeomorph.refl I M' ⊤)) ∘ Sum.inr := by congr
      _ = φ.F ∘ Subtype.val ∘ φ.φ.symm ∘ (Sum.inr ∘ (Diffeomorph.refl I M' ⊤)) := by congr
      _ = φ.F ∘ Subtype.val ∘ φ.φ.symm ∘ Sum.inr := by congr
      _ = t.f := φ.hFg

-- Actually, I don't need these: when I want to argue with "manifolds are cobordant",
-- I'll use symmetry of the bordism relation instead!
-- /-- Suppose `W` is a cobordism between `M` and `N`.
-- Then a diffeomorphism `f : N'' → N` induces a cobordism between `M` and `N''`. -/
-- def comap_snd (φ : UnorientedCobordism s t bd) (f : Diffeomorph I I M'' M' ∞) :
--     UnorientedCobordism s (have := t.hdim; t.comap f.contMDiff_toFun) bd where
--   hW := φ.hW
--   hW' := φ.hW'
--   F := φ.F
--   hF := φ.hF
--   φ := Diffeomorph.trans φ.φ (Diffeomorph.sum_map (Diffeomorph.refl _ M _) f.symm)
--   hFf := by
--     have := s.hdim
--     -- Nothing interesting happens: the map is the same on this end.
--     calc φ.F ∘ Subtype.val ∘ ⇑(φ.φ.trans ((Diffeomorph.refl I M _).sum_map f.symm)).symm ∘ Sum.inl
--       _ = φ.F ∘ Subtype.val ∘ φ.φ.symm ∘ Sum.inl ∘ (Diffeomorph.refl I M ⊤) := by congr
--       _ = φ.F ∘ Subtype.val ∘ φ.φ.symm ∘ Sum.inl := by congr
--       _ = s.f := φ.hFf
--   hFg := by
--     have := t.hdim
--     calc φ.F ∘ Subtype.val ∘ ⇑(φ.φ.trans ((Diffeomorph.refl I M _).sum_map f.symm)).symm ∘ Sum.inr
--       -- These are the interesting part.
--       _ = φ.F ∘ Subtype.val ∘ φ.φ.symm ∘ Sum.inr ∘ f := by congr
--       _ = (t.comap f.contMDiff_toFun).f := by
--         rw [SingularNManifold.comap_f, ← φ.hFg]; congr

variable {N N' : Type*} [TopologicalSpace N] [ChartedSpace H N] [SmoothManifoldWithCorners I N]
  [TopologicalSpace N'] [ChartedSpace H N'] [SmoothManifoldWithCorners I N']
  [CompactSpace N] [BoundarylessManifold I N] [CompactSpace N'] [BoundarylessManifold I N']
variable {s' : SingularNManifold X n N I} {t' : SingularNManifold X n N' I}
  {W' : Type*} [TopologicalSpace W'] [ChartedSpace H'' W'] [SmoothManifoldWithCorners J W']
  {bd' : BoundaryManifoldData W' J} [HasNiceBoundary bd']

variable (s t) in
/-- The disjoint union of two singular `n`-manifolds `(M,f)` and `(N, g)` into `X`. -/
def _root_.SingularNManifold.disjointUnion : SingularNManifold X n (M ⊕ M') I where
  f := Sum.elim s.f t.f
  hf := Continuous.sum_elim s.hf t.hf
  hdim := s.hdim

-- /-- The canonical cobordism between a singular `n`-simple `M` and `M ⊔ ∅`. -/
-- def sumEmpty [IsEmpty M'] [Fact (finrank ℝ E = n)]:
--     UnorientedCobordism (s.disjointUnion (SingularNManifold.empty M')) s
--     ((productBoundaryData M I 0 1)) := by
--   let S := UnorientedCobordism.refl s
--   convert S.comap_fst (Diffeomorph.sum_empty M)

def _root_.BoundaryManifoldData.sum [Nonempty H''] (bd : BoundaryManifoldData W J)
    (bd' : BoundaryManifoldData W' J) : BoundaryManifoldData (W ⊕ W') J := sorry

-- TODO: this is actually not fully true; for it certainly requires the boundaries
-- to have the same dimension
instance [Nonempty H''] (bd : BoundaryManifoldData W J) (bd' : BoundaryManifoldData W' J)
    [HasNiceBoundary bd] [HasNiceBoundary bd' ]: HasNiceBoundary (bd.sum bd') := sorry

-- TODO: impose further conditions, such as bd and bd' having the same model...
-- so I guess I actually need an equivalence of models here? Ugh!
-- def HasNiceBoundary.equiv_boundary_sum [Nonempty H''] (bd : BoundaryManifoldData W J)
-- (bd' : BoundaryManifoldData W' J) [HasNiceBoundary bd] [HasNiceBoundary bd'] :
--     Diffeomorph (bd.sum bd').model (bd.sum bd').model (bd.sum bd').model.boundary (W ⊕ W')
--       (bd.model.sum bd'.model).boundary (W ⊕ W') n := sorry

/-- The disjoint union of two oriented cobordisms `W` between `M` and `N` and
`W'` between `M'` and `N'`. -/
def disjointUnion [Nonempty H''] (φ : UnorientedCobordism s t bd)
    (ψ : UnorientedCobordism s' t' bd')  :
    UnorientedCobordism (s.disjointUnion s') (t.disjointUnion t') (bd.sum bd') where
  hW := sorry -- not hard: disjoint union of compact spaces is compact
  hW' := φ.hW'
  F := Sum.elim φ.F ψ.F
  hF := Continuous.sum_elim φ.hF ψ.hF
  φ := by
    -- idea: boundary is the disjoint union of the boundaries; in fact diffeomorphic
    -- apply Diffeomorph.map_sum after composing with such diffeomorphism
    -- TODO: need to rewrite by an equivalence again... how to do this nicely?
    sorry
  hFf := sorry
  hFg := sorry

-- FUTURE: transporting a cobordism under a diffeomorphism in general

-- define the bordism relation (hard part: how to state this in Lean?)
-- Two singular `n`-manifolds are cobordant iff there exists a smooth cobordism between them.

-- bordism relation is an equiv relation: all pieces sketched (transivitity is below)
-- define: equivalence classes, are the cobordism classes I care about
-- The unoriented `n`-bordism group `Ω_n^O(X)` of `X` is the set of all equivalence classes
-- of singular n-manifolds up to bordism.

-- define: empty cobordism = class of SingularNManifold.empty
-- define addition, by the disjoint union of cobordisms
-- prove this is well-defined: this is where the above sorry enters

-- M cobordant to M ⊔ ∅ : easy, by that diffeo
-- being cobordant is associative: TODO think; shouldn't be hard
-- commutative: use Diffeomorph.swap and the diffeo operation

-- prove: every element is self-inverse => define cobordism of M ⊔ M to the empty set
-- (mostly "done" already; except that part is needs some more lemmas)
-- then: group operations are done
--

-- Fleshing out the details for transitivity will take us too far: we merely sketch the necessary
-- pieces.
section transSketch

variable {u : SingularNManifold X n M'' I}
  {W' : Type*} [TopologicalSpace W'] [ChartedSpace H''' W']
  {J' : ModelWithCorners ℝ E''' H'''} [SmoothManifoldWithCorners J' W']
  {bd' : BoundaryManifoldData W' J'} [HasNiceBoundary bd']

-- Idea: glue the cobordisms W and W' along their common boundary M',
-- as identified by the diffeomorphism W → M' ← W'.
-- This could be formalised as an adjunction/attaching maps: these are a special case of pushouts
-- (in the category of topological spaces).
-- mathlib has abstract pushouts (and proved that TopCat has them);
-- `Topology/Category/TopCat/Limits/Pullbacks.lean` provides a concrete description of pullbacks
-- in TopCat. A good next step would be to adapt this argument to pushouts, and use this here.
-- TODO: can I remove the s and t variables from this definition?
def glue (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') : Type* := sorry

instance (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    TopologicalSpace (glue φ ψ) := sorry

-- This and the next item require the collar neighbourhood theorem.
instance (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    ChartedSpace H (glue φ ψ) := sorry

def glueModel (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    ModelWithCorners ℝ E H := sorry

instance (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    SmoothManifoldWithCorners (glueModel φ ψ) (glue φ ψ) := sorry

def glueBoundaryData (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    BoundaryManifoldData (glue φ ψ) (glueModel φ ψ) := sorry

instance (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    HasNiceBoundary (glueBoundaryData φ ψ) := sorry

noncomputable def trans (φ : UnorientedCobordism s t bd) (ψ : UnorientedCobordism t u bd') :
    UnorientedCobordism s u (glueBoundaryData φ ψ) where
  hW := sorry
  hW' := sorry
  F := sorry
  hF := sorry
  φ := sorry
  hFf := sorry
  hFg := sorry

end transSketch

-- Fun things one could prove, once the bordism groups are defined

-- functor between them: already have this on the level of singular n-manifolds
-- need to show this is well-defined, of course (and functoriality, which should be easy)

-- prove: every element in Ω_n^O(X) has order two; essentially already shown above
-- direct sum property of bordism groups
-- homotopy axiom: a homotopy basically gives a cobordism already
-- harder: relative bordism groups; long exact sequence, excision; proving bordism groups form
-- an extraordinary homology theory

end UnorientedCobordism

-- We declare these variables *after* the definition above, so `SingularNManifold` can have
-- its current order of arguments.
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M'] [SmoothManifoldWithCorners I M'] {n : ℕ}
  [BoundarylessManifold I M] [CompactSpace M] [FiniteDimensional ℝ E]
  {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  --[BoundarylessManifold I M'] [CompactSpace M'] [FiniteDimensional ℝ E']

-- The oriented bordism relation on the space of singular `n`-manifolds on `X`
-- whose charts are modelled on some fixed space `E`.
-- (I'm not sure if this requirement is essential: it can certainly be eased later.)

#exit
-- TODO: can I vary M and I as well? How to prescribe these? Packaging it all into one structure
-- also does not fully solve it...
universe u in
structure BoundaryWithBordism (s t : SingularNManifold X n M I) where
  W := Type u
  H'' := Type u
  [hn : Nonempty H]
  [ht : TopologicalSpace H'']
  [htW : TopologicalSpace W]
  [charts : ChartedSpace H'' W]
  [model : ModelWithCorners ℝ E'' H'']
  [mfd : have:= charts; SmoothManifoldWithCorners model W]
  boundaryData : BoundaryManifoldData W model
  hasNiceBoundary : HasNiceBoundary boundaryData
  bordism : UnorientedCobordism s t boundaryData
-- #lint
-- variable (n X M I) in
-- def orientedBordismRelation : (SingularNManifold X n M I) → (SingularNManifold X n M I) → Prop :=
--   fun s t ↦ ∃ φ : BoundaryWithBordism s t (E := E) (E'' := E'')

def sdf : Setoid (SingularNManifold X n M I) where
  r s t := ∃ φ : BoundaryWithBordism s t (E := E) (E'' := E''), True--orientedBordismRelation X M I n (bd := bd)
  iseqv := by
    apply Equivalence.mk
    · intro s
      -- TODO: my definition is not right, as I cannot "choose" bd here...
      sorry -- use UnorientedCobordism.refl s
    · intro s t hst
      choose φ _ using hst
      sorry -- synthesisation order is wrong... something is very funky here!
      --have := φ.ht
      --use UnorientedCobordism.symm φ.bordism
    · intro s t u hst htu
      choose φ _ using hst
      choose ψ _ using htu
      -- TODO: the definition is not quite right, as bd must be chosen
      sorry -- use UnorientedCobordism.trans φ ψ

-- Is there already a notion of "post-compose a PartialHom with an OpenEmbedding?
-- Because that would suffice for my purposes...
-- I vaguely recall something like that for structomorphisms, or Winston Yin speaking about this.
