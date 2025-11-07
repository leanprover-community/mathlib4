/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.ContMDiff.Defs
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Bordism
import Mathlib.Geometry.Manifold.HasSmoothBoundary
import Mathlib.Algebra.Group.MinimalAxioms

/-!
## (Unoriented) bordism theory

TODO: rewrite this doc-string and merge everything with Bordism.lean

This file defines the beginnings of (unoriented) bordism theory. We define singular n-manifolds,
unoriented bordisms and the bordism groups of a topological space.
We only sorry the proof of transitivity (as this requires the collar neighbourhood theorem,
which is a fair amount of work from the current state of mathlib).

The basic concept of bordism theory are *singular *n*-manifolds*: a singular n-manifold on a
topological space `X` is a closed n-dimensional smooth manifold `M` together with and a continuous
map `M → F`. (The word *singular* does not refer to singularities, but is by analogy to singular
n-chains in the definition of singular homology.)

The next key concept is the definition of (unoriented) bordisms between singular n-manifolds:
given two singular n-manifolds `s` and `t`, a bordism between `s` and `t` is a compact smooth
`n+1`-dimensional manifold whose boundary is (diffeomorphic to) the disjoint union of `s` and `t`,
together with a map which restricts to the maps on `s` and `t`.
We call `s` and `t` bordant if there exists a bordism between them: this turns out to define an
equivalence relation. (Transitivity is the hardest part, and uses the collar neighbourhood theorem.)
Finally, the `n`obordism group of `X` is the set of bordism classes of singular `n`-manifolds on`X`.

XXX design decisions, model parameters etc.

## Main definitions

- **SingularNManifold**: a singular `n`-manifold on a topological space `X`, for `n ∈ ℕ`, is a pair
  `(M, f)` of a closed `n`-dimensional smooth manifold `M` together with a continuous map `M → X`.
  We don't assume `M` to be modelled on `ℝ^n`, but add the model topological space `H`,
  the vector space `E` and the model with corners `I` as type parameters.

- **UnorientedBordism**: TODO write more!

- **uBordismClass X k I** is the type of unoriented `C^k` bordism classes on `X`,
  modelled over the model `I`.

## Main results

- `SingularNManifold.map`: a map `X → Y` of topological spaces induces a map between the spaces
  of singular n-manifolds
- `SingularNManifold.comap`: if `(N,f)` is a singular n-manifold on `X`
  and `φ: M → N` is continuous, the `comap` of `(N,f)` and `φ`
  is the induced singular n-manifold `(M, f ∘ φ)` on `X`.
- `SingularNManifold.empty`: the empty set `M`, viewed as an `n`-manifold,
  as a singular `n`-manifold over any space `X`.
- `SingularNManifold.toPUnit`: an `n`-dimensional manifold induces a singular `n`-manifold
  on the one-point space.
- `SingularNManifold.prod`: the product of a singular `n`-manifold and a singular `m`-manifold
  on the one-point space, is a singular `n+m`-manifold on the one-point space.
- `SingularNManifold.sum`: the disjoint union of two singular `n`-manifolds
  is a singular `n`-manifold.

- `UnorientedBordism.symm`: being bordant is symmetric (by "turning around" the bordism)
- `UrorientedBordism.trans`: being bordant is transitive (provided the bordism has dimension one)
  higher than the boundary components, and the collars of the manifolds fit together smoothly:
  this result is only stated (as its proof requires the not yet formalised
  collar neighbourhood theorem)

- `UnorientedBordism.sum_self`: the direct sum of a manifold with itself is null-bordant:
  this is only true for unoriented bordisms.
- `UnorientedBordism.sumAssoc`: the direct sum of singular n-manifolds is associative up to bordism
- `UnorientedBordism.sumComm`: the direct sum of singular n-manifolds is commutative up to bordism
- `UnorientedBordism.sumEmpty`: each singular `n`-manifold
  is bordant to itself plus the empty manifold
- `UnorientedBordism.sum`: the direct sum of two bordisms (over the same model `J`) is a bordism
- `UnorientedBordism.sumComm`: the direct sum of bordisms is commutative
- `UnorientedBordism.comap_{fst,snd}`: TODO write!

- `uBordismClass.sum`: addition of bordism classes --- the disjoint union on their representatives
- `uBordismClass.instAddCommGroup`: bordism classes form an abelian group

## Implementation notes

To be written! Document the design decisions and why they were made.

## TODO
- for bordisms on a one-point space, define multiplication and prove the bordism ring structure
- define relative bordism groups (generalising the previous three points)
- prove that relative unoriented bordism groups define an extraordinary homology theory

## Tags

singular n-manifold, bordism, bordism group
-/

open scoped Manifold
open Module Set

suppress_compilation

variable (k) in
/-- An **unoriented bordism** between two singular `n`-manifolds `(M, f)` and `(N, g)` on `X`
is a compact smooth `n`-manifold `W` with a continuous map `F: W → X`
whose boundary is diffeomorphic to the disjoint union `M ⊔ N` such that `F` restricts to `f`
resp. `g` in the obvious way.

We prescribe the model with corners of the underlying manifold `W` as part of this type,
as gluing arguments require matching models to work.

We list all the relevant variables in this definition to ensure the universe variables `u` and `v`
describing the singular manifolds at the boundary are the first ones in this definition.
-/
structure UnorientedBordism.{u, v} {X E H E' H' : Type*}
    [TopologicalSpace X] [TopologicalSpace H] [TopologicalSpace H']
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
    (k : WithTop ℕ∞) {I : ModelWithCorners ℝ E H} [FiniteDimensional ℝ E]
    (s : SingularManifold.{u} X k I) (t : SingularManifold.{v} X k I)
    (J : ModelWithCorners ℝ E' H') where
  /-- The underlying compact manifold of this unoriented bordism -/
  W : Type (max u v) -- or: new parameter w
  /-- The manifold `W` is a topological space. -/
  [topologicalSpace: TopologicalSpace W]
  [compactSpace : CompactSpace W]
  /-- The manifold `W` is a charted space over `H'`. -/
  [chartedSpace: ChartedSpace H' W]
  [isManifold: IsManifold J k W]
  /-- The presentation of the boundary `W` as a smooth manifold -/
  -- Future: we could allow bd.M₀ to be modelled on some other model, not necessarily I:
  -- we only care that this is fixed in the type.
  bd: BoundaryManifoldData W J k I
  /-- A continuous map `W → X` of the bordism into the topological space we work on -/
  F : W → X
  hF : Continuous F := by fun_prop
  /-- The boundary of `W` is diffeomorphic to the disjoint union `M ⊔ M'`. -/
  φ : Diffeomorph I I (s.M ⊕ t.M) bd.M₀ k
  /-- `F` restricted to `M ↪ ∂W` equals `f`: this is formalised more nicely as
  `f = F ∘ ι ∘ φ⁻¹ : M → X`, where `ι : ∂W → W` is the inclusion. -/
  hFf : F ∘ bd.f ∘ φ ∘ Sum.inl = s.f
  /-- `F` restricted to `N ↪ ∂W` equals `g` -/
  hFg : F ∘ bd.f ∘ φ ∘ Sum.inr = t.f

attribute [fun_prop] UnorientedBordism.hF

namespace UnorientedBordism

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

-- Let M and M' be smooth manifolds.
variable {E E' E'' E''' H H' H'' H''' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable {k : WithTop ℕ∞}

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I k M]
  -- {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']
  -- /-{I' : ModelWithCorners ℝ E H}-/ [IsManifold I k M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  {I'' : ModelWithCorners ℝ E H} [IsManifold I k M'']
  [CompactSpace M] [BoundarylessManifold I M]
  --[CompactSpace M'] [BoundarylessManifold I M']
  [CompactSpace M''] [BoundarylessManifold I M'']
  [CompactSpace M] [FiniteDimensional ℝ E]
  --[CompactSpace M'] [FiniteDimensional ℝ E'] [CompactSpace M''] [FiniteDimensional ℝ E'']

variable {s s' t t' u : SingularManifold X k I} {J : ModelWithCorners ℝ E' H'}

instance (φ : UnorientedBordism k s t J) : TopologicalSpace φ.W := φ.topologicalSpace

instance (φ : UnorientedBordism k s t J) : CompactSpace φ.W := φ.compactSpace

instance (φ : UnorientedBordism k s t J) : ChartedSpace H' φ.W := φ.chartedSpace

instance (φ : UnorientedBordism k s t J) : IsManifold J k φ.W := φ.isManifold

/-
/-- The bordism between two empty singular manifolds. -/
def empty [IsEmpty M] [IsEmpty M''] : UnorientedBordism k (SingularManifold.empty X M I)
    (SingularManifold.empty X M'' I) I where
  -- XXX: generalise to any model J, by post-composing the boundary data
  bd := BoundaryManifoldData.of_boundaryless M I
  F x := (IsEmpty.false x).elim
  hF := by
    rw [continuous_iff_continuousAt]
    exact fun x ↦ (IsEmpty.false x).elim
  φ := Diffeomorph.empty
  hFf := by ext x; exact (IsEmpty.false x).elim
  hFg := by ext x; exact (IsEmpty.false x).elim
-/

/-- The disjoint union of two unoriented bordisms (over the same model `J`). -/
noncomputable def sum (φ : UnorientedBordism k s t J) (ψ : UnorientedBordism k s' t' J) :
    UnorientedBordism k (s.sum s') (t.sum t') J where
  W := φ.W ⊕ ψ.W
  bd := φ.bd.sum ψ.bd
  F := Sum.elim φ.F ψ.F
  φ := Diffeomorph.trans (Diffeomorph.sumSumSumComm I s.M k t.M s'.M t'.M).symm
      (Diffeomorph.sumCongr φ.φ ψ.φ)
  hFf := by
    ext x
    cases x with
    | inl x =>
      dsimp
      change (φ.F ∘ φ.bd.f ∘ φ.φ ∘ Sum.inl) x = s.f x
      rw [φ.hFf]
    | inr x =>
      dsimp
      change (ψ.F ∘ ψ.bd.f ∘ ψ.φ ∘ Sum.inl) x = s'.f x
      rw [ψ.hFf]
  hFg := by
    ext x
    cases x with
    | inl x =>
      dsimp
      change (φ.F ∘ φ.bd.f ∘ φ.φ ∘ Sum.inr) x = t.f x
      rw [φ.hFg]
    | inr x =>
      dsimp
      change (ψ.F ∘ ψ.bd.f ∘ ψ.φ ∘ Sum.inr) x = t'.f x
      rw [ψ.hFg]

/-- Suppose `W` is a bordism between `M` and `N`.
Then a diffeomorphism `f : M'' → M` induces a bordism between `M''` and `N`. -/
def comap_fst (φ : UnorientedBordism k s t J) (f : Diffeomorph I I M'' s.M k) :
    UnorientedBordism k (s.comap f.continuous) t J where
  W := φ.W
  bd := φ.bd
  F := φ.F
  φ := Diffeomorph.trans (f.sumCongr (Diffeomorph.refl _ _ _)) φ.φ
  hFf := by dsimp; rw [← φ.hFf]; congr 1
  hFg := by dsimp; rw [← φ.hFg]; congr 1

/-- Suppose `W` is a bordism between `M` and `N`.
Then a diffeomorphism `f : N'' → N` induces a bordism between `M` and `N''`. -/
def comap_snd (φ : UnorientedBordism k s t J) (f : Diffeomorph I I M t.M k) :
    UnorientedBordism k s (t.comap f.continuous) J where
  W := φ.W
  bd := φ.bd
  F := φ.F
  φ := Diffeomorph.trans ((Diffeomorph.refl _ _ _).sumCongr f) φ.φ
  hFf := by dsimp; rw [← φ.hFf]; congr 1
  hFg := by dsimp; rw [← φ.hFg]; congr 1

variable (s) in
/-- Each singular manifold is bordant to itself. -/
def refl : UnorientedBordism k s s (I.prod (𝓡∂ 1)) where
  W := s.M × (Set.Icc (0 : ℝ) 1)
  -- XXX: I'm using special boundary data modelled on I, as opposed to
  -- BoundaryManifoldData.prod_of_boundaryless_left s.M I (BoundaryManifoldData.Icc k)
  -- modelled on I × (∂[0,1])
  bd := BoundaryManifoldData.prod_Icc _ k I
  F := s.f ∘ (fun p ↦ p.1)
  hF := s.hf.comp continuous_fst
  φ := Diffeomorph.refl I _ k
  hFf := by
    simp only [BoundaryManifoldData.prod_Icc_f, Function.comp_assoc]
    congr
  hFg := by
    simp only [BoundaryManifoldData.prod_Icc_f, Function.comp_assoc]
    congr

/-- Being bordant is symmetric. -/
def symm (φ : UnorientedBordism k s t J) : UnorientedBordism k t s J where
  W := φ.W
  bd := φ.bd
  F := φ.F
  φ := (Diffeomorph.sumComm I t.M k s.M).trans φ.φ
  hFf := by rw [← φ.hFg]; congr 1
  hFg := by rw [← φ.hFf]; congr 1

/-- Replace the first singular manifold in an unoriented bordism by an equivalent one:
useful to fix definitional equalities. -/
def copy_map_fst.{u, v} (φ : UnorientedBordism.{u, v} k s t J)
    (eq : Diffeomorph I I s'.M s.M k) (h_eq : s'.f = s.f ∘ eq) :
    UnorientedBordism.{u, v} k s' t J where
  W := φ.W
  bd := φ.bd
  F := φ.F
  φ := Diffeomorph.trans (Diffeomorph.sumCongr eq (Diffeomorph.refl I t.M k)) φ.φ
  hFf := by dsimp; rw [h_eq, ← φ.hFf]; congr 1
  hFg := by dsimp; rw [← φ.hFg]; congr 1

/-- Replace the second singular manifold in an unoriented bordism by an equivalent one:
useful to fix definitional equalities. -/
def copy_map_snd.{u, v} (φ : UnorientedBordism.{u, v} k s t J)
    (eq : Diffeomorph I I t'.M t.M k) (h_eq : t'.f = t.f ∘ eq) :
    UnorientedBordism.{u, v} k s t' J where
  W := φ.W
  bd := φ.bd
  F := φ.F
  φ := Diffeomorph.trans (Diffeomorph.sumCongr (Diffeomorph.refl I s.M k) eq) φ.φ
  hFf := by dsimp; rw [← φ.hFf]; congr 1
  hFg := by dsimp; rw [h_eq, ← φ.hFg]; congr 1

-- Note. The naive approach `almost` is not sufficient, as it would yield a bordism
-- from s to `s.sum (SingularNManifold.empty X M I)`,
-- whereas I want `s.comap (Diffeomorph.sumEmpty)`... these are not *exactly* the same.

/-- Each singular manifold is bordant to itself plus the empty manifold. -/
def sumEmpty [IsEmpty M] :
    UnorientedBordism k (s.sum (SingularManifold.empty X M I)) s (I.prod (𝓡∂ 1)) :=
  letI almost := (refl s).comap_fst (Diffeomorph.sumEmpty I s.M (M' := M) k)
  almost.copy_map_fst (Diffeomorph.refl I _ k) (by
    ext x
    cases x with
    | inl x => dsimp; congr
    | inr x => exact (IsEmpty.false x).elim)

/-- The direct sum of singular manifolds is commutative up to bordism. -/
def sumComm : UnorientedBordism k (t.sum s) (s.sum t) (I.prod (𝓡∂ 1)) :=
  letI almost := (refl (s.sum t)).comap_fst (Diffeomorph.sumComm I s.M k t.M).symm
  almost.copy_map_fst (Diffeomorph.refl I _ k) (by
    ext x
    dsimp
    -- This uses to be just `cases x <;> simp`.
    cases x with
    | inl x' =>-- <;> simp
      simp
      erw [Diffeomorph.coe_refl] -- TODO: why is the erw necessary? fix this!
      simp
    | inr x' =>
      simp; erw [Diffeomorph.coe_refl]; simp)

lemma foo {α β γ X : Type*} {f : α → X} {g : β → X} {h : γ → X} :
    Sum.elim (Sum.elim f g) h = Sum.elim f (Sum.elim g h) ∘ (Equiv.sumAssoc α β γ) := by
  aesop

variable (s t u) in
/-- The direct sum of singular manifolds is associative up to bordism. -/
def sumAssoc : UnorientedBordism k (s.sum (t.sum u)) ((s.sum t).sum u) (I.prod (𝓡∂ 1)) := by
  letI almost := (refl (s.sum (t.sum u))).comap_snd (Diffeomorph.sumAssoc I s.M k t.M u.M)
  exact almost.copy_map_snd (Diffeomorph.refl I _ k) (by
    simpa only [mfld_simps, CompTriple.comp_eq] using foo)

variable (s) in
/-- The direct sum of a manifold with itself is null-bordant. -/
def sum_self [IsEmpty M] :
    UnorientedBordism k (s.sum s) (SingularManifold.empty X M I) (I.prod (𝓡∂ 1)) where
  -- This is the same manifold as for `refl`, but with a different map.
  W := s.M × (Set.Icc (0 : ℝ) 1)
  -- XXX: I'm using special boundary data modelled on I, as opposed to
  -- BoundaryManifoldData.prod_of_boundaryless_left s.M I (BoundaryManifoldData.Icc k)
  -- modelled on I × (∂[0,1])
  bd := BoundaryManifoldData.prod_Icc _ k I
  F := s.f ∘ (fun p ↦ p.1)
  hF := s.hf.comp continuous_fst
  φ := Diffeomorph.sumEmpty I _ k
  hFf := by
    ext x
    cases x <;> simp
  hFg := by
    ext x
    apply (IsEmpty.false x).elim

/-- Mapping a bordism between `M` and `N` on `X` under a continuous map `f : X → Y` -/
def map.{u, v} {f : X → Y} (hf : Continuous f) (φ : UnorientedBordism.{u, v} k s t J) :
    UnorientedBordism k (s.map hf) (t.map hf) J where
  W := φ.W
  bd := φ.bd
  F := f ∘ φ.F
  φ := φ.φ
  hFf := by simp [Function.comp_assoc, ← φ.hFf]
  hFg := by simp [Function.comp_assoc, ← φ.hFg]

lemma map_W {f : X → Y} (hf : Continuous f) (φ : UnorientedBordism k s t J) :
    (φ.map hf).W = φ.W :=
  rfl

@[simp, mfld_simps]
lemma map_F {f : X → Y} (hf : Continuous f) (φ : UnorientedBordism k s t J) :
    (φ.map hf).F = f ∘ φ.F :=
  rfl

section collarNeighbourhood

variable {I₀ : ModelWithCorners ℝ E'' H''} [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'']

open Fact.Manifold

namespace _root_

/-- A `C^k` collar neighbourhood of a smooth finite-dimensional manifold `M` with smooth boundary
of co-dimension one. -/
structure CollarNeighbourhood (bd : BoundaryManifoldData M I k I₀) where
  ε : ℝ
  hε : 0 < ε
  -- XXX: I may want Ico instead; add if I need it
  φ : Set.Icc 0 ε × bd.M₀ → M
  contMDiff : haveI := Fact.mk hε; ContMDiff (((𝓡∂ 1)).prod I₀) I k φ
  isEmbedding: Topology.IsEmbedding φ
  isImmersion: haveI := Fact.mk hε; ∀ x, Function.Injective (mfderiv ((𝓡∂ 1).prod I₀) I φ x)

/- The collar neighbourhood theorem: if `M` is a compact finite-dimensional manifold
with smooth boundary of co-dimension one,
there exist some `ε > 0` and a smooth embedding `[0, ε) × ∂M → M`, which maps `{0}×∂M` to `∂M`.

Proof outline.
(1) construct a normal vector field `X` in a neighbourhood of `∂M`, pointing inwards
(In a chart on Euclidean half-space, we can just take the unit vector in the first component.
 These can be combined using e.g. a partition of unity.)
(1') It might simplify the next steps to `X` to a smooth global vector field on `M`, say be zero.
(2) Since `∂M` is compact, there is an `ε` such that the flow of `X` is defined for time `ε`.
  (This is not *exactly* the same as ongoing work, but should follow from the same ideas.)
(3) Thus, the flow of `X` defines a map `[0, ε) × ∂M → M`
(4) Shrinking `ε` if needed, we can assume `φ` is a (topological) embedding.
  Since `∂M` is compact and `M` is Hausdorff, it suffices to show injectivity (and continuity).
  Each `x∈∂M` has a neighbourhood `U_x` where the vector field looks like a flow box
  (by construction), hence the flow is injective on `U_x` for some time `ε_x`.
  Cover `∂M` with finitely many such neighbourhoods, then `ε := min ε_i` is positive, and
  each flow line does not self-intersect until time `ε`.
  Suppose the map `φ` is not injective, then `φ(x, t)=φ(x', t')`. Say `x ∈ U_i` and `x' ∈ U_j`,
  then `x, x' ∉ U_i ∩ U_j` by hypothesis, and `x, x'` lie inside separated closed sets:
  these are some positive distance apart. Now continuity and compactness yields a lower bound
  `ε_ij` for each pair, on which there is no intersection. (a bit sketchy, but mostly works)
(5) `φ` is smooth, since solutions of smooth ODEs depend smoothly on their initial conditions
(6) `φ` is an immersion... that should be obvious

Steps (4) and (5) definitely use ongoing work of Winston Yin; I don't know if the flow of a vector
field is already defined.
-/
def collar_neighbourhood_theorem (h : finrank ℝ E = finrank ℝ E'' + 1)
    (bd : BoundaryManifoldData M I k I₀) : CollarNeighbourhood bd := sorry

end _root_

end collarNeighbourhood

section trans

variable {n : ℕ} [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']

/-- Being bordant is transitive: two `n+1`-dimensional bordisms with `n`-dimensional boundary
can be glued along their common boundary (thanks to the collar neighbourhood theorem). -/
-- The proof depends on the collar neighbourhood theorem.
-- TODO: do I need a stronger definition of bordisms, including a *choice* of collars?
-- At least, I need to argue that one *can* choose matching collars...
def trans (φ : UnorientedBordism k s t J) (ψ : UnorientedBordism k t u J)
    (h : finrank ℝ E' = finrank ℝ E + 1) : UnorientedBordism k s u J :=
  /- Outline of the proof:
    - using the collar neighbourhood theorem, choose matching collars for t in φ and ψ
      invert the first collar, to get a map (-ε, 0] × t.M → φ.W
    - let W be the attaching space, of φ.W and ψ.W along their common collar
      (i.e., we quotient the disjoint union φ.W ⊕ ψ.W along the identification by the collars)
    - the union of the collars defines an open neighbourhood of `t.M`:
      this is where the hypothesis `h` is used
    - the quotient is a smooth manifold: away from the boundary, the charts come from W and W';
      on the image of t.M, we define charts using the common map by the collars
      (smoothness is the tricky part: this requires the collars to *match*!)
    - prove: the inclusions of `φ.W` and `ψ.W` into this gluing are smooth
    - then, boundary data etc. are all easy to construct

  We could state a few more sorries, and provide more of an outline: we will not prove this in
  detail, this will be a larger project in itself. -/
  sorry

end trans

end UnorientedBordism

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

-- Let M and M' be smooth manifolds.
variable {k : WithTop ℕ∞} {E E' H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [IsManifold I k M] [CompactSpace M] [BoundarylessManifold I M]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] (h : finrank ℝ E' = finrank ℝ E + 1)

variable (X k I) in
/-- The "unordered bordism" equivalence relation: two singular manifolds modelled on `I`
are equivalent iff there exists an unoriented bordism between them. -/
-- FIXME: what is needed to remove the E' and H' arguments below?
def unorientedBordismRelation.{u, v} (X : Type u_1) [TopologicalSpace X] (k : WithTop ℕ∞)
    {E E' H H' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [TopologicalSpace H] [TopologicalSpace H']
    (I : ModelWithCorners ℝ E H) [FiniteDimensional ℝ E] (J : ModelWithCorners ℝ E' H') :
    SingularManifold.{u} X k I → SingularManifold.{v} X k I → Prop :=
  -- XXX: shall we demand a relation between I and J here? for the equivalence, we need to!
  fun s t ↦ ∃ _φ : UnorientedBordism k s t J, True

namespace unorientedBordismRelation

variable {J : ModelWithCorners ℝ E' H'} {s t u : SingularManifold X k I}

omit [FiniteDimensional ℝ E']

@[symm]
lemma symm (h : unorientedBordismRelation X k I J s t) : unorientedBordismRelation X k I J t s := by
  choose φ _ using h
  use UnorientedBordism.symm φ

@[trans]
lemma trans (h : finrank ℝ E' = finrank ℝ E + 1)
    (hst : unorientedBordismRelation X k I J s t) (htu : unorientedBordismRelation X k I J t u) :
    unorientedBordismRelation X k I J s u := by
    choose φ _ using hst
    choose ψ _ using htu
    use φ.trans ψ (by simp [h])

end unorientedBordismRelation

-- TODO: does this hold for general models J, as opposed to just I.prod 𝓡∂ 1?
variable (X k I) in
lemma uBordismRelation.{u} :
  Equivalence (unorientedBordismRelation.{_, u, u} X k I (I.prod (𝓡∂ 1))) := by
  apply Equivalence.mk
  · intro s; use UnorientedBordism.refl s
  · intro s t h
    exact h.symm
  · intro s t u hst htu
    exact hst.trans (by simp) htu

variable (X k I) in
/-- The `Setoid` of singular `I`-manifolds, with the unoriented bordism relation. -/
def unorientedBordismSetoid.{u} : Setoid (SingularManifold.{u} X k I) :=
  Setoid.mk _ (uBordismRelation.{_, _, _, u} X k I)

variable (X k I) in
/-- The type of unoriented `C^k` bordism classes on `X`. -/
abbrev uBordismClass := Quotient <| Setoid.mk _ <| uBordismRelation X k I

variable (X k n) in
/-- The type of unoriented `n`-dimensional `C^k` bordism classes on `X`. -/
abbrev uBordismClassN (n : ℕ) := uBordismClass X k (𝓡 n)

namespace uBordismClass

variable (X k I) in
/-- The bordism class of the empty set: the neutral element for the group operation -/
def empty.{u} : uBordismClass X k I :=
  haveI := ChartedSpace.empty
  Quotient.mk _ (SingularManifold.empty.{_, _, _, u} X PEmpty I)

-- TODO: better name!
/-- The disjoint union of singular manifolds descends to bordism classes. -/
private lemma aux.{u} {a₁ b₁ a₂ b₂ : SingularManifold.{u} X k I}
    (h : unorientedBordismRelation X k I (I.prod (𝓡∂ 1)) a₁ a₂)
    (h' : unorientedBordismRelation X k I (I.prod (𝓡∂ 1)) b₁ b₂) :
    unorientedBordismRelation X k I (I.prod (𝓡∂ 1)) (a₁.sum b₁) (a₂.sum b₂) := by
  simp only [unorientedBordismRelation]
  choose φ _ using h
  choose ψ _ using h'
  use φ.sum ψ

/-- The group operation on unoriented bordism classes: lifting the sum of singular manifolds
to bordism classes, i.e. lifting `SingularNManifold.sum` to `unorientedBordismSetoid` -/
def sum.{u} :
    (uBordismClass.{_, _, _, u} X k I) → (uBordismClass X k I) → uBordismClass X k I :=
  letI sum := Quotient.lift₂
    (s₁ := unorientedBordismSetoid X k I) (s₂ := unorientedBordismSetoid X k I)
    (f := fun s t ↦ Quotient.mk (unorientedBordismSetoid X k I) (s.sum t))
  fun s t ↦ sum (fun _ _ _ _ h h' ↦ Quotient.sound (aux h h')) s t

lemma mk_sum_mk {s t : SingularManifold X k I} :
    sum (Quotient.mk _ s) (Quotient.mk _ t) = Quotient.mk _ (s.sum t) := by
  dsimp only [sum, Quotient.lift_mk]
  rfl

lemma sum_eq_out_sum_out.{u} {Φ Ψ : uBordismClass.{_, _, _, u} X k I} :
    Φ.sum Ψ = Quotient.mk _ (Φ.out.sum Ψ.out) := by
  nth_rw 1 [← Φ.out_eq, ← Ψ.out_eq, mk_sum_mk]

instance : Zero (uBordismClass X k I) where
  zero := empty X k I

instance : Neg (uBordismClass X k I) where
  neg Φ := Φ

instance : Add (uBordismClass X k I) where
  add := sum

lemma foo {α : Type*} (a : α) : ∃ _ : α, True := by use a


variable (X k I J) in
private def unorientedBordismGroup_aux.{u} : AddGroup (uBordismClass.{_, _, _, u} X k I) := by
  apply AddGroup.ofLeftAxioms
  · apply Quotient.ind; intro Φ
    apply Quotient.ind; intro Ψ
    apply Quotient.ind; intro Δ
    apply Quotient.sound
    symm
    -- TODO: which direction do I want?
    use UnorientedBordism.sumAssoc Φ Ψ Δ
  · apply Quotient.ind; intro S
    apply Quotient.sound
    -- TODO: want UnorientedBordism.emptySum also, because I need this here
    sorry -- use UnorientedBordism.emptySum s
  · apply Quotient.ind; intro S
    apply Quotient.sound
    -- TODO: this fails to find the charted space instance I need, not sure why
    -- different universes, somehow?
    have : IsEmpty PEmpty := by exact J
    haveI : ChartedSpace H PEmpty.{u + 1} := ChartedSpace.empty _ _
    have aux := UnorientedBordism.sum_self S (M := PEmpty)
    apply foo
    -- apply aux does not quite work...
    sorry

instance instAddCommGroup : AddCommGroup (uBordismClass X k I) where
  toAddGroup := unorientedBordismGroup_aux X k I sorry
  add_comm := by
    apply Quotient.ind; intro Φ
    apply Quotient.ind; intro Ψ
    apply Quotient.sound
    use UnorientedBordism.sumComm

section functor

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {k : WithTop ℕ∞}
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I k M] [CompactSpace M] [BoundarylessManifold I M]
  {f : X → Y} {g : Y → Z}

/-- If `s` and `t` are cobordant, so are `s.map hf` and `t.map hf`. -/
lemma map_aux (hf : Continuous f) {s t : SingularManifold X k I}
    (h : unorientedBordismRelation X k I (I.prod (𝓡∂ 1)) s t) :
    unorientedBordismRelation Y k I (I.prod (𝓡∂ 1)) (s.map hf) (t.map hf) := by
  choose φ _ using h
  use φ.map hf

/-- Map an unoriented bordism class under a continuous map -/
def map (hf : Continuous f) : (uBordismClass X k I) → (uBordismClass Y k I) :=
  Quotient.lift (fun s ↦ Quotient.mk _ (s.map hf)) (fun _ _ h ↦ Quotient.sound (map_aux hf h))

lemma mk_map (hf : Continuous f) {s : SingularManifold X k I} :
    uBordismClass.map hf (Quotient.mk _ s) = Quotient.mk _ (s.map hf) := by
  dsimp only [uBordismClass.map, Quotient.lift_mk]

theorem map_id (Φ : uBordismClass X k I) : Φ.map continuous_id = Φ := by
  set φ := Φ.out with φ_eq
  rw [← Φ.out_eq, mk_map, Quotient.eq, ← φ_eq]
  dsimp only
  use (UnorientedBordism.refl φ).copy_map_fst (Diffeomorph.refl I _ k) (by dsimp)

theorem map_id' : uBordismClass.map (k := k) (I := I) (@continuous_id X _) = id := by
  ext Φ
  exact map_id Φ

theorem map_comp (hf : Continuous f) (hg : Continuous g) (Φ : uBordismClass X k I) :
    (Φ.map hf).map hg = Φ.map (hg.comp hf) := by
  set φ := Φ.out with φ_eq
  rw [← Φ.out_eq, mk_map, ← φ_eq, mk_map, mk_map, Quotient.eq]
  dsimp only
  use ((UnorientedBordism.refl φ).map (hg.comp hf)).copy_map_fst
    (Diffeomorph.refl I _ k) (by dsimp [Function.comp_assoc])

theorem map_comp' (hf : Continuous f) (hg : Continuous g) :
    (fun s : uBordismClass X k I ↦ (s.map hf).map hg) = uBordismClass.map (hg.comp hf) := by
  ext Φ
  apply map_comp hf hg

end functor

end uBordismClass
