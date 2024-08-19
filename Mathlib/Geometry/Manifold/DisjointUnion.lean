/-
Copyright (c) 2024 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.InteriorBoundary

/-!
# The disjoint union of smooth manifolds

We prove some basic facts about disjoint unions (which should move to more basic files)
and exhibit the disjoint union of two smooth manifolds over the same charted as a smooth manifold.

## Main results

* `ChartedSpace.sum`: if `M` and `M'` are charted spaces over the same space `H`,
the disjoint union `M ⊕ M'` is a charted space over `H`
* xxx: prerequisite lemma: about continuity of extensions,
  yyy lemma about extending PartialHom's under open embeddings
(which ought to capture both my "left" and "right" cases)

* `SmoothManifoldWithCorners.sum`: the disjoint union of two smooth manifolds modelled on `(E,H)`
is a smooth manifold modeled on `(E, H)`.
* `ModelWithCorners.boundary_sum`: the boundary of a disjoint union of manifolds is the
disjoint union of its boundaries (as a set).
* `BoundarylessManifold.sum`: the disjoint union of two boundaryless manifolds is boundaryless.

## TODO
This file is only a transitionary place: more basic results should move out of it;
medium-term this material should move into a new file `SmoothManifoldWithCorners.Constructions`,
which can contain the empty set and products as well.

* does the disjoint union really require *the same* underlying charted space?
Could we also compose with equivalences of such spaces? Same for the models...
-/

noncomputable section

open scoped Manifold

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

-- Facts about the disjoint union of types and topological spaces: move to more basic files
-- and/or replace with what mathlib already has.
section Basic

variable {α β γ : Type*}

-- To what extent do these results exist abstractly?
def Sum.swapEquiv : α ⊕ β ≃ β ⊕ α where
  toFun := Sum.swap
  invFun := Sum.swap
  left_inv := Sum.swap_leftInverse
  right_inv := Sum.swap_leftInverse

lemma Continuous.swap : Continuous (@Sum.swap X Y) :=
  Continuous.sum_elim continuous_inr continuous_inl

def Homeomorph.swap : X ⊕ Y ≃ₜ Y ⊕ X where
  toEquiv := Sum.swapEquiv
  continuous_toFun := Continuous.swap
  continuous_invFun := Continuous.swap

def Sum.assocLeft : α ⊕ (β ⊕ γ) → (α ⊕ β) ⊕ γ :=
  Sum.elim (fun x ↦ Sum.inl (Sum.inl x)) (Sum.map Sum.inr id)

def Sum.assocRight : (α ⊕ β) ⊕ γ → α ⊕ (β ⊕ γ) :=
  Sum.elim (Sum.map id Sum.inl) (fun x ↦ Sum.inr (Sum.inr x))

def Equiv.swapAssociativity : α ⊕ (β ⊕ γ) ≃ (α ⊕ β) ⊕ γ where
  toFun := Sum.assocLeft
  invFun := Sum.assocRight
  left_inv x := by aesop
  right_inv x := by aesop

-- FUTURE: can fun_prop be powered up to solve these automatically? also for differentiability?
def Homeomorph.associativity : X ⊕ (Y ⊕ Z) ≃ₜ (X ⊕ Y) ⊕ Z where
  toEquiv := Equiv.swapAssociativity
  continuous_toFun := by
    apply Continuous.sum_elim (by fun_prop)
    exact Continuous.sum_map continuous_inr continuous_id
  continuous_invFun := by
    apply Continuous.sum_elim (by fun_prop)
    exact Continuous.comp continuous_inr continuous_inr

def Equiv.sum_empty {α β : Type*} [IsEmpty β] : α ⊕ β ≃ α where
  toFun := Sum.elim (@id α) fun x ↦ (IsEmpty.false x).elim
  invFun := Sum.inl
  left_inv x := by
    by_cases h : Sum.isLeft x
    · rw [Sum.eq_left_getLeft_of_isLeft h]
      dsimp only [Sum.elim_inl, id_eq]
    · have h' : Sum.isRight x := Sum.not_isLeft.mp h
      exact (IsEmpty.false (Sum.getRight x h')).elim
  right_inv x := by aesop

def Homeomorph.sum_empty [IsEmpty Y] :
  X ⊕ Y ≃ₜ X where
  toEquiv := Equiv.sum_empty
  continuous_toFun := Continuous.sum_elim continuous_id (continuous_of_const fun _ ↦ congrFun rfl)
  continuous_invFun := continuous_inl

end Basic

-- Results about extending a continuous function on a subtype.
-- Perhaps these exist already, but if so, I cannot find them...
section extensions

variable [Nonempty Y] {U : Set X} {f : U → Y}

/-- Any extension of a continuous function `f : U → Y` on an open set `U ⊆ X` to `X`
remains continuous on `U`. -/
lemma continuous_subtype_extension (hU : IsOpen U) (hf : Continuous f) {g : X → Y} :
    ContinuousOn (Function.extend Subtype.val f g) U := by
  let F := Function.extend Subtype.val f g
  suffices h : ∀ x : U, ContinuousAt F x from
    ContinuousAt.continuousOn (by convert h; exact Iff.symm Subtype.forall)
  intro x
  rw [← (hU.openEmbedding_subtype_val).continuousAt_iff, Function.extend_comp Subtype.val_injective]
  exact hf.continuousAt

/-- Corollary. *Any* extension `F:X→ Y` of `f : U → Y` to `X` is continuous on `U`. -/
lemma continuous_subtype_extension' (hU : IsOpen U) (hf : Continuous f)
    {F : X → Y} (hg : Set.restrict U F = f) : ContinuousOn F U := by
  let F' := Function.extend Subtype.val f F
  have : ContinuousOn F' U := continuous_subtype_extension hU hf
  apply ContinuousOn.congr this
  show Set.EqOn F F' U -- should be obvious, let's do the details...
  intro x hx
  suffices F x = f ⟨x, hx⟩ ∧ F' x = f ⟨x, hx⟩ from Eq.trans this.1 this.2.symm
  constructor
  · rw [← hg]
    exact rfl
  · sorry -- apply Function.Injective.extend_apply, sth sth about extensions...

lemma real_lemma {V : Set X} (hV : IsOpen V) {U : Set V} (hU : IsOpen U)
    {f : V → Y} (hf : ContinuousOn f U)
    {F : X → Y} (hF : Set.restrict V F = f) : ContinuousOn F U := by
  let g : U → Y := Set.restrict U f
  have : Continuous g := continuousOn_iff_continuous_restrict.mp hf

  -- F extends g; should also be easy (F extends f and f extends g)
  -- xxx: this doesn't type-check... think! because I have subtypes twice?!
  -- have : (Set.restrict U F) = g := sorry

  -- thus, F is continuous on U; by the corollary above
  sorry

-- TODO: state a more general version of real_lemma, for open embeddings (or so);
-- the proof should be just the same

end extensions

-- Let M, M' and M'' be smooth manifolds *over the same space* `H`, with *the same* `model `I`.
-- TODO: need we also assume their models are literally the same? or on the same space E?
-- or can something weaker suffice?
variable {E E' E'' E''' H H' H'' H''' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E'']  [NormedSpace ℝ E'']
  [NormedAddCommGroup E'''] [NormedSpace ℝ E''']
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H''] [TopologicalSpace H''']

variable {M : Type*} [TopologicalSpace M] [cm : ChartedSpace H M]
  {I : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M]
  {M' : Type*} [TopologicalSpace M'] [cm': ChartedSpace H M'] [SmoothManifoldWithCorners I M']
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H M'']
  {I'' : ModelWithCorners ℝ E H} [SmoothManifoldWithCorners I M'']

-- Exhibiting the disjoint union as a smooth manifold
section defs

-- TODO: can I avoid this assumption anywhere? It seems actually not:
-- if U ≠ M, the extended map needs to have *some* junk value in H...
variable [Nonempty H]

open scoped Topology

-- XXX: can this be deduced from the results above?

/-- Extend a partial homeomorphism from an open subset `U ⊆ M` to all of `M`. -/
-- experiment: does this work the same as foo?
def PartialHomeomorph.extend_subtype {U : Set M} (φ : PartialHomeomorph U H) (hU : IsOpen U) :
    PartialHomeomorph M H where
  toFun := Function.extend Subtype.val φ (Classical.arbitrary _)
  invFun := Subtype.val ∘ φ.symm
  left_inv' := by
    rintro x ⟨x', hx', hx'eq⟩
    rw [← hx'eq, Subtype.val_injective.extend_apply]
    dsimp
    congr
    exact PartialHomeomorph.left_inv φ hx'
  right_inv' x hx := by
    rw [Function.comp, Subtype.val_injective.extend_apply]
    exact φ.right_inv' hx
  source := Subtype.val '' φ.source
  target := φ.target
  map_source' := by
    rintro x ⟨x', hx', hx'eq⟩
    rw [← hx'eq, Subtype.val_injective.extend_apply]
    apply φ.map_source hx'
  map_target' x hx := ⟨φ.symm x, φ.map_target' hx, rfl⟩
  open_source := (hU.openEmbedding_subtype_val.open_iff_image_open).mp φ.open_source
  open_target := φ.open_target
  -- TODO: missing lemma, want a stronger version of `continuous_sum_elim`;
  -- perhaps use `continuous_sup_dom` to prove
  continuousOn_toFun := by
    -- first ingredient towards generalising real_lemma...
    --have hU : IsOpen U := (hU.openEmbedding_subtype_val.open_iff_image_open).mp φ.open_source

    apply real_lemma hU φ.open_source φ.continuousOn_toFun
    apply Function.extend_comp Subtype.val_injective
    -- -- mimicking the proof above
    -- set F := Function.extend Subtype.val φ (Classical.arbitrary _)
    -- dsimp
    -- show ContinuousOn F (Subtype.val '' φ.source)
    -- suffices h : ∀ x : (Subtype.val '' φ.source), ContinuousAt F x from
    --   ContinuousAt.continuousOn (by convert h; exact Iff.symm Subtype.forall)
    -- intro x
    -- have h := (hU.openEmbedding_subtype_val.open_iff_image_open).mp φ.open_source
    -- rw [← (h.openEmbedding_subtype_val).continuousAt_iff]
    -- --rw [Function.extend_comp Subtype.val_injective]
    -- let g : (Subtype.val '' φ.source) → H := (F ∘ Subtype.val)
    -- show ContinuousAt g x
    -- apply Continuous.continuousAt -- remains: g is continuous

    -- dsimp
    -- let myf := (φ.source).restrict φ.toFun
    -- let h := φ.open_source
    -- convert continuous_subtype_extension h (f := myf) ?hf--_(hf := φ.continuousOn_toFun)
    -- · congr
    --   --apply?
    --   sorry
    -- · sorry
    /-#exit
    dsimp
    -- TODO: why is the extension continuous? mathematically, there's not much to fuss about,
    -- `source` is open, also within U, so we can locally argue with that...
    -- in practice, this seems very annoying!
    refine ContinuousAt.continuousOn ?hcont
    rintro x ⟨x', hx', hx'eq⟩
    have : ContinuousAt φ x' := sorry -- is x', not x
    apply ContinuousAt.congr
    · sorry -- apply this--(φ.continuousOn_toFun).continuousAt (x := x') ?_
    sorry -- want to use toFun = φ on U...
    sorry-/
  continuousOn_invFun := sorry

/-- A partial homeomorphism `M → H` defines a partial homeomorphism `M ⊕ M' → H`. -/
def foo (φ : PartialHomeomorph M H) : PartialHomeomorph (M ⊕ M') H where
  -- TODO: this should be describable in terms of existing constructions!
  toFun := Sum.elim φ (Classical.arbitrary _)
  invFun := Sum.inl ∘ φ.symm
  source := Sum.inl '' φ.source
  target := φ.target
  map_source' := by
    rintro x ⟨x', hx', hx'eq⟩
    rw [← hx'eq, Sum.elim_inl]
    apply φ.map_source hx'
  map_target' x hx := ⟨φ.symm x, φ.map_target' hx, rfl⟩
  left_inv' := by
    rintro x ⟨x', hx', hx'eq⟩
    rw [← hx'eq, Sum.elim_inl]
    dsimp
    congr
    exact PartialHomeomorph.left_inv φ hx'
  right_inv' x hx := by
    rw [Function.comp, Sum.elim_inl]
    exact φ.right_inv' hx
  open_source := (openEmbedding_inl.open_iff_image_open).mp φ.open_source
  open_target := φ.open_target
  -- TODO: missing lemma, want a stronger version of `continuous_sum_elim`;
  -- perhaps use `continuous_sup_dom` to prove
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry

lemma foo_source (φ : PartialHomeomorph M H) :
    (foo φ (M' := M')).source = Sum.inl '' φ.source := rfl

/-- A partial homeomorphism `M' → H` defines a partial homeomorphism `M ⊕ M' → H`. -/
def bar (φ : PartialHomeomorph M' H) : PartialHomeomorph (M ⊕ M') H where
  toFun := Sum.elim (Classical.arbitrary _) φ
  invFun := Sum.inr ∘ φ.symm
  left_inv' := by
    rintro x ⟨x', hx', hx'eq⟩
    rw [← hx'eq, Sum.elim_inr]
    dsimp
    congr
    exact PartialHomeomorph.left_inv φ hx'
  right_inv' x hx := by
    rw [Function.comp, Sum.elim_inr]
    exact φ.right_inv' hx
  source := Sum.inr '' φ.source
  target := φ.target
  map_source' := by
    rintro x ⟨x', hx', hx'eq⟩
    rw [← hx'eq, Sum.elim_inr]
    apply φ.map_source hx'
  map_target' x hx := ⟨φ.symm x, φ.map_target' hx, rfl⟩
  open_source := (openEmbedding_inr.open_iff_image_open).mp φ.open_source
  open_target := φ.open_target
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry

lemma bar_source (φ : PartialHomeomorph M' H) :
    (bar φ (M := M)).source = Sum.inr '' φ.source := rfl

/-- The disjoint union of two charted spaces on `H` is a charted space over `H`. -/
instance ChartedSpace.sum : ChartedSpace H (M ⊕ M') where
  atlas := (foo '' cm.atlas) ∪ (bar '' cm'.atlas)
  -- At `x : M`, the chart is the chart in `M`; at `x' ∈ M'`, it is the chart in `M'`.
  chartAt := Sum.elim (fun x ↦ foo (cm.chartAt x)) (fun x ↦ bar (cm'.chartAt x))
  mem_chart_source p := by
    by_cases h : Sum.isLeft p
    · let x := Sum.getLeft p h
      rw [Sum.eq_left_getLeft_of_isLeft h]
      let aux := cm.mem_chart_source x
      dsimp
      rw [foo_source]
      use x
    · have h' : Sum.isRight p := Sum.not_isLeft.mp h
      let x := Sum.getRight p h'
      rw [Sum.eq_right_getRight_of_isRight h']
      let aux := cm'.mem_chart_source x
      dsimp
      rw [bar_source]
      use x
  chart_mem_atlas p := by
    by_cases h : Sum.isLeft p
    · let x := Sum.getLeft p h
      rw [Sum.eq_left_getLeft_of_isLeft h]
      dsimp
      left
      let aux := cm.chart_mem_atlas x
      use ChartedSpace.chartAt x
    · have h' : Sum.isRight p := Sum.not_isLeft.mp h
      let x := Sum.getRight p h'
      rw [Sum.eq_right_getRight_of_isRight h']
      dsimp
      right
      let aux := cm'.chart_mem_atlas x
      use ChartedSpace.chartAt x

/-- The disjoint union of two smooth manifolds modelled on `(E,H)`
is a smooth manifold modeled on `(E, H)`. -/
-- XXX. do I really need the same model twice??
instance SmoothManifoldWithCorners.sum : SmoothManifoldWithCorners I (M ⊕ M') := sorry

/-- The boundary of a disjoint union is the disjoint union of its boundaries:
this provides an equivalence of sets. -/
-- TODO: prove the same for the interiors
def ModelWithCorners.boundary_sum : I.boundary (M ⊕ M') ≃ I.boundary M ⊕ (I.boundary M') := sorry

/-- The disjoint union of two boundaryless manifolds is boundaryless. -/
instance BoundarylessManifold.sum : BoundarylessManifold I (M ⊕ M') := sorry

end defs

variable {N J : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {J : ModelWithCorners ℝ E' H'} [SmoothManifoldWithCorners J N]
variable {N' : Type*} [TopologicalSpace N'] [ChartedSpace H' N'] [SmoothManifoldWithCorners J N']

-- These should go into more basic files about manifolds.
-- TODO: move next to contMDiff_const
lemma contMDiff_of_const {f : M → N} (h : ∀ (x y : M), f x = f y) : ContMDiff I J ∞ f := by
  intro x
  have : f = fun _ ↦ f x := by ext y; exact h y x
  rw [this]
  apply contMDiff_const

-- Smoothness results about maps using the disjoint union.
section smoothness

variable [Nonempty H]

/-- The inclusion `M → M ⊕ M'` is smooth. -/
lemma ContMDiff.inl : ContMDiff I I ∞ (M' := M ⊕ M') Sum.inl := sorry

/-- The inclusion `M' → M ⊕ M'` is smooth. -/
lemma ContMDiff.inr : ContMDiff I I ∞ (M' := M ⊕ M') Sum.inr := sorry

lemma ContMDiff.sum_elim {f : M → N} {g : M' → N} (hf : Smooth I J f) (hg : Smooth I J g) :
    ContMDiff I J ∞ (Sum.elim f g) := sorry

-- actually, want an iff version here...
lemma ContMDiff.sum_map {n : ℕ∞} [Nonempty H'] {f : M → N} {g : M' → N'}
    (hf : ContMDiff I J n f) (hg : ContMDiff I J n g) : ContMDiff I J n (Sum.map f g) := sorry

def Diffeomorph.sum_map [Nonempty H'] {n : ℕ∞} (φ : Diffeomorph I J M N n)
    (ψ : Diffeomorph I J M' N' n) : Diffeomorph I J (M ⊕ M') (N ⊕ N') n where
  toFun := Sum.map φ ψ
  invFun := Sum.map φ.symm ψ.symm
  left_inv := by
    apply congrFun
    calc (Sum.map φ.symm ψ.symm) ∘ Sum.map φ ψ
      _ = Sum.map (φ.symm ∘ φ) (ψ.symm ∘ ψ) := by apply Sum.map_comp_map
      _ = Sum.map id id := by
        have h : φ.symm ∘ φ = id := by ext x; apply φ.left_inv x
        have : ψ.symm ∘ ψ = id := by ext x; apply ψ.left_inv x
        rw [h, this]
      _ = id := Sum.map_id_id
  right_inv := by
    apply congrFun
    calc (Sum.map φ ψ) ∘ (Sum.map φ.symm ψ.symm)
      _ = Sum.map (φ ∘ φ.symm) (ψ ∘ ψ.symm) := by apply Sum.map_comp_map
      _ = Sum.map id id := by
        have h : φ ∘ φ.symm = id := by ext x; apply φ.right_inv x
        have : ψ ∘ ψ.symm = id := by ext x; apply ψ.right_inv x
        rw [h, this]
      _ = id := Sum.map_id_id
  contMDiff_toFun := ContMDiff.sum_map φ.contMDiff_toFun ψ.contMDiff_toFun
  contMDiff_invFun := ContMDiff.sum_map φ.contMDiff_invFun ψ.contMDiff_invFun

lemma Diffeomorph.sum_map_symm_symm [Nonempty H'] {n : ℕ∞} (φ : Diffeomorph I J M N n)
    (ψ : Diffeomorph I J M' N' n) :
  Diffeomorph.sum_map φ.symm ψ.symm = (Diffeomorph.sum_map φ ψ).symm := rfl

lemma Diffeomorph.sum_map_coe [Nonempty H'] {n : ℕ∞} (φ : Diffeomorph I J M N n)
    (ψ : Diffeomorph I J M' N' n) :
  Diffeomorph.sum_map φ ψ = Sum.map φ ψ := rfl

lemma Diffeomorph.sum_map_inl [Nonempty H'] {n : ℕ∞} (φ : Diffeomorph I J M N n)
    (ψ : Diffeomorph I J M' N' n) :
  (Diffeomorph.sum_map φ ψ) ∘ Sum.inl = Sum.inl ∘ φ := rfl

lemma Diffeomorph.sum_map_inr [Nonempty H'] {n : ℕ∞} (φ : Diffeomorph I J M N n)
    (ψ : Diffeomorph I J M' N' n) :
  (Diffeomorph.sum_map φ ψ) ∘ Sum.inr = Sum.inr ∘ ψ := rfl

lemma ContMDiff.swap : ContMDiff I I ∞ (@Sum.swap M M') := ContMDiff.sum_elim inr inl

variable (I M M') in -- TODO: argument order is weird!
def Diffeomorph.swap : Diffeomorph I I (M ⊕ M') (M' ⊕ M) ∞ where
  toEquiv := Sum.swapEquiv
  contMDiff_toFun := ContMDiff.swap
  contMDiff_invFun := ContMDiff.swap

theorem Diffeomorph.coe_swap : (Diffeomorph.swap M I M' : (M ⊕ M') → (M' ⊕ M)) = Sum.swap := rfl

theorem Diffeomorph.swap_symm : (Diffeomorph.swap M I M').symm = Diffeomorph.swap M' I M := rfl

variable (I M M') in
def Diffeomorph.associativity [Nonempty H] [Nonempty H'] :
    Diffeomorph I I (M ⊕ (M' ⊕ M'')) ((M ⊕ M') ⊕ M'') ∞ where
  toEquiv := Equiv.swapAssociativity
  contMDiff_toFun := by
    apply ContMDiff.sum_elim
    · exact ContMDiff.comp ContMDiff.inl ContMDiff.inl -- xxx: can I power up fun_prop to do this?
    · exact ContMDiff.sum_map ContMDiff.inr contMDiff_id
  contMDiff_invFun := by
    apply ContMDiff.sum_elim
    · exact ContMDiff.sum_map contMDiff_id ContMDiff.inl
    · exact ContMDiff.comp ContMDiff.inr ContMDiff.inr

variable (M) in
def Diffeomorph.sum_empty [IsEmpty M'] : Diffeomorph I I (M ⊕ M') M ∞ where
  toEquiv := Equiv.sum_empty
  contMDiff_toFun := ContMDiff.sum_elim contMDiff_id (contMDiff_of_const (fun _ ↦ congrFun rfl))
  contMDiff_invFun := ContMDiff.inl

variable (M M' I) in
lemma Diffeomorph.swap_inl : (Diffeomorph.swap M I M') ∘ Sum.inl = Sum.inr := by
  ext
  exact Sum.swap_inl

variable (M M' I) in
lemma Diffeomorph.swap_inr : (Diffeomorph.swap M I M') ∘ Sum.inr = Sum.inl := by
  ext
  exact Sum.swap_inr

end smoothness
