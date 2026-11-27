/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.Topology.Sheaves.SheafOfFunctions
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Functions satisfying a local predicate form a sheaf.

At this stage, in `Mathlib/Topology/Sheaves/SheafOfFunctions.lean`
we've proved that not-necessarily-continuous functions from a topological space
into some type (or type family) form a sheaf.

Why do the continuous functions form a sheaf?
The point is just that continuity is a local condition,
so one can use the lifting condition for functions to provide a candidate lift,
then verify that the lift is actually continuous by using the factorisation condition for the lift
(which guarantees that on each open set it agrees with the functions being lifted,
which were assumed to be continuous).

This file abstracts this argument to work for
any collection of dependent functions on a topological space
satisfying a "local predicate".

As an application, we check that continuity is a local predicate in this sense, and provide
* `TopCat.sheafToTop`: continuous functions into a topological space form a sheaf

A sheaf constructed in this way has a natural map `stalkToFiber` from the stalks
to the types in the ambient type family.

We give conditions sufficient to show that this map is injective and/or surjective.
-/

@[expose] public section

noncomputable section

variable {X : TopCat}
variable (T : X → Type*)

open TopologicalSpace

open Opposite

open CategoryTheory

open CategoryTheory.Limits

open CategoryTheory.Limits.Types

namespace TopCat

/-- Given a topological space `X : TopCat` and a type family `T : X → Type`,
a `P : PrelocalPredicate T` consists of:
* a family of predicates `P.pred`, one for each `U : Opens X`, of the form `(Π x : U, T x) → Prop`
* a proof that if `f : Π x : V, T x` satisfies the predicate on `V : Opens X`, then
  the restriction of `f` to any open subset `U` also satisfies the predicate.
-/
structure PrelocalPredicate where
  /-- The underlying predicate of a prelocal predicate -/
  pred : ∀ {U : Opens X}, (∀ x : U, T x) → Prop
  /-- The underlying predicate should be invariant under restriction -/
  res : ∀ {U V : Opens X} (i : U ⟶ V) (f : ∀ x : V, T x) (_ : pred f), pred fun x : U ↦ f (i x)

variable (X)

/-- Continuity is a "prelocal" predicate on functions to a fixed topological space `T`.
-/
@[simps!]
def continuousPrelocal (T) [TopologicalSpace T] : PrelocalPredicate fun _ : X ↦ T where
  pred {_} f := Continuous f
  res {_ _} i _ h := Continuous.comp h (Opens.isOpenEmbedding_of_le i.le).continuous

/-- Satisfying the inhabited linter. -/
instance inhabitedPrelocalPredicate (T) [TopologicalSpace T] :
    Inhabited (PrelocalPredicate fun _ : X ↦ T) :=
  ⟨continuousPrelocal X T⟩

variable {X} in
/-- Given a topological space `X : TopCat` and a type family `T : X → Type`,
a `P : LocalPredicate T` consists of:
* a family of predicates `P.pred`, one for each `U : Opens X`, of the form `(Π x : U, T x) → Prop`
* a proof that if `f : Π x : V, T x` satisfies the predicate on `V : Opens X`, then
  the restriction of `f` to any open subset `U` also satisfies the predicate, and
* a proof that given some `f : Π x : U, T x`,
  if for every `x : U` we can find an open set `x ∈ V ≤ U`
  so that the restriction of `f` to `V` satisfies the predicate,
  then `f` itself satisfies the predicate.
-/
structure LocalPredicate extends PrelocalPredicate T where
  /-- A local predicate must be local --- provided that it is locally satisfied, it is also globally
  satisfied -/
  locality :
    ∀ {U : Opens X} (f : ∀ x : U, T x)
      (_ : ∀ x : U, ∃ (V : Opens X) (_ : x.val ∈ V) (i : V ⟶ U),
        pred fun x : V ↦ f (i x : U)), pred f

set_option backward.defeqAttrib.useBackward true in
/-- Continuity is a "local" predicate on functions to a fixed topological space `T`.
-/
def continuousLocal (T) [TopologicalSpace T] : LocalPredicate fun _ : X ↦ T :=
  { continuousPrelocal X T with
    locality := fun {U} f w ↦ by
      apply continuous_iff_continuousAt.2
      intro x
      specialize w x
      rcases w with ⟨V, m, i, w⟩
      dsimp at w
      rw [continuous_iff_continuousAt] at w
      specialize w ⟨x, m⟩
      simpa using (Opens.isOpenEmbedding_of_le i.le).continuousAt_iff.1 w }

/-- Satisfying the inhabited linter. -/
instance inhabitedLocalPredicate (T) [TopologicalSpace T] :
    Inhabited (LocalPredicate fun _ : X ↦ T) :=
  ⟨continuousLocal X T⟩

variable {X T}

/-- The conjunction of two prelocal predicates is prelocal. -/
def PrelocalPredicate.and (P Q : PrelocalPredicate T) : PrelocalPredicate T where
  pred f := P.pred f ∧ Q.pred f
  res i f h := ⟨P.res i f h.1, Q.res i f h.2⟩

/-- The conjunction of two prelocal predicates is prelocal. -/
def LocalPredicate.and (P Q : LocalPredicate T) : LocalPredicate T where
  __ := P.toPrelocalPredicate.and Q.toPrelocalPredicate
  locality f w := by
    refine ⟨P.locality f ?_, Q.locality f ?_⟩ <;>
      (intro x; have ⟨V, hV, i, h⟩ := w x; use V, hV, i)
    exacts [h.1, h.2]

/-- The local predicate of being a partial section of a function. -/
def isSection {T} (p : T → X) : LocalPredicate fun _ : X ↦ T where
  pred f := p ∘ f = (↑)
  res _ _ h := funext fun _ ↦ congr_fun h _
  locality _ w := funext fun x ↦ have ⟨_, hV, _, h⟩ := w x; congr_fun h ⟨x, hV⟩

/-- Given a `P : PrelocalPredicate`, we can always construct a `LocalPredicate`
by asking that the condition from `P` holds locally near every point.
-/
def PrelocalPredicate.sheafify {T : X → Type*} (P : PrelocalPredicate T) : LocalPredicate T where
  pred {U} f := ∀ x : U, ∃ (V : Opens X) (_ : x.val ∈ V) (i : V ⟶ U), P.pred fun x : V ↦ f (i x : U)
  res {V U} i f w x := by
    specialize w (i x)
    rcases w with ⟨V', m', i', p⟩
    exact ⟨V ⊓ V', ⟨x.property, m'⟩, V.infLELeft _, P.res (V.infLERight V') _ p⟩
  locality {U} f w x := by
    specialize w x
    rcases w with ⟨V, m, i, p⟩
    specialize p ⟨x.val, m⟩
    rcases p with ⟨V', m', i', p'⟩
    exact ⟨V', m', i' ≫ i, p'⟩

namespace PrelocalPredicate

theorem sheafifyOf {T : X → Type*} {P : PrelocalPredicate T} {U : Opens X}
    {f : ∀ x : U, T x} (h : P.pred f) : P.sheafify.pred f := fun x ↦
  ⟨U, x.property, 𝟙 _, by convert h⟩

/-- For a unary operation (e.g. `x ↦ -x`) defined at each stalk, if a prelocal predicate is closed
under the operation on each open set (possibly by refinement), then the sheafified predicate is
also closed under the operation. See `sheafify_inductionOn'` for the version without refinement. -/
theorem sheafify_inductionOn {X : TopCat} {T : X → Type*} (P : PrelocalPredicate T)
    (op : {x : X} → T x → T x)
    (hop : ∀ {U : Opens X} {a : (x : U) → T x}, P.pred a →
      ∀ (p : U), ∃ (W : Opens X) (i : W ⟶ U), p.val ∈ W ∧ P.pred fun x : W ↦ op (a (i x)))
    {U : Opens X} {a : (x : U) → T x} (ha : P.sheafify.pred a) :
    P.sheafify.pred (fun x : U ↦ op (a x)) := by
  intro x
  rcases ha x with ⟨Va, ma, ia, ha⟩
  rcases hop ha ⟨x, ma⟩ with ⟨W, sa, hx, hw⟩
  exact ⟨W, hx, sa ≫ ia, hw⟩

/-- For a unary operation (e.g. `x ↦ -x`) defined at each stalk, if a prelocal predicate is closed
under the operation on each open set, then the sheafified predicate is also closed under the
operation. See `sheafify_inductionOn` for the version with refinement. -/
theorem sheafify_inductionOn' {X : TopCat} {T : X → Type*} (P : PrelocalPredicate T)
    (op : {x : X} → T x → T x)
    (hop : ∀ {U : Opens X} {a : (x : U) → T x}, P.pred a → P.pred fun x : U ↦ op (a x))
    {U : Opens X} {a : (x : U) → T x} (ha : P.sheafify.pred a) :
    P.sheafify.pred (fun x : U ↦ op (a x)) :=
  P.sheafify_inductionOn op (fun ha p ↦ ⟨_, 𝟙 _, p.property, hop ha⟩) ha

/-- For a binary operation (e.g. `x ↦ y ↦ x + y`) defined at each stalk, if a prelocal predicate is
closed under the operation on each open set (possibly by refinement), then the sheafified predicate
is also closed under the operation. See `sheafify_inductionOn₂'` for the version without
refinement. -/
theorem sheafify_inductionOn₂ {X : TopCat} {T₁ T₂ T₃ : X → Type*}
    (P₁ : PrelocalPredicate T₁) (P₂ : PrelocalPredicate T₂) (P₃ : PrelocalPredicate T₃)
    (op : {x : X} → T₁ x → T₂ x → T₃ x)
    (hop : ∀ {U V : Opens X} {a : (x : U) → T₁ x} {b : (x : V) → T₂ x}, P₁.pred a → P₂.pred b →
      ∀ (p : (U ⊓ V : Opens X)), ∃ (W : Opens X) (ia : W ⟶ U) (ib : W ⟶ V),
      p.val ∈ W ∧ P₃.pred fun x : W ↦ op (a (ia x)) (b (ib x)))
    {U : Opens X} {a : (x : U) → T₁ x} {b : (x : U) → T₂ x}
    (ha : P₁.sheafify.pred a) (hb : P₂.sheafify.pred b) :
    P₃.sheafify.pred (fun x : U ↦ op (a x) (b x)) := by
  intro x
  rcases ha x with ⟨Va, ma, ia, ha⟩
  rcases hb x with ⟨Vb, mb, ib, hb⟩
  rcases hop ha hb ⟨x, ma, mb⟩ with ⟨W, sa, sb, hx, hw⟩
  exact ⟨W, hx, sa ≫ ia, hw⟩

/-- For a binary operation (e.g. `x ↦ y ↦ x + y`) defined at each stalk, if a prelocal predicate is
closed under the operation on each open set, then the sheafified predicate is also closed under the
operation. See `sheafify_inductionOn₂` for the version with refinement. -/
theorem sheafify_inductionOn₂' {X : TopCat} {T₁ T₂ T₃ : X → Type*}
    (P₁ : PrelocalPredicate T₁) (P₂ : PrelocalPredicate T₂) (P₃ : PrelocalPredicate T₃)
    (op : {x : X} → T₁ x → T₂ x → T₃ x)
    (hop : ∀ {U V : Opens X} {a : (x : U) → T₁ x} {b : (x : V) → T₂ x}, P₁.pred a → P₂.pred b →
      P₃.pred fun x : (U ⊓ V : Opens X) ↦ op (a ⟨x, x.property.1⟩) (b ⟨x, x.property.2⟩))
    {U : Opens X} {a : (x : U) → T₁ x} {b : (x : U) → T₂ x}
    (ha : P₁.sheafify.pred a) (hb : P₂.sheafify.pred b) :
    P₃.sheafify.pred (fun x : U ↦ op (a x) (b x)) :=
  P₁.sheafify_inductionOn₂ P₂ P₃ op
    (fun ha hb p ↦ ⟨_, Opens.infLELeft _ _, Opens.infLERight _ _, p.property, hop ha hb⟩) ha hb

end PrelocalPredicate

/-- The subpresheaf of dependent functions on `X` satisfying the "pre-local" predicate `P`.
-/
@[simps]
def subpresheafToTypes (P : PrelocalPredicate T) : Presheaf (Type _) X where
  obj U := { f : ∀ x : U.unop, T x // P.pred f }
  map i := ↾fun f ↦ ⟨fun x ↦ f.val (i.unop x), P.res i.unop f.val f.property⟩

namespace subpresheafToTypes

variable (P : PrelocalPredicate T)

/-- The natural transformation including the subpresheaf of functions satisfying a local predicate
into the presheaf of all functions.
-/
def subtype : subpresheafToTypes P ⟶ presheafToTypes X T where app _ := ↾fun f ↦ f.val

open TopCat.Presheaf

/-- The functions satisfying a local predicate satisfy the sheaf condition.
-/
theorem isSheaf (P : LocalPredicate T) : (subpresheafToTypes P.toPrelocalPredicate).IsSheaf :=
  Presheaf.isSheaf_of_isSheafUniqueGluing_types _ fun ι U sf sf_comp ↦ by
    -- We show the sheaf condition in terms of unique gluing.
    -- First we obtain a family of sections for the underlying sheaf of functions,
    -- by forgetting that the predicate holds
    let sf' (i : ι) : (presheafToTypes X T).obj (op (U i)) := (sf i).val
    -- Since our original family is compatible, this one is as well
    have sf'_comp : (presheafToTypes X T).IsCompatible U sf' := fun i j ↦
      congr($(sf_comp i j).val)
    -- So, we can obtain a unique gluing
    obtain ⟨gl, gl_spec, gl_uniq⟩ := (sheafToTypes X T).existsUnique_gluing U sf'
      -- `by exact` to help Lean infer the `ConcreteCategory` instance
      (by exact sf'_comp)
    refine ⟨⟨gl, ?_⟩, ?_, ?_⟩
    · -- Our first goal is to show that this chosen gluing satisfies the
      -- predicate. Of course, we use locality of the predicate.
      apply P.locality
      rintro ⟨x, mem⟩
      -- Once we're at a particular point `x`, we can select some open set `x ∈ U i`.
      choose i hi using Opens.mem_iSup.mp mem
      -- We claim that the predicate holds in `U i`
      use U i, hi, Opens.leSupr U i
      -- This follows, since our original family `sf` satisfies the predicate
      convert (sf i).property using 1
      exact gl_spec i
    -- It remains to show that the chosen lift is really a gluing for the subsheaf and
    -- that it is unique. Both of which follow immediately from the corresponding facts
    -- in the sheaf of functions without the local predicate.
    · exact fun i ↦ Subtype.ext (gl_spec i)
    · intro gl' hgl'
      refine Subtype.ext ?_
      exact gl_uniq gl'.val fun i ↦ congr($(hgl' i).val)

end subpresheafToTypes

/-- The subsheaf of the sheaf of all dependently typed functions satisfying the local predicate `P`.
-/
@[simps]
def subsheafToTypes (P : LocalPredicate T) : Sheaf (Type _) X :=
  ⟨subpresheafToTypes P.toPrelocalPredicate, subpresheafToTypes.isSheaf P⟩

/-- Auxiliary definition for `stalkToFiber`. -/
def LocalPredicate.cocone (P : LocalPredicate T) (x : X) :
    Cocone ((OpenNhds.inclusion x).op ⋙ subpresheafToTypes P.toPrelocalPredicate) where
  pt := T x
  ι := { app U := ↾fun f ↦ f.val ⟨x, (unop U).property⟩ }

/-- There is a canonical map from the stalk to the original fiber, given by evaluating sections.
-/
def stalkToFiber (P : LocalPredicate T) (x : X) :
    (subsheafToTypes P).presheaf.stalk x ⟶ T x :=
  colimit.desc _ (P.cocone x)

set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma stalkToFiber_ι (P : LocalPredicate T) (x : X) (U : (OpenNhds x)ᵒᵖ)
    (fU : {f //  P.pred f}) :
    dsimp% (stalkToFiber P x)
      (colimit.ι ((OpenNhds.inclusion x).op ⋙ subpresheafToTypes P.toPrelocalPredicate) U fU) =
      (P.cocone x).ι.app U fU :=
  colimit.ι_desc_apply _ _ _

theorem stalkToFiber_germ (P : LocalPredicate T) (U : Opens X) (x : X) (hx : x ∈ U) (f) :
    stalkToFiber P x ((subsheafToTypes P).presheaf.germ U x hx f) = f.val ⟨x, hx⟩ := by
  dsimp [stalkToFiber, Presheaf.germ]
  exact colimit.ι_desc_apply _ _ _

/-- The `stalkToFiber` map is surjective at `x` if
every point in the fiber `T x` has an allowed section passing through it.
-/
theorem stalkToFiber_surjective (P : LocalPredicate T) (x : X)
    (w : ∀ t : T x,
      ∃ (U : OpenNhds x) (f : ∀ y : U.val, T y) (_ : P.pred f), f ⟨x, U.property⟩ = t) :
    Function.Surjective (stalkToFiber P x) := fun t ↦ by
  rcases w t with ⟨U, f, h, rfl⟩
  fconstructor
  · exact (subsheafToTypes P).presheaf.germ _ x U.property ⟨f, h⟩
  · exact stalkToFiber_germ P U.val x U.property ⟨f, h⟩

set_option backward.defeqAttrib.useBackward true in
/-- The `stalkToFiber` map is injective at `x` if any two allowed sections which agree at `x`
agree on some neighborhood of `x`.
-/
theorem stalkToFiber_injective (P : LocalPredicate T) (x : X)
    (w :
      ∀ (U V : OpenNhds x) (fU : ∀ y : U.val, T y) (_ : P.pred fU) (fV : ∀ y : V.val, T y)
        (_ : P.pred fV) (_ : fU ⟨x, U.property⟩ = fV ⟨x, V.property⟩),
        ∃ (W : OpenNhds x) (iU : W ⟶ U) (iV : W ⟶ V), ∀ w : W.val,
          fU (iU w : U.val) = fV (iV w : V.val)) :
    Function.Injective (stalkToFiber P x) := fun tU tV h ↦ by
  -- We promise to provide all the ingredients of the proof later:
  let Q :
    ∃ (W : (OpenNhds x)ᵒᵖ) (s : ∀ w : (unop W).val, T w) (hW : P.pred s),
      tU = (subsheafToTypes P).presheaf.germ _ x (unop W).property ⟨s, hW⟩ ∧
        tV = (subsheafToTypes P).presheaf.germ _ x (unop W).property ⟨s, hW⟩ :=
    ?_
  · choose W s hW e using Q
    exact e.1.trans e.2.symm
  -- Then use induction to pick particular representatives of `tU tV : stalk x`
  dsimp at tU tV h
  obtain ⟨U, ⟨fU, hU⟩, rfl⟩ := jointly_surjective' tU
  obtain ⟨V, ⟨fV, hV⟩, rfl⟩ := jointly_surjective' tV
  -- Decompose everything into its constituent parts:
  simp only [Functor.whiskeringLeft_obj_obj, Functor.comp_obj, Functor.op_obj,
    subpresheafToTypes_obj, stalkToFiber_ι] at h
  specialize w (unop U) (unop V) fU hU fV hV h
  rcases w with ⟨W, iU, iV, w⟩
  -- and put it back together again in the correct order.
  refine ⟨op W, fun w ↦ fU (iU w : (unop U).val), P.res ?_ _ hU, ?_⟩
  · rcases W with ⟨W, m⟩
    exact iU
  · exact ⟨colimit_sound iU.op (Subtype.ext rfl), colimit_sound iV.op (Subtype.ext (funext w).symm)⟩

universe u

/-- Some repackaging:
the presheaf of functions satisfying `continuousPrelocal` is just the same thing as
the presheaf of continuous functions.
-/
def subpresheafContinuousPrelocalIsoPresheafToTop {X : TopCat.{u}} (T : TopCat.{u}) :
    subpresheafToTypes (continuousPrelocal X T) ≅ presheafToTop X T :=
  NatIso.ofComponents fun X ↦
    { hom := ↾fun f ↦ ofHom ⟨f.val, f.property⟩
      inv := ↾fun f ↦ ⟨f.hom', map_continuous f.hom'⟩ }

/-- The sheaf of continuous functions on `X` with values in a space `T`.
-/
def sheafToTop (T : TopCat) : Sheaf (Type _) X :=
  ⟨presheafToTop X T,
    Presheaf.isSheaf_of_iso (subpresheafContinuousPrelocalIsoPresheafToTop T)
      (subpresheafToTypes.isSheaf (continuousLocal X T))⟩

end TopCat
