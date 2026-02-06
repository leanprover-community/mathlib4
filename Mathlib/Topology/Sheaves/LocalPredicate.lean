/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kim Morrison, Adam Topaz
-/
module

public import Mathlib.Topology.Sheaves.SheafOfFunctions
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

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
  pred : Π ⦃U : Opens X⦄, (Π x : U, T x) → Prop
  -- TODO: change `pred` to `Pred` according to naming convention
  /-- The underlying predicate should be invariant under restriction -/
  res : ∀ {U V : Opens X} (i : U ⟶ V) (f : Π x : V, T x), pred f → pred fun x : U ↦ f (i x)

namespace Predicate

variable {T} (P : Π ⦃U : Opens X⦄, (Π x : U, T x) → Prop)

/-- The sheafification of a predicate. -/
def Sheafify ⦃U : Opens X⦄ (f : Π x : U, T x) :=
  ∀ x : U, ∃ (V : Opens X) (_ : x.1 ∈ V) (i : V ⟶ U), P (f <| i ·)

lemma le_sheafify : P ≤ Sheafify P := fun U _f hf x ↦ ⟨U, x.2, 𝟙 U, hf⟩

/-- A predicate is local if sheafification doesn't make it more general. -/
def IsLocal := Sheafify P ≤ P

lemma sheafify_eq_iff : Sheafify P = P ↔ IsLocal P := by
  simp [IsLocal, le_antisymm_iff, le_sheafify]

lemma isLocal_sheafify : IsLocal (Sheafify P) := fun _U _f h x ↦
  have ⟨_V, m, i, p⟩ := h x
  have ⟨V, m', i', p'⟩ := p ⟨x, m⟩
  ⟨V, m', i' ≫ i, p'⟩

end Predicate

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
  locality : Predicate.IsLocal pred

section Pullback

variable {X T} {S : X → Type*} (F : Π x : X, T x → S x) (P : Π ⦃U : Opens X⦄, (Π x : U, S x) → Prop)

def Predicate.Pullback ⦃U : Opens X⦄ (s : Π x : U, T x) : Prop := P (F _ <| s ·)

/-- The pullback of a prelocal predicate. -/
def PrelocalPredicate.pullback (P : PrelocalPredicate S) : PrelocalPredicate T where
  pred := Pullback F P.pred
  res i f := P.res i (F _ <| f ·)

/-- The pullback of a local predicate. -/
def LocalPredicate.pullback (P : LocalPredicate S) : LocalPredicate T where
  __ := P.toPrelocalPredicate.pullback F
  locality U s := P.locality U (F _ <| s ·)

end Pullback

section Predicate

variable {B : TopCat} {F : B → Type*} (P : Π ⦃U : Opens B⦄, (Π b : U, F b) → Prop) (b : B)

/-- The surjectivity criterion for a family of types `F` to behave like the stalks of a
set of sections (represented as a predicate `pred`) says that every germ comes from a section. -/
abbrev IsStalkSurj :=
  ∀ x : F b, ∃ (U : OpenNhds b) (s : Π b : U.1, F b), P s ∧ s ⟨b, U.2⟩ = x

open OpenNhds

/-- The injectivity criterion for a family of types `F` to behave like stalks says that
if two sections pass through the same germ, then they are equal on a neighborhood. -/
abbrev IsStalkInj :=
  ∀ (U V : OpenNhds b) (s : Π b : U.1, F b) (t : Π b : V.1, F b),
    P s → P t → s ⟨b, U.2⟩ = t ⟨b, V.2⟩ →
    ∃ (W : OpenNhds b) (iU : W ⟶ U) (iV : W ⟶ V), ∀ w : W.1, s (iU w) = t (iV w)

/-- The injectivity criterion suitable for a prelocal predicate. -/
abbrev IsStalkInj' :=
  ∀ (U : OpenNhds b) (s t : Π b : U.1, F b), P s → P t → s ⟨b, U.2⟩ = t ⟨b, U.2⟩ →
    ∃ (V : OpenNhds b) (i : V ⟶ U), ∀ b : V.1, s (i b) = t (i b)

theorem IsStalkInj.isStalkInj' {b : B} (h : IsStalkInj P b) : IsStalkInj' P b :=
  fun U s t hs ht eq ↦ have ⟨W, iU, _, h⟩ := h U U s t hs ht eq; ⟨W, iU, h⟩

theorem PrelocalPredicate.isStalkInj_iff {P : PrelocalPredicate F} {b : B} :
    IsStalkInj P.pred b ↔ IsStalkInj' P.pred b := by
  refine ⟨(·.isStalkInj'), fun h U V s t hs ht eq ↦ ?_⟩
  have ⟨W, i, h⟩ := h _ _ _ (P.res (infLELeft U V) s hs) (P.res (infLERight U V) t ht) eq
  exact ⟨W, i ≫ infLELeft U V, i ≫ infLERight U V, h⟩

/-- A set of sections satisfies the identity principle on an open set `U` if sections on `U`
are determined by any germ. `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` shows that
sheaves of analytic functions satisfies the identity principle on any connected open set. -/
abbrev HasIdentityPrincipleOn (U : Opens B) :=
  ∀ (s t : Π b : U.1, F b) b, P s → P t → s b = t b → s = t

/-- A set of sections satisfies the identity principle at a point `b` if every neighborhood of `b`
contains a neighborhood on which the identity principle is satisfied.
This definition is intended to be applied to a locally connected base space `B`. -/
abbrev HasIdentityPrinciple :=
  ∀ U : OpenNhds b, ∃ V ≤ U, HasIdentityPrincipleOn P V.1

/-- A set of sections is separated at a point `b` if any two germs at `b` can be separated by
disjoint sections. -/
abbrev IsSeparated :=
  ∀ x y : F b, x ≠ y → ∃ (U : OpenNhds b) (s t : Π b : U.1, F b), P s ∧ P t ∧
    s ⟨b, U.2⟩ = x ∧ t ⟨b, U.2⟩ = y ∧ ∀ b' : U.1, s b' ≠ t b'

/-- A set of sections is constant on a (connected) open set `U` if every germ on `U` can be
extended to a section on `U` in exactly one way.
This corresponds to the `IsEvenlyCovered` condition in the associated étale space. -/
abbrev IsConstantOn (U : Opens B) : Prop :=
  ∀ (b₀ : U) (x : F b₀), ∃! s : Π b : U, F b, P s ∧ s b₀ = x

/-- A trivialization indexed by `ι` of a set of sections on a set `U` is a subset of sections
indexed by `ι` which induces, for each point of `U`, a bijection between `ι` and the germs
at that point. Together with `IsStalkInj`, this is enough to guarantee that `U` is evenly
covered by the étalé space associated to the set of sections. -/
structure TrivializationOn (U : Opens B) (ι : Type*) : Type _ where
  /-- The sections indexed by `ι`. -/
  sec : ι → Π b : U, F b
  pred i : P (sec i)
  bijective b : Function.Bijective (sec · b)

/-- A set of sections is weakly locally constant at a point `b` if `b` has a neighborhood on which
every germ can be extended to a section in exactly one way.
This is weaker than `IsLocallyConstant`, and the étalé space associated to a weakly locally
constant set of sections is not necessarily a covering space, but `IsWeaklyLocallyConstant` still
implies `IsSeparated` and `IsStalkSurj`. -/
abbrev IsWeaklyLocallyConstant := ∃ U : OpenNhds b, IsConstantOn P U.1

/-- A set of sections is locally constant at a point `b` if every neighborhood of `b` contains
a neighborhood on which every germ can be extended to a section in exactly one way.
This definition is intended to be applied to a locally connected base space `B`:
if `B` is not locally connected, locally constant sheaves on `B` may not give rise to
locally constant sets of sections, but locally constant sets of sections do always give
rise to covering spaces. -/
abbrev IsLocallyConstant := ∀ U : OpenNhds b, ∃ V ≤ U, IsConstantOn P V.1

variable {P}

theorem isConstantOn_iff {U : Opens B} : IsConstantOn P U ↔
    HasIdentityPrincipleOn P U ∧ ∀ (b : U) (x : F b), ∃ s : Π b : U, F b, P s ∧ s b = x where
  mp h := ⟨fun _s t b hs ht eq ↦ (h b (t b)).unique ⟨hs, eq⟩ ⟨ht, rfl⟩,
    fun b x ↦ (h b x).exists⟩
  mpr := fun ⟨ip, surj⟩ b x ↦ existsUnique_of_exists_of_unique (surj b x)
    fun s t hs ht ↦ ip s t b hs.1 ht.1 (hs.2.trans ht.2.symm)

theorem IsConstantOn.hasIdentityPrincipleOn {U : Opens B} (h : IsConstantOn P U) :
    HasIdentityPrincipleOn P U := (isConstantOn_iff.mp h).1

theorem IsLocallyConstant.hasIdentityPrinciple (h : IsLocallyConstant P b) :
    HasIdentityPrinciple P b :=
  fun U ↦ have ⟨V, le, hV⟩ := h U; ⟨V, le, hV.hasIdentityPrincipleOn⟩

theorem IsLocallyConstant.isWeaklyLocallyConstant (h : IsLocallyConstant P b) :
    IsWeaklyLocallyConstant P b :=
  have ⟨U, _, hU⟩ := h ⊤; ⟨U, hU⟩

theorem HasIdentityPrinciple.isSeparated {P : PrelocalPredicate F}
    (ip : HasIdentityPrinciple P.pred b) (surj : IsStalkSurj P.pred b) : IsSeparated P.pred b :=
  fun x y ne ↦ by
    obtain ⟨U₁, s₁, h₁, rfl⟩ := surj x
    obtain ⟨U₂, s₂, h₂, rfl⟩ := surj y
    have ⟨U, le, hU⟩ := ip (U₁ ⊓ U₂)
    replace h₁ := P.res (le.hom ≫ infLELeft ..) _ h₁
    replace h₂ := P.res (le.hom ≫ infLERight ..) _ h₂
    exact ⟨U, _, _, h₁, h₂, rfl, rfl, fun x eq ↦ ne <| congr_fun (hU _ _ _ h₁ h₂ eq) ⟨b, U.2⟩⟩

theorem IsWeaklyLocallyConstant.isStalkSurj (h : IsWeaklyLocallyConstant P b) :
    IsStalkSurj P b :=
  fun x ↦ have ⟨U, hU⟩ := h; have ⟨s, hs, _⟩ := hU ⟨b, U.2⟩ x; ⟨U, s, hs⟩

theorem IsWeaklyLocallyConstant.isSeparated (h : IsWeaklyLocallyConstant P b) :
    IsSeparated P b :=
  fun x y ne ↦ by
    have ⟨U, hU⟩ := h
    have ⟨s, hs, hsu⟩ := hU ⟨b, U.2⟩ x
    have ⟨t, ht, htu⟩ := hU ⟨b, U.2⟩ y
    refine ⟨U, s, t, hs.1, ht.1, hs.2, ht.2, fun b' eq ↦ ne ?_⟩
    rw [← hs.2, (isConstantOn_iff.mp hU).1 s t b' hs.1 ht.1 eq, ht.2]

theorem HasIdentityPrinciple.isStalkInj {P : PrelocalPredicate F}
    (h : HasIdentityPrinciple P.pred b) : IsStalkInj P.pred b :=
  P.isStalkInj_iff.mpr fun U _s _t hs ht eq ↦ have ⟨V, le, ip⟩ := h U
    ⟨V, le.hom, congr_fun (ip _ _ ⟨b, V.2⟩ (P.res le.hom _ hs) (P.res le.hom _ ht) eq)⟩

namespace IsConstantOn

variable {U : Opens B} (h : IsConstantOn P U) {b : U} (x : F b)

/-- The section on `U` with given germ at `b : U` within a set of sections constant on `U`. -/
def sec : Π b : U, F b := (h b x).choose

lemma pred_sec : P (h.sec x) := (h b x).choose_spec.1.1

lemma sec_apply : h.sec x b = x := (h b x).choose_spec.1.2

lemma sec_eq_of_pred {s : Π b : U, F b} (hs : P s) (b : U) : h.sec (s b) = s :=
  (isConstantOn_iff.mp h).1 _ _ b (h.pred_sec _) hs (h.sec_apply _)

/-- The monodromy induced by a set of sections constant on `U`. -/
def monodromy (b b' : U) : F b ≃ F b' where
  toFun x := h.sec x b'
  invFun x := h.sec x b
  left_inv _ := by simp_rw [h.sec_eq_of_pred (h.pred_sec _), h.sec_apply]
  right_inv _ := by simp_rw [h.sec_eq_of_pred (h.pred_sec _), h.sec_apply]

include h in
/-- The trivialization induced by a set of sections constant on `U`. -/
def trivializationOn (b : U) : TrivializationOn P U (F b) where
  sec := h.sec
  pred := h.pred_sec
  bijective _ := (h.monodromy ..).bijective

end IsConstantOn

namespace TrivializationOn

variable {U : Opens B} {ι} (t : TrivializationOn P U ι)

/-- A trivialization of a set of sections over a set `U` induces a trivialization of the `Sigma`
type over `U`. -/
def equiv : {f : Σ b, F b // f.1 ∈ U} ≃ U × ι :=
  .trans (.symm (.trans (.sigmaCongrRight (.ofBijective _ <| t.bijective ·)) .sigmaSubtypeComm))
    (.sigmaEquivProd ..)

lemma symm_apply_coe (x : U × ι) : t.equiv.symm x = Sigma.mk _ (t.sec x.2 x.1) := rfl

lemma preimage_snd_comp_equiv (i : ι) :
    Prod.snd ∘ t.equiv ⁻¹' {i} = Subtype.val ⁻¹' Set.range (Sigma.mk _ <| t.sec i ·) :=
  Set.ext fun f ↦ (Equiv.symm_apply_eq _).trans <| by
    simp only [Equiv.sigmaSubtypeComm, Equiv.coe_fn_symm_mk,
      Equiv.ofBijective_apply, Set.mem_preimage, Set.mem_range]
    refine ⟨fun h ↦ ⟨⟨_, f.2⟩, congr(Sigma.mk _ $h).symm⟩, fun ⟨b, h⟩ ↦ ?_⟩
    obtain ⟨⟨b', x⟩, hbx⟩ := f
    cases congr($h.1)
    exact congr($h.2).symm

end TrivializationOn

end Predicate

open Predicate

/-- Continuity is a "local" predicate on functions to a fixed topological space `T`.
-/
def continuousLocal (T : Type*) [TopologicalSpace T] : LocalPredicate fun _ : X ↦ T :=
  { continuousPrelocal X T with
    locality := fun {U} f w ↦ by
      apply continuous_iff_continuousAt.2
      intro x
      rcases w x with ⟨V, m, i, w⟩
      dsimp at w
      rw [continuous_iff_continuousAt] at w
      specialize w ⟨x, m⟩
      simpa using (Opens.isOpenEmbedding_of_le i.le).continuousAt_iff.1 w }

/-- Satisfying the inhabited linter. -/
instance inhabitedLocalPredicate (T : Type*) [TopologicalSpace T] :
    Inhabited (LocalPredicate fun _ : X ↦ T) :=
  ⟨continuousLocal X T⟩

variable {X T}

/-- The conjunction of two prelocal predicates is prelocal. -/
def PrelocalPredicate.and (P Q : PrelocalPredicate T) : PrelocalPredicate T where
  pred _ f := P.pred f ∧ Q.pred f
  res i f h := ⟨P.res i f h.1, Q.res i f h.2⟩

lemma Predicate.IsLocal.inf {P Q : Π ⦃U : Opens X⦄, (Π x : U, T x) → Prop}
    (hP : IsLocal P) (hQ : IsLocal Q) : IsLocal (P ⊓ Q) := fun U f w ↦ by
  refine ⟨hP U f ?_, hQ U f ?_⟩ <;> (intro x; have ⟨V, hV, i, h⟩ := w x; use V, hV, i)
  exacts [h.1, h.2]

/-- The conjunction of two prelocal predicates is prelocal. -/
def LocalPredicate.and (P Q : LocalPredicate T) : LocalPredicate T where
  __ := P.1.and Q.1
  locality := P.locality.inf Q.locality

/-- The local predicate of being a partial section of a function. -/
def isSection {T} (p : T → X) : LocalPredicate fun _ : X ↦ T where
  pred _ f := p ∘ f = (↑)
  res _ _ h := funext fun _ ↦ congr_fun h _
  locality _ _ w := funext fun x ↦ have ⟨_, hV, _, h⟩ := w x; congr_fun h ⟨x, hV⟩

/-- Continuity is a local predicate on sections of a map between topological spaces. -/
def isContinuousSection {T} [TopologicalSpace T] (p : T → X) : LocalPredicate (p ⁻¹' {·}) where
  pred _U f := Continuous fun x ↦ (f x).1
  res i _f := (continuousLocal X T).res i _
  locality U _f h := (continuousLocal X T).locality U _ h

section Sheafify

variable {T : X → Type*} (P : PrelocalPredicate T)

/-- Given a `P : PrelocalPredicate`, we can always construct a `LocalPredicate`
by asking that the condition from `P` holds locally near every point.
-/
def PrelocalPredicate.sheafify : LocalPredicate T where
  pred := Sheafify P.pred
  res {V U} i f w x := by
    rcases w (i x) with ⟨V', m', i', p⟩
    exact ⟨V ⊓ V', ⟨x.2, m'⟩, V.infLELeft _, P.res (V.infLERight V') _ p⟩
  locality := isLocal_sheafify _

variable {P}

theorem PrelocalPredicate.sheafifyOf {U : Opens X} {f : Π x : U, T x} (h : P.pred f) :
    P.sheafify.pred f := le_sheafify _ _ _ h

theorem IsStalkSurj.sheafify {x : X} (h : IsStalkSurj P.pred x) :
    IsStalkSurj P.sheafify.pred x :=
  fun t ↦ have ⟨U, s, hs, eq⟩ := h t; ⟨U, s, P.sheafifyOf hs, eq⟩

theorem IsStalkInj.sheafify {x : X} (h : IsStalkInj P.pred x) : IsStalkInj P.sheafify.pred x :=
  fun U V _fU _fV hU hV e ↦
    have ⟨U', mU, iU, hU⟩ := hU ⟨x, U.2⟩
    have ⟨V', mV, iV, hV⟩ := hV ⟨x, V.2⟩
    have ⟨W, iU', iV', h⟩ := h ⟨U', mU⟩ ⟨V', mV⟩ _ _ hU hV e
    ⟨W, iU' ≫ iU, iV' ≫ iV, h⟩

end Sheafify

namespace PrelocalPredicate

/-- For a unary operation (e.g. `x ↦ -x`) defined at each stalk, if a prelocal predicate is closed
under the operation on each open set (possibly by refinement), then the sheafified predicate is
also closed under the operation. See `sheafify_inductionOn'` for the version without refinement. -/
theorem sheafify_inductionOn {X : TopCat} {T : X → Type*} (P : PrelocalPredicate T)
    (op : {x : X} → T x → T x)
    (hop : ∀ {U : Opens X} {a : (x : U) → T x}, P.pred a →
      ∀ (p : U), ∃ (W : Opens X) (i : W ⟶ U), p.1 ∈ W ∧ P.pred fun x : W ↦ op (a (i x)))
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
  P.sheafify_inductionOn op (fun ha p ↦ ⟨_, 𝟙 _, p.2, hop ha⟩) ha

/-- For a binary operation (e.g. `x ↦ y ↦ x + y`) defined at each stalk, if a prelocal predicate is
closed under the operation on each open set (possibly by refinement), then the sheafified predicate
is also closed under the operation. See `sheafify_inductionOn₂'` for the version without
refinement. -/
theorem sheafify_inductionOn₂ {X : TopCat} {T₁ T₂ T₃ : X → Type*}
    (P₁ : PrelocalPredicate T₁) (P₂ : PrelocalPredicate T₂) (P₃ : PrelocalPredicate T₃)
    (op : {x : X} → T₁ x → T₂ x → T₃ x)
    (hop : ∀ {U V : Opens X} {a : (x : U) → T₁ x} {b : (x : V) → T₂ x}, P₁.pred a → P₂.pred b →
      ∀ (p : (U ⊓ V : Opens X)), ∃ (W : Opens X) (ia : W ⟶ U) (ib : W ⟶ V),
      p.1 ∈ W ∧ P₃.pred fun x : W ↦ op (a (ia x)) (b (ib x)))
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
      P₃.pred fun x : (U ⊓ V : Opens X) ↦ op (a ⟨x, x.2.1⟩) (b ⟨x, x.2.2⟩))
    {U : Opens X} {a : (x : U) → T₁ x} {b : (x : U) → T₂ x}
    (ha : P₁.sheafify.pred a) (hb : P₂.sheafify.pred b) :
    P₃.sheafify.pred (fun x : U ↦ op (a x) (b x)) :=
  P₁.sheafify_inductionOn₂ P₂ P₃ op
    (fun ha hb p ↦ ⟨_, Opens.infLELeft _ _, Opens.infLERight _ _, p.2, hop ha hb⟩) ha hb

end PrelocalPredicate

/-- The subpresheaf of dependent functions on `X` satisfying the "pre-local" predicate `P`.
-/
@[simps!]
def subpresheafToTypes (P : PrelocalPredicate T) : Presheaf (Type _) X where
  obj U := { f : Π x : U.unop, T x // P.pred f }
  map {_ _} i f := ⟨fun x ↦ f.1 (i.unop x), P.res i.unop f.1 f.2⟩

namespace subpresheafToTypes

variable (P : PrelocalPredicate T)

/-- The natural transformation including the subpresheaf of functions satisfying a local predicate
into the presheaf of all functions.
-/
def subtype : subpresheafToTypes P ⟶ presheafToTypes X T where app _ f := f.1

open TopCat.Presheaf

attribute [local instance] Types.instFunLike Types.instConcreteCategory in
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
      congr_arg Subtype.val (sf_comp i j)
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
      exact gl_uniq gl'.1 fun i ↦ congr_arg Subtype.val (hgl' i)

end subpresheafToTypes

/-- The subsheaf of the sheaf of all dependently typed functions satisfying the local predicate `P`.
-/
@[simps]
def subsheafToTypes (P : LocalPredicate T) : Sheaf (Type _) X :=
  ⟨subpresheafToTypes P.toPrelocalPredicate, subpresheafToTypes.isSheaf P⟩

/-- There is a canonical map from the stalk to the original fiber, given by evaluating sections. -/
def stalkToFiber (P : PrelocalPredicate T) (x : X) : (subpresheafToTypes P).stalk x → T x :=
  ULift.down ∘ colimit.desc _
    { pt := ULift (T x)
      ι := { app := fun U f ↦ ⟨by exact f.1 ⟨x, (unop U).2⟩⟩ } }

theorem stalkToFiber_germ (P : PrelocalPredicate T) (U : Opens X) (x : X) (hx : x ∈ U) (f) :
    stalkToFiber P x ((subpresheafToTypes P).germ U x hx f) = f.1 ⟨x, hx⟩ := by
  simp [stalkToFiber, Presheaf.germ, Colimit.ι_desc_apply]

/-- The `stalkToFiber` map is surjective at `x` if
every point in the fiber `T x` has an allowed section passing through it. -/
-- TODO: upgrade to iff?
theorem stalkToFiber_surjective (P : PrelocalPredicate T) (x : X) (w : IsStalkSurj P.pred x) :
    Function.Surjective (stalkToFiber P x) := fun t ↦ by
  rcases w t with ⟨U, f, h, rfl⟩
  exact ⟨_, stalkToFiber_germ P U.1 x U.2 ⟨f, h⟩⟩

/-- The `stalkToFiber` map is injective at `x` if any two allowed sections which agree at `x`
agree on some neighborhood of `x`. -/
-- TODO: upgrade to iff?
theorem stalkToFiber_injective (P : PrelocalPredicate T) (x : X) (w : IsStalkInj P.pred x) :
    Function.Injective (stalkToFiber P x) := fun tU tV h ↦ by
  -- We promise to provide all the ingredients of the proof later:
  let Q :
    ∃ (W : (OpenNhds x)ᵒᵖ) (s : Π w : (unop W).1, T w) (hW : P.pred s),
      tU = (subpresheafToTypes P).germ _ x (unop W).2 ⟨s, hW⟩ ∧
        tV = (subpresheafToTypes P).germ _ x (unop W).2 ⟨s, hW⟩ := ?_
  · choose W s hW e using Q
    exact e.1.trans e.2.symm
  -- Then use induction to pick particular representatives of `tU tV : stalk x`
  obtain ⟨U, ⟨fU, hU⟩, rfl⟩ := jointly_surjective' tU
  obtain ⟨V, ⟨fV, hV⟩, rfl⟩ := jointly_surjective' tV
  -- Decompose everything into its constituent parts:
  simp_rw [stalkToFiber, Function.comp_apply, Colimit.ι_desc_apply] at h
  specialize w (unop U) (unop V) fU fV hU hV h
  rcases w with ⟨W, iU, iV, w⟩
  -- and put it back together again in the correct order.
  refine ⟨op W, fun w ↦ fU (iU w : (unop U).1), P.res ?_ _ hU, ?_⟩
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
    { hom := by rintro ⟨f, c⟩; exact ofHom ⟨f, c⟩
      inv := by rintro ⟨f, c⟩; exact ⟨f, c⟩ }

/-- The sheaf of continuous functions on `X` with values in a space `T`.
-/
def sheafToTop (T : TopCat) : Sheaf (Type _) X :=
  ⟨presheafToTop X T,
    Presheaf.isSheaf_of_iso (subpresheafContinuousPrelocalIsoPresheafToTop T)
      (subpresheafToTypes.isSheaf (continuousLocal X T))⟩

end TopCat
