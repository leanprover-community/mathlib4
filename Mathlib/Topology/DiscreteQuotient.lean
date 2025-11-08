/-
Copyright (c) 2021 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne, Adam Topaz
-/
import Mathlib.Data.Setoid.Partition
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Connected.TotallyDisconnected

/-!

# Discrete quotients of a topological space.

This file defines the type of discrete quotients of a topological space,
denoted `DiscreteQuotient X`. To avoid quantifying over types, we model such
quotients as setoids whose equivalence classes are clopen.

## Definitions
1. `DiscreteQuotient X` is the type of discrete quotients of `X`.
  It is endowed with a coercion to `Type`, which is defined as the
  quotient associated to the setoid in question, and each such quotient
  is endowed with the discrete topology.
2. Given `S : DiscreteQuotient X`, the projection `X → S` is denoted
  `S.proj`.
3. When `X` is compact and `S : DiscreteQuotient X`, the space `S` is
  endowed with a `Fintype` instance.

## Order structure

The type `DiscreteQuotient X` is endowed with an instance of a `SemilatticeInf` with `OrderTop`.
The partial ordering `A ≤ B` mathematically means that `B.proj` factors through `A.proj`.
The top element `⊤` is the trivial quotient, meaning that every element of `X` is collapsed
to a point. Given `h : A ≤ B`, the map `A → B` is `DiscreteQuotient.ofLE h`.

Whenever `X` is a locally connected space, the type `DiscreteQuotient X` is also endowed with an
instance of an `OrderBot`, where the bot element `⊥` is given by the `connectedComponentSetoid`,
i.e., `x ~ y` means that `x` and `y` belong to the same connected component. In particular, if `X`
is a discrete topological space, then `x ~ y` is equivalent (propositionally, not definitionally) to
`x = y`.

Given `f : C(X, Y)`, we define a predicate `DiscreteQuotient.LEComap f A B` for
`A : DiscreteQuotient X` and `B : DiscreteQuotient Y`, asserting that `f` descends to `A → B`. If
`cond : DiscreteQuotient.LEComap h A B`, the function `A → B` is obtained by
`DiscreteQuotient.map f cond`.

## Theorems

The two main results proved in this file are:

1. `DiscreteQuotient.eq_of_forall_proj_eq` which states that when `X` is compact, T₂, and totally
  disconnected, any two elements of `X` are equal if their projections in `Q` agree for all
  `Q : DiscreteQuotient X`.

2. `DiscreteQuotient.exists_of_compat` which states that when `X` is compact, then any
  system of elements of `Q` as `Q : DiscreteQuotient X` varies, which is compatible with
  respect to `DiscreteQuotient.ofLE`, must arise from some element of `X`.

## Remarks
The constructions in this file will be used to show that any profinite space is a limit
of finite discrete spaces.
-/


open Set Function TopologicalSpace Topology

variable {α X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The type of discrete quotients of a topological space. -/
@[ext]
structure DiscreteQuotient (X : Type*) [TopologicalSpace X] extends Setoid X where
  /-- For every point `x`, the set `{ y | Rel x y }` is an open set. -/
  protected isOpen_setOf_rel : ∀ x, IsOpen (setOf (toSetoid x))

namespace DiscreteQuotient

variable (S : DiscreteQuotient X)

lemma toSetoid_injective : Function.Injective (@toSetoid X _)
  | ⟨_, _⟩, ⟨_, _⟩, _ => by congr

/-- Construct a discrete quotient from a clopen set. -/
def ofIsClopen {A : Set X} (h : IsClopen A) : DiscreteQuotient X where
  toSetoid := ⟨fun x y => x ∈ A ↔ y ∈ A, fun _ => Iff.rfl, Iff.symm, Iff.trans⟩
  isOpen_setOf_rel x := by by_cases hx : x ∈ A <;> simp [hx, h.1, h.2, ← compl_setOf]

theorem refl : ∀ x, S.toSetoid x x := S.refl'

theorem symm (x y : X) : S.toSetoid x y → S.toSetoid y x := S.symm'

theorem trans (x y z : X) : S.toSetoid x y → S.toSetoid y z → S.toSetoid x z := S.trans'

/-- The setoid whose quotient yields the discrete quotient. -/
add_decl_doc toSetoid

instance : CoeSort (DiscreteQuotient X) (Type _) :=
  ⟨fun S => Quotient S.toSetoid⟩

instance : TopologicalSpace S :=
  inferInstanceAs (TopologicalSpace (Quotient S.toSetoid))

/-- The projection from `X` to the given discrete quotient. -/
def proj : X → S := Quotient.mk''

theorem fiber_eq (x : X) : S.proj ⁻¹' {S.proj x} = setOf (S.toSetoid x) :=
  Set.ext fun _ => eq_comm.trans Quotient.eq''

theorem proj_surjective : Function.Surjective S.proj :=
  Quotient.mk''_surjective

theorem proj_isQuotientMap : IsQuotientMap S.proj :=
  isQuotientMap_quot_mk

theorem proj_continuous : Continuous S.proj :=
  S.proj_isQuotientMap.continuous

instance : DiscreteTopology S :=
  discreteTopology_iff_isOpen_singleton.2 <| S.proj_surjective.forall.2 fun x => by
    rw [← S.proj_isQuotientMap.isOpen_preimage, fiber_eq]
    exact S.isOpen_setOf_rel _

theorem proj_isLocallyConstant : IsLocallyConstant S.proj :=
  (IsLocallyConstant.iff_continuous S.proj).2 S.proj_continuous

theorem isClopen_preimage (A : Set S) : IsClopen (S.proj ⁻¹' A) :=
  (isClopen_discrete A).preimage S.proj_continuous

theorem isOpen_preimage (A : Set S) : IsOpen (S.proj ⁻¹' A) :=
  (S.isClopen_preimage A).2

theorem isClosed_preimage (A : Set S) : IsClosed (S.proj ⁻¹' A) :=
  (S.isClopen_preimage A).1

theorem isClopen_setOf_rel (x : X) : IsClopen (setOf (S.toSetoid x)) := by
  rw [← fiber_eq]
  apply isClopen_preimage

instance : Min (DiscreteQuotient X) :=
  ⟨fun S₁ S₂ => ⟨S₁.1 ⊓ S₂.1, fun x => (S₁.2 x).inter (S₂.2 x)⟩⟩

instance : SemilatticeInf (DiscreteQuotient X) :=
  Injective.semilatticeInf toSetoid toSetoid_injective fun _ _ => rfl

instance : OrderTop (DiscreteQuotient X) where
  top := ⟨⊤, fun _ => isOpen_univ⟩
  le_top a := by tauto

instance : Inhabited (DiscreteQuotient X) := ⟨⊤⟩

instance inhabitedQuotient [Inhabited X] : Inhabited S := ⟨S.proj default⟩

-- TODO: add instances about `Nonempty (Quot _)`/`Nonempty (Quotient _)`
instance [Nonempty X] : Nonempty S := Nonempty.map S.proj ‹_›

/-- The quotient by `⊤ : DiscreteQuotient X` is a `Subsingleton`. -/
instance : Subsingleton (⊤ : DiscreteQuotient X) where
  allEq := by rintro ⟨_⟩ ⟨_⟩; exact Quotient.sound trivial

section Comap

variable (g : C(Y, Z)) (f : C(X, Y))

/-- Comap a discrete quotient along a continuous map. -/
def comap (S : DiscreteQuotient Y) : DiscreteQuotient X where
  toSetoid := Setoid.comap f S.1
  isOpen_setOf_rel _ := (S.2 _).preimage f.continuous

@[simp]
theorem comap_id : S.comap (ContinuousMap.id X) = S := rfl

@[simp]
theorem comap_comp (S : DiscreteQuotient Z) : S.comap (g.comp f) = (S.comap g).comap f :=
  rfl

@[mono]
theorem comap_mono {A B : DiscreteQuotient Y} (h : A ≤ B) : A.comap f ≤ B.comap f := by tauto

end Comap

section OfLE

variable {A B C : DiscreteQuotient X}

/-- The map induced by a refinement of a discrete quotient. -/
def ofLE (h : A ≤ B) : A → B :=
  Quotient.map' id h

@[simp]
theorem ofLE_refl : ofLE (le_refl A) = id := by
  ext ⟨⟩
  rfl

theorem ofLE_refl_apply (a : A) : ofLE (le_refl A) a = a := by simp

@[simp]
theorem ofLE_ofLE (h₁ : A ≤ B) (h₂ : B ≤ C) (x : A) :
    ofLE h₂ (ofLE h₁ x) = ofLE (h₁.trans h₂) x := by
  rcases x with ⟨⟩
  rfl

@[simp]
theorem ofLE_comp_ofLE (h₁ : A ≤ B) (h₂ : B ≤ C) : ofLE h₂ ∘ ofLE h₁ = ofLE (le_trans h₁ h₂) :=
  funext <| ofLE_ofLE _ _

theorem ofLE_continuous (h : A ≤ B) : Continuous (ofLE h) :=
  continuous_of_discreteTopology

@[simp]
theorem ofLE_proj (h : A ≤ B) (x : X) : ofLE h (A.proj x) = B.proj x :=
  Quotient.sound' (B.refl _)

@[simp]
theorem ofLE_comp_proj (h : A ≤ B) : ofLE h ∘ A.proj = B.proj :=
  funext <| ofLE_proj _

end OfLE

/-- When `X` is a locally connected space, there is an `OrderBot` instance on
`DiscreteQuotient X`. The bottom element is given by `connectedComponentSetoid X`
-/
instance [LocallyConnectedSpace X] : OrderBot (DiscreteQuotient X) where
  bot :=
    { toSetoid := connectedComponentSetoid X
      isOpen_setOf_rel := fun x => by
        convert isOpen_connectedComponent (x := x)
        ext y
        simpa only [connectedComponentSetoid, ← connectedComponent_eq_iff_mem] using eq_comm }
  bot_le S := fun x y (h : connectedComponent x = connectedComponent y) =>
    (S.isClopen_setOf_rel x).connectedComponent_subset (S.refl _) <| h.symm ▸ mem_connectedComponent

@[simp]
theorem proj_bot_eq [LocallyConnectedSpace X] {x y : X} :
    proj ⊥ x = proj ⊥ y ↔ connectedComponent x = connectedComponent y :=
  Quotient.eq''

theorem proj_bot_inj [DiscreteTopology X] {x y : X} : proj ⊥ x = proj ⊥ y ↔ x = y := by simp

theorem proj_bot_injective [DiscreteTopology X] : Injective (⊥ : DiscreteQuotient X).proj :=
  fun _ _ => proj_bot_inj.1

theorem proj_bot_bijective [DiscreteTopology X] : Bijective (⊥ : DiscreteQuotient X).proj :=
  ⟨proj_bot_injective, proj_surjective _⟩

section Map

variable (f : C(X, Y)) (A A' : DiscreteQuotient X) (B B' : DiscreteQuotient Y)

/-- Given `f : C(X, Y)`, `DiscreteQuotient.LEComap f A B` is defined as
`A ≤ B.comap f`. Mathematically this means that `f` descends to a morphism `A → B`. -/
def LEComap : Prop :=
  A ≤ B.comap f

theorem leComap_id : LEComap (.id X) A A := le_rfl

variable {A A' B B'} {f} {g : C(Y, Z)} {C : DiscreteQuotient Z}

@[simp]
theorem leComap_id_iff : LEComap (ContinuousMap.id X) A A' ↔ A ≤ A' :=
  Iff.rfl

theorem LEComap.comp : LEComap g B C → LEComap f A B → LEComap (g.comp f) A C := by tauto

@[mono]
theorem LEComap.mono (h : LEComap f A B) (hA : A' ≤ A) (hB : B ≤ B') : LEComap f A' B' :=
  hA.trans <| h.trans <| comap_mono _ hB

/-- Map a discrete quotient along a continuous map. -/
def map (f : C(X, Y)) (cond : LEComap f A B) : A → B := Quotient.map' f cond

theorem map_continuous (cond : LEComap f A B) : Continuous (map f cond) :=
  continuous_of_discreteTopology

@[simp]
theorem map_comp_proj (cond : LEComap f A B) : map f cond ∘ A.proj = B.proj ∘ f :=
  rfl

@[simp]
theorem map_proj (cond : LEComap f A B) (x : X) : map f cond (A.proj x) = B.proj (f x) :=
  rfl

@[simp]
theorem map_id : map _ (leComap_id A) = id := by ext ⟨⟩; rfl

/- This can't be a `@[simp]` lemma since `h1` and `h2` can't be found by unification in a Prop. -/
theorem map_comp (h1 : LEComap g B C) (h2 : LEComap f A B) :
    map (g.comp f) (h1.comp h2) = map g h1 ∘ map f h2 := by
  ext ⟨⟩
  rfl

@[simp]
theorem ofLE_map (cond : LEComap f A B) (h : B ≤ B') (a : A) :
    ofLE h (map f cond a) = map f (cond.mono le_rfl h) a := by
  rcases a with ⟨⟩
  rfl

@[simp]
theorem ofLE_comp_map (cond : LEComap f A B) (h : B ≤ B') :
    ofLE h ∘ map f cond = map f (cond.mono le_rfl h) :=
  funext <| ofLE_map cond h

@[simp]
theorem map_ofLE (cond : LEComap f A B) (h : A' ≤ A) (c : A') :
    map f cond (ofLE h c) = map f (cond.mono h le_rfl) c := by
  rcases c with ⟨⟩
  rfl

@[simp]
theorem map_comp_ofLE (cond : LEComap f A B) (h : A' ≤ A) :
    map f cond ∘ ofLE h = map f (cond.mono h le_rfl) :=
  funext <| map_ofLE cond h

end Map

theorem eq_of_forall_proj_eq [T2Space X] [CompactSpace X] [disc : TotallyDisconnectedSpace X]
    {x y : X} (h : ∀ Q : DiscreteQuotient X, Q.proj x = Q.proj y) : x = y := by
  rw [← mem_singleton_iff, ← connectedComponent_eq_singleton, connectedComponent_eq_iInter_isClopen,
    mem_iInter]
  rintro ⟨U, hU1, hU2⟩
  exact (Quotient.exact' (h (ofIsClopen hU1))).mpr hU2

theorem fiber_subset_ofLE {A B : DiscreteQuotient X} (h : A ≤ B) (a : A) :
    A.proj ⁻¹' {a} ⊆ B.proj ⁻¹' {ofLE h a} := by
  rcases A.proj_surjective a with ⟨a, rfl⟩
  rw [fiber_eq, ofLE_proj, fiber_eq]
  exact fun _ h' => h h'

theorem exists_of_compat [CompactSpace X] (Qs : (Q : DiscreteQuotient X) → Q)
    (compat : ∀ (A B : DiscreteQuotient X) (h : A ≤ B), ofLE h (Qs _) = Qs _) :
    ∃ x : X, ∀ Q : DiscreteQuotient X, Q.proj x = Qs _ := by
  have H₁ : ∀ Q₁ Q₂, Q₁ ≤ Q₂ → proj Q₁ ⁻¹' {Qs Q₁} ⊆ proj Q₂ ⁻¹' {Qs Q₂} := fun _ _ h => by
    rw [← compat _ _ h]
    exact fiber_subset_ofLE _ _
  obtain ⟨x, hx⟩ : Set.Nonempty (⋂ Q, proj Q ⁻¹' {Qs Q}) :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      (fun Q : DiscreteQuotient X => Q.proj ⁻¹' {Qs _}) (directed_of_isDirected_ge H₁)
      (fun Q => (singleton_nonempty _).preimage Q.proj_surjective)
      (fun Q => (Q.isClosed_preimage {Qs _}).isCompact) fun Q => Q.isClosed_preimage _
  exact ⟨x, mem_iInter.1 hx⟩

/-- If `X` is a compact space, then any discrete quotient of `X` is finite. -/
instance [CompactSpace X] : Finite S := by
  have : CompactSpace S := Quotient.compactSpace
  rwa [← isCompact_univ_iff, isCompact_iff_finite, finite_univ_iff] at this

variable (X)

open Classical in
/--
If `X` is a compact space, then we associate to any discrete quotient on `X` a finite set of
clopen subsets of `X`, given by the fibers of `proj`.

TODO: prove that these form a partition of `X`
-/
noncomputable def finsetClopens [CompactSpace X]
    (d : DiscreteQuotient X) : Finset (Clopens X) := have : Fintype d := Fintype.ofFinite _
  (Set.range (fun (x : d) ↦ ⟨_, d.isClopen_preimage {x}⟩) : Set (Clopens X)).toFinset

/-- A helper lemma to prove that `finsetClopens X` is injective, see `finsetClopens_inj`. -/
lemma comp_finsetClopens [CompactSpace X] :
    (Set.image (fun (t : Clopens X) ↦ t.carrier) ∘ (↑)) ∘
      finsetClopens X = fun ⟨f, _⟩ ↦ f.classes := by
  ext d
  simp only [Setoid.classes, Set.mem_setOf_eq, Function.comp_apply,
    finsetClopens, Set.coe_toFinset, Set.mem_image, Set.mem_range,
    exists_exists_eq_and]
  constructor
  · refine fun ⟨y, h⟩ ↦ ⟨Quotient.out (s := d.toSetoid) y, ?_⟩
    ext
    simpa [← h] using Quotient.mk_eq_iff_out (s := d.toSetoid)
  · exact fun ⟨y, h⟩ ↦ ⟨d.proj y, by ext; simp [h, proj]⟩

/-- `finsetClopens X` is injective. -/
theorem finsetClopens_inj [CompactSpace X] :
    (finsetClopens X).Injective := by
  apply Function.Injective.of_comp (f := Set.image (fun (t : Clopens X) ↦ t.carrier) ∘ (↑))
  rw [comp_finsetClopens]
  intro ⟨_, _⟩ ⟨_, _⟩ h
  congr
  rw [Setoid.classes_inj]
  exact h

/--
The discrete quotients of a compact space are in bijection with a subtype of the type of
`Finset (Clopens X)`.

TODO: show that this is precisely those finsets of clopens which form a partition of `X`.
-/
noncomputable
def equivFinsetClopens [CompactSpace X] := Equiv.ofInjective _ (finsetClopens_inj X)

variable {X}

end DiscreteQuotient

namespace LocallyConstant

variable (f : LocallyConstant X α)

/-- Any locally constant function induces a discrete quotient. -/
def discreteQuotient : DiscreteQuotient X where
  toSetoid := .comap f ⊥
  isOpen_setOf_rel _ := f.isLocallyConstant _

/-- The (locally constant) function from the discrete quotient associated to a locally constant
function. -/
def lift : LocallyConstant f.discreteQuotient α :=
  ⟨fun a => Quotient.liftOn' a f fun _ _ => id, fun _ => isOpen_discrete _⟩

@[simp]
theorem lift_comp_proj : f.lift ∘ f.discreteQuotient.proj = f := rfl

end LocallyConstant
