/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import Mathlib.CategoryTheory.Sites.SheafOfTypes
import Mathlib.Order.Closure

#align_import category_theory.sites.closed from "leanprover-community/mathlib"@"4cfc30e317caad46858393f1a7a33f609296cc30"

/-!
# Closed sieves

A natural closure operator on sieves is a closure operator on `Sieve X` for each `X` which commutes
with pullback.
We show that a Grothendieck topology `J` induces a natural closure operator, and define what the
closed sieves are. The collection of `J`-closed sieves forms a presheaf which is a sheaf for `J`,
and further this presheaf can be used to determine the Grothendieck topology from the sheaf
predicate.
Finally we show that a natural closure operator on sieves induces a Grothendieck topology, and hence
that natural closure operators are in bijection with Grothendieck topologies.

## Main definitions

* `CategoryTheory.GrothendieckTopology.close`: Sends a sieve `S` on `X` to the set of arrows
  which it covers. This has all the usual properties of a closure operator, as well as commuting
  with pullback.
* `CategoryTheory.GrothendieckTopology.closureOperator`: The bundled `ClosureOperator` given
  by `CategoryTheory.GrothendieckTopology.close`.
* `CategoryTheory.GrothendieckTopology.IsClosed`: A sieve `S` on `X` is closed for the topology `J`
   if it contains every arrow it covers.
* `CategoryTheory.Functor.closedSieves`: The presheaf sending `X` to the collection of `J`-closed
  sieves on `X`. This is additionally shown to be a sheaf for `J`, and if this is a sheaf for a
  different topology `J'`, then `J' ≤ J`.
* `CategoryTheory.topologyOfClosureOperator`: A closure operator on the
  set of sieves on every object which commutes with pullback additionally induces a Grothendieck
  topology, giving a bijection with `CategoryTheory.GrothendieckTopology.closureOperator`.


## Tags

closed sieve, closure, Grothendieck topology

## References

* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
-/


universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (J₁ J₂ : GrothendieckTopology C)

namespace GrothendieckTopology

/-- The `J`-closure of a sieve is the collection of arrows which it covers. -/
@[simps]
def close {X : C} (S : Sieve X) : Sieve X where
  arrows _ f := J₁.Covers S f
  downward_closed hS := J₁.arrow_stable _ _ hS
#align category_theory.grothendieck_topology.close CategoryTheory.GrothendieckTopology.close

/-- Any sieve is smaller than its closure. -/
theorem le_close {X : C} (S : Sieve X) : S ≤ J₁.close S :=
  fun _ _ hg => J₁.covering_of_eq_top (S.pullback_eq_top_of_mem hg)
#align category_theory.grothendieck_topology.le_close CategoryTheory.GrothendieckTopology.le_close

/-- A sieve is closed for the Grothendieck topology if it contains every arrow it covers.
In the case of the usual topology on a topological space, this means that the open cover contains
every open set which it covers.

Note this has no relation to a closed subset of a topological space.
-/
def IsClosed {X : C} (S : Sieve X) : Prop :=
  ∀ ⦃Y : C⦄ (f : Y ⟶ X), J₁.Covers S f → S f
#align category_theory.grothendieck_topology.is_closed CategoryTheory.GrothendieckTopology.IsClosed

/-- If `S` is `J₁`-closed, then `S` covers exactly the arrows it contains. -/
theorem covers_iff_mem_of_isClosed {X : C} {S : Sieve X} (h : J₁.IsClosed S) {Y : C} (f : Y ⟶ X) :
    J₁.Covers S f ↔ S f :=
  ⟨h _, J₁.arrow_max _ _⟩
#align category_theory.grothendieck_topology.covers_iff_mem_of_closed CategoryTheory.GrothendieckTopology.covers_iff_mem_of_isClosed

/-- Being `J`-closed is stable under pullback. -/
theorem isClosed_pullback {X Y : C} (f : Y ⟶ X) (S : Sieve X) :
    J₁.IsClosed S → J₁.IsClosed (S.pullback f) :=
  fun hS Z g hg => hS (g ≫ f) (by rwa [J₁.covers_iff, Sieve.pullback_comp])
                                  -- 🎉 no goals
#align category_theory.grothendieck_topology.is_closed_pullback CategoryTheory.GrothendieckTopology.isClosed_pullback

/-- The closure of a sieve `S` is the largest closed sieve which contains `S` (justifying the name
"closure").
-/
theorem le_close_of_isClosed {X : C} {S T : Sieve X} (h : S ≤ T) (hT : J₁.IsClosed T) :
    J₁.close S ≤ T :=
  fun _ f hf => hT _ (J₁.superset_covering (Sieve.pullback_monotone f h) hf)
#align category_theory.grothendieck_topology.le_close_of_is_closed CategoryTheory.GrothendieckTopology.le_close_of_isClosed

/-- The closure of a sieve is closed. -/
theorem close_isClosed {X : C} (S : Sieve X) : J₁.IsClosed (J₁.close S) :=
  fun _ g hg => J₁.arrow_trans g _ S hg fun _ hS => hS
#align category_theory.grothendieck_topology.close_is_closed CategoryTheory.GrothendieckTopology.close_isClosed

/-- The sieve `S` is closed iff its closure is equal to itself. -/
theorem isClosed_iff_close_eq_self {X : C} (S : Sieve X) : J₁.IsClosed S ↔ J₁.close S = S := by
  constructor
  -- ⊢ IsClosed J₁ S → close J₁ S = S
  · intro h
    -- ⊢ close J₁ S = S
    apply le_antisymm
    -- ⊢ close J₁ S ≤ S
    · intro Y f hf
      -- ⊢ S.arrows f
      rw [← J₁.covers_iff_mem_of_isClosed h]
      -- ⊢ Covers J₁ S f
      apply hf
      -- 🎉 no goals
    · apply J₁.le_close
      -- 🎉 no goals
  · intro e
    -- ⊢ IsClosed J₁ S
    rw [← e]
    -- ⊢ IsClosed J₁ (close J₁ S)
    apply J₁.close_isClosed
    -- 🎉 no goals
#align category_theory.grothendieck_topology.is_closed_iff_close_eq_self CategoryTheory.GrothendieckTopology.isClosed_iff_close_eq_self

theorem close_eq_self_of_isClosed {X : C} {S : Sieve X} (hS : J₁.IsClosed S) : J₁.close S = S :=
  (J₁.isClosed_iff_close_eq_self S).1 hS
#align category_theory.grothendieck_topology.close_eq_self_of_is_closed CategoryTheory.GrothendieckTopology.close_eq_self_of_isClosed

/-- Closing under `J` is stable under pullback. -/
theorem pullback_close {X Y : C} (f : Y ⟶ X) (S : Sieve X) :
    J₁.close (S.pullback f) = (J₁.close S).pullback f := by
  apply le_antisymm
  -- ⊢ close J₁ (Sieve.pullback f S) ≤ Sieve.pullback f (close J₁ S)
  · refine' J₁.le_close_of_isClosed (Sieve.pullback_monotone _ (J₁.le_close S)) _
    -- ⊢ IsClosed J₁ (Sieve.pullback f (close J₁ S))
    apply J₁.isClosed_pullback _ _ (J₁.close_isClosed _)
    -- 🎉 no goals
  · intro Z g hg
    -- ⊢ (close J₁ (Sieve.pullback f S)).arrows g
    change _ ∈ J₁ _
    -- ⊢ Sieve.pullback g (Sieve.pullback f S) ∈ sieves J₁ Z
    rw [← Sieve.pullback_comp]
    -- ⊢ Sieve.pullback (g ≫ f) S ∈ sieves J₁ Z
    apply hg
    -- 🎉 no goals
#align category_theory.grothendieck_topology.pullback_close CategoryTheory.GrothendieckTopology.pullback_close

@[mono]
theorem monotone_close {X : C} : Monotone (J₁.close : Sieve X → Sieve X) :=
  fun _ S₂ h => J₁.le_close_of_isClosed (h.trans (J₁.le_close _)) (J₁.close_isClosed S₂)
#align category_theory.grothendieck_topology.monotone_close CategoryTheory.GrothendieckTopology.monotone_close

@[simp]
theorem close_close {X : C} (S : Sieve X) : J₁.close (J₁.close S) = J₁.close S :=
  le_antisymm (J₁.le_close_of_isClosed le_rfl (J₁.close_isClosed S))
    (J₁.monotone_close (J₁.le_close _))
#align category_theory.grothendieck_topology.close_close CategoryTheory.GrothendieckTopology.close_close

/--
The sieve `S` is in the topology iff its closure is the maximal sieve. This shows that the closure
operator determines the topology.
-/
theorem close_eq_top_iff_mem {X : C} (S : Sieve X) : J₁.close S = ⊤ ↔ S ∈ J₁ X := by
  constructor
  -- ⊢ close J₁ S = ⊤ → S ∈ sieves J₁ X
  · intro h
    -- ⊢ S ∈ sieves J₁ X
    apply J₁.transitive (J₁.top_mem X)
    -- ⊢ ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, ⊤.arrows f → Sieve.pullback f S ∈ sieves J₁ Y
    intro Y f hf
    -- ⊢ Sieve.pullback f S ∈ sieves J₁ Y
    change J₁.close S f
    -- ⊢ (close J₁ S).arrows f
    rwa [h]
    -- 🎉 no goals
  · intro hS
    -- ⊢ close J₁ S = ⊤
    rw [eq_top_iff]
    -- ⊢ ⊤ ≤ close J₁ S
    intro Y f _
    -- ⊢ (close J₁ S).arrows f
    apply J₁.pullback_stable _ hS
    -- 🎉 no goals
#align category_theory.grothendieck_topology.close_eq_top_iff_mem CategoryTheory.GrothendieckTopology.close_eq_top_iff_mem

/-- A Grothendieck topology induces a natural family of closure operators on sieves. -/
@[simps!]
def closureOperator (X : C) : ClosureOperator (Sieve X) :=
  ClosureOperator.mk' J₁.close
    (fun _ S₂ h => J₁.le_close_of_isClosed (h.trans (J₁.le_close _)) (J₁.close_isClosed S₂))
    J₁.le_close fun S => J₁.le_close_of_isClosed le_rfl (J₁.close_isClosed S)
#align category_theory.grothendieck_topology.closure_operator CategoryTheory.GrothendieckTopology.closureOperator

@[simp]
theorem closed_iff_closed {X : C} (S : Sieve X) :
    S ∈ (J₁.closureOperator X).closed ↔ J₁.IsClosed S :=
  (J₁.isClosed_iff_close_eq_self S).symm
#align category_theory.grothendieck_topology.closed_iff_closed CategoryTheory.GrothendieckTopology.closed_iff_closed

end GrothendieckTopology

/--
The presheaf sending each object to the set of `J`-closed sieves on it. This presheaf is a `J`-sheaf
(and will turn out to be a subobject classifier for the category of `J`-sheaves).
-/
@[simps]
def Functor.closedSieves : Cᵒᵖ ⥤ Type max v u where
  obj X := { S : Sieve X.unop // J₁.IsClosed S }
  map f S := ⟨S.1.pullback f.unop, J₁.isClosed_pullback f.unop _ S.2⟩
#align category_theory.functor.closed_sieves CategoryTheory.Functor.closedSieves

/-- The presheaf of `J`-closed sieves is a `J`-sheaf.
The proof of this is adapted from [MM92], Chapter III, Section 7, Lemma 1.
-/
theorem classifier_isSheaf : Presieve.IsSheaf J₁ (Functor.closedSieves J₁) := by
  intro X S hS
  -- ⊢ Presieve.IsSheafFor (Functor.closedSieves J₁) S.arrows
  rw [← Presieve.isSeparatedFor_and_exists_isAmalgamation_iff_isSheafFor]
  -- ⊢ Presieve.IsSeparatedFor (Functor.closedSieves J₁) S.arrows ∧ ∀ (x : Presieve …
  refine' ⟨_, _⟩
  -- ⊢ Presieve.IsSeparatedFor (Functor.closedSieves J₁) S.arrows
  · rintro x ⟨M, hM⟩ ⟨N, hN⟩ hM₂ hN₂
    -- ⊢ { val := M, property := hM } = { val := N, property := hN }
    simp only [Functor.closedSieves_obj]
    -- ⊢ { val := M, property := hM } = { val := N, property := hN }
    ext Y f
    -- ⊢ (↑{ val := M, property := hM }).arrows f ↔ (↑{ val := N, property := hN }).a …
    dsimp only [Subtype.coe_mk]
    -- ⊢ M.arrows f ↔ N.arrows f
    rw [← J₁.covers_iff_mem_of_isClosed hM, ← J₁.covers_iff_mem_of_isClosed hN]
    -- ⊢ GrothendieckTopology.Covers J₁ M f ↔ GrothendieckTopology.Covers J₁ N f
    have q : ∀ ⦃Z : C⦄ (g : Z ⟶ X) (_ : S g), M.pullback g = N.pullback g :=
      fun Z g hg => congr_arg Subtype.val ((hM₂ g hg).trans (hN₂ g hg).symm)
    have MSNS : M ⊓ S = N ⊓ S := by
      ext Z g
      rw [Sieve.inter_apply, Sieve.inter_apply]
      simp only [and_comm]
      apply and_congr_right
      intro hg
      rw [Sieve.pullback_eq_top_iff_mem, Sieve.pullback_eq_top_iff_mem, q g hg]
    constructor
    -- ⊢ GrothendieckTopology.Covers J₁ M f → GrothendieckTopology.Covers J₁ N f
    · intro hf
      -- ⊢ GrothendieckTopology.Covers J₁ N f
      rw [J₁.covers_iff]
      -- ⊢ Sieve.pullback f N ∈ GrothendieckTopology.sieves J₁ Y
      apply J₁.superset_covering (Sieve.pullback_monotone f inf_le_left)
      -- ⊢ Sieve.pullback f (N ⊓ ?m.20423) ∈ GrothendieckTopology.sieves J₁ Y
      rw [← MSNS]
      -- ⊢ Sieve.pullback f (M ⊓ S) ∈ GrothendieckTopology.sieves J₁ Y
      apply J₁.arrow_intersect f M S hf (J₁.pullback_stable _ hS)
      -- 🎉 no goals
    · intro hf
      -- ⊢ GrothendieckTopology.Covers J₁ M f
      rw [J₁.covers_iff]
      -- ⊢ Sieve.pullback f M ∈ GrothendieckTopology.sieves J₁ Y
      apply J₁.superset_covering (Sieve.pullback_monotone f inf_le_left)
      -- ⊢ Sieve.pullback f (M ⊓ ?m.20633) ∈ GrothendieckTopology.sieves J₁ Y
      rw [MSNS]
      -- ⊢ Sieve.pullback f (N ⊓ S) ∈ GrothendieckTopology.sieves J₁ Y
      apply J₁.arrow_intersect f N S hf (J₁.pullback_stable _ hS)
      -- 🎉 no goals
  · intro x hx
    -- ⊢ ∃ t, Presieve.FamilyOfElements.IsAmalgamation x t
    rw [Presieve.compatible_iff_sieveCompatible] at hx
    -- ⊢ ∃ t, Presieve.FamilyOfElements.IsAmalgamation x t
    let M := Sieve.bind S fun Y f hf => (x f hf).1
    -- ⊢ ∃ t, Presieve.FamilyOfElements.IsAmalgamation x t
    have : ∀ ⦃Y⦄ (f : Y ⟶ X) (hf : S f), M.pullback f = (x f hf).1 := by
      intro Y f hf
      apply le_antisymm
      · rintro Z u ⟨W, g, f', hf', hg : (x f' hf').1 _, c⟩
        rw [Sieve.pullback_eq_top_iff_mem,
          ← show (x (u ≫ f) _).1 = (x f hf).1.pullback u from congr_arg Subtype.val (hx f u hf)]
        conv_lhs => congr; congr; rw [← c] -- Porting note: Originally `simp_rw [← c]`
        rw [show (x (g ≫ f') _).1 = _ from congr_arg Subtype.val (hx f' g hf')]
        apply Sieve.pullback_eq_top_of_mem _ hg
      · apply Sieve.le_pullback_bind S fun Y f hf => (x f hf).1
    refine' ⟨⟨_, J₁.close_isClosed M⟩, _⟩
    -- ⊢ Presieve.FamilyOfElements.IsAmalgamation x { val := GrothendieckTopology.clo …
    · intro Y f hf
      -- ⊢ (Functor.closedSieves J₁).map f.op { val := GrothendieckTopology.close J₁ M, …
      simp only [Functor.closedSieves_obj]
      -- ⊢ (Functor.closedSieves J₁).map f.op { val := GrothendieckTopology.close J₁ (S …
      ext1
      -- ⊢ ↑((Functor.closedSieves J₁).map f.op { val := GrothendieckTopology.close J₁  …
      dsimp
      -- ⊢ Sieve.pullback f (GrothendieckTopology.close J₁ (Sieve.bind S.arrows fun Y f …
      rw [← J₁.pullback_close, this _ hf]
      -- ⊢ GrothendieckTopology.close J₁ ↑(x f hf) = ↑(x f hf)
      apply le_antisymm (J₁.le_close_of_isClosed le_rfl (x f hf).2) (J₁.le_close _)
      -- 🎉 no goals
#align category_theory.classifier_is_sheaf CategoryTheory.classifier_isSheaf

/-- If presheaf of `J₁`-closed sieves is a `J₂`-sheaf then `J₁ ≤ J₂`. Note the converse is true by
`classifier_isSheaf` and `isSheaf_of_le`.
-/
theorem le_topology_of_closedSieves_isSheaf {J₁ J₂ : GrothendieckTopology C}
    (h : Presieve.IsSheaf J₁ (Functor.closedSieves J₂)) : J₁ ≤ J₂ := by
  intro X S hS
  -- ⊢ S ∈ GrothendieckTopology.sieves J₂ X
  rw [← J₂.close_eq_top_iff_mem]
  -- ⊢ GrothendieckTopology.close J₂ S = ⊤
  have : J₂.IsClosed (⊤ : Sieve X) := by
    intro Y f _
    trivial
  suffices (⟨J₂.close S, J₂.close_isClosed S⟩ : Subtype _) = ⟨⊤, this⟩ by
    rw [Subtype.ext_iff] at this
    exact this
  apply (h S hS).isSeparatedFor.ext
  -- ⊢ ∀ ⦃Y : C⦄ ⦃f : Y ⟶ X⦄, S.arrows f → (Functor.closedSieves J₂).map f.op { val …
  · intro Y f hf
    -- ⊢ (Functor.closedSieves J₂).map f.op { val := GrothendieckTopology.close J₂ S, …
    simp only [Functor.closedSieves_obj]
    -- ⊢ (Functor.closedSieves J₂).map f.op { val := GrothendieckTopology.close J₂ S, …
    ext1
    -- ⊢ ↑((Functor.closedSieves J₂).map f.op { val := GrothendieckTopology.close J₂  …
    dsimp
    -- ⊢ Sieve.pullback f (GrothendieckTopology.close J₂ S) = Sieve.pullback f ⊤
    rw [Sieve.pullback_top, ← J₂.pullback_close, S.pullback_eq_top_of_mem hf,
      J₂.close_eq_top_iff_mem]
    apply J₂.top_mem
    -- 🎉 no goals
#align category_theory.le_topology_of_closed_sieves_is_sheaf CategoryTheory.le_topology_of_closedSieves_isSheaf

/-- If being a sheaf for `J₁` is equivalent to being a sheaf for `J₂`, then `J₁ = J₂`. -/
theorem topology_eq_iff_same_sheaves {J₁ J₂ : GrothendieckTopology C} :
    J₁ = J₂ ↔ ∀ P : Cᵒᵖ ⥤ Type max v u, Presieve.IsSheaf J₁ P ↔ Presieve.IsSheaf J₂ P := by
  constructor
  -- ⊢ J₁ = J₂ → ∀ (P : Cᵒᵖ ⥤ Type (max v u)), Presieve.IsSheaf J₁ P ↔ Presieve.IsS …
  · rintro rfl
    -- ⊢ ∀ (P : Cᵒᵖ ⥤ Type (max v u)), Presieve.IsSheaf J₁ P ↔ Presieve.IsSheaf J₁ P
    intro P
    -- ⊢ Presieve.IsSheaf J₁ P ↔ Presieve.IsSheaf J₁ P
    rfl
    -- 🎉 no goals
  · intro h
    -- ⊢ J₁ = J₂
    apply le_antisymm
    -- ⊢ J₁ ≤ J₂
    · apply le_topology_of_closedSieves_isSheaf
      -- ⊢ Presieve.IsSheaf J₁ (Functor.closedSieves J₂)
      rw [h]
      -- ⊢ Presieve.IsSheaf J₂ (Functor.closedSieves J₂)
      apply classifier_isSheaf
      -- 🎉 no goals
    · apply le_topology_of_closedSieves_isSheaf
      -- ⊢ Presieve.IsSheaf J₂ (Functor.closedSieves J₁)
      rw [← h]
      -- ⊢ Presieve.IsSheaf J₁ (Functor.closedSieves J₁)
      apply classifier_isSheaf
      -- 🎉 no goals
#align category_theory.topology_eq_iff_same_sheaves CategoryTheory.topology_eq_iff_same_sheaves

/--
A closure (increasing, inflationary and idempotent) operation on sieves that commutes with pullback
induces a Grothendieck topology.
In fact, such operations are in bijection with Grothendieck topologies.
-/
@[simps]
def topologyOfClosureOperator (c : ∀ X : C, ClosureOperator (Sieve X))
    (hc : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (S : Sieve X), c _ (S.pullback f) = (c _ S).pullback f) :
    GrothendieckTopology C where
  sieves X := { S | c X S = ⊤ }
  top_mem' X := top_unique ((c X).le_closure _)
  pullback_stable' X Y S f hS := by
    rw [Set.mem_setOf_eq] at hS
    -- ⊢ Sieve.pullback f S ∈ (fun X => {S | ↑(c X) S = ⊤}) Y
    rw [Set.mem_setOf_eq, hc, hS, Sieve.pullback_top]
    -- 🎉 no goals
  transitive' X S hS R hR := by
    rw [Set.mem_setOf_eq] at hS
    -- ⊢ R ∈ (fun X => {S | ↑(c X) S = ⊤}) X
    rw [Set.mem_setOf_eq, ← (c X).idempotent, eq_top_iff, ← hS]
    -- ⊢ ↑(c X) S ≤ ↑(c X) (↑(c X) R)
    apply (c X).monotone fun Y f hf => _
    -- ⊢ ∀ (Y : C) (f : Y ⟶ X), S.arrows f → (↑(c X) R).arrows f
    intros Y f hf
    -- ⊢ (↑(c X) R).arrows f
    rw [Sieve.pullback_eq_top_iff_mem, ← hc]
    -- ⊢ ↑(c Y) (Sieve.pullback f R) = ⊤
    apply hR hf
    -- 🎉 no goals
#align category_theory.topology_of_closure_operator CategoryTheory.topologyOfClosureOperator

/--
The topology given by the closure operator `J.close` on a Grothendieck topology is the same as `J`.
-/
theorem topologyOfClosureOperator_self :
    (topologyOfClosureOperator J₁.closureOperator fun X Y => J₁.pullback_close) = J₁ := by
  ext X S
  -- ⊢ S ∈ GrothendieckTopology.sieves (topologyOfClosureOperator (GrothendieckTopo …
  apply GrothendieckTopology.close_eq_top_iff_mem
  -- 🎉 no goals
#align category_theory.topology_of_closure_operator_self CategoryTheory.topologyOfClosureOperator_self

theorem topologyOfClosureOperator_close (c : ∀ X : C, ClosureOperator (Sieve X))
    (pb : ∀ ⦃X Y : C⦄ (f : Y ⟶ X) (S : Sieve X), c Y (S.pullback f) = (c X S).pullback f) (X : C)
    (S : Sieve X) : (topologyOfClosureOperator c pb).close S = c X S := by
  ext Y f
  -- ⊢ (GrothendieckTopology.close (topologyOfClosureOperator c pb) S).arrows f ↔ ( …
  change c _ (Sieve.pullback f S) = ⊤ ↔ c _ S f
  -- ⊢ ↑(c Y) (Sieve.pullback f S) = ⊤ ↔ (↑(c X) S).arrows f
  rw [pb, Sieve.pullback_eq_top_iff_mem]
  -- 🎉 no goals
#align category_theory.topology_of_closure_operator_close CategoryTheory.topologyOfClosureOperator_close

end CategoryTheory
