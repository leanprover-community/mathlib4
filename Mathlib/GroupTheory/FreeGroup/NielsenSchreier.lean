/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import Mathlib.CategoryTheory.Action
import Mathlib.Combinatorics.Quiver.Arborescence
import Mathlib.Combinatorics.Quiver.ConnectedComponent
import Mathlib.GroupTheory.FreeGroup.IsFreeGroup

/-!
# The Nielsen-Schreier theorem

This file proves that a subgroup of a free group is itself free.

## Main result

- `subgroupIsFreeOfIsFree H`: an instance saying that a subgroup of a free group is free.

## Proof overview

The proof is analogous to the proof using covering spaces and fundamental groups of graphs,
but we work directly with groupoids instead of topological spaces. Under this analogy,

- `IsFreeGroupoid G` corresponds to saying that a space is a graph.
- `endMulEquivSubgroup H` plays the role of replacing 'subgroup of fundamental group' with
  'fundamental group of covering space'.
- `actionGroupoidIsFree G A` corresponds to the fact that a covering of a (single-vertex)
  graph is a graph.
- `endIsFree T` corresponds to the fact that, given a spanning tree `T` of a
  graph, its fundamental group is free (generated by loops from the complement of the tree).

## Implementation notes

Our definition of `IsFreeGroupoid` is nonstandard. Normally one would require that functors
`G ⥤ X` to any _groupoid_ `X` are given by graph homomorphisms from the generators, but we only
consider _groups_ `X`. This simplifies the argument since functor equality is complicated in
general, but simple for functors to single object categories.

## References

https://ncatlab.org/nlab/show/Nielsen-Schreier+theorem

## Tags

free group, free groupoid, Nielsen-Schreier

-/


noncomputable section

open scoped Classical

universe v u

/- Porting note: ./././Mathport/Syntax/Translate/Command.lean:229:11:unsupported:
unusual advanced open style -/
open CategoryTheory CategoryTheory.ActionCategory CategoryTheory.SingleObj Quiver FreeGroup

/-- `IsFreeGroupoid.Generators G` is a type synonym for `G`. We think of this as
the vertices of the generating quiver of `G` when `G` is free. We can't use `G` directly,
since `G` already has a quiver instance from being a groupoid. -/
-- Porting note(#5171): @[nolint has_nonempty_instance]
@[nolint unusedArguments]
def IsFreeGroupoid.Generators (G) [Groupoid G] :=
  G

/-- A groupoid `G` is free when we have the following data:
 - a quiver on `IsFreeGroupoid.Generators G` (a type synonym for `G`)
 - a function `of` taking a generating arrow to a morphism in `G`
 - such that a functor from `G` to any group `X` is uniquely determined
   by assigning labels in `X` to the generating arrows.

   This definition is nonstandard. Normally one would require that functors `G ⥤ X`
   to any _groupoid_ `X` are given by graph homomorphisms from `generators`. -/
class IsFreeGroupoid (G) [Groupoid.{v} G] where
  quiverGenerators : Quiver.{v + 1} (IsFreeGroupoid.Generators G)
  of : ∀ {a b : IsFreeGroupoid.Generators G}, (a ⟶ b) → ((show G from a) ⟶ b)
  unique_lift :
    ∀ {X : Type v} [Group X] (f : Labelling (IsFreeGroupoid.Generators G) X),
      ∃! F : G ⥤ CategoryTheory.SingleObj X, ∀ (a b) (g : a ⟶ b), F.map (of g) = f g

attribute [nolint docBlame] IsFreeGroupoid.of IsFreeGroupoid.unique_lift

namespace IsFreeGroupoid

attribute [instance] quiverGenerators

/-- Two functors from a free groupoid to a group are equal when they agree on the generating
quiver. -/
@[ext]
theorem ext_functor {G} [Groupoid.{v} G] [IsFreeGroupoid G] {X : Type v} [Group X]
    (f g : G ⥤ CategoryTheory.SingleObj X) (h : ∀ (a b) (e : a ⟶ b), f.map (of e) = g.map (of e)) :
    f = g :=
  let ⟨_, _, u⟩ := @unique_lift G _ _ X _ fun (a b : Generators G) (e : a ⟶ b) => g.map (of e)
  _root_.trans (u _ h) (u _ fun _ _ _ => rfl).symm

/-- An action groupoid over a free group is free. More generally, one could show that the groupoid
of elements over a free groupoid is free, but this version is easier to prove and suffices for our
purposes.

Analogous to the fact that a covering space of a graph is a graph. (A free groupoid is like a graph,
and a groupoid of elements is like a covering space.) -/
instance actionGroupoidIsFree {G A : Type u} [Group G] [IsFreeGroup G] [MulAction G A] :
    IsFreeGroupoid (ActionCategory G A) where
  quiverGenerators :=
    ⟨fun a b => { e : IsFreeGroup.Generators G // IsFreeGroup.of e • a.back = b.back }⟩
  of := fun (e : { e // _}) => ⟨IsFreeGroup.of e, e.property⟩
  unique_lift := by
    intro X _ f
    let f' : IsFreeGroup.Generators G → (A → X) ⋊[mulAutArrow] G := fun e =>
      ⟨fun b => @f ⟨(), _⟩ ⟨(), b⟩ ⟨e, smul_inv_smul _ b⟩, IsFreeGroup.of e⟩
    rcases IsFreeGroup.unique_lift f' with ⟨F', hF', uF'⟩
    refine ⟨uncurry F' ?_, ?_, ?_⟩
    · suffices SemidirectProduct.rightHom.comp F' = MonoidHom.id _ by
        -- Porting note: `MonoidHom.ext_iff` has been deprecated.
        exact DFunLike.ext_iff.mp this
      apply IsFreeGroup.ext_hom (fun x ↦ ?_)
      rw [MonoidHom.comp_apply, hF']
      rfl
    · rintro ⟨⟨⟩, a : A⟩ ⟨⟨⟩, b⟩ ⟨e, h : IsFreeGroup.of e • a = b⟩
      change (F' (IsFreeGroup.of _)).left _ = _
      rw [hF']
      cases inv_smul_eq_iff.mpr h.symm
      rfl
    · intro E hE
      have : curry E = F' := by
        apply uF'
        intro e
        ext
        · convert hE _ _ _
          rfl
        · rfl
      apply Functor.hext
      · intro
        apply Unit.ext
      · refine ActionCategory.cases ?_
        intros
        simp only [← this, uncurry_map, curry_apply_left, coe_back, homOfPair.val]
        rfl

namespace SpanningTree

/- In this section, we suppose we have a free groupoid with a spanning tree for its generating
quiver. The goal is to prove that the vertex group at the root is free. A picture to have in mind
is that we are 'pulling' the endpoints of all the edges of the quiver along the spanning tree to
the root. -/
variable {G : Type u} [Groupoid.{u} G] [IsFreeGroupoid G]
  (T : WideSubquiver (Symmetrify <| Generators G)) [Arborescence T]

/-- The root of `T`, except its type is `G` instead of the type synonym `T`. -/
private def root' : G :=
  show T from root T
-- #align is_free_groupoid.spanning_tree.root' IsFreeGroupoid.SpanningTree.root'

-- this has to be marked noncomputable, see issue #451.
-- It might be nicer to define this in terms of `composePath`
/-- A path in the tree gives a hom, by composition. -/
-- Porting note: removed noncomputable. This is already declared at the beginning of the section.
def homOfPath : ∀ {a : G}, Path (root T) a → (root' T ⟶ a)
  | _, Path.nil => 𝟙 _
  | _, Path.cons p f => homOfPath p ≫ Sum.recOn f.val (fun e => of e) fun e => inv (of e)

/-- For every vertex `a`, there is a canonical hom from the root, given by the path in the tree. -/
def treeHom (a : G) : root' T ⟶ a :=
  homOfPath T default

/-- Any path to `a` gives `treeHom T a`, since paths in the tree are unique. -/
theorem treeHom_eq {a : G} (p : Path (root T) a) : treeHom T a = homOfPath T p := by
  rw [treeHom, Unique.default_eq]

@[simp]
theorem treeHom_root : treeHom T (root' T) = 𝟙 _ :=
  -- this should just be `treeHom_eq T Path.nil`, but Lean treats `homOfPath` with suspicion.
    _root_.trans
    (treeHom_eq T Path.nil) rfl

/-- Any hom in `G` can be made into a loop, by conjugating with `treeHom`s. -/
def loopOfHom {a b : G} (p : a ⟶ b) : End (root' T) :=
  treeHom T a ≫ p ≫ inv (treeHom T b)

/-- Turning an edge in the spanning tree into a loop gives the identity loop. -/
theorem loopOfHom_eq_id {a b : Generators G} (e) (H : e ∈ wideSubquiverSymmetrify T a b) :
    loopOfHom T (of e) = 𝟙 (root' T) := by
  rw [loopOfHom, ← Category.assoc, IsIso.comp_inv_eq, Category.id_comp]
  cases' H with H H
  · rw [treeHom_eq T (Path.cons default ⟨Sum.inl e, H⟩), homOfPath]
    rfl
  · rw [treeHom_eq T (Path.cons default ⟨Sum.inr e, H⟩), homOfPath]
    simp only [IsIso.inv_hom_id, Category.comp_id, Category.assoc, treeHom]

/-- Since a hom gives a loop, any homomorphism from the vertex group at the root
    extends to a functor on the whole groupoid. -/
@[simps]
def functorOfMonoidHom {X} [Monoid X] (f : End (root' T) →* X) :
    G ⥤ CategoryTheory.SingleObj X where
  obj _ := ()
  map p := f (loopOfHom T p)
  map_id := by
    intro a
    dsimp only [loopOfHom]
    rw [Category.id_comp, IsIso.hom_inv_id, ← End.one_def, f.map_one, id_as_one]
  map_comp := by
    intros
    rw [comp_as_mul, ← f.map_mul]
    simp only [IsIso.inv_hom_id_assoc, loopOfHom, End.mul_def, Category.assoc]

/-- Given a free groupoid and an arborescence of its generating quiver, the vertex
    group at the root is freely generated by loops coming from generating arrows
    in the complement of the tree. -/
lemma endIsFree : IsFreeGroup (End (root' T)) :=
  IsFreeGroup.ofUniqueLift ((wideSubquiverEquivSetTotal <| wideSubquiverSymmetrify T)ᶜ : Set _)
    (fun e => loopOfHom T (of e.val.hom))
    (by
      intro X _ f
      let f' : Labelling (Generators G) X := fun a b e =>
        if h : e ∈ wideSubquiverSymmetrify T a b then 1 else f ⟨⟨a, b, e⟩, h⟩
      rcases unique_lift f' with ⟨F', hF', uF'⟩
      refine ⟨F'.mapEnd _, ?_, ?_⟩
      · suffices ∀ {x y} (q : x ⟶ y), F'.map (loopOfHom T q) = (F'.map q : X) by
          rintro ⟨⟨a, b, e⟩, h⟩
          erw [Functor.mapEnd_apply, this, hF']
          exact dif_neg h
        intros x y q
        suffices ∀ {a} (p : Path (root T) a), F'.map (homOfPath T p) = 1 by
          simp only [this, treeHom, comp_as_mul, inv_as_inv, loopOfHom, inv_one, mul_one,
            one_mul, Functor.map_inv, Functor.map_comp]
        intro a p
        induction' p with b c p e ih
        · rw [homOfPath, F'.map_id, id_as_one]
        rw [homOfPath, F'.map_comp, comp_as_mul, ih, mul_one]
        rcases e with ⟨e | e, eT⟩
        · rw [hF']
          exact dif_pos (Or.inl eT)
        · rw [F'.map_inv, inv_as_inv, inv_eq_one, hF']
          exact dif_pos (Or.inr eT)
      · intro E hE
        ext x
        suffices (functorOfMonoidHom T E).map x = F'.map x by
          simpa only [loopOfHom, functorOfMonoidHom, IsIso.inv_id, treeHom_root,
            Category.id_comp, Category.comp_id] using this
        congr
        apply uF'
        intro a b e
        change E (loopOfHom T _) = dite _ _ _
        split_ifs with h
        · rw [loopOfHom_eq_id T e h, ← End.one_def, E.map_one]
        · exact hE ⟨⟨a, b, e⟩, h⟩)

end SpanningTree

/-- Another name for the identity function `G → G`, to help type checking. -/
private def symgen {G : Type u} [Groupoid.{v} G] [IsFreeGroupoid G] :
    G → Symmetrify (Generators G) :=
  id
-- #align is_free_groupoid.symgen IsFreeGroupoid.symgen

/-- If there exists a morphism `a → b` in a free groupoid, then there also exists a zigzag
from `a` to `b` in the generating quiver. -/
theorem path_nonempty_of_hom {G} [Groupoid.{u, u} G] [IsFreeGroupoid G] {a b : G} :
    Nonempty (a ⟶ b) → Nonempty (Path (symgen a) (symgen b)) := by
  rintro ⟨p⟩
  rw [← @WeaklyConnectedComponent.eq (Generators G), eq_comm, ← FreeGroup.of_injective.eq_iff, ←
    mul_inv_eq_one]
  let X := FreeGroup (WeaklyConnectedComponent <| Generators G)
  let f : G → X := fun g => FreeGroup.of (WeaklyConnectedComponent.mk g)
  let F : G ⥤ CategoryTheory.SingleObj.{u} (X : Type u) := SingleObj.differenceFunctor f
  change (F.map p) = ((@CategoryTheory.Functor.const G _ _ (SingleObj.category X)).obj ()).map p
  congr; ext
  rw [Functor.const_obj_map, id_as_one, differenceFunctor_map, @mul_inv_eq_one _ _ (f _)]
  apply congr_arg FreeGroup.of
  apply (WeaklyConnectedComponent.eq _ _).mpr
  exact ⟨Hom.toPath (Sum.inr (by assumption))⟩

/-- Given a connected free groupoid, its generating quiver is rooted-connected. -/
instance generators_connected (G) [Groupoid.{u, u} G] [IsConnected G] [IsFreeGroupoid G] (r : G) :
    RootedConnected (symgen r) :=
  ⟨fun b => path_nonempty_of_hom (CategoryTheory.nonempty_hom_of_preconnected_groupoid r b)⟩

/-- A vertex group in a free connected groupoid is free. With some work one could drop the
connectedness assumption, by looking at connected components. -/
instance endIsFreeOfConnectedFree
    {G : Type u} [Groupoid G] [IsConnected G] [IsFreeGroupoid G] (r : G) :
    IsFreeGroup.{u} (End r) :=
  SpanningTree.endIsFree <| geodesicSubtree (symgen r)

end IsFreeGroupoid

/-- The Nielsen-Schreier theorem: a subgroup of a free group is free. -/
instance subgroupIsFreeOfIsFree {G : Type u} [Group G] [IsFreeGroup G] (H : Subgroup G) :
    IsFreeGroup H :=
  IsFreeGroup.ofMulEquiv (endMulEquivSubgroup H)
