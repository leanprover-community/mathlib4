/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala, Yury Kudryashov
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Product
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Operations
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.CategoryTheory.Slice
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Homotopic maps induce naturally isomorphic functors

## Main definitions

- `FundamentalGroupoidFunctor.homotopicMapsNatIso H` The natural isomorphism
  between the induced functors `f : π(X) ⥤ π(Y)` and `g : π(X) ⥤ π(Y)`, given a homotopy
  `H : f ∼ g`

- `FundamentalGroupoidFunctor.equivOfHomotopyEquiv hequiv` The equivalence of the categories
  `π(X)` and `π(Y)` given a homotopy equivalence `hequiv : X ≃ₕ Y` between them.
-/

@[expose] public section

noncomputable section

universe u v

open FundamentalGroupoid CategoryTheory FundamentalGroupoidFunctor
open scoped FundamentalGroupoid unitInterval

set_option backward.isDefEq.respectTransparency false in
/-- Let `F` be a homotopy between two continuous maps `f g : C(X, Y)`.
Given a path `p : Path x₁ x₂` in the domain, consider the following two paths in the codomain.
One path goes along the image of `p` under `f`, then along the trajectory of `x₂` under `F`.
The other path goes along the trajectory of `x₁` under `F`, then along the image of `p` under `g`.

These two paths are homotopic. -/
theorem Path.Homotopic.map_trans_evalAt {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (F : f.Homotopy g) {x₁ x₂ : X} (p : Path x₁ x₂) :
    ((p.map (map_continuous f)).trans (F.evalAt x₂)).Homotopic
      ((F.evalAt x₁).trans (p.map (map_continuous g))) := by
  /- Let `G` be the continuous map on the unit square sending `(t, s)` to `F(t, p(s))`.
  Then our homotopy is the image under `G` of a homotopy
  between the two paths from `(0, 0)` to `(1, 1)` along the sides of the square. -/
  set G : C(I × I, Y) := F.toContinuousMap.comp (.prodMap (.id _) p)
  set p₁ : Path ((0, 0) : I × I) (1, 1) := .prod (.trans (.refl _) .id) (.trans .id (.refl _))
  set p₂ : Path ((0, 0) : I × I) (1, 1) := .prod (.trans .id (.refl _)) (.trans (.refl _) .id)
  set Fsq : p₁.Homotopy p₂ :=
    Path.Homotopic.prodHomotopy (.trans (.reflTrans _) (.symm <| .transRefl _))
      (.trans (.transRefl _) (.symm <| .reflTrans _))
  refine ⟨((Fsq.map G).pathCast ?H0 ?H1).cast ?hp ?hq⟩
  all_goals aesop (add simp Path.trans_apply)

namespace FundamentalGroupoidFunctor

open CategoryTheory
open scoped FundamentalGroupoid ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  {f g : C(X, Y)}

set_option backward.isDefEq.respectTransparency false in
set_option pp.proofs.withType true in
/-- Given a homotopy H : f ∼ g, we have an associated natural isomorphism between the induced
functors `map f` and `map g` on fundamental groupoids. -/
def homotopicMapsNatIso (H : ContinuousMap.Homotopy f g) : map f ⟶ map g where
  app x := ⟦H.evalAt x.as⟧
  naturality := by
    rintro ⟨x⟩ ⟨y⟩ p
    rcases Path.Homotopic.Quotient.mk_surjective p with ⟨p, rfl⟩
    simp only [map_map, map_obj_as, Path.Homotopic.Quotient.mk''_eq_mk, comp_eq,
      ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_trans]
    rw [Path.Homotopic.Quotient.eq]
    exact .map_trans_evalAt _ _

instance (H : ContinuousMap.Homotopy f g) : IsIso (homotopicMapsNatIso H) :=
  NatIso.isIso_of_isIso_app _

open scoped ContinuousMap

/-- Homotopy equivalent topological spaces have equivalent fundamental groupoids. -/
def equivOfHomotopyEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (hequiv : X ≃ₕ Y) :
    πₓ (.of X) ≌ πₓ (.of Y) := by
  apply CategoryTheory.Equivalence.mk (map hequiv.toFun) (map hequiv.invFun)
  · simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
      using (asIso (homotopicMapsNatIso hequiv.left_inv.some)).symm
  · simpa only [FundamentalGroupoid.map_id, FundamentalGroupoid.map_comp]
      using asIso (homotopicMapsNatIso hequiv.right_inv.some)

end FundamentalGroupoidFunctor

/-!
### Old proof

The rest of the file contains definitions and theorems required to write the same proof
in a slightly different manner.

The proof was rewritten in 2025 for two reasons:

- the new proof is much more straightforward;
- the new proof is fully universe polymorphic.

TODO: review which of these definitions and theorems are useful for other reasons,
then deprecate the rest of them.
-/

namespace unitInterval

/-- The path 0 ⟶ 1 in `I` -/
def path01 : Path (0 : I) 1 where
  toFun := id
  source' := rfl
  target' := rfl

/-- The path 0 ⟶ 1 in `ULift I` -/
def upath01 : Path (ULift.up 0 : ULift.{u} I) (ULift.up 1) where
  toFun := ULift.up
  source' := rfl
  target' := rfl

/-- The homotopy path class of 0 → 1 in `ULift I` -/
def uhpath01 : @fromTop (TopCat.of <| ULift.{u} I) (ULift.up (0 : I)) ⟶ fromTop (ULift.up 1) :=
  ⟦upath01⟧

end unitInterval

namespace ContinuousMap.Homotopy

open unitInterval (uhpath01)

section Casts

/-- Abbreviation for `eqToHom` that accepts points in a topological space -/
abbrev hcast {X : TopCat} {x₀ x₁ : X} (hx : x₀ = x₁) : fromTop x₀ ⟶ fromTop x₁ :=
  eqToHom <| FundamentalGroupoid.ext hx

@[simp]
theorem hcast_def {X : TopCat} {x₀ x₁ : X} (hx₀ : x₀ = x₁) :
    hcast hx₀ = eqToHom (FundamentalGroupoid.ext hx₀) :=
  rfl

variable {X₁ X₂ Y : TopCat.{u}} {f : C(X₁, Y)} {g : C(X₂, Y)} {x₀ x₁ : X₁} {x₂ x₃ : X₂}
  {p : Path x₀ x₁} {q : Path x₂ x₃} (hfg : ∀ t, f (p t) = g (q t))
include hfg

/-- If `f(p(t) = g(q(t))` for two paths `p` and `q`, then the induced path homotopy classes
`f(p)` and `g(p)` are the same as well, despite having a priori different types -/
theorem heq_path_of_eq_image :
    (πₘ (TopCat.ofHom f)).map ⟦p⟧ ≍ (πₘ (TopCat.ofHom g)).map ⟦q⟧ := by
  simp only [map_eq]
  apply Path.Homotopic.hpath_hext
  exact hfg

set_option backward.privateInPublic true in
private theorem start_path : f x₀ = g x₂ := by convert hfg 0 <;> simp only [Path.source]

set_option backward.privateInPublic true in
private theorem end_path : f x₁ = g x₃ := by convert hfg 1 <;> simp only [Path.target]

set_option backward.isDefEq.respectTransparency false in
set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
theorem eq_path_of_eq_image :
    (πₘ (TopCat.ofHom f)).map ⟦p⟧ =
        hcast (start_path hfg) ≫ (πₘ (TopCat.ofHom g)).map ⟦q⟧ ≫ hcast (end_path hfg).symm := by
  rw [conj_eqToHom_iff_heq
    ((πₘ (TopCat.ofHom f)).map ⟦p⟧) ((πₘ (TopCat.ofHom g)).map ⟦q⟧)
    (FundamentalGroupoid.ext <| start_path hfg)
    (FundamentalGroupoid.ext <| end_path hfg)]
  exact heq_path_of_eq_image hfg

end Casts

-- We let `X` and `Y` be spaces, and `f` and `g` be homotopic maps between them
variable {X Y : TopCat.{u}} {f g : C(X, Y)} (H : ContinuousMap.Homotopy f g) {x₀ x₁ : X}
  (p : fromTop x₀ ⟶ fromTop x₁)

/-!
These definitions set up the following diagram, for each path `p`:

```
            f(p)
        *--------*
        | \      |
    H₀  |   \ d  |  H₁
        |     \  |
        *--------*
            g(p)
```

Here, `H₀ = H.evalAt x₀` is the path from `f(x₀)` to `g(x₀)`,
and similarly for `H₁`. Similarly, `f(p)` denotes the
path in Y that the induced map `f` takes `p`, and similarly for `g(p)`.

Finally, `d`, the diagonal path, is H(0 ⟶ 1, p), the result of the induced `H` on
`Path.Homotopic.prod (0 ⟶ 1) p`, where `(0 ⟶ 1)` denotes the path from `0` to `1` in `I`.

It is clear that the diagram commutes (`H₀ ≫ g(p) = d = f(p) ≫ H₁`), but unfortunately,
many of the paths do not have defeq starting/ending points, so we end up needing some casting.
-/


/-- Interpret a homotopy `H : C(I × X, Y)` as a map `C(ULift I × X, Y)` -/
def uliftMap : C(TopCat.of (ULift.{u} I × X), Y) :=
  ⟨fun x => H (x.1.down, x.2),
    H.continuous.comp ((continuous_uliftDown.comp continuous_fst).prodMk continuous_snd)⟩

theorem ulift_apply (i : ULift.{u} I) (x : X) : H.uliftMap (i, x) = H (i.down, x) :=
  rfl

/-- An abbreviation for `prodToProdTop`, with some types already in place to help the
typechecker. In particular, the first path should be on the ulifted unit interval. -/
abbrev prodToProdTopI {a₁ a₂ : TopCat.of (ULift I)} {b₁ b₂ : X} (p₁ : fromTop a₁ ⟶ fromTop a₂)
    (p₂ : fromTop b₁ ⟶ fromTop b₂) :=
  (prodToProdTop (TopCat.of <| ULift I) X).map (X := (⟨a₁⟩, ⟨b₁⟩)) (Y := (⟨a₂⟩, ⟨b₂⟩)) (p₁, p₂)

/-- The diagonal path `d` of a homotopy `H` on a path `p` -/
def diagonalPath : fromTop (H (0, x₀)) ⟶ fromTop (H (1, x₁)) :=
  (πₘ (TopCat.ofHom H.uliftMap)).map (prodToProdTopI uhpath01 p)

/-- The diagonal path, but starting from `f x₀` and going to `g x₁` -/
def diagonalPath' : fromTop (f x₀) ⟶ fromTop (g x₁) :=
  hcast (H.apply_zero x₀).symm ≫ H.diagonalPath p ≫ hcast (H.apply_one x₁)

/-- Proof that `f(p) = H(0 ⟶ 0, p)`, with the appropriate casts -/
theorem apply_zero_path : (πₘ (TopCat.ofHom f)).map p = hcast (H.apply_zero x₀).symm ≫
    (πₘ (TopCat.ofHom H.uliftMap)).map
      (prodToProdTopI (𝟙 (@fromTop (TopCat.of _) (ULift.up 0))) p) ≫
    hcast (H.apply_zero x₁) :=
  Quotient.inductionOn p fun p' => by
    apply @eq_path_of_eq_image _ _ _ _ H.uliftMap _ _ _ _ _ ((Path.refl (ULift.up _)).prod p')
    intros
    rw [Path.prod_coe, ulift_apply H]
    simp

/-- Proof that `g(p) = H(1 ⟶ 1, p)`, with the appropriate casts -/
theorem apply_one_path : (πₘ (TopCat.ofHom g)).map p = hcast (H.apply_one x₀).symm ≫
    (πₘ (TopCat.ofHom H.uliftMap)).map
      (prodToProdTopI (𝟙 (@fromTop (TopCat.of _) (ULift.up 1))) p) ≫
    hcast (H.apply_one x₁) :=
  Quotient.inductionOn p fun p' => by
    apply @eq_path_of_eq_image _ _ _ _ H.uliftMap _ _ _ _ _ ((Path.refl (ULift.up _)).prod p')
    intros
    rw [Path.prod_coe, ulift_apply H]
    simp

set_option backward.isDefEq.respectTransparency false in
/-- Proof that `H.evalAt x = H(0 ⟶ 1, x ⟶ x)`, with the appropriate casts -/
theorem evalAt_eq (x : X) : ⟦H.evalAt x⟧ = hcast (H.apply_zero x).symm ≫
    (πₘ (TopCat.ofHom H.uliftMap)).map (prodToProdTopI uhpath01 (𝟙 (fromTop x))) ≫
      hcast (H.apply_one x).symm.symm := by
  dsimp only [prodToProdTopI, uhpath01, hcast]
  refine (@conj_eqToHom_iff_heq (πₓ Y) _ _ _ _ _ _ _ _
    (FundamentalGroupoid.ext <| H.apply_one x).symm).mpr ?_
  simp only [map_eq]
  apply Path.Homotopic.hpath_hext; intro; rfl

set_option backward.isDefEq.respectTransparency false in
-- Finally, we show `d = f(p) ≫ H₁ = H₀ ≫ g(p)`
theorem eq_diag_path : (πₘ (TopCat.ofHom f)).map p ≫ ⟦H.evalAt x₁⟧ = H.diagonalPath' p ∧
    (⟦H.evalAt x₀⟧ ≫ (πₘ (TopCat.ofHom g)).map p :
    fromTop (f x₀) ⟶ fromTop (g x₁)) = H.diagonalPath' p := by
  rw [H.apply_zero_path, H.apply_one_path, H.evalAt_eq]
  erw [H.evalAt_eq]
  dsimp only [prodToProdTopI]
  constructor
  · slice_lhs 2 4 => rw [eqToHom_trans, eqToHom_refl] -- Porting note: this ↓ `simp` didn't do this
    slice_lhs 2 4 => simp [← CategoryTheory.Functor.map_comp]
    rfl
  · slice_lhs 2 4 => rw [eqToHom_trans, eqToHom_refl] -- Porting note: this ↓ `simp` didn't do this
    slice_lhs 2 4 => simp [← CategoryTheory.Functor.map_comp]
    rfl

end ContinuousMap.Homotopy
