/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Group.Action.Pi
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.RepresentationTheory.Action.Basic

/-!
# Constructors for `Action V G` for some concrete categories

We construct `Action (Type u) G` from a `[MulAction G X]` instance and give some applications.
-/

universe u v

open CategoryTheory Limits

namespace Action

/-- Bundles a type `H` with a multiplicative action of `G` as an `Action`. -/
def ofMulAction (G H : Type u) [Monoid G] [MulAction G H] : Action (Type u) (MonCat.of G) where
  V := H
  ρ := @MulAction.toEndHom _ _ _ (by assumption)

@[simp]
theorem ofMulAction_apply {G H : Type u} [Monoid G] [MulAction G H] (g : G) (x : H) :
    (ofMulAction G H).ρ g x = (g • x : H) :=
  rfl

/-- Given a family `F` of types with `G`-actions, this is the limit cone demonstrating that the
product of `F` as types is a product in the category of `G`-sets. -/
def ofMulActionLimitCone {ι : Type v} (G : Type max v u) [Monoid G] (F : ι → Type max v u)
    [∀ i : ι, MulAction G (F i)] :
    LimitCone (Discrete.functor fun i : ι => Action.ofMulAction G (F i)) where
  cone :=
    { pt := Action.ofMulAction G (∀ i : ι, F i)
      π := Discrete.natTrans (fun i => ⟨fun x => x i.as, fun g => rfl⟩) }
  isLimit :=
    { lift := fun s =>
        { hom := fun x i => (s.π.app ⟨i⟩).hom x
          comm := fun g => by
            ext x
            funext j
            exact congr_fun ((s.π.app ⟨j⟩).comm g) x }
      fac := fun s j => rfl
      uniq := fun s f h => by
        ext x
        funext j
        dsimp at *
        rw [← h ⟨j⟩]
        rfl }

/-- The `G`-set `G`, acting on itself by left multiplication. -/
@[simps!]
def leftRegular (G : Type u) [Monoid G] : Action (Type u) (MonCat.of G) :=
  Action.ofMulAction G G

/-- The `G`-set `Gⁿ`, acting on itself by left multiplication. -/
@[simps!]
def diagonal (G : Type u) [Monoid G] (n : ℕ) : Action (Type u) (MonCat.of G) :=
  Action.ofMulAction G (Fin n → G)

/-- We have `Fin 1 → G ≅ G` as `G`-sets, with `G` acting by left multiplication. -/
def diagonalOneIsoLeftRegular (G : Type u) [Monoid G] : diagonal G 1 ≅ leftRegular G :=
  Action.mkIso (Equiv.funUnique _ _).toIso fun _ => rfl

namespace FintypeCat

/-- If `X` is a type with `[Fintype X]` and `G` acts on `X`, then `G` also acts on
`FintypeCat.of X`. -/
instance (G : Type*) (X : Type*) [Monoid G] [MulAction G X] [Fintype X] :
    MulAction G (FintypeCat.of X) :=
  inferInstanceAs <| MulAction G X

/-- Bundles a finite type `H` with a multiplicative action of `G` as an `Action`. -/
def ofMulAction (G : Type u) (H : FintypeCat.{u}) [Monoid G] [MulAction G H] :
    Action FintypeCat (MonCat.of G) where
  V := H
  ρ := @MulAction.toEndHom _ _ _ (by assumption)

@[simp]
theorem ofMulAction_apply {G : Type u} {H : FintypeCat.{u}} [Monoid G] [MulAction G H]
    (g : G) (x : H) : (FintypeCat.ofMulAction G H).ρ g x = (g • x : H) :=
  rfl

section

/-- Shorthand notation for the quotient of `G` by `H` as a finite `G`-set. -/
notation:10 G:10 " ⧸ₐ " H:10 => Action.FintypeCat.ofMulAction G (FintypeCat.of <| G ⧸ H)

variable {G : Type*} [Group G] (H N : Subgroup G) [Fintype (G ⧸ N)]

/-- If `N` is a normal subgroup of `G`, then this is the group homomorphism
sending an element `g` of `G` to the `G`-endomorphism of `G ⧸ₐ N` given by
multiplication with `g⁻¹` on the right. -/
def toEndMul [N.Normal] : G →* End (G ⧸ₐ N) where
  toFun v := {
    hom := Quotient.lift (fun σ ↦ ⟦σ * v⁻¹⟧) <| fun a b h ↦ Quotient.sound <| by
      apply (QuotientGroup.leftRel_apply).mpr
      simp only [mul_inv_rev, inv_inv]
      convert_to v * (a⁻¹ * b) * v⁻¹ ∈ N
      · group
      · exact Subgroup.Normal.conj_mem ‹_› _ (QuotientGroup.leftRel_apply.mp h) _
    comm := fun (g : G) ↦ by
      ext (x : G ⧸ N)
      induction' x using Quotient.inductionOn with x
      simp only [FintypeCat.comp_apply, Action.FintypeCat.ofMulAction_apply, Quotient.lift_mk]
      show Quotient.lift (fun σ ↦ ⟦σ * v⁻¹⟧) _ (⟦g • x⟧) = _
      simp only [smul_eq_mul, Quotient.lift_mk, mul_assoc]
      rfl
  }
  map_one' := by
    apply Action.hom_ext
    ext (x : G ⧸ N)
    induction' x using Quotient.inductionOn with x
    simp
  map_mul' σ τ := by
    apply Action.hom_ext
    ext (x : G ⧸ N)
    induction' x using Quotient.inductionOn with x
    show ⟦x * (σ * τ)⁻¹⟧ = ⟦x * τ⁻¹ * σ⁻¹⟧
    rw [mul_inv_rev, mul_assoc]

/-- If `H` and `N` are subgroups of a group `G` with `N` normal, there is a canonical
group homomorphism `H ⧸ N ⊓ H` to the `G`-endomorphisms of `G ⧸ N`. -/
def quotientToEndHom [N.Normal] : H ⧸ Subgroup.subgroupOf N H →* End (G ⧸ₐ N) :=
  let φ' : H →* End (G ⧸ₐ N) := (toEndMul N).comp H.subtype
  QuotientGroup.lift (Subgroup.subgroupOf N H) φ' <| fun u uinU' ↦ by
  apply Action.hom_ext
  ext (x : G ⧸ N)
  induction' x using Quotient.inductionOn with μ
  apply Quotient.sound
  apply (QuotientGroup.leftRel_apply).mpr
  simpa

@[simp]
lemma quotientToEndHom_mk [N.Normal] (x : H) (g : G) :
    (quotientToEndHom H N ⟦x⟧).hom ⟦g⟧ = ⟦g * x⁻¹⟧ :=
  rfl

/-- If `N` and `H` are subgroups of a group `G` with `N ≤ H`, this is the canonical
`G`-morphism `G ⧸ N ⟶ G ⧸ H`. -/
def quotientToQuotientOfLE [Fintype (G ⧸ H)] (h : N ≤ H) : (G ⧸ₐ N) ⟶ (G ⧸ₐ H) where
  hom := Quotient.lift _ <| fun a b hab ↦ Quotient.sound <|
    (QuotientGroup.leftRel_apply).mpr (h <| (QuotientGroup.leftRel_apply).mp hab)
  comm g := by
    ext (x : G ⧸ N)
    induction' x using Quotient.inductionOn with μ
    rfl

@[simp]
lemma quotientToQuotientOfLE_hom_mk [Fintype (G ⧸ H)] (h : N ≤ H) (x : G) :
    (quotientToQuotientOfLE H N h).hom ⟦x⟧ = ⟦x⟧ :=
  rfl

end

end FintypeCat

section ToMulAction

variable {V : Type (u + 1)} [LargeCategory V] [ConcreteCategory V]

instance instMulAction {G : MonCat.{u}} (X : Action V G) :
    MulAction G ((CategoryTheory.forget _).obj X) where
  smul g x := ((CategoryTheory.forget _).map (X.ρ g)) x
  one_smul x := by
    show ((CategoryTheory.forget _).map (X.ρ 1)) x = x
    simp only [Action.ρ_one, FunctorToTypes.map_id_apply]
  mul_smul g h x := by
    show (CategoryTheory.forget V).map (X.ρ (g * h)) x =
      ((CategoryTheory.forget V).map (X.ρ h) ≫ (CategoryTheory.forget V).map (X.ρ g)) x
    rw [← Functor.map_comp, map_mul]
    rfl

/- Specialize `instMulAction` to assist typeclass inference. -/
instance {G : MonCat.{u}} (X : Action FintypeCat G) : MulAction G X.V := Action.instMulAction X
instance {G : Type u} [Group G] (X : Action FintypeCat (MonCat.of G)) : MulAction G X.V :=
  Action.instMulAction X

end ToMulAction

end Action
