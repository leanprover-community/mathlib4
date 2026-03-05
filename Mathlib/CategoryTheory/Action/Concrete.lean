/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.CategoryTheory.Action.Basic
public import Mathlib.CategoryTheory.FintypeCat
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Constructors for `Action V G` for some concrete categories

We construct `Action (Type*) G` from a `[MulAction G X]` instance and give some applications.
-/

@[expose] public section

assert_not_exists Field

universe u v

open CategoryTheory Limits

namespace Action

section
variable {G : Type u} [Group G] {A : Action (Type u) G}

@[simp]
theorem ρ_inv_self_apply (g : G) (x : A.V) :
    A.ρ g⁻¹ (A.ρ g x) = x :=
  show (A.ρ g⁻¹ * A.ρ g) x = x by simp [← map_mul]

@[simp]
theorem ρ_self_inv_apply (g : G) (x : A.V) :
    A.ρ g (A.ρ g⁻¹ x) = x :=
  show (A.ρ g * A.ρ g⁻¹) x = x by simp [← map_mul]

end

/-- Bundles a type `H` with a multiplicative action of `G` as an `Action`. -/
@[simps -isSimp]
def ofMulAction (G : Type*) (H : Type u) [Monoid G] [MulAction G H] : Action (Type u) G where
  V := H
  ρ := @MulAction.toEndHom _ _ _ (by assumption)

@[simp]
theorem ofMulAction_apply {G H : Type*} [Monoid G] [MulAction G H] (g : G) (x : H) :
    (ofMulAction G H).ρ g x = (g • x : H) :=
  rfl

/-- Given a family `F` of types with `G`-actions, this is the limit cone demonstrating that the
product of `F` as types is a product in the category of `G`-sets. -/
def ofMulActionLimitCone {ι : Type v} (G : Type max v u) [Monoid G] (F : ι → Type max v u)
    [∀ i : ι, MulAction G (F i)] :
    LimitCone (Discrete.functor fun i : ι => Action.ofMulAction G (F i)) where
  cone :=
    { pt := Action.ofMulAction G (∀ i : ι, F i)
      π := Discrete.natTrans (fun i => ⟨fun x => x i.as, fun _ => rfl⟩) }
  isLimit :=
    { lift := fun s =>
        { hom := fun x i => (s.π.app ⟨i⟩).hom x
          comm := fun g => by
            ext x
            funext j
            exact congr_fun ((s.π.app ⟨j⟩).comm g) x }
      fac := fun _ _ => rfl
      uniq := fun s f h => by
        ext x
        funext j
        dsimp at *
        rw [← h ⟨j⟩]
        rfl }

/-- The `G`-set `G`, acting on itself by left multiplication. -/
abbrev leftRegular (G : Type u) [Monoid G] : Action (Type u) G :=
  Action.ofMulAction G G

/-- The `G`-set `Gⁿ`, acting on itself by left multiplication. -/
abbrev diagonal (G : Type u) [Monoid G] (n : ℕ) : Action (Type u) G :=
  Action.ofMulAction G (Fin n → G)

/-- We have `Fin 1 → G ≅ G` as `G`-sets, with `G` acting by left multiplication. -/
def diagonalOneIsoLeftRegular (G : Type*) [Monoid G] : diagonal G 1 ≅ leftRegular G :=
  Action.mkIso (Equiv.funUnique _ _).toIso fun _ => rfl

namespace FintypeCat

/-- If `X` is a type with `[Fintype X]` and `G` acts on `X`, then `G` also acts on
`FintypeCat.of X`. -/
instance (G : Type*) (X : Type*) [Monoid G] [MulAction G X] [Fintype X] :
    MulAction G (FintypeCat.of X) :=
  inferInstaceAs% (MulAction G X)

/-- Bundles a finite type `H` with a multiplicative action of `G` as an `Action`. -/
def ofMulAction (G : Type*) (H : FintypeCat.{u}) [Monoid G] [MulAction G H] :
    Action FintypeCat G where
  V := H
  ρ := InducedCategory.endEquiv.symm.toMonoidHom.comp MulAction.toEndHom

@[simp]
theorem ofMulAction_apply {G : Type*} {H : FintypeCat.{u}} [Monoid G] [MulAction G H]
    (g : G) (x : H) : ConcreteCategory.hom ((FintypeCat.ofMulAction G H).ρ g) x = (g • x : H) :=
  rfl

section

/-- Shorthand notation for the quotient of `G` by `H` as a finite `G`-set. -/
notation:10 G:10 " ⧸ₐ " H:10 => Action.FintypeCat.ofMulAction G (FintypeCat.of <| G ⧸ H)

variable {G : Type*} [Group G] (H N : Subgroup G) [Fintype (G ⧸ N)]

/-- If `N` is a normal subgroup of `G`, then this is the group homomorphism
sending an element `g` of `G` to the `G`-endomorphism of `G ⧸ₐ N` given by
multiplication with `g⁻¹` on the right. -/
def toEndHom [N.Normal] : G →* End (G ⧸ₐ N) where
  toFun v :=
  { hom := FintypeCat.homMk (Quotient.lift (fun σ ↦ ⟦σ * v⁻¹⟧) <| fun a b h ↦ Quotient.sound <| by
      apply (QuotientGroup.leftRel_apply).mpr
      -- We avoid `group` here to minimize imports while low in the hierarchy;
      -- typically it would be better to invoke the tactic.
      simpa [mul_assoc] using Subgroup.Normal.conj_mem ‹_› _ (QuotientGroup.leftRel_apply.mp h) _)
    comm := fun (g : G) ↦ by
      ext (x : G ⧸ N)
      induction x using Quotient.inductionOn with | h x
      dsimp
      apply (Quotient.lift_mk _ _ _).trans
      simp only [smul_eq_mul, QuotientGroup.mk_mul, mul_assoc]
      rfl }
  map_one' := by
    apply Action.hom_ext
    ext (x : G ⧸ N)
    induction x using Quotient.inductionOn
    simp
  map_mul' σ τ := by
    apply Action.hom_ext
    ext (x : G ⧸ N)
    induction x using Quotient.inductionOn with | _ x
    change ⟦x * (σ * τ)⁻¹⟧ = ⟦x * τ⁻¹ * σ⁻¹⟧
    rw [mul_inv_rev, mul_assoc]

@[simp]
lemma toEndHom_apply [N.Normal] (g h : G) : (toEndHom N g).hom ⟦h⟧ = ⟦h * g⁻¹⟧ := rfl

variable {N} in
lemma toEndHom_trivial_of_mem [N.Normal] {n : G} (hn : n ∈ N) : toEndHom N n = 𝟙 (G ⧸ₐ N) := by
  apply Action.hom_ext
  ext (x : G ⧸ N)
  induction x using Quotient.inductionOn
  exact Quotient.sound ((QuotientGroup.leftRel_apply).mpr <| by simpa)

/-- If `H` and `N` are subgroups of a group `G` with `N` normal, there is a canonical
group homomorphism `H ⧸ N ⊓ H` to the `G`-endomorphisms of `G ⧸ N`. -/
def quotientToEndHom [N.Normal] : H ⧸ Subgroup.subgroupOf N H →* End (G ⧸ₐ N) :=
  QuotientGroup.lift (Subgroup.subgroupOf N H) ((toEndHom N).comp H.subtype) <| fun _ uinU' ↦
    toEndHom_trivial_of_mem uinU'

@[simp]
lemma quotientToEndHom_mk [N.Normal] (x : H) (g : G) :
    (quotientToEndHom H N ⟦x⟧).hom ⟦g⟧ = ⟦g * x⁻¹⟧ :=
  rfl

/-- If `N` and `H` are subgroups of a group `G` with `N ≤ H`, this is the canonical
`G`-morphism `G ⧸ N ⟶ G ⧸ H`. -/
def quotientToQuotientOfLE [Fintype (G ⧸ H)] (h : N ≤ H) : (G ⧸ₐ N) ⟶ (G ⧸ₐ H) where
  hom := FintypeCat.homMk (Quotient.lift _ <| fun _ _ hab ↦ Quotient.sound <|
    (QuotientGroup.leftRel_apply).mpr (h <| (QuotientGroup.leftRel_apply).mp hab))
  comm g := by
    ext (x : G ⧸ N)
    induction x using Quotient.inductionOn
    rfl

@[simp]
lemma quotientToQuotientOfLE_hom_mk [Fintype (G ⧸ H)] (h : N ≤ H) (x : G) :
    (quotientToQuotientOfLE H N h).hom ⟦x⟧ = ⟦x⟧ :=
  rfl

end

end FintypeCat

section ToMulAction

variable {V : Type (u + 1)} [LargeCategory V] {FV : V → V → Type*} {CV : V → Type*}
variable [∀ X Y, FunLike (FV X Y) (CV X) (CV Y)] [ConcreteCategory V FV]

instance instMulAction {G : Type*} [Monoid G] (X : Action V G) :
    MulAction G (ToType X) where
  smul g x := ConcreteCategory.hom (X.ρ g) x
  one_smul x := by
    change ConcreteCategory.hom (X.ρ 1) x = x
    simp
  mul_smul g h x := by
    change ConcreteCategory.hom (X.ρ (g * h)) x =
      ConcreteCategory.hom (X.ρ g) ((ConcreteCategory.hom (X.ρ h)) x)
    simp

/- Specialize `instMulAction` to assist typeclass inference. -/
instance {G : Type*} [Monoid G] (X : Action FintypeCat G) : MulAction G X.V :=
  Action.instMulAction X

end ToMulAction

end Action
