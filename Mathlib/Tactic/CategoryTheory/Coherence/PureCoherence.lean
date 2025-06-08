/-
Copyright (c) 2024 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import Lean.Meta.Tactic.Apply
import Mathlib.Tactic.CategoryTheory.Coherence.Datatypes

/-!
# Coherence tactic

This file provides a meta framework for the coherence tactic, which solves goals of the form
`η = θ`, where `η` and `θ` are 2-morphism in a bicategory or morphisms in a monoidal category
made up only of associators, unitors, and identities.

The function defined here is a meta reimplementation of the formalized coherence theorems provided
in the following files:
- Mathlib.CategoryTheory.Monoidal.Free.Coherence
- Mathlib.CategoryTheory.Bicategory.Coherence
See these files for a mathematical explanation of the proof of the coherence theorem.

The actual tactics that users will use are given in
- `Mathlib/Tactic/CategoryTheory/Monoidal/PureCoherence.lean`
- `Mathlib/Tactic/CategoryTheory/Bicategory/PureCoherence.lean`

-/

open Lean Meta

namespace Mathlib.Tactic

namespace BicategoryLike

/-- The result of normalizing a 1-morphism. -/
structure Normalize.Result where
  /-- The normalized 1-morphism. -/
  normalizedHom : NormalizedHom
  /-- The 2-morphism from the original 1-morphism to the normalized 1-morphism. -/
  toNormalize : Mor₂Iso
  deriving Inhabited

open Mor₂Iso MonadMor₂Iso

variable {ρ : Type} [Context ρ] [MonadMor₁ (CoherenceM ρ)] [MonadMor₂Iso (CoherenceM ρ)]

/-- Meta version of `CategoryTheory.FreeBicategory.normalizeIso`. -/
def normalize (p : NormalizedHom) (f : Mor₁) :
    CoherenceM ρ Normalize.Result := do
  match f with
  | .id _ _ =>
    return ⟨p, ← rightUnitorM' p.e⟩
  | .comp _ f g =>
    let ⟨pf, η_f⟩ ← normalize p f
    let η_f' ← whiskerRightM η_f g
    let ⟨pfg, η_g⟩ ← normalize pf g
    let η ← comp₂M η_f' η_g
    let α ← symmM (← associatorM' p.e f g)
    let η' ← comp₂M α η
    return ⟨pfg, η'⟩
  | .of f =>
    let pf ← NormalizedHom.consM p f
    let α ← id₂M' pf.e
    return ⟨pf, α⟩

/-- Lemmas to prove the meta version of `CategoryTheory.FreeBicategory.normalize_naturality`. -/
class MonadNormalizeNaturality (m : Type → Type) where
  /-- The naturality for the associator. -/
  mkNaturalityAssociator (p pf pfg pfgh : NormalizedHom) (f g h : Mor₁)
    (η_f η_g η_h : Mor₂Iso) : m Expr
  /-- The naturality for the left unitor. -/
  mkNaturalityLeftUnitor (p pf : NormalizedHom) (f : Mor₁) (η_f : Mor₂Iso) : m Expr
  /-- The naturality for the right unitor. -/
  mkNaturalityRightUnitor (p pf : NormalizedHom) (f : Mor₁) (η_f : Mor₂Iso) : m Expr
  /-- The naturality for the identity. -/
  mkNaturalityId (p pf : NormalizedHom) (f : Mor₁) (η_f : Mor₂Iso) : m Expr
  /-- The naturality for the composition. -/
  mkNaturalityComp (p pf : NormalizedHom) (f g h : Mor₁) (η θ η_f η_g η_h : Mor₂Iso)
    (ih_η ih_θ : Expr) : m Expr
  /-- The naturality for the left whiskering. -/
  mkNaturalityWhiskerLeft (p pf pfg : NormalizedHom) (f g h : Mor₁)
    (η η_f η_fg η_fh : Mor₂Iso) (ih_η : Expr) : m Expr
  /-- The naturality for the right whiskering. -/
  mkNaturalityWhiskerRight (p pf pfh : NormalizedHom) (f g h : Mor₁) (η η_f η_g η_fh : Mor₂Iso)
    (ih_η : Expr) : m Expr
  /-- The naturality for the horizontal composition. -/
  mkNaturalityHorizontalComp (p pf₁ pf₁f₂ : NormalizedHom) (f₁ g₁ f₂ g₂ : Mor₁)
    (η θ η_f₁ η_g₁ η_f₂ η_g₂ : Mor₂Iso) (ih_η ih_θ : Expr) : m Expr
  /-- The naturality for the inverse. -/
  mkNaturalityInv (p pf : NormalizedHom) (f g : Mor₁) (η η_f η_g : Mor₂Iso) (ih_η : Expr) : m Expr

open MonadNormalizeNaturality

variable [MonadCoherehnceHom (CoherenceM ρ)] [MonadNormalizeNaturality (CoherenceM ρ)]

/-- Meta version of `CategoryTheory.FreeBicategory.normalize_naturality`. -/
partial def naturality (nm : Name) (p : NormalizedHom) (η : Mor₂Iso) : CoherenceM ρ Expr := do
  let result ← match η with
  | .of _ => throwError m!"could not find a structural isomorphism, but {η.e}"
  | .coherenceComp _ _ _ _ _ α η θ => withTraceNode nm (fun _ => return m!"monoidalComp") do
    let α ← MonadCoherehnceHom.unfoldM α
    let αθ ← comp₂M α θ
    let ηαθ ← comp₂M η αθ
    naturality nm p ηαθ
  | .structuralAtom η => match η with
    | .coherenceHom α => withTraceNode nm (fun _ => return m!"coherenceHom") do
      let α ← MonadCoherehnceHom.unfoldM α
      naturality nm p α
    | .associator _ f g h => withTraceNode nm (fun _ => return m!"associator") do
      let ⟨pf, η_f⟩ ← normalize p f
      let ⟨pfg, η_g⟩ ← normalize pf g
      let ⟨pfgh, η_h⟩ ← normalize pfg h
      mkNaturalityAssociator p pf pfg pfgh f g h η_f η_g η_h
    | .leftUnitor _ f => withTraceNode nm (fun _ => return m!"leftUnitor") do
      let ⟨pf, η_f⟩ ← normalize p f
      mkNaturalityLeftUnitor p pf f η_f
    | .rightUnitor _ f => withTraceNode nm (fun _ => return m!"rightUnitor") do
      let ⟨pf, η_f⟩ ← normalize p f
      mkNaturalityRightUnitor p pf f η_f
    | .id _ f => withTraceNode nm (fun _ => return m!"id") do
    let ⟨pf, η_f⟩ ← normalize p f
    mkNaturalityId p pf f η_f
  | .comp _ f g h η θ => withTraceNode nm (fun _ => return m!"comp") do
    let ⟨pf, η_f⟩ ← normalize p f
    let ⟨_, η_g⟩ ← normalize p g
    let ⟨_, η_h⟩ ← normalize p h
    let ih_η ← naturality nm p η
    let ih_θ ← naturality nm p θ
    mkNaturalityComp p pf f g h η θ η_f η_g η_h ih_η ih_θ
  | .whiskerLeft _ f g h η => withTraceNode nm (fun _ => return m!"whiskerLeft") do
    let ⟨pf, η_f⟩ ← normalize p f
    let ⟨pfg, η_fg⟩ ← normalize pf g
    let ⟨_, η_fh⟩ ← normalize pf h
    let ih ← naturality nm pf η
    mkNaturalityWhiskerLeft p pf pfg f g h η η_f η_fg η_fh ih
  | .whiskerRight _ f g η h => withTraceNode nm (fun _ => return m!"whiskerRight") do
    let ⟨pf, η_f⟩ ← normalize p f
    let ⟨_, η_g⟩ ← normalize p g
    let ⟨pfh, η_fh⟩ ← normalize pf h
    let ih ← naturality nm p η
    mkNaturalityWhiskerRight p pf pfh f g h η η_f η_g η_fh ih
  | .horizontalComp _ f₁ g₁ f₂ g₂ η θ => withTraceNode nm (fun _ => return m!"hComp") do
    let ⟨pf₁, η_f₁⟩ ← normalize p f₁
    let ⟨_, η_g₁⟩ ← normalize p g₁
    let ⟨pf₁f₂, η_f₂⟩ ← normalize pf₁ f₂
    let ⟨_, η_g₂⟩ ← normalize pf₁ g₂
    let ih_η ← naturality nm p η
    let ih_θ ← naturality nm pf₁ θ
    mkNaturalityHorizontalComp p pf₁ pf₁f₂ f₁ g₁ f₂ g₂ η θ η_f₁ η_g₁ η_f₂ η_g₂ ih_η ih_θ
  | .inv _ f g η => withTraceNode nm (fun _ => return m!"inv") do
    let ⟨pf, η_f⟩ ← normalize p f
    let ⟨_, η_g⟩ ← normalize p g
    let ih_η ← naturality nm p η
    mkNaturalityInv p pf f g η η_f η_g ih_η
  withTraceNode nm (fun _ => return m!"{checkEmoji} {← inferType result}") do
    if ← isTracingEnabledFor nm then addTrace nm m!"proof: {result}"
  return result

/-- Prove the equality between structural isomorphisms using the naturality of `normalize`. -/
class MkEqOfNaturality (m : Type → Type) where
  /-- Auxiliary function for `pureCoherence`. -/
  mkEqOfNaturality (η θ : Expr) (η' θ' : IsoLift) (η_f η_g : Mor₂Iso) (Hη Hθ : Expr) : m Expr

export MkEqOfNaturality (mkEqOfNaturality)

/-- Close the goal of the form `η = θ`, where `η` and `θ` are 2-isomorphisms made up only of
associators, unitors, and identities. -/
def pureCoherence (ρ : Type) [Context ρ] [MkMor₂ (CoherenceM ρ)]
    [MonadMor₁ (CoherenceM ρ)] [MonadMor₂Iso (CoherenceM ρ)]
    [MonadCoherehnceHom (CoherenceM ρ)] [MonadNormalizeNaturality (CoherenceM ρ)]
    [MkEqOfNaturality (CoherenceM ρ)]
    (nm : Name) (mvarId : MVarId) : MetaM (List MVarId) :=
  mvarId.withContext do
    withTraceNode nm (fun ex => match ex with
      | .ok _ => return m!"{checkEmoji} coherence equality: {← mvarId.getType}"
      | .error err => return m!"{crossEmoji} {err.toMessageData}") do
      let e ← instantiateMVars <| ← mvarId.getType
      let some (_, η, θ) := (← whnfR e).eq?
        | throwError "coherence requires an equality goal"
      let ctx : ρ ← mkContext η
      CoherenceM.run (ctx := ctx) do
        let .some ηIso := (← MkMor₂.ofExpr η).isoLift? |
          throwError "could not find a structural isomorphism, but {η}"
        let .some θIso := (← MkMor₂.ofExpr θ).isoLift? |
          throwError "could not find a structural isomorphism, but {θ}"
        let f ← ηIso.e.srcM
        let g ← ηIso.e.tgtM
        let a := f.src
        let nil ← normalizedHom.nilM a
        let ⟨_, η_f⟩ ← normalize nil f
        let ⟨_, η_g⟩ ← normalize nil g
        let Hη ← withTraceNode nm (fun ex => do return m!"{exceptEmoji ex} LHS") do
          naturality nm nil ηIso.e
        let Hθ ← withTraceNode nm (fun ex => do return m!"{exceptEmoji ex} RHS") do
          naturality nm nil θIso.e
        let H ← mkEqOfNaturality η θ ηIso θIso η_f η_g Hη Hθ
        mvarId.apply H

end Mathlib.Tactic.BicategoryLike
