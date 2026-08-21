/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Convert domain of a function

The core algorithm of the `compute_asymptotics` tactic computes asymptotics of functions of type
`ℝ → ℝ`. In this file we extend the algorithm to work with functions of type `ℕ → ℝ`, `ℤ → ℝ`
and `ℚ → ℝ`.
-/

public meta section

namespace Mathlib.Tactic.ComputeAsymptotics

namespace ConvertDomain

open Lean Meta Elab Tactic Qq

open Filter Topology Asymptotics

section convertDomain

/-- Auxiliary function that takes `f : α → ℝ` as expression and replaces all occurrences of
`cast x` (where `x` is the bound variable of the function) with a new variable `y : ℝ`. If all
occurrences of `x` are in this form, then `f` is definitionally equal to `f' ∘ cast`.
This function returns `f'`. -/
def convertFunFromWith {α : Q(Type)} (cast : Name) (f : Q($α → ℝ)) : MetaM Q(ℝ → ℝ) := do
  lambdaBoundedTelescope f 1 fun args (body : Q(ℝ)) => do
  let #[(x : Q($α))] := args | throwError "function must be of the form fun x ↦ ..."
  withLocalDeclQ .anonymous .default q(ℝ) fun y => do
    let body' := body.replace fun e =>
      match e with
      | .app _ _ =>
        let (fn, args) := e.getAppFnArgs
        if fn == cast && args.back! == x then
          y
        else
          none
      | _ => none
    return ← mkLambdaFVars #[y] body'

lemma ratCast_comap_nhds_left {c : ℚ} :
    (𝓝[<] (Rat.cast c)).comap (Rat.cast : ℚ → ℝ) = 𝓝[<] c := by
  simp only [nhdsWithin, comap_inf, comap_principal, Rat.preimage_cast_Iio]
  congr
  exact (nhds_induced Rat.cast c).symm

lemma ratCast_comap_nhds_right {c : ℚ} :
    (𝓝[>] (Rat.cast c)).comap (Rat.cast : ℚ → ℝ) = 𝓝[>] c := by
  simp only [nhdsWithin, comap_inf, comap_principal, Rat.preimage_cast_Ioi]
  congr
  exact (nhds_induced Rat.cast c).symm

lemma ratCast_comap_nhds_punctured {c : ℚ} :
    (𝓝[≠] (Rat.cast c)).comap (Rat.cast : ℚ → ℝ) = 𝓝[≠] c := by
  simp [punctured_nhds_eq_nhdsWithin_sup_nhdsWithin, comap_sup,
    ratCast_comap_nhds_left, ratCast_comap_nhds_right]

/-- Result of `convertFunDomain`. -/
structure ConvertFunDomainResult {α : Q(Type)} (f : Q($α → ℝ)) (source : Q(Filter $α)) where
  /-- Cast function -/
  cast : Q($α → ℝ)
  /-- Converted source filter in `ℝ` -/
  source' : Q(Filter ℝ)
  /-- Proof of `source'.comap cast = source` -/
  h_source : Q(($source').comap $cast = $source)
  /-- Converted function -/
  f' : Q(ℝ → ℝ)
  /-- Proof that `f` is definitionally equal to `f' ∘ cast` -/
  h_eq : $f =Q $f' ∘ $cast

/-- Given a function `f : α → ℝ`, expresses `f` as `f' ∘ cast` where `cast` is a
coercion from `α` to `ℝ`, and converts the source filter `source` to `Filter ℝ` with a proof of
`source'.comap cast = source`. -/
def convertFunDomain {α : Q(Type)} (f : Q($α → ℝ)) (source : Q(Filter $α)) :
    MetaM (ConvertFunDomainResult q($f) q($source)) := do
  match α with
  | ~q(ℕ) =>
    let f' : Q(ℝ → ℝ) := ← convertFunFromWith ``Nat.cast q($f)
    let ⟨h_eq⟩ := ← assertDefEqQ _ _
    match source with
    | ~q(atTop (α := ℕ)) => pure {
        cast := q(Nat.cast)
        source' := q(atTop)
        h_source := q(Nat.comap_cast_atTop)
        f' := q($f')
        h_eq := h_eq
      }
    | _ => throwError f!"convertFunDomain: Unsupported source filter: {← ppExpr source}"
  | ~q(ℤ) =>
    let f' : Q(ℝ → ℝ) := ← convertFunFromWith ``Int.cast q($f)
    let ⟨h_eq⟩ := ← assertDefEqQ _ _
    match source with
    | ~q(atTop (α := ℤ)) => pure {
        cast := q(Int.cast),
        source' := q(atTop),
        h_source := q(Int.comap_cast_atTop),
        f' := q($f')
        h_eq := h_eq
      }
    | ~q(atBot (α := ℤ)) => pure {
        cast := q(Int.cast),
        source' := q(atBot),
        h_source := q(Int.comap_cast_atBot),
        f' := q($f')
        h_eq := h_eq
      }
    | _ => throwError f!"convertFunDomain: Unsupported source filter: {← ppExpr source}"
  | ~q(ℚ) =>
    let f' : Q(ℝ → ℝ) := ← convertFunFromWith ``Rat.cast q($f)
    let ⟨h_eq⟩ := ← assertDefEqQ _ _
    match source with
    | ~q(atTop) => pure {
        cast := q(Rat.cast),
        source' := q(atTop),
        h_source := q(Rat.comap_cast_atTop),
        f' := q($f')
        h_eq := h_eq
      }
    | ~q(atBot) => pure {
        cast := q(Rat.cast),
        source' := q(atBot),
        h_source := q(Rat.comap_cast_atBot),
        f' := q($f')
        h_eq := h_eq
      }
    | ~q(𝓝[>] $c) => pure {
        cast := q(Rat.cast),
        source' := q(𝓝[>] (Rat.cast $c)),
        h_source := q(ratCast_comap_nhds_right),
        f' := q($f')
        h_eq := h_eq
      }
    | ~q(𝓝[<] $c) => pure {
        cast := q(Rat.cast),
        source' := q(𝓝[<] (Rat.cast $c)),
        h_source := q(ratCast_comap_nhds_left),
        f' := q($f')
        h_eq := h_eq
      }
    | ~q(𝓝[≠] $c) => pure {
        cast := q(Rat.cast),
        source' := q(𝓝[≠] (Rat.cast $c)),
        h_source := q(ratCast_comap_nhds_punctured),
        f' := q($f')
        h_eq := h_eq
      }
    | _ => throwError f!"convertFunDomain: Unsupported source filter: {← ppExpr source}"
  | _ => throwError f!"convertFunDomain: Unsupported domain of function."

lemma tendsto_cast_domain {α : Type} (f : ℝ → ℝ) (source : Filter α) (source' target : Filter ℝ)
    (cast : α → ℝ)
    (h_source : source'.comap cast = source)
    (h : Tendsto f source' target) :
    Tendsto (f ∘ cast) source target := by
  apply Tendsto.comp h
  rw [Tendsto, ← h_source]
  exact map_comap_le

lemma IsLittleO_cast_domain {α : Type} (f g : ℝ → ℝ) (l : Filter α) (l' : Filter ℝ)
    (cast : α → ℝ)
    (h : IsLittleO l' f g)
    (h_filter : l'.comap cast = l) :
    IsLittleO l (f ∘ cast) (g ∘ cast) := by
  rw [← Asymptotics.isLittleO_map, ← h_filter]
  exact Asymptotics.IsLittleO.mono h map_comap_le

lemma IsBigOWith_cast_domain {α : Type} (C : ℝ) (f g : ℝ → ℝ) (l : Filter α) (l' : Filter ℝ)
    (cast : α → ℝ)
    (h : IsBigOWith C l' f g)
    (h_filter : l'.comap cast = l) :
    IsBigOWith C l (f ∘ cast) (g ∘ cast) := by
  rw [← Asymptotics.isBigOWith_map, ← h_filter]
  exact Asymptotics.IsBigOWith.mono h map_comap_le

lemma IsBigO_cast_domain {α : Type} (f g : ℝ → ℝ) (l : Filter α) (l' : Filter ℝ)
    (cast : α → ℝ)
    (h : IsBigO l' f g)
    (h_filter : l'.comap cast = l) :
    IsBigO l (f ∘ cast) (g ∘ cast) := by
  rw [← Asymptotics.isBigO_map, ← h_filter]
  exact Asymptotics.IsBigO.mono h map_comap_le

lemma IsTheta_cast_domain {α : Type} (f g : ℝ → ℝ) (l : Filter α) (l' : Filter ℝ)
    (cast : α → ℝ)
    (h : IsTheta l' f g)
    (h_filter : l'.comap cast = l) :
    IsTheta l (f ∘ cast) (g ∘ cast) :=
  ⟨IsBigO_cast_domain _ _ _ _ _ h.left h_filter, IsBigO_cast_domain _ _ _ _ _ h.right h_filter⟩

lemma IsEquivalent_cast_domain {α : Type} (f g : ℝ → ℝ) (l : Filter α) (l' : Filter ℝ)
    (cast : α → ℝ)
    (h : IsEquivalent l' f g)
    (h_filter : l'.comap cast = l) :
    IsEquivalent l (f ∘ cast) (g ∘ cast) := by
  simp only [IsEquivalent] at h ⊢
  convert_to! ((f - g) ∘ cast) =o[l] (g ∘ cast)
  apply IsLittleO_cast_domain _ _ _ _ _ h h_filter

end convertDomain

section convertCodomain

lemma tendsto_atTop_nat_right {α : Type} (l : Filter α) (f : α → ℕ)
    (h : Tendsto (fun x ↦ (f x : ℝ)) l atTop) :
    Tendsto f l atTop := by
  rwa [tendsto_natCast_atTop_iff] at h

lemma tendsto_atTop_int_right {α : Type} (l : Filter α) (f : α → ℤ)
    (h : Tendsto (fun x ↦ (f x : ℝ)) l atTop) :
    Tendsto f l atTop := by
  rwa [tendsto_intCast_atTop_iff] at h

lemma tendsto_atBot_int_right {α : Type} (l : Filter α) (f : α → ℤ)
    (h : Tendsto (fun x ↦ (f x : ℝ)) l atBot) :
    Tendsto f l atBot := by
  rwa [tendsto_intCast_atBot_iff] at h

lemma tendsto_atTop_rat_right {α : Type} (l : Filter α) (f : α → ℚ)
    (h : Tendsto (fun x ↦ (f x : ℝ)) l atTop) :
    Tendsto f l atTop := by
  rwa [tendsto_ratCast_atTop_iff] at h

lemma tendsto_atBot_rat_right {α : Type} (l : Filter α) (f : α → ℚ)
    (h : Tendsto (fun x ↦ (f x : ℝ)) l atBot) :
    Tendsto f l atBot := by
  rwa [tendsto_ratCast_atBot_iff] at h

lemma tendsto_nhds_rat {α : Type} (l : Filter α) (f : α → ℚ) {c : ℚ}
    (h : Tendsto (fun x ↦ (f x : ℝ)) l (𝓝 (Rat.cast c))) :
    Tendsto f l (𝓝 c) := by
  rwa [← (nhds_induced Rat.cast c).symm, tendsto_comap_iff]

/-- Result of `convertTendstoTarget`. -/
structure ConvertTargetResult {α β : Q(Type)} (f : Q($α → $β)) (source : Q(Filter $α))
    (target : Q(Filter $β)) where
  /-- Cast function -/
  cast : Q($β → ℝ)
  /-- Converted target filter in `ℝ` -/
  target' : Q(Filter ℝ)
  /-- Proof of `Tendsto (cast ∘ f) source target' → Tendsto f source target` -/
  h_tendsto : Q(Tendsto ($cast ∘ $f) $source $target' → Tendsto $f $source $target)

/-- Given a filter `target : Filter β`, converts it to `target' : Filter ℝ` and a proof of
`Tendsto (cast ∘ f) source target' → Tendsto f source target`. -/
def convertTendstoTarget {α β : Q(Type)} (f : Q($α → $β)) (source : Q(Filter $α))
    (target : Q(Filter $β)) :
    MetaM <| ConvertTargetResult q($f) q($source) q($target) := do
  match β with
  | ~q(ℕ) =>
    match target with
    | ~q(atTop (α := ℕ)) =>
      return ⟨q(Nat.cast), q(atTop), q(tendsto_atTop_nat_right $source $f)⟩
    | _ => throwError f!"Unsupported target filter: {target}"
  | ~q(ℤ) =>
    match target with
    | ~q(atTop (α := ℤ)) =>
      return ⟨q(Int.cast), q(atTop), q(tendsto_atTop_int_right $source $f)⟩
    | ~q(atBot (α := ℤ)) =>
      return ⟨q(Int.cast), q(atBot), q(tendsto_atBot_int_right $source $f)⟩
    | _ => throwError f!"Unsupported target filter: {target}"
  | ~q(ℚ) =>
    match target with
    | ~q(atTop) =>
      return ⟨q(Rat.cast), q(atTop), q(tendsto_atTop_rat_right $source $f)⟩
    | ~q(atBot) =>
      return ⟨q(Rat.cast), q(atBot), q(tendsto_atBot_rat_right $source $f)⟩
    | ~q(𝓝 $c) =>
      return ⟨q(Rat.cast), q(𝓝 (Rat.cast $c)), q(tendsto_nhds_rat $source $f)⟩
    | _ => throwError f!"Unsupported target filter: {target}"
  | _ => throwError f!"Unsupported target filter: {target}"

/-- Properies required from a `cast` function to be used to switch from
goals `(f : α → β) =o[l] (g : α → γ)` to `(f ∘ castf : ℝ → ℝ) =o[l] (g ∘ castg : ℝ → ℝ)`, and
similarly for `IsBigO` and `IsEquivalent`. -/
def LawfulCodomainCast {α : Type} [NormedAddCommGroup α] (cast : α → ℝ) : Prop :=
  (∀ x, ‖x‖ = |cast x|) ∧ (∀ x y, cast (x - y) = cast x - cast y)

lemma intCast_codomain_lawful : LawfulCodomainCast Int.cast :=
  ⟨Int.norm_cast_real, Int.cast_sub⟩

lemma ratCast_codomain_lawful : LawfulCodomainCast Rat.cast :=
  ⟨Rat.norm_cast_real, Rat.cast_sub⟩

lemma id_codomain_lawful : LawfulCodomainCast (id : ℝ → ℝ) :=
  ⟨fun _ ↦ rfl, fun _ _ ↦ rfl⟩

/-- Given a type `α`, returns a coercion `cast : α → ℝ` with
a proof of `LawfulCodomainCast cast`. -/
def getLawfulCodomainCast (α : Q(Type)) (inst : Q(NormedAddCommGroup $α)) :
    MetaM <| (cast : Q($α → ℝ)) × Q(LawfulCodomainCast $cast) := do
  match α with
  | ~q(ℤ) =>
    haveI : Int.instNormedAddCommGroup =Q $inst := ⟨⟩
    return ⟨q(Int.cast), q(intCast_codomain_lawful)⟩
  | ~q(ℚ) =>
    haveI : Rat.instNormedAddCommGroup =Q $inst := ⟨⟩
    return ⟨q(Rat.cast), q(ratCast_codomain_lawful)⟩
  | ~q(ℝ) =>
    haveI : Real.normedAddCommGroup =Q $inst := ⟨⟩
    return ⟨q(id), q(id_codomain_lawful)⟩
  | _ => throwError f!"castCodomain: unsupported type"

lemma IsLittleO_cast_codomain {α β γ : Type} (f : α → β) (g : α → γ) (l : Filter α)
    [NormedAddCommGroup β] [NormedAddCommGroup γ]
    (castf : β → ℝ) (castg : γ → ℝ)
    (h_castf : LawfulCodomainCast castf)
    (h_castg : LawfulCodomainCast castg)
    (h : IsLittleO l (castf ∘ f) (castg ∘ g)) :
    IsLittleO l f g := by
  simpa [IsLittleO, IsBigOWith, h_castf.left, h_castg.left] using h

lemma IsBigOWith_cast_codomain {α β γ : Type} (C : ℝ) (f : α → β) (g : α → γ) (l : Filter α)
    [NormedAddCommGroup β] [NormedAddCommGroup γ]
    (castf : β → ℝ) (castg : γ → ℝ)
    (h_castf : LawfulCodomainCast castf)
    (h_castg : LawfulCodomainCast castg)
    (h : IsBigOWith C l (castf ∘ f) (castg ∘ g)) :
    IsBigOWith C l f g := by
  simpa [IsBigOWith, h_castf.left, h_castg.left] using h

lemma IsBigO_cast_codomain {α β γ : Type} (f : α → β) (g : α → γ) (l : Filter α)
    [NormedAddCommGroup β] [NormedAddCommGroup γ]
    (castf : β → ℝ) (castg : γ → ℝ)
    (h_castf : LawfulCodomainCast castf)
    (h_castg : LawfulCodomainCast castg)
    (h : IsBigO l (castf ∘ f) (castg ∘ g)) :
    IsBigO l f g := by
  simpa [IsBigO, IsBigOWith, h_castf.left, h_castg.left] using h

lemma IsTheta_cast_codomain {α β γ : Type} (f : α → β) (g : α → γ) (l : Filter α)
    [NormedAddCommGroup β] [NormedAddCommGroup γ]
    (castf : β → ℝ) (castg : γ → ℝ)
    (h_castf : LawfulCodomainCast castf)
    (h_castg : LawfulCodomainCast castg)
    (h : IsTheta l (castf ∘ f) (castg ∘ g)) :
    IsTheta l f g :=
  ⟨IsBigO_cast_codomain _ _ _ _ _ h_castf h_castg h.left,
    IsBigO_cast_codomain _ _ _ _ _ h_castg h_castf h.right⟩

lemma IsEquivalent_cast_codomain {α β : Type} (f g : α → β) (l : Filter α)
    [NormedAddCommGroup β]
    (cast : β → ℝ)
    (h_cast : LawfulCodomainCast cast)
    (h : IsEquivalent l (cast ∘ f) (cast ∘ g)) :
    IsEquivalent l f g := by
  simp only [IsEquivalent] at h ⊢
  apply IsLittleO_cast_codomain _ _ _ _ _ h_cast h_cast
  convert! h
  ext x
  simp [h_cast.right]

end convertCodomain

end ConvertDomain

end Mathlib.Tactic.ComputeAsymptotics
