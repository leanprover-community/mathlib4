/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/

module

public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.ZeroOutside

/-!
# Flasque Sheaves

We define and prove basic properties about flasque sheaves on topological spaces.

## Main definition

* `TopCat.Sheaf.IsFlasque`: A sheaf is flasque if all of the restriction morphisms are epimorphisms.

## Main results

* `TopCat.Sheaf.IsFlasque.epi_of_shortExact_Γ_map`: Given a short exact sequence of sheaves,
  `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` is flasque then `𝓖(U) ⟶ 𝓗(U)` is surjective, for any open `U`.

* `TopCat.Sheaf.IsFlasque.X₃_shortExact_isFlasque_X₁_isFlasque_X₂`: Given a short exact sequence of
  sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` and `𝓖` are flasque, then `𝓗` is flasque.

* `TopCat.Sheaf.IsFlasque.of_injective`: Injective sheaves are flasque.

* `TopCat.Sheaf.IsFlasque.H_isZero`: Flasque sheaves have no higher cohomology. For most
  applications, it is probably better to use `Subsingleton (H F (n + 1))` which can be proven by
  `infer_instance`

-/

@[expose] public section

universe u v w

open TopCat TopologicalSpace Opposite CategoryTheory Presheaf Limits
open scoped AlgebraicGeometry

variable {X : TopCat.{u}}

namespace TopCat.Sheaf

/-- A sheaf is flasque if all of the restriction morphisms are epimorphisms. -/
class IsFlasque {C : Type v} [Category.{w} C] (F : Sheaf C X) : Prop where
  epi : ∀{U V : Opens X} (i : U ⟶ V), Epi (F.val.map i.op)

namespace IsFlasque

instance (priority := low) {C : Type v} [Category.{w} C] (F : Sheaf C X) [h : IsFlasque F]
    {U V : Opens X} (i : U ⟶ V) : Epi (F.val.map i.op) := h.epi i

variable {U : Opens X} {F G : Sheaf AddCommGrpCat X} (g : F ⟶ G) (s : G.val.obj (op U))

/-- Given a morphism of sheaves `g: F ⟶ G` and a section `s` of `G(U)`, `Under g s` is comprised of
an open `V` and a section of `F(V)` that maps to `s |_ V` via `g`. This is not likely to be useful
elsewhere so we leave it in the `IsFlasque` namespace. -/
structure Under : Type u where
  /-- the open subset that our section is on -/
  V : Opens X
  /-- V must be contained in U -/
  le : V ≤ U
  /-- the section itself -/
  sec : F.val.obj (op V)
  /-- `sec` must be "under s" in the sense that `g` applied to `sec` is `s |_ V` -/
  app_s : g.val.app (op V) sec = s |_ V

/-- Given `t₁` and `t₂` in `Under g s`, we say `t₁ ≤ t₂` if `t₂.sec` restricts to `t₁.sec` -/
structure Under.R (t₁ t₂ : Under g s) : Prop where
  /-- inclusion of the opens that the sections live on -/
  le : t₁.V ≤ t₂.V
  /-- the second section restricts to the first -/
  restricts : t₂.sec |_ t₁.V = t₁.sec

open Under

/- The next two lemmas prove that the relation `R` satisfies the requirements for applying Zorn's
lemma -/
lemma Under.R.trans {a b c : Under g s} (h1 : (R g s) a b) (h2 : (R g s) b c) : (R g s) a c := by
  apply R.mk (le_trans h1.le h2.le)
  rw [← h1.restricts, ← h2.restricts]
  exact Eq.symm (restrict_restrict h1.le h2.le c.sec)

lemma Under.R.chains_bounded (c : Set (Under g s)) (h : IsChain (R g s) c) :
    ∃ ub, ∀ a ∈ c, (R g s) a ub := by
  let f : c → (Opens X) := fun x => x.val.V
  obtain ⟨t, ht, _⟩ : ∃! s_1, IsGluing F.val f (fun x => x.val.sec) s_1 := by
    apply Sheaf.existsUnique_gluing
    intro i j
    by_cases hij : i = j
    · subst hij; rfl
    dsimp
    obtain h1 | h1 := h i.property j.property (by grind)
    · rw [← h1.restricts]
      have := h1.le
      change (j.1.sec |_ i.1.V) |_ ((f i) ⊓ (f j)) = j.1.sec |_ ((f i) ⊓ (f j))
      rw [restrict_restrict]
    rw [← h1.restricts]
    have := h1.1
    change i.1.sec |_ ((f i) ⊓ (f j)) = (i.1.sec |_ j.1.V) |_ ((f i) ⊓ (f j))
    rw [restrict_restrict]
  have le : iSup f ≤ U := iSup_le fun a => a.1.le
  use ⟨iSup f, le, t, eq_app_of_forall_eq ht _ (fun i => i.val.app_s)⟩
  exact fun a ha => ⟨_, ht ⟨a, ha⟩⟩

/-- Given a short exact sequence of sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` is flasque then
`𝓖(U) ⟶ 𝓗(U)` is surjective, for any open `U`. -/
theorem epi_of_shortExact {S : ShortComplex (Sheaf AddCommGrpCat X)} (hS : S.ShortExact)
    [IsFlasque S.X₁] : Epi (S.g.1.app (op U)) := by
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro s
  -- We apply Zorn's lemma to obtain a term `t` of `Under S.g s` that is maximal.
  obtain ⟨t, ht⟩ := exists_maximal_of_chains_bounded (R.chains_bounded S.g s) (R.trans S.g s)
  have : U ≤ t.V := by
    intro x hx
    have : TopCat.Presheaf.IsLocallySurjective S.g.val := by
      change CategoryTheory.Sheaf.IsLocallySurjective S.g
      rw [CategoryTheory.Sheaf.isLocallySurjective_iff_epi']
      exact hS.epi_g
    -- We use local surjectivity to find a section of `S.X₂` on a neighborhood `W` of `x` that maps
    -- to `s |_ W`
    obtain ⟨W, i, ⟨t₁, ht₁⟩, hW⟩ := (isLocallySurjective_iff S.g.val).mp this U s x hx
    have := leOfHom i
    --`t.sec` and `t₁` need not agree on their overlap so we need to deal with their difference `t₂`
    let t₂ := t.sec |_ (t.V ⊓ W) - t₁ |_ (t.V ⊓ W)
    have : (S.g.val.app (op (t.V ⊓ W))) t₂ = 0 := by
      simp only [map_sub, map_restrict, t.app_s, restrict_restrict, ht₁, sub_eq_zero, t₂]
      conv => rhs; arg 1; change s |_ W
      simp only [restrict_restrict]
    -- Since `S` is exact and `t₂` maps to zero, we can lift it to a section `t₃` of `S.X₁`
    obtain ⟨t₃, ht₃⟩ := addCommGrpCat_shortExact_app_zero t₂ this hS.1 hS.2
    have i₁ : t.V ⊓ W ⟶ W := homOfLE inf_le_right
    -- Using that `S.X₁` is flasque, we can lift `t₃` to a section on `W`
    obtain ⟨t₄, (ht₄ : t₄ |_ (t.V ⊓ W) = t₃)⟩ :=
      (AddCommGrpCat.epi_iff_surjective (S.X₁.val.map i₁.op)).mp inferInstance t₃
    let f : Fin 2 → Opens X
    | 0 => t.V
    | 1 => W
    let sf : (i : Fin 2) → S.X₂.val.obj (op (f i))
    | 0 => t.sec
    | 1 => t₁ + (S.f.val.app (op W)) t₄
    have : sf 0 |_ (t.V ⊓ W) = sf 1 |_ (t.V ⊓ W) := by
      rw [restrict_sum, ← map_restrict, ht₄]
      simp only [ht₃, t₂, Fin.isValue, add_sub_cancel]
      rfl
    -- We glue `t.sec` and `t₁ + (S.f.val.app (op W)) t₄` together to form `t₅`
    obtain ⟨t₅, ht₅, _⟩ : ∃! t₅, IsGluing S.X₂.val f sf t₅ := by
      apply Sheaf.existsUnique_gluing
      simp only [IsCompatible, Fin.forall_fin_two]
      exact ⟨⟨rfl, this⟩, Eq.symm (restrict_inf_flip this), rfl⟩
    have le : iSup f ≤ U := by
      simp only [iSup_le_iff, Fin.forall_fin_two]
      exact ⟨t.le, leOfHom i⟩
    have app : S.g.val.app (op (iSup f)) t₅ = s |_ (iSup f) := by
      apply eq_app_of_forall_eq ht₅
        (by rw [Fin.forall_fin_two]; exact ⟨t.le, leOfHom i⟩) ?_
      rw [Fin.forall_fin_two]
      refine ⟨t.app_s, ?_⟩
      change S.g.val.app (op W) (t₁ + (S.f.val.app (op W)) t₄) = s |_ W
      have : (S.f.val.app (op W) ≫ S.g.val.app (op W)) = 0 := by
        change (S.f ≫ S.g).val.app (op W) = 0; rw [S.6]; rfl
      simp only [map_add, ← ConcreteCategory.comp_apply, this, AddCommGrpCat.hom_zero,
        AddMonoidHom.zero_apply, add_zero]
      exact ht₁
    let t₆ : Under S.g s := ⟨iSup f, le, t₅, app⟩
    have htt₆ : R S.g s t t₆ := ⟨_, ht₅ 0⟩
    exact (ht t₆ htt₆).le (by cat_disch)
  use t.sec |_ U
  conv => rhs; equals (S.g.val.app (op t.V)) t.sec |_ U =>
    rw [t.app_s, restrict_restrict, restrictOpen, restrict]
    cat_disch
  apply map_restrict

/-- Given a short exact sequence of sheaves, `0 ⟶ 𝓕 ⟶ 𝓖 ⟶ 𝓗 ⟶ 0`, if `𝓕` and `𝓖` are flasque,
then `𝓗` is flasque. -/
theorem X₃_shortExact_isFlasque_X₁_isFlasque_X₂ {S : ShortComplex (Sheaf AddCommGrpCat X)}
    (hS : S.ShortExact) [IsFlasque S.X₁] [IsFlasque S.X₂] : IsFlasque S.X₃ where
  epi {U V} := fun i => by
    have : Epi (S.g.1.app (op V) ≫ S.X₃.val.map i.op) := by
      rw [← S.g.val.naturality i.op]
      exact CategoryTheory.epi_comp' inferInstance (epi_of_shortExact hS)
    exact CategoryTheory.epi_of_epi (S.g.1.app (op V)) (S.X₃.val.map i.op)

/-- Injective sheaves are flasque. -/
instance of_injective (I : Sheaf AddCommGrpCat.{u} X) [Injective I] : IsFlasque I where
  epi := fun i => epi_map_of_injective I (leOfHom i)

/-- Flasque sheaves have no higher cohomology. For most applications, it is probably better to use
  `Subsingleton (H F (n + 1))` which can be proven by `infer_instance` -/
theorem H_isZero (F : Sheaf AddCommGrpCat X) [IsFlasque F] (n : ℕ) :
    IsZero (AddCommGrpCat.of (H F (n+1))) := by
  induction n generalizing F with
  | zero =>
    obtain ⟨I, _, f, hf⟩ := CategoryTheory.EnoughInjectives.presentation F
    let S := ShortComplex.mk f (cokernel.π f) (by cat_disch)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel f)
    have hLS := Sheaf.H.longSequence_exact hS 0 1
    refine ShortComplex.Exact.isZero_of_both_zeros (hLS.exact 2) ?_
      (zero_of_target_iso_zero _ (IsZero.isoZero (AddCommGrpCat.isZero_of_subsingleton
      (AddCommGrpCat.of (H I 1)))))
    rw[← ShortComplex.Exact.epi_f_iff (hLS.exact 1), AddCommGrpCat.epi_iff_surjective,
      ← Equiv.surjective_comp (H.equiv₀ I).symm.toEquiv]
    change Function.Surjective ((H.map S.g 0) ∘ (H.equiv₀ I).symm.toEquiv)
    conv => right; equals (H.equiv₀ S.X₃).symm.toEquiv ∘ S.g.val.app (op ⊤)
      => ext x; exact H.equiv₀_symm_comp S.g x
    rw [Equiv.comp_surjective, ← AddCommGrpCat.epi_iff_surjective]
    exact epi_of_shortExact hS
  | succ n hn =>
    obtain ⟨I, _, f, hf⟩ := CategoryTheory.EnoughInjectives.presentation F
    let S := ShortComplex.mk f (cokernel.π f) (by cat_disch)
    have hS : S.ShortExact := ShortComplex.ShortExact.mk (ShortComplex.exact_cokernel f)
    have hX₃ : S.X₃.IsFlasque := X₃_shortExact_isFlasque_X₁_isFlasque_X₂ hS
    have hLS := Sheaf.H.longSequence_exact hS (n+1) (n+2)
    exact ShortComplex.Exact.isZero_of_both_isZero (hLS.exact 2) (hn _)
      (AddCommGrpCat.isZero_of_subsingleton (AddCommGrpCat.of (H I (n + 2))))

instance {F : Sheaf AddCommGrpCat X} [IsFlasque F] (n : ℕ) : Subsingleton (H F (n + 1)) :=
  AddCommGrpCat.subsingleton_of_isZero (H_isZero F n)

end TopCat.Sheaf.IsFlasque
