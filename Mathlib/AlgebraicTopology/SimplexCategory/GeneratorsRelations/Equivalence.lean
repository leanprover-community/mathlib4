/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.NormalForms
/-! # Equivalence between `SimplexCategoryGenRel` and `SimplexCategory`.

In this file, we establish that `toSimplexCategory : SimplexCategoryGenRel ⥤ SimplexCategory` is
an equivalence of categories. We introduce `equivSimplexCategory` as this equivalence.

## References:
* [Kerodon Tag 04FW](https://kerodon.net/tag/04FW)

-/
namespace SimplexCategoryGenRel

open CategoryTheory

section EquivalenceWithSimplexCategory

-- Marked private as the stronger statement with unicity is below.
/-- Every epimorphism in the usual simplex category can be represented in SimplexCategoryGenRel by
a morphism satisfying `P_σ`. -/
private lemma exists_P_σ_of_epi {m k : ℕ} (f : SimplexCategory.mk (m + k) ⟶ .mk m)
    (hf : Epi f) : ∃ (g : SimplexCategoryGenRel.mk (m + k) ⟶ .mk m),
      P_σ g ∧ toSimplexCategory.map g = f := by
  induction k with
  | zero =>
    dsimp only [Nat.add_zero] at f
    haveI : f = 𝟙 _ := SimplexCategory.eq_id_of_epi _
    subst this
    exact ⟨𝟙 _, P_σ.id, by simp⟩
  | succ k h_rec =>
    have eq_1 : SimplexCategory.mk (m + k + 1) = SimplexCategory.mk (m + (k + 1)) := by
      rw [Nat.add_assoc]
    let f' := eqToHom eq_1 ≫ f
    have f'_epi : Epi f' := by apply epi_comp
    haveI : ¬(Function.Injective f'.toOrderHom) := by
      intro h
      rw [← SimplexCategory.mono_iff_injective] at h
      have le := SimplexCategory.len_lt_of_mono f'
        (by intro h0
            apply_fun (fun x ↦ x.len) at h0
            simp only [SimplexCategory.len_mk] at h0
            linarith)
      simp only [SimplexCategory.len_mk] at le
      linarith
    obtain ⟨j₀, f₀, hf₀⟩ := SimplexCategory.eq_σ_comp_of_not_injective _ this
    haveI : Epi f₀ := by
      rw [hf₀] at f'_epi
      apply CategoryTheory.epi_of_epi (SimplexCategory.σ j₀)
    obtain ⟨g₀, hg₀⟩ := h_rec f₀ this
    use (σ j₀ ≫ g₀)
    constructor
    · exact P_σ_comp _ _ (P_σ.σ _) hg₀.left
    · rw [Functor.map_comp, hg₀.right, toSimplexCategory_map_σ, ← hf₀]
      dsimp only [toSimplexCategory_obj_mk, eqToHom_refl, f']
      simp

/-- Every epimorphism in the usual simplex category can be uniquely represented in
`SimplexCategoryGenRel` by a morphism satisfying `P_σ`. -/
theorem existsUnique_P_σ_of_epi {m k : ℕ} (f : SimplexCategory.mk (m + k) ⟶ .mk m)
    (hf : Epi f) : ∃! (g : SimplexCategoryGenRel.mk (m + k) ⟶ .mk m),
      P_σ g ∧ toSimplexCategory.map g = f := by
  -- We already established existence.
  apply existsUnique_of_exists_of_unique (exists_P_σ_of_epi _ hf)
  rintro g₁ g₂ ⟨hg₁, hg₁'⟩ ⟨hg₂, hg₂'⟩
  obtain ⟨L₁, m₁, b₁, he₁, he₁', hL₁, hL₁_adm, h_comp₁⟩ := exists_normal_form_P_σ g₁ hg₁
  obtain ⟨L₂, m₂, b₂, he₂, he₂', hL₂, hL₂_adm, h_comp₂⟩ := exists_normal_form_P_σ g₂ hg₂
  -- Eliminate as much eqToHom as we can by substitutions, this is just "noise".
  have h₁ : m₁ = m₂ := by
    haveI := he₂.trans he₁.symm |>.symm
    apply_fun (fun x ↦ x.len) at this
    exact this
  have h₂ : m = m₁ := by
    haveI := he₁.symm
    apply_fun (fun x ↦ x.len) at this
    exact this
  subst h₁
  subst h₂
  have h₃ : b₁ = k := by
    haveI := he₁'.symm
    apply_fun (fun x ↦ x.len) at this
    simpa using this
  have h₄ : b₂ = k := by
    haveI := he₂'.symm
    apply_fun (fun x ↦ x.len) at this
    simpa using this
  subst h₃
  subst h₄
  symm at hL₂
  subst hL₂
  -- The "actual proof" starts here: it suffices to show the indices in the normal
  -- forms are the same, and they are characterized by simplicialEvalσ, which only cares
  -- about the order hom associated with the morphisms.
  suffices hL₁₂ : L₁ = L₂ by
    subst hL₁₂
    rw [h_comp₁, h_comp₂]
  apply isAdmissible_ext L₁ L₂ hL₁_adm hL₂_adm
  intro x
  apply (mem_isAdmissible_iff L₁ hL₁_adm x).trans
  rw [mem_isAdmissible_iff L₂ hL₂_adm x]
  have h_length : L₁.length = L₂.length := by
    rwa [← hL₂] at hL₁
  rw [h_length]
  simp only [Nat.succ_eq_add_one, and_congr_right_iff]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h_comp₁ h_comp₂
  subst h_comp₂ h_comp₁
  symm at hg₁'
  subst hg₁'
  intro hx
  rw [← simplicialEvalσ_of_isAdmissible L₁ hL₁_adm L₂.length hL₁ _ (hx.trans (lt_add_one _)),
    ← simplicialEvalσ_of_isAdmissible L₂ hL₂_adm L₂.length rfl _ (hx.trans (lt_add_one _)),
    ← simplicialEvalσ_of_isAdmissible L₁ hL₁_adm L₂.length hL₁ _ (Nat.succ_lt_succ hx),
    ← simplicialEvalσ_of_isAdmissible L₂ hL₂_adm L₂.length rfl _ (Nat.succ_lt_succ hx),
    hg₂' ]

-- Marked private as the stronger statement with unicity is below.
private lemma exists_P_δ_of_mono {m k : ℕ} (f : SimplexCategory.mk m ⟶ .mk (m + k))
    (hf : Mono f) : ∃ (g : SimplexCategoryGenRel.mk m ⟶ .mk (m + k)),
      P_δ g ∧ toSimplexCategory.map g = f := by
  induction k with
  | zero =>
    dsimp only [Nat.add_zero] at f
    haveI : f = 𝟙 _ := SimplexCategory.eq_id_of_mono _
    subst this
    exact ⟨𝟙 _, P_δ.id, by simp⟩
  | succ k h_rec =>
    have eq_1 : SimplexCategory.mk (m + k + 1) = SimplexCategory.mk (m + (k + 1)) := by
      rw [Nat.add_assoc]
    let f' := f ≫ eqToHom eq_1
    have f'_mono : Mono f' := by apply mono_comp
    haveI : ¬(Function.Surjective f'.toOrderHom) := by
      intro h
      rw [← SimplexCategory.epi_iff_surjective] at h
      have le := SimplexCategory.len_le_of_epi h
      simp only [SimplexCategory.len_mk] at le
      linarith
    obtain ⟨j₀, f₀, hf₀⟩ := SimplexCategory.eq_comp_δ_of_not_surjective _ this
    haveI : Mono f₀ := by
      rw [hf₀] at f'_mono
      apply CategoryTheory.mono_of_mono (f := f₀) (g := SimplexCategory.δ j₀)
    obtain ⟨g₀, hg₀⟩ := h_rec f₀ this
    use (g₀ ≫ δ j₀)
    constructor
    · exact P_δ_comp _ _ hg₀.left (P_δ.δ _)
    · rw [Functor.map_comp, hg₀.right, toSimplexCategory_map_δ, ← hf₀]
      dsimp [f']
      simp

/-- Every epimorphism in the usual simplex category can be uniquely represented in
`SimplexCategoryGenRel` by a morphism satisfying `P_δ`. -/
theorem existsUnique_P_δ_of_mono {m k : ℕ} (f : SimplexCategory.mk m ⟶ .mk (m + k))
    (hf : Mono f) : ∃! (g : SimplexCategoryGenRel.mk m ⟶ .mk (m + k)),
      P_δ g ∧ toSimplexCategory.map g = f := by
  apply existsUnique_of_exists_of_unique (exists_P_δ_of_mono _ hf)
  rintro g₁ g₂ ⟨hg₁, hg₁'⟩ ⟨hg₂, hg₂'⟩
  obtain ⟨L₁, m₁, b₁, he₁, he₁', hL₁, hL₁_adm, h_comp₁⟩ := exists_normal_form_P_δ g₁ hg₁
  obtain ⟨L₂, m₂, b₂, he₂, he₂', hL₂, hL₂_adm, h_comp₂⟩ := exists_normal_form_P_δ g₂ hg₂
  -- Again get rid of eqToHoms by substitutions
  have h₁ : m₁ = m₂ := congrArg (fun x ↦ x.len) (he₁.symm.trans he₂)
  have h₂ : m = m₁ := congrArg (fun x ↦ x.len) he₁
  subst h₁
  subst h₂
  have h₃ : b₁ = k := by simpa using (congrArg (fun x ↦ x.len) he₁')
  have h₄ : b₂ = k := by simpa using (congrArg (fun x ↦ x.len) he₂')
  subst h₃
  subst h₄
  symm at hL₂
  subst hL₂
  suffices hL₁₂ : L₁ = L₂ by
    subst hL₁₂
    rw [h_comp₁, h_comp₂]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at h_comp₁ h_comp₂
  apply eq_of_simplicialEvalδ_eq L₁ hL₁_adm L₂ hL₂_adm
  · intro x hx
    rw [← simplicialEvalδ_of_isAdmissible L₁ hL₁_adm L₂.length hL₁ x hx,
      ← simplicialEvalδ_of_isAdmissible L₂ hL₂_adm L₂.length hL₂ x hx,
      ← h_comp₁, ← h_comp₂, hg₁', hg₂']
  · tauto

theorem existsUnique_toSimplexCategory_map
    {x y : SimplexCategoryGenRel}
    (f : toSimplexCategory.obj x ⟶ toSimplexCategory.obj y)
    : ∃! g: x ⟶ y, toSimplexCategory.map g = f := by
  -- First step is to factorize f as an epi followed by a mono
  let strong_fac_f := (Limits.HasStrongEpiMonoFactorisations.has_fac f).some
  let z := strong_fac_f.I
  let epi₀ := strong_fac_f.toMonoFactorisation.e
  let mono₀ := strong_fac_f.toMonoFactorisation.m
  have fac := strong_fac_f.fac
  induction' x with n
  induction' y with m
  haveI := SimplexCategory.len_le_of_epi
    (Limits.HasStrongEpiMonoFactorisations.has_fac f).some.e_strong_epi.epi
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le this
  dsimp only [toSimplexCategory_obj_mk, SimplexCategory.len_mk] at hk
  let epi₁ : SimplexCategory.mk (z.len + k) ⟶ SimplexCategory.mk z.len :=
    eqToHom (by ext; simpa [z] using hk.symm) ≫ epi₀
  -- we already have existence and unicity for epis
  obtain ⟨e₁, ⟨P_σ_e₁, he₁⟩, he₁'⟩ := existsUnique_P_σ_of_epi epi₁ (by infer_instance)
  haveI := SimplexCategory.len_le_of_mono
    (Limits.HasStrongEpiMonoFactorisations.has_fac f).some.m_mono
  obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le this
  dsimp only [toSimplexCategory_obj_mk, SimplexCategory.len_mk, z] at hl
  let mono₁ : SimplexCategory.mk z.len ⟶ SimplexCategory.mk (z.len + l) :=
     mono₀ ≫ eqToHom (by ext; simpa [z] using hl)
  -- same for monos
  obtain ⟨m₁, ⟨P_δ_m₁, hm₁⟩, hm₁'⟩ := existsUnique_P_δ_of_mono mono₁ (by infer_instance)
  use eqToHom (by ext; tauto) ≫ e₁ ≫ m₁ ≫ eqToHom (by ext; tauto)
  -- this takes care of existence
  simp [he₁, hm₁, epi₁, mono₁, epi₀, mono₀, eqToHom_map]
  intro g hg
  -- for unicitiy, we use the uniqueness of epi-mono factorisation in SimplexCategory.
  -- plus unicity of e₁ and m₁.
  obtain ⟨z₁, e₂, m₂, P_σ_e₂, P_δ_m₂, fac₂⟩ := exists_P_σ_P_δ_factorisation g
  rw [fac₂] at hg
  haveI : Epi (toSimplexCategory.map e₂) := by
    apply (isSplitEpi_P_σ_toSimplexCategory P_σ_e₂).epi
  haveI : Mono (toSimplexCategory.map m₂) := by
    apply (isSplitMono_P_δ_toSimplexCategory P_δ_m₂).mono
  simp only [Functor.map_comp, toSimplexCategory_obj_mk, epi₁, z, epi₀, mono₁, mono₀] at hg
  have im₁ := SimplexCategory.image_eq hg
  have im₂ := SimplexCategory.image_eq fac
  have eq_z₁ : z₁ = mk z.len := by
    ext
    apply_fun (fun x ↦ x.len) at im₁
    apply_fun (fun x ↦ x.len) at im₂
    dsimp only [z]
    simp only [toSimplexCategory_len, mono₁, mono₀, z, epi₁, epi₀, strong_fac_f] at im₁
    exact im₁.symm.trans im₂
  generalize_proofs p₁ p₂
  -- leveraging epi-mono factorisation unicity in SimplexCategory
  let e₃ := toSimplexCategory.map e₂ ≫ eqToHom im₁.symm
  let m₃ := eqToHom im₁ ≫ toSimplexCategory.map m₂
  have fac₃ : e₃ ≫ m₃ = f := by simp [e₃, m₃, hg]
  have eq1 := SimplexCategory.image_ι_eq fac₃
  have eq2 := SimplexCategory.factorThruImage_eq fac₃
  let e₄ := eqToHom ((by ext; simpa [z] using hk) : SimplexCategory.mk n = _) ≫ epi₁ ≫
    eqToHom im₂.symm
  let m₄ := eqToHom im₂ ≫ mono₁ ≫
    eqToHom ((by ext; simpa [z] using hl.symm) : _ = SimplexCategory.mk m)
  have fac₄ : e₄ ≫ m₄ = f := by simpa [e₄, m₄, epi₁, mono₁, fac]
  have eq3 := SimplexCategory.image_ι_eq fac₄
  have eq4 := SimplexCategory.factorThruImage_eq fac₄
  -- Finally we can prove uniqueness of each morphisms
  -- Given that there are eqToHom everywhere, it will be better to show they are HEq.
  have eq₁ := he₁' (eqToHom p₁.symm ≫ e₂ ≫ eqToHom eq_z₁) ?_
  · have eq₂ := hm₁' (eqToHom eq_z₁.symm ≫ m₂ ≫ eqToHom p₂.symm) ?_
    · rw [← eq₁, ← eq₂]
      simpa
    · constructor
      · apply P_δ_comp _ _ (P_δ_eqToHom _)
        apply P_δ_comp _ _ _ (P_δ_eqToHom _)
        assumption
      · simp only [toSimplexCategory_obj_mk, SimplexCategory.mk_len, Functor.map_comp, eqToHom_map,
          Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, m₄, mono₁, e₄, z, e₃, epi₁,
          epi₀, m₃] at eq1 eq3 ⊢
        rw [← heq_iff_eq] at eq1 eq3 ⊢
        simp only [heq_comp_eqToHom_iff, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
          heq_eqToHom_comp_iff] at eq1 eq3 ⊢
        rw [HEq.comm] at eq3 ⊢
        exact HEq.trans eq3 eq1
  · constructor
    · apply P_σ_comp _ _ (P_σ_eqToHom _)
      apply P_σ_comp _ _ _ (P_σ_eqToHom _)
      assumption
    · simp only [toSimplexCategory_obj_mk, SimplexCategory.mk_len, Functor.map_comp, eqToHom_map,
          Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id, m₄, epi₁, e₄, z, e₃,
          m₃] at eq2 eq4 ⊢
      rw [← heq_iff_eq] at eq2 eq4 ⊢
      simp only [heq_comp_eqToHom_iff, eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
          heq_eqToHom_comp_iff] at eq2 eq4 ⊢
      rw [HEq.comm] at eq4 ⊢
      exact HEq.trans eq4 eq2

instance : toSimplexCategory.Full where
  map_surjective {x y} f := by
    obtain ⟨a, ha, _⟩ := existsUnique_toSimplexCategory_map f
    exact ⟨a, ha⟩

instance : toSimplexCategory.Faithful where
  map_injective {x y} f g hfg := by
    obtain ⟨a, ha, u⟩ := existsUnique_toSimplexCategory_map (toSimplexCategory.map f)
    exact (u f rfl).trans (u g hfg.symm).symm

instance : toSimplexCategory.EssSurj where
  mem_essImage x := by
    let y := SimplexCategoryGenRel.mk (x.len)
    haveI : toSimplexCategory.obj y ≅ x := Iso.refl _
    apply Functor.essImage.ofIso this
    exact toSimplexCategory.obj_mem_essImage _

instance : toSimplexCategory.IsEquivalence := by
  apply Functor.IsEquivalence.mk <;> infer_instance

/-- The equivalence between `SimplexCategoryGenRel` and `SimplexCategory`. -/
noncomputable def equivSimplexCategory : SimplexCategoryGenRel ≌ SimplexCategory :=
  toSimplexCategory.asEquivalence

@[simp]
lemma equivSimplexCategory_functor_obj_mk (n : ℕ) :
    equivSimplexCategory.functor.obj (mk n) = .mk n := by
  rfl

@[simp]
lemma equivSimplexCategory_functor_map_σ (n : ℕ) (i : Fin (n + 1)) :
    equivSimplexCategory.functor.map (σ i) = SimplexCategory.σ i := by
  rfl

@[simp]
lemma equivSimplexCategory_functor_map_δ (n : ℕ) (i : Fin (n + 2)) :
    equivSimplexCategory.functor.map (δ i) = SimplexCategory.δ i := by
  rfl

/-- The inverse of equivSimplexCategory at `SimplexCategory.mk n` is isomorphism to
`SimplexCategoryGenRel.mk n`. -/
noncomputable def equivSimplexCategory_inverse_objIsoMk (n : ℕ) :
    equivSimplexCategory.inverse.obj (.mk n) ≅ mk n :=
  (equivSimplexCategory.unitIso.app (mk n)).symm

/-- The inverse of equivSimplexCategory sends the degeneracies to degeneracies, up to
conjugation by the isomorphism `equivSimplexCategory_inverse_objIsoMk`. -/
@[simp]
lemma equivSimplexCategory_inverse_map_σ (n : ℕ) (i : Fin (n + 1)) :
   (equivSimplexCategory_inverse_objIsoMk (n + 1)).inv ≫
      equivSimplexCategory.inverse.map (SimplexCategory.σ i) ≫
        (equivSimplexCategory_inverse_objIsoMk n).hom  = σ i := by
  apply equivSimplexCategory.functor.map_injective
  simp only [equivSimplexCategory_functor_obj_mk, equivSimplexCategory_inverse_objIsoMk,
    Functor.id_obj, Functor.comp_obj, Iso.symm_inv, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.map_comp, Equivalence.fun_inv_map, Category.assoc, equivSimplexCategory_functor_map_σ]
  conv_lhs =>
    right
    left
    change equivSimplexCategory.counitIso.hom.app (equivSimplexCategory.functor.obj (mk (n + 1)))
  rw [reassoc_of%(equivSimplexCategory.functor_unitIso_comp (mk (n + 1)))]
  conv_lhs =>
    right
    left
    change equivSimplexCategory.counitInv.app (equivSimplexCategory.functor.obj (mk n))
  rw [equivSimplexCategory.counitInv_app_functor (mk n), ← Functor.map_comp]
  simp

/-- The inverse of equivSimplexCategory sends the faces to faces, up to
conjugation by the isomorphism `equivSimplexCategory_inverse_objIsoMk`. -/
@[simp]
lemma equivSimplexCategory_inverse_δ (n : ℕ) (i : Fin (n + 2)):
   (equivSimplexCategory_inverse_objIsoMk n).inv ≫
      equivSimplexCategory.inverse.map (SimplexCategory.δ i) ≫
        (equivSimplexCategory_inverse_objIsoMk (n + 1)).hom  = δ i := by
  apply equivSimplexCategory.functor.map_injective
  simp only [equivSimplexCategory_functor_obj_mk, equivSimplexCategory_inverse_objIsoMk,
    Functor.id_obj, Functor.comp_obj, Iso.symm_inv, Iso.app_hom, Iso.symm_hom, Iso.app_inv,
    Functor.map_comp, Equivalence.fun_inv_map, Category.assoc, equivSimplexCategory_functor_map_δ]
  conv_lhs =>
    right
    left
    change equivSimplexCategory.counitIso.hom.app (equivSimplexCategory.functor.obj (mk n))
  rw [reassoc_of%(equivSimplexCategory.functor_unitIso_comp (mk n))]
  conv_lhs =>
    right
    left
    change equivSimplexCategory.counitInv.app (equivSimplexCategory.functor.obj (mk (n + 1)))
  rw [equivSimplexCategory.counitInv_app_functor (mk (n + 1)), ← Functor.map_comp]
  simp

end EquivalenceWithSimplexCategory

end SimplexCategoryGenRel
