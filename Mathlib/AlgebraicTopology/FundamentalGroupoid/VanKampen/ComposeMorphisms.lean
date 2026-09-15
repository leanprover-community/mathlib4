module

public import Mathlib
public import Mathlib.CategoryTheory.Groupoid.Basic
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.VanKampen.EqToHomHelpers

@[expose] public section

open CategoryTheory
variable {C : Type*} [Groupoid C]
/-- Helper: dependent congruence for homs family. -/
lemma homs_dep_congr {k : ℕ} {objs : Fin (k + 1) → C}
    {homs : ∀ i : Fin k, objs (Fin.castSucc i) ⟶ objs (Fin.succ i)}
    {i j : Fin k} (h : i = j) :
    eqToHom (congr_arg (fun x : Fin k => objs (Fin.castSucc x)) h).symm ≫
    homs i ≫
    eqToHom (congr_arg (fun x : Fin k => objs (Fin.succ x)) h) =
    homs j := by
  cases h
  simp [eqToHom_refl, Category.comp_id, Category.id_comp]
  <;> rfl
/-- Compose a list of morphisms f₀, f₁, ..., fₙ₋₁ where the codomain of fᵢ equals
    the domain of fᵢ₊₁. -/
def comp_list (n : ℕ) (objs : Fin (n + 1) → C)
    (homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i)) :
    objs 0 ⟶ objs (Fin.last n) := by
  induction n with
  | zero =>
    exact 𝟙 (objs 0)
  | succ n ih =>
    let objs' : Fin (n + 1) → C := fun i : Fin (n + 1) => objs (Fin.castSucc i)
    let homs' : ∀ i : Fin n, objs' (Fin.castSucc i) ⟶ objs' (Fin.succ i) :=
      fun i : Fin n => homs (Fin.castSucc i)
    exact (ih objs' homs') ≫ homs (Fin.last n)
/-- Composing 0 morphisms gives the identity. -/
theorem comp_list_zero (objs : Fin 1 → C) :
    comp_list 0 objs (fun i => Fin.elim0 i) = 𝟙 (objs 0) := by
  rfl
/-- Composing n+1 morphisms is composing n morphisms then adding one more. -/
theorem comp_list_succ (n : ℕ) (objs : Fin (n + 2) → C)
    (homs : ∀ i : Fin (n + 1), objs (Fin.castSucc i) ⟶ objs (Fin.succ i)) :
    comp_list (n + 1) objs homs =
    comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
      (fun i : Fin n => homs (Fin.castSucc i)) ≫ homs (Fin.last n) := by
  rfl
/-- Composing 1 morphism gives just that morphism. -/
theorem comp_list_one (objs : Fin 2 → C)
    (homs : ∀ i : Fin 1, objs (Fin.castSucc i) ⟶ objs (Fin.succ i)) :
    comp_list 1 objs homs = homs 0 := by
  simp [comp_list, Fin.last]
  <;> rfl
/-- Congruence: if two families of morphisms are pointwise equal, then their comp_list is equal. -/
theorem comp_list_congr {n : ℕ} (objs : Fin (n + 1) → C)
    (homs₁ homs₂ : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i))
    (h : ∀ i : Fin n, homs₁ i = homs₂ i) :
    comp_list n objs homs₁ = comp_list n objs homs₂ := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    have h₁ : comp_list (n + 1) objs homs₁ =
        comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
          (fun i : Fin n => homs₁ (Fin.castSucc i)) ≫ homs₁ (Fin.last n) := by
      rw [comp_list_succ]
    have h₂ : comp_list (n + 1) objs homs₂ =
        comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
          (fun i : Fin n => homs₂ (Fin.castSucc i)) ≫ homs₂ (Fin.last n) := by
      rw [comp_list_succ]
    rw [h₁, h₂]
    have h3 : comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
        (fun i : Fin n => homs₁ (Fin.castSucc i)) =
        comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
          (fun i : Fin n => homs₂ (Fin.castSucc i)) := by
      apply ih
      intro i
      exact h (Fin.castSucc i)
    rw [h3, h (Fin.last n)]
/-- Strong congruence for comp_list: if objects are pointwise equal and morphisms
    are compatible with the eqToHom transports, then the compositions are equal
    (up to eqToHom at the endpoints). -/
theorem comp_list_congr_with_eqToHom {n : ℕ}
    (objs₁ objs₂ : Fin (n + 1) → C)
    (homs₁ : ∀ i : Fin n, objs₁ (Fin.castSucc i) ⟶ objs₁ (Fin.succ i))
    (homs₂ : ∀ i : Fin n, objs₂ (Fin.castSucc i) ⟶ objs₂ (Fin.succ i))
    (h_objs : ∀ i : Fin (n + 1), objs₁ i = objs₂ i)
    (h_homs : ∀ i : Fin n,
      eqToHom (h_objs (Fin.castSucc i)).symm ≫ homs₁ i ≫ eqToHom (h_objs (Fin.succ i)) = homs₂ i) :
    eqToHom (h_objs 0).symm ≫ comp_list n objs₁ homs₁ ≫ eqToHom (h_objs (Fin.last n)) =
    comp_list n objs₂ homs₂ := by
  induction n with
  | zero =>
    have h1 : comp_list 0 objs₁ homs₁ = 𝟙 (objs₁ 0) := comp_list_zero objs₁
    have h2 : comp_list 0 objs₂ homs₂ = 𝟙 (objs₂ 0) := comp_list_zero objs₂
    rw [h1, h2]
    have h : eqToHom (h_objs 0).symm ≫ 𝟙 (objs₁ 0) ≫ eqToHom (h_objs 0) = 𝟙 (objs₂ 0) := by
      simp [eqToHom_refl, Category.id_comp]
      <;> rfl
    exact h
  | succ n ih =>
    set objs₁' : Fin (n + 1) → C := fun i : Fin (n + 1) => objs₁ (Fin.castSucc i) with h_objs₁'
    set objs₂' : Fin (n + 1) → C := fun i : Fin (n + 1) => objs₂ (Fin.castSucc i) with h_objs₂'
    set homs₁' : ∀ i : Fin n, objs₁' (Fin.castSucc i) ⟶ objs₁' (Fin.succ i) :=
      fun i : Fin n => homs₁ (Fin.castSucc i) with h_homs₁'
    set homs₂' : ∀ i : Fin n, objs₂' (Fin.castSucc i) ⟶ objs₂' (Fin.succ i) :=
      fun i : Fin n => homs₂ (Fin.castSucc i) with h_homs₂'
    set h_objs' : ∀ i : Fin (n + 1), objs₁' i = objs₂' i :=
      fun i => h_objs (Fin.castSucc i) with h_h_objs'
    let f := comp_list n objs₁' homs₁'
    let g := homs₁ (Fin.last n)
    let f' := comp_list n objs₂' homs₂'
    let g' := homs₂ (Fin.last n)
    let hX : objs₁' 0 = objs₂' 0 := h_objs' 0
    let hY : objs₁' (Fin.last n) = objs₂' (Fin.last n) := h_objs' (Fin.last n)
    let hZ : objs₁ (Fin.succ (Fin.last n)) = objs₂ (Fin.succ (Fin.last n)) := h_objs (Fin.succ (Fin.last n))
    have hY_eq : hY = h_objs (Fin.castSucc (Fin.last n)) := by rfl
    have h_ih : eqToHom hX.symm ≫ f ≫ eqToHom hY = f' :=
      ih objs₁' objs₂' homs₁' homs₂' h_objs' (fun i => h_homs (Fin.castSucc i))
    have h_last : eqToHom hY.symm ≫ g ≫ eqToHom hZ = g' := by
      rw [hY_eq]
      exact h_homs (Fin.last n)
    have h_comp : (eqToHom hX.symm ≫ f ≫ eqToHom hY) ≫ (eqToHom hY.symm ≫ g ≫ eqToHom hZ) =
        eqToHom hX.symm ≫ (f ≫ g) ≫ eqToHom hZ :=
      eqToHom_comp_cancel hX hY hZ f g
    have h_main : eqToHom hX.symm ≫ (f ≫ g) ≫ eqToHom hZ = f' ≫ g' := by
      rw [←h_comp, h_ih, h_last]
    have h1 : comp_list (n + 1) objs₁ homs₁ = f ≫ g := by
      rw [comp_list_succ] <;> rfl
    have h2 : comp_list (n + 1) objs₂ homs₂ = f' ≫ g' := by
      rw [comp_list_succ] <;> rfl
    have h3 : h_objs 0 = hX := by rfl
    have h4 : h_objs (Fin.last (n + 1)) = hZ := by rfl
    rw [h1, h2, h3, h4]
    exact h_main
/-- Helper: extend a comp_list by one more morphism at the end.
    Construct objs' and homs' explicitly by appending one more object and morphism.
    Then use comp_list_succ to show the equality. -/
lemma comp_list_extend {k : ℕ} (objs : Fin (k + 1) → C)
    (homs : ∀ i : Fin k, objs (Fin.castSucc i) ⟶ objs (Fin.succ i))
    {X : C} (g : objs (Fin.last k) ⟶ X) :
    ∃ (objs' : Fin (k + 2) → C)
      (homs' : ∀ i : Fin (k + 1), objs' (Fin.castSucc i) ⟶ objs' (Fin.succ i))
      (h0 : objs' 0 = objs 0)
      (h_last : objs' (Fin.last (k + 1)) = X),
    eqToHom h0.symm ≫ comp_list (k + 1) objs' homs' ≫ eqToHom h_last =
      comp_list k objs homs ≫ g := by
  classical
  let objs' : Fin (k + 2) → C := fun i =>
    if h : i.val ≤ k then
      objs ⟨i.val, by omega⟩
    else
      X
  have h_objs'_castSucc : ∀ (i : Fin (k + 1)), objs' (Fin.castSucc i) = objs i := by
    intro i
    have h1 : (Fin.castSucc i).val ≤ k := by
      simp [Fin.castSucc] <;> omega
    have h2 : objs' (Fin.castSucc i) = objs ⟨(Fin.castSucc i).val, by omega⟩ := by
      dsimp only [objs']
      rw [dif_pos h1]
    rw [h2]
    have h3 : (Fin.castSucc i).val = i.val := by
      simp [Fin.castSucc] <;> omega
    congr <;> omega
  have h_objs'_last : objs' (Fin.last (k + 1)) = X := by
    have h1 : ¬ (Fin.last (k + 1)).val ≤ k := by
      simp [Fin.last] <;> omega
    dsimp only [objs']
    rw [dif_neg h1]
  have h_objs'_succ_lt : ∀ (i : Fin k), objs' (Fin.succ (Fin.castSucc i)) = objs (Fin.succ i) := by
    intro i
    have h_succ_val : (Fin.succ (Fin.castSucc i)).val ≤ k := by
      simp [Fin.castSucc, Fin.succ] <;> omega
    have h4 : objs' (Fin.succ (Fin.castSucc i)) = objs ⟨(Fin.succ (Fin.castSucc i)).val, by omega⟩ := by
      dsimp only [objs']
      rw [dif_pos h_succ_val]
    rw [h4]
    <;> congr <;> simp [Fin.castSucc, Fin.succ] <;> omega
  let homs' : ∀ i : Fin (k + 1), objs' (Fin.castSucc i) ⟶ objs' (Fin.succ i) := by
    intro i
    by_cases h : i.val < k
    · -- i.val < k, so both endpoints are in the original objs
      let j : Fin k := ⟨i.val, h⟩
      have h_domain : objs' (Fin.castSucc i) = objs (Fin.castSucc j) := by
        rw [h_objs'_castSucc]
        <;> congr <;> simp [j, Fin.castSucc] <;> omega
      have h_codomain : objs' (Fin.succ i) = objs (Fin.succ j) := by
        have h_succ_val : (Fin.succ i).val ≤ k := by
          simp [Fin.succ] <;> omega
        have h4 : objs' (Fin.succ i) = objs ⟨(Fin.succ i).val, by omega⟩ := by
          dsimp only [objs']
          rw [dif_pos h_succ_val]
        rw [h4]
        <;> congr <;> simp [j, Fin.succ] <;> omega
      exact eqToHom h_domain ≫ homs j ≫ eqToHom h_codomain.symm
    · -- i.val = k, so this is the last morphism
      have h' : i.val = k := by omega
      have h_domain : objs' (Fin.castSucc i) = objs (Fin.last k) := by
        have h4 : i = Fin.last k := by
          apply Fin.ext <;> simp [Fin.last, h'] <;> omega
        rw [h4, h_objs'_castSucc] <;> rfl
      have h_codomain : objs' (Fin.succ i) = X := by
        have h4 : Fin.succ i = Fin.last (k + 1) := by
          apply Fin.ext <;> simp [Fin.last, Fin.succ, h'] <;> omega
        rw [h4, h_objs'_last]
      exact eqToHom h_domain ≫ g ≫ eqToHom h_codomain.symm
  have h0 : objs' 0 = objs 0 := by
    have h1 : (0 : Fin (k + 2)).val ≤ k := by simp <;> omega
    have h2 : objs' 0 = objs ⟨(0 : Fin (k + 2)).val, by omega⟩ := by
      dsimp only [objs']
      rw [dif_pos h1]
    rw [h2] <;> rfl
  have h_last : objs' (Fin.last (k + 1)) = X := h_objs'_last
  have h_homs_castSucc : ∀ (i : Fin k),
      eqToHom (h_objs'_castSucc (Fin.castSucc i)).symm ≫
      homs' (Fin.castSucc i) ≫
      eqToHom (h_objs'_succ_lt i) = homs i := by
    intro i
    have h_i_lt_k : i.val < k := i.is_lt
    have h1 : (Fin.castSucc i).val < k := by simp [Fin.castSucc] <;> omega
    dsimp only [homs']
    rw [dif_pos h1]
    simp [eqToHom_refl, Category.assoc, Category.comp_id, Category.id_comp]
    <;> rfl
  have h_homs_last :
      eqToHom (h_objs'_castSucc (Fin.last k)).symm ≫
      homs' (Fin.last k) ≫
      eqToHom h_objs'_last = g := by
    have h2 : ¬ (Fin.last k).val < k := by simp [Fin.last] <;> omega
    dsimp only [homs']
    rw [dif_neg h2]
    simp [eqToHom_refl, Category.assoc, Category.comp_id, Category.id_comp]
    <;> rfl
  let objs_mid : Fin (k + 1) → C := fun i : Fin (k + 1) => objs' (Fin.castSucc i)
  let homs_mid : ∀ i : Fin k, objs_mid (Fin.castSucc i) ⟶ objs_mid (Fin.succ i) :=
    fun i : Fin k => homs' (Fin.castSucc i)
  have h_objs_eq : ∀ (i : Fin (k + 1)), objs_mid i = objs i := by
    intro i
    exact h_objs'_castSucc i
  have h_main1 : eqToHom (h_objs_eq 0).symm ≫ comp_list k objs_mid homs_mid ≫ eqToHom (h_objs_eq (Fin.last k)) =
      comp_list k objs homs :=
    comp_list_congr_with_eqToHom objs_mid objs homs_mid homs h_objs_eq h_homs_castSucc
  have h_main2 : comp_list (k + 1) objs' homs' = comp_list k objs_mid homs_mid ≫ homs' (Fin.last k) := by
    rw [comp_list_succ] <;> rfl
  refine' ⟨objs', homs', h0, h_last, _⟩
  have h_step1 : eqToHom h0.symm ≫ comp_list (k + 1) objs' homs' ≫ eqToHom h_last =
      eqToHom h0.symm ≫ (comp_list k objs_mid homs_mid ≫ homs' (Fin.last k)) ≫ eqToHom h_last := by
    exact congr_arg (fun f => eqToHom h0.symm ≫ f ≫ eqToHom h_last) h_main2
  have h_step2 : eqToHom h0.symm ≫ (comp_list k objs_mid homs_mid ≫ homs' (Fin.last k)) ≫ eqToHom h_last =
      (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid) ≫ (homs' (Fin.last k) ≫ eqToHom h_last) := by
    simp [Category.assoc] <;> rfl
  have h_step3 : (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid) ≫ (homs' (Fin.last k) ≫ eqToHom h_last) =
      (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid ≫ eqToHom (h_objs_eq (Fin.last k))) ≫
      (eqToHom (h_objs_eq (Fin.last k)).symm ≫ homs' (Fin.last k) ≫ eqToHom h_last) := by
    let h := h_objs_eq (Fin.last k)
    have h_id : eqToHom h ≫ eqToHom h.symm = 𝟙 (objs_mid (Fin.last k)) := by
      rw [eqToHom_trans, eqToHom_refl]
      <;> rfl
    calc
      (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid) ≫ (homs' (Fin.last k) ≫ eqToHom h_last)
        = (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid) ≫ 𝟙 (objs_mid (Fin.last k)) ≫ (homs' (Fin.last k) ≫ eqToHom h_last) := by
          simp [Category.assoc, Category.id_comp] <;> rfl
      _ = (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid) ≫ (eqToHom h ≫ eqToHom h.symm) ≫ (homs' (Fin.last k) ≫ eqToHom h_last) := by
          rw [h_id] <;> rfl
      _ = (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid ≫ eqToHom h) ≫ (eqToHom h.symm ≫ homs' (Fin.last k) ≫ eqToHom h_last) := by
          simp [Category.assoc] <;> rfl
  have h_final : (eqToHom h0.symm ≫ comp_list k objs_mid homs_mid ≫ eqToHom (h_objs_eq (Fin.last k))) ≫
      (eqToHom (h_objs_eq (Fin.last k)).symm ≫ homs' (Fin.last k) ≫ eqToHom h_last) =
      comp_list k objs homs ≫ g := by
    have h1 : eqToHom h0.symm ≫ comp_list k objs_mid homs_mid ≫ eqToHom (h_objs_eq (Fin.last k)) =
        comp_list k objs homs := h_main1
    have h2 : eqToHom (h_objs_eq (Fin.last k)).symm ≫ homs' (Fin.last k) ≫ eqToHom h_last = g := h_homs_last
    rw [h1, h2]
    <;> rfl
  rw [h_step1, h_step2, h_step3, h_final]
/-- Given two lists of morphisms where the first n of the longer list correspond
    to the shorter list (via eqToHom transport), and the last morphism of the longer
    list corresponds to a given morphism g, then the composition of the longer list
    equals the composition of the shorter list followed by g (up to eqToHom transport). -/
theorem comp_list_snoc {n : ℕ}
    (objs : Fin (n + 1) → C)
    (homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i))
    (objs' : Fin (n + 2) → C)
    (homs' : ∀ i : Fin (n + 1), objs' (Fin.castSucc i) ⟶ objs' (Fin.succ i))
    (h0 : objs' 0 = objs 0)
    (h_corresp : ∀ (i : Fin n),
      ∃ (h1 : objs' (Fin.castSucc (Fin.castSucc i)) = objs (Fin.castSucc i))
        (h2 : objs' (Fin.succ (Fin.castSucc i)) = objs (Fin.succ i)),
      eqToHom h1.symm ≫ homs' (Fin.castSucc i) ≫ eqToHom h2 = homs i)
    {mid : C}
    (h_last_obj : objs' (Fin.last (n + 1)) = mid)
    (g : objs (Fin.last n) ⟶ mid)
    (h_last_hom : ∃ (h1 : objs' (Fin.castSucc (Fin.last n)) = objs (Fin.last n))
        (h2 : objs' (Fin.succ (Fin.last n)) = mid),
      eqToHom h1.symm ≫ homs' (Fin.last n) ≫ eqToHom h2 = g) :
    eqToHom h0.symm ≫ comp_list (n + 1) objs' homs' ≫ eqToHom h_last_obj =
    comp_list n objs homs ≫ g := by
  classical
  let objs'_first : Fin (n + 1) → C := fun i => objs' (Fin.castSucc i)
  let homs'_first : ∀ i : Fin n, objs'_first (Fin.castSucc i) ⟶ objs'_first (Fin.succ i) :=
    fun i => homs' (Fin.castSucc i)
  have h_objs_eq : ∀ (j : Fin (n + 1)), objs'_first j = objs j := by
    intro j
    induction j using Fin.induction with
    | zero =>
      simpa [objs'_first] using h0
    | succ j ih =>
      rcases h_corresp j with ⟨h1, h2, _⟩
      have h_castSucc_succ : objs'_first (Fin.succ j) = objs' (Fin.succ (Fin.castSucc j)) := by
        simp [objs'_first] <;> rfl
      rw [h_castSucc_succ]
      exact h2
  have h_homs_eq : ∀ (i : Fin n),
      eqToHom (h_objs_eq (Fin.castSucc i)).symm ≫ homs'_first i ≫ eqToHom (h_objs_eq (Fin.succ i)) = homs i := by
    intro i
    rcases h_corresp i with ⟨h1, h2, h_hom⟩
    have h_eq1 : h_objs_eq (Fin.castSucc i) = h1 := by exact Subsingleton.elim _ _
    have h_eq2 : h_objs_eq (Fin.succ i) = h2 := by exact Subsingleton.elim _ _
    rw [h_eq1, h_eq2]
    exact h_hom
  rcases h_last_hom with ⟨h1_last, h2_last, h_hom_last⟩
  let hX : objs'_first 0 = objs 0 := h_objs_eq 0
  let hY : objs'_first (Fin.last n) = objs (Fin.last n) := h_objs_eq (Fin.last n)
  have hY_eq : hY = h1_last := by exact Subsingleton.elim _ _
  have hZ_eq : h_last_obj = h2_last := by exact Subsingleton.elim _ _
  let f := comp_list n objs'_first homs'_first
  let g_hom := homs' (Fin.last n)
  have h_ih : eqToHom hX.symm ≫ f ≫ eqToHom hY = comp_list n objs homs :=
    comp_list_congr_with_eqToHom objs'_first objs homs'_first homs h_objs_eq h_homs_eq
  have h_last : eqToHom hY.symm ≫ g_hom ≫ eqToHom h_last_obj = g := by
    have h : eqToHom h1_last.symm ≫ g_hom ≫ eqToHom h2_last = g := h_hom_last
    have hY' : hY = h1_last := hY_eq
    have hZ' : h_last_obj = h2_last := hZ_eq
    rw [hY', hZ'] at *
    exact h
  have h_comp : (eqToHom hX.symm ≫ f ≫ eqToHom hY) ≫ (eqToHom hY.symm ≫ g_hom ≫ eqToHom h_last_obj) =
      eqToHom hX.symm ≫ (f ≫ g_hom) ≫ eqToHom h_last_obj :=
    eqToHom_comp_cancel hX hY h_last_obj f g_hom
  have h_main : eqToHom hX.symm ≫ (f ≫ g_hom) ≫ eqToHom h_last_obj = comp_list n objs homs ≫ g := by
    rw [←h_comp, h_ih, h_last]
  have h1 : comp_list (n + 1) objs' homs' = f ≫ g_hom := comp_list_succ n objs' homs'
  have h2 : h0 = hX := by exact Subsingleton.elim _ _
  rw [h2, h1]
  exact h_main

theorem comp_list_concat_explicit {n m : ℕ}
    (objs₁ : Fin (n + 1) → C)
    (homs₁ : ∀ i : Fin n, objs₁ (Fin.castSucc i) ⟶ objs₁ (Fin.succ i))
    (objs₂ : Fin (m + 1) → C)
    (homs₂ : ∀ i : Fin m, objs₂ (Fin.castSucc i) ⟶ objs₂ (Fin.succ i))
    (h_match : objs₁ (Fin.last n) = objs₂ 0)
    (objs_concat : Fin (n + m + 1) → C)
    (homs_concat : ∀ i : Fin (n + m), objs_concat (Fin.castSucc i) ⟶ objs_concat (Fin.succ i))
    (h_objs_first : ∀ (i : Fin (n + 1)), objs_concat ⟨i.val, by omega⟩ = objs₁ i)
    (h_objs_second : ∀ (i : Fin (m + 1)), objs_concat ⟨n + i.val, by omega⟩ = objs₂ i)
    (h_homs_first : ∀ (i : Fin n),
      eqToHom (h_objs_first (Fin.castSucc i)).symm ≫ homs_concat ⟨i.val, by omega⟩ ≫ eqToHom (h_objs_first (Fin.succ i)) = homs₁ i)
    (h_homs_second : ∀ (i : Fin m),
      eqToHom (h_objs_second (Fin.castSucc i)).symm ≫ homs_concat ⟨n + i.val, by omega⟩ ≫ eqToHom (h_objs_second (Fin.succ i)) = homs₂ i) :
    eqToHom (h_objs_first 0).symm ≫ comp_list (n + m) objs_concat homs_concat ≫ eqToHom (h_objs_second (Fin.last m)) =
    comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list m objs₂ homs₂ := by
  induction m with
  | zero =>
    -- Base case: m = 0
    have h_comp0 : comp_list 0 objs₂ homs₂ = 𝟙 (objs₂ 0) := comp_list_zero objs₂
    have h_last0 : h_objs_second (Fin.last 0) = h_objs_second 0 := by
      simp [Fin.last] <;> rfl
    have h1 : objs_concat ⟨(Fin.last n).val, by omega⟩ = objs_concat ⟨n + 0, by omega⟩ := by
      congr <;> simp [Fin.last] <;> omega
    have h_eq1 : (h_objs_first (Fin.last n)).trans h_match = h_objs_second 0 := by
      exact Subsingleton.elim _ _
    have h_eq_trans : eqToHom (h_objs_second 0) = eqToHom (h_objs_first (Fin.last n)) ≫ eqToHom h_match := by
      rw [←h_eq1, eqToHom_trans] <;> rfl
    have h_congr : eqToHom (h_objs_first 0).symm ≫ comp_list n objs_concat homs_concat ≫ eqToHom (h_objs_first (Fin.last n)) =
        comp_list n objs₁ homs₁ :=
      comp_list_congr_with_eqToHom objs_concat objs₁ homs_concat homs₁ h_objs_first h_homs_first
    have h_goal : eqToHom (h_objs_first 0).symm ≫ comp_list (n + 0) objs_concat homs_concat ≫ eqToHom (h_objs_second (Fin.last 0)) =
        comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list 0 objs₂ homs₂ := by
      have h_comp_n : comp_list (n + 0) objs_concat homs_concat = comp_list n objs_concat homs_concat := by rfl
      have h_rhs : comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list 0 objs₂ homs₂ =
          comp_list n objs₁ homs₁ ≫ eqToHom h_match := by
        rw [h_comp0]
        have h : (comp_list n objs₁ homs₁ ≫ eqToHom h_match) ≫ 𝟙 (objs₂ 0) = comp_list n objs₁ homs₁ ≫ eqToHom h_match := by
          rw [Category.comp_id]
        simpa [Category.assoc] using h
      have h_main : eqToHom (h_objs_first 0).symm ≫ comp_list n objs_concat homs_concat ≫ eqToHom (h_objs_second 0) =
          comp_list n objs₁ homs₁ ≫ eqToHom h_match := by
        have h_eq : eqToHom (h_objs_second 0) = eqToHom (h_objs_first (Fin.last n)) ≫ eqToHom h_match := h_eq_trans
        have h_assoc : eqToHom (h_objs_first 0).symm ≫ comp_list n objs_concat homs_concat ≫ (eqToHom (h_objs_first (Fin.last n)) ≫ eqToHom h_match) =
            (eqToHom (h_objs_first 0).symm ≫ comp_list n objs_concat homs_concat ≫ eqToHom (h_objs_first (Fin.last n))) ≫ eqToHom h_match := by
          simp [Category.assoc] <;> rfl
        have h_goal2 : comp_list n objs_concat homs_concat ≫ eqToHom (h_objs_second 0) =
            comp_list n objs_concat homs_concat ≫ (eqToHom (h_objs_first (Fin.last n)) ≫ eqToHom h_match) := by
          exact congr_arg (fun x => comp_list n objs_concat homs_concat ≫ x) h_eq
        have h_goal : eqToHom (h_objs_first 0).symm ≫ comp_list n objs_concat homs_concat ≫ eqToHom (h_objs_second 0) =
            (eqToHom (h_objs_first 0).symm ≫ comp_list n objs_concat homs_concat ≫ eqToHom (h_objs_first (Fin.last n))) ≫ eqToHom h_match := by
          rw [h_goal2]
          <;> exact h_assoc
        rw [h_goal, h_congr]
      have h_last0_eq : h_objs_second (Fin.last 0) = h_objs_second 0 := by
        simp [Fin.last] <;> rfl
      rw [h_rhs]
      have h_final : eqToHom (h_objs_first 0).symm ≫ comp_list (n + 0) objs_concat homs_concat ≫ eqToHom (h_objs_second (Fin.last 0)) =
          comp_list n objs₁ homs₁ ≫ eqToHom h_match := by
        rw [h_comp_n, h_last0_eq]
        exact h_main
      exact h_final
    exact h_goal
  | succ m ih =>
    -- Inductive step: m → m + 1
    let objs₂' : Fin (m + 1) → C := fun i : Fin (m + 1) => objs₂ (Fin.castSucc i)
    let homs₂' : ∀ i : Fin m, objs₂' (Fin.castSucc i) ⟶ objs₂' (Fin.succ i) :=
      fun i : Fin m => homs₂ (Fin.castSucc i)
    let last_hom : objs₂' (Fin.last m) ⟶ objs₂ (Fin.succ (Fin.last m)) := homs₂ (Fin.last m)
    let objs_concat' : Fin (n + m + 1) → C := fun i : Fin (n + m + 1) => objs_concat ⟨i.val, by omega⟩
    let homs_concat' : ∀ i : Fin (n + m), objs_concat' (Fin.castSucc i) ⟶ objs_concat' (Fin.succ i) :=
      fun i : Fin (n + m) => homs_concat ⟨i.val, by omega⟩
    let h_objs_second' : ∀ (i : Fin (m + 1)), objs_concat' ⟨n + i.val, by omega⟩ = objs₂' i :=
      fun i : Fin (m + 1) => h_objs_second (Fin.castSucc i)
    let h_homs_second' : ∀ (i : Fin m),
        eqToHom (h_objs_second' (Fin.castSucc i)).symm ≫ homs_concat' ⟨n + i.val, by omega⟩ ≫ eqToHom (h_objs_second' (Fin.succ i)) = homs₂' i :=
      fun i : Fin m => h_homs_second (Fin.castSucc i)
    have h_ih' := ih objs₂' homs₂' h_match objs_concat' homs_concat' h_objs_first h_objs_second' h_homs_first h_homs_second'
    have h_last_hom : homs_concat (Fin.last (n + m)) = homs_concat ⟨n + (Fin.last m).val, by omega⟩ := by
      congr <;> simp [Fin.last] <;> omega
    have h_homs_last : eqToHom (h_objs_second (Fin.castSucc (Fin.last m))).symm ≫ homs_concat (Fin.last (n + m)) ≫ eqToHom (h_objs_second (Fin.succ (Fin.last m))) = last_hom := by
      rw [h_last_hom]
      exact h_homs_second (Fin.last m)
    have h_mid_eq : h_objs_second (Fin.castSucc (Fin.last m)) = h_objs_second' (Fin.last m) := by
      simp [h_objs_second', Fin.last] <;> rfl
    have h_end_eq : h_objs_second (Fin.succ (Fin.last m)) = h_objs_second (Fin.last (m + 1)) := by
      simp [Fin.last] <;> rfl
    have h_comp_concat : comp_list (n + m + 1) objs_concat homs_concat =
        comp_list (n + m) objs_concat' homs_concat' ≫ homs_concat (Fin.last (n + m)) := by
      rw [comp_list_succ] <;> rfl
    have h_comp₂ : comp_list (m + 1) objs₂ homs₂ = comp_list m objs₂' homs₂' ≫ last_hom := by
      rw [comp_list_succ] <;> rfl
    let h_mid := h_objs_second' (Fin.last m)
    let h_end := h_objs_second (Fin.last (m + 1))
    have h_g : homs_concat (Fin.last (n + m)) ≫ eqToHom h_end = eqToHom h_mid ≫ last_hom := by
      have h_mid_eq2 : h_objs_second (Fin.castSucc (Fin.last m)) = h_mid := by
        simp [h_objs_second', h_mid, Fin.last] <;> rfl
      have h_end_eq2 : h_objs_second (Fin.succ (Fin.last m)) = h_end := by
        simp [h_end, Fin.last] <;> rfl
      have h : eqToHom (h_objs_second (Fin.castSucc (Fin.last m))).symm ≫ homs_concat (Fin.last (n + m)) ≫ eqToHom (h_objs_second (Fin.succ (Fin.last m))) = last_hom := by
        rw [h_last_hom]
        exact h_homs_second (Fin.last m)
      have h' : eqToHom h_mid.symm ≫ homs_concat (Fin.last (n + m)) ≫ eqToHom h_end = last_hom := by
        rw [h_mid_eq2, h_end_eq2] at h
        exact h
      have h_left : eqToHom h_mid ≫ (eqToHom h_mid.symm ≫ homs_concat (Fin.last (n + m)) ≫ eqToHom h_end) =
          eqToHom h_mid ≫ last_hom := by
        exact congr_arg (fun x => eqToHom h_mid ≫ x) h'
      have h_left_simp : eqToHom h_mid ≫ (eqToHom h_mid.symm ≫ homs_concat (Fin.last (n + m)) ≫ eqToHom h_end) =
          homs_concat (Fin.last (n + m)) ≫ eqToHom h_end := by
        have h1 : eqToHom h_mid ≫ eqToHom h_mid.symm = 𝟙 (objs_concat' (Fin.last (n + m))) := by
          simp [eqToHom_trans] <;> rfl
        simp [Category.assoc, h1] <;> rfl
      rw [h_left_simp] at h_left
      exact h_left
    have h_goal : eqToHom (h_objs_first 0).symm ≫ comp_list (n + m + 1) objs_concat homs_concat ≫ eqToHom h_end =
        comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list (m + 1) objs₂ homs₂ := by
      let f := eqToHom (h_objs_first 0).symm
      let g := comp_list (n + m) objs_concat' homs_concat'
      let last := homs_concat (Fin.last (n + m))
      have h_step1 : eqToHom (h_objs_first 0).symm ≫ comp_list (n + m + 1) objs_concat homs_concat ≫ eqToHom h_end =
          f ≫ (g ≫ last) ≫ eqToHom h_end := by
        rw [h_comp_concat] <;> rfl
      have h_step2 : f ≫ (g ≫ last) ≫ eqToHom h_end = (f ≫ g) ≫ last ≫ eqToHom h_end := by
        simp [Category.assoc] <;> rfl
      have h_step3 : (f ≫ g) ≫ last ≫ eqToHom h_end = (f ≫ g) ≫ (last ≫ eqToHom h_end) := by
        simp [Category.assoc] <;> rfl
      have h_step4 : (f ≫ g) ≫ (last ≫ eqToHom h_end) = (f ≫ g) ≫ (eqToHom h_mid ≫ last_hom) := by
        exact congr_arg (fun x => (f ≫ g) ≫ x) h_g
      have h_step5 : (f ≫ g) ≫ (eqToHom h_mid ≫ last_hom) = (f ≫ g ≫ eqToHom h_mid) ≫ last_hom := by
        simp [Category.assoc] <;> rfl
      have h_step6 : (f ≫ g ≫ eqToHom h_mid) ≫ last_hom = (comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list m objs₂' homs₂') ≫ last_hom := by
        exact congr_arg (fun x => x ≫ last_hom) h_ih'
      have h_step7 : (comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list m objs₂' homs₂') ≫ last_hom =
          comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ (comp_list m objs₂' homs₂' ≫ last_hom) := by
        simp [Category.assoc] <;> rfl
      have h_step8 : comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ (comp_list m objs₂' homs₂' ≫ last_hom) =
          comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ comp_list (m + 1) objs₂ homs₂ := by
        exact congr_arg (fun x => comp_list n objs₁ homs₁ ≫ eqToHom h_match ≫ x) h_comp₂.symm
      rw [h_step1, h_step2, h_step3, h_step4, h_step5, h_step6, h_step7, h_step8]
    exact h_goal

/-- A functor preserves comp_list: applying the functor to the whole composition
    equals composing the functor's action on each morphism. -/

theorem comp_list_functor_map {C D : Type*} [Groupoid C] [Groupoid D]
    (F : C ⥤ D) {n : ℕ}
    (objs : Fin (n + 1) → C)
    (homs : ∀ i : Fin n, objs (Fin.castSucc i) ⟶ objs (Fin.succ i)) :
    F.map (comp_list n objs homs) =
    comp_list n (fun i => F.obj (objs i)) (fun i => F.map (homs i)) := by
  induction n with
  | zero =>
    have h_homs : homs = fun i : Fin 0 => Fin.elim0 i := by
      funext i
      exact Fin.elim0 i
    rw [h_homs]
    simp [comp_list_zero, Functor.map_id]
    <;> rfl
  | succ n ih =>
    have h1 : F.map (comp_list (n + 1) objs homs) =
        F.map (comp_list n (fun i : Fin (n + 1) => objs (Fin.castSucc i))
          (fun i : Fin n => homs (Fin.castSucc i)) ≫ homs (Fin.last n)) := by
      congr
      <;> exact comp_list_succ n objs homs
    rw [h1, Functor.map_comp]
    rw [ih (fun i : Fin (n + 1) => objs (Fin.castSucc i)) (fun i : Fin n => homs (Fin.castSucc i))]
    <;> rfl

end
