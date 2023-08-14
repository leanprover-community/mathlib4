import Mathlib.Topology.Category.Profinite.Basic

universe u

variable {ι : Type u} {X : ι → Type} [∀ i, TopologicalSpace (X i)] [∀ i, Inhabited (X i)]
  (C : Set ((i : ι) → X i))

section General

variable {J K L : ι → Prop} [∀ i, Decidable (J i)] [∀ i, Decidable (K i)] [∀ i, Decidable (L i)]

def ProjRestricts (h : ∀ i, J i → K i) : C.proj K → C.proj J :=
  Homeomorph.setCongr (proj_eq_of_subset C J K h) ∘ ProjRestrict (C.proj K) J

lemma continuous_projRestricts (h : ∀ i, J i → K i) : Continuous (ProjRestricts C h) :=
  Continuous.comp (Homeomorph.continuous _) (continuous_projRestrict _ _)

lemma surjective_projRestricts (h : ∀ i, J i → K i) : Function.Surjective (ProjRestricts C h) :=
  Function.Surjective.comp (Homeomorph.surjective _) (surjective_projRestrict _ _)

variable (J) in
lemma projRestricts_eq_id  :
    ProjRestricts C (fun i (h : J i) ↦ h) = id := by
  ext ⟨_, ⟨y, hy⟩⟩ i
  simp only [ProjRestricts, Homeomorph.setCongr, Homeomorph.homeomorph_mk_coe, ProjRestrict, Proj,
    Function.comp_apply, Equiv.setCongr_apply, Set.val_codRestrict_apply, id_eq, ite_eq_left_iff]
  rw [← hy.2, eq_comm]
  simp only [Proj, Bool.default_bool, ite_eq_right_iff]
  exact fun h₁ h₂ ↦ by simp [h₁] at h₂

lemma projRestricts_eq_comp (hJK : ∀ i, J i → K i) (hKL : ∀ i, K i → L i) :
    ProjRestricts C hJK ∘ ProjRestricts C hKL = ProjRestricts C (fun i ↦ hKL i ∘ hJK i) := by
  ext x i
  dsimp [ProjRestricts, ProjRestrict, Proj, Homeomorph.setCongr]
  simp only [Function.comp_apply, Proj]
  split_ifs with h hh
  · rfl
  · simp only [hJK i h, not_true] at hh
  · rfl

lemma projRestricts_comp_projRestrict (h : ∀ i, J i → K i) :
    ProjRestricts C h ∘ ProjRestrict C K = ProjRestrict C J := by
  ext x i
  dsimp [ProjRestricts, ProjRestrict, Proj, Homeomorph.setCongr, Function.comp_apply, Proj]
  split_ifs with hh hh'
  · rfl
  · simp only [h i hh, not_true] at hh'
  · rfl

end General

section Finsets

variable [∀ i, T2Space (X i)] [∀ i, TotallyDisconnectedSpace (X i)]
  {J K L : Finset ι} [∀ (J : Finset ι) i, Decidable (i ∈ J)]
  [∀ (J : Finset ι), Fintype (C.proj (· ∈ J))] {C} (hC : IsCompact C)

open CategoryTheory Limits Opposite

lemma mem_projRestrict (h : J ⊆ K) (x : C.proj (· ∈ K)) :
    Proj X (· ∈ J) x.val ∈ C.proj (· ∈ J) := by
  obtain ⟨y, hy⟩ := x.prop
  refine ⟨y, ⟨hy.1, ?_⟩⟩
  dsimp [Proj]
  ext i
  split_ifs with hh
  · rw [← hy.2, eq_comm]
    simp only [Proj, ite_eq_left_iff]
    exact fun hK ↦ by simp only [h hh, not_true] at hK
  · rfl

variable (C) in
noncomputable
def FinsetsToProfinite :
    (Finset ι)ᵒᵖ ⥤ Profinite.{u} where
  obj J := Profinite.of (C.proj (· ∈ (unop J)))
  map h := ⟨(ProjRestricts C (leOfHom h.unop)), continuous_projRestricts _ _⟩
  map_id J := by dsimp; simp_rw [projRestricts_eq_id C (· ∈ (unop J))]; rfl
  map_comp _ _ := by dsimp; congr; dsimp; rw [projRestricts_eq_comp]

noncomputable
def FinsetsCone : Cone (FinsetsToProfinite C) where
  pt := @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _
  π := {
    app := fun J ↦ ⟨ProjRestrict C (· ∈ (J.unop)), continuous_projRestrict _ _⟩
    naturality := by
      intro _ _ h
      simp only [Functor.const_obj_obj, FinsetsToProfinite, ProjRestricts, Homeomorph.setCongr,
        Homeomorph.homeomorph_mk_coe, ProjRestrict, Functor.const_obj_map, Category.id_comp]
      congr
      ext x i
      dsimp [Proj]
      split_ifs with h₁ h₂
      · rfl
      · simp only [(leOfHom h.unop h₁), not_true] at h₂
      · rfl
  }

lemma eq_of_forall_proj_eq (a b : C) (h : ∀ (J : Finset ι), ProjRestrict C (· ∈ J) a =
    ProjRestrict C (· ∈ J) b) : a = b := by
  ext i
  specialize h ({i} : Finset ι)
  dsimp [ProjRestrict, Proj] at h
  rw [Subtype.ext_iff] at h
  have hh := congr_fun h i
  simp only [Finset.mem_singleton, Set.val_codRestrict_apply, Function.comp_apply, ite_true] at hh
  exact hh

namespace Profinite

instance isIso_finsetsCone_lift [DecidableEq ι] :
    IsIso ((limitConeIsLimit (FinsetsToProfinite C)).lift (FinsetsCone hC)) :=
  haveI : CompactSpace C := by rwa [← isCompact_iff_compactSpace]
  isIso_of_bijective _
    (by
      refine ⟨fun a b h ↦ ?_, fun a ↦ ?_⟩
      · refine eq_of_forall_proj_eq a b (fun J ↦ ?_)
        apply_fun fun f : (limitCone (FinsetsToProfinite C)).pt => f.val (op J) at h
        exact h
      · suffices : ∃ (x : C), ∀ (J : Finset ι), ProjRestrict C (· ∈ J) x = a.val (op J)
        · obtain ⟨b, hb⟩ := this
          use b
          apply Subtype.ext
          apply funext
          rintro J
          exact hb (unop J)
        have hc : ∀ (J : Finset ι) s, IsClosed ((ProjRestrict C (· ∈ J)) ⁻¹' s)
        · intro J s
          refine IsClosed.preimage (continuous_projRestrict C (· ∈ J)) ?_
          haveI : DiscreteTopology (C.proj (· ∈ J)) := discrete_of_t1_of_finite
          exact isClosed_discrete _
        have H₁ : ∀ (Q₁ Q₂ : Finset ι), Q₁ ≤ Q₂ →
            ProjRestrict C (· ∈ Q₁) ⁻¹' {a.val (op Q₁)} ⊇
            ProjRestrict C (· ∈ Q₂) ⁻¹' {a.val (op Q₂)}
        · intro J K h x hx
          simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx ⊢
          rw [← projRestricts_comp_projRestrict C h, Function.comp_apply,
            hx, ← a.prop (homOfLE h).op]
          rfl
        obtain ⟨x, hx⟩ :
            Set.Nonempty (⋂ (J : Finset ι), ProjRestrict C (· ∈ J) ⁻¹' {a.val (op J)}) :=
          IsCompact.nonempty_iInter_of_directed_nonempty_compact_closed
            (fun J : Finset ι => ProjRestrict C (· ∈ J) ⁻¹' {a.val (op J)}) (directed_of_sup H₁)
            (fun J => (Set.singleton_nonempty _).preimage (surjective_projRestrict _ _))
            (fun J => (hc J {a.val (op J)}).isCompact) fun J => hc J _
        exact ⟨x, Set.mem_iInter.1 hx⟩)

noncomputable
def isoFinsetsConeLift [DecidableEq ι] :
    @Profinite.of C _ (by rwa [← isCompact_iff_compactSpace]) _ _ ≅
    (Profinite.limitCone (FinsetsToProfinite C)).pt :=
  asIso <| (Profinite.limitConeIsLimit _).lift (FinsetsCone hC)

noncomputable
def asLimitFinsetsConeIso [DecidableEq ι] : FinsetsCone hC ≅ Profinite.limitCone _ :=
  Limits.Cones.ext (isoFinsetsConeLift hC) fun _ => rfl

noncomputable
def finsetsCone_isLimit [DecidableEq ι] : CategoryTheory.Limits.IsLimit (FinsetsCone hC) :=
  Limits.IsLimit.ofIsoLimit (Profinite.limitConeIsLimit _) (asLimitFinsetsConeIso hC).symm

end Profinite

end Finsets
