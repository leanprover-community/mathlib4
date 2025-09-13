import Mathlib.RepresentationTheory.Character

universe u
open CategoryTheory LinearMap Representation Module


namespace FDRep
variable {k G : Type u} [Field k] [CommMonoid G]


theorem existsUnique_smul_id_eq_of_simple [IsAlgClosed k] {V : FDRep k G} [Simple V] (f : V ⟶ V) :
    LinearMap.trace k V f.hom.hom • 𝟙 V = finrank k V • f := by
  have : finrank k (V ⟶ V) = 1 := by
    rw[finrank_hom_simple_simple]; simp
  obtain ⟨c,rfl⟩ := endomorphism_simple_eq_smul_id k f
  congr
  rw[Action.smul_hom, Action.id_hom, ModuleCat.hom_smul]
  simp
  sorry




open Module


def end_hom_of_commMonoid (g : G) {V : FDRep k G} : V ⟶ V := _ -- does this exist already

theorem finrank_eq_one_simple_of_commMonoid [IsAlgClosed k]
    {V : FDRep k G} [Simple V] : finrank k V = 1 := by
  have finrank_pos : 0 < finrank k V := by
    by_contra! h
    rw[nonpos_iff_eq_zero, Module.finrank_zero_iff] at h
    have := id_nonzero V
    apply this
    ext a
    change Subsingleton ↑V.V.obj at h
    apply Subsingleton.allEq

  rw[finrank_pos_iff_exists_ne_zero] at finrank_pos
  obtain ⟨x, ne⟩ := finrank_pos
  let W := ↥ (Submodule.span k {x})
  let rho_endo (g : G) : V ⟶ V := ⟨FGModuleCat.ofHom <| V.ρ g, by
    intro h
    ext a
    simp only [FGModuleCat.obj_carrier, FGModuleCat.hom_comp, ModuleCat.hom_ofHom, hom_action_ρ,
      LinearMap.coe_comp, Function.comp_apply]
    rw[← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]⟩
  have invariant (g y) (hy : y ∈ Submodule.span k {x}) : (V.ρ g) y ∈ Submodule.span k {x} := by
    change (rho_endo g) y ∈ Submodule.span k {x}
    obtain ⟨c, eq⟩ := endomorphism_simple_eq_smul_id k <| rho_endo g
    rw[← eq]
    change (c • 𝟙 V).hom.hom y ∈ Submodule.span k {x}
    rw[Action.smul_hom, Action.id_hom, ModuleCat.hom_smul]
    simp only [FGModuleCat.obj_carrier, FGModuleCat.hom_id, smul_apply, id_coe, id_eq]
    exact Submodule.smul_mem (Submodule.span k {x}) c hy
  let w_rho : G →* W →ₗ[k] W := ⟨⟨fun g => (V.ρ g).restrict <| invariant g,
    by ext a; simp⟩,
    by intro g h
       ext a
       aesop⟩
  let WMod := FDRep.of w_rho
  let incl : WMod ⟶ V := ⟨FGModuleCat.ofHom <| Submodule.subtype _, by
    intro g
    norm_cast⟩
  have mono_incl := (forget (FDRep k G)).reflectsMonomorphisms_of_faithful.reflects incl (by
    rw[CategoryTheory.mono_iff_injective]
    rintro ⟨a,ha⟩ ⟨b,hb⟩ eq
    rcases eq
    rfl)
  have incl_nz : incl ≠ 0 := by
    intro h
    have mem : x ∈ Submodule.span k {x} := by simp
    have wrong : incl ⟨x,mem⟩ = (0 : WMod ⟶ V) ⟨x,mem⟩ := by rw[h]
    exact ne wrong
  have incl_isIso := isIso_of_mono_of_nonzero incl_nz
  let incl_iso := asIso incl
  let incl' := (forget₂ (FGModuleCat k) (ModuleCat k)).mapIso <|
    (forget₂ _ (FGModuleCat k)).mapIso incl_iso
  let incl_equiv : WMod ≃ₗ[k] V.V := CategoryTheory.Iso.toLinearEquiv <| incl'
  rw[← LinearEquiv.finrank_eq incl_equiv]
  apply finrank_span_singleton ne



end FDRep
