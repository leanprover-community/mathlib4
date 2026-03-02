module

public import Mathlib.RepresentationTheory.Rep.Basic

@[expose] public section

universe w u v1 v2

variable {R : Type u} [Ring R] {G : Type v1} {H : Type v2} [Monoid G] [Monoid H]

open CategoryTheory

namespace Rep

/--
The restriction functor `Rep R G ⥤ Rep R H` for a subgroup `H` of `G`.
-/
def resFunctor (f : H →* G) : Rep R G ⥤ Rep R H := Action.res (ModuleCat R) f

abbrev res (f : H →* G) (M : Rep R G) := (resFunctor f).obj M

-- /--
-- If `M` is an object of `Rep R G` and `φ : H →* G` then `M ↓ φ` is the restriction of the
-- representation `M` to `H`, as an object of `Rep R H`.

-- This is notation for `(Rep.res H).obj M`, which is an abbreviation of
-- `(Action.res (ModuleCat R) H.subtype).obj M`
-- -/
-- notation3:60 M:60 " ↓ " f:61 => (res f).obj M

variable (f : H →* G) (M : Rep R G)

#exit
lemma res_obj_ρ :
  have := res f M
  -- have := this.ρ (k := R)
  sorry = (M.ρ.comp f) := rfl

lemma coe_res_obj_ρ' (h : H) : (M ↓ f).ρ h = M.ρ (f h) := rfl

lemma res_obj_V : (M ↓ f).V = M.V := rfl

@[simp] lemma res_map_hom {M N : Rep R G} (p : M ⟶ N): ((res f).map p).hom = p.hom := rfl

section

local notation3:max "res% " R':max f:max => res (R := R') f

instance : (res% R f).Faithful :=
  inferInstanceAs (Action.res _ _).Faithful

theorem full_res (hf : (⇑f).Surjective) : (res% R f).Full :=
  Action.full_res _ _ hf

instance : (res% R f).Additive :=
  inferInstanceAs <| (Action.res _ _).Additive

instance : (res% R f).Linear R :=
  inferInstanceAs <| (Action.res _ _).Linear R

variable (R) in
@[simps! unit_app_hom_hom counit_app_hom_hom]
noncomputable def indResAdjunction' : indFunctor R f ⊣ res% R f :=
  indResAdjunction ..

variable (R) in
@[simps! counit_app_hom_hom unit_app_hom_hom]
noncomputable abbrev resCoindAdjunction' : res% R f ⊣ coindFunctor R f :=
  resCoindAdjunction ..

instance : (res% R f).IsRightAdjoint :=
  (indResAdjunction' R f).isRightAdjoint

instance : (res% R f).IsLeftAdjoint :=
  (resCoindAdjunction' R f).isLeftAdjoint

instance (H : Subgroup G) : (res% R H.subtype).PreservesProjectiveObjects :=
  inferInstanceAs (Action.res _ _).PreservesProjectiveObjects

end

variable (R) in
def resEquiv (f : H ≃* G) : Rep R G ≌ Rep R H := Action.resEquiv _ f

section
variable (f : H ≃* G)

@[simp] lemma resEquiv_functor : (resEquiv R f).functor = res f := rfl
@[simp] lemma resEquiv_inverse : (resEquiv R f).inverse = res f.symm := rfl

end

/--
The instances above show that the restriction functor `res φ : Rep R G ⥤ Rep R H`
preserves and reflects exactness.
-/
lemma res_map_ShortComplex_Exact (H : Type u) [Group H] (φ : H →* G) (S : ShortComplex (Rep R G)) :
    (S.map (res φ)).Exact ↔ S.Exact := by
  rw [ShortComplex.exact_map_iff_of_faithful]

/--
An object of `Rep R G` is zero iff the underlying `R`-module is zero.
-/
lemma isZero_iff (M : Rep R G) : IsZero M ↔ IsZero (M.V) := by
  simp only [IsZero.iff_id_eq_zero]
  apply Action.hom_ext_iff

/--
An object of `Rep R G` is zero iff its restriction to `H` is zero.
-/
lemma isZero_res_iff (M : Rep R G) {H : Type u} [Group H] (φ : H →* G) :
    IsZero (M ↓ φ) ↔ IsZero M := by
  rw [isZero_iff, isZero_iff, Rep.res_obj_V]

/--
The restriction functor `res φ : Rep R G ⥤ Rep R H` takes short exact sequences to short
exact sequences.
-/
@[simp] lemma shortExact_res {H : Type u} [Group H] (φ : H →* G) {S : ShortComplex (Rep R G)} :
    (S.map (Rep.res φ)).ShortExact ↔ S.ShortExact := by
  constructor
  · intro h
    have h₁ := h.1
    have h₂ := h.2
    have h₃ := h.3
    rw [ShortComplex.exact_map_iff_of_faithful] at h₁
    simp only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_f,
      Functor.mono_map_iff_mono, ShortComplex.map_X₃, ShortComplex.map_g,
      Functor.epi_map_iff_epi] at h₂ h₃
    exact {
      exact := h₁
      mono_f := h₂
      epi_g := h₃
    }
  · intro h
    have h₁ := h.1
    have h₂ := h.2
    have h₃ := h.3
    exact {
      exact := by rwa [ShortComplex.exact_map_iff_of_faithful]
      mono_f := by simpa using h₂
      epi_g := by simpa using h₃
    }

@[simp] lemma norm_hom_res [Fintype G] [Fintype H] (M : Rep R G) (e : H ≃* G) :
    (M ↓ e.toMonoidHom).norm.hom = M.norm.hom := by
  ext
  simp [res_obj_V, Representation.norm, res_obj_ρ',← e.toEquiv.sum_comp]

end Rep
