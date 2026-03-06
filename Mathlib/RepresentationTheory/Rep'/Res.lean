module

public import Mathlib.RepresentationTheory.Rep'.Basic
public import Mathlib.CategoryTheory.Action.Monoidal
public import Mathlib.CategoryTheory.Action.Limits

@[expose] public section

universe t w u v v1 v2

variable {k : Type u} [CommRing k] {G : Type v1} {H : Type v2} [Monoid G] [Monoid H]

open CategoryTheory

namespace Rep

/--
The restriction functor `Rep R G ⥤ Rep R H` for a subgroup `H` of `G`.
-/
abbrev resFunctor (f : H →* G) : Rep.{t} k G ⥤ Rep k H where
  obj A := of (X := A.V) (A.ρ.comp f)
  map f' := ofHom ⟨f'.hom, fun h ↦ by simpa using f'.hom.2 (f h)⟩

abbrev res (f : H →* G) (M : Rep k G) := (resFunctor f).obj M

variable (f : H →* G) (M : Rep k G)

@[simp]
lemma res_obj_ρ :
  (res f M).ρ = (M.ρ.comp f) := rfl

lemma coe_res_obj_ρ' (h : H) : (res f M).ρ h = M.ρ (f h) := rfl

-- @[simp]
lemma res_obj_V : (res f M).V = M.V := rfl

@[simp]
lemma res_map_hom_toLinearMap {M N : Rep k G} (p : M ⟶ N) :
    ((resFunctor f).map p).hom.toLinearMap = p.hom.toLinearMap := rfl

-- def

section

instance : (resFunctor (k := k) f).Faithful where
  map_injective h := by
    ext : 2
    rw [Rep.hom_ext_iff, Representation.IntertwiningMap.ext_iff] at h
    simpa using h

abbrev liftHomOfSurj {X Y : Rep k G} (hf : Function.Surjective f) (f' : res f X ⟶ res f Y) :
    X ⟶ Y :=
  ofHom ⟨f'.hom.toLinearMap, fun g ↦ by
    obtain ⟨h, rfl⟩ := hf g; simpa using f'.hom.2 h⟩

@[simp]
lemma liftHomOfSurj_toLinearMap {X Y : Rep k G} (hf : Function.Surjective f)
    (f' : res f X ⟶ res f Y) : (liftHomOfSurj f hf f').hom.toLinearMap =
      f'.hom.toLinearMap := rfl

lemma full_res (hf : (⇑f).Surjective) : (resFunctor (k := k) f).Full where
  map_surjective {X Y} f' := ⟨liftHomOfSurj f hf f', by
    ext : 2; rw [res_map_hom_toLinearMap, liftHomOfSurj_toLinearMap]⟩

instance : (resFunctor (k := k) f).Additive where
  map_add {_ _} _ _ := by
    ext : 2;
    simp only [add_hom, Representation.IntertwiningMap.add_toLinearMap]
    rfl

instance : (resFunctor (k := k) f).Linear k where
  map_smul {X Y} l r := by
    ext : 2;
    rw [smul_hom, Representation.IntertwiningMap.smul_toLinearMap,
      res_map_hom_toLinearMap, smul_hom, Representation.IntertwiningMap.smul_toLinearMap,
      res_map_hom_toLinearMap]

noncomputable section

variable {G : Type v} [Group G] (A : Rep k G) (S : Subgroup G)
  [S.Normal] [Representation.IsTrivial (A.ρ.comp S.subtype)]

/-- Given a normal subgroup `S ≤ G`, a `G`-representation `ρ` which is trivial on `S` factors
through `G ⧸ S`. -/
abbrev ofQuotient : Rep k (G ⧸ S) := Rep.of (A.ρ.ofQuotient S)

/-- A `G`-representation `A` on which a normal subgroup `S ≤ G` acts trivially induces a
`G ⧸ S`-representation on `A`, and composing this with the quotient map `G → G ⧸ S` gives the
original representation by definition. Useful for typechecking. -/
abbrev resOfQuotientIso [Representation.IsTrivial (A.ρ.comp S.subtype)] :
    (res (QuotientGroup.mk' S) (A.ofQuotient S)) ≅ A := Iso.refl _

end

#exit
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
