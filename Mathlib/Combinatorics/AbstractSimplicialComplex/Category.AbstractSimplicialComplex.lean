import Mathlib.Combinatorics.AbstractSimplicialComplex.FacePoset
import Mathlib.Combinatorics.AbstractSimplicialComplex.FintypeNECat
import Mathlib.Combinatorics.AbstractSimplicialComplex.Equivalence
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Reflective
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.Topology.Category.TopCat.Limits.Basic

universe u v

open AbstractSimplicialComplex SimplicialMap CategoryTheory

/-- Objects of the category of abstract simplicial complexes in a universe `u`.-/
@[nolint checkUnivs]
def AbstractSimplicialComplexCat :=
  Bundled AbstractSimplicialComplex.{u}

namespace AbstractSimplicialComplexCat

instance : CoeSort AbstractSimplicialComplexCat (Type u) where coe := Bundled.α

/-- Construct a bundled `AbstractSimplicialComplexCat` from the underlying type and the typeclass. -/
def of (V : Type u) (K : AbstractSimplicialComplex V) : AbstractSimplicialComplexCat.{u} :=
  @Bundled.of _ V K

/-- The category of abstract simplicial complexes has at least one object (the empty
complex on the empty type).-/
instance : Inhabited AbstractSimplicialComplexCat :=
  ⟨AbstractSimplicialComplexCat.of Empty (@AbstractSimplicialComplex.Bot Empty).1⟩

/-- Morphisms. -/
protected def Hom (C D : AbstractSimplicialComplexCat) :=
  C.2 →ₛ D.2

/-- Make a morphism from a simplicial map. -/
def mk {C D : AbstractSimplicialComplexCat} (f : C.2 →ₛ D.2) :
    AbstractSimplicialComplexCat.Hom C D := f

/-- Category structure on `AbstractSimplicialComplexCat` -/
noncomputable instance category : LargeCategory.{u} AbstractSimplicialComplexCat.{u}
    where
  Hom C D := AbstractSimplicialComplexCat.Hom C D
  id C := SimplicialMap.id C.2
  comp F G := SimplicialMap.comp G F

/-- Forgetful functor to types (sends an abstract simplicial complex on `α` to the type of its
vertices).-/
@[simps]
noncomputable def forget : AbstractSimplicialComplexCat.{u} ⥤ Type u
    where
  obj C := C.2.vertices
  map F := F.vertex_map

/-- Functor sending an abstract simplicial complex to its poset of faces.-/
@[simps]
noncomputable def toFacePoset : AbstractSimplicialComplexCat.{u} ⥤ PartOrd.{u}
    where
  obj C := PartOrd.of C.2.faces
  map F := toOrderHom_faces F
  map_id := fun C => by simp only; unfold toOrderHom_faces
                        apply OrderHom.ext
                        tauto
  map_comp := fun f g => by simp only; unfold toOrderHom_faces
                            apply OrderHom.ext
                            erw [OrderHom.comp_coe]
                            simp only [PartOrd.coe_of]
                            tauto

end AbstractSimplicialComplexCat

/-! The functor from `AbstractSimplicialComplexCat` to `FintypeNECat`.-/

variable {α α' α'' β β' β'' : Type u} [DecidableEq α] [DecidableEq α'] [DecidableEq α'']
  [DecidableEq β] [DecidableEq β'] [DecidableEq β'']

variable (α)

namespace AbstractSimplicialComplex

/-- If `K` is an abstract simplicial on `β` and `α` is a type, then we denote by
`mapFromType α K` the set of maps `f : α → β` that sends every nonempty finset of `α` to a face
of `K`.-/
def mapFromType (K : AbstractSimplicialComplex β) :
    Type u := {f : α → β | ∀ (S : Finset α), S.Nonempty → Finset.image f S ∈ K.faces}

variable {α}

/-- A simplicial map from the maximal abstract simplicial on `α` (the "infinite simplex" on `α`)
to `K` defines an element of `mapFromType α K`.-/
def mapFromType_from_simplicialMap {K : AbstractSimplicialComplex β}
    (f : (⊤ : AbstractSimplicialComplex α) →ₛ K) : mapFromType α K := by
  set g : α → β := by
    intro a
    have hav : a ∈ (⊤ : AbstractSimplicialComplex α).vertices := by
      rw [vertices_top]
      simp only [Set.top_eq_univ, Set.mem_univ]
    exact (f.vertex_map ⟨a, hav⟩).1
  refine ⟨g, ?_⟩
  intro S hSne
  have hSf : S ∈ (⊤ : AbstractSimplicialComplex α).faces := by rw [← faces_top]; exact hSne
  have heq : Finset.image g S = (f.face_map ⟨S, hSf⟩).1 := by
    ext b
    simp only [Finset.mem_image, Subtype.exists]
    constructor
    · intro hb
      match hb with
      | ⟨a, haS, hab⟩ =>
        rw [← hab,  f.face_vertex]
        exists a; exists haS
    · intro hb
      rw [f.face_vertex] at hb
      match hb with
      | ⟨a, has, hab⟩ =>
        exists a
  rw [heq]
  exact (f.face_map ⟨S, hSf⟩).2

/- An element of `mapFromType α K` defines a morphism of abstract simplicial complexes
from the maximal abstract simplicial on `α` to `K`.-/
noncomputable def mapFromType_toSimplicialMap {K : AbstractSimplicialComplex β}
    (f : mapFromType α K) : (⊤ : AbstractSimplicialComplex α) →ₛ K := by
  apply ofMap (f := f.1)
  intro s hsf
  rw [← faces_top] at hsf
  exact f.2 s hsf

/-- If `f` is an element of `mapFromType α K`, then it sends every element of `α` to a vertex
of `K`.-/
lemma mapFromType_image_point {K : AbstractSimplicialComplex β} (f : mapFromType α K) (a : α) :
    f.1 a ∈ K.vertices := by
  rw [mem_vertices, ← Finset.image_singleton]
  exact f.2 _ (Finset.singleton_nonempty _)

/-- The construction `mapFromType` is contravariantly functorial in its first argument.-/
def mapFromType_func1 (f : α → α') (K : AbstractSimplicialComplex β) :
    mapFromType α' K → mapFromType α K := by
  intro g
  refine ⟨g.1 ∘ f, ?_⟩
  intro S hSne
  have heq : Finset.image (g.1 ∘ f) S = Finset.image g.1 (Finset.image f S) := by
    rw [←Finset.coe_inj, Finset.coe_image, Finset.coe_image, Finset.coe_image, Set.image_comp]
  rw [heq]
  apply g.2
  simp only [Finset.image_nonempty]
  exact hSne

variable (α)

lemma mapFromType_func1_id (K : AbstractSimplicialComplex β) :
    mapFromType_func1 (@id α) K = @_root_.id (mapFromType α K) := by
  ext f
  unfold mapFromType_func1
  simp only [Set.mem_setOf_eq, Function.comp_id, Subtype.coe_eta, id_eq]

variable {α}

lemma mapFromType_func1_comp (f : α → α') (g : α' → α'') (K : AbstractSimplicialComplex β) :
    mapFromType_func1 (g ∘ f) K = (mapFromType_func1 f K) ∘ (mapFromType_func1 g K) := by
  ext h
  unfold mapFromType_func1
  rw [← SetCoe.ext_iff]
  simp only [Set.mem_setOf_eq, Function.comp_apply]
  rfl

variable (α)

/-- The construction of `mapFromType` is functorial in its second argument.-/
def mapFromType_func2 {K : AbstractSimplicialComplex β} {L : AbstractSimplicialComplex β'}
    (f : K →ₛ L) : mapFromType α K → mapFromType α L := by
  intro g
  refine ⟨fun a => (f.vertex_map ⟨g.1 a, mapFromType_image_point g a⟩).1, ?_⟩
  intro S hSne
  set T := Finset.image g.1 S
  have hTf : T ∈ K.faces := g.2 S hSne
  have hTeq : (f.face_map ⟨T, hTf⟩).1 = Finset.image (fun a => (f.vertex_map ⟨g.1 a,
    mapFromType_image_point g a⟩).1) S := by
    ext b
    simp only [Set.mem_setOf_eq, Finset.mem_image, Subtype.exists]
    constructor
    · intro hb; rw [f.face_vertex] at hb
      match hb with
      | ⟨a, haS, hab⟩ =>
         simp only [Finset.mem_image] at haS
         match haS with
         | ⟨c, hcS, hca⟩ =>
           exists c
           rw [and_iff_right hcS]
           simp_rw [hca, hab]
    · intro hb
      match hb with
      | ⟨a, haS, hab⟩ =>
        rw [f.face_vertex]
        exists g.1 a
        have h : g.1 a ∈ Finset.image g.1 S := by
          simp only [Set.mem_setOf_eq, Finset.mem_image]
          exists a
        exists h
  rw [← hTeq]
  exact (f.face_map ⟨T, hTf⟩).2

lemma mapFromType_func2_id (K : AbstractSimplicialComplex β) :
    mapFromType_func2 α (id K) = @_root_.id (mapFromType α K) := by
  ext f
  unfold mapFromType_func2
  simp only [Set.mem_setOf_eq, id_eq]
  rw [← SetCoe.ext_iff]
  ext a
  unfold SimplicialMap.id
  simp only [Set.mem_setOf_eq]

lemma mapFromType_func2_comp {K : AbstractSimplicialComplex β} {L : AbstractSimplicialComplex β'}
    {M : AbstractSimplicialComplex β''} (f : K →ₛ L) (g : L →ₛ M) :
    mapFromType_func2 α (g.comp f) = (mapFromType_func2 α g) ∘ (mapFromType_func2 α f) := by
  ext h
  unfold mapFromType_func2 comp
  rw [← SetCoe.ext_iff]
  simp only [Set.mem_setOf_eq, Function.comp_apply, Subtype.coe_eta]

variable {α}

/-- Compatibility between the two functorialities of `mapFromType`.-/
def mapFromType_func1_func2 (g : α → α') {K : AbstractSimplicialComplex β}
    {L : AbstractSimplicialComplex β'} (f : K →ₛ L) :
    (mapFromType_func2 α f) ∘ (mapFromType_func1 g K) =
    (mapFromType_func1 g L) ∘ (mapFromType_func2 α' f) := by
  ext h
  unfold mapFromType_func1 mapFromType_func2
  simp only [Set.mem_setOf_eq, Function.comp_apply]
  rw [← SetCoe.ext_iff]
  simp only
  ext a
  simp only [Function.comp_apply]

end AbstractSimplicialComplex

namespace AbstractSimplicialComplexCat

variable {α}

open Classical

/-- The functor from abstract simplicial complex to presheaves on `FintypeNECat`.-/
noncomputable def toPresheaf : AbstractSimplicialComplexCat ⥤ FintypeNECatᵒᵖ ⥤ Type u where
  obj K :=
   {obj := fun S ↦ mapFromType S.1 K.2
    map := fun f ↦ mapFromType_func1 f.1 K.2
    map_id := fun S => mapFromType_func1_id S.1 K.2
    map_comp := fun f g => mapFromType_func1_comp g.1 f.1 K.2}
  map f :=
   {app := fun S ↦ mapFromType_func2 S.1 f
    naturality := fun _ _ g ↦ mapFromType_func1_func2 g.1 f}
  map_id K := by
    ext S f
    unfold mapFromType_func2
    tauto
  map_comp f g := by
    ext S h
    unfold mapFromType_func2
    tauto

end AbstractSimplicialComplexCat

/-! A left adjoint of `AbstractSimplicialComplexCat.toPresheaf`. -/

namespace FintypeNE

/-- If `S` is a nonempty fintype, then any element of `S` defines a morphism from `S` to `PUnit`
in `FintypeNECatᵒᵖ`.-/
def elementToMap {S : FintypeNECat.{u}ᵒᵖ} (a : S.unop.1) :
    S ⟶ (Opposite.op (FintypeNECat.of PUnit)) := by
  apply Quiver.Hom.op
  exact fun _ => a

lemma elementToMap_naturality {S T : FintypeNECat.{u}ᵒᵖ} (f : S ⟶ T) (a : T.unop.1) :
    elementToMap (f.unop a) = f ≫ (elementToMap a) := by tauto

lemma elementToMap_PUnit (a : (Opposite.op (FintypeNECat.of.{u} PUnit)).unop.1) :
    elementToMap a = CategoryTheory.CategoryStruct.id _ := by
  unfold elementToMap
  apply Quiver.Hom.unop_inj
  simp only [Opposite.unop_op, Quiver.Hom.unop_op, unop_id]
  change _ = fun x => x
  ext x
  exact PUnit.ext a x

end FintypeNE

namespace Presheaf

open FintypeNE

-- Shouldn't this be some Yoneda construction ?
/-- If `F` is a presheaf on `FintypeNECat`, `S` is a nonempty fintype and `e` is an element
of `F.obj S`, then we get a map from `S` to `F PUnit`.-/
def map (F : FintypeNECat.{u}ᵒᵖ ⥤ Type u) {S : FintypeNECatᵒᵖ} (e : F.obj S) :
    S.unop.1 → F.obj (Opposite.op (FintypeNECat.of PUnit)) :=
  fun a => F.map (elementToMap a) e

lemma map_self (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u)
    (a : P.obj (Opposite.op (FintypeNECat.of PUnit))) : ∀ x, map P a x = a := by
  intro x
  unfold map
  rw [elementToMap_PUnit x]
  simp only [FunctorToTypes.map_id_apply]

lemma map_naturality1 (F : FintypeNECat.{u}ᵒᵖ ⥤ Type u) {S T : FintypeNECatᵒᵖ} (f : S ⟶ T)
    (e : F.obj S) : map F (F.map f e) = (map F e) ∘ f.unop := by
  ext a
  unfold map
  rw [← @Function.comp_apply _ _ _ (F.map (elementToMap a)) (F.map f) e]
  change ((F.map f) ≫ _) e = _
  rw [←F.map_comp, ← elementToMap_naturality]
  simp only [Function.comp_apply]

lemma map_naturality2 {P Q : FintypeNECat.{u}ᵒᵖ ⥤ Type u} (f : P ⟶ Q) {S : FintypeNECatᵒᵖ}
    (u : P.obj S) : map Q (f.app S u) =
    (f.app (Opposite.op (FintypeNECat.of PUnit))) ∘ (map P u) := by
  unfold map
  ext a
  rw [← @Function.comp_apply _ _ _ (Q.map (elementToMap a)) (f.app S) u]
  change ((f.app _) ≫ (Q.map _)) u = _
  rw [← f.naturality]
  tauto

open Classical

/-- I honestly forgot what this is doing.-/
noncomputable def mapFactorization {P : FintypeNECat.{u}ᵒᵖ ⥤ Type u}
    {T : FintypeNECat.{u}ᵒᵖ} (e : P.obj T)
    {s : Finset (P.obj (Opposite.op (FintypeNECat.of PUnit)))}
    (hsne : s.Nonempty) (heq : s = Finset.image (map P e) ⊤) :
    T ⟶ (Opposite.op (@FintypeNECat.of s {FinsetCoe.fintype s with
    Nonempty := Finset.Nonempty.to_subtype hsne})) := by
  apply Quiver.Hom.op
  intro a
  have has := a.2
  simp_rw [heq, Finset.mem_image] at has
  exact Classical.choose has

lemma mapFactorization_prop1 {P : FintypeNECat.{u}ᵒᵖ ⥤ Type u} {T : FintypeNECat.{u}ᵒᵖ}
    (e : P.obj T) {s : Finset (P.obj (Opposite.op (FintypeNECat.of PUnit)))} (hsne : s.Nonempty)
    (heq : s = Finset.image (map P e) ⊤) (a : s) :
    map P e ((mapFactorization e hsne heq).unop a) = a := by
  have has := a.2
  simp_rw [heq, Finset.mem_image] at has
  exact (Classical.choose_spec has).2

lemma mapFactorization_prop2 {P : FintypeNECat.{u}ᵒᵖ ⥤ Type u} {T : FintypeNECat.{u}ᵒᵖ}
    (e : P.obj T) {s : Finset (P.obj (Opposite.op (FintypeNECat.of PUnit)))} (hsne : s.Nonempty)
    {g : T ⟶ (Opposite.op (@FintypeNECat.of s {FinsetCoe.fintype s with
    Nonempty := Finset.Nonempty.to_subtype hsne}))}
    (hg : ∀ (a : s), map P e (g.unop a) = a) : map P (P.map g e) = fun a => a.1 := by
  rw [map_naturality1]
  ext a
  simp only [Finset.coe_sort_coe, Opposite.unop_op, Function.comp_apply]
  exact hg a

def faces (F : FintypeNECat.{u}ᵒᵖ ⥤ Type u) :=
  {s : Finset (F.obj (Opposite.op (FintypeNECat.of PUnit))) |
  ∃ (S : FintypeNECatᵒᵖ) (e : F.obj S), s = Finset.image (map F e) ⊤}

lemma faces_down_closed {F : FintypeNECat.{u}ᵒᵖ ⥤ Type u}
    {s t : Finset (F.obj (Opposite.op (FintypeNECat.of PUnit)))} (hsf : s ∈ faces F) (hts : t ⊆ s)
    (htne : Finset.Nonempty t) : t ∈ faces F := by
  match hsf with
  | ⟨S, e, hSs⟩ =>
      set T' := @Finset.filter S.unop.1 (fun a => map F e a ∈ t) _ ⊤
      letI htfin : Fintype T' := Finset.fintypeCoeSort _
      letI htne : Nonempty T' := by
        simp only [Finset.top_eq_univ, Finset.mem_univ, forall_true_left, Finset.mem_filter,
          true_and, nonempty_subtype]
        cases htne with
        | intro a hat =>
          have has := hts hat
          rw [hSs] at has
          simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and] at has
          cases has with
          | intro x hxa =>
            exists x; rw [hxa]; exact hat
      letI : FintypeNE T' := {htfin with Nonempty := htne}
      set T := Opposite.op (FintypeNECat.of T')
      set f : S ⟶ T := by
        apply Quiver.Hom.op
        exact fun ⟨a, _⟩ => a
      set e' := F.map f e
      exists T; exists e'
      ext a
      constructor
      · intro hat
        have has := hts hat
        rw [hSs] at has
        simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and] at has
        match has with
        | ⟨x, hxa⟩ =>
          have hxT : x ∈ T' := by
            simp only [Finset.top_eq_univ, Finset.mem_univ, forall_true_left, Finset.mem_filter,
              hxa, hat, and_self]
          have hxa' : a = map F e' ⟨x, hxT⟩ := by
            rw [←hxa]
            unfold map elementToMap
            simp only [Finset.top_eq_univ, Opposite.unop_op]
            change _ = ((F.map _) ≫ (F.map _)) _
            rw [← F.map_comp]
            tauto
          rw [hxa']
          simp only [Finset.top_eq_univ, Opposite.unop_op, Finset.mem_image, Finset.mem_univ,
            true_and, exists_apply_eq_apply]
      · intro hat
        simp only [Finset.top_eq_univ, Opposite.unop_op, Finset.mem_image, Finset.mem_univ,
          true_and] at hat
        match hat with
        | ⟨⟨x, hxT⟩, hxa⟩ =>
          simp only [Finset.mem_univ, forall_true_left, Finset.mem_filter, true_and] at hxT
          have haT' : a = map F e x := by
            rw [← hxa]
            unfold map elementToMap
            change ((F.map _) ≫ (F.map _)) _ = _
            rw [← F.map_comp]
            tauto
          rw [haT']; exact hxT

/-- Functor from presheavs on `FintypeNECat` to `AbstractSimplicialComplexVat` : action on
objects.-/
def toAbstractSimplicialComplex_obj (F : FintypeNECat.{u}ᵒᵖ ⥤ Type u) :
    AbstractSimplicialComplexCat.{u} := by
  apply AbstractSimplicialComplexCat.of (F.obj (Opposite.op (FintypeNECat.of PUnit)))
  refine {faces := faces F, nonempty_of_mem := ?_, down_closed := faces_down_closed}
  intro s hsf
  unfold faces at hsf
  simp only [Finset.top_eq_univ, Set.mem_setOf_eq] at hsf
  match hsf with
  | ⟨S, e, hSs⟩ =>
    rw [hSs]
    simp only [Finset.image_nonempty]
    rw [Finset.univ_nonempty_iff]
    exact S.unop.2.2

/-- Functor from presheavs on `FintypeNECat` to `AbstractSimplicialComplexVat` : action on
morphism.-/
noncomputable def toAbstractSimplicialComplex_map {F : FintypeNECat.{u}ᵒᵖ ⥤ Type u}
    {G : FintypeNECat.{u}ᵒᵖ ⥤ Type u} (u : F ⟶ G) :
    toAbstractSimplicialComplex_obj F ⟶ toAbstractSimplicialComplex_obj G := by
  set f : (F.obj (Opposite.op (FintypeNECat.of PUnit))) →
      (G.obj (Opposite.op (FintypeNECat.of PUnit))) := u.app _
  apply ofMap (f := f)
  intro s hsf
  match hsf with
  | ⟨S, e, hSs⟩ =>
    exists S
    exists u.app S e
    simp only
    rw [hSs, Finset.image_image]
    unfold map
    ext a
    simp only [Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, Function.comp_apply,
      true_and]
    constructor
    · intro ha
      cases ha with
      | intro x hxa =>
        change ((F.map _) ≫ (u.app _)) _ = _ at hxa
        rw [u.naturality] at hxa
        exists x
    · intro ha
      cases ha with
      | intro x hxa =>
        change ((u.app _) ≫ (G.map _)) _ = _ at hxa
        rw [←u.naturality] at hxa
        exists x


lemma toAbstractSimplicialComplex_map_id (F : FintypeNECat.{u}ᵒᵖ ⥤ Type u) :
    toAbstractSimplicialComplex_map (CategoryStruct.id F) =
    SimplicialMap.id (toAbstractSimplicialComplex_obj F).2 := by
  apply SimplicialMap.ext_vertex
  tauto

lemma toAbstractSimplicialComplex_map_comp {F : FintypeNECat.{u}ᵒᵖ ⥤ Type u}
    {G : FintypeNECat.{u}ᵒᵖ ⥤ Type u} {H : FintypeNECat.{u}ᵒᵖ ⥤ Type u} (u : F ⟶ G) (v : G ⟶ H) :
    toAbstractSimplicialComplex_map (u ≫ v) =
    (toAbstractSimplicialComplex_map u) ≫ (toAbstractSimplicialComplex_map v) := by
  apply SimplicialMap.ext_vertex; tauto

/-- Functor from presheavs on `FintypeNECat` to `AbstractSimplicialComplexVat`.-/
noncomputable def toAbstractSimplicialComplex :
    (FintypeNECat.{u}ᵒᵖ ⥤ Type u) ⥤ AbstractSimplicialComplexCat.{u} where
  obj F := toAbstractSimplicialComplex_obj F
  map u := toAbstractSimplicialComplex_map u
  map_id F := toAbstractSimplicialComplex_map_id F
  map_comp u v := toAbstractSimplicialComplex_map_comp u v

/-- A simpler characterization of the faces of PresheaftoAbstractSimplicialComplex.obj P.-/
lemma toAbstractSimplicialComplex_mem_faces (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u)
    (s : Finset (P.obj (Opposite.op (FintypeNECat.of PUnit)))) (hsne : s.Nonempty) :
    s ∈ (toAbstractSimplicialComplex.obj P).2.faces ↔ (∃ (e : P.obj (Opposite.op
    (@FintypeNECat.of s {FinsetCoe.fintype s with Nonempty := Finset.Nonempty.to_subtype hsne}))),
    map P e = fun a => a.1) := by
  constructor
  . intro hsf
    match hsf with
    | ⟨S, e, hSs⟩ =>
      exists (P.map (mapFactorization e hsne hSs) e)
      exact mapFactorization_prop2 e hsne (mapFactorization_prop1 e hsne hSs)
  . intro hs
    match hs with
    | ⟨e, hes⟩ =>
      exists (Opposite.op (@FintypeNECat.of s {FinsetCoe.fintype s with
        Nonempty := Finset.Nonempty.to_subtype hsne}))
      exists e
      rw [hes]
      ext a
      simp only [Finset.coe_sort_coe, Opposite.unop_op, Finset.top_eq_univ, Finset.mem_image,
        Finset.mem_univ, true_and]
      constructor
      . exact fun has => by exists ⟨a, has⟩
      . intro ha
        match ha with
        | ⟨b, hba⟩ => rw [←hba]; exact b.2

end Presheaf

namespace AbstractSimplicialComplexCattoPresheaf

open AbstractSimplicialComplexCat Presheaf Classical

/-! The unit of the adjunction.-/

/-- Unit.-/
noncomputable def Unit_app_app (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u) (S : FintypeNECatᵒᵖ) :
    P.obj S ⟶ ((toAbstractSimplicialComplex ⋙ toPresheaf).obj P).obj S := by
  intro u
  simp only [Functor.comp_obj]
  unfold toPresheaf mapFromType
  simp only [Set.coe_setOf]
  refine ⟨map P u, ?_⟩
  intro s hsne
  unfold toAbstractSimplicialComplex toAbstractSimplicialComplex_obj Presheaf.faces
  have hsfin : Fintype s := FinsetCoe.fintype s
  letI : FintypeNE s := {hsfin with Nonempty := Finset.Nonempty.to_subtype hsne}
  exists Opposite.op (FintypeNECat.of s)
  set f : S ⟶ Opposite.op (FintypeNECat.of s) := by
    apply Quiver.Hom.op
    exact fun a => a.1
  exists P.map f u
  have heq : map P (P.map f u) = (map P u) ∘ (fun a => a.1) := by
    rw [map_naturality1]
    simp only [Opposite.unop_op, Quiver.Hom.unop_op]
  have hseq : (s : Finset ↑S.unop) = Finset.image
      (fun (a : ↑(Opposite.op (FintypeNECat.of { x // x ∈ s })).unop) => a.1) ⊤ := by
    simp only [Opposite.unop_op, Finset.top_eq_univ]
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · exact fun has => by exists ⟨a, has⟩
    · intro has
      match has with
      | ⟨b, hba⟩ => rw [←hba]; exact b.2
  rw [heq, ← Finset.image_image, ← hseq]

lemma Unit_app_naturality (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u) {S T : FintypeNECatᵒᵖ}
    (f : S ⟶ T) : (P.map f) ≫ (Unit_app_app P T)  = (Unit_app_app P S) ≫
    ((toAbstractSimplicialComplex ⋙ toPresheaf).obj P).map f := by
  ext u
  unfold Unit_app_app
  simp only [Functor.comp_obj, Set.coe_setOf, id_eq, types_comp_apply]
  unfold toAbstractSimplicialComplex toPresheaf
  rw [← SetCoe.ext_iff]
  simp only
  rw [map_naturality1]
  tauto

/-- Unit.-/
noncomputable def Unit_app (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u) :
    P ⟶ (toAbstractSimplicialComplex ⋙ toPresheaf).obj P where
  app := Unit_app_app P
  naturality _ _ := Unit_app_naturality P

lemma Unit_naturality {P Q : FintypeNECat.{u}ᵒᵖ ⥤ Type u} (f : P ⟶ Q) :
    f ≫ (Unit_app Q) = (Unit_app P) ≫ (toAbstractSimplicialComplex ⋙ toPresheaf).map f := by
  ext S u
  unfold Unit_app Unit_app_app
  rw [← SetCoe.ext_iff]
  simp only [Set.mem_setOf_eq, Functor.comp_obj, Set.coe_setOf, id_eq, FunctorToTypes.comp,
    Functor.comp_map]
  rw [map_naturality2]
  tauto

/-- Unit.-/
noncomputable def Unit : (𝟭 (FintypeNECat.{u}ᵒᵖ ⥤ Type u))  ⟶
    toAbstractSimplicialComplex ⋙ toPresheaf
where
  app := Unit_app
  naturality _ _ := Unit_naturality

/-! Counit of the adjunction. -/

noncomputable def Counit_app_aux (K : AbstractSimplicialComplexCat.{u}) :
    ((toPresheaf ⋙ toAbstractSimplicialComplex).obj K).1 → K.1 := by
  intro f
  apply f.1
  simp only [Opposite.unop_op]
  unfold FintypeNECat.of Bundled.of
  simp only
  exact PUnit.unit

noncomputable def Counit_app (K : AbstractSimplicialComplexCat.{u}) :
    ((toPresheaf ⋙ toAbstractSimplicialComplex).obj K) ⟶ K := by
  apply ofMap (f := Counit_app_aux K)
  intro s hsf
  simp only [Functor.comp_obj] at hsf
  unfold toAbstractSimplicialComplex
  match hsf with
  | ⟨S, f, hSs⟩ =>
    have heq : (Counit_app_aux K) ∘ (map (toPresheaf.obj K) f) =
        fun a => f.1 a := by
      ext a
      unfold Counit_app_aux toPresheaf map FintypeNE.elementToMap mapFromType mapFromType_func1
      simp only [Set.coe_setOf, Set.mem_setOf_eq, Functor.comp_obj, Opposite.unop_op, id_eq,
        Function.comp_apply]
      rfl
    erw [hSs, Finset.image_image, heq]
    apply f.2
    simp only [Finset.top_eq_univ]
    rw [Finset.univ_nonempty_iff]
    exact S.unop.2.2

lemma Counit_naturality {K L : AbstractSimplicialComplexCat.{u}} (f : K ⟶ L) :
    ((toPresheaf ⋙ toAbstractSimplicialComplex).map f) ≫ (Counit_app L) =
    (Counit_app K) ≫ f := by
  apply SimplicialMap.ext_vertex
  tauto

noncomputable def Counit :
    toPresheaf ⋙ toAbstractSimplicialComplex ⟶ 𝟭 AbstractSimplicialComplexCat.{u} where
  app := Counit_app
  naturality _ _ := Counit_naturality

/-! Definition of the adjunction.-/

lemma coeur_LT_aux1 (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u)
    (a : P.obj (Opposite.op (FintypeNECat.of PUnit)))
    (f : ((toAbstractSimplicialComplex ⋙ toPresheaf).obj P).obj
    (Opposite.op (FintypeNECat.of PUnit))) (hfa : ∀ x, f.1 x = a)
    (hfv : f ∈ ((toAbstractSimplicialComplex ⋙ toPresheaf ⋙
    toAbstractSimplicialComplex).obj P).2.vertices) :
    ((Counit.app (toAbstractSimplicialComplex.obj P)).vertex_map ⟨f, hfv⟩).1 = a := by
  have x : (Opposite.op (FintypeNECat.of.{u} PUnit)).unop.1 := by
    simp only [Opposite.unop_op]
    exact PUnit.unit
  rw [← hfa x]
  tauto

lemma coeur_LT_aux2 (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u)
    (a : P.obj (Opposite.op (FintypeNECat.of PUnit)))
    (hav : a ∈ (toAbstractSimplicialComplex.obj P).2.vertices) :
    ∀ x, ((toAbstractSimplicialComplex.map (Unit.app P)).vertex_map ⟨a, hav⟩).1.1 x = a := by
  intro x
  unfold toAbstractSimplicialComplex Unit Unit_app Unit_app_app
  simp only [Opposite.unop_op, Set.mem_setOf_eq, Functor.comp_obj, Functor.id_obj,
    Set.coe_setOf, id_eq]
  exact map_self P a _

noncomputable def Coeur : CategoryTheory.Adjunction.CoreUnitCounit toAbstractSimplicialComplex.{u}
    toPresheaf.{u} where
unit := Unit
counit := Counit
left_triangle := by
  ext P
  apply SimplicialMap.ext_vertex
  ext ⟨a, hav⟩
  simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, whiskerRight_app,
    Functor.associator_hom_app, whiskerLeft_app, Category.id_comp, NatTrans.id_app']
  change _ = a
  simp only [Functor.comp_obj, Functor.id_obj] at hav
  rw [@SetCoe.ext_iff _ _ _ ⟨a, hav⟩]
  change SimplicialMap.vertex_map (SimplicialMap.comp _ _) ⟨a, hav⟩ = _
  unfold SimplicialMap.comp
  simp only [Functor.comp_obj, Functor.id_obj, Function.comp_apply]
  rw [← SetCoe.ext_iff]
  change _ = a
  apply coeur_LT_aux1
  apply coeur_LT_aux2
right_triangle := by tauto

noncomputable def Adjunction : CategoryTheory.Adjunction toAbstractSimplicialComplex toPresheaf :=
  CategoryTheory.Adjunction.mkOfUnitCounit Coeur

/-! Reflexivity of the functor `toPresheaf`. This means that it is fully faithful, and we
prove this by proving that the counit of the adjunction is an isomorphism.-/

/-- The inverse of the counit.-/
noncomputable def InverseCounit_app_aux (K : AbstractSimplicialComplexCat.{u}) (a : K.1)
    (hav : a ∈ K.2.vertices) : (toPresheaf.obj K).obj (Opposite.op (FintypeNECat.of PUnit)) := by
  set f : PUnit → K.1 := fun _ => a
  set g : (toPresheaf.obj K).obj (Opposite.op (FintypeNECat.of PUnit)) := by
    refine ⟨f, ?_⟩
    simp only [Opposite.unop_op, Set.mem_setOf_eq]
    intro s hsne
    have heq : Finset.image (fun _ => a) s = {a} := by
      ext b
      simp only [Opposite.unop_op, Finset.mem_image, exists_and_right, Finset.mem_singleton]
      constructor
      · exact fun h => Eq.symm h.2
      · intro h
        rw [h]
        simp only [and_true]
        exact hsne
    erw [heq]
    exact hav
  exact g

noncomputable def InverseCounit_app (K : AbstractSimplicialComplexCat.{u}) :
K ⟶ ((toPresheaf ⋙ toAbstractSimplicialComplex).obj K) where
  vertex_map := by
    intro a
    refine ⟨InverseCounit_app_aux K a.1 a.2, ?_⟩
    rw [mem_vertices]
    unfold toAbstractSimplicialComplex
    simp only [Functor.comp_obj]
    change ∃ _, _
    exists (Opposite.op (FintypeNECat.of PUnit))
    exists InverseCounit_app_aux K a.1 a.2
  face_map := by
    intro ⟨s, hsf⟩
    set t := Finset.image (fun (a : s) => InverseCounit_app_aux K ↑a
      (by rw [mem_vertices_iff]; exists ⟨s, hsf⟩; exact a.2)) ⊤
    refine ⟨t, ?_⟩
    change ∃ _, _
    have hsfin : Fintype s := by
      exact FinsetCoe.fintype s
    have hsne : Nonempty s := by
      simp only [nonempty_subtype]
      exact K.2.nonempty_of_mem hsf
    haveI : FintypeNE s := {hsfin with Nonempty := hsne}
    exists (Opposite.op (FintypeNECat.of s))
    set f : s → K.1 := fun a => ↑a
    exists ⟨f, ?_⟩
    ·  simp only [Opposite.unop_op, Set.mem_setOf_eq]
       intro S hSne
       apply K.2.down_closed hsf
       · intro a ha
         simp only [Finset.mem_image] at ha
         match ha with
         | ⟨b, _, hab⟩ => rw [←hab]; exact b.2
       · simp only [Finset.image_nonempty, hSne]
    · ext b
      simp only [Finset.top_eq_univ, Finset.univ_eq_attach, Finset.mem_image, Finset.mem_attach,
        true_and, Subtype.exists, Opposite.unop_op, Set.mem_setOf_eq, Finset.mem_univ]
      constructor
      · intro hb
        match hb with
        | ⟨a, has, _, hab⟩ =>
          exists ⟨a, has⟩
      · intro hb
        match hb with
        | ⟨⟨a, has⟩, hab⟩ =>
          exists a; exists has
          constructor
          · rw [@Finset.top_eq_univ _ (Finset.Subtype.fintype s)]
            apply @Finset.mem_univ _ (Finset.Subtype.fintype s)
          · tauto
  vertex_face := by tauto
  face_vertex := by
    intro s b
    simp only [Functor.comp_obj, Finset.top_eq_univ, Finset.univ_eq_attach]
    erw [Finset.mem_image]
    constructor
    · intro hb
      match hb with
      | ⟨a, _, hab⟩ =>
        exists a.1; exists a.2
    · intro hb
      match hb with
      | ⟨a, has, hab⟩ =>
      exists ⟨a, has⟩
      simp only [Finset.mem_attach, true_and]
      exact hab

lemma InverseCounit_naturality {K L : AbstractSimplicialComplexCat} (f : K ⟶ L) :
    f ≫ (InverseCounit_app L) = (InverseCounit_app K) ≫
    ((toPresheaf ⋙ toAbstractSimplicialComplex).map f) := by
  apply SimplicialMap.ext_vertex
  tauto

noncomputable def InverseCounit :
𝟭 AbstractSimplicialComplexCat.{u} ⟶ toPresheaf ⋙ toAbstractSimplicialComplex  where
  app := InverseCounit_app
  naturality _ _ := InverseCounit_naturality

noncomputable def Counit_isIso : IsIso Counit where
  out := by
    exists InverseCounit
    constructor
    · ext K
      apply SimplicialMap.ext_vertex
      tauto
    · ext K
      apply SimplicialMap.ext_vertex
      tauto

end AbstractSimplicialComplexCattoPresheaf

namespace AbstractSimplicialComplexCat

open AbstractSimplicialComplexCattoPresheaf Presheaf

/-- The functor `toPresheaf` is fully faithful.-/
noncomputable def toPresheaf_full : Full toPresheaf :=
@rFullOfCounitIsIso _ _ _ _ _ _ Adjunction Counit_isIso

lemma toPresheaf_faithful : Faithful toPresheaf :=
  @R_faithful_of_counit_isIso _ _ _ _ _ _ Adjunction Counit_isIso

/-- The functor `toPresheaf` is reflective.-/
noncomputable instance toPresheaf_reflective : Reflective toPresheaf where
  toFull := toPresheaf_full
  toFaithful := toPresheaf_faithful
  toIsRightAdjoint := {left := toAbstractSimplicialComplex, adj := Adjunction}

/-! The essential image of `toPresheaf` is the full subcategory of concrete presheaves,
i.e. presheaves `P` such that `P S -> (Hom(*,S) -> P(*))` is injective for every `S`. As the
functor is reflective, we know that `P` is in its essential if and only if the unit of the
adjunction is an isomorphism at `P`, so we first prove that this is the case if and only if `P`
is concrete.-/

open Classical

def _root_.Presheaf.isConcrete (P : FintypeNECatᵒᵖ ⥤ Type u) := ∀ (S : FintypeNECatᵒᵖ),
Function.Injective (fun (e : P.obj S) => map P e)

lemma inv_unit_of_isConcrete {P : FintypeNECat.{u}ᵒᵖ ⥤ Type u} {S : FintypeNECatᵒᵖ}
    (f : ((toAbstractSimplicialComplex ⋙ toPresheaf).obj P).obj S) :
    ∃ (e : P.obj S), map P e = f.1 := by
  set T := Finset.image f.1 ⊤
  have hTf : T ∈ (toAbstractSimplicialComplex.obj P).2.faces := by
    refine f.2 ⊤ ?_
    rw [Finset.top_eq_univ, Finset.univ_nonempty_iff]
    exact S.unop.2.2
  have hTne := ((toAbstractSimplicialComplex.obj P).2.nonempty_of_mem hTf)
  rw [toAbstractSimplicialComplex_mem_faces P T hTne] at hTf
  set e := Classical.choose hTf
  set g : Opposite.op (@FintypeNECat.of T {FinsetCoe.fintype T with
    Nonempty := Finset.Nonempty.to_subtype hTne}) ⟶ S := by
    apply Quiver.Hom.op
    intro a
    refine ⟨f.1 a, ?_⟩
    simp only [Set.mem_setOf_eq, Finset.top_eq_univ, Finset.mem_image, Finset.mem_univ, true_and,
      exists_apply_eq_apply, hTne]
  exists P.map g e
  rw [map_naturality1, Classical.choose_spec hTf]
  ext a
  simp only [Set.mem_setOf_eq, Finset.top_eq_univ, Finset.coe_sort_coe, Opposite.unop_op,
    Quiver.Hom.unop_op, Function.comp_apply]

lemma isIso_unit_of_isConcrete {P : FintypeNECat.{u}ᵒᵖ ⥤ Type u} (hconc : isConcrete P) :
    IsIso (Unit.app P) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ (Unit.app P) ?_
  intro S
  refine {out := ?_}
  set I : ((toAbstractSimplicialComplex ⋙ toPresheaf).obj P).obj S → P.obj S :=
    fun f => Classical.choose (inv_unit_of_isConcrete f)
  exists I
  simp only [Functor.id_obj, Functor.comp_obj, Set.mem_setOf_eq]
  constructor
  · ext a
    simp only [types_comp_apply, types_id_apply]
    apply hconc S
    simp only
    rw [Classical.choose_spec (inv_unit_of_isConcrete ((Unit.app P).app S a))]
    tauto
  · ext f
    have hI := Classical.choose_spec (inv_unit_of_isConcrete f)
    simp only [types_comp_apply, types_id_apply]
    unfold AbstractSimplicialComplexCattoPresheaf.Unit Unit_app Unit_app_app
    simp only [Functor.comp_obj, Set.coe_setOf, id_eq]
    rw [← SetCoe.ext_iff]
    simp only
    exact hI

lemma isConcrete_of_unit_isIso {P : FintypeNECat.{u}ᵒᵖ ⥤ Type u} (hiso : IsIso (Unit.app P)) :
    isConcrete P := by
  intro S u v huv
  set eta := Unit.app P
  simp only [Functor.id_obj, Functor.comp_obj] at eta
  have heq : eta.app S u = eta.app S v := by
    simp only
    unfold AbstractSimplicialComplexCattoPresheaf.Unit Unit_app Unit_app_app
    simp only [Functor.comp_obj, Set.coe_setOf, id_eq]
    rw [← SetCoe.ext_iff]
    exact huv
  set eta' := (@CategoryTheory.inv _ _ _ _ eta hiso)
  apply_fun (eta'.app S) at heq
  rw [← @Function.comp_apply _ _ _ (eta'.app S) (eta.app S) u, ← @Function.comp_apply _ _ _
    (eta'.app S) (eta.app S) v] at heq
  change ((eta.app S) ≫ _) u = ((eta.app S) ≫ _) v at heq
  rw [← NatTrans.vcomp_app] at heq
  simp only [NatTrans.vcomp_eq_comp, IsIso.hom_inv_id, NatTrans.id_app, types_id_apply] at heq
  exact heq

lemma isConcrete_iff_essImage (P : FintypeNECat.{u}ᵒᵖ ⥤ Type u) :
    P ∈ Functor.essImage toPresheaf ↔ isConcrete P := by
  constructor
  . exact fun h => isConcrete_of_unit_isIso (Functor.essImage.unit_isIso h)
  . exact fun h => @mem_essImage_of_unit_isIso _ _ _ _ _ _ P (isIso_unit_of_isConcrete h)

end AbstractSimplicialComplexCat

/-! Geometric realization of an abstract simplicial complex: we define it on `FintypeNECat` by
sending `S` to the standard simplex on `S` (see `FintypeNECat.toTopObj`), extend it to the
category of presheaves `FintypeNECatᵒᵖ ⥤ Type u`  by left Kan extension along Yoneda, and then
restrict it to `AbstractSimplicialComplexCat` via the reflective functor `toPresheaf`.
Except that for universe reasons, we do the left Kan extension on the skeleton of `FintypeNECat`.-/

/-- The geometric realization functor on `FintypeNECat.Skeletonᵒᵖ ⥤ Type`.-/
noncomputable def PresheafSkeleton.toTop : (FintypeNECat.Skeletonᵒᵖ ⥤ Type u) ⥤ TopCat.{u} :=
  ColimitAdj.extendAlongYoneda (FintypeNECat.Skeleton.incl ⋙ FintypeNECat.toTop)

/-- The geometric realization on `AbstractSimplicialComplexCat`.-/
noncomputable def AbstractSimplicialComplexCat.toTop :
    AbstractSimplicialComplexCat.{u} ⥤ TopCat.{u} :=
  toPresheaf ⋙ (equivalence_functorCategory _ _ (Type u)
  FintypeNECat.Skeleton.equivalence.op).inverse ⋙ PresheafSkeleton.toTop
