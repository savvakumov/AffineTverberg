import AffineTverberg.SimplicialMayerVietorisSES
import AffineTverberg.SingularCohomologyDuality

set_option linter.style.header false

/-!
# Gluing actual singular homology equivalences over open covers

The map of the actual Mayer-Vietoris short exact sequences proves the two-open
gluing step. The inclusion of small singular chains is a proved quasi-isomorphism,
so the conclusion concerns the original continuous map, not an auxiliary map.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace AffineTverberg.AffChain

variable {X Y : TopCat.{0}}

/-- Homology equivalence is unchanged by homeomorphic changes of the
source and target which commute with the actual maps. -/
theorem quasiIso_singChainsMap_iff_of_iso {X' Y' : TopCat.{0}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (eX : X ≅ X') (eY : Y ≅ Y')
    (h : eX.hom ≫ g = f ≫ eY.hom) :
    QuasiIso (singChainsMap f) ↔ QuasiIso (singChainsMap g) := by
  have hnat : singChainsMap eX.hom ≫ singChainsMap g =
      singChainsMap f ≫ singChainsMap eY.hom := by
    rw [← singChainsMap_comp, h, singChainsMap_comp]
  have hx : IsIso (singChainsMap eX.hom) := by
    change IsIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℝ)).obj
      (ModuleCat.of ℝ ℝ)).map eX.hom)
    infer_instance
  have hy : IsIso (singChainsMap eY.hom) := by
    change IsIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℝ)).obj
      (ModuleCat.of ℝ ℝ)).map eY.hom)
    infer_instance
  rw [← quasiIso_iff_comp_right (singChainsMap f) (singChainsMap eY.hom),
    ← hnat, quasiIso_iff_comp_left]

/-- Restrict a map to the full preimage of a subset of its target. -/
def preimageRestriction (f : X ⟶ Y) (S : Set Y) :
    subSpace (f ⁻¹' S) ⟶ subSpace S :=
  restrictMap f (fun _ hx ↦ hx)

/-- Remove a redundant ambient-subspace condition. -/
def nestedSubtypeHomeomorph {Z : Type*} [TopologicalSpace Z]
    {S T : Set Z} (h : S ⊆ T) :
    ↥((Subtype.val : T → Z) ⁻¹' S) ≃ₜ S where
  toFun z := ⟨z.val.val, z.property⟩
  invFun z := ⟨⟨z.val, h z.property⟩, z.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Restricting first to `T` and then to `S ⊆ T` induces the same homology
map as restricting directly to `S`, up to the explicit subtype homeomorphisms. -/
theorem quasiIso_preimageRestriction_nested (f : X ⟶ Y)
    {S T : Set Y} (h : S ⊆ T) :
    QuasiIso (singChainsMap (preimageRestriction (preimageRestriction f T)
      ((Subtype.val : T → Y) ⁻¹' S))) ↔
    QuasiIso (singChainsMap (preimageRestriction f S)) := by
  exact quasiIso_singChainsMap_iff_of_iso _ _
    (TopCat.isoOfHomeo (nestedSubtypeHomeomorph (Set.preimage_mono h)))
    (TopCat.isoOfHomeo (nestedSubtypeHomeomorph h)) rfl

/-- A map which induces homology isomorphisms on both opens and their
intersection induces homology isomorphisms on the whole covered space. -/
theorem quasiIso_singChainsMap_of_open_cover
    (f : X ⟶ Y) {A B : Set X} {A' B' : Set Y}
    (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B')
    (hAo : IsOpen A) (hBo : IsOpen B) (hcov : ∀ x : X, x ∈ A ∨ x ∈ B)
    (hAo' : IsOpen A') (hBo' : IsOpen B') (hcov' : ∀ y : Y, y ∈ A' ∨ y ∈ B')
    (hqa : QuasiIso (singChainsMap (restrictMap f hA)))
    (hqb : QuasiIso (singChainsMap (restrictMap f hB)))
    (hqi : QuasiIso (singChainsMap (restrictMap f (inter_map f hA hB)))) :
    QuasiIso (singChainsMap f) := by
  have hqp := quasiIso_pairMap (singChainsMap (restrictMap f hA))
    (singChainsMap (restrictMap f hB))
  have hqsmall : QuasiIso (smallCxMap A B A' B' f hA hB) :=
    HomologySequence.quasiIso_τ₃ (mvNat f hA hB) (mvShortExact A B)
      (mvShortExact A' B') hqi hqp
  have hsi : QuasiIso (smallInc (mvCover A B)) :=
    quasiIso_smallInc _ (isOpen_mvCover _ _ hAo hBo) (exists_mem_mvCover _ _ hcov)
  have hsi' : QuasiIso (smallInc (mvCover A' B')) :=
    quasiIso_smallInc _ (isOpen_mvCover _ _ hAo' hBo') (exists_mem_mvCover _ _ hcov')
  have hcomp : QuasiIso (smallInc (mvCover A B) ≫ singChainsMap f) := by
    rw [← smallCxMap_comp_smallInc A B A' B' f hA hB]
    infer_instance
  exact quasiIso_of_comp_left (smallInc (mvCover A B)) (singChainsMap f)

/-- The restriction to the empty set is a homology equivalence. -/
theorem quasiIso_preimageRestriction_empty (f : X ⟶ Y) :
    QuasiIso (singChainsMap (preimageRestriction f ∅)) := by
  have : IsEmpty (subSpace (f ⁻¹' (∅ : Set Y))) := ⟨fun x ↦ x.property⟩
  have : IsEmpty (subSpace (∅ : Set Y)) := ⟨fun x ↦ x.property⟩
  let e : subSpace (f ⁻¹' (∅ : Set Y)) ≅ subSpace (∅ : Set Y) :=
    TopCat.isoOfHomeo Homeomorph.empty
  have he : preimageRestriction f ∅ = e.hom := by
    ext x
    exact x.property.elim
  rw [he]
  change QuasiIso (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℝ)).obj
    (ModuleCat.of ℝ ℝ)).map e.hom)
  infer_instance

theorem quasiIso_preimageRestriction_univ_iff (f : X ⟶ Y) :
    QuasiIso (singChainsMap (preimageRestriction f Set.univ)) ↔
      QuasiIso (singChainsMap f) :=
  quasiIso_singChainsMap_iff_of_iso _ _
    (TopCat.isoOfHomeo (Homeomorph.Set.univ X))
    (TopCat.isoOfHomeo (Homeomorph.Set.univ Y)) rfl

/-- Homology equivalence on full preimages is stable under a two-open union. -/
theorem quasiIso_preimageRestriction_union (f : X ⟶ Y) {A B : Set Y}
    (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : QuasiIso (singChainsMap (preimageRestriction f A)))
    (hB : QuasiIso (singChainsMap (preimageRestriction f B)))
    (hI : QuasiIso (singChainsMap (preimageRestriction f (A ∩ B)))) :
    QuasiIso (singChainsMap (preimageRestriction f (A ∪ B))) := by
  let g := preimageRestriction f (A ∪ B)
  let U : Set (subSpace (A ∪ B)) := Subtype.val ⁻¹' A
  let W : Set (subSpace (A ∪ B)) := Subtype.val ⁻¹' B
  have hoU : IsOpen U := hAo.preimage continuous_subtype_val
  have hoW : IsOpen W := hBo.preimage continuous_subtype_val
  apply quasiIso_singChainsMap_of_open_cover g
    (A := g ⁻¹' U) (B := g ⁻¹' W) (A' := U) (B' := W)
    (fun _ hx ↦ hx) (fun _ hx ↦ hx)
    (hoU.preimage g.hom.continuous) (hoW.preimage g.hom.continuous)
    (fun x ↦ x.property) hoU hoW (fun y ↦ y.property)
  · exact (quasiIso_preimageRestriction_nested f Set.subset_union_left).mpr hA
  · exact (quasiIso_preimageRestriction_nested f Set.subset_union_right).mpr hB
  · exact (quasiIso_preimageRestriction_nested f
      (show A ∩ B ⊆ A ∪ B from fun _ hx ↦ Or.inl hx.1)).mpr hI

end AffineTverberg.AffChain

namespace AffineTverberg

/-- The finite-cover induction used by local-to-global arguments. Only
nonempty finite intersections are required; the empty union is handled
separately. This lemma is independent of any homology theory. -/
theorem property_iUnion_of_finite_intersections
    {Y ι : Type*} [TopologicalSpace Y]
    (P : Set Y → Prop) (hempty : P ∅)
    (hunion : ∀ A B : Set Y, IsOpen A → IsOpen B →
      P A → P B → P (A ∩ B) → P (A ∪ B))
    (t : Finset ι) (U : ι → Set Y)
    (ho : ∀ i ∈ t, IsOpen (U i))
    (hP : ∀ s ⊆ t, s.Nonempty → P (⋂ i ∈ s, U i)) :
    P (⋃ i ∈ t, U i) := by
  classical
  induction t using Finset.induction_on generalizing U with
  | empty => simpa using hempty
  | @insert a t ha ih =>
    have hta : t ⊆ insert a t := Finset.subset_insert _ _
    have hot : ∀ i ∈ t, IsOpen (U i) := fun i hi ↦ ho i (hta hi)
    have hpU : P (U a) := by
      simpa using hP {a} (by simp) (Finset.singleton_nonempty a)
    have hpT : P (⋃ i ∈ t, U i) :=
      ih U hot (fun s hs hne ↦ hP s (hs.trans hta) hne)
    have hpI : P (⋃ i ∈ t, U a ∩ U i) := by
      apply ih (fun i ↦ U a ∩ U i)
      · exact fun i hi ↦ (ho a (Finset.mem_insert_self _ _)).inter (hot i hi)
      · intro s hs hne
        have hEq : (⋂ i ∈ s, U a ∩ U i) = ⋂ i ∈ insert a s, U i := by
          ext y
          simp only [Set.mem_iInter, Finset.mem_insert, forall_eq_or_imp, Set.mem_inter_iff]
          constructor
          · intro h
            obtain ⟨i, hi⟩ := hne
            exact ⟨(h i hi).1, fun j hj ↦ (h j hj).2⟩
          · exact fun h i hi ↦ ⟨h.1, h.2 i hi⟩
        rw [hEq]
        exact hP (insert a s) (Finset.insert_subset_insert a hs)
          (Finset.insert_nonempty _ _)
    have hinter : U a ∩ (⋃ i ∈ t, U i) = ⋃ i ∈ t, U a ∩ U i := by
      ext y
      simp only [Set.mem_inter_iff, Set.mem_iUnion]
      aesop
    have hres := hunion (U a) (⋃ i ∈ t, U i) (ho a (Finset.mem_insert_self _ _))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hot i hi) hpU hpT
      (hinter.symm ▸ hpI)
    simpa only [Finset.set_biUnion_insert] using hres

end AffineTverberg

namespace AffineTverberg.AffChain

/-- Finite open-cover descent for the actual singular chain map. All
nonempty finite intersections, including empty spaces among them, are handled.
No nerve or general proper-map theorem is assumed. -/
theorem quasiIso_singChainsMap_of_finite_open_cover
    {X Y : TopCat.{0}} {ι : Type*} (f : X ⟶ Y)
    (t : Finset ι) (U : ι → Set Y)
    (ho : ∀ i ∈ t, IsOpen (U i)) (hcover : (⋃ i ∈ t, U i) = Set.univ)
    (hlocal : ∀ s ⊆ t, s.Nonempty →
      QuasiIso (singChainsMap (preimageRestriction f (⋂ i ∈ s, U i)))) :
    QuasiIso (singChainsMap f) := by
  have h := property_iUnion_of_finite_intersections
    (fun S ↦ QuasiIso (singChainsMap (preimageRestriction f S)))
    (quasiIso_preimageRestriction_empty f)
    (fun _ _ hA hB hqa hqb hqi ↦ quasiIso_preimageRestriction_union f hA hB hqa hqb hqi)
    t U ho hlocal
  rw [hcover] at h
  exact (quasiIso_preimageRestriction_univ_iff f).mp h

end AffineTverberg.AffChain
