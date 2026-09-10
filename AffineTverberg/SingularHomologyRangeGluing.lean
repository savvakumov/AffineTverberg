import AffineTverberg.SingularHomologyGluing

set_option linter.style.header false

/-!
# Finite descent with the sharp epimorphism endpoint

The fiber argument needs isomorphisms below a cutoff and surjectivity at
the cutoff, not vanishing of the fibers in that last degree. The exact
Mayer--Vietoris sequence preserves precisely this range.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace AffineTverberg.AffChain

variable {C D C' D' : ChainComplex (ModuleCat.{0} ℝ) ℕ}

/-- Isomorphisms strictly below `q`, epimorphisms through `q`. -/
def HomologyRange (φ : C ⟶ D) (q : ℕ) : Prop :=
  (∀ k, k < q → IsIso (homologyMap φ k)) ∧
    ∀ k, k ≤ q → Epi (homologyMap φ k)

theorem homologyRange_of_quasiIso (φ : C ⟶ D) [QuasiIso φ] (q : ℕ) :
    HomologyRange φ q := by
  constructor
  · intro k _
    infer_instance
  · intro k _
    infer_instance

/-- Epimorphisms on the two summands induce an epimorphism on their sum. -/
theorem epi_homologyMap_pairMap (φ : C ⟶ C') (ψ : D ⟶ D') (k : ℕ)
    [Epi (homologyMap φ k)] [Epi (homologyMap ψ k)] :
    Epi (homologyMap (pairMap φ ψ) k) := by
  have hinl : homologyMap (pairInl C D) k ≫ homologyMap (pairMap φ ψ) k =
      homologyMap φ k ≫ homologyMap (pairInl C' D') k := by
    rw [← homologyMap_comp, ← homologyMap_comp, pairInl_comp_pairMap]
  have hinr : homologyMap (pairInr C D) k ≫ homologyMap (pairMap φ ψ) k =
      homologyMap ψ k ≫ homologyMap (pairInr C' D') k := by
    rw [← homologyMap_comp, ← homologyMap_comp, pairInr_comp_pairMap]
  refine ⟨fun {Z} g h heq ↦ ?_⟩
  have hl : homologyMap (pairInl C' D') k ≫ g =
      homologyMap (pairInl C' D') k ≫ h := by
    rw [← cancel_epi (homologyMap φ k), ← Category.assoc, ← Category.assoc,
      ← hinl, Category.assoc, Category.assoc, heq]
  have hr : homologyMap (pairInr C' D') k ≫ g =
      homologyMap (pairInr C' D') k ≫ h := by
    rw [← cancel_epi (homologyMap ψ k), ← Category.assoc, ← Category.assoc,
      ← hinr, Category.assoc, Category.assoc, heq]
  calc
    g = 𝟙 _ ≫ g := (Category.id_comp g).symm
    _ = 𝟙 _ ≫ h := by
      rw [← homology_pair_total C' D' k]
      simp only [Preadditive.add_comp, Category.assoc, hl, hr]
    _ = h := Category.id_comp h

theorem homologyRange_pairMap (φ : C ⟶ C') (ψ : D ⟶ D') {q : ℕ}
    (hφ : HomologyRange φ q) (hψ : HomologyRange ψ q) :
    HomologyRange (pairMap φ ψ) q := by
  constructor
  · intro k hk
    exact isIso_homologyMap_pairMap φ ψ k (hφ.1 k hk) (hψ.1 k hk)
  · intro k hk
    have := hφ.2 k hk
    have := hψ.2 k hk
    exact epi_homologyMap_pairMap φ ψ k

/-- The sharp range is preserved by passage to the third term of a map
of short exact sequences of nonnegative chain complexes. -/
theorem homologyRange_τ₃
    {S₁ S₂ : ShortComplex (ChainComplex (ModuleCat.{0} ℝ) ℕ)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) {q : ℕ}
    (h₁ : HomologyRange φ.τ₁ q) (h₂ : HomologyRange φ.τ₂ q) :
    HomologyRange φ.τ₃ q := by
  constructor
  · intro k hk
    apply HomologySequence.isIso_homologyMap_τ₃ φ hS₁ hS₂ k
      (h₁.2 k hk.le) (h₂.1 k hk)
    · intro j hj
      have : j + 1 = k := hj
      exact h₁.1 j (by omega)
    · intro j hj
      have : j + 1 = k := hj
      have := h₂.1 j (by omega)
      infer_instance
  · intro k hk
    apply HomologySequence.epi_homologyMap_τ₃ φ hS₁ hS₂ k (h₂.2 k hk)
    · intro j hj
      have : j + 1 = k := hj
      exact h₁.2 j (by omega)
    · intro j hj
      have : j + 1 = k := hj
      have := h₂.1 j (by omega)
      infer_instance

theorem homologyRange_comp_left_iff {B : ChainComplex (ModuleCat.{0} ℝ) ℕ}
    (φ : B ⟶ C) (ψ : C ⟶ D) [QuasiIso φ] (q : ℕ) :
    HomologyRange (φ ≫ ψ) q ↔ HomologyRange ψ q := by
  simp only [HomologyRange, homologyMap_comp, isIso_comp_left_iff, epi_comp_iff_of_epi]

theorem homologyRange_comp_right_iff {B : ChainComplex (ModuleCat.{0} ℝ) ℕ}
    (φ : B ⟶ C) (ψ : C ⟶ D) [QuasiIso ψ] (q : ℕ) :
    HomologyRange (φ ≫ ψ) q ↔ HomologyRange φ q := by
  simp only [HomologyRange, homologyMap_comp, isIso_comp_right_iff, epi_comp_iff_of_isIso]

variable {X Y : TopCat.{0}}

/-- The endpoint range concerns the original continuous map, after removing
the two small-chain inclusions in the Mayer--Vietoris comparison. -/
theorem homologyRange_singChainsMap_of_open_cover
    (f : X ⟶ Y) {A B : Set X} {A' B' : Set Y} {q : ℕ}
    (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B')
    (hAo : IsOpen A) (hBo : IsOpen B) (hcov : ∀ x : X, x ∈ A ∨ x ∈ B)
    (hAo' : IsOpen A') (hBo' : IsOpen B') (hcov' : ∀ y : Y, y ∈ A' ∨ y ∈ B')
    (hqa : HomologyRange (singChainsMap (restrictMap f hA)) q)
    (hqb : HomologyRange (singChainsMap (restrictMap f hB)) q)
    (hqi : HomologyRange (singChainsMap (restrictMap f (inter_map f hA hB))) q) :
    HomologyRange (singChainsMap f) q := by
  have hqp := homologyRange_pairMap (singChainsMap (restrictMap f hA))
    (singChainsMap (restrictMap f hB)) hqa hqb
  have hsmall : HomologyRange (smallCxMap A B A' B' f hA hB) q :=
    homologyRange_τ₃ (mvNat f hA hB) (mvShortExact A B) (mvShortExact A' B') hqi hqp
  have hsi : QuasiIso (smallInc (mvCover A B)) :=
    quasiIso_smallInc _ (isOpen_mvCover _ _ hAo hBo) (exists_mem_mvCover _ _ hcov)
  have hsi' : QuasiIso (smallInc (mvCover A' B')) :=
    quasiIso_smallInc _ (isOpen_mvCover _ _ hAo' hBo') (exists_mem_mvCover _ _ hcov')
  apply (homologyRange_comp_left_iff (smallInc (mvCover A B)) (singChainsMap f) q).mp
  rw [← smallCxMap_comp_smallInc A B A' B' f hA hB]
  exact (homologyRange_comp_right_iff _ _ q).mpr hsmall

/-- Transport the sharp range along a commuting square of homeomorphisms. -/
theorem homologyRange_singChainsMap_iff_of_iso {X' Y' : TopCat.{0}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (eX : X ≅ X') (eY : Y ≅ Y')
    (h : eX.hom ≫ g = f ≫ eY.hom) (q : ℕ) :
    HomologyRange (singChainsMap f) q ↔ HomologyRange (singChainsMap g) q := by
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
  rw [← homologyRange_comp_right_iff (singChainsMap f) (singChainsMap eY.hom),
    ← hnat, homologyRange_comp_left_iff]

theorem homologyRange_preimageRestriction_nested (f : X ⟶ Y)
    {S T : Set Y} (h : S ⊆ T) (q : ℕ) :
    HomologyRange (singChainsMap (preimageRestriction (preimageRestriction f T)
      ((Subtype.val : T → Y) ⁻¹' S))) q ↔
    HomologyRange (singChainsMap (preimageRestriction f S)) q :=
  homologyRange_singChainsMap_iff_of_iso
    (preimageRestriction (preimageRestriction f T) ((Subtype.val : T → Y) ⁻¹' S))
    (preimageRestriction f S)
    (TopCat.isoOfHomeo (nestedSubtypeHomeomorph (Set.preimage_mono h)))
    (TopCat.isoOfHomeo (nestedSubtypeHomeomorph h)) rfl q

theorem homologyRange_preimageRestriction_univ_iff (f : X ⟶ Y) (q : ℕ) :
    HomologyRange (singChainsMap (preimageRestriction f Set.univ)) q ↔
      HomologyRange (singChainsMap f) q :=
  homologyRange_singChainsMap_iff_of_iso (preimageRestriction f Set.univ) f
    (TopCat.isoOfHomeo (Homeomorph.Set.univ X))
    (TopCat.isoOfHomeo (Homeomorph.Set.univ Y)) rfl q

/-- The sharp homology range is stable under a two-open union. -/
theorem homologyRange_preimageRestriction_union (f : X ⟶ Y)
    {A B : Set Y} {q : ℕ} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : HomologyRange (singChainsMap (preimageRestriction f A)) q)
    (hB : HomologyRange (singChainsMap (preimageRestriction f B)) q)
    (hI : HomologyRange (singChainsMap (preimageRestriction f (A ∩ B))) q) :
    HomologyRange (singChainsMap (preimageRestriction f (A ∪ B))) q := by
  let g := preimageRestriction f (A ∪ B)
  let U : Set (subSpace (A ∪ B)) := Subtype.val ⁻¹' A
  let W : Set (subSpace (A ∪ B)) := Subtype.val ⁻¹' B
  have hoU : IsOpen U := hAo.preimage continuous_subtype_val
  have hoW : IsOpen W := hBo.preimage continuous_subtype_val
  apply homologyRange_singChainsMap_of_open_cover g
    (A := g ⁻¹' U) (B := g ⁻¹' W) (A' := U) (B' := W)
    (fun _ hx ↦ hx) (fun _ hx ↦ hx)
    (hoU.preimage g.hom.continuous) (hoW.preimage g.hom.continuous)
    (fun x ↦ x.property) hoU hoW (fun y ↦ y.property)
  · exact (homologyRange_preimageRestriction_nested f Set.subset_union_left q).mpr hA
  · exact (homologyRange_preimageRestriction_nested f Set.subset_union_right q).mpr hB
  · exact (homologyRange_preimageRestriction_nested f
      (show A ∩ B ⊆ A ∪ B from fun _ hx ↦ Or.inl hx.1) q).mpr hI

/-- **Finite-open-cover descent with the epimorphism endpoint.** This is
the range required for the sphere projection in the final obstruction. -/
theorem homologyRange_singChainsMap_of_finite_open_cover
    {ι : Type*} (f : X ⟶ Y) (q : ℕ) (t : Finset ι) (U : ι → Set Y)
    (ho : ∀ i ∈ t, IsOpen (U i)) (hcover : (⋃ i ∈ t, U i) = Set.univ)
    (hlocal : ∀ s ⊆ t, s.Nonempty →
      HomologyRange (singChainsMap (preimageRestriction f (⋂ i ∈ s, U i))) q) :
    HomologyRange (singChainsMap f) q := by
  have he : HomologyRange (singChainsMap (preimageRestriction f ∅)) q := by
    have := quasiIso_preimageRestriction_empty f
    exact homologyRange_of_quasiIso _ q
  have h := property_iUnion_of_finite_intersections
    (fun S ↦ HomologyRange (singChainsMap (preimageRestriction f S)) q) he
    (fun _ _ hA hB hqa hqb hqi ↦ homologyRange_preimageRestriction_union f hA hB hqa hqb hqi)
    t U ho hlocal
  rw [hcover] at h
  exact (homologyRange_preimageRestriction_univ_iff f q).mp h

end AffineTverberg.AffChain
