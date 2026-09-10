import AffineTverberg.SingularHomologyRangeGluing

set_option linter.style.header false

/-!
# Mayer--Vietoris with a degree shifted intersection hypothesis

For the local-to-global descent the binary gluing theorem has to be sharp in
the intersection variable: to obtain isomorphisms below `q` and an
epimorphism in degree `q` for a union of two opens, the intersection is only
needed one degree lower. `HomologyRangeShift φ q` is exactly the hypothesis
that the long exact sequence uses about the intersection, and it is vacuous
for `q = 0`, so the degree-zero case of the descent needs nothing at all.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace AffineTverberg.AffChain

variable {C D : ChainComplex (ModuleCat.{0} ℝ) ℕ}

/-- Isomorphisms strictly below `q - 1`, epimorphisms through `q - 1`;
vacuous for `q = 0`. -/
def HomologyRangeShift (φ : C ⟶ D) (q : ℕ) : Prop :=
  (∀ k, k + 1 < q → IsIso (homologyMap φ k)) ∧
    ∀ k, k + 1 ≤ q → Epi (homologyMap φ k)

theorem homologyRangeShift_zero (φ : C ⟶ D) : HomologyRangeShift φ 0 :=
  ⟨fun _ hk => absurd hk (by omega), fun _ hk => absurd hk (by omega)⟩

theorem homologyRangeShift_succ_iff (φ : C ⟶ D) (q : ℕ) :
    HomologyRangeShift φ (q + 1) ↔ HomologyRange φ q := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun k hk => h1 k (by omega), fun k hk => h2 k (by omega)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun k hk => h1 k (by omega), fun k hk => h2 k (by omega)⟩

theorem HomologyRange.shift {φ : C ⟶ D} {q : ℕ} (h : HomologyRange φ q) :
    HomologyRangeShift φ q :=
  ⟨fun k hk => h.1 k (by omega), fun k hk => h.2 k (by omega)⟩

theorem homologyRangeShift_of_quasiIso (φ : C ⟶ D) [QuasiIso φ] (q : ℕ) :
    HomologyRangeShift φ q :=
  (homologyRange_of_quasiIso φ q).shift

theorem homologyRangeShift_comp_left_iff {B : ChainComplex (ModuleCat.{0} ℝ) ℕ}
    (φ : B ⟶ C) (ψ : C ⟶ D) [QuasiIso φ] (q : ℕ) :
    HomologyRangeShift (φ ≫ ψ) q ↔ HomologyRangeShift ψ q := by
  simp only [HomologyRangeShift, homologyMap_comp, isIso_comp_left_iff, epi_comp_iff_of_epi]

theorem homologyRangeShift_comp_right_iff {B : ChainComplex (ModuleCat.{0} ℝ) ℕ}
    (φ : B ⟶ C) (ψ : C ⟶ D) [QuasiIso ψ] (q : ℕ) :
    HomologyRangeShift (φ ≫ ψ) q ↔ HomologyRangeShift φ q := by
  simp only [HomologyRangeShift, homologyMap_comp, isIso_comp_right_iff, epi_comp_iff_of_isIso]

/-- **The sharp form of the third-term theorem.** Only the shifted range is
required of the first terms. -/
theorem homologyRange_τ₃_shift
    {S₁ S₂ : ShortComplex (ChainComplex (ModuleCat.{0} ℝ) ℕ)}
    (φ : S₁ ⟶ S₂) (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact) {q : ℕ}
    (h₁ : HomologyRangeShift φ.τ₁ q) (h₂ : HomologyRange φ.τ₂ q) :
    HomologyRange φ.τ₃ q := by
  constructor
  · intro k hk
    apply HomologySequence.isIso_homologyMap_τ₃ φ hS₁ hS₂ k
      (h₁.2 k (by omega)) (h₂.1 k hk)
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

variable {X Y : TopCat.{0}}

theorem homologyRangeShift_singChainsMap_iff_of_iso {X' Y' : TopCat.{0}}
    (f : X ⟶ Y) (g : X' ⟶ Y') (eX : X ≅ X') (eY : Y ≅ Y')
    (h : eX.hom ≫ g = f ≫ eY.hom) (q : ℕ) :
    HomologyRangeShift (singChainsMap f) q ↔ HomologyRangeShift (singChainsMap g) q := by
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
  rw [← homologyRangeShift_comp_right_iff (singChainsMap f) (singChainsMap eY.hom),
    ← hnat, homologyRangeShift_comp_left_iff]

theorem homologyRangeShift_preimageRestriction_nested (f : X ⟶ Y)
    {S T : Set Y} (h : S ⊆ T) (q : ℕ) :
    HomologyRangeShift (singChainsMap (preimageRestriction (preimageRestriction f T)
      ((Subtype.val : T → Y) ⁻¹' S))) q ↔
    HomologyRangeShift (singChainsMap (preimageRestriction f S)) q :=
  homologyRangeShift_singChainsMap_iff_of_iso
    (preimageRestriction (preimageRestriction f T) ((Subtype.val : T → Y) ⁻¹' S))
    (preimageRestriction f S)
    (TopCat.isoOfHomeo (nestedSubtypeHomeomorph (Set.preimage_mono h)))
    (TopCat.isoOfHomeo (nestedSubtypeHomeomorph h)) rfl q

/-- The two-open comparison with the sharp intersection hypothesis. -/
theorem homologyRange_singChainsMap_of_open_cover_shift
    (f : X ⟶ Y) {A B : Set X} {A' B' : Set Y} {q : ℕ}
    (hA : ∀ x ∈ A, (ConcreteCategory.hom f) x ∈ A')
    (hB : ∀ x ∈ B, (ConcreteCategory.hom f) x ∈ B')
    (hAo : IsOpen A) (hBo : IsOpen B) (hcov : ∀ x : X, x ∈ A ∨ x ∈ B)
    (hAo' : IsOpen A') (hBo' : IsOpen B') (hcov' : ∀ y : Y, y ∈ A' ∨ y ∈ B')
    (hqa : HomologyRange (singChainsMap (restrictMap f hA)) q)
    (hqb : HomologyRange (singChainsMap (restrictMap f hB)) q)
    (hqi : HomologyRangeShift (singChainsMap (restrictMap f (inter_map f hA hB))) q) :
    HomologyRange (singChainsMap f) q := by
  have hqp := homologyRange_pairMap (singChainsMap (restrictMap f hA))
    (singChainsMap (restrictMap f hB)) hqa hqb
  have hsmall : HomologyRange (smallCxMap A B A' B' f hA hB) q :=
    homologyRange_τ₃_shift (mvNat f hA hB) (mvShortExact A B) (mvShortExact A' B') hqi hqp
  have hsi : QuasiIso (smallInc (mvCover A B)) :=
    quasiIso_smallInc _ (isOpen_mvCover _ _ hAo hBo) (exists_mem_mvCover _ _ hcov)
  have hsi' : QuasiIso (smallInc (mvCover A' B')) :=
    quasiIso_smallInc _ (isOpen_mvCover _ _ hAo' hBo') (exists_mem_mvCover _ _ hcov')
  apply (homologyRange_comp_left_iff (smallInc (mvCover A B)) (singChainsMap f) q).mp
  rw [← smallCxMap_comp_smallInc A B A' B' f hA hB]
  exact (homologyRange_comp_right_iff _ _ q).mpr hsmall

/-- **Binary gluing with the sharp intersection hypothesis.** -/
theorem homologyRange_preimageRestriction_union_shift (f : X ⟶ Y)
    {A B : Set Y} {q : ℕ} (hAo : IsOpen A) (hBo : IsOpen B)
    (hA : HomologyRange (singChainsMap (preimageRestriction f A)) q)
    (hB : HomologyRange (singChainsMap (preimageRestriction f B)) q)
    (hI : HomologyRangeShift (singChainsMap (preimageRestriction f (A ∩ B))) q) :
    HomologyRange (singChainsMap (preimageRestriction f (A ∪ B))) q := by
  let g := preimageRestriction f (A ∪ B)
  let U : Set (subSpace (A ∪ B)) := Subtype.val ⁻¹' A
  let W : Set (subSpace (A ∪ B)) := Subtype.val ⁻¹' B
  have hoU : IsOpen U := hAo.preimage continuous_subtype_val
  have hoW : IsOpen W := hBo.preimage continuous_subtype_val
  apply homologyRange_singChainsMap_of_open_cover_shift g
    (A := g ⁻¹' U) (B := g ⁻¹' W) (A' := U) (B' := W)
    (fun _ hx ↦ hx) (fun _ hx ↦ hx)
    (hoU.preimage g.hom.continuous) (hoW.preimage g.hom.continuous)
    (fun x ↦ x.property) hoU hoW (fun y ↦ y.property)
  · exact (homologyRange_preimageRestriction_nested f Set.subset_union_left q).mpr hA
  · exact (homologyRange_preimageRestriction_nested f Set.subset_union_right q).mpr hB
  · exact (homologyRangeShift_preimageRestriction_nested f
      (show A ∩ B ⊆ A ∪ B from fun _ hx ↦ Or.inl hx.1) q).mpr hI

end AffineTverberg.AffChain
