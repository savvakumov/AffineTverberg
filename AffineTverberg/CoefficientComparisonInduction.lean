import AffineTverberg.CoefficientSimplicialMayerVietorisSES
import AffineTverberg.ComparisonInduction

set_option linter.style.header false

/-!
# Simplicial-to-singular comparison over arbitrary fields

This proves the actual comparison chain map is a quasi-isomorphism for every
finite face-closed family and every field. The induction reuses the existing
real geometric open cover and its three homotopy equivalences, and compares
the proved arbitrary-field short exact sequences. No real-coefficient result
is substituted for a characteristic-two homology computation.
-/

noncomputable section

open CategoryTheory Limits AffineTverberg.AffChain AffineTverberg.Simplicial

namespace AffineTverberg.Coefficients

variable (𝕜 : Type) [Field 𝕜]

namespace AffChain

variable {C D C' D' E F : ChainComplex (ModuleCat.{0} 𝕜) ℕ}

/-- Composition on the left distributes over `pairLift 𝕜`. -/
theorem comp_pairLift (θ : F ⟶ E) (α : E ⟶ C) (β : E ⟶ D) :
    θ ≫ pairLift 𝕜 α β = pairLift 𝕜 (θ ≫ α) (θ ≫ β) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

variable {X : TopCat.{0}} {ι : Type} (U : ι → Set X)

/-- The inclusion of the small chains is a monomorphism of chain complexes. -/
instance mono_smallInc : Mono (smallInc 𝕜 U) :=
  HomologicalComplex.mono_of_mono_f _
    (fun n => (ModuleCat.mono_iff_injective _).2 (smallInc_injective 𝕜 U n))

end AffChain

section SimplicialSection

open AffineTverberg.Coefficients.AffChain

variable {V : Type} [Fintype V] [LinearOrder V]

/-! ### Naturality of the comparison map into a subspace -/

variable {K L M : Finset (Finset V)}

omit [LinearOrder V] in
theorem singularChainsMap_eq_singChainsMap (h : K ⊆ L) :
    singularChainsMap 𝕜 h = singChainsMap 𝕜 (baryInclusion h) := rfl

/-- Naturality of `comparisonSub 𝕜` in the subfamily. -/
theorem comparisonSub_naturality (hL : FaceClosed L) (hM : FaceClosed M)
    (hLM : L ⊆ M) (hMK : M ⊆ K) (S : Set ↥(barySpace K))
    (hS : ∀ y : ↥(barySpace K), y.val ∈ barycentricCarrier M → y ∈ S) :
    simplicialChainsInclusion 𝕜 hL hM hLM ≫ comparisonSub 𝕜 hM hMK S hS =
      comparisonSub 𝕜 hL (hLM.trans hMK) S
        (fun y hy => hS y (barycentricCarrier_mono hLM hy)) := by
  have hnat := comparisonChainMap_naturality 𝕜 hL hM hLM
  rw [comparisonSub, ← Category.assoc, ← hnat, Category.assoc,
    singularChainsMap_eq_singChainsMap 𝕜, ← singChainsMap_comp 𝕜]
  rfl

/-! ### The degenerate case of a family with no nonempty face -/

theorem subsingleton_simplicialChains_X (hK : FaceClosed K) (hempty : ∀ t ∈ K, t = ∅) (m : ℕ) :
    Subsingleton ((simplicialChains 𝕜 hK).X m) := by
  have hzero : ∀ x : Finset V → 𝕜, x ∈ chains 𝕜 K (m + 1) → x = 0 := by
    intro x hx
    funext t
    by_contra h
    obtain ⟨htK, htcard⟩ := hx t h
    rw [hempty t htK] at htcard
    simp at htcard
  constructor
  intro c d
  refine chainCoeff_injective 𝕜 hK ?_
  rw [hzero _ (chainCoeff_mem 𝕜 hK c), hzero _ (chainCoeff_mem 𝕜 hK d)]


omit [LinearOrder V] in
theorem subsingleton_singularChains_X (hempty : ∀ t ∈ K, t = ∅) (m : ℕ) :
    Subsingleton ((singularChains 𝕜 K).X m) := by
  have hE : IsEmpty ↥(barycentricCarrier K) := isEmpty_barycentricCarrier hempty
  have hidx : IsEmpty (singIdx (barySpace K) m) := by
    constructor
    intro x
    exact hE.false (simplexMap x (stdSimplex.vertex (0 : Fin (m + 1))))
  have hsub : Subsingleton (singIdx (barySpace K) m →₀ 𝕜) := by
    constructor
    intro f g
    exact Finsupp.ext fun x => hidx.elim x
  exact (chainEquiv 𝕜 (barySpace K) m).injective.subsingleton

/-- The degenerate base case: if no face of `K` is nonempty, both chain
complexes vanish and the comparison map is an isomorphism. -/
theorem quasiIso_comparisonChainMap_of_empty (hK : FaceClosed K) (hempty : ∀ t ∈ K, t = ∅) :
    QuasiIso (comparisonChainMap 𝕜 hK) := by
  have hiso : ∀ m : ℕ, IsIso ((comparisonChainMap 𝕜 hK).f m) := by
    intro m
    have h1 := subsingleton_simplicialChains_X 𝕜 hK hempty m
    have h2 := subsingleton_singularChains_X 𝕜 hempty m
    have hm : Mono ((comparisonChainMap 𝕜 hK).f m) :=
      (ModuleCat.mono_iff_injective _).2 (fun _ _ _ => Subsingleton.elim _ _)
    have he : Epi ((comparisonChainMap 𝕜 hK).f m) :=
      (ModuleCat.epi_iff_surjective _).2 (fun _ => ⟨0, Subsingleton.elim _ _⟩)
    exact isIso_of_mono_of_epi _
  have : IsIso (comparisonChainMap 𝕜 hK) := HomologicalComplex.Hom.isIso_of_components _
  infer_instance

/-! ### The two open sets of the cover -/

section Step

variable {K : Finset (Finset V)} {s : Finset V}



/-- The comparison map of `K.erase s` into the punctured realization. -/
abbrev compErase (hA : FaceClosed (K.erase s)) (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    simplicialChains 𝕜 hA ⟶ singChains 𝕜 (subSpace (coverPunctured K s)) :=
  comparisonSub 𝕜 hA (Finset.erase_subset _ _) (coverPunctured K s)
    (mem_coverPunctured_of_mem_carrier_erase hmax)

/-- The comparison map of the closed simplex of `s` into the open star. -/
abbrev compStar (hBK : s.powerset ⊆ K) :
    simplicialChains 𝕜 (faceClosed_powerset s) ⟶ singChains 𝕜 (subSpace (coverStar K s)) :=
  comparisonSub 𝕜 (faceClosed_powerset s) hBK (coverStar K s)
    (mem_coverStar_of_mem_carrier_powerset K s)

/-- The comparison map of the boundary of `s` into the intersection of the two
sets of the cover. -/
abbrev compBoundary (hCK : boundaryFamily s ⊆ K) :
    simplicialChains 𝕜 (faceClosed_boundaryFamily s) ⟶
      singChains 𝕜 (subSpace (coverPunctured K s ∩ coverStar K s)) :=
  comparisonSub 𝕜 (faceClosed_boundaryFamily s) hCK (coverPunctured K s ∩ coverStar K s)
    (mem_inter_of_mem_carrier_boundaryFamily K s)

theorem quasiIso_compErase (hK : FaceClosed K) (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) (hA : FaceClosed (K.erase s))
    (ihA : QuasiIso (comparisonChainMap 𝕜 hA)) : QuasiIso (compErase 𝕜 hA hmax) :=
  quasiIso_comparisonSub 𝕜 hA (Finset.erase_subset _ _) _ _ ihA
    (puncturedHomotopyEquiv hK hs hmax).symm rfl

theorem quasiIso_compStar (hsK : s ∈ K) (hs : s.Nonempty) (hBK : s.powerset ⊆ K) :
    QuasiIso (compStar 𝕜 hBK) := by
  refine quasiIso_comparisonSub 𝕜 _ hBK _ _ ?_ (starHomotopyEquiv hsK).symm rfl
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  obtain ⟨v, hv⟩ := hs
  exact isIso_comparisonHomologyMap_powerset 𝕜 hv n

theorem quasiIso_compBoundary (hsK : s ∈ K) (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) (hCK : boundaryFamily s ⊆ K)
    (ihC : QuasiIso (comparisonChainMap 𝕜 (faceClosed_boundaryFamily s))) :
    QuasiIso (compBoundary 𝕜 hCK) :=
  quasiIso_comparisonSub 𝕜 _ hCK _ _ ihC
    (starPuncturedBoundaryHomotopyEquiv hs hsK hmax).symm rfl

/-! ### The two commuting squares -/

theorem comparison_comm₁₂ (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    (hA : FaceClosed (K.erase s)) (hCA : boundaryFamily s ⊆ K.erase s)
    (hBK : s.powerset ⊆ K) (hCK : boundaryFamily s ⊆ K) :
    simpMvF 𝕜 (faceClosed_boundaryFamily s) hA (faceClosed_powerset s) hCA
        (Finset.erase_subset _ _) ≫ pairMap 𝕜 (compErase 𝕜 hA hmax) (compStar 𝕜 hBK) =
      compBoundary 𝕜 hCK ≫ mvF 𝕜 (coverPunctured K s) (coverStar K s) := by
  rw [show simpMvF 𝕜 (faceClosed_boundaryFamily s) hA (faceClosed_powerset s) hCA
        (Finset.erase_subset _ _) =
      pairLift 𝕜 (simplicialChainsInclusion 𝕜 (faceClosed_boundaryFamily s) hA hCA)
        (-(simplicialChainsInclusion 𝕜 (faceClosed_boundaryFamily s) (faceClosed_powerset s)
          (Finset.erase_subset _ _))) from rfl,
    show mvF 𝕜 (coverPunctured K s) (coverStar K s) =
      pairLift 𝕜 (subMap 𝕜 Set.inter_subset_left) (-(subMap 𝕜 Set.inter_subset_right)) from rfl,
    pairLift_comp 𝕜, comp_pairLift 𝕜, Preadditive.neg_comp, Preadditive.comp_neg,
    comparisonSub_naturality 𝕜 (faceClosed_boundaryFamily s) hA hCA (Finset.erase_subset _ _),
    comparisonSub_naturality 𝕜 (faceClosed_boundaryFamily s) (faceClosed_powerset s)
      (Finset.erase_subset _ _) hBK,
    comparisonSub_comp_subMap 𝕜, comparisonSub_comp_subMap 𝕜]

theorem comparison_comm₂₃ (hK : FaceClosed K) (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    (hA : FaceClosed (K.erase s)) (hBK : s.powerset ⊆ K) :
    simpMvG 𝕜 hA (faceClosed_powerset s) hK (Finset.erase_subset _ _) hBK ≫
        comparisonSmall 𝕜 hK (faces_small hmax) =
      pairMap 𝕜 (compErase 𝕜 hA hmax) (compStar 𝕜 hBK) ≫
        mvG 𝕜 (coverPunctured K s) (coverStar K s) := by
  rw [← cancel_mono (smallInc 𝕜 (mvCover (coverPunctured K s) (coverStar K s))),
    Category.assoc, Category.assoc, comparisonSmall_comp_smallInc 𝕜, mvG_comp_smallInc 𝕜,
    show simpMvG 𝕜 hA (faceClosed_powerset s) hK (Finset.erase_subset _ _) hBK =
      pairDesc 𝕜 (simplicialChainsInclusion 𝕜 hA hK (Finset.erase_subset _ _))
        (simplicialChainsInclusion 𝕜 (faceClosed_powerset s) hK hBK) from rfl,
    pairDesc_comp 𝕜, pairMap_comp_pairDesc 𝕜, comparisonSub_comp_chainsInclusion 𝕜,
    comparisonSub_comp_chainsInclusion 𝕜,
    comparisonChainMap_naturality 𝕜 hA hK (Finset.erase_subset _ _),
    comparisonChainMap_naturality 𝕜 (faceClosed_powerset s) hK hBK]


/-- The morphism from the simplicial Mayer-Vietoris short exact sequence of
the decomposition `K = (K.erase s) ∪ s.powerset` to the singular Mayer-Vietoris
short exact sequence of the open cover `{coverPunctured K s, coverStar K s}`,
given by the comparison map in each of the three spots. -/
def comparisonMvHom (hK : FaceClosed K) (hmax : ∀ t ∈ K, s ⊆ t → t = s)
    (hA : FaceClosed (K.erase s)) (hCA : boundaryFamily s ⊆ K.erase s)
    (hBK : s.powerset ⊆ K) (hCK : boundaryFamily s ⊆ K) :
    simpMvShortComplex 𝕜 (faceClosed_boundaryFamily s) hA (faceClosed_powerset s) hK hCA
        (Finset.erase_subset _ _) (Finset.erase_subset _ _) hBK ⟶
      mvShortComplex 𝕜 (coverPunctured K s) (coverStar K s) where
  τ₁ := compBoundary 𝕜 hCK
  τ₂ := pairMap 𝕜 (compErase 𝕜 hA hmax) (compStar 𝕜 hBK)
  τ₃ := comparisonSmall 𝕜 hK (faces_small hmax)
  comm₁₂ := (comparison_comm₁₂ 𝕜 hmax hA hCA hBK hCK).symm
  comm₂₃ := (comparison_comm₂₃ 𝕜 hK hmax hA hBK).symm

/-- **The induction step.**  If `s` is a maximal nonempty face of `K` and the
comparison map is a quasi-isomorphism for `K.erase s` and for the boundary of
`s`, then it is one for `K`. -/
theorem quasiIso_comparisonChainMap_step (hK : FaceClosed K) (hsK : s ∈ K) (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) (hA : FaceClosed (K.erase s))
    (ihA : QuasiIso (comparisonChainMap 𝕜 hA))
    (ihC : QuasiIso (comparisonChainMap 𝕜 (faceClosed_boundaryFamily s))) :
    QuasiIso (comparisonChainMap 𝕜 hK) := by
  have hBK : s.powerset ⊆ K := fun t ht => hK s hsK t (Finset.mem_powerset.1 ht)
  have hCA : boundaryFamily s ⊆ K.erase s := fun t ht =>
    Finset.mem_erase.2 ⟨(Finset.mem_erase.1 ht).1, hBK (Finset.erase_subset _ _ ht)⟩
  have hCK : boundaryFamily s ⊆ K := hCA.trans (Finset.erase_subset _ _)
  have := quasiIso_compErase 𝕜 hK hs hmax hA ihA
  have := quasiIso_compStar 𝕜 hsK hs hBK
  have hqC := quasiIso_compBoundary 𝕜 hsK hs hmax hCK ihC
  have hq3 : QuasiIso (comparisonSmall 𝕜 hK (faces_small hmax)) :=
    HomologicalComplex.HomologySequence.quasiIso_τ₃ (comparisonMvHom 𝕜 hK hmax hA hCA hBK hCK)
      (simpMv_shortExact 𝕜 (faceClosed_boundaryFamily s) hA (faceClosed_powerset s) hK hCA
        (Finset.erase_subset _ _) (Finset.erase_subset _ _) hBK
        (subset_erase_union_powerset K s) (mem_boundaryFamily_of_mem_both K s))
      (mvShortExact 𝕜 (coverPunctured K s) (coverStar K s)) hqC (quasiIso_pairMap 𝕜 _ _)
  have hsi : QuasiIso (smallInc 𝕜 (mvCover (coverPunctured K s) (coverStar K s))) :=
    quasiIso_smallInc 𝕜 _
      (isOpen_mvCover _ _ (isOpen_coverPunctured K s) (isOpen_coverStar K s))
      (exists_mem_mvCover _ _ (mem_coverPunctured_union_coverStar hs))
  rw [← comparisonSmall_comp_smallInc 𝕜 hK (faces_small hmax)]
  infer_instance

/-! ### The general comparison theorem -/

/-- **The comparison chain map is a quasi-isomorphism** for every finite
face-closed family. -/
theorem quasiIso_comparisonChainMap {K : Finset (Finset V)} (hK : FaceClosed K) :
    QuasiIso (comparisonChainMap 𝕜 hK) := by
  classical
  induction hn : K.card using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    subst hn
    by_cases hempty : ∀ t ∈ K, t = ∅
    · exact quasiIso_comparisonChainMap_of_empty 𝕜 hK hempty
    · push Not at hempty
      obtain ⟨t₀, ht₀K, ht₀⟩ := hempty
      -- choose a face of maximal cardinality
      obtain ⟨s, hsK, hsmax⟩ := K.exists_max_image Finset.card ⟨t₀, ht₀K⟩
      have hs : s.Nonempty := by
        rw [← Finset.card_pos]
        exact lt_of_lt_of_le (Finset.card_pos.2 ht₀)
          (hsmax t₀ ht₀K)
      have hmax : ∀ t ∈ K, s ⊆ t → t = s := fun t htK hst =>
        (Finset.eq_of_subset_of_card_le hst (hsmax t htK)).symm
      have hA : FaceClosed (K.erase s) := faceClosed_erase_of_max hK hmax
      have hcardA : (K.erase s).card < K.card := Finset.card_erase_lt_of_mem hsK
      have hcardC : (boundaryFamily s).card < K.card := by
        refine lt_of_le_of_lt (Finset.card_le_card ?_) hcardA
        exact fun t ht =>
          Finset.mem_erase.2 ⟨(Finset.mem_erase.1 ht).1,
            hK s hsK t (Finset.mem_powerset.1 (Finset.erase_subset _ _ ht))⟩
      exact quasiIso_comparisonChainMap_step 𝕜 hK hsK hs hmax hA
        (ih _ hcardA hA rfl) (ih _ hcardC (faceClosed_boundaryFamily s) rfl)

/-- **The general comparison theorem.**  For every finite linearly ordered
vertex type, every finite face-closed family `K` and every ordinary degree `n`,
the comparison map from the oriented simplicial homology of `K` to the singular
homology of the barycentric realization of `K` is an isomorphism. -/
theorem isIso_comparisonHomologyMap {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    IsIso (comparisonHomologyMap 𝕜 hK n) := by
  have hq := quasiIso_comparisonChainMap 𝕜 hK
  have h : IsIso (HomologicalComplex.homologyMap (comparisonChainMap 𝕜 hK) n) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact (quasiIso_iff _).1 hq n
  exact h

/-! ### Reduced homology in degree zero

In degree `0` the correct statement is about the *augmented* complexes: the
comparison theorem identifies the reduced degree-zero homology of `K` with the
reduced degree-zero singular homology of the realization, i.e. with the kernel
of Mathlib's singular augmentation.  We record the transfer of invertibility of
the augmentation, which is the reduced vanishing statement. -/

/-- The comparison map in degree `0` intertwines the two augmentations. -/
theorem comparisonHomologyMap_zero_singularAugmentation {K : Finset (Finset V)}
    (hK : FaceClosed K) :
    HomologicalComplex.homologyMap (comparisonChainMap 𝕜 hK) 0 ≫
        (singularAugmentation 𝕜 (barySpace K) :
          (singularChains 𝕜 K).homology 0 ⟶ ModuleCat.of 𝕜 𝕜) =
      augHomology 𝕜 (simplicialChains 𝕜 hK) (simplicialAug 𝕜 hK) (d_simplicialAug 𝕜 hK) := by
  rw [← augHomology_singular_eq 𝕜 K]
  exact comparisonHomologyMap_zero_augHomology 𝕜 hK

/-- **Reduced degree zero.**  If the augmentation of the oriented simplicial
chain complex of `K` induces an isomorphism on degree-zero homology — that is,
if the reduced simplicial homology of `K` vanishes in degree `0` — then
Mathlib's singular augmentation of the realization of `K` is an isomorphism,
i.e. the reduced singular homology of the realization vanishes in degree
`0`. -/
theorem isIso_singularAugmentation_of_simplicial {K : Finset (Finset V)}
    (hK : FaceClosed K)
    (h : IsIso (augHomology 𝕜 (simplicialChains 𝕜 hK)
      (simplicialAug 𝕜 hK) (d_simplicialAug 𝕜 hK))) :
    IsIso (singularAugmentation 𝕜 (barySpace K)) := by
  have hc : IsIso (HomologicalComplex.homologyMap (comparisonChainMap 𝕜 hK) 0) := by
    rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact (quasiIso_iff _).1 (quasiIso_comparisonChainMap 𝕜 hK) 0
  have hcomp : IsIso (HomologicalComplex.homologyMap (comparisonChainMap 𝕜 hK) 0 ≫
      (singularAugmentation 𝕜 (barySpace K) :
        (singularChains 𝕜 K).homology 0 ⟶ ModuleCat.of 𝕜 𝕜)) := by
    rw [comparisonHomologyMap_zero_singularAugmentation 𝕜 hK]
    exact h
  exact IsIso.of_isIso_comp_left
    (HomologicalComplex.homologyMap (comparisonChainMap 𝕜 hK) 0)
    (singularAugmentation 𝕜 (barySpace K))

end Step

end SimplicialSection

end AffineTverberg.Coefficients
