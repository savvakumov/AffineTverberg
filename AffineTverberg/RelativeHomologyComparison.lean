import AffineTverberg.RelativeSingularHomology
import AffineTverberg.ComparisonInduction

set_option linter.style.header false

/-!
# Relative simplicial-to-singular comparison

For a finite subcomplex pair `L ⊆ K`, the relative simplicial complex is the
actual cokernel of the inclusion of oriented simplicial chains. Its comparison
to the actual relative singular complex is induced by the already verified
absolute comparisons. The map is a quasi-isomorphism in all degrees, by the
two short exact sequences. Neither excision nor duality is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

open AffineTverberg.AffChain

variable {V : Type} [Fintype V] [LinearOrder V]
  {L K : Finset (Finset V)}

/-- The actual realized subcomplex, as a subset of the realized complex. -/
def subcomplexRealization (L K : Finset (Finset V)) : Set ↥(barySpace K) :=
  Subtype.val ⁻¹' barycentricCarrier L

/-- The abstract realization and its image as a subspace are homeomorphic. -/
def subcomplexRealizationHomeomorph (h : L ⊆ K) :
    ↥(barySpace L) ≃ₜ ↥(subcomplexRealization L K) where
  toFun x := ⟨⟨x.1, barycentricCarrier_mono h x.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The relative oriented simplicial chain complex. -/
def simplicialRelativeCx (hL : FaceClosed L) (hK : FaceClosed K) (h : L ⊆ K) :
    ChainComplex (ModuleCat.{0} ℝ) ℕ := cokernel (simplicialChainsInclusion hL hK h)

theorem mono_simplicialChainsInclusion (hL : FaceClosed L) (hK : FaceClosed K) (h : L ⊆ K) :
    Mono (simplicialChainsInclusion hL hK h) := by
  apply HomologicalComplex.mono_of_mono_f
  intro m
  apply (ModuleCat.mono_iff_injective _).mpr
  change Function.Injective (Submodule.inclusion (chains_mono (𝕜 := ℝ) h (m + 1)))
  exact Submodule.inclusion_injective _

/-- The short complex defining relative simplicial homology. -/
def simplicialRelativeShortComplex (hL : FaceClosed L) (hK : FaceClosed K) (h : L ⊆ K) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℝ) ℕ) :=
  ShortComplex.mk (simplicialChainsInclusion hL hK h)
    (cokernel.π (simplicialChainsInclusion hL hK h)) (cokernel.condition _)

theorem simplicialRelativeShortExact (hL : FaceClosed L) (hK : FaceClosed K) (h : L ⊆ K) :
    (simplicialRelativeShortComplex hL hK h).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := mono_simplicialChainsInclusion hL hK h
  epi_g := coequalizer.π_epi

/-- The original comparison, regarded as mapping to the literal subspace. -/
def subcomplexComparison (hL : FaceClosed L) (h : L ⊆ K) :
    simplicialChains hL ⟶ singChains (subSpace (subcomplexRealization L K)) :=
  comparisonSub hL h (subcomplexRealization L K) (fun _ hy => hy)

theorem subcomplexComparison_naturality (hL : FaceClosed L) (hK : FaceClosed K) (h : L ⊆ K) :
    simplicialChainsInclusion hL hK h ≫ comparisonChainMap hK =
      subcomplexComparison hL h ≫ chainsInclusion (subcomplexRealization L K) := by
  exact (comparisonChainMap_naturality hL hK h).symm.trans
    (comparisonSub_comp_chainsInclusion hL h (subcomplexRealization L K)
      (fun _ hy => hy)).symm

theorem quasiIso_subcomplexComparison (hL : FaceClosed L) (h : L ⊆ K) :
    QuasiIso (subcomplexComparison hL h) :=
  quasiIso_comparisonSub hL h (subcomplexRealization L K) (fun _ hy => hy)
    (quasiIso_comparisonChainMap hL) (subcomplexRealizationHomeomorph h).toHomotopyEquiv rfl

/-- The actual relative comparison induced on the two cokernels. -/
def relativeComparisonChainMap (hL : FaceClosed L) (hK : FaceClosed K) (h : L ⊆ K) :
    simplicialRelativeCx hL hK h ⟶ relCx (subcomplexRealization L K) :=
  cokernel.map (simplicialChainsInclusion hL hK h) (chainsInclusion (subcomplexRealization L K))
    (subcomplexComparison hL h) (comparisonChainMap hK) (subcomplexComparison_naturality hL hK h)

theorem relativeComparisonChainMap_proj (hL : FaceClosed L) (hK : FaceClosed K) (h : L ⊆ K) :
    cokernel.π (simplicialChainsInclusion hL hK h) ≫ relativeComparisonChainMap hL hK h =
      comparisonChainMap hK ≫ relProj (subcomplexRealization L K) :=
  cokernel.π_desc _ _ _

/-- A map of the actual short exact sequences of the pair. -/
def relativeComparisonShortComplexMap (hL : FaceClosed L) (hK : FaceClosed K) (h : L ⊆ K) :
    simplicialRelativeShortComplex hL hK h ⟶ relShortComplex (subcomplexRealization L K) where
  τ₁ := subcomplexComparison hL h
  τ₂ := comparisonChainMap hK
  τ₃ := relativeComparisonChainMap hL hK h
  comm₁₂ := (subcomplexComparison_naturality hL hK h).symm
  comm₂₃ := (relativeComparisonChainMap_proj hL hK h).symm

/-- Relative simplicial and actual relative singular homology agree, in
every degree, with no additional topological premise. -/
theorem quasiIso_relativeComparisonChainMap (hL : FaceClosed L) (hK : FaceClosed K)
    (h : L ⊆ K) : QuasiIso (relativeComparisonChainMap hL hK h) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (relativeComparisonShortComplexMap hL hK h)
    (simplicialRelativeShortExact hL hK h) (relShortExact (subcomplexRealization L K))
    (quasiIso_subcomplexComparison hL h) (quasiIso_comparisonChainMap hK)

theorem isIso_relativeComparisonHomologyMap (hL : FaceClosed L) (hK : FaceClosed K)
    (h : L ⊆ K) (k : ℕ) :
    IsIso (HomologicalComplex.homologyMap (relativeComparisonChainMap hL hK h) k) := by
  have := quasiIso_relativeComparisonChainMap hL hK h
  infer_instance

/-- The resulting isomorphism of the genuine relative homology modules. -/
def relativeComparisonHomologyIso (hL : FaceClosed L) (hK : FaceClosed K) (h : L ⊆ K) (k : ℕ) :
    (simplicialRelativeCx hL hK h).homology k ≅ relativeHomology (subcomplexRealization L K) k := by
  have := isIso_relativeComparisonHomologyMap hL hK h k
  exact asIso (HomologicalComplex.homologyMap (relativeComparisonChainMap hL hK h) k)

/-- The comparison commutes with the connecting morphisms of the pair. -/
theorem relativeComparison_delta_naturality (hL : FaceClosed L) (hK : FaceClosed K)
    (h : L ⊆ K) (k : ℕ) :
    (simplicialRelativeShortExact hL hK h).δ (k + 1) k (by simp) ≫
        HomologicalComplex.homologyMap (subcomplexComparison hL h) k =
      HomologicalComplex.homologyMap (relativeComparisonChainMap hL hK h) (k + 1) ≫
        relDelta (subcomplexRealization L K) k :=
  HomologicalComplex.HomologySequence.δ_naturality (relativeComparisonShortComplexMap hL hK h)
    (simplicialRelativeShortExact hL hK h) (relShortExact (subcomplexRealization L K))
    (k + 1) k (by simp)

end AffineTverberg.Simplicial
