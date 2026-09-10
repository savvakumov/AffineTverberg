import AffineTverberg.CoefficientComparison
import AffineTverberg.CoefficientSingularMayerVietorisNaturality
import AffineTverberg.ComparisonSubspace

set_option linter.style.header false

/-!
# The arbitrary-field comparison map into subspaces and small chains

The existing real geometric realization maps are reused. Only the chain
coefficients vary. Both factorizations are actual commuting chain maps.
-/

noncomputable section

open CategoryTheory Limits AffineTverberg.Simplicial

namespace AffineTverberg.Coefficients

open AffineTverberg.Coefficients.AffChain AffineTverberg.AffChain

variable (𝕜 : Type) [Field 𝕜]
variable {V : Type} [Fintype V] [LinearOrder V]

theorem isIso_homologyMap_singChainsMap_of_homotopyEquiv {P Q : Type} [TopologicalSpace P]
    [TopologicalSpace Q] (e : ContinuousMap.HomotopyEquiv P Q) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (singChainsMap 𝕜 (X := TopCat.of P) (Y := TopCat.of Q) (TopCat.ofHom e.toFun)) n) :=
  (singularHomologyIsoOfHomotopyEquiv 𝕜 e n).isIso_hom

theorem quasiIso_singChainsMap_of_homotopyEquiv {P Q : Type} [TopologicalSpace P]
    [TopologicalSpace Q] (e : ContinuousMap.HomotopyEquiv P Q) :
    QuasiIso (singChainsMap 𝕜 (X := TopCat.of P) (Y := TopCat.of Q) (TopCat.ofHom e.toFun)) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_singChainsMap_of_homotopyEquiv 𝕜 e n

variable {K L : Finset (Finset V)}

/-- The comparison chain map of `L`, viewed as a map into the singular chains
of a subspace `S` of the realization of `K` containing the realization of
`L`. -/
def comparisonSub (hL : FaceClosed L) (h : L ⊆ K) (S : Set ↥(barySpace K))
    (hS : ∀ y : ↥(barySpace K), y.val ∈ barycentricCarrier L → y ∈ S) :
    simplicialChains 𝕜 hL ⟶ singChains 𝕜 (subSpace S) :=
  comparisonChainMap 𝕜 hL ≫ singChainsMap 𝕜 (baryToSub h S hS)

theorem comparisonSub_comp_chainsInclusion (hL : FaceClosed L) (h : L ⊆ K)
    (S : Set ↥(barySpace K))
    (hS : ∀ y : ↥(barySpace K), y.val ∈ barycentricCarrier L → y ∈ S) :
    comparisonSub 𝕜 hL h S hS ≫ chainsInclusion 𝕜 S =
      comparisonChainMap 𝕜 hL ≫ singularChainsMap 𝕜 h := by
  rw [comparisonSub, Category.assoc, chainsInclusion_eq 𝕜, ← singChainsMap_comp 𝕜,
    baryToSub_comp_subIncl]
  rfl

theorem comparisonSub_comp_subMap (hL : FaceClosed L) (h : L ⊆ K)
    {S T : Set ↥(barySpace K)} (hST : S ⊆ T)
    (hS : ∀ y : ↥(barySpace K), y.val ∈ barycentricCarrier L → y ∈ S) :
    comparisonSub 𝕜 hL h S hS ≫ subMap 𝕜 hST =
      comparisonSub 𝕜 hL h T (fun y hy => hST (hS y hy)) := by
  rw [comparisonSub, comparisonSub, Category.assoc]
  congr 1
  rw [subMap_eq_singChainsMap 𝕜, ← singChainsMap_comp 𝕜, baryToSub_comp_subInclMap]

/-- The comparison chain map of a subfamily is a quasi-isomorphism into the
chains of a subspace as soon as it is one into the chains of the realization
and the inclusion of the realization into the subspace is a homotopy
equivalence. -/
theorem quasiIso_comparisonSub (hL : FaceClosed L) (h : L ⊆ K)
    (S : Set ↥(barySpace K))
    (hS : ∀ y : ↥(barySpace K), y.val ∈ barycentricCarrier L → y ∈ S)
    (hcomp : QuasiIso (comparisonChainMap 𝕜 hL))
    (e : ContinuousMap.HomotopyEquiv ↥(barycentricCarrier L) ↥S)
    (he : TopCat.ofHom e.toFun = baryToSub h S hS) :
    QuasiIso (comparisonSub 𝕜 hL h S hS) := by
  have hq : QuasiIso (singChainsMap 𝕜 (baryToSub h S hS)) := by
    rw [← he]
    exact quasiIso_singChainsMap_of_homotopyEquiv 𝕜 e
  rw [comparisonSub]
  infer_instance


variable {U W : Set ↥(barySpace K)}

/-- The affine singular simplex of a face as a basis element of singular chains. -/
theorem iotaAffine_eq_smul_sElt {t : Finset V} {m : ℕ} (ht : t ∈ K) (hc : t.card = m + 1)
    (r : 𝕜) :
    (iotaAffine 𝕜 K t m).hom r = r • sElt 𝕜 (X := barySpace K) (affineSimplexMap ht hc) := by
  rw [iotaAffine_of_mem 𝕜 ht hc]
  have hsmul := map_smul
    ((ιs 𝕜 (singSimplex (X := barySpace K) (affineSimplexMap ht hc))).hom) r (1 : 𝕜)
  rw [smul_eq_mul, mul_one] at hsmul
  exact hsmul

/-- If every closed simplex of `K` lies in one of the two sets of the cover,
then the affine singular simplex of every face is a small chain. -/
theorem iotaAffine_mem_smallChains
    (hsmall : ∀ t ∈ K, (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ U) ∨
      (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ W))
    (t : Finset V) (m : ℕ) (r : 𝕜) :
    (iotaAffine 𝕜 K t m).hom r ∈ smallChains 𝕜 (mvCover U W) m := by
  by_cases ht : t ∈ K ∧ t.card = m + 1
  · rw [iotaAffine_eq_smul_sElt 𝕜 ht.1 ht.2]
    refine Submodule.smul_mem _ _ ?_
    rcases hsmall t ht.1 with hU | hW
    · exact sElt_mem_smallChains 𝕜 (U := mvCover U W) (i := true)
        (fun x => hU _ (affineSimplexMap_mem_face ht.1 ht.2 x))
    · exact sElt_mem_smallChains 𝕜 (U := mvCover U W) (i := false)
        (fun x => hW _ (affineSimplexMap_mem_face ht.1 ht.2 x))
  · rw [iotaAffine_of_not 𝕜 ht]
    simp

theorem comparisonHom_mem_smallChains
    (hsmall : ∀ t ∈ K, (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ U) ∨
      (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ W))
    (m : ℕ) (c : ↥(chains 𝕜 K (m + 1))) :
    (comparisonHom 𝕜 K m).hom c ∈ smallChains 𝕜 (mvCover U W) m := by
  rw [comparisonHom_apply 𝕜]
  exact Submodule.sum_mem _ fun t _ => iotaAffine_mem_smallChains 𝕜 hsmall t m _

/-- The comparison chain map of `K`, corestricted to the complex of small
chains of the cover `{U, W}`. -/
def comparisonSmall (hK : FaceClosed K)
    (hsmall : ∀ t ∈ K, (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ U) ∨
      (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ W)) :
    simplicialChains 𝕜 hK ⟶ smallCx 𝕜 (mvCover U W) where
  f m := ModuleCat.ofHom (LinearMap.codRestrict _ (comparisonHom 𝕜 K m).hom
    (comparisonHom_mem_smallChains 𝕜 hsmall m))
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    have h := congrArg (fun (g : (simplicialChains 𝕜 hK).X (j + 1) ⟶ (singularChains 𝕜 K).X j) =>
      g.hom c) ((comparisonChainMap 𝕜 hK).comm (j + 1) j)
    simp only [comparisonChainMap_f 𝕜] at h
    simp only [smallCx_d_eq 𝕜, AffineTverberg.Coefficients.AffChain.smallCxD]
    exact h

theorem comparisonSmall_comp_smallInc (hK : FaceClosed K)
    (hsmall : ∀ t ∈ K, (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ U) ∨
      (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ W)) :
    comparisonSmall 𝕜 hK hsmall ≫ smallInc 𝕜 (mvCover U W) = comparisonChainMap 𝕜 hK := by
  apply HomologicalComplex.hom_ext
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

end AffineTverberg.Coefficients
