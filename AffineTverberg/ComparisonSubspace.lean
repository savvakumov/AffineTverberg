import AffineTverberg.StarThickening
import AffineTverberg.SimplicialToSingular
import AffineTverberg.SingularMayerVietorisNaturality

set_option linter.style.header false

/-!
# The comparison chain map into subspaces and into small chains

This file prepares the general simplicial-to-singular comparison theorem.  For
a face-closed subfamily `L ⊆ K` whose realization is contained in a subset
`S ⊆ |K|` we factor the comparison chain map of `L` through the singular chain
complex of the subspace `S`, and for a two-set cover of `|K|` such that every
closed simplex of `K` lies inside one of the two sets we factor the comparison
chain map of `K` through the complex of *small* chains of the cover.

These two factorizations are what turn the comparison map into a morphism of
Mayer-Vietoris short exact sequences of chain complexes; no comparison theorem
is assumed anywhere.
-/

noncomputable section

open CategoryTheory Limits

namespace AffineTverberg

namespace Simplicial

open AffChain

variable {V : Type} [Fintype V] [LinearOrder V]

/-! ### Homotopy equivalences are quasi-isomorphisms of singular chains -/

theorem isIso_homologyMap_singChainsMap_of_homotopyEquiv {P Q : Type} [TopologicalSpace P]
    [TopologicalSpace Q] (e : ContinuousMap.HomotopyEquiv P Q) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (singChainsMap (X := TopCat.of P) (Y := TopCat.of Q) (TopCat.ofHom e.toFun)) n) :=
  (realSingularHomologyIsoOfHomotopyEquiv e n).isIso_hom

theorem quasiIso_singChainsMap_of_homotopyEquiv {P Q : Type} [TopologicalSpace P]
    [TopologicalSpace Q] (e : ContinuousMap.HomotopyEquiv P Q) :
    QuasiIso (singChainsMap (X := TopCat.of P) (Y := TopCat.of Q) (TopCat.ofHom e.toFun)) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact isIso_homologyMap_singChainsMap_of_homotopyEquiv e n

/-! ### The comparison map into a subspace of the realization -/

variable {K L : Finset (Finset V)}

/-- The realization of a subfamily `L ⊆ K`, mapped into a subset `S` of the
realization of `K` which contains it. -/
def baryToSub (h : L ⊆ K) (S : Set ↥(barySpace K))
    (hS : ∀ y : ↥(barySpace K), y.val ∈ barycentricCarrier L → y ∈ S) :
    barySpace L ⟶ subSpace S :=
  TopCat.ofHom ⟨fun y => ⟨⟨y.1, barycentricCarrier_mono h y.2⟩, hS _ y.2⟩, by fun_prop⟩

omit [LinearOrder V] in
theorem baryToSub_comp_subIncl (h : L ⊆ K) (S : Set ↥(barySpace K))
    (hS : ∀ y : ↥(barySpace K), y.val ∈ barycentricCarrier L → y ∈ S) :
    baryToSub h S hS ≫ subIncl S = baryInclusion h := rfl

omit [LinearOrder V] in
theorem baryToSub_comp_subInclMap (h : L ⊆ K) {S T : Set ↥(barySpace K)} (hST : S ⊆ T)
    (hS : ∀ y : ↥(barySpace K), y.val ∈ barycentricCarrier L → y ∈ S) :
    baryToSub h S hS ≫ subInclMap hST = baryToSub h T (fun y hy => hST (hS y hy)) := rfl

/-- The comparison chain map of `L`, viewed as a map into the singular chains
of a subspace `S` of the realization of `K` containing the realization of
`L`. -/
def comparisonSub (hL : FaceClosed L) (h : L ⊆ K) (S : Set ↥(barySpace K))
    (hS : ∀ y : ↥(barySpace K), y.val ∈ barycentricCarrier L → y ∈ S) :
    simplicialChains hL ⟶ singChains (subSpace S) :=
  comparisonChainMap hL ≫ singChainsMap (baryToSub h S hS)

theorem comparisonSub_comp_chainsInclusion (hL : FaceClosed L) (h : L ⊆ K)
    (S : Set ↥(barySpace K))
    (hS : ∀ y : ↥(barySpace K), y.val ∈ barycentricCarrier L → y ∈ S) :
    comparisonSub hL h S hS ≫ chainsInclusion S =
      comparisonChainMap hL ≫ singularChainsMap h := by
  rw [comparisonSub, Category.assoc, chainsInclusion_eq, ← singChainsMap_comp,
    baryToSub_comp_subIncl]
  rfl

theorem comparisonSub_comp_subMap (hL : FaceClosed L) (h : L ⊆ K)
    {S T : Set ↥(barySpace K)} (hST : S ⊆ T)
    (hS : ∀ y : ↥(barySpace K), y.val ∈ barycentricCarrier L → y ∈ S) :
    comparisonSub hL h S hS ≫ subMap hST =
      comparisonSub hL h T (fun y hy => hST (hS y hy)) := by
  rw [comparisonSub, comparisonSub, Category.assoc]
  congr 1
  rw [subMap_eq_singChainsMap, ← singChainsMap_comp, baryToSub_comp_subInclMap]

/-- The comparison chain map of a subfamily is a quasi-isomorphism into the
chains of a subspace as soon as it is one into the chains of the realization
and the inclusion of the realization into the subspace is a homotopy
equivalence. -/
theorem quasiIso_comparisonSub (hL : FaceClosed L) (h : L ⊆ K)
    (S : Set ↥(barySpace K))
    (hS : ∀ y : ↥(barySpace K), y.val ∈ barycentricCarrier L → y ∈ S)
    (hcomp : QuasiIso (comparisonChainMap hL))
    (e : ContinuousMap.HomotopyEquiv ↥(barycentricCarrier L) ↥S)
    (he : TopCat.ofHom e.toFun = baryToSub h S hS) :
    QuasiIso (comparisonSub hL h S hS) := by
  have hq : QuasiIso (singChainsMap (baryToSub h S hS)) := by
    rw [← he]
    exact quasiIso_singChainsMap_of_homotopyEquiv e
  rw [comparisonSub]
  infer_instance

/-! ### The comparison map into small chains -/

variable {U W : Set ↥(barySpace K)}

/-- The image of the affine simplex of a face `t` lies in the closed simplex of
`t`. -/
theorem affineSimplexMap_mem_face {t : Finset V} {m : ℕ} (ht : t ∈ K) (hc : t.card = m + 1)
    (x : Δt m) : ((affineSimplexMap ht hc x : ↥(barycentricCarrier K)) : V → ℝ) ∈
      barycentricFace t :=
  stdSimplexMap_mem_barycentricFace t hc x

/-- The affine singular simplex of a face, as a basis element of the singular
chains. -/
theorem iotaAffine_eq_smul_sElt {t : Finset V} {m : ℕ} (ht : t ∈ K) (hc : t.card = m + 1)
    (r : ℝ) :
    (iotaAffine K t m).hom r = r • sElt (X := barySpace K) (affineSimplexMap ht hc) := by
  rw [iotaAffine_of_mem ht hc]
  have hsmul := map_smul
    ((ιs (singSimplex (X := barySpace K) (affineSimplexMap ht hc))).hom) r (1 : ℝ)
  rw [smul_eq_mul, mul_one] at hsmul
  exact hsmul

/-- If every closed simplex of `K` lies in one of the two sets of the cover,
then the affine singular simplex of every face is a small chain. -/
theorem iotaAffine_mem_smallChains
    (hsmall : ∀ t ∈ K, (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ U) ∨
      (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ W))
    (t : Finset V) (m : ℕ) (r : ℝ) :
    (iotaAffine K t m).hom r ∈ smallChains (mvCover U W) m := by
  by_cases ht : t ∈ K ∧ t.card = m + 1
  · rw [iotaAffine_eq_smul_sElt ht.1 ht.2]
    refine Submodule.smul_mem _ _ ?_
    rcases hsmall t ht.1 with hU | hW
    · exact sElt_mem_smallChains (U := mvCover U W) (i := true)
        (fun x => hU _ (affineSimplexMap_mem_face ht.1 ht.2 x))
    · exact sElt_mem_smallChains (U := mvCover U W) (i := false)
        (fun x => hW _ (affineSimplexMap_mem_face ht.1 ht.2 x))
  · rw [iotaAffine_of_not ht]
    simp

theorem comparisonHom_mem_smallChains
    (hsmall : ∀ t ∈ K, (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ U) ∨
      (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ W))
    (m : ℕ) (c : ↥(chains ℝ K (m + 1))) :
    (comparisonHom K m).hom c ∈ smallChains (mvCover U W) m := by
  rw [comparisonHom_apply]
  exact Submodule.sum_mem _ fun t _ => iotaAffine_mem_smallChains hsmall t m _

/-- The comparison chain map of `K`, corestricted to the complex of small
chains of the cover `{U, W}`. -/
def comparisonSmall (hK : FaceClosed K)
    (hsmall : ∀ t ∈ K, (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ U) ∨
      (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ W)) :
    simplicialChains hK ⟶ smallCx (mvCover U W) where
  f m := ModuleCat.ofHom (LinearMap.codRestrict _ (comparisonHom K m).hom
    (comparisonHom_mem_smallChains hsmall m))
  comm' i j hij := by
    obtain ⟨rfl⟩ : j + 1 = i := hij
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    have h := congrArg (fun (g : (simplicialChains hK).X (j + 1) ⟶ (singularChains K).X j) =>
      g.hom c) ((comparisonChainMap hK).comm (j + 1) j)
    simp only [comparisonChainMap_f] at h
    simp only [smallCx_d_eq, smallCxD]
    exact h

theorem comparisonSmall_comp_smallInc (hK : FaceClosed K)
    (hsmall : ∀ t ∈ K, (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ U) ∨
      (∀ y : ↥(barySpace K), y.val ∈ barycentricFace t → y ∈ W)) :
    comparisonSmall hK hsmall ≫ smallInc (mvCover U W) = comparisonChainMap hK := by
  apply HomologicalComplex.hom_ext
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  rfl

end Simplicial

end AffineTverberg
