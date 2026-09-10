import AffineTverberg.CofaceConnectingClasses
import AffineTverberg.DualBlockCofaceModel

set_option linter.style.header false

/-!
# The genuine geometric coface connecting map on representatives

The actual realization homeomorphism is a map of pairs. Composing its map
of short exact sequences with the coface comparison identifies the geometric
pair connecting map with the literal coefficient boundary. This also applies
to dual blocks by taking the costar of their cone apex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace AffineTverberg.Simplicial

open AffineTverberg.AffChain

variable {V E : Type} [Fintype V] [LinearOrder V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E}

/-- Both comparisons are maps of the actual short exact sequences. -/
def geometricCofaceComparisonShortComplexMap (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (L : Finset V) :
    cofaceShortComplex hK L ⟶
      relShortComplex (X := TopCat.of ↥(geometricCarrier K p))
        (geometricSubcomplexRealization (costarFamily K L) K p) :=
  cofaceComparisonShortComplexMap hK L ≫
    relativeShortComplexMap
      (TopCat.ofHom (geometricRealizationHomeomorph hgeom).toHomotopyEquiv.toFun)
      (fun x hx => (geometricRealizationHomeomorph_mem_subcomplex hgeom
        (costarFamily_subset K L) x).mp hx)

/-- The literal boundary-subspace comparison, not a chosen abstract map. -/
def geometricCostarComparisonChainMap (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (L : Finset V) :
    simplicialChains (faceClosed_costarFamily hK L) ⟶
      singChains (subSpace (X := TopCat.of ↥(geometricCarrier K p))
        (geometricSubcomplexRealization (costarFamily K L) K p)) :=
  (geometricCofaceComparisonShortComplexMap hK hgeom L).τ₁

theorem geometricCoface_delta_naturality (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (L : Finset V) (k : ℕ) :
    (cofaceShortExact hK L).δ (k + 1) k (by simp) ≫
      homologyMap (geometricCostarComparisonChainMap hK hgeom L) k =
    homologyMap (geometricCofaceComparisonChainMap hK hgeom L) (k + 1) ≫
      relDelta (X := TopCat.of ↥(geometricCarrier K p))
        (geometricSubcomplexRealization (costarFamily K L) K p) k :=
  HomologicalComplex.HomologySequence.δ_naturality
    (geometricCofaceComparisonShortComplexMap hK hgeom L) (cofaceShortExact hK L)
    (relShortExact (X := TopCat.of ↥(geometricCarrier K p))
      (geometricSubcomplexRealization (costarFamily K L) K p)) (k + 1) k (by simp)

/-- The actual geometric connecting map takes the compared coefficient
cycle to its compared boundary, including a receiving H0 group. -/
theorem geometricRelDelta_cofaceChainClass (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) {L : Finset V} {k : ℕ} {c : Finset V → ℝ}
    (hc : c ∈ cofaceChains K L (k + 2)) (hcbd : cofaceBoundary L c = 0) :
    (relDelta (X := TopCat.of ↥(geometricCarrier K p))
      (geometricSubcomplexRealization (costarFamily K L) K p) k).hom
      ((geometricCofaceHomologyIso hK hgeom L (k + 1)).hom.hom (cofaceChainClass hK hc hcbd)) =
    (homologyMap (geometricCostarComparisonChainMap hK hgeom L) k).hom
      (costarBoundaryClass hK hc hcbd) := by
  have h := congrArg (fun f : (cofaceComplex hK L).homology (k + 1) ⟶
      (singChains (subSpace (X := TopCat.of ↥(geometricCarrier K p))
        (geometricSubcomplexRealization (costarFamily K L) K p))).homology k =>
      f.hom (cofaceChainClass hK hc hcbd)) (geometricCoface_delta_naturality hK hgeom L k)
  change (homologyMap (geometricCostarComparisonChainMap hK hgeom L) k).hom
      (((cofaceShortExact hK L).δ (k + 1) k (by simp)).hom (cofaceChainClass hK hc hcbd)) =
    (relDelta (X := TopCat.of ↥(geometricCarrier K p))
      (geometricSubcomplexRealization (costarFamily K L) K p) k).hom
      ((geometricCofaceHomologyIso hK hgeom L (k + 1)).hom.hom (cofaceChainClass hK hc hcbd)) at h
  rw [coface_delta_chainClass] at h
  exact h.symm

end AffineTverberg.Simplicial
