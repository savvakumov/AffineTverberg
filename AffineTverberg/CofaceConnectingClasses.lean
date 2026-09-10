import AffineTverberg.ConnectingHomologyClasses
import AffineTverberg.CofaceAcyclicity

set_option linter.style.header false

/-!
# Connecting maps of coface pairs on explicit coefficient cycles

For a coface cycle c, its ordinary simplicial boundary lies in the costar.
The actual connecting morphism sends the class of c to the class of this
literal boundary. The genuine simplicial-to-singular comparison preserves
this calculation, including a degree-zero receiving group. In particular,
it applies to the apex costar model of each dual-block pair.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace AffineTverberg.Simplicial

open AffineTverberg.AffChain

variable {V : Type} [Fintype V] [LinearOrder V]
  {K : Finset (Finset V)} {L : Finset V} {k : ℕ} {c : Finset V → ℝ}

theorem cofaceChain_isCycleAt (hK : FaceClosed K)
    (hc : c ∈ cofaceChains K L (k + 2)) (hcbd : cofaceBoundary L c = 0) :
    IsCycleAt (cofaceComplex hK L) (k + 1) (⟨c, hc⟩ : ↥(cofaceChains K L (k + 2))) := by
  apply isCycleAt_succ
  rw [cofaceComplex_d]
  exact Subtype.ext hcbd

/-- The actual coface homology class of a coefficient cycle. -/
def cofaceChainClass (hK : FaceClosed K)
    (hc : c ∈ cofaceChains K L (k + 2)) (hcbd : cofaceBoundary L c = 0) :
    (cofaceComplex hK L).homology (k + 1) :=
  homClass (⟨c, hc⟩ : ↥(cofaceChains K L (k + 2))) (cofaceChain_isCycleAt hK hc hcbd)

theorem costarBoundary_isCycleAt (hK : FaceClosed K)
    (hc : c ∈ cofaceChains K L (k + 2)) (hcbd : cofaceBoundary L c = 0) :
    IsCycleAt (simplicialChains (faceClosed_costarFamily hK L)) k
      (⟨boundary ℝ V c, boundary_mem_chains_costar hK hc hcbd⟩ :
        ↥(chains ℝ (costarFamily K L) (k + 1))) := by
  cases k with
  | zero => exact isCycleAt_zero _
  | succ k =>
    apply isCycleAt_succ
    rw [simplicialChains_d]
    exact Subtype.ext (boundary_boundary_apply c)

/-- The class of the literal coefficient boundary in the costar. -/
def costarBoundaryClass (hK : FaceClosed K)
    (hc : c ∈ cofaceChains K L (k + 2)) (hcbd : cofaceBoundary L c = 0) :
    (simplicialChains (faceClosed_costarFamily hK L)).homology k :=
  homClass (⟨boundary ℝ V c, boundary_mem_chains_costar hK hc hcbd⟩ :
    ↥(chains ℝ (costarFamily K L) (k + 1))) (costarBoundary_isCycleAt hK hc hcbd)

/-- The connecting map in the actual coface short exact sequence is the
literal simplicial boundary on representatives. -/
theorem coface_delta_chainClass (hK : FaceClosed K)
    (hc : c ∈ cofaceChains K L (k + 2)) (hcbd : cofaceBoundary L c = 0) :
    ((cofaceShortExact hK L).δ (k + 1) k (by simp)).hom (cofaceChainClass hK hc hcbd) =
      costarBoundaryClass hK hc hcbd := by
  apply homologySequence_delta_homClass (cofaceShortExact hK L) k
    (⟨c, hc⟩ : ↥(cofaceChains K L (k + 2))) (cofaceChain_isCycleAt hK hc hcbd)
    (⟨c, cofaceChains_le L (k + 2) hc⟩ : ↥(chains ℝ K (k + 2)))
    _ (⟨boundary ℝ V c, boundary_mem_chains_costar hK hc hcbd⟩ :
      ↥(chains ℝ (costarFamily K L) (k + 1))) _ (costarBoundary_isCycleAt hK hc hcbd)
  · exact Subtype.ext (cofaceRestriction_eq_self hc)
  · change ((simplicialChainsInclusion (faceClosed_costarFamily hK L) hK
      (costarFamily_subset K L)).f k).hom _ = ((simplicialChains hK).d (k + 1) k).hom _
    rw [simplicialChains_d]
    rfl

/-- The relative coface comparison is part of a map of the genuine short
exact sequences, with the previously proved absolute comparison maps. -/
def cofaceComparisonShortComplexMap (hK : FaceClosed K) (L : Finset V) :
    cofaceShortComplex hK L ⟶ relShortComplex (subcomplexRealization (costarFamily K L) K) where
  τ₁ := subcomplexComparison (faceClosed_costarFamily hK L) (costarFamily_subset K L)
  τ₂ := comparisonChainMap hK
  τ₃ := cofaceComparisonChainMap hK L
  comm₁₂ := (subcomplexComparison_naturality (faceClosed_costarFamily hK L) hK
    (costarFamily_subset K L)).symm
  comm₂₃ := (cofaceComparisonChainMap_proj hK L).symm

/-- Actual connecting homomorphisms commute with the coface comparison. -/
theorem cofaceComparison_delta_naturality (hK : FaceClosed K) (L : Finset V) (k : ℕ) :
    (cofaceShortExact hK L).δ (k + 1) k (by simp) ≫
      homologyMap (subcomplexComparison (faceClosed_costarFamily hK L)
        (costarFamily_subset K L)) k =
    homologyMap (cofaceComparisonChainMap hK L) (k + 1) ≫
      relDelta (subcomplexRealization (costarFamily K L) K) k :=
  HomologicalComplex.HomologySequence.δ_naturality (cofaceComparisonShortComplexMap hK L)
    (cofaceShortExact hK L) (relShortExact (subcomplexRealization (costarFamily K L) K))
    (k + 1) k (by simp)

/-- The genuine singular connecting map sends the compared coface cycle
to the compared literal costar boundary, in all receiving degrees k>=0. -/
theorem relDelta_cofaceChainClass (hK : FaceClosed K)
    (hc : c ∈ cofaceChains K L (k + 2)) (hcbd : cofaceBoundary L c = 0) :
    (relDelta (subcomplexRealization (costarFamily K L) K) k).hom
      ((cofaceRelativeHomologyIso hK L (k + 1)).hom.hom (cofaceChainClass hK hc hcbd)) =
      (homologyMap (subcomplexComparison (faceClosed_costarFamily hK L)
        (costarFamily_subset K L)) k).hom (costarBoundaryClass hK hc hcbd) := by
  have h := congrArg (fun f : (cofaceComplex hK L).homology (k + 1) ⟶
      (singChains (subSpace (subcomplexRealization (costarFamily K L) K))).homology k =>
        f.hom (cofaceChainClass hK hc hcbd)) (cofaceComparison_delta_naturality hK L k)
  change (homologyMap (subcomplexComparison (faceClosed_costarFamily hK L)
      (costarFamily_subset K L)) k).hom
      (((cofaceShortExact hK L).δ (k + 1) k (by simp)).hom (cofaceChainClass hK hc hcbd)) =
    (relDelta (subcomplexRealization (costarFamily K L) K) k).hom
      ((cofaceRelativeHomologyIso hK L (k + 1)).hom.hom (cofaceChainClass hK hc hcbd)) at h
  rw [coface_delta_chainClass] at h
  exact h.symm

end AffineTverberg.Simplicial
