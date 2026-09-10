import AffineTverberg.GeometricCofaceConnecting

set_option linter.style.header false

/-!
# Explicit cone representatives for genuine relative classes

Coning an augmented cycle in the apex costar gives an explicit relative
cycle. Its boundary is exactly the original coefficient cycle, so the
actual connecting map sends its class to that boundary class. This is
verified both for the coface model and for the genuine geometric singular
pair, including relative degree one and its H0 boundary.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace AffineTverberg.Simplicial

open AffineTverberg.AffChain

variable {V : Type} [Fintype V] [LinearOrder V]
  {K : Finset (Finset V)} {a : V} {k n : ℕ} {b : Finset V → ℝ}

/-- The explicit cone chain has the original cycle as its literal boundary. -/
theorem boundary_coneHomotopy_of_cycle (a : V) (hb : boundary ℝ V b = 0) :
    boundary ℝ V (coneHomotopy ℝ V a b) = b := by
  funext t
  have h := coneHomotopy_identity (𝕜 := ℝ) a b t
  rw [hb, map_zero, Pi.zero_apply, add_zero] at h
  exact h

/-- Coning a chain in the apex costar produces a chain supported on cofaces
of that apex, with the existing oriented cone coefficients. -/
theorem coneHomotopy_mem_cofaceChains (hcone : IsConeWithApex K a)
    (hb : b ∈ chains ℝ (costarFamily K {a}) n) :
    coneHomotopy ℝ V a b ∈ cofaceChains K {a} (n + 1) := by
  have hmem := coneHomotopy_mem_chains hcone
    (chains_mono (costarFamily_subset K {a}) n hb)
  intro t ht
  have hat : a ∈ t := by
    by_contra h
    exact ht (by simp [h])
  exact ⟨Finset.mem_filter.mpr ⟨(hmem t ht).1, Finset.singleton_subset_iff.mpr hat⟩,
    (hmem t ht).2⟩

theorem cofaceBoundary_coneHomotopy_eq_zero (hb : b ∈ cycles ℝ (costarFamily K {a}) n) :
    cofaceBoundary {a} (coneHomotopy ℝ V a b) = 0 := by
  change cofaceRestriction {a} (boundary ℝ V (coneHomotopy ℝ V a b)) = 0
  rw [boundary_coneHomotopy_of_cycle a hb.2]
  exact (cofaceRestriction_eq_zero_iff_costar
    (chains_mono (costarFamily_subset K {a}) n hb.1)).mpr hb.1

/-- An augmented cycle in cardinality degree k+1 is an ordinary cycle in
degree k, including the ordinary H0 endpoint. -/
theorem simplicialReducedCycle_isCycleAt (hK : FaceClosed K)
    (hb : b ∈ cycles ℝ K (k + 1)) :
    IsCycleAt (simplicialChains hK) k (⟨b, hb.1⟩ : ↥(chains ℝ K (k + 1))) := by
  cases k with
  | zero => exact isCycleAt_zero _
  | succ k =>
    apply isCycleAt_succ
    rw [simplicialChains_d]
    exact Subtype.ext hb.2

/-- The actual relative class represented by the explicit oriented cone chain. -/
def coneCofaceClass (hK : FaceClosed K) (hcone : IsConeWithApex K a)
    (hb : b ∈ cycles ℝ (costarFamily K {a}) (k + 1)) :
    (cofaceComplex hK {a}).homology (k + 1) :=
  cofaceChainClass hK (coneHomotopy_mem_cofaceChains hcone hb.1)
    (cofaceBoundary_coneHomotopy_eq_zero hb)

theorem costarBoundaryClass_coneHomotopy (hK : FaceClosed K)
    (hcone : IsConeWithApex K a) (hb : b ∈ cycles ℝ (costarFamily K {a}) (k + 1)) :
    costarBoundaryClass hK (coneHomotopy_mem_cofaceChains hcone hb.1)
      (cofaceBoundary_coneHomotopy_eq_zero hb) =
      homClass (⟨b, hb.1⟩ : ↥(chains ℝ (costarFamily K {a}) (k + 1)))
        (simplicialReducedCycle_isCycleAt (faceClosed_costarFamily hK {a}) hb) := by
  apply homClass_congr
  exact Subtype.ext (boundary_coneHomotopy_of_cycle a hb.2)

/-- The actual coface connecting map takes the cone class to its prescribed
boundary class, with no unspecified scalar or sign. -/
theorem coface_delta_coneCofaceClass (hK : FaceClosed K) (hcone : IsConeWithApex K a)
    (hb : b ∈ cycles ℝ (costarFamily K {a}) (k + 1)) :
    ((cofaceShortExact hK {a}).δ (k + 1) k (by simp)).hom (coneCofaceClass hK hcone hb) =
      homClass (⟨b, hb.1⟩ : ↥(chains ℝ (costarFamily K {a}) (k + 1)))
        (simplicialReducedCycle_isCycleAt (faceClosed_costarFamily hK {a}) hb) := by
  rw [coneCofaceClass, coface_delta_chainClass]
  exact costarBoundaryClass_coneHomotopy hK hcone hb

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : V → E}

/-- The genuine geometric singular connecting map has the same explicit
cone representative calculation, also from relative H1 to boundary H0. -/
theorem geometricRelDelta_coneCofaceClass (hK : FaceClosed K)
    (hgeom : IsGeometricRealization K p) (hcone : IsConeWithApex K a)
    (hb : b ∈ cycles ℝ (costarFamily K {a}) (k + 1)) :
    (relDelta (X := TopCat.of ↥(geometricCarrier K p))
      (geometricSubcomplexRealization (costarFamily K {a}) K p) k).hom
      ((geometricCofaceHomologyIso hK hgeom {a} (k + 1)).hom.hom (coneCofaceClass hK hcone hb)) =
    (homologyMap (geometricCostarComparisonChainMap hK hgeom {a}) k).hom
      (homClass (⟨b, hb.1⟩ : ↥(chains ℝ (costarFamily K {a}) (k + 1)))
        (simplicialReducedCycle_isCycleAt (faceClosed_costarFamily hK {a}) hb)) := by
  rw [coneCofaceClass, geometricRelDelta_cofaceChainClass,
    costarBoundaryClass_coneHomotopy hK hcone hb]

end AffineTverberg.Simplicial
