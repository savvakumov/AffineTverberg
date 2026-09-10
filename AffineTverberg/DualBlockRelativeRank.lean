import AffineTverberg.RelativeHomologyAugmentation
import AffineTverberg.ZeroDimensionalHomology
import AffineTverberg.CofaceMaximalHomology
import AffineTverberg.DualBlockHomologyAllDegrees
import AffineTverberg.DualBlockRelativeHomology
import AffineTverberg.LinkTopCycleRank

set_option linter.style.header false

/-!
# Rank one for actual relative dual-block homology, including low degrees

In relative degrees at least two the genuine connecting isomorphism leads
to ordinary link homology. In degree one it leads instead to the actual
augmentation kernel; the zero-dimensional link comparison identifies that
kernel with reduced vertex cycles. In degree zero a maximal original face
has a single-vertex dual block, whose relative chain complex is a line.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.Simplicial

open AffineTverberg.AffChain

variable {V : Type} [Fintype V] [LinearOrder V]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E} {s : Finset V}

/-- The genuine relative H1 connecting map, followed by the actual boundary
homeomorphism and augmentation comparison, reaches reduced link cycles. -/
def dualBlockRelativeHomologyOneEquivLinkCycles
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty) (htop : ∀ t ∈ link K s, t.card ≤ 1) :
    relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
      (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) 1 ≃ₗ[ℝ]
      ↥(cycles ℝ (link K s) 1) := by
  have hcontr : ContractibleSpace ↥(dualBlockSpace K p s) :=
    contractibleSpace_dualBlockSpace hsK hs
  let eh := (subsetSubtypeHomeomorph (dualBlockBoundarySpace_subset K p s)).trans
    (dualBlockBoundaryHomeomorph hgeom hK s)
  let iso := relativeHomologyOneAugmentationKernelIso
    (X := TopCat.of ↥(dualBlockSpace K p s)) (Subtype.val ⁻¹' dualBlockBoundarySpace K p s)
  exact (iso ≪≫ singularAugmentationKernelIsoOfHomotopyEquiv eh.toHomotopyEquiv).toLinearEquiv.trans
    (singularAugmentationKernelTopEquiv (faceClosed_link hK s) htop)

/-- The higher-degree relative connecting map gives the ordinary top link
cycle space when the link has the indicated dimension bound. -/
def dualBlockRelativeHomologyPositiveEquivLinkCycles
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty) (k : ℕ)
    (htop : ∀ t ∈ link K s, t.card ≤ k + 2) :
    relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
      (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) (k + 2) ≃ₗ[ℝ]
      ↥(cycles ℝ (link K s) (k + 2)) :=
  ((dualBlockRelativeHomologyIso hsK hs (k + 1) (by omega)) ≪≫
    realSingularHomologyIsoOfHomotopyEquiv
      (dualBlockBoundaryHomeomorph hgeom hK s).toHomotopyEquiv (k + 1)).toLinearEquiv.trans
        (realSingularHomologyTopEquiv (faceClosed_link hK s) k htop)

section Zero

variable [inst : LinearOrder (Finset V)]

local instance : DecidableEq (Finset V) := inst.toDecidableEq

/-- The actual degree-zero relative group of the dual block of a maximal
face is a line, including its empty boundary. -/
theorem finrank_dualBlockRelativeHomology_zero_of_maximal
    (hgeom : IsGeometricRealization K p) (hsK : s ∈ K) (hs : s.Nonempty)
    (hmax : ∀ t ∈ K, s ⊆ t → t = s) :
    Module.finrank ℝ (relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
      (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) 0) = 1 := by
  have hB : FaceClosed (dualBlockFaces K s) := by
    convert faceClosed_dualBlockFaces K s using 1
  have hBg : IsGeometricRealization (dualBlockFaces K s) (faceBarycenter p) := by
    have h := @IsGeometricRealization.mono (Finset V) (fun a b => a.decidableEq b)
      E _ _ _ _ _ (isGeometricRealization_subdivisionFaces hgeom) (dualBlockFaces_subset K s)
    convert h using 1
  have hApex : ({s} : Finset (Finset V)) ∈ dualBlockFaces K s := by
    convert singleton_mem_dualBlockFaces hsK hs using 1
  have hmaxApex : ∀ C ∈ dualBlockFaces K s, ({s} : Finset (Finset V)) ⊆ C → C = {s} := by
    intro C hC hsC
    refine Finset.Subset.antisymm (fun t ht => ?_) hsC
    obtain ⟨hCsd, hsub⟩ := mem_dualBlockFaces.mp hC
    exact Finset.mem_singleton.mpr
      (hmax t ((mem_subdivisionFaces.mp hCsd).1 ht) (hsub t ht))
  have hfin := finrank_cofaceHomology_of_maximal hB hApex hmaxApex 0 (by simp)
  have hiso := geometricCofaceHomologyIso hB hBg {s} 0
  have result := hiso.toLinearEquiv.finrank_eq.symm.trans hfin
  change Module.finrank ℝ (relativeHomology
    (X := TopCat.of ↥(geometricCarrier (dualBlockFaces K s) (faceBarycenter p)))
    (Subtype.val ⁻¹' geometricCarrier (costarFamily (dualBlockFaces K s) {s})
      (faceBarycenter p)) 0) = 1 at result
  rw [costar_dualBlock_apex] at result
  exact result

end Zero

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- Every actual dual-block pair in a triangulated topological sphere has
rank-one homology in its expected degree, including relative degrees zero
and one. The only topology assumed is the given sphere homeomorphism. -/
theorem finrank_dualBlockRelativeHomology_of_sphere
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty) {N : ℕ}
    (hdim : Module.finrank ℝ F = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1)
    (htop : ∀ t ∈ K, t.card ≤ N + 1) (q : ℕ) (hq : q + s.card = N + 1) :
    Module.finrank ℝ (relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
      (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) q) = 1 := by
  match q with
  | 0 =>
    let : LinearOrder (Finset V) :=
      LinearOrder.lift' (Fintype.equivFin (Finset V)) (Equiv.injective _)
    apply finrank_dualBlockRelativeHomology_zero_of_maximal hgeom hsK hs
    intro t ht hst
    have hcard := htop t ht
    exact (Finset.eq_of_subset_of_card_le hst (by omega)).symm
  | 1 =>
    have hlink : ∀ t ∈ link K s, t.card ≤ 1 := by
      intro t ht
      have := card_le_of_mem_link htop ht
      omega
    rw [(dualBlockRelativeHomologyOneEquivLinkCycles hgeom hK hsK hs hlink).finrank_eq]
    exact finrank_top_cycles_link hK hsK hs hdim hN e htop hq
  | k + 2 =>
    have hlink : ∀ t ∈ link K s, t.card ≤ k + 2 := by
      intro t ht
      have := card_le_of_mem_link htop ht
      omega
    rw [(dualBlockRelativeHomologyPositiveEquivLinkCycles hgeom hK hsK hs k hlink).finrank_eq]
    exact finrank_top_cycles_link hK hsK hs hdim hN e htop hq

end AffineTverberg.Simplicial
