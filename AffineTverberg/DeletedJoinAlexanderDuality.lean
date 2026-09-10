import AffineTverberg.SimplicialAlexanderDuality
import AffineTverberg.BoundaryJoinPairModel

set_option linter.style.header false

/-!
# Alexander duality applied to the deleted join

The finite simplicial Alexander duality of `SimplicialAlexanderDuality` is
applied to the actual paper pair.  The ambient complex is the bad-edge
subdivision `a.joinComplex` of the boundary join, which is a triangulated
topological sphere of coordinate dimension `(m + 1) * n`; the deleted join is
the induced subcomplex `a.deletedComplex` on the good vertices, and the
complementary induced subcomplex is exactly the bad complex `a.badComplex`,
whose top homology already vanishes by the private-facet (free-facet)
argument.

Duality therefore gives vanishing of `H̃_{n-1}` of the deleted join.
`MainTheoremProof` uses this result to prove the simplicial-ball zero theorem
and assemble the two cases of `mainTheoremStatement`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.BadEdge.BoundaryJoinVertexIndexing

open AffineTverberg AffineTverberg.Simplicial

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  (a : BoundaryJoinVertexIndexing n K m)

/-- **The deleted join is reduced acyclic in cardinality degree `n`.**  This is
Alexander duality inside the triangulated boundary-join sphere: the
complementary induced subcomplex is the bad complex, whose top homology
vanishes because every top bad simplex has a private facet. -/
theorem isReducedAcyclicAt_deletedComplex (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    (hm : 2 ≤ m) :
    letI := a.subdivisionOrder
    IsReducedAcyclicAt ℝ a.deletedComplex n := by
  let := a.subdivisionOrder
  have hmul : (m + 1) * n = m * n + n := by ring
  have hmn : 4 ≤ m * n := by nlinarith
  have hdim : Module.finrank ℝ (CoordinateSpace ((m + 1) * n)) = ((m + 1) * n - 1) + 1 := by
    rw [AffineTverberg.finrank_coordinateSpace]
    omega
  have hN : 2 ≤ (m + 1) * n - 1 := by omega
  have htop : ∀ t ∈ a.joinComplex, t.card ≤ ((m + 1) * n - 1) + 1 := by
    intro t ht
    have := a.card_joinComplex_le ht
    omega
  have hbad : IsReducedAcyclicAt ℝ a.badComplex ((m * n - 1) + 1) := by
    have h := a.homology_subsingleton ℝ hm (by omega)
    rw [homology_subsingleton_iff] at h
    have hrw : m * n - 1 + 1 = m * n := by omega
    rw [hrw]
    exact h
  have hA : ∀ s, s ∈ a.deletedComplex ↔
      s ∈ a.joinComplex ∧ ∀ v ∈ s, v ∈ goodSdVertices (Fin a.size) := by
    intro s
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := mem_inducedFaces.mp h
      exact ⟨h1, fun v hv => h2 hv⟩
    · rintro ⟨h1, h2⟩
      exact mem_inducedFaces.mpr ⟨h1, fun v hv => h2 v hv⟩
  have hL : ∀ s, s ∈ a.badComplex ↔
      s ∈ a.joinComplex ∧ ∀ v ∈ s, v ∉ goodSdVertices (Fin a.size) := by
    intro s
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := (mem_badJoinFaces a.factor a.vertex).mp h
      exact ⟨h1, fun v hv hg => h2 v hv (mem_goodSdVertices.mp hg)⟩
    · rintro ⟨h1, h2⟩
      exact (mem_badJoinFaces a.factor a.vertex).mpr
        ⟨h1, fun v hv hg => h2 v hv (mem_goodSdVertices.mpr hg)⟩
  have hres := isReducedAcyclicAt_inducedFaces_of_sphere
    (E := CoordinateSpace ((m + 1) * n)) a.faceClosed_joinComplex hdim hN
    (a.joinBarycentricSphereHomeomorph hball hn) htop (goodSdVertices (Fin a.size))
    hA hL (q := n - 1) (k := m * n - 1) (by omega) (by omega) hbad
  have hrw : n - 1 + 1 = n := by omega
  rw [hrw] at hres
  exact hres

end AffineTverberg.BadEdge.BoundaryJoinVertexIndexing

namespace AffineTverberg

open CategoryTheory CategoryTheory.Limits AffineTverberg.Simplicial
open AffineTverberg.BadEdge

/-- **The homology of the actual deleted join vanishes in the paper's degree.**
No PL, shellability, orientability or extra local acyclicity hypothesis is
used; the geometric input is the original topological ball assumption. -/
theorem isZero_deletedJoin_homology_of_ball {e n m : ℕ}
    {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n) (hm : 2 ≤ m) :
    IsZero ((realSingularHomology (n - 1)).obj
      (TopCat.of ↥(simplicialDeletedJoinCarrier n K m))) := by
  classical
  set a := boundaryJoinVertexIndexing (n := n) (m := m) hball.finite_faces with hadef
  let := a.subdivisionOrder
  obtain ⟨j, hj⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  have hac : IsReducedAcyclicAt ℝ a.deletedComplex (j + 2) := by
    rw [← hj]
    exact a.isReducedAcyclicAt_deletedComplex hball hn hm
  have hz : IsZero ((realSingularHomology (j + 1)).obj (barySpace a.deletedComplex)) :=
    (isZero_realSingularHomology_barySpace_iff a.faceClosed_deletedComplex j).mpr hac
  have hsub := (realSingularHomology_subsingleton_iff_of_homotopyEquiv
    a.deletedBarycentricHomeomorph.toHomotopyEquiv (j + 1)).mp
      (ModuleCat.subsingleton_of_isZero hz)
  rw [show n - 1 = j + 1 from by omega]
  exact ModuleCat.isZero_iff_subsingleton.mpr hsub

end AffineTverberg
