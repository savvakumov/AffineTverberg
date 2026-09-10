import AffineTverberg.CofaceHomologyCell
import AffineTverberg.BoundaryJoinPairModel

set_option linter.style.header false

/-!
# Full local relative homology for the paper's actual sphere triangulation

The costar/coface calculation is applied to the existing boundary-join model
using only the paper's original simplicial-ball hypothesis. Vanishing covers
every off-top degree, including zero and one. Top relative homology is
one-dimensional in the simplicial-ball range r=m+1>=3.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.BadEdge.BoundaryJoinVertexIndexing

open AffineTverberg.Simplicial

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  (a : BoundaryJoinVertexIndexing n K m)

/-- Actual local relative homology vanishes in every degree other than the sphere dimension. -/
theorem isZero_join_cofaceHomology (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {L : Finset (Finset (Fin a.size))} (hL : L ∈ a.joinComplex) (hLne : L.Nonempty)
    (q : ℕ) (hq : q + 1 ≠ (m + 1) * n) :
    letI := a.subdivisionOrder
    IsZero ((cofaceComplex (by convert a.faceClosed_joinComplex using 1) L).homology q) := by
  let := a.subdivisionOrder
  let : DecidableEq (Finset (Fin a.size)) := a.subdivisionOrder.toDecidableEq
  have hJ : FaceClosed a.joinComplex := by convert a.faceClosed_joinComplex using 1
  change IsZero ((cofaceComplex hJ L).homology q)
  obtain ⟨F, hF, hLF, hcard⟩ := a.exists_top_simplex_extension hball hn hL
  have hmax : ∀ t ∈ a.joinComplex, F ⊆ t → t = F := by
    intro t ht hFt
    exact (Finset.eq_of_subset_of_card_le hFt
      (by rw [hcard]; exact a.card_joinComplex_le ht)).symm
  exact isZero_cofaceHomology_of_maximal_coface hJ hLF hF hLne hmax
    (a.joinBarycentricSphereHomeomorph hball hn) q (by simpa only [hcard] using hq)

/-- Top relative homology at every nonempty face of the paper's sphere is a line. -/
theorem finrank_join_cofaceHomology (hball : IsSimplicialBall n K) (hn : 2 ≤ n) (hm : 2 ≤ m)
    {L : Finset (Finset (Fin a.size))} (hL : L ∈ a.joinComplex) (hLne : L.Nonempty) :
    letI := a.subdivisionOrder
    Module.finrank ℝ
      ((cofaceComplex (by convert a.faceClosed_joinComplex using 1) L).homology
        ((m + 1) * n - 1)) = 1 := by
  let := a.subdivisionOrder
  let : DecidableEq (Finset (Fin a.size)) := a.subdivisionOrder.toDecidableEq
  have hJ : FaceClosed a.joinComplex := by convert a.faceClosed_joinComplex using 1
  have hdim : 3 ≤ (m + 1) * n := by nlinarith
  have hshift : (m + 1) * n - 2 + 2 = (m + 1) * n := by omega
  have hdegree : (m + 1) * n - 2 + 1 = (m + 1) * n - 1 := by omega
  have h := finrank_coface_top_homology (k := (m + 1) * n - 2) hJ
    (fun t ht => by rw [hshift]; exact a.card_joinComplex_le ht) hL hLne
    (a.joinBarycentricSphereHomeomorph hball hn)
    (by rw [finrank_coordinateSpace, hshift]) (by omega)
  change Module.finrank ℝ ((cofaceComplex hJ L).homology ((m + 1) * n - 1)) = 1
  exact hdegree ▸ h

end AffineTverberg.BadEdge.BoundaryJoinVertexIndexing
