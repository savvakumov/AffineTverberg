import AffineTverberg.BoundaryJoinPairModel
import AffineTverberg.SphereFundamentalCycle
import AffineTverberg.StarOrientationCycle

set_option linter.style.header false

/-!
# A fundamental cycle for the paper's actual boundary-join triangulation

The original finite topological-ball assumptions give a real top cycle on
the existing subdivision, with a nonzero coefficient on every top simplex.
This is orientation data for dual chains, not a replacement homology theory
or an additional hypothesis about the sphere.
-/

noncomputable section

namespace AffineTverberg.BadEdge.BoundaryJoinVertexIndexing

open AffineTverberg.Simplicial

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  (a : BoundaryJoinVertexIndexing n K m)

/-- The exact paper triangulation has a nonzero cycle with full top-simplex support. -/
theorem exists_join_fundamental_cycle (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    letI := a.subdivisionOrder
    ∃ c : Finset (Finset (Fin a.size)) → ℝ,
      c ∈ cycles ℝ a.joinComplex ((m + 1) * n) ∧ c ≠ 0 ∧
        ∀ σ ∈ a.joinComplex, σ.card = (m + 1) * n → c σ ≠ 0 := by
  let := a.subdivisionOrder
  let : DecidableEq (Finset (Fin a.size)) := a.subdivisionOrder.toDecidableEq
  have hK : FaceClosed a.joinComplex := by
    convert a.faceClosed_joinComplex using 1
  have hdim : 2 ≤ (m + 1) * n := by nlinarith
  have hshift : (m + 1) * n - 2 + 2 = (m + 1) * n := by omega
  have h := exists_fundamental_sphere_cycle hK ((m + 1) * n - 2)
    (fun σ hσ => by rw [hshift]; exact a.card_joinComplex_le hσ)
    (a.joinBarycentricSphereHomeomorph hball hn)
    (by rw [finrank_coordinateSpace, hshift])
  simpa only [hshift] using h

/-- The cycle may be normalized at any chosen top simplex of the paper's triangulation. -/
theorem exists_join_normalized_fundamental_cycle (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {σ : Finset (Finset (Fin a.size))} (hσ : σ ∈ a.joinComplex)
    (hσcard : σ.card = (m + 1) * n) :
    letI := a.subdivisionOrder
    ∃ c : Finset (Finset (Fin a.size)) → ℝ,
      c ∈ cycles ℝ a.joinComplex ((m + 1) * n) ∧ c σ = 1 ∧
        ∀ τ ∈ a.joinComplex, τ.card = (m + 1) * n → c τ ≠ 0 := by
  let := a.subdivisionOrder
  let : DecidableEq (Finset (Fin a.size)) := a.subdivisionOrder.toDecidableEq
  have hK : FaceClosed a.joinComplex := by
    convert a.faceClosed_joinComplex using 1
  have hdim : 2 ≤ (m + 1) * n := by nlinarith
  have hshift : (m + 1) * n - 2 + 2 = (m + 1) * n := by omega
  have h := exists_normalized_sphere_cycle hK ((m + 1) * n - 2)
    (fun τ hτ => by rw [hshift]; exact a.card_joinComplex_le hτ)
    (a.joinBarycentricSphereHomeomorph hball hn)
    (by rw [finrank_coordinateSpace, hshift]) hσ (by rw [hshift]; exact hσcard)
  simpa only [hshift] using h

/-- One global cycle gives explicit nonzero local homology cycles at every
nonempty face of the paper's actual triangulation. -/
theorem exists_join_compatible_local_cycles (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    letI := a.subdivisionOrder
    ∃ c : Finset (Finset (Fin a.size)) → ℝ,
      c ∈ cycles ℝ a.joinComplex ((m + 1) * n) ∧ c ≠ 0 ∧
        ∀ L ∈ a.joinComplex, L.Nonempty →
          boundary ℝ (Finset (Fin a.size)) (cofaceRestriction L c) ∈
            cycles ℝ (starBoundaryFamily a.joinComplex L) ((m + 1) * n - 1) ∧
          boundary ℝ (Finset (Fin a.size)) (cofaceRestriction L c) ∉
            boundaries ℝ (starBoundaryFamily a.joinComplex L) ((m + 1) * n - 1) := by
  let := a.subdivisionOrder
  let : DecidableEq (Finset (Fin a.size)) := a.subdivisionOrder.toDecidableEq
  obtain ⟨c, hc, hc0, hcfull⟩ := a.exists_join_fundamental_cycle hball hn
  refine ⟨c, hc, hc0, ?_⟩
  intro L hL hLne
  have hK : FaceClosed a.joinComplex := by
    convert a.faceClosed_joinComplex using 1
  have hpos : 0 < (m + 1) * n := Nat.mul_pos (by omega) (by omega)
  have hshift : (m + 1) * n - 1 + 1 = (m + 1) * n := by omega
  have hc' : c ∈ cycles ℝ a.joinComplex ((m + 1) * n - 1 + 1) := by
    rwa [hshift]
  obtain ⟨F, hF, hLF, hFcard⟩ := a.exists_top_simplex_extension hball hn hL
  exact ⟨boundary_cofaceRestriction_mem_cycles hK hc' L,
    boundary_cofaceRestriction_notMem_boundaries
      (fun s hs => by rw [hshift]; exact a.card_joinComplex_le hs)
      hLF hLne (hcfull F hF hFcard)⟩

end AffineTverberg.BadEdge.BoundaryJoinVertexIndexing
