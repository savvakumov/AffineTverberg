import AffineTverberg.BallPuncturedRank
import AffineTverberg.SimplicialBallLocalHomology

set_option linter.style.header false

/-!
# The homologically detected boundary of a space, and of a simplicial ball

For a space `X` and a degree `k`, the *homology boundary*

`homologyBoundary X k = {p | Subsingleton (H_k (X \ {p}))}`

is a manifestly topological invariant: a homeomorphism `X ≃ₜ Y` restricts to a
homeomorphism of the two homology boundaries.

For the closed unit ball of an `(n + 2)`-dimensional normed space in degree
`n + 1` this set is exactly the unit sphere, by the two local computations of
`AffineTverberg.PuncturedBall` and `AffineTverberg.BallPuncturedRank`
(rank one at an interior point, rank zero at a boundary point).

Consequently, for a simplicial ball `IsSimplicialBall n K` with `2 ≤ n`, the
homology boundary of the actual polyhedron `K.space` in degree `n - 1` is
homeomorphic to the unit `(n-1)`-sphere of `CoordinateSpace n`.  No property of
`K` beyond the hypotheses of `IsSimplicialBall` is used.

This is the topological half of the boundary-sphere statement needed by
`AffineTverberg.BoundaryJoinSphere`. The combinatorial identification of this
homology boundary with `simplicialBoundaryCarrier K n`, the union of the
faces contained in boundary ridges, is proved later in
`BoundaryIdentification.lean`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set

namespace AffineTverberg

section General

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The set of points whose complement has vanishing degree-`k` homology. -/
def homologyBoundary (X : Type) [TopologicalSpace X] (k : ℕ) : Set X :=
  {p | Subsingleton ((realSingularHomology k).obj (TopCat.of ↥{q : X | q ≠ p}))}

theorem mem_homologyBoundary_iff {k : ℕ} {p : X} :
    p ∈ homologyBoundary X k ↔
      Subsingleton ((realSingularHomology k).obj (TopCat.of ↥{q : X | q ≠ p})) :=
  Iff.rfl

/-- The homology boundary is a topological invariant. -/
theorem homologyBoundary_congr (e : X ≃ₜ Y) (k : ℕ) (p : X) :
    p ∈ homologyBoundary X k ↔ e p ∈ homologyBoundary Y k := by
  have hiso := (realSingularHomologyIsoOfHomotopyEquiv
    (puncturedHomeomorph e p).toHomotopyEquiv k).toLinearEquiv
  exact hiso.toEquiv.subsingleton_congr

/-- A homeomorphism restricts to a homeomorphism of homology boundaries. -/
def homologyBoundaryHomeomorph (e : X ≃ₜ Y) (k : ℕ) :
    ↥(homologyBoundary X k) ≃ₜ ↥(homologyBoundary Y k) :=
  e.subtype (fun x => homologyBoundary_congr e k x)

end General

section Ball

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The homology boundary of a closed ball is its unit sphere.** -/
theorem homologyBoundary_closedBall {n : ℕ} (hdim : Module.finrank ℝ E = n + 2) :
    homologyBoundary ↥(closedBall (0 : E) 1) (n + 1) =
      Subtype.val ⁻¹' (sphere (0 : E) 1) := by
  ext p
  rw [mem_homologyBoundary_iff, mem_preimage, mem_sphere_zero_iff_norm]
  exact subsingleton_homology_ballPunctured_iff hdim p

/-- The homology boundary of the closed ball, as a space, is the sphere. -/
def closedBallHomologyBoundaryHomeomorph {n : ℕ} (hdim : Module.finrank ℝ E = n + 2) :
    ↥(homologyBoundary ↥(closedBall (0 : E) 1) (n + 1)) ≃ₜ ↥(sphere (0 : E) 1) :=
  (Homeomorph.setCongr (homologyBoundary_closedBall hdim)).trans
    (subsetSubtypeHomeomorph sphere_subset_closedBall)

end Ball

namespace IsSimplicialBall

variable {e n : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- **The homology boundary of a simplicial ball is a sphere.**  Only the
hypotheses of `IsSimplicialBall` and `2 ≤ n` are used. -/
def homologyBoundaryHomeomorphSphere (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    ↥(homologyBoundary ↥K.space (n - 1)) ≃ₜ ↥(sphere (0 : CoordinateSpace n) 1) := by
  have hdim : Module.finrank ℝ (CoordinateSpace n) = (n - 2) + 2 := by
    simp only [CoordinateSpace, Module.finrank_pi, Fintype.card_fin]
    omega
  have hdeg : n - 2 + 1 = n - 1 := by omega
  let h := hball.homeomorph_closedBall.some
  refine (homologyBoundaryHomeomorph h (n - 1)).trans ?_
  rw [← hdeg]
  exact closedBallHomologyBoundaryHomeomorph hdim

/-- The homology boundary of a simplicial ball is nonempty: it is a sphere of
positive dimension. -/
theorem homologyBoundary_nonempty (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    (homologyBoundary ↥K.space (n - 1)).Nonempty := by
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨s, hs⟩ := (NormedSpace.sphere_nonempty (E := CoordinateSpace n) (x := 0)
    (r := 1)).mpr zero_le_one
  let p := (homologyBoundaryHomeomorphSphere hball hn).symm ⟨s, hs⟩
  exact ⟨p.1, p.2⟩

end IsSimplicialBall

end AffineTverberg
