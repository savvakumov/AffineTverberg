import AffineTverberg.GeometricLocalStar
import AffineTverberg.SimplicialBoundaryJoin

set_option linter.style.header false

/-!
# The combinatorial boundary is contained in the homology boundary

`AffineTverberg/GeometricLocalStar.lean` proves that every *carrier point*
(relative-interior point) of a boundary ridge of a simplicial ball lies in the
homology boundary of the polyhedron.  This file upgrades that to the whole
closed simplex of every boundary face, which is one of the two inclusions of the
identification

`Subtype.val ⁻¹' (simplicialBoundaryCarrier K n) = homologyBoundary ↥K.space (n - 1)`

still missing between the combinatorial and the homological boundary.

Two ingredients are supplied here:

* `isCarrierPoint_towards_centroid` — pushing any point of the closed simplex of
  a face `L` towards the centroid of `L` produces a carrier point of `L`.  This
  uses the actual barycentric coordinate functionals and the intersection axiom
  of a geometric simplicial complex, so relative-interior points are dense in
  every closed simplex of the complex.
* `IsSimplicialBall.isClosed_homologyBoundary` — the homology boundary of a
  simplicial ball is closed, since it is the preimage of the unit sphere under
  the ball homeomorphism.

The reverse inclusion is proved in `BoundaryIdentification.lean`, using the
mod-two cycle on the actual closed-star link, including the lower-dimensional
carrier faces. This module supplies the forward inclusion independently.
-/

noncomputable section

open Metric Set

namespace AffineTverberg

variable {e n : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- The value of an affine functional at the centroid of a finset. -/
theorem affine_apply_centroid {L : Finset (CoordinateSpace e)} (hne : L.Nonempty)
    (lam : CoordinateSpace e →ᵃ[ℝ] ℝ) :
    lam (L.centroid ℝ id) = ∑ u ∈ L, (L.card : ℝ)⁻¹ * lam u := by
  rw [Finset.centroid_def, Finset.map_affineCombination _ _ _
      (L.sum_centroidWeights_eq_one_of_nonempty ℝ hne),
    Finset.affineCombination_eq_linear_combination _ _ _
      (L.sum_centroidWeights_eq_one_of_nonempty ℝ hne)]
  exact Finset.sum_congr rfl fun u _ ↦ by simp [Finset.centroidWeights_apply, smul_eq_mul]

/-- **Relative-interior points are dense in every closed simplex.**  Moving a
point of the closed simplex of `L` towards the centroid of `L` gives a carrier
point of `L`. -/
theorem isCarrierPoint_towards_centroid {L : Finset (CoordinateSpace e)} (hL : L ∈ K.faces)
    {x : CoordinateSpace e} (hx : x ∈ convexHull ℝ (L : Set (CoordinateSpace e)))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    IsCarrierPoint K L ((1 - t) • x + t • L.centroid ℝ id) := by
  classical
  have hne := K.nonempty_of_mem_faces hL
  have hc : L.centroid ℝ id ∈ convexHull ℝ (L : Set (CoordinateSpace e)) :=
    L.centroid_mem_convexHull (R := ℝ) hne
  have hmem : ((1 - t) • x + t • L.centroid ℝ id) ∈
      convexHull ℝ (L : Set (CoordinateSpace e)) :=
    (convex_convexHull ℝ _) hx hc (by linarith) ht0.le (by ring)
  refine ⟨hmem, ?_⟩
  intro s hs hps
  by_contra hsub
  obtain ⟨v, hvL, hvs⟩ := Finset.not_subset.mp hsub
  -- the point lies in the closed simplex of `L ∩ s`
  have hint : ((1 - t) • x + t • L.centroid ℝ id) ∈
      convexHull ℝ ((L ∩ s : Finset (CoordinateSpace e)) : Set (CoordinateSpace e)) := by
    have hIn : convexHull ℝ (L : Set (CoordinateSpace e)) ∩
        convexHull ℝ (s : Set (CoordinateSpace e)) =
        convexHull ℝ ((L : Set (CoordinateSpace e)) ∩ (s : Set (CoordinateSpace e))) :=
      K.convexHull_inter_convexHull hL hs
    have hmem' : ((1 - t) • x + t • L.centroid ℝ id) ∈ convexHull ℝ
        ((L : Set (CoordinateSpace e)) ∩ (s : Set (CoordinateSpace e))) := by
      rw [← hIn]
      exact ⟨hmem, hps⟩
    simpa [Finset.coe_inter] using hmem'
  -- the barycentric coordinate of a vertex of `L` outside `s`
  have hvLs : v ∉ L ∩ s := fun h ↦ hvs (Finset.mem_inter.mp h).2
  obtain ⟨lam, hlam1, hlamnn, hlam0⟩ :=
    exists_vertexCoord (K.indep hL) hvL hvLs Finset.inter_subset_left
  have hzero : lam ((1 - t) • x + t • L.centroid ℝ id) = 0 := hlam0 _ hint
  -- but the coordinate is positive at the shifted point
  have hcombo : lam ((1 - t) • x + t • L.centroid ℝ id)
      = (1 - t) * lam x + t * lam (L.centroid ℝ id) := by
    have := Convex.combo_affine_apply (𝕜 := ℝ) (f := lam) (a := 1 - t) (b := t)
      (x := x) (y := L.centroid ℝ id) (by ring)
    simpa using this
  have hcpos : 0 < lam (L.centroid ℝ id) := by
    rw [affine_apply_centroid hne lam]
    have hcard : (0 : ℝ) < (L.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hne
    have hterm : ∀ u ∈ L, 0 ≤ (L.card : ℝ)⁻¹ * lam u := by
      intro u hu
      exact mul_nonneg (by positivity) (hlamnn u (subset_convexHull ℝ _ hu))
    have hle : (L.card : ℝ)⁻¹ * lam v ≤ ∑ u ∈ L, (L.card : ℝ)⁻¹ * lam u :=
      Finset.single_le_sum hterm hvL
    have hvpos : (0 : ℝ) < (L.card : ℝ)⁻¹ * lam v := by
      rw [hlam1, mul_one]
      positivity
    linarith
  have hxnn : 0 ≤ lam x := hlamnn x hx
  have hpos : 0 < lam ((1 - t) • x + t • L.centroid ℝ id) := by
    rw [hcombo]
    have h1 : 0 ≤ (1 - t) * lam x := mul_nonneg (by linarith) hxnn
    have h2 : 0 < t * lam (L.centroid ℝ id) := mul_pos ht0 hcpos
    linarith
  exact absurd hzero (ne_of_gt hpos)

namespace IsSimplicialBall

/-- The homology boundary of a simplicial ball is closed: it is the preimage of
the unit sphere under the ball homeomorphism. -/
theorem isClosed_homologyBoundary (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    IsClosed (homologyBoundary ↥K.space (n - 1)) := by
  have hdim : Module.finrank ℝ (CoordinateSpace n) = (n - 2) + 2 := by
    simp only [CoordinateSpace, Module.finrank_pi, Fintype.card_fin]
    omega
  have hdeg : n - 2 + 1 = n - 1 := by omega
  let h := hball.homeomorph_closedBall.some
  have hset : homologyBoundary ↥K.space (n - 1)
      = h ⁻¹' (homologyBoundary ↥(closedBall (0 : CoordinateSpace n) 1) (n - 1)) := by
    ext x
    exact homologyBoundary_congr h (n - 1) x
  rw [hset, ← hdeg, homologyBoundary_closedBall hdim]
  exact ((isClosed_sphere).preimage continuous_subtype_val).preimage h.continuous

/-- **The combinatorial boundary is contained in the homology boundary.**  Every
point of the closed simplex of a boundary face of a simplicial ball has
vanishing punctured homology in degree `n - 1`. -/
theorem boundaryCarrier_subset_homologyBoundary (hball : IsSimplicialBall n K) (hn : 2 ≤ n) :
    Subtype.val ⁻¹' (simplicialBoundaryCarrier K n) ⊆ homologyBoundary ↥K.space (n - 1) := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
  obtain ⟨L, hLridge, hsL⟩ := hs.2
  have hLface : L ∈ K.faces := hLridge.1
  have hxL : x.val ∈ convexHull ℝ (L : Set (CoordinateSpace e)) :=
    convexHull_mono (by exact_mod_cast hsL) hxs
  apply (hball.isClosed_homologyBoundary hn).closure_subset
  rw [Metric.mem_closure_iff]
  intro ε hε
  set c : CoordinateSpace e := L.centroid ℝ id with hcdef
  set t : ℝ := min 1 (ε / (‖c - x.val‖ + 1)) with htdef
  have hnormpos : (0 : ℝ) < ‖c - x.val‖ + 1 := by positivity
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have hcarrier : IsCarrierPoint K L ((1 - t) • x.val + t • c) :=
    isCarrierPoint_towards_centroid hLface hxL ht0 ht1
  refine ⟨⟨(1 - t) • x.val + t • c, hcarrier.mem_space hLface⟩,
    carrierPoint_boundaryRidge_mem_homologyBoundary hball hn hLridge hcarrier, ?_⟩
  have hdiff : ((1 - t) • x.val + t • c) - x.val = t • (c - x.val) := by
    module
  have hdist : dist x ⟨(1 - t) • x.val + t • c, hcarrier.mem_space hLface⟩
      = ‖x.val - ((1 - t) • x.val + t • c)‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
  rw [hdist, ← norm_neg, neg_sub, hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
  have hle : t ≤ ε / (‖c - x.val‖ + 1) := min_le_right _ _
  have hbound : t * ‖c - x.val‖ ≤ ε / (‖c - x.val‖ + 1) * ‖c - x.val‖ := by
    apply mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  have hlast : ε / (‖c - x.val‖ + 1) * ‖c - x.val‖ < ε := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hnormpos]
    nlinarith [norm_nonneg (c - x.val)]
  linarith

end IsSimplicialBall

end AffineTverberg
