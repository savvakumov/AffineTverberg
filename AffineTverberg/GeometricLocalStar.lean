import AffineTverberg.HomologyBoundary
import AffineTverberg.SimplicialBallRidge

set_option linter.style.header false

/-!
# The local star of a face of a geometric simplicial complex

This file proves the local geometry needed to decide, homologically, whether a
point of the polyhedron of a finite geometric simplicial complex is a boundary
point.

* `face_subset_of_centroid_mem` — if the centroid of a face `L` lies in the
  closed simplex of a face `s`, then `L ⊆ s`.  This is unique barycentric
  representation, using the affine independence of `L` and the intersection
  axiom of a simplicial complex.
* `exists_localRadius` — around every point of `K.space` there is a radius
  within which only the closed simplices *through that point* are met.
* `exists_localRadius_facet` — consequently, around the centroid of a face `L`
  all of `K.space` is contained in `convexHull F` as soon as every face
  containing `L` is contained in `F`; for a boundary ridge, `F` is its unique
  facet.
* `contractibleSpace_punctured_localCell` — the punctured local cell
  `(convexHull F ∩ ball p ε) \ {p}` at the centroid `p` of a proper face
  `L ⊆ F` is star convex about a nearby point of `convexHull F` off
  `convexHull L`, hence contractible.  The witness that the puncture does not
  disconnect anything is the barycentric coordinate functional of a vertex of
  `F` outside `L`.
* `IsSimplicialBall.centroid_boundaryRidge_mem_homologyBoundary` — therefore
  the centroid of a boundary ridge of a simplicial ball lies in the homology
  boundary of `K.space` (in the sense of `AffineTverberg.HomologyBoundary`):
  its complement has vanishing homology in degree `n - 1`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set

namespace AffineTverberg

/-! ### Unique barycentric representation -/

/-- The centroid of an affinely independent finset lies in the affine span of a
subset only if that subset is everything. -/
theorem subset_of_centroid_mem_affineSpan {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L T : Finset E} (hne : L.Nonempty) (hind : AffineIndependent ℝ ((↑) : ↥L → E))
    (hT : T ⊆ L) (hmem : L.centroid ℝ id ∈ affineSpan ℝ (T : Set E)) : L ⊆ T := by
  classical
  have hcard : (0 : ℝ) < (L.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hne
  set w : ↥L → ℝ := fun _ => (L.card : ℝ)⁻¹ with hw
  have hsum : ∑ i : ↥L, w i = 1 := by
    simp [hw]
    field_simp
  have heq : Finset.affineCombination ℝ (Finset.univ : Finset ↥L) ((↑) : ↥L → E) w
      = L.centroid ℝ id := by
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum]
    rw [Finset.centroid_def, Finset.affineCombination_eq_linear_combination]
    · simp only [hw, Finset.centroidWeights_apply, id]
      exact Finset.sum_coe_sort L (fun x => (L.card : ℝ)⁻¹ • x)
    · simp [Finset.centroidWeights_apply, Finset.sum_const]
      field_simp
  intro x hx
  by_contra hxT
  have hspan : Finset.affineCombination ℝ (Finset.univ : Finset ↥L) ((↑) : ↥L → E) w ∈
      affineSpan ℝ (((↑) : ↥L → E) '' {i : ↥L | (i : E) ∈ T}) := by
    have himg : ((↑) : ↥L → E) '' {i : ↥L | (i : E) ∈ T} = (T : Set E) := by
      ext y
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact hi
      · intro hy
        exact ⟨⟨y, hT hy⟩, hy, rfl⟩
    rw [himg, heq]
    exact hmem
  have hzero := hind.eq_zero_of_affineCombination_mem_affineSpan hsum hspan
    (Finset.mem_univ ⟨x, hx⟩) (by simpa using hxT)
  exact (inv_ne_zero (ne_of_gt hcard)) hzero

variable {e n : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- If the centroid of a face lies in the closed simplex of another face, the
first face is contained in the second. -/
theorem face_subset_of_centroid_mem {L s : Finset (CoordinateSpace e)}
    (hL : L ∈ K.faces) (hs : s ∈ K.faces)
    (hmem : L.centroid ℝ id ∈ convexHull ℝ (s : Set (CoordinateSpace e))) : L ⊆ s := by
  classical
  have hne := K.nonempty_of_mem_faces hL
  have hcent := L.centroid_mem_convexHull (R := ℝ) hne
  have hint : L.centroid ℝ id ∈
      convexHull ℝ ((L ∩ s : Finset (CoordinateSpace e)) : Set (CoordinateSpace e)) := by
    have hIn : convexHull ℝ (L : Set (CoordinateSpace e)) ∩
        convexHull ℝ (s : Set (CoordinateSpace e)) =
        convexHull ℝ ((L : Set (CoordinateSpace e)) ∩ (s : Set (CoordinateSpace e))) :=
      K.convexHull_inter_convexHull hL hs
    have : L.centroid ℝ id ∈ convexHull ℝ
        ((L : Set (CoordinateSpace e)) ∩ (s : Set (CoordinateSpace e))) := by
      rw [← hIn]
      exact ⟨hcent, hmem⟩
    simpa [Finset.coe_inter] using this
  have hsub : L ⊆ L ∩ s :=
    subset_of_centroid_mem_affineSpan hne (K.indep hL) Finset.inter_subset_left
      (convexHull_subset_affineSpan _ hint)
  exact fun x hx => (Finset.mem_inter.mp (hsub hx)).2

/-- The centroid of a face lies in the polyhedron. -/
theorem centroid_mem_space {L : Finset (CoordinateSpace e)} (hL : L ∈ K.faces) :
    L.centroid ℝ id ∈ K.space :=
  Geometry.SimplicialComplex.convexHull_subset_space hL
    (L.centroid_mem_convexHull (R := ℝ) (K.nonempty_of_mem_faces hL))

/-! ### Carrier points -/

/-- `p` is a point of the polyhedron with carrier face `s`: it lies in the closed
simplex of `s`, and every face whose closed simplex contains `p` contains `s`.
This is the relative interior of the simplex of `s`, phrased combinatorially. -/
def IsCarrierPoint (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (s : Finset (CoordinateSpace e)) (p : CoordinateSpace e) : Prop :=
  p ∈ convexHull ℝ (s : Set (CoordinateSpace e)) ∧
    ∀ t ∈ K.faces, p ∈ convexHull ℝ (t : Set (CoordinateSpace e)) → s ⊆ t

/-- The centroid of a face is a carrier point of that face. -/
theorem isCarrierPoint_centroid {L : Finset (CoordinateSpace e)} (hL : L ∈ K.faces) :
    IsCarrierPoint K L (L.centroid ℝ id) :=
  ⟨L.centroid_mem_convexHull (R := ℝ) (K.nonempty_of_mem_faces hL),
    fun _ ht hmem => face_subset_of_centroid_mem hL ht hmem⟩

theorem IsCarrierPoint.mem_space {L : Finset (CoordinateSpace e)} {p : CoordinateSpace e}
    (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p) : p ∈ K.space :=
  Geometry.SimplicialComplex.convexHull_subset_space hL hp.1

/-- A carrier point of `L` avoids the closed simplex of every proper face of
`L`. -/
theorem IsCarrierPoint.notMem_convexHull_erase {L : Finset (CoordinateSpace e)}
    {p : CoordinateSpace e} (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p)
    {v : CoordinateSpace e} (hv : v ∈ L) (hne : (L.erase v).Nonempty) :
    p ∉ convexHull ℝ ((L.erase v : Finset (CoordinateSpace e)) : Set (CoordinateSpace e)) := by
  intro hmem
  have hface : L.erase v ∈ K.faces := K.down_closed hL (Finset.erase_subset _ _) hne
  exact (Finset.notMem_erase v L) (hp.2 _ hface hmem hv)

/-! ### The local radius -/

/-- Around every point there is a radius within which the polyhedron consists
only of closed simplices through that point. -/
theorem exists_localRadius (hfin : K.faces.Finite) (p : CoordinateSpace e) :
    ∃ ε > 0, ∀ x ∈ K.space, ‖x - p‖ < ε →
      ∃ s ∈ K.faces, p ∈ convexHull ℝ (s : Set (CoordinateSpace e)) ∧
        x ∈ convexHull ℝ (s : Set (CoordinateSpace e)) := by
  classical
  set U : Set (CoordinateSpace e) :=
    ⋃ s ∈ {s | s ∈ K.faces ∧ p ∉ convexHull ℝ (s : Set (CoordinateSpace e))},
      convexHull ℝ (s : Set (CoordinateSpace e)) with hU
  have hUclosed : IsClosed U := by
    apply Set.Finite.isClosed_biUnion (hfin.subset fun s hs => hs.1)
    exact fun s _ => (s.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hpU : p ∉ U := by
    intro h
    obtain ⟨s, hs, hps⟩ := mem_iUnion₂.mp h
    exact hs.2 hps
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hUclosed.isOpen_compl p hpU
  refine ⟨ε, hε, fun x hx hxd => ?_⟩
  obtain ⟨s, hs, hxs⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
  refine ⟨s, hs, ?_, hxs⟩
  by_contra hps
  have hxU : x ∈ U := mem_iUnion₂.mpr ⟨s, ⟨hs, hps⟩, hxs⟩
  have hxball : x ∈ ball p ε := by
    simpa [Metric.mem_ball, dist_eq_norm] using hxd
  exact (hball hxball) hxU

/-- If every face containing `L` is contained in `F`, then near a carrier point
of `L` the polyhedron is contained in the closed simplex of `F`. -/
theorem exists_localRadius_of_carrier (hfin : K.faces.Finite)
    {L F : Finset (CoordinateSpace e)} {p : CoordinateSpace e}
    (hp : IsCarrierPoint K L p) (huniq : ∀ G ∈ K.faces, L ⊆ G → G ⊆ F) :
    ∃ ε > 0, ∀ x ∈ K.space, ‖x - p‖ < ε →
      x ∈ convexHull ℝ (F : Set (CoordinateSpace e)) := by
  obtain ⟨ε, hε, h⟩ := exists_localRadius hfin p
  refine ⟨ε, hε, fun x hx hxd => ?_⟩
  obtain ⟨s, hs, hps, hxs⟩ := h x hx hxd
  have hLs := hp.2 s hs hps
  exact convexHull_mono (by exact_mod_cast huniq s hs hLs) hxs

/-- The same statement at the centroid of `L`. -/
theorem exists_localRadius_facet (hfin : K.faces.Finite)
    {L F : Finset (CoordinateSpace e)} (hL : L ∈ K.faces)
    (huniq : ∀ G ∈ K.faces, L ⊆ G → G ⊆ F) :
    ∃ ε > 0, ∀ x ∈ K.space, ‖x - L.centroid ℝ id‖ < ε →
      x ∈ convexHull ℝ (F : Set (CoordinateSpace e)) :=
  exists_localRadius_of_carrier hfin (isCarrierPoint_centroid hL) huniq

/-- For a boundary ridge every face through it lies in its unique facet. -/
theorem subset_facet_of_isBoundaryRidge (hfin : K.faces.Finite)
    {L F : Finset (CoordinateSpace e)}
    (huniq : ∀ G ∈ K.facets, L ⊆ G → G = F) :
    ∀ G ∈ K.faces, L ⊆ G → G ⊆ F := by
  intro G hG hLG
  obtain ⟨G', hG', hGG'⟩ := exists_facet_superset hfin hG
  have : G' = F := huniq G' hG' (hLG.trans hGG')
  exact this ▸ hGG'

/-! ### The barycentric coordinate functional of a vertex -/

/-- For an affinely independent finset `F`, a vertex `v ∈ F` and a subset `L`
not containing `v`, there is an affine functional which is `1` at `v`,
nonnegative on the closed simplex of `F` and zero on the closed simplex of
`L`.  It is the barycentric coordinate of `v` in an affine basis extending
`F`. -/
theorem exists_vertexCoord {F L : Finset (CoordinateSpace e)} {v : CoordinateSpace e}
    (hind : AffineIndependent ℝ ((↑) : ↑F → CoordinateSpace e))
    (hv : v ∈ F) (hvL : v ∉ L) (hLF : L ⊆ F) :
    ∃ lam : CoordinateSpace e →ᵃ[ℝ] ℝ, lam v = 1 ∧
      (∀ z ∈ convexHull ℝ (F : Set (CoordinateSpace e)), 0 ≤ lam z) ∧
      (∀ z ∈ convexHull ℝ (L : Set (CoordinateSpace e)), lam z = 0) := by
  classical
  have hind' : AffineIndependent ℝ
      ((fun x => x) : ((F : Set (CoordinateSpace e)) : Type) → CoordinateSpace e) := hind
  obtain ⟨t, hFt, hindt, hspant⟩ := exists_subset_affineIndependent_affineSpan_eq_top hind'
  have hrange : affineSpan ℝ (Set.range (fun x : (↑t : Type) => (x : CoordinateSpace e))) = ⊤ := by
    rwa [Subtype.range_coe]
  let b : AffineBasis (↑t : Type) ℝ (CoordinateSpace e) :=
    ⟨fun x => (x : CoordinateSpace e), hindt, hrange⟩
  have hbapply : ∀ x : (↑t : Type), b x = (x : CoordinateSpace e) := fun _ => rfl
  refine ⟨b.coord ⟨v, hFt hv⟩, ?_, ?_, ?_⟩
  · exact b.coord_apply_eq ⟨v, hFt hv⟩
  · intro z hz
    have himg : (b.coord ⟨v, hFt hv⟩) '' (convexHull ℝ (F : Set (CoordinateSpace e))) =
        convexHull ℝ ((b.coord ⟨v, hFt hv⟩) '' (F : Set (CoordinateSpace e))) :=
      AffineMap.image_convexHull _ _
    have hmem : (b.coord ⟨v, hFt hv⟩) z ∈
        convexHull ℝ ((b.coord ⟨v, hFt hv⟩) '' (F : Set (CoordinateSpace e))) := by
      rw [← himg]
      exact ⟨z, hz, rfl⟩
    have hsub : convexHull ℝ ((b.coord ⟨v, hFt hv⟩) '' (F : Set (CoordinateSpace e))) ⊆
        Set.Ici (0 : ℝ) := by
      apply convexHull_min _ (convex_Ici 0)
      rintro _ ⟨x, hx, rfl⟩
      by_cases hxv : x = v
      · subst hxv
        have : (b.coord ⟨x, hFt hv⟩) x = 1 := b.coord_apply_eq ⟨x, hFt hv⟩
        simp [this]
      · have : (b.coord ⟨v, hFt hv⟩) x = 0 := by
          have hne : (⟨v, hFt hv⟩ : (↑t : Type)) ≠ ⟨x, hFt hx⟩ := by
            simp only [ne_eq, Subtype.mk.injEq]
            exact fun h => hxv h.symm
          simpa [hbapply] using b.coord_apply_ne hne
        simp [this]
    exact hsub hmem
  · intro z hz
    have himg : (b.coord ⟨v, hFt hv⟩) '' (convexHull ℝ (L : Set (CoordinateSpace e))) =
        convexHull ℝ ((b.coord ⟨v, hFt hv⟩) '' (L : Set (CoordinateSpace e))) :=
      AffineMap.image_convexHull _ _
    have hmem : (b.coord ⟨v, hFt hv⟩) z ∈
        convexHull ℝ ((b.coord ⟨v, hFt hv⟩) '' (L : Set (CoordinateSpace e))) := by
      rw [← himg]
      exact ⟨z, hz, rfl⟩
    have hsub : convexHull ℝ ((b.coord ⟨v, hFt hv⟩) '' (L : Set (CoordinateSpace e))) ⊆
        {(0 : ℝ)} := by
      apply convexHull_min _ (convex_singleton 0)
      rintro _ ⟨x, hx, rfl⟩
      have hxv : x ≠ v := fun h => hvL (h ▸ hx)
      have hne : (⟨v, hFt hv⟩ : (↑t : Type)) ≠ ⟨x, hFt (hLF hx)⟩ := by
        simp only [ne_eq, Subtype.mk.injEq]
        exact fun h => hxv h.symm
      have : (b.coord ⟨v, hFt hv⟩) x = 0 := by
        simpa [hbapply] using b.coord_apply_ne hne
      simp [this]
    exact hsub hmem

/-! ### The punctured local cell is contractible -/

/-- The local cell of `F` at the centroid `p` of a face `L ⊆ F`, punctured at
`p`, is star convex about the point obtained by moving from `p` towards a
vertex `v` of `F` outside `L`.  The barycentric coordinate of `v` is positive
at every point of that segment, and vanishes at `p`. -/
theorem starConvex_punctured_localCell {F L : Finset (CoordinateSpace e)}
    (hind : AffineIndependent ℝ ((↑) : ↑F → CoordinateSpace e))
    {p : CoordinateSpace e} (hpL : p ∈ convexHull ℝ (L : Set (CoordinateSpace e)))
    (hLF : L ⊆ F) {v : CoordinateSpace e} (hv : v ∈ F) (hvL : v ∉ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ q ∈ (convexHull ℝ (F : Set (CoordinateSpace e)) ∩ ball p ε) \ {p},
      StarConvex ℝ q ((convexHull ℝ (F : Set (CoordinateSpace e)) ∩ ball p ε) \ {p}) := by
  classical
  obtain ⟨lam, hlv, hlF, hlL⟩ := exists_vertexCoord hind hv hvL hLF
  have hpF : p ∈ convexHull ℝ (F : Set (CoordinateSpace e)) :=
    convexHull_mono (by exact_mod_cast hLF) hpL
  have hlp : lam p = 0 := hlL p hpL
  have hvF : v ∈ convexHull ℝ (F : Set (CoordinateSpace e)) := subset_convexHull ℝ _ hv
  have hvp : v ≠ p := by
    intro h
    rw [h, hlp] at hlv
    exact zero_ne_one hlv
  have hd : 0 < ‖v - p‖ := norm_sub_pos_iff.mpr hvp
  set τ : ℝ := min (1 / 2) (ε / (2 * ‖v - p‖)) with hτ
  have hτ0 : 0 < τ := lt_min (by norm_num) (by positivity)
  have hτ1 : τ ≤ 1 := le_trans (min_le_left _ _) (by norm_num)
  set q : CoordinateSpace e := AffineMap.lineMap p v τ with hq
  have hqF : q ∈ convexHull ℝ (F : Set (CoordinateSpace e)) :=
    (convex_convexHull ℝ _).lineMap_mem hpF hvF ⟨hτ0.le, hτ1⟩
  have hqsub : q - p = τ • (v - p) := by
    rw [hq, AffineMap.lineMap_apply_module]
    module
  have hqball : q ∈ ball p ε := by
    have hnorm : ‖q - p‖ = τ * ‖v - p‖ := by
      rw [hqsub, norm_smul, Real.norm_eq_abs, abs_of_pos hτ0]
    have hlt : τ * ‖v - p‖ < ε := by
      have hτle : τ ≤ ε / (2 * ‖v - p‖) := min_le_right _ _
      have hmul : τ * ‖v - p‖ ≤ (ε / (2 * ‖v - p‖)) * ‖v - p‖ :=
        mul_le_mul_of_nonneg_right hτle (norm_nonneg _)
      have heq : (ε / (2 * ‖v - p‖)) * ‖v - p‖ = ε / 2 := by
        field_simp
      rw [heq] at hmul
      linarith
    simpa [Metric.mem_ball, dist_eq_norm, hnorm] using hlt
  have hlq : lam q = τ := by
    rw [hq, AffineMap.apply_lineMap, hlv, hlp, AffineMap.lineMap_apply_module]
    simp
  have hqne : q ≠ p := by
    intro h
    rw [h, hlp] at hlq
    exact (ne_of_gt hτ0) hlq.symm
  refine ⟨q, ⟨⟨hqF, hqball⟩, hqne⟩, ?_⟩
  intro y hy a b ha hb hab
  have hconv : Convex ℝ (convexHull ℝ (F : Set (CoordinateSpace e)) ∩ ball p ε) :=
    (convex_convexHull ℝ _).inter (convex_ball p ε)
  have hz : a • q + b • y ∈ convexHull ℝ (F : Set (CoordinateSpace e)) ∩ ball p ε :=
    hconv ⟨hqF, hqball⟩ hy.1 ha hb hab
  refine ⟨hz, ?_⟩
  intro hzp
  rcases eq_or_lt_of_le ha with h0 | hpos
  · have hb1 : b = 1 := by linarith [h0.symm]
    have hzy : a • q + b • y = y := by
      rw [← h0, hb1]
      simp
    rw [hzy] at hzp
    exact hy.2 hzp
  · have hline : a • q + b • y = AffineMap.lineMap y q a := by
      rw [AffineMap.lineMap_apply_module]
      have hb' : b = 1 - a := by linarith
      rw [hb']
      module
    have hlz : lam (a • q + b • y) = (1 - a) * lam y + a * τ := by
      rw [hline, AffineMap.apply_lineMap, hlq, AffineMap.lineMap_apply_module]
      simp
    have hly : 0 ≤ lam y := hlF y hy.1.1
    have hposz : 0 < lam (a • q + b • y) := by
      rw [hlz]
      have hnn : 0 ≤ (1 - a) * lam y := mul_nonneg (by linarith) hly
      nlinarith
    have hzero : lam (a • q + b • y) = 0 := by
      rw [show a • q + b • y = p from hzp]
      exact hlp
    linarith

/-- The punctured local cell is contractible. -/
theorem contractibleSpace_punctured_localCell {F L : Finset (CoordinateSpace e)}
    (hind : AffineIndependent ℝ ((↑) : ↑F → CoordinateSpace e))
    {p : CoordinateSpace e} (hpL : p ∈ convexHull ℝ (L : Set (CoordinateSpace e)))
    (hLF : L ⊆ F) {v : CoordinateSpace e} (hv : v ∈ F) (hvL : v ∉ L)
    {ε : ℝ} (hε : 0 < ε) :
    ContractibleSpace ↥((convexHull ℝ (F : Set (CoordinateSpace e)) ∩ ball p ε) \ {p}) := by
  obtain ⟨q, hq, hstar⟩ := starConvex_punctured_localCell hind hpL hLF hv hvL hε
  exact hstar.contractibleSpace ⟨q, hq⟩

/-! ### Boundary ridges give homology boundary points -/

namespace IsSimplicialBall

/-- The polyhedron of a simplicial ball is contractible. -/
theorem contractibleSpace_space (hball : IsSimplicialBall n K) : ContractibleSpace ↥K.space := by
  have h := hball.homeomorph_closedBall.some
  have : ContractibleSpace ↥(closedBall (0 : CoordinateSpace n) 1) :=
    (convex_closedBall (0 : CoordinateSpace n) 1).contractibleSpace ⟨0, by simp⟩
  exact h.toHomotopyEquiv.contractibleSpace

/-- **Every carrier point of a boundary ridge is a homology boundary point.**
Near such a point the polyhedron is the single closed facet through the ridge,
so the punctured neighbourhood is contractible, and Mayer-Vietoris against the
contractible polyhedron kills the homology of the complement of the point. -/
theorem carrierPoint_boundaryRidge_mem_homologyBoundary
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {L : Finset (CoordinateSpace e)} (hL : IsBoundaryRidge n K L)
    {p : CoordinateSpace e} (hp : IsCarrierPoint K L p) :
    (⟨p, hp.mem_space hL.1⟩ : ↥K.space) ∈ homologyBoundary ↥K.space (n - 1) := by
  classical
  obtain ⟨F, hFmem, huniq'⟩ := hL.2.2
  have hF : F ∈ K.facets := hFmem.1
  have hLF : L ⊆ F := hFmem.2
  have hFfaces : F ∈ K.faces := Geometry.SimplicialComplex.facets_subset hF
  have huniq : ∀ G ∈ K.facets, L ⊆ G → G = F := fun G hG hLG => huniq' G ⟨hG, hLG⟩
  obtain ⟨ε, hε, hloc⟩ := exists_localRadius_of_carrier hball.finite_faces hp
    (subset_facet_of_isBoundaryRidge hball.finite_faces huniq)
  have hpspace : p ∈ K.space := hp.mem_space hL.1
  set P : ↥K.space := ⟨p, hpspace⟩ with hP
  set C : Set (CoordinateSpace e) := convexHull ℝ (F : Set (CoordinateSpace e)) ∩ ball p ε with hC
  -- a vertex of the facet outside the ridge
  have hLne : L.Nonempty := Finset.card_pos.mp (by rw [hL.2.1]; omega)
  have hcardF : F.card = n + 1 := hball.pure F hF
  have hssub : L ⊂ F := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨hLF, fun hLeq => ?_⟩
    have hc := hL.2.1
    rw [hLeq, hcardF] at hc
    omega
  obtain ⟨v, hvF, hvL⟩ := Finset.exists_of_ssubset hssub
  -- the punctured local cell is contractible
  have hcontr : ContractibleSpace ↥(C \ {p}) :=
    contractibleSpace_punctured_localCell (K.indep hFfaces) hp.1 hLF hvF hvL hε
  -- the Mayer-Vietoris cover of the polyhedron
  set A : Set ↥K.space := {q | q ≠ P} with hA
  set B : Set ↥K.space := {q | ‖(q : CoordinateSpace e) - p‖ < ε} with hB
  have hAopen : IsOpen A := isOpen_compl_singleton
  have hBopen : IsOpen B := by
    have hcont : Continuous fun q : ↥K.space => ‖(q : CoordinateSpace e) - p‖ :=
      continuous_norm.comp (continuous_subtype_val.sub continuous_const)
    exact isOpen_lt hcont continuous_const
  have hcov : ∀ q : ↥K.space, q ∈ A ∨ q ∈ B := by
    intro q
    by_cases h : q = P
    · refine Or.inr ?_
      change ‖(q : CoordinateSpace e) - p‖ < ε
      rw [h, hP]
      simpa using hε
    · exact Or.inl h
  have hCsub : C \ {p} ⊆ K.space := fun x hx =>
    Geometry.SimplicialComplex.convexHull_subset_space hFfaces hx.1.1
  have hinter : A ∩ B = Subtype.val ⁻¹' (C \ {p}) := by
    ext q
    constructor
    · rintro ⟨h1, h2⟩
      have h2' : ‖(q : CoordinateSpace e) - p‖ < ε := h2
      have hball' : (q : CoordinateSpace e) ∈ ball p ε := by
        simpa [Metric.mem_ball, dist_eq_norm] using h2'
      exact ⟨⟨hloc q.val q.property h2', hball'⟩, fun hq => h1 (Subtype.ext hq)⟩
    · rintro ⟨⟨-, h2⟩, h3⟩
      refine ⟨fun hq => h3 (by rw [hq, hP]; rfl), ?_⟩
      change ‖(q : CoordinateSpace e) - p‖ < ε
      simpa [Metric.mem_ball, dist_eq_norm] using h2
  have hhomeo : ↥(A ∩ B) ≃ₜ ↥(C \ {p}) :=
    (Homeomorph.setCongr hinter).trans (subsetSubtypeHomeomorph hCsub)
  have hsubint : Subsingleton ((realSingularHomology (n - 1)).obj (TopCat.of ↥(A ∩ B))) := by
    have hsub0 : Subsingleton ((realSingularHomology (n - 1)).obj (TopCat.of ↥(C \ {p}))) :=
      realSingularHomology_subsingleton_of_contractible ↥(C \ {p}) (n - 1) (by omega)
    have hiso := (realSingularHomologyIsoOfHomotopyEquiv
      hhomeo.toHomotopyEquiv (n - 1)).toLinearEquiv
    exact hiso.toEquiv.subsingleton_congr.mpr hsub0
  -- the polyhedron itself is contractible
  have : ContractibleSpace ↥K.space := hball.contractibleSpace_space
  have hXzero : IsZero ((realSingularHomology (n - 1)).obj (TopCat.of ↥K.space)) := by
    have : Subsingleton ((realSingularHomology (n - 1)).obj (TopCat.of ↥K.space)) :=
      realSingularHomology_subsingleton_of_contractible ↥K.space (n - 1) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  have hsurj := AffChain.surjective_homology_inter_left
    (X := TopCat.of ↥K.space) A B hAopen hBopen hcov (n - 1) hXzero
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := hsurj x
  obtain ⟨b, rfl⟩ := hsurj y
  rw [Subsingleton.elim a b]

/-- The centroid of a boundary ridge is a homology boundary point. -/
theorem centroid_boundaryRidge_mem_homologyBoundary
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {L : Finset (CoordinateSpace e)} (hL : IsBoundaryRidge n K L) :
    (⟨L.centroid ℝ id, centroid_mem_space hL.1⟩ : ↥K.space) ∈
      homologyBoundary ↥K.space (n - 1) :=
  carrierPoint_boundaryRidge_mem_homologyBoundary hball hn hL (isCarrierPoint_centroid hL.1)

end IsSimplicialBall

end AffineTverberg
