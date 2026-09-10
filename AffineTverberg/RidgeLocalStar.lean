import AffineTverberg.GeometricLocalStar

set_option linter.style.header false

/-!
# The closed star of a face and the local homology upper bound

For a face `L` of a finite geometric simplicial complex `K` the *closed star*
`closedStar K L` is the union of the closed simplices of the facets through
`L`.  Near a carrier point of `L` the polyhedron `K.space` coincides with the
closed star (`exists_localRadius_closedStar`), and the closed star is star
convex about that point (`starConvex_closedStar`).

Combining this with Mayer-Vietoris injectivity against the punctured ball
gives the **local homology upper bound**: for a simplicial ball of dimension
`n ≥ 2` the punctured local star at any point has homology of rank at most one
in degree `n - 1`, and that homology is finite dimensional.  This is the upper
half of the local computation at a ridge; the matching lower bound
`(number of facets through the ridge) - 1` is the combinatorial content of
`AffineTverberg.Simplicial.card_sub_one_le_finrank_realSingularHomology_boundaryJoinPoints`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set

namespace AffineTverberg

variable {e n : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-! ### The closed star of a face -/

/-- The closed star of a face: the union of the closed simplices of the facets
containing it. -/
def closedStar (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (L : Finset (CoordinateSpace e)) : Set (CoordinateSpace e) :=
  ⋃ F ∈ facetsThrough K L, convexHull ℝ (F : Set (CoordinateSpace e))

theorem mem_closedStar_iff {L : Finset (CoordinateSpace e)} {x : CoordinateSpace e} :
    x ∈ closedStar K L ↔
      ∃ F ∈ facetsThrough K L, x ∈ convexHull ℝ (F : Set (CoordinateSpace e)) := by
  simp [closedStar]

theorem convexHull_subset_closedStar {L F : Finset (CoordinateSpace e)}
    (hF : F ∈ facetsThrough K L) :
    convexHull ℝ (F : Set (CoordinateSpace e)) ⊆ closedStar K L :=
  fun _ hx => mem_closedStar_iff.mpr ⟨F, hF, hx⟩

theorem closedStar_subset_space (L : Finset (CoordinateSpace e)) :
    closedStar K L ⊆ K.space := by
  intro x hx
  obtain ⟨F, hF, hxF⟩ := mem_closedStar_iff.mp hx
  exact Geometry.SimplicialComplex.convexHull_subset_space
    (Geometry.SimplicialComplex.facets_subset hF.1) hxF

/-- A carrier point of `L` lies in the closed star of `L`. -/
theorem mem_closedStar_of_isCarrierPoint (hfin : K.faces.Finite)
    {L : Finset (CoordinateSpace e)} (hL : L ∈ K.faces) {p : CoordinateSpace e}
    (hp : IsCarrierPoint K L p) : p ∈ closedStar K L := by
  obtain ⟨F, hF, hLF⟩ := exists_facet_superset hfin hL
  exact mem_closedStar_iff.mpr ⟨F, ⟨hF, hLF⟩,
    convexHull_mono (by exact_mod_cast hLF) hp.1⟩

/-- The closed star of `L` is star convex about any point of the closed simplex
of `L`: every facet through `L` is a convex set containing that point. -/
theorem starConvex_closedStar
    {L : Finset (CoordinateSpace e)} {p : CoordinateSpace e}
    (hpL : p ∈ convexHull ℝ (L : Set (CoordinateSpace e))) :
    StarConvex ℝ p (closedStar K L) := by
  intro y hy a b ha hb hab
  obtain ⟨F, hF, hyF⟩ := mem_closedStar_iff.mp hy
  have hpF : p ∈ convexHull ℝ (F : Set (CoordinateSpace e)) :=
    convexHull_mono (by exact_mod_cast hF.2) hpL
  exact convexHull_subset_closedStar hF
    ((convex_convexHull ℝ _) hpF hyF ha hb hab)

/-- Near a carrier point of `L` the polyhedron is contained in the closed star
of `L`. -/
theorem exists_localRadius_closedStar (hfin : K.faces.Finite)
    {L : Finset (CoordinateSpace e)} {p : CoordinateSpace e}
    (hp : IsCarrierPoint K L p) :
    ∃ ε > 0, ∀ x ∈ K.space, ‖x - p‖ < ε → x ∈ closedStar K L := by
  obtain ⟨ε, hε, h⟩ := exists_localRadius hfin p
  refine ⟨ε, hε, fun x hx hxd => ?_⟩
  obtain ⟨s, hs, hps, hxs⟩ := h x hx hxd
  have hLs := hp.2 s hs hps
  obtain ⟨F, hF, hsF⟩ := exists_facet_superset hfin hs
  exact mem_closedStar_iff.mpr ⟨F, ⟨hF, hLs.trans hsF⟩,
    convexHull_mono (by exact_mod_cast hsF) hxs⟩

/-- Consequently the polyhedron and the closed star agree on a small ball. -/
theorem space_inter_ball_eq_closedStar_inter_ball (hfin : K.faces.Finite)
    {L : Finset (CoordinateSpace e)} {p : CoordinateSpace e}
    (hp : IsCarrierPoint K L p) :
    ∃ ε > 0, K.space ∩ ball p ε = closedStar K L ∩ ball p ε := by
  obtain ⟨ε, hε, hloc⟩ := exists_localRadius_closedStar hfin hp
  refine ⟨ε, hε, Set.Subset.antisymm ?_ ?_⟩
  · rintro x ⟨hx, hxb⟩
    exact ⟨hloc x hx (by simpa [Metric.mem_ball, dist_eq_norm] using hxb), hxb⟩
  · rintro x ⟨hx, hxb⟩
    exact ⟨closedStar_subset_space L hx, hxb⟩

/-- Star convexity of the local star, in the form used by Mayer-Vietoris. -/
theorem starConvex_space_inter_ball (hfin : K.faces.Finite)
    {L : Finset (CoordinateSpace e)} {p : CoordinateSpace e}
    (hp : IsCarrierPoint K L p) :
    ∃ ε > 0, StarConvex ℝ p (K.space ∩ ball p ε) := by
  obtain ⟨ε, hε, heq⟩ := space_inter_ball_eq_closedStar_inter_ball hfin hp
  refine ⟨ε, hε, ?_⟩
  rw [heq]
  exact (starConvex_closedStar hp.1).inter
    ((convex_ball p ε).starConvex (mem_ball_self hε))

/-! ### The local homology upper bound -/

namespace IsSimplicialBall

/-- **The local homology of a simplicial ball has rank at most one.**  If `B`
is an open contractible neighbourhood of a point `P` of the polyhedron of an
`n`-dimensional simplicial ball, then `B` punctured at `P` has finite
dimensional homology of rank at most one in degree `n - 1`.

Mayer-Vietoris against the cover by the complement of `P` and `B` embeds this
homology in that of the punctured polyhedron, which is the punctured ball. -/
theorem finrank_homology_punctured_open_le_one
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {P : ↥K.space} {B : Set ↥K.space} (hBopen : IsOpen B) (hPB : P ∈ B)
    (hBcontr : ContractibleSpace ↥B) :
    FiniteDimensional ℝ ((realSingularHomology (n - 1)).obj (TopCat.of
        ↥({q : ↥K.space | q ≠ P} ∩ B))) ∧
      Module.finrank ℝ ((realSingularHomology (n - 1)).obj (TopCat.of
        ↥({q : ↥K.space | q ≠ P} ∩ B))) ≤ 1 := by
  classical
  have hAopen : IsOpen {q : ↥K.space | q ≠ P} := isOpen_compl_singleton
  have hcov : ∀ q : ↥K.space, q ∈ {q : ↥K.space | q ≠ P} ∨ q ∈ B := by
    intro q
    by_cases h : q = P
    · exact Or.inr (h ▸ hPB)
    · exact Or.inl h
  have hBzero : IsZero ((realSingularHomology (n - 1)).obj (TopCat.of ↥B)) := by
    have : Subsingleton ((realSingularHomology (n - 1)).obj (TopCat.of ↥B)) :=
      realSingularHomology_subsingleton_of_contractible ↥B (n - 1) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  have hcontrX : ContractibleSpace ↥K.space := hball.contractibleSpace_space
  have hXzero : IsZero ((realSingularHomology ((n - 1) + 1)).obj (TopCat.of ↥K.space)) := by
    have : Subsingleton ((realSingularHomology ((n - 1) + 1)).obj (TopCat.of ↥K.space)) :=
      realSingularHomology_subsingleton_of_contractible ↥K.space ((n - 1) + 1) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  have hinj := AffChain.injective_homology_inter_left (X := TopCat.of ↥K.space)
    {q : ↥K.space | q ≠ P} B hAopen hBopen hcov (n - 1) hXzero hBzero
  have hfinA : FiniteDimensional ℝ ((realSingularHomology (n - 1)).obj (TopCat.of
      ↥{q : ↥K.space | q ≠ P})) :=
    hball.finiteDimensional_punctured hn P
  have hrankA : Module.finrank ℝ ((realSingularHomology (n - 1)).obj (TopCat.of
      ↥{q : ↥K.space | q ≠ P})) ≤ 1 :=
    hball.finrank_punctured_le_one hn P
  exact ⟨Module.Finite.of_injective _ hinj,
    le_trans (LinearMap.finrank_le_finrank_of_injective hinj) hrankA⟩

/-- At a homology boundary point every open punctured neighbourhood is acyclic
in degree `n - 1`. -/
theorem subsingleton_homology_punctured_open_of_mem_homologyBoundary
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {P : ↥K.space} {B : Set ↥K.space} (hBopen : IsOpen B) (hPB : P ∈ B)
    (hBcontr : ContractibleSpace ↥B)
    (hmem : P ∈ homologyBoundary ↥K.space (n - 1)) :
    Subsingleton ((realSingularHomology (n - 1)).obj (TopCat.of
      ↥({q : ↥K.space | q ≠ P} ∩ B))) := by
  classical
  have hAopen : IsOpen {q : ↥K.space | q ≠ P} := isOpen_compl_singleton
  have hcov : ∀ q : ↥K.space, q ∈ {q : ↥K.space | q ≠ P} ∨ q ∈ B := by
    intro q
    by_cases h : q = P
    · exact Or.inr (h ▸ hPB)
    · exact Or.inl h
  have hBzero : IsZero ((realSingularHomology (n - 1)).obj (TopCat.of ↥B)) := by
    have : Subsingleton ((realSingularHomology (n - 1)).obj (TopCat.of ↥B)) :=
      realSingularHomology_subsingleton_of_contractible ↥B (n - 1) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  have hcontrX : ContractibleSpace ↥K.space := hball.contractibleSpace_space
  have hXzero : IsZero ((realSingularHomology ((n - 1) + 1)).obj (TopCat.of ↥K.space)) := by
    have : Subsingleton ((realSingularHomology ((n - 1) + 1)).obj (TopCat.of ↥K.space)) :=
      realSingularHomology_subsingleton_of_contractible ↥K.space ((n - 1) + 1) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  have hinj := AffChain.injective_homology_inter_left (X := TopCat.of ↥K.space)
    {q : ↥K.space | q ≠ P} B hAopen hBopen hcov (n - 1) hXzero hBzero
  have hsubA : Subsingleton ((realSingularHomology (n - 1)).obj (TopCat.of
      ↥{q : ↥K.space | q ≠ P})) := hmem
  exact ⟨fun x y => hinj (Subsingleton.elim _ _)⟩

/-- **The local homology of a simplicial ball has rank at most one.**  If the
polyhedron of an `n`-dimensional simplicial ball is star convex about `p` on a
ball of radius `ε`, then the punctured `ε`-neighbourhood of `p` has finite
dimensional homology of rank at most one in degree `n - 1`.

Mayer-Vietoris against the cover by the complement of `p` and the
`ε`-neighbourhood embeds this homology in that of the punctured polyhedron,
which is the punctured ball. -/
theorem finrank_homology_punctured_nbhd_le_one
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {p : CoordinateSpace e} (hpspace : p ∈ K.space)
    {ε : ℝ} (hε : 0 < ε) (hstar : StarConvex ℝ p (K.space ∩ ball p ε)) :
    FiniteDimensional ℝ ((realSingularHomology (n - 1)).obj (TopCat.of
        ↥({q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)} ∩
          {q : ↥K.space | ‖(q : CoordinateSpace e) - p‖ < ε}))) ∧
      Module.finrank ℝ ((realSingularHomology (n - 1)).obj (TopCat.of
        ↥({q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)} ∩
          {q : ↥K.space | ‖(q : CoordinateSpace e) - p‖ < ε}))) ≤ 1 := by
  classical
  have hAopen : IsOpen {q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)} :=
    isOpen_compl_singleton
  have hBopen : IsOpen {q : ↥K.space | ‖(q : CoordinateSpace e) - p‖ < ε} := by
    have hcont : Continuous fun q : ↥K.space => ‖(q : CoordinateSpace e) - p‖ :=
      continuous_norm.comp (continuous_subtype_val.sub continuous_const)
    exact isOpen_lt hcont continuous_const
  have hcov : ∀ q : ↥K.space, q ∈ {q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)} ∨
      q ∈ {q : ↥K.space | ‖(q : CoordinateSpace e) - p‖ < ε} := by
    intro q
    by_cases h : q = (⟨p, hpspace⟩ : ↥K.space)
    · refine Or.inr ?_
      change ‖(q : CoordinateSpace e) - p‖ < ε
      rw [h]
      simpa using hε
    · exact Or.inl h
  -- the neighbourhood is contractible
  have hBset : {q : ↥K.space | ‖(q : CoordinateSpace e) - p‖ < ε} =
      Subtype.val ⁻¹' (K.space ∩ ball p ε) := by
    ext q
    constructor
    · intro hq
      have hq' : ‖(q : CoordinateSpace e) - p‖ < ε := hq
      exact ⟨q.property, by simpa [Metric.mem_ball, dist_eq_norm] using hq'⟩
    · rintro ⟨-, hq⟩
      have : ‖(q : CoordinateSpace e) - p‖ < ε := by
        simpa [Metric.mem_ball, dist_eq_norm] using hq
      exact this
  have hBhomeo : ↥{q : ↥K.space | ‖(q : CoordinateSpace e) - p‖ < ε} ≃ₜ
      ↥(K.space ∩ ball p ε) :=
    (Homeomorph.setCongr hBset).trans (subsetSubtypeHomeomorph Set.inter_subset_left)
  have hBzero : IsZero ((realSingularHomology (n - 1)).obj (TopCat.of
      ↥{q : ↥K.space | ‖(q : CoordinateSpace e) - p‖ < ε})) := by
    have hc0 : ContractibleSpace ↥(K.space ∩ ball p ε) :=
      hstar.contractibleSpace ⟨p, hpspace, by simpa using hε⟩
    have hc : ContractibleSpace ↥{q : ↥K.space | ‖(q : CoordinateSpace e) - p‖ < ε} :=
      hBhomeo.toHomotopyEquiv.contractibleSpace
    have : Subsingleton ((realSingularHomology (n - 1)).obj (TopCat.of
        ↥{q : ↥K.space | ‖(q : CoordinateSpace e) - p‖ < ε})) :=
      realSingularHomology_subsingleton_of_contractible _ (n - 1) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  -- the polyhedron is contractible, hence acyclic one degree up
  have hcontrX : ContractibleSpace ↥K.space := hball.contractibleSpace_space
  have hXzero : IsZero ((realSingularHomology ((n - 1) + 1)).obj (TopCat.of ↥K.space)) := by
    have : Subsingleton ((realSingularHomology ((n - 1) + 1)).obj (TopCat.of ↥K.space)) :=
      realSingularHomology_subsingleton_of_contractible ↥K.space ((n - 1) + 1) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  have hinj := AffChain.injective_homology_inter_left (X := TopCat.of ↥K.space)
    {q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)}
    {q : ↥K.space | ‖(q : CoordinateSpace e) - p‖ < ε}
    hAopen hBopen hcov (n - 1) hXzero hBzero
  have hfinA : FiniteDimensional ℝ ((realSingularHomology (n - 1)).obj (TopCat.of
      ↥{q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)})) :=
    hball.finiteDimensional_punctured hn ⟨p, hpspace⟩
  have hrankA : Module.finrank ℝ ((realSingularHomology (n - 1)).obj (TopCat.of
      ↥{q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)})) ≤ 1 :=
    hball.finrank_punctured_le_one hn ⟨p, hpspace⟩
  exact ⟨Module.Finite.of_injective _ hinj,
    le_trans (LinearMap.finrank_le_finrank_of_injective hinj) hrankA⟩

/-- The same bound at a carrier point of a face, with the star neighbourhood
supplied by the closed star. -/
theorem exists_finrank_homology_punctured_nbhd_le_one
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n)
    {L : Finset (CoordinateSpace e)} (hL : L ∈ K.faces) {p : CoordinateSpace e}
    (hp : IsCarrierPoint K L p) :
    ∃ ε > 0, (K.space ∩ ball p ε = closedStar K L ∩ ball p ε) ∧
      FiniteDimensional ℝ ((realSingularHomology (n - 1)).obj (TopCat.of
        ↥({q : ↥K.space | q ≠ (⟨p, hp.mem_space hL⟩ : ↥K.space)} ∩
          {q : ↥K.space | ‖(q : CoordinateSpace e) - p‖ < ε}))) ∧
      Module.finrank ℝ ((realSingularHomology (n - 1)).obj (TopCat.of
        ↥({q : ↥K.space | q ≠ (⟨p, hp.mem_space hL⟩ : ↥K.space)} ∩
          {q : ↥K.space | ‖(q : CoordinateSpace e) - p‖ < ε}))) ≤ 1 := by
  obtain ⟨ε, hε, heq⟩ := space_inter_ball_eq_closedStar_inter_ball hball.finite_faces hp
  have hstar : StarConvex ℝ p (K.space ∩ ball p ε) := by
    rw [heq]
    exact (starConvex_closedStar hp.1).inter
      ((convex_ball p ε).starConvex (mem_ball_self hε))
  obtain ⟨hfd, hle⟩ :=
    hball.finrank_homology_punctured_nbhd_le_one hn (hp.mem_space hL) hε hstar
  exact ⟨ε, hε, heq, hfd, hle⟩

end IsSimplicialBall

end AffineTverberg
