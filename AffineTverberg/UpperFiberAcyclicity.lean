import AffineTverberg.RyFaceLattice
import AffineTverberg.SimplicialSingularBridge

set_option linter.style.header false

/-!
# Acyclicity of the actual top-incidence fibers

This file assembles the polytopal upper-fiber theorem.  For a nondegenerate
polytopal join map `Φ` and a nonzero dual functional `y`:

* the upper facets of the lifted polytope `R_y` are exactly the facets visible
  from a point high above a base point (`UpperFacetVisibility.lean`), so the
  recursive line shelling of `CanonicalVisibleShelling.lean` shells them inside
  the canonical face lattice of `R_y`;
* every cell of that certificate is a genuine face of `R_y` lying on an upper
  facet, so the face `qFace` of the Cayley join above it is an actual face
  (`RyUpperFaces.lean`) whose projected dimension is the dimension of the cell
  minus one — this is the degree shift `CellShelling.dimShift`;
* the good subcomplexes of these faces therefore glue acyclically
  (`ShellableGluing.lean`), and their geometric carrier is exactly the actual
  fiber `deletedJoinTopLocus y`;
* the general simplicial-to-singular bridge turns this into actual singular
  acyclicity of the actual fiber, and hence of the fiber of the actual
  projection `topIncidenceProjection`.
-/

noncomputable section

open Set CategoryTheory CategoryTheory.Limits

namespace AffineTverberg
namespace BadVertex

open CayleyJoin PolytopeFace BadEdge UpperFacet _root_.AffineTverberg.Simplicial
open CompactConvexProjection

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Φ : PolytopalJoinMap P m V) (y : StrongDual ℝ V)

/-- The cells of the shelling: the canonical faces of `R_y` visible from `q`. -/
def ryShellCells (q : CoordinateSpace n × ℝ) : Finset (CanonFace (ryVerts Φ y)) :=
  canonCells (ryVerts Φ y) (visibleCells (ryVerts Φ y) q)

/-- The good subcomplex assigned to a canonical face of `R_y`: the good
subcomplex of the bad-vertex triangulation of the face of `Q` above it. -/
def ryAssign (c : CanonFace (ryVerts Φ y)) :
    Finset (Finset (Finset (JoinVertex P m))) :=
  inducedFaces (sdQ P m (qFace Φ y c.1)) (goodJoinVertices P m)

/-- The dimension function of the shelling: the projected dimension of the
face of `Q` above the cell. -/
def ryDim (c : CanonFace (ryVerts Φ y)) : ℕ := projDim P m (qFace Φ y c.1)

/-- The glued good complex over the visible cells. -/
def ryUnion (q : CoordinateSpace n × ℝ) :
    Finset (Finset (Finset (JoinVertex P m))) :=
  (ryShellCells Φ y q).biUnion (ryAssign Φ y)

variable {Φ y}

theorem mem_ryUnion {q : CoordinateSpace n × ℝ}
    {σ : Finset (Finset (JoinVertex P m))} :
    σ ∈ ryUnion Φ y q ↔ ∃ c ∈ ryShellCells Φ y q, σ ∈ ryAssign Φ y c := by
  rw [ryUnion, Finset.mem_biUnion]

/-! ### The four hypotheses of the acyclic gluing theorem -/

theorem ryAssign_bot : ryAssign Φ y ⊥ = {∅} := by
  rw [ryAssign, CanonFace.coe_bot, qFace_empty, sdQ_empty, inducedFaces]
  simp

theorem ryAssign_inf (c d : CanonFace (ryVerts Φ y))
    (σ : Finset (Finset (JoinVertex P m))) :
    σ ∈ ryAssign Φ y (c ⊓ d) ↔ σ ∈ ryAssign Φ y c ∧ σ ∈ ryAssign Φ y d := by
  have hc : qFace Φ y c.1 ∈ faceFamily P m := qFace_mem_faceFamily c.2
  have hd : qFace Φ y d.1 ∈ faceFamily P m := qFace_mem_faceFamily d.2
  simp only [ryAssign, CanonFace.coe_inf, qFace_inter, mem_inducedFaces,
    sdQ_inter hc hd, Finset.mem_inter]
  tauto

theorem faceClosed_ryAssign (c : CanonFace (ryVerts Φ y)) :
    FaceClosed (ryAssign Φ y c) :=
  faceClosed_inducedFaces (faceClosed_sdQ _) _

theorem ryAssign_subset_sdQ_topFace (c : CanonFace (ryVerts Φ y)) :
    ryAssign Φ y c ⊆ sdQ P m (topFace P m) := by
  intro σ hσ
  exact sdQ_mono P m (qFace_mem_faceFamily c.2) (Finset.subset_univ _)
    (mem_inducedFaces.mp hσ).1

theorem ryUnion_subset_sdQ_topFace (q : CoordinateSpace n × ℝ) :
    ryUnion Φ y q ⊆ sdQ P m (topFace P m) := by
  intro σ hσ
  obtain ⟨c, -, hσc⟩ := mem_ryUnion.mp hσ
  exact ryAssign_subset_sdQ_topFace c hσc

theorem faceClosed_ryUnion (q : CoordinateSpace n × ℝ) :
    FaceClosed (ryUnion Φ y q) := by
  intro σ hσ τ hτ
  obtain ⟨c, hc, hσc⟩ := mem_ryUnion.mp hσ
  exact mem_ryUnion.mpr ⟨c, hc, faceClosed_ryAssign c σ hσc τ hτ⟩

section Order

variable [LinearOrder (Finset (JoinVertex P m))]

theorem local_acyclicity_ryAssign (c : CanonFace (ryVerts Φ y)) (hc : c ≠ ⊥) :
    IsReducedAcyclicUpTo ℝ (ryAssign Φ y c) (ryDim Φ y c) := by
  have hne : (qFace Φ y c.1).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    exact hc (Subtype.ext ((qFace_eq_empty_iff c.2.subset).mp h))
  exact local_simplicial_acyclicity_sdQ (qFace_mem_faceFamily c.2) hne

/-- **The glued good complex over the visible upper cells is reduced acyclic up
to degree `n`.** -/
theorem isReducedAcyclicUpTo_ryUnion (hy : y ≠ 0)
    (hfspan : FactorImagesAffinelySpan Φ.factor) {q : CoordinateSpace n × ℝ}
    (hqout : q ∉ convexHull ℝ ((ryVerts Φ y : Finset (CoordinateSpace n × ℝ)) :
      Set (CoordinateSpace n × ℝ)))
    (hqvis : ∀ j : FacetIdx (ryVerts Φ y),
      facetRhs j < facetForm j q → IsUpperFacet j) :
    IsReducedAcyclicUpTo ℝ (ryUnion Φ y q) n := by
  classical
  set s := ryVerts Φ y with hs_def
  have hs : s.Nonempty := ryVerts_nonempty Φ y
  have hspan : affineSpan ℝ (s : Set (CoordinateSpace n × ℝ)) = ⊤ :=
    affineSpan_ryVerts Φ y hy hfspan
  have hq : q ∈ affineSpan ℝ (s : Set (CoordinateSpace n × ℝ)) := by
    rw [hspan]; trivial
  have hrank : arank (convexHull ℝ (s : Set (CoordinateSpace n × ℝ))) = n + 2 :=
    arank_ryVerts Φ y hy hfspan
  -- the geometric shelling in the canonical face lattice
  have hshellRank : CellShelling (canonDim s)
      (arank (convexHull ℝ (s : Set (CoordinateSpace n × ℝ))) - 1)
      (ryShellCells Φ y q) :=
    cellShelling_visibleCells_canon_of_notMem hs hq hqout
  -- the dimension shift, valid on every cell below a visible facet
  have hdim : ∀ e ∈ cellSupport (ryShellCells Φ y q),
      ryDim Φ y e + 1 = canonDim s e := by
    rintro e ⟨hene, c, hc, hec⟩
    obtain ⟨j, hjvis, hjc⟩ := mem_visibleCells.mp (mem_canonCells.mp hc)
    have hupper : IsUpperFacet j := hqvis j hjvis
    have hsub : e.1 ⊆ s := e.2.subset
    have hne : e.1.Nonempty := CanonFace.ne_bot_iff.mp hene
    have htight : ∀ v ∈ e.1, facetForm j v = facetRhs j := by
      intro v hv
      have hvj : v ∈ j.1.1 := by
        rw [hjc]
        exact hec hv
      rw [facetIdx_index_eq_contactGens j] at hvj
      exact (mem_contactGens.mp hvj).2
    have := projDim_qFace_of_upper hsub hne (ne_of_gt hupper) htight
    rw [ryDim, canonDim, hullDim]
    exact this
  have hshell : CellShelling (ryDim Φ y) n (ryShellCells Φ y q) := by
    have := hshellRank.dimShift hdim
    rw [hrank] at this
    simpa using this
  exact isReducedAcyclicUpTo_union_of_cellShelling (ryDim Φ y) (ryAssign Φ y)
    ryAssign_bot ryAssign_inf faceClosed_ryAssign local_acyclicity_ryAssign
    hshell _ fun _ ↦ mem_ryUnion

end Order

/-! ### The geometric carrier of the glued complex is the actual fiber -/

theorem geometricCarrier_ryUnion (q : CoordinateSpace n × ℝ) :
    geometricCarrier (ryUnion Φ y q) (sdPoint P m) =
      ⋃ c ∈ ryShellCells Φ y q, goodRealization P m (qFace Φ y c.1) := by
  ext x
  simp only [geometricCarrier, goodRealization, simplexCarrier, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨σ, hσ, hx⟩
    obtain ⟨c, hc, hσc⟩ := mem_ryUnion.mp hσ
    refine ⟨c, hc, σ, ?_, hx⟩
    rwa [ryAssign, inducedFaces_eq_goodSimplices] at hσc
  · rintro ⟨c, hc, σ, hσ, hx⟩
    refine ⟨σ, mem_ryUnion.mpr ⟨c, hc, ?_⟩, hx⟩
    rwa [ryAssign, inducedFaces_eq_goodSimplices]

/-! ### Elementary monotonicity of the good realization -/

theorem goodRealization_mono {S T : Finset (JoinVertex P m)} (hS : S ∈ faceFamily P m)
    (hST : S ⊆ T) : goodRealization P m S ⊆ goodRealization P m T := by
  intro z hz
  obtain ⟨σ, hσ, hzσ⟩ := Set.mem_iUnion₂.mp hz
  obtain ⟨hσQ, hgood⟩ := Finset.mem_filter.mp hσ
  exact Set.mem_iUnion₂.mpr
    ⟨σ, Finset.mem_filter.mpr ⟨sdQ_mono P m hS hST hσQ, hgood⟩, hzσ⟩

theorem goodRealization_subset_sdCarrier {S : Finset (JoinVertex P m)}
    (hS : S ∈ faceFamily P m) : goodRealization P m S ⊆ sdCarrier P m S := by
  rw [goodRealization_eq_deletedFaces hS]
  exact Set.iUnion₂_subset fun _ hT ↦ sdCarrier_mono P m hT.2.1

/-- **The carrier of the face above an upper facet lies in the top locus.** -/
theorem sdCarrier_qFace_subset_topLocus {j : FacetIdx (ryVerts Φ y)}
    (hj : IsUpperFacet j) :
    sdCarrier P m (qFace Φ y j.1.1) ⊆ (Φ.upperEnvelopeData y).topLocus := by
  intro z hz
  have hsub : (j.1.1 : Finset (CoordinateSpace n × ℝ)) ⊆ ryVerts Φ y :=
    Finset.mem_powerset.mp j.1.2
  have hzQ : z ∈ (Φ.upperEnvelopeData y).carrier := by
    rw [Φ.upperEnvelopeData_carrier, ← sdCarrier_topFace P m]
    exact sdCarrier_mono P m (Finset.subset_univ _) hz
  have hp : (Φ.upperEnvelopeData y).liftedMap z ∈ facetFace j := by
    have hmem : (Φ.upperEnvelopeData y).liftedMap z ∈
        (Φ.upperEnvelopeData y).liftedMap '' sdCarrier P m (qFace Φ y j.1.1) := ⟨z, hz, rfl⟩
    rwa [liftedMap_image_sdCarrier_qFace hsub] at hmem
  rw [CompactConvexProjection.mem_topLocus_iff]
  refine ⟨hzQ, fun v hv hproj ↦ ?_⟩
  have hqmem : (Φ.upperEnvelopeData y).liftedMap v ∈
      convexHull ℝ ((ryVerts Φ y : Finset (CoordinateSpace n × ℝ)) :
        Set (CoordinateSpace n × ℝ)) := by
    rw [convexHull_ryVerts]
    exact ⟨v, hv, rfl⟩
  exact le_of_mem_facetFace_of_isUpperFacet hj hp hqmem hproj

/-- **The union of the good realizations over the visible upper cells is the
actual fiber `Y_y`.** -/
theorem iUnion_goodRealization_qFace (hy : y ≠ 0)
    (hfspan : FactorImagesAffinelySpan Φ.factor) {q : CoordinateSpace n × ℝ}
    (hqvis : ∀ j : FacetIdx (ryVerts Φ y),
      (facetRhs j < facetForm j q ↔ IsUpperFacet j)) :
    ⋃ c ∈ ryShellCells Φ y q, goodRealization P m (qFace Φ y c.1) =
      Φ.deletedJoinTopLocus y := by
  classical
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun c hc ↦ ?_
    obtain ⟨j, hjvis, hjc⟩ := mem_visibleCells.mp (mem_canonCells.mp hc)
    have hupper : IsUpperFacet j := (hqvis j).1 hjvis
    intro z hz
    refine ⟨?_, ?_⟩
    · have hzD : z ∈ goodRealization P m (topFace P m) :=
        goodRealization_mono (qFace_mem_faceFamily c.2) (Finset.subset_univ _) hz
      rwa [goodRealization_topFace] at hzD
    · have hzc : z ∈ sdCarrier P m (qFace Φ y c.1) :=
        goodRealization_subset_sdCarrier (qFace_mem_faceFamily c.2) hz
      rw [← hjc] at hzc
      exact sdCarrier_qFace_subset_topLocus hupper hzc
  · rintro z ⟨hzD, hztop⟩
    have hzQ : z ∈ (Φ.upperEnvelopeData y).carrier := hztop.1
    set p := (Φ.upperEnvelopeData y).liftedMap z with hpdef
    have hpmem : p ∈ convexHull ℝ ((ryVerts Φ y : Finset (CoordinateSpace n × ℝ)) :
        Set (CoordinateSpace n × ℝ)) := by
      rw [convexHull_ryVerts]
      exact ⟨z, hzQ, rfl⟩
    have hptop : ∀ w ∈ convexHull ℝ ((ryVerts Φ y : Finset (CoordinateSpace n × ℝ)) :
        Set (CoordinateSpace n × ℝ)), w.1 = p.1 → w.2 ≤ p.2 := by
      intro w hw hw1
      rw [convexHull_ryVerts] at hw
      obtain ⟨v, hv, rfl⟩ := hw
      exact ((CompactConvexProjection.mem_topLocus_iff _).1 hztop).2 v hv hw1
    obtain ⟨j, hjupper, hjface⟩ :=
      exists_upperFacet_of_top (ryVerts_nonempty Φ y)
        (affineSpan_ryVerts Φ y hy hfspan) hpmem hptop
    have hcanon : IsExposedGens (ryVerts Φ y) j.1.1 := isExposedGens_facetIdx j
    have hqf : qFace Φ y j.1.1 ∈ faceFamily P m := qFace_mem_faceFamily hcanon
    have hzq : z ∈ sdCarrier P m (qFace Φ y j.1.1) := by
      rw [sdCarrier_qFace_eq
        (g := facetForm j) (c := facetRhs j)
        (fun v hv ↦ facetForm_le_facetRhs j (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)))
        (fun v ↦ by rw [facetIdx_index_eq_contactGens j, mem_contactGens])
        (facetIdx_nonempty j)]
      refine ⟨?_, ((mem_facetFace_iff j).1 hjface).2⟩
      rwa [Φ.upperEnvelopeData_carrier] at hzQ
    rw [← goodRealization_topFace,
      goodRealization_eq_deletedFaces (topFace_mem_faceFamily P m)] at hzD
    obtain ⟨T, ⟨hTfam, -, hTdel⟩, hzT⟩ := Set.mem_iUnion₂.mp hzD
    obtain ⟨hinterfam, hintercar⟩ := sdCarrier_inter hTfam hqf
    refine Set.mem_iUnion₂.mpr
      ⟨CanonFace.mk' j.1.1 hcanon,
        mem_canonCells.mpr (mem_visibleCells.mpr ⟨j, (hqvis j).2 hjupper, rfl⟩), ?_⟩
    simp only [CanonFace.coe_mk']
    rw [goodRealization_eq_deletedFaces hqf]
    refine Set.mem_iUnion₂.mpr ⟨T ∩ qFace Φ y j.1.1,
      ⟨hinterfam, Finset.inter_subset_right, hTdel.mono Finset.inter_subset_left⟩, ?_⟩
    rw [hintercar]
    exact ⟨hzT, hzq⟩

/-! ### The actual singular acyclicity of the actual fiber -/

/-- **Actual singular acyclicity of the actual top-incidence fiber.**  For a
nondegenerate polytopal join map and any nonzero dual functional the fiber
`Y_y = D ∩ topLocus(λ_y)` is nonempty, has invertible degree-zero singular
augmentation as soon as `1 ≤ n`, and vanishing singular homology in every
degree `k ≠ 0` with `k + 1 ≤ n`. -/
theorem singular_acyclicity_deletedJoinTopLocus (hy : y ≠ 0)
    (hfspan : FactorImagesAffinelySpan Φ.factor) :
    (Φ.deletedJoinTopLocus y).Nonempty ∧
      (1 ≤ n → IsIso (realSingularAugmentation
        (TopCat.of ↥(Φ.deletedJoinTopLocus y)))) ∧
      ∀ k, k ≠ 0 → k + 1 ≤ n →
        IsZero ((realSingularHomology k).obj
          (TopCat.of ↥(Φ.deletedJoinTopLocus y))) := by
  classical
  let : LinearOrder (Finset (JoinVertex P m)) := joinVertexSetOrder P m
  -- a point of the lifted polytope, and a point high above it
  obtain ⟨v₀, hv₀⟩ := P.actualVertices_nonempty
  obtain ⟨k₀, -⟩ := exists_vtx P hv₀
  set w₀ : JoinVertex P m := ((0, k₀) : JoinVertex P m) with hw₀
  have hmem₀ : ((liftedVertex Φ y w₀).1, (liftedVertex Φ y w₀).2) ∈
      convexHull ℝ ((ryVerts Φ y : Finset (CoordinateSpace n × ℝ)) :
        Set (CoordinateSpace n × ℝ)) :=
    subset_convexHull ℝ _ (Finset.mem_coe.mpr ((mem_ryVerts Φ y).mpr ⟨w₀, rfl⟩))
  obtain ⟨T, hTout, hTvis⟩ := exists_visible_eq_upper hmem₀
  set q : CoordinateSpace n × ℝ := ((liftedVertex Φ y w₀).1, T) with hq
  have hacy : IsReducedAcyclicUpTo ℝ (ryUnion Φ y q) n :=
    isReducedAcyclicUpTo_ryUnion hy hfspan hTout (fun j hj ↦ (hTvis j).1 hj)
  have hcover : geometricCarrier (ryUnion Φ y q) (sdPoint P m) =
      Φ.deletedJoinTopLocus y := by
    rw [geometricCarrier_ryUnion]
    exact iUnion_goodRealization_qFace hy hfspan hTvis
  have hgeombase : IsGeometricRealization (ryUnion Φ y q) (sdPoint P m) :=
    (isGeometricRealization_sdQ (topFace P m)).mono (ryUnion_subset_sdQ_topFace q)
  -- the same statement for the decidable equality carried by the linear order
  have hgeom : @IsGeometricRealization (Finset (JoinVertex P m))
      (fun a b ↦ LinearOrder.toDecidableEq a b) _ _ _ (ryUnion Φ y q) (sdPoint P m) := by
    convert hgeombase using 1
  -- a vertex of the glued complex
  obtain ⟨x, hx⟩ : (geometricCarrier (ryUnion Φ y q) (sdPoint P m)).Nonempty := by
    rw [hcover]
    exact Φ.deletedJoinTopLocus_nonempty y
  obtain ⟨σ, hσ, hxσ⟩ := Set.mem_iUnion₂.mp hx
  have hσne : σ.Nonempty := by
    rcases Finset.eq_empty_or_nonempty σ with rfl | h
    · simp at hxσ
    · exact h
  obtain ⟨a, ha⟩ := hσne
  have hvertex : ({a} : Finset (Finset (JoinVertex P m))) ∈ ryUnion Φ y q :=
    faceClosed_ryUnion q σ hσ {a} (Finset.singleton_subset_iff.mpr ha)
  have hmain := Simplicial.singular_acyclicity_of_isReducedAcyclicUpTo
    (faceClosed_ryUnion q) hgeom hvertex hacy
  rwa [hcover] at hmain

/-- The same statement for the fiber of the actual projection
`topIncidenceProjection`. -/
theorem singular_acyclicity_topIncidenceFiber
    (hfspan : FactorImagesAffinelySpan Φ.factor) (y : DualUnitSphere V) :
    Nonempty (Φ.TopIncidenceFiber y) ∧
      (1 ≤ n → IsIso (realSingularAugmentation
        (TopCat.of (Φ.TopIncidenceFiber y)))) ∧
      ∀ k, k ≠ 0 → k + 1 ≤ n →
        IsZero ((realSingularHomology k).obj
          (TopCat.of (Φ.TopIncidenceFiber y))) := by
  have hy : (y : StrongDual ℝ V) ≠ 0 := by
    intro h
    have hnorm := y.2
    rw [h] at hnorm
    simp at hnorm
  obtain ⟨hne, hiso, hzero⟩ :=
    singular_acyclicity_deletedJoinTopLocus (Φ := Φ) (y := (y : StrongDual ℝ V)) hy hfspan
  set e := Φ.topIncidenceFiberHomeomorph y with he
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hne
    exact ⟨e.symm ⟨z, hz⟩⟩
  · intro hn
    have h0 := hiso hn
    have hmap : IsIso ((realSingularHomology 0).map
        (TopCat.ofHom (e : C(Φ.TopIncidenceFiber y, Φ.DeletedJoinTopLocusSpace y)))) :=
      (realSingularHomologyIsoOfHomotopyEquiv e.toHomotopyEquiv 0).isIso_hom
    rw [← realSingularAugmentation_naturality (TopCat.ofHom
      (e : C(Φ.TopIncidenceFiber y, Φ.DeletedJoinTopLocusSpace y)))]
    infer_instance
  · intro k hk hkn
    exact (hzero k hk hkn).of_iso
      (realSingularHomologyIsoOfHomotopyEquiv e.toHomotopyEquiv k)

/-- **Every fiber of the actual top-incidence projection is reduced singular
acyclic below degree `n`**, in the packaged form used by the descent
machinery of `SingularAcyclicFiber.lean`.  This is the fiber input for the
remaining sphere-projection step. -/
theorem singularAcyclicBelow_topIncidenceFiber (hn : 1 ≤ n)
    (hfspan : FactorImagesAffinelySpan Φ.factor) (y : DualUnitSphere V) :
    SingularAcyclicBelow (TopCat.of (Φ.TopIncidenceFiber y)) n := by
  obtain ⟨-, hiso, hzero⟩ := singular_acyclicity_topIncidenceFiber hfspan y
  exact ⟨hiso hn, fun k hk hkn ↦ hzero k hk hkn⟩

end BadVertex
end AffineTverberg
