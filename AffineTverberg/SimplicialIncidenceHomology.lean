import AffineTverberg.BarycentricFaceIncidence
import AffineTverberg.SimplicialBadTopology
import AffineTverberg.SimplicialCohomologicalObstruction

set_option linter.style.header false

/-!
# The actual simplicial first incidence projection

The deleted join of a finite geometric simplicial complex is already a finite
geometric simplicial complex on its colored vertices. Its cells are simplices,
so their inverse images under barycentric realization are exactly support
conditions. The actual fiber contractions therefore give a singular homology
equivalence for the first projection of the piecewise-affine incidence space.
-/

noncomputable section

open Set CategoryTheory HomologicalComplex
open AffineTverberg.Simplicial AffineTverberg.AffChain

namespace AffineTverberg

namespace Simplicial

variable {W E : Type*} [Fintype W] [DecidableEq W]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a genuine geometric realization, membership in one of its simplices
is exactly the barycentric support condition, even if the whole carrier is
not convex. -/
theorem barycentricEvaluation_mem_simplex_iff
    {J : Finset (Finset W)} {p : W → E} (hgeom : IsGeometricRealization J p)
    {s : Finset W} (hs : s ∈ J) {x : W → ℝ} (hx : x ∈ barycentricCarrier J) :
    barycentricEvaluation p x ∈ convexHull ℝ (p '' (s : Set W)) ↔
      ∀ w, w ∉ s → x w = 0 := by
  have hcar : geometricCarrier {s} p = convexHull ℝ (p '' (s : Set W)) := by
    ext z
    simp [geometricCarrier]
  have h := evaluation_mem_subfamily_iff hgeom
    (show ({s} : Finset (Finset W)) ⊆ J from Finset.singleton_subset_iff.mpr hs) hx
  rw [hcar] at h
  rw [h]
  constructor
  · rintro ⟨_, _, t, ht, hxt⟩
    simpa only [Finset.mem_singleton.mp ht] using hxt
  · intro hxs
    exact ⟨hx.1, hx.2.1, s, Finset.mem_singleton_self s, hxs⟩

end Simplicial

namespace BadEdge

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  {W : Type} [Fintype W] [LinearOrder W]
  (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)

/-- The finite face family of the original, unsubdivided deleted join. -/
def deletedJoinFaceFamily : Finset (Finset W) := by
  classical
  exact Finset.univ.filter fun s ↦ IsDeletedFace vert s ∧ IsJoinFace n K idx vert s

theorem mem_deletedJoinFaceFamily {s : Finset W} :
    s ∈ deletedJoinFaceFamily (n := n) (K := K) idx vert ↔
      IsDeletedFace vert s ∧ IsJoinFace n K idx vert s := by
  classical
  simp [deletedJoinFaceFamily]

theorem faceClosed_deletedJoinFaceFamily :
    FaceClosed (deletedJoinFaceFamily (n := n) (K := K) idx vert) := by
  intro s hs t hts
  obtain ⟨hd, hj⟩ := (mem_deletedJoinFaceFamily idx vert).mp hs
  exact (mem_deletedJoinFaceFamily idx vert).mpr ⟨hd.mono hts, hj.mono hts⟩

omit [Fintype W] in
/-- Deleted cells are unsubdivided simplices. Their affine independence
follows from the already verified Cayley subdivision on that same cell. -/
theorem affineIndependent_cayleyPt_of_deletedJoinFace
    [Finite W]
    (hinj : Function.Injective fun w ↦ (idx w, vert w)) {s : Finset W}
    (hd : IsDeletedFace vert s) (hj : IsJoinFace n K idx vert s) :
    AffineIndependent ℝ (fun w : s ↦ cayleyPt idx vert w.val) := by
  classical
  let : Fintype W := Fintype.ofFinite W
  have hsd : sdSimplexOf s ∈ sdFaces vert s := by
    rw [sdFaces_of_isDeletedFace vert hd]
    exact Finset.mem_image.mpr ⟨s, Finset.mem_powerset.mpr le_rfl, rfl⟩
  let emb : s ↪ ↥(sdSimplexOf s) :=
    ⟨fun w ↦ ⟨{w.val}, Finset.mem_image.mpr ⟨w.val, w.property, rfl⟩⟩,
      fun a b h ↦ Subtype.ext (Finset.singleton_inj.mp (congrArg Subtype.val h))⟩
  have h := (affineIndependent_sdPt vert
    (affIndepOn_cayleyPt_of_isJoinFace idx vert hinj hj) hsd).comp_embedding emb
  change AffineIndependent ℝ (fun w : s ↦ sdPt (cayleyPt idx vert) {w.val}) at h
  simpa only [sdPt_singleton] using h

/-- The original deleted-join family has the genuine geometric intersection
property across cells, not just within each individual simplex. -/
theorem isGeometricRealization_deletedJoinFaceFamily
    (hinj : Function.Injective fun w ↦ (idx w, vert w)) :
    IsGeometricRealization (deletedJoinFaceFamily (n := n) (K := K) idx vert)
      (cayleyPt idx vert) where
  independent s hs := by
    obtain ⟨hd, hj⟩ := (mem_deletedJoinFaceFamily idx vert).mp hs
    exact affineIndependent_cayleyPt_of_deletedJoinFace idx vert hinj hd hj
  intersection s hs t ht := by
    simp only [convexHull_cayleyPt_eq_joinCellCarrier]
    exact joinCellCarrier_joinFactor_inter_subset idx vert hinj
      ((mem_deletedJoinFaceFamily idx vert).mp hs).2
      ((mem_deletedJoinFaceFamily idx vert).mp ht).2

variable (hinj : Function.Injective fun w ↦ (idx w, vert w))
  (hcover : ∀ (i : Fin (m + 1)) (s : Finset (CoordinateSpace e)),
    IsBoundarySimplicialFace n K s → ∀ v ∈ s, ∃ w, idx w = i ∧ vert w = v)

include hinj hcover in
theorem geometricCarrier_deletedJoinFaceFamily :
    geometricCarrier (deletedJoinFaceFamily (n := n) (K := K) idx vert)
      (cayleyPt idx vert) = simplicialDeletedJoinCarrier n K m := by
  rw [← iUnion_deleted_joinFactor_eq_deletedJoin idx vert hinj hcover]
  ext z
  simp only [geometricCarrier, mem_iUnion, exists_prop, mem_deletedJoinFaceFamily,
    Set.mem_ofPred_eq, convexHull_cayleyPt_eq_joinCellCarrier]

/-- Exact barycentric realization of the actual simplicial deleted join. -/
def simplicialDeletedJoinBarycentricHomeomorph :
    barycentricCarrier (deletedJoinFaceFamily (n := n) (K := K) idx vert) ≃ₜ
      simplicialDeletedJoinCarrier n K m :=
  (geometricRealizationHomeomorph
    (isGeometricRealization_deletedJoinFaceFamily idx vert hinj)).trans
      (Homeomorph.setCongr (geometricCarrier_deletedJoinFaceFamily idx vert hinj hcover))

include hcover in
omit [LinearOrder W] in
theorem joinFactor_preimage_deletedCell (F : SimplicialDeletedCellIndex n K m) :
    joinFactor idx vert (preimageJoinFace idx vert F.val) = F.val := by
  apply funext
  apply joinFactor_preimageJoinFace idx vert
  intro i v hv
  rcases F.property.1 i with hf | hf
  · rw [hf] at hv
    exact (Finset.notMem_empty v hv).elim
  · exact hcover i (F.val i) hf v hv

include hinj hcover in
theorem preimage_deletedCell_mem (F : SimplicialDeletedCellIndex n K m) :
    preimageJoinFace idx vert F.val ∈ deletedJoinFaceFamily (n := n) (K := K) idx vert := by
  apply (mem_deletedJoinFaceFamily idx vert).mpr
  refine ⟨isDeletedFace_preimageJoinFace idx vert hinj F.property.2, ?_⟩
  intro i
  rw [joinFactor_preimage_deletedCell idx vert hcover F]
  exact F.property.1 i

/-- Every actual deleted cell corresponds to precisely its colored-vertex
support, under the same global homeomorphism. -/
theorem simplicialDeletedJoinBarycentricHomeomorph_mem_cell_iff
    (F : SimplicialDeletedCellIndex n K m)
    (x : barycentricCarrier (deletedJoinFaceFamily (n := n) (K := K) idx vert)) :
    (simplicialDeletedJoinBarycentricHomeomorph idx vert hinj hcover x).val ∈
      joinCellCarrier F.val ↔
      ∀ w, w ∉ preimageJoinFace idx vert F.val → x.val w = 0 := by
  change barycentricEvaluation (cayleyPt idx vert) x.val ∈ joinCellCarrier F.val ↔ _
  have hcar : convexHull ℝ (cayleyPt idx vert ''
      (preimageJoinFace idx vert F.val : Set W)) = joinCellCarrier F.val := by
    rw [convexHull_cayleyPt_eq_joinCellCarrier, joinFactor_preimage_deletedCell idx vert hcover F]
  rw [← hcar]
  exact barycentricEvaluation_mem_simplex_iff
    (isGeometricRealization_deletedJoinFaceFamily idx vert hinj)
    (preimage_deletedCell_mem idx vert hinj hcover F) x.property

end BadEdge

/-- **The actual simplicial first projection is a singular homology
equivalence under zero avoidance.** The finite indexing, geometric model,
cell support compatibility and fiber contractions are all discharged. -/
theorem quasiIso_simplicialCellIncidenceProjection
    {e n d m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
    (φ : K.space → CoordinateSpace d) (hfin : K.faces.Finite)
    (hφ : IsAffineOnSimplicialFaces K φ)
    (hzero : ∀ z : SimplicialDeletedJoinSpace n K m,
      simplicialGlobalSarkariaMap φ z ≠ 0) :
    QuasiIso (singChainsMap (simplicialCellIncidenceProjectionTopHom (n := n) (m := m) φ)) := by
  let a := BadEdge.boundaryJoinVertexIndexing (n := n) (m := m) hfin
  exact quasiIso_faceIncidenceProjection_of_model
    (fun F : SimplicialDeletedCellIndex n K m ↦ joinCellCarrier F.val)
    (simplicialGlobalSarkariaAmbient (n := n) φ)
    (fun F ↦ BadEdge.preimageJoinFace a.factor a.vertex F.val)
    (BadEdge.simplicialDeletedJoinBarycentricHomeomorph a.factor a.vertex a.injective a.covers)
    (BadEdge.simplicialDeletedJoinBarycentricHomeomorph_mem_cell_iff
      a.factor a.vertex a.injective a.covers)
    (BadEdge.faceClosed_deletedJoinFaceFamily a.factor a.vertex)
    (simplicialCellIncidenceFiber_contractible φ hfin hφ hzero)

theorem isIso_simplicialCellIncidenceProjection_homology
    {e n d m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
    (φ : K.space → CoordinateSpace d) (hfin : K.faces.Finite)
    (hφ : IsAffineOnSimplicialFaces K φ)
    (hzero : ∀ z : SimplicialDeletedJoinSpace n K m,
      simplicialGlobalSarkariaMap φ z ≠ 0) (k : ℕ) :
    IsIso ((realSingularHomology k).map
      (simplicialCellIncidenceProjectionTopHom (n := n) (m := m) φ)) := by
  exact (quasiIsoAt_iff_isIso_homologyMap _ _).mp
    ((quasiIso_iff _).mp (quasiIso_simplicialCellIncidenceProjection φ hfin hφ hzero) k)

end AffineTverberg
