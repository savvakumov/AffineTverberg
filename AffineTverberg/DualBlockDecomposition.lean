import AffineTverberg.DualBlocks

set_option linter.style.header false

/-!
# The dual block decomposition of a polyhedron

The dual blocks of the faces of a finite geometric complex `K` cover its
polyhedron, meet in the dual block of the union of the two faces, and the
boundary of a block is the union of the blocks of the faces strictly containing
it.  Every block is contractible (it is a geometric cone with apex the
barycenter of its face).

These are the geometric statements underlying the dual cell decomposition used
in Poincaré–Alexander duality.  All of them are proved from the actual
barycentric subdivision of `BarycentricSubdivisionGeometry`; no PL structure,
manifold hypothesis or shellability is assumed.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {V : Type*} [Fintype V] [DecidableEq V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E}

/-- The polyhedron of the dual block of a face. -/
def dualBlockSpace (K : Finset (Finset V)) (p : V → E) (s : Finset V) : Set E :=
  geometricCarrier (dualBlockFaces K s) (faceBarycenter p)

/-- The polyhedron of the boundary of the dual block of a face. -/
def dualBlockBoundarySpace (K : Finset (Finset V)) (p : V → E) (s : Finset V) : Set E :=
  geometricCarrier (dualBlockBoundaryFaces K s) (faceBarycenter p)

theorem dualBlockBoundarySpace_subset (K : Finset (Finset V)) (p : V → E) (s : Finset V) :
    dualBlockBoundarySpace K p s ⊆ dualBlockSpace K p s :=
  geometricCarrier_mono_of_subset (dualBlockBoundaryFaces_subset K s) _

theorem dualBlockSpace_subset_space (hK : FaceClosed K) (s : Finset V) :
    dualBlockSpace K p s ⊆ geometricCarrier K p := by
  rw [dualBlockSpace, ← geometricCarrier_subdivisionFaces hK]
  exact geometricCarrier_mono_of_subset (dualBlockFaces_subset K s) _

/-- Dual blocks meet exactly in the dual block of the union of their faces. -/
theorem dualBlockSpace_inter (hgeom : IsGeometricRealization K p) (s t : Finset V) :
    dualBlockSpace K p s ∩ dualBlockSpace K p t = dualBlockSpace K p (s ∪ t) := by
  classical
  rw [dualBlockSpace, dualBlockSpace, dualBlockSpace,
    geometricCarrier_inter (isGeometricRealization_subdivisionFaces hgeom)
      (faceClosed_dualBlockFaces K s) (faceClosed_dualBlockFaces K t)
      (dualBlockFaces_subset K s) (dualBlockFaces_subset K t),
    dualBlockFaces_inter]

/-- The dual blocks of the nonempty faces cover the whole polyhedron. -/
theorem iUnion_dualBlockSpace (hK : FaceClosed K) :
    ⋃ s ∈ K, dualBlockSpace K p s = geometricCarrier K p := by
  classical
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun s _ ↦ dualBlockSpace_subset_space hK s
  · intro x hx
    rw [← geometricCarrier_subdivisionFaces hK] at hx
    obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
    rcases Finset.eq_empty_or_nonempty C with rfl | hCne
    · simp at hxC
    obtain ⟨u, hu, hCu⟩ := exists_mem_dualBlockFaces hC hCne
    exact Set.mem_iUnion₂.mpr ⟨u, hu, Set.mem_iUnion₂.mpr ⟨C, hCu, hxC⟩⟩

/-- The boundary of a dual block is the union of the dual blocks of the faces
strictly containing it. -/
theorem dualBlockBoundarySpace_eq_iUnion (s : Finset V) :
    dualBlockBoundarySpace K p s = ⋃ u ∈ K.filter fun u ↦ s ⊂ u, dualBlockSpace K p u := by
  classical
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨C, hC, hxC⟩ := Set.mem_iUnion₂.mp hx
    rcases Finset.eq_empty_or_nonempty C with rfl | hCne
    · simp at hxC
    obtain ⟨u, huK, hsu, hCu⟩ := (mem_dualBlockBoundaryFaces_iff hCne).mp hC
    exact Set.mem_iUnion₂.mpr ⟨u, Finset.mem_filter.mpr ⟨huK, hsu⟩,
      Set.mem_iUnion₂.mpr ⟨C, hCu, hxC⟩⟩
  · refine Set.iUnion₂_subset fun u hu ↦ ?_
    obtain ⟨huK, hsu⟩ := Finset.mem_filter.mp hu
    refine geometricCarrier_mono_of_subset (fun C hC ↦ ?_) _
    obtain ⟨hCsd, hCu⟩ := mem_dualBlockFaces.mp hC
    exact mem_dualBlockBoundaryFaces.mpr ⟨hCsd, fun t ht ↦ hsu.trans_le (hCu t ht)⟩

/-- The dual block of a face is a nonempty compact star-shaped set. -/
theorem faceBarycenter_mem_dualBlockSpace {s : Finset V} (hs : s ∈ K) (hsne : s.Nonempty) :
    faceBarycenter p s ∈ dualBlockSpace K p s :=
  faceBarycenter_mem_geometricCarrier_dualBlockFaces hs hsne

theorem contractibleSpace_dualBlockSpace {s : Finset V} (hs : s ∈ K) (hsne : s.Nonempty) :
    ContractibleSpace ↥(dualBlockSpace K p s) :=
  contractible_geometricCarrier_dualBlockFaces hs hsne

end AffineTverberg.Simplicial

end
