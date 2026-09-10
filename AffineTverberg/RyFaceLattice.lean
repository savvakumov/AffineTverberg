import AffineTverberg.RyUpperFaces

set_option linter.style.header false

/-!
# The face of `Q` above a canonical face of `R_y`

The face `qFace t` of the Cayley join lying above a canonical face `t` of the
lifted polytope `R_y` is an actual face of the join, its carrier is the exposed
face of `Q` cut out by the same supporting functional, and — for a face on an
*upper* supporting hyperplane — its projected dimension is the affine dimension
of `t` itself, because the first-coordinate projection is injective there.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace BadVertex

open CayleyJoin PolytopeFace BadEdge UpperFacet _root_.AffineTverberg.Simplicial
open CompactConvexProjection

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Φ : PolytopalJoinMap P m V} {y : StrongDual ℝ V}

/-- The Cayley join is the hull of its Cayley vertices. -/
theorem polytopalJoinCarrier_eq_convexHull (P : FullDimensionalPolytope n) (m : ℕ) :
    polytopalJoinCarrier P m =
      convexHull ℝ (pt P m '' ((Finset.univ : Finset (JoinVertex P m)) :
        Set (JoinVertex P m))) :=
  (sdCarrier_topFace P m).symm

theorem vtx_mem_carrier (P : FullDimensionalPolytope n)
    (k : Fin P.actualVertices.card) : vtx P k ∈ P.carrier :=
  (P.mem_actualVertices.mp (vtx_mem P k)).1

/-- The composite functional on the Cayley join determined by a functional on
the lifted space. -/
def joinForm (Φ : PolytopalJoinMap P m V) (y : StrongDual ℝ V)
    (g : (CoordinateSpace n × ℝ) →L[ℝ] ℝ) : PolytopalJoinAmbient n m →L[ℝ] ℝ :=
  g.comp ((Φ.upperEnvelopeData y).liftedMap)

theorem joinForm_pt (g : (CoordinateSpace n × ℝ) →L[ℝ] ℝ) (w : JoinVertex P m) :
    joinForm Φ y g (pt P m w) = g (liftedVertex Φ y w) := rfl

/-- A functional which is bounded by `c` on the lifted vertex set is bounded by
`c` on the whole Cayley join. -/
theorem joinForm_le_of_valid {g : (CoordinateSpace n × ℝ) →L[ℝ] ℝ} {c : ℝ}
    (hvalid : ∀ v ∈ ryVerts Φ y, g v ≤ c) :
    ∀ z ∈ polytopalJoinCarrier P m, joinForm Φ y g z ≤ c := by
  classical
  have hconv : Convex ℝ {z : PolytopalJoinAmbient n m | joinForm Φ y g z ≤ c} :=
    convex_halfSpace_le (LinearMap.isLinear (joinForm Φ y g).toLinearMap) c
  have hsub : pt P m '' ((Finset.univ : Finset (JoinVertex P m)) :
      Set (JoinVertex P m)) ⊆ {z : PolytopalJoinAmbient n m | joinForm Φ y g z ≤ c} := by
    rintro _ ⟨w, -, rfl⟩
    exact hvalid _ ((mem_ryVerts Φ y).mpr ⟨w, rfl⟩)
  intro z hz
  rw [polytopalJoinCarrier_eq_convexHull] at hz
  exact convexHull_min hsub hconv hz

/-- Membership in `qFace` is cut out by the composite functional. -/
theorem mem_qFace_iff_joinForm {t : Finset (CoordinateSpace n × ℝ)}
    {g : (CoordinateSpace n × ℝ) →L[ℝ] ℝ} {c : ℝ}
    (hmem : ∀ v, v ∈ t ↔ (v ∈ ryVerts Φ y ∧ g v = c)) (w : JoinVertex P m) :
    w ∈ qFace Φ y t ↔ joinForm Φ y g (pt P m w) = c := by
  rw [mem_qFace, hmem]
  refine ⟨fun h ↦ h.2, fun h ↦ ⟨(mem_ryVerts Φ y).mpr ⟨w, rfl⟩, h⟩⟩

/-- **The face above a canonical face is an actual face of the Cayley join.** -/
theorem qFace_mem_faceFamily {t : Finset (CoordinateSpace n × ℝ)}
    (ht : IsExposedGens (ryVerts Φ y) t) : qFace Φ y t ∈ faceFamily P m := by
  classical
  obtain ⟨g, c, hvalid, hmem⟩ := ht
  set G : PolytopalJoinAmbient n m →L[ℝ] ℝ := joinForm Φ y g with hGdef
  have hGle : ∀ x ∈ P.carrier, ∀ i : Fin (m + 1), G (polytopalJoinCopy i x) ≤ c := by
    intro x hx i
    exact joinForm_le_of_valid hvalid _ (polytopalJoinCopy_mem_carrier P i ⟨x, hx⟩)
  have hdecomp : ∀ (i : Fin (m + 1)) (x : CoordinateSpace n),
      polytopalJoinCopy i x =
        polytopalJoinCopyLinear i x + polytopalJoinCopy i 0 := by
    intro i x
    simp [polytopalJoinCopy, polytopalJoinCopyLinear, ← Pi.single_add, Prod.mk_add_mk]
  have hface : ∀ i : Fin (m + 1),
      P.IsFace {x ∈ P.carrier | G (polytopalJoinCopy i x) = c} := by
    intro i hne
    obtain ⟨x₀, hx₀P, hx₀c⟩ := hne
    refine ⟨G.comp (LinearMap.toContinuousLinearMap (polytopalJoinCopyLinear i)), ?_⟩
    set L : CoordinateSpace n →L[ℝ] ℝ :=
      G.comp (LinearMap.toContinuousLinearMap (polytopalJoinCopyLinear i)) with hLdef
    have hsplit : ∀ x : CoordinateSpace n,
        G (polytopalJoinCopy i x) = L x + G (polytopalJoinCopy i 0) := by
      intro x
      rw [hdecomp i x, map_add]
      rfl
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hxP, hxc⟩
      refine ⟨hxP, fun z hz ↦ ?_⟩
      have h1 : L z + G (polytopalJoinCopy i 0) ≤ c := by
        rw [← hsplit z]; exact hGle z hz i
      have h2 : L x + G (polytopalJoinCopy i 0) = c := by rw [← hsplit x]; exact hxc
      linarith
    · rintro ⟨hxP, hmax⟩
      refine ⟨hxP, ?_⟩
      have h0 : L x₀ ≤ L x := hmax x₀ hx₀P
      have h1 : L x₀ + G (polytopalJoinCopy i 0) = c := by
        rw [← hsplit x₀]; exact hx₀c
      have h2 : G (polytopalJoinCopy i x) ≤ c := hGle x hxP i
      rw [hsplit x]
      rw [hsplit x] at h2
      linarith
  refine (mem_faceFamily_iff P m).mpr
    ⟨fun i ↦ PolytopeFaceIndex.ofFace _ (hface i), ?_⟩
  ext w
  rw [mem_faceVertexSet, PolytopeFaceIndex.carrier_ofFace,
    mem_qFace_iff_joinForm hmem w]
  simp only [Set.mem_ofPred_eq]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨vtx_mem_carrier P w.2, h⟩⟩

/-- The carrier of the face above `t` maps onto `conv t`. -/
theorem liftedMap_image_sdCarrier_qFace {t : Finset (CoordinateSpace n × ℝ)}
    (ht : t ⊆ ryVerts Φ y) :
    (Φ.upperEnvelopeData y).liftedMap '' sdCarrier P m (qFace Φ y t) =
      convexHull ℝ (t : Set (CoordinateSpace n × ℝ)) := by
  classical
  rw [sdCarrier]
  change ⇑((Φ.upperEnvelopeData y).liftedMap.toLinearMap) '' _ = _
  rw [(Φ.upperEnvelopeData y).liftedMap.toLinearMap.image_convexHull]
  congr 1
  rw [Set.image_image]
  change liftedVertex Φ y '' _ = _
  rw [← Finset.coe_image, image_liftedVertex_qFace ht]

/-- **The carrier of the face above a canonical face is the exposed face of `Q`
cut out by the same supporting functional.** -/
theorem sdCarrier_qFace_eq {t : Finset (CoordinateSpace n × ℝ)}
    {g : (CoordinateSpace n × ℝ) →L[ℝ] ℝ} {c : ℝ}
    (hvalid : ∀ v ∈ ryVerts Φ y, g v ≤ c)
    (hmem : ∀ v, v ∈ t ↔ (v ∈ ryVerts Φ y ∧ g v = c)) (hne : t.Nonempty) :
    sdCarrier P m (qFace Φ y t) =
      {z ∈ polytopalJoinCarrier P m | g ((Φ.upperEnvelopeData y).liftedMap z) = c} := by
  classical
  set G : PolytopalJoinAmbient n m →L[ℝ] ℝ := joinForm Φ y g with hGdef
  have hGle := joinForm_le_of_valid (Φ := Φ) (y := y) hvalid
  -- a Cayley vertex of the face
  obtain ⟨v₀, hv₀⟩ := hne
  obtain ⟨w₀, hw₀⟩ := (mem_ryVerts Φ y).mp ((hmem v₀).1 hv₀).1
  have hw₀mem : w₀ ∈ qFace Φ y t := mem_qFace.mpr (hw₀ ▸ hv₀)
  have hw₀c : G (pt P m w₀) = c := (mem_qFace_iff_joinForm hmem w₀).1 hw₀mem
  apply Subset.antisymm
  · -- the hull of the vertices of the face lies in the exposed set
    have hconv : Convex ℝ {z ∈ polytopalJoinCarrier P m | G z = c} := by
      have h1 : Convex ℝ (polytopalJoinCarrier P m) := convex_convexHull ℝ _
      have h2 : Convex ℝ {z : PolytopalJoinAmbient n m | G z = c} := by
        have : {z : PolytopalJoinAmbient n m | G z = c} =
            {z : PolytopalJoinAmbient n m | G z ≤ c} ∩
              {z : PolytopalJoinAmbient n m | c ≤ G z} := by
          ext z; simp [le_antisymm_iff, and_comm]
        rw [this]
        exact (convex_halfSpace_le (LinearMap.isLinear G.toLinearMap) c).inter
          (convex_halfSpace_ge (LinearMap.isLinear G.toLinearMap) c)
      exact h1.inter h2
    refine convexHull_min ?_ hconv
    rintro _ ⟨w, hw, rfl⟩
    refine ⟨?_, (mem_qFace_iff_joinForm hmem w).1 (Finset.mem_coe.mp hw)⟩
    rw [polytopalJoinCarrier_eq_convexHull]
    exact subset_convexHull ℝ _ ⟨w, Finset.mem_coe.mpr (Finset.mem_univ w), rfl⟩
  · -- conversely, the exposed set is the hull of the maximizing vertices
    intro z hz
    obtain ⟨hzQ, hzc⟩ := hz
    have hQeq : polytopalJoinCarrier P m =
        convexHull ℝ (((Finset.univ : Finset (JoinVertex P m)).image (pt P m) :
          Finset (PolytopalJoinAmbient n m)) : Set (PolytopalJoinAmbient n m)) := by
      rw [polytopalJoinCarrier_eq_convexHull, Finset.coe_image]
    have hzmem : z ∈ exposedBy (polytopalJoinCarrier P m) G := by
      refine ⟨hzQ, fun u hu ↦ ?_⟩
      have := hGle u hu
      change G u ≤ c at this
      change G u ≤ G z
      rw [show G z = c from hzc]
      exact this
    rw [hQeq, exposedBy_convexHull] at hzmem
    refine convexHull_mono ?_ hzmem
    intro u hu
    obtain ⟨huim, humax⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hu)
    obtain ⟨w, -, rfl⟩ := Finset.mem_image.mp huim
    have hw₀im : pt P m w₀ ∈ (Finset.univ : Finset (JoinVertex P m)).image (pt P m) :=
      Finset.mem_image.mpr ⟨w₀, Finset.mem_univ _, rfl⟩
    have hge : c ≤ G (pt P m w) := by
      have := humax _ hw₀im
      rw [hw₀c] at this
      exact this
    have hle : G (pt P m w) ≤ c := by
      refine hGle _ ?_
      rw [polytopalJoinCarrier_eq_convexHull]
      exact subset_convexHull ℝ _ ⟨w, Finset.mem_coe.mpr (Finset.mem_univ w), rfl⟩
    exact ⟨w, Finset.mem_coe.mpr ((mem_qFace_iff_joinForm hmem w).2 (le_antisymm hle hge)),
      rfl⟩

/-! ### The projected dimension of an upper face -/

theorem fst_liftedVertex (w : JoinVertex P m) :
    (liftedVertex Φ y w).1 = vtx P w.2 := by
  have h : (liftedVertex Φ y w).1 = (Φ.upperEnvelopeData y).projection (pt P m w) := rfl
  rw [h, Φ.upperEnvelopeData_projection y, pt, polytopalJoinProjection_copy]

/-- The projected vertex set of the face above `t` is the base projection of
`t`. -/
theorem projPts_qFace {t : Finset (CoordinateSpace n × ℝ)} (ht : t ⊆ ryVerts Φ y) :
    projPts P m (qFace Φ y t) = Prod.fst '' (t : Set (CoordinateSpace n × ℝ)) := by
  classical
  ext v
  simp only [projPts, Set.mem_iUnion, mem_factorPts, Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨i, w, hw, -, rfl⟩
    exact ⟨liftedVertex Φ y w, mem_qFace.mp hw, fst_liftedVertex w⟩
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨w, rfl⟩ := (mem_ryVerts Φ y).mp (ht hp)
    exact ⟨w.1, w, mem_qFace.mpr hp, rfl, (fst_liftedVertex w).symm⟩

/-- **For a face on an upper supporting hyperplane the projected dimension is
the dimension of the face itself.** -/
theorem projDim_qFace_of_upper {t : Finset (CoordinateSpace n × ℝ)} (ht : t ⊆ ryVerts Φ y)
    (hne : t.Nonempty) {g : (CoordinateSpace n × ℝ) →L[ℝ] ℝ} {c : ℝ}
    (hg : vcoeff g ≠ 0) (htight : ∀ v ∈ t, g v = c) :
    projDim P m (qFace Φ y t) + 1 =
      arank (convexHull ℝ (t : Set (CoordinateSpace n × ℝ))) := by
  classical
  have hrank : arank (Prod.fst '' (t : Set (CoordinateSpace n × ℝ))) =
      arank (t : Set (CoordinateSpace n × ℝ)) :=
    arank_fst_image_of_forall_tight hg (fun p hp ↦ htight p (Finset.mem_coe.mp hp))
  have hpos : 0 < arank (t : Set (CoordinateSpace n × ℝ)) := by
    obtain ⟨v, hv⟩ := hne
    exact arank_pos ⟨v, Finset.mem_coe.mpr hv⟩
  rw [arank_convexHull, projDim, projPts_qFace ht, hrank]
  omega

end BadVertex
end AffineTverberg
