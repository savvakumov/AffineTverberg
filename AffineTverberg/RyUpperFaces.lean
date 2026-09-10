import AffineTverberg.UpperFacetVisibility
import AffineTverberg.RyFacetPresentation
import AffineTverberg.PolytopalCellGluing

set_option linter.style.header false

/-!
# The upper faces of `R_y` and the faces of `Q` above them

`R_y = (π, y ∘ Φ)(Q)` is the lifted image of the Cayley join `Q`.  Its
generating set is the image `ryVerts` of the Cayley vertices under the lifting
map, so the whole facet theory of `RelativeFacet.lean` and the shelling of
`CanonicalVisibleShelling.lean` apply to it.

This file connects a canonical face `t` of `ryVerts` with the face

`qFace t = {w : Cayley vertex | (π, y ∘ Φ)(w) ∈ t}`

of the Cayley join lying above it:

* `qFace_mem_faceFamily` — it is an actual face of the Cayley join, i.e. a
  member of `BadVertex.faceFamily`, obtained from the exposed faces of `P`
  which the supporting functional cuts out in each copy;
* `qFace_inter`, `qFace_eq_empty_iff`, `qFace_inj` — the assignment is a
  meet-preserving, bottom-reflecting injection on canonical faces;
* `sdCarrier_qFace` — its carrier is the exposed face of `Q` above the face
  `conv t`, and `liftedMap_image_sdCarrier_qFace` — it maps onto `conv t`;
* `projDim_qFace` — for a face lying on an *upper* facet hyperplane the
  projected dimension is the affine dimension of the face itself, because the
  first-coordinate projection is injective there.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace BadVertex

open CayleyJoin PolytopeFace BadEdge UpperFacet _root_.AffineTverberg.Simplicial
open CompactConvexProjection

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### The lifted vertex set of `R_y` -/

/-- The lifted Cayley vertex: its base point together with its `y`-height. -/
def liftedVertex (Φ : PolytopalJoinMap P m V) (y : StrongDual ℝ V)
    (w : JoinVertex P m) : CoordinateSpace n × ℝ :=
  (Φ.upperEnvelopeData y).liftedMap (pt P m w)

/-- The finite generating set of the lifted polytope `R_y`. -/
def ryVerts (Φ : PolytopalJoinMap P m V) (y : StrongDual ℝ V) :
    Finset (CoordinateSpace n × ℝ) :=
  Finset.univ.image (liftedVertex Φ y)

variable (Φ : PolytopalJoinMap P m V) (y : StrongDual ℝ V)

theorem mem_ryVerts {v : CoordinateSpace n × ℝ} :
    v ∈ ryVerts Φ y ↔ ∃ w : JoinVertex P m, liftedVertex Φ y w = v := by
  simp [ryVerts]

/-- **The lifted vertex set generates `R_y`.** -/
theorem convexHull_ryVerts :
    convexHull ℝ ((ryVerts Φ y : Finset (CoordinateSpace n × ℝ)) : Set (CoordinateSpace n × ℝ)) =
      (Φ.upperEnvelopeData y).liftedImage := by
  classical
  have hQ : (Φ.upperEnvelopeData y).carrier =
      convexHull ℝ (pt P m '' (Finset.univ : Finset (JoinVertex P m))) := by
    rw [Φ.upperEnvelopeData_carrier, ← sdCarrier_topFace P m]
    rfl
  have himg : ((ryVerts Φ y : Finset (CoordinateSpace n × ℝ)) : Set (CoordinateSpace n × ℝ)) =
      (Φ.upperEnvelopeData y).liftedMap '' (pt P m '' (Finset.univ : Finset (JoinVertex P m))) := by
    ext v
    simp [ryVerts, liftedVertex]
  rw [himg, CompactConvexProjection.liftedImage, hQ]
  exact ((Φ.upperEnvelopeData y).liftedMap.toLinearMap.image_convexHull _).symm

theorem ryVerts_nonempty : (ryVerts Φ y).Nonempty := by
  obtain ⟨v, hv⟩ := P.actualVertices_nonempty
  obtain ⟨k, -⟩ := exists_vtx P hv
  exact ⟨liftedVertex Φ y ((0, k) : JoinVertex P m),
    (mem_ryVerts Φ y).mpr ⟨((0, k) : JoinVertex P m), rfl⟩⟩

/-- The affine span of the lifted vertex set is everything, for a nondegenerate
join map. -/
theorem affineSpan_ryVerts (hy : y ≠ 0) (hspan : FactorImagesAffinelySpan Φ.factor) :
    affineSpan ℝ ((ryVerts Φ y : Finset (CoordinateSpace n × ℝ)) :
      Set (CoordinateSpace n × ℝ)) = ⊤ := by
  have h := Φ.upperEnvelopeData_liftedImage_affineSpan_eq_top y hy hspan
  rw [← convexHull_ryVerts Φ y, affineSpan_convexHull] at h
  exact h

/-- The affine rank of `R_y` is `n + 2`: it is a full dimensional polytope in
`CoordinateSpace n × ℝ`. -/
theorem arank_ryVerts (hy : y ≠ 0) (hspan : FactorImagesAffinelySpan Φ.factor) :
    arank (convexHull ℝ ((ryVerts Φ y : Finset (CoordinateSpace n × ℝ)) :
      Set (CoordinateSpace n × ℝ))) = n + 2 := by
  have hne : (convexHull ℝ ((ryVerts Φ y : Finset (CoordinateSpace n × ℝ)) :
      Set (CoordinateSpace n × ℝ))).Nonempty := by
    obtain ⟨v, hv⟩ := ryVerts_nonempty Φ y
    exact ⟨v, subset_convexHull ℝ _ (Finset.mem_coe.mpr hv)⟩
  rw [arank_of_nonempty hne]
  have hspan' := affineSpan_ryVerts Φ y hy hspan
  have hvs : vectorSpan ℝ ((ryVerts Φ y : Finset (CoordinateSpace n × ℝ)) :
      Set (CoordinateSpace n × ℝ)) = ⊤ := by
    have := congrArg AffineSubspace.direction hspan'
    rwa [direction_affineSpan, AffineSubspace.direction_top] at this
  have hvs' : vectorSpan ℝ (convexHull ℝ ((ryVerts Φ y : Finset (CoordinateSpace n × ℝ)) :
      Set (CoordinateSpace n × ℝ))) = ⊤ := by
    have h1 : affineSpan ℝ (convexHull ℝ ((ryVerts Φ y : Finset (CoordinateSpace n × ℝ)) :
        Set (CoordinateSpace n × ℝ))) = ⊤ := by
      rw [affineSpan_convexHull]; exact hspan'
    have := congrArg AffineSubspace.direction h1
    rwa [direction_affineSpan, AffineSubspace.direction_top] at this
  rw [hvs']
  have : Module.finrank ℝ (⊤ : Submodule ℝ (CoordinateSpace n × ℝ)) =
      Module.finrank ℝ (CoordinateSpace n × ℝ) := finrank_top ℝ _
  rw [this]
  simp [Module.finrank_prod]

/-! ### The face of `Q` above a face of `R_y` -/

/-- The face of the Cayley join lying above a set of lifted vertices. -/
def qFace (t : Finset (CoordinateSpace n × ℝ)) : Finset (JoinVertex P m) :=
  Finset.univ.filter fun w ↦ liftedVertex Φ y w ∈ t

variable {Φ y}

@[simp] theorem mem_qFace {t : Finset (CoordinateSpace n × ℝ)} {w : JoinVertex P m} :
    w ∈ qFace Φ y t ↔ liftedVertex Φ y w ∈ t := by
  simp [qFace]

theorem qFace_inter (t₁ t₂ : Finset (CoordinateSpace n × ℝ)) :
    qFace Φ y (t₁ ∩ t₂) = qFace Φ y t₁ ∩ qFace Φ y t₂ := by
  ext w
  simp [Finset.mem_inter]

theorem qFace_mono {t₁ t₂ : Finset (CoordinateSpace n × ℝ)} (h : t₁ ⊆ t₂) :
    qFace Φ y t₁ ⊆ qFace Φ y t₂ := by
  intro w hw
  exact mem_qFace.mpr (h (mem_qFace.mp hw))

theorem qFace_empty : qFace Φ y (∅ : Finset (CoordinateSpace n × ℝ)) = ∅ := by
  ext w
  simp

/-- The lifted vertices of the face above `t` are exactly `t`. -/
theorem image_liftedVertex_qFace {t : Finset (CoordinateSpace n × ℝ)}
    (ht : t ⊆ ryVerts Φ y) : (qFace Φ y t).image (liftedVertex Φ y) = t := by
  ext v
  simp only [Finset.mem_image, mem_qFace]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hv
    obtain ⟨w, rfl⟩ := (mem_ryVerts Φ y).mp (ht hv)
    exact ⟨w, hv, rfl⟩

theorem qFace_eq_empty_iff {t : Finset (CoordinateSpace n × ℝ)} (ht : t ⊆ ryVerts Φ y) :
    qFace Φ y t = ∅ ↔ t = ∅ := by
  constructor
  · intro h
    have := image_liftedVertex_qFace ht
    rw [h] at this
    simpa using this.symm
  · rintro rfl
    exact qFace_empty

theorem qFace_inj {t₁ t₂ : Finset (CoordinateSpace n × ℝ)} (h₁ : t₁ ⊆ ryVerts Φ y)
    (h₂ : t₂ ⊆ ryVerts Φ y) (h : qFace Φ y t₁ = qFace Φ y t₂) : t₁ = t₂ := by
  rw [← image_liftedVertex_qFace h₁, ← image_liftedVertex_qFace h₂, h]

end BadVertex
end AffineTverberg
