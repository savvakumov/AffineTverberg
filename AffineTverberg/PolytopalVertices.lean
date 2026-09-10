import AffineTverberg.PolytopalDeletedJoin
import Mathlib.Analysis.Convex.KreinMilman

set_option linter.style.header false

/-!
# Actual vertices and face intersections of a polytope

The `vertices` field of `FullDimensionalPolytope` is a finite generating set,
not an assertion that each generator is an extreme point. This file extracts
the actual vertices and proves that they still generate the polytope and
all its exposed faces. In particular, faces intersect exactly when they share
an actual vertex. This is the repeated-vertex test used by the bad-edge
triangulation; it does not assume that the original presentation was minimal.
-/

noncomputable section

open Set

namespace AffineTverberg

section FiniteHull

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem finite_extremePoints_convexHull (s : Finset E) :
    ((convexHull ℝ (s : Set E)).extremePoints ℝ).Finite :=
  s.finite_toSet.subset extremePoints_convexHull_subset

omit [FiniteDimensional ℝ E] in
/-- The closure in Krein--Milman disappears for a finitely generated convex set,
because its extreme points form a finite set. -/
theorem convexHull_extremePoints_finiteHull (s : Finset E) :
    convexHull ℝ ((convexHull ℝ (s : Set E)).extremePoints ℝ) =
      convexHull ℝ (s : Set E) := by
  have hclosed := (finite_extremePoints_convexHull s).isCompact_convexHull ℝ
  simpa only [hclosed.isClosed.closure_eq] using
    closure_convexHull_extremePoints (s.finite_toSet.isCompact_convexHull ℝ)
      (convex_convexHull ℝ (s : Set E))

end FiniteHull

namespace FullDimensionalPolytope

variable {n : ℕ} (P : FullDimensionalPolytope n)

theorem carrier_compact : IsCompact P.carrier :=
  P.vertices.finite_toSet.isCompact_convexHull ℝ

theorem carrier_nonempty : P.carrier.Nonempty :=
  P.vertices_nonempty.to_set.mono (subset_convexHull ℝ _)

theorem carrier_convex : Convex ℝ P.carrier := convex_convexHull ℝ _

theorem actualVertices_finite : (P.carrier.extremePoints ℝ).Finite :=
  finite_extremePoints_convexHull P.vertices

/-- The actual extreme vertices, independent of redundant chosen generators. -/
def actualVertices : Finset (CoordinateSpace n) := P.actualVertices_finite.toFinset

@[simp]
theorem mem_actualVertices {v : CoordinateSpace n} :
    v ∈ P.actualVertices ↔ v ∈ P.carrier.extremePoints ℝ :=
  P.actualVertices_finite.mem_toFinset

@[simp]
theorem coe_actualVertices : (P.actualVertices : Set (CoordinateSpace n)) =
    P.carrier.extremePoints ℝ := P.actualVertices_finite.coe_toFinset

theorem actualVertices_subset : P.actualVertices ⊆ P.vertices := by
  intro v hv
  exact extremePoints_convexHull_subset (P.mem_actualVertices.mp hv)

theorem actualVertices_nonempty : P.actualVertices.Nonempty := by
  obtain ⟨v, hv⟩ := P.carrier_compact.extremePoints_nonempty P.carrier_nonempty
  exact ⟨v, P.mem_actualVertices.mpr hv⟩

theorem convexHull_actualVertices :
    convexHull ℝ (P.actualVertices : Set (CoordinateSpace n)) = P.carrier := by
  rw [P.coe_actualVertices]
  exact convexHull_extremePoints_finiteHull P.vertices

/-- Re-presenting the same polytope using only actual vertices. -/
def vertexPresentation : FullDimensionalPolytope n where
  vertices := P.actualVertices
  vertices_nonempty := P.actualVertices_nonempty
  affineSpan_vertices := by
    rw [← affineSpan_convexHull, P.convexHull_actualVertices]
    exact (affineSpan_convexHull _).trans P.affineSpan_vertices

@[simp]
theorem carrier_vertexPresentation : P.vertexPresentation.carrier = P.carrier :=
  P.convexHull_actualVertices

/-- The actual vertices of a face are precisely the vertices of the polytope
which belong to that face. -/
theorem extremePoints_face {F : Set (CoordinateSpace n)} (hF : P.IsFace F) :
    F.extremePoints ℝ = F ∩ (P.actualVertices : Set (CoordinateSpace n)) := by
  rw [P.coe_actualVertices]
  exact hF.isExtreme.extremePoints_eq

theorem face_eq_convexHull_actualVertices {F : Set (CoordinateSpace n)}
    (hF : P.IsFace F) :
    F = convexHull ℝ (F ∩ (P.actualVertices : Set (CoordinateSpace n))) := by
  rw [← P.extremePoints_face hF]
  have h := convexHull_extremePoints_finiteHull (P.faceVertices F)
  rw [← P.face_eq_convexHull_filter_vertices hF] at h
  exact h.symm

theorem nonempty_face_contains_actualVertex {F : Set (CoordinateSpace n)}
    (hF : P.IsFace F) (hne : F.Nonempty) :
    ∃ v ∈ P.actualVertices, v ∈ F := by
  obtain ⟨v, hv⟩ := (hF.isCompact P.carrier_compact).extremePoints_nonempty hne
  rw [P.extremePoints_face hF] at hv
  exact ⟨v, hv.2, hv.1⟩

/-- Two exposed faces of a polytope meet if and only if they share an actual
vertex. This includes empty faces and the whole polytope. -/
theorem faces_inter_nonempty_iff {F G : Set (CoordinateSpace n)}
    (hF : P.IsFace F) (hG : P.IsFace G) :
    (F ∩ G).Nonempty ↔ ∃ v ∈ P.actualVertices, v ∈ F ∧ v ∈ G := by
  constructor
  · exact P.nonempty_face_contains_actualVertex (hF.inter hG)
  · rintro ⟨v, _, hv⟩
    exact ⟨v, hv⟩

theorem disjoint_faces_iff {F G : Set (CoordinateSpace n)}
    (hF : P.IsFace F) (hG : P.IsFace G) :
    Disjoint F G ↔ ∀ v ∈ P.actualVertices, v ∈ F → v ∉ G := by
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty,
    P.faces_inter_nonempty_iff hF hG]
  simp only [not_exists, not_and]

/-- The no-repeated-vertex characterization of a deleted face tuple. -/
theorem pairwise_disjoint_faces_iff {ι : Type*} (F : ι → Set (CoordinateSpace n))
    (hF : ∀ i, P.IsFace (F i)) :
    Pairwise (fun i j ↦ Disjoint (F i) (F j)) ↔
      ∀ i j, i ≠ j → ∀ v ∈ P.actualVertices, v ∈ F i → v ∉ F j := by
  simp only [Pairwise, P.disjoint_faces_iff (hF _) (hF _)]

end FullDimensionalPolytope

end AffineTverberg
