import AffineTverberg.UpperSubdivision
import AffineTverberg.PolytopalJoin

set_option linter.style.header false

/-!
# The actual facet presentation and upper subdivision of `R_y`

`R_y = (π, y ∘ Φ)(Q)` is the lifted image of the concrete polytopal join
`Q = conv (polytopalJoinVertices P m)`.  Since `Q` is an honest `V`-polytope
and `R_y` is full dimensional (`upperEnvelopeData_liftedImage_affineSpan_eq_top`
for a nondegenerate join map and `y ≠ 0`), the facet description of
`PolytopeHDescription.lean` applies verbatim and produces

* `ryPresentation` — an **exact finite halfspace presentation** of `R_y`, with
  actual facet inequalities `a(x) + b t ≤ c` obtained from the finite vertex
  set of `Q`; nothing is assumed.

From it we get, with no further hypotheses, the statements of the upper
subdivision of `P`:

* `ry_topGraph_eq_iUnion_topFacet` — the union of the top facets (`b > 0`) of
  `R_y` is exactly the upper graph of `R_y`;
* `ry_iUnion_cell_eq_carrier` — their projections cover `P`;
* `ry_cells_intersect` — the cells meet exactly along the projections of the
  facet intersections, each cell having a unique affine graph lift;
* `ry_arank_cell` — projection preserves the affine dimension of a top facet,
  so the dimension of a cell is the dimension of the corresponding upper face;
* `ry_carrierFace_eq_exposedBy` and `ry_liftedMap_image_carrierFace` — the
  preimage in `Q` of a facet of `R_y` is an actual exposed face of `Q` mapping
  onto it;
* `ry_exists_visibility_threshold` — from a point `(x₀, T)` over the base with
  `T` large, precisely the top facets of `R_y` are violated, i.e. visible.

What is *not* proved here, and is the remaining geometric gap towards the
`ShellableGluing.CellShelling` certificate for the upper faces, is the
Bruggesser--Mani recursive line shelling itself: that the visible facets from
such an external point can be ordered so that each new facet meets the union of
the previous ones in a recursively shelled ball of one lower dimension.  The
present file supplies the ingredients that statement quantifies over (actual
facets, their contact faces, the cells and their dimensions, and the exact
visibility criterion from a far away point), but the recursive overlap
statement itself is not formalized.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace PolytopalJoinMap

open CompactConvexProjection CayleyJoin

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Φ : PolytopalJoinMap P m V)

/-- The index type of the actual facet presentation of `R_y`: subsets of the
lifted vertex set of the join polytope. -/
abbrev RyFacetIndex (y : StrongDual ℝ V) : Type _ :=
  (Φ.upperEnvelopeData y).FacetIndex (polytopalJoinVertices P m)

/-- **The actual finite halfspace presentation of `R_y`.**  Its inequalities
are the genuine facet inequalities of the polytope `R_y`, computed from the
finite vertex set of the Cayley join. -/
def ryPresentation (y : StrongDual ℝ V) (hy : y ≠ 0)
    (hspan : FactorImagesAffinelySpan Φ.factor) :
    FiniteHalfspacePresentation (Φ.upperEnvelopeData y) (J := Φ.RyFacetIndex y) :=
  polytopalPresentation (Φ.upperEnvelopeData y) rfl
    (Φ.upperEnvelopeData_liftedImage_affineSpan_eq_top y hy hspan)

section Results

variable {Φ} {y : StrongDual ℝ V} (hy : y ≠ 0) (hspan : FactorImagesAffinelySpan Φ.factor)

/-- **The union of the top facets of `R_y` is exactly its upper graph.** -/
theorem ry_topGraph_eq_iUnion_topFacet :
    (Φ.upperEnvelopeData y).topGraph =
      ⋃ (j : Φ.RyFacetIndex y) (_ : (Φ.ryPresentation y hy hspan).IsTopIndex j),
        (Φ.ryPresentation y hy hspan).facetSet j :=
  FiniteHalfspacePresentation.topGraph_eq_iUnion_topFacet _

/-- **The cells of the upper subdivision cover `P`.** -/
theorem ry_iUnion_cell_eq_carrier :
    ⋃ (j : Φ.RyFacetIndex y) (_ : (Φ.ryPresentation y hy hspan).IsTopIndex j),
        (Φ.ryPresentation y hy hspan).cell j = P.carrier := by
  rw [FiniteHalfspacePresentation.iUnion_cell_eq_base]
  exact Φ.upperEnvelopeData_base y

/-- **The cells meet exactly along the projections of the facet
intersections.** -/
theorem ry_cells_intersect {j k : Φ.RyFacetIndex y}
    (hj : (Φ.ryPresentation y hy hspan).IsTopIndex j)
    (hk : (Φ.ryPresentation y hy hspan).IsTopIndex k) :
    Prod.fst '' ((Φ.ryPresentation y hy hspan).facetSet j ∩
        (Φ.ryPresentation y hy hspan).facetSet k) =
      (Φ.ryPresentation y hy hspan).cell j ∩ (Φ.ryPresentation y hy hspan).cell k :=
  FiniteHalfspacePresentation.fst_image_inter_facetSet _ hj hk

/-- Each top facet is the graph of the affine lift of its cell. -/
theorem ry_graphLift_fst {j : Φ.RyFacetIndex y}
    (hj : (Φ.ryPresentation y hy hspan).IsTopIndex j)
    {p : CoordinateSpace n × ℝ} (hp : (Φ.ryPresentation y hy hspan).IsActiveAt j p) :
    (Φ.ryPresentation y hy hspan).graphLift j p.1 = p :=
  FiniteHalfspacePresentation.graphLift_fst _ hj hp

/-- **Projection preserves the affine dimension of an upper face.** -/
theorem ry_arank_cell {j : Φ.RyFacetIndex y}
    (hj : (Φ.ryPresentation y hy hspan).IsTopIndex j) :
    arank ((Φ.ryPresentation y hy hspan).cell j) =
      arank ((Φ.ryPresentation y hy hspan).facetSet j) :=
  FiniteHalfspacePresentation.arank_cell _ hj

/-- **The preimage in `Q` of a facet of `R_y` is an actual exposed face of
`Q`.** -/
theorem ry_carrierFace_eq_exposedBy {j : Φ.RyFacetIndex y}
    (hne : ((Φ.ryPresentation y hy hspan).carrierFace j).Nonempty) :
    (Φ.ryPresentation y hy hspan).carrierFace j =
      PolytopeFace.exposedBy (polytopalJoinCarrier P m)
        (((Φ.ryPresentation y hy hspan).formCLM j).comp
          (Φ.upperEnvelopeData y).liftedMap) :=
  FiniteHalfspacePresentation.carrierFace_eq_exposedBy _ hne

/-- That exposed face maps onto the facet. -/
theorem ry_liftedMap_image_carrierFace (j : Φ.RyFacetIndex y) :
    (Φ.upperEnvelopeData y).liftedMap '' (Φ.ryPresentation y hy hspan).carrierFace j =
      (Φ.ryPresentation y hy hspan).facetSet j :=
  FiniteHalfspacePresentation.liftedMap_image_carrierFace _ j

/-- **From a point high above a base point, precisely the top facets of `R_y`
are visible.** -/
theorem ry_exists_visibility_threshold {x₀ : CoordinateSpace n} (hx₀ : x₀ ∈ P.carrier) :
    ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ j : Φ.RyFacetIndex y,
      ((Φ.ryPresentation y hy hspan).IsViolatedAt j (x₀, T) ↔
        (Φ.ryPresentation y hy hspan).IsTopIndex j) := by
  apply FiniteHalfspacePresentation.exists_visibility_threshold
  rw [Φ.upperEnvelopeData_base y]
  exact hx₀

end Results

end PolytopalJoinMap
end AffineTverberg
