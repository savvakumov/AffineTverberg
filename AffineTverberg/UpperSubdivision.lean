import AffineTverberg.PolytopalUpperFacets

set_option linter.style.header false

/-!
# The upper subdivision of the base induced by the top facets

Let `A` be a compact convex projection with an exact finite halfspace
presentation `H` of its lifted image `R` (produced from actual polytope data in
`PolytopalUpperFacets.lean`).  The top facets of `R` are the contact sets of the
inequalities with positive vertical coefficient, and their union is exactly the
upper graph of `R`.  This file proves that projecting them to the base is an
honest cell decomposition:

* `injOn_fst_topGraph` — the projection is injective on the upper graph, so
  every projected cell has a *unique* graph lift; `graphLift` is the explicit
  affine lift determined by the facet hyperplane, and `graphLift_fst` says it
  inverts the projection on the facet.
* `fst_image_inter_facetSet` — projections of top facets intersect exactly in
  the projection of their intersection, i.e. the cells fit together along
  their common faces.
* `arank_fst_image_facetSet` — the projection preserves the affine dimension of
  a top facet: the cell has the same dimension as the facet.
* `fst_image_topGraph` — the cells cover the whole base.
* `carrierFace_eq_exposedBy`, `liftedMap_image_carrierFace` — the preimage in
  `Q` of a facet of `R` is an actual *exposed* face of `Q` mapping onto that
  facet, and preimages of intersections are intersections of preimages.

Everything is proved for the genuine oriented data of the presentation; no
subdivision, triangulation, or facet system is assumed.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace CompactConvexProjection

open CayleyJoin

/-! ### Affine rank under affine maps -/

section Rank

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

omit [FiniteDimensional ℝ Y] in
/-- An affine image does not increase the affine rank. -/
theorem arank_image_le (f : X →ᵃ[ℝ] Y) (s : Set X) : arank (f '' s) ≤ arank s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · rw [arank_of_nonempty hs, arank_of_nonempty (hs.image f)]
    have hspan : vectorSpan ℝ (f '' s) = Submodule.map f.linear (vectorSpan ℝ s) :=
      (AffineMap.map_vectorSpan f).symm
    rw [hspan]
    exact Nat.succ_le_succ (Submodule.finrank_map_le _ _)

/-- Two affine maps inverse to each other on a set preserve its affine rank. -/
theorem arank_image_eq_of_leftInvOn (f : X →ᵃ[ℝ] Y) (g : Y →ᵃ[ℝ] X) {s : Set X}
    (hgf : ∀ x ∈ s, g (f x) = x) : arank (f '' s) = arank s := by
  refine le_antisymm (arank_image_le f s) ?_
  have himg : g '' (f '' s) = s := by
    ext x
    constructor
    · rintro ⟨y, ⟨x', hx', rfl⟩, rfl⟩
      rwa [hgf x' hx']
    · intro hx
      exact ⟨f x, ⟨x, hx, rfl⟩, hgf x hx⟩
  calc arank s = arank (g '' (f '' s)) := by rw [himg]
    _ ≤ arank (f '' s) := arank_image_le g _

end Rank

section BaseProjection

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] (A : CompactConvexProjection E F)

/-- The projection to the base is injective on the upper graph. -/
theorem injOn_fst_topGraph : Set.InjOn Prod.fst A.topGraph := by
  intro p hp q hq hpq
  have hp2 : p.2 = A.upperEnvelope p.1 := hp.2
  have hq2 : q.2 = A.upperEnvelope q.1 := hq.2
  exact Prod.ext hpq (by rw [hp2, hq2, hpq])

/-- **The cells cover the base**: the projection of the upper graph is the whole
base. -/
theorem fst_image_topGraph : Prod.fst '' A.topGraph = A.base := by
  apply Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    exact hp.1
  · intro x hx
    exact ⟨(x, A.upperEnvelope x), ⟨hx, rfl⟩, rfl⟩

end BaseProjection

namespace FiniteHalfspacePresentation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {J : Type*} [Finite J] {A : CompactConvexProjection E F}
  (H : FiniteHalfspacePresentation A (J := J))

/-! ### The unique graph lift over a cell -/

/-- The affine lift determined by a top facet hyperplane: over the base point
`x` it returns the unique height with `a(x) + b t = c`. -/
def graphLift (j : J) : F →ᵃ[ℝ] F × ℝ where
  toFun x := (x, (H.bound j - H.baseNormal j x) / H.verticalCoeff j)
  linear :=
    { toFun := fun v ↦ (v, -(H.baseNormal j v) / H.verticalCoeff j)
      map_add' := by intro v w; simp [Prod.ext_iff]; ring
      map_smul' := by intro r v; simp [Prod.ext_iff]; ring }
  map_vadd' := by
    intro x v
    simp [Prod.ext_iff]
    ring

omit [Finite J] in
@[simp] theorem graphLift_apply (j : J) (x : F) :
    H.graphLift j x = (x, (H.bound j - H.baseNormal j x) / H.verticalCoeff j) := rfl

omit [Finite J] in
/-- On the facet, the lift inverts the projection. -/
theorem graphLift_fst {j : J} (hj : H.IsTopIndex j) {p : F × ℝ}
    (hp : H.IsActiveAt j p) : H.graphLift j p.1 = p := by
  have hb : H.verticalCoeff j ≠ 0 := ne_of_gt hj
  have hactive : H.baseNormal j p.1 + H.verticalCoeff j * p.2 = H.bound j := hp
  have h2 : (H.bound j - H.baseNormal j p.1) / H.verticalCoeff j = p.2 := by
    field_simp
    linarith
  simp [graphLift_apply, h2]

/-! ### The cells: projections of the top facets -/

/-- The cell of the base subdivision below a facet. -/
def cell (j : J) : Set F := Prod.fst '' H.facetSet j

include H in
theorem facetSet_subset_topGraph {j : J} (hj : H.IsTopIndex j) :
    H.facetSet j ⊆ A.topGraph := by
  have : Nonempty J := ⟨j⟩
  intro p hp
  rw [H.mem_topGraph_iff_exists_top_active p]
  exact ⟨hp.1, j, hj, hp.2⟩

/-- **The cells fit together**: the projections of two top facets meet exactly
in the projection of the intersection of the facets. -/
theorem fst_image_inter_facetSet {j k : J} (hj : H.IsTopIndex j) (hk : H.IsTopIndex k) :
    Prod.fst '' (H.facetSet j ∩ H.facetSet k) = H.cell j ∩ H.cell k := by
  apply Subset.antisymm
  · rintro x ⟨p, hp, rfl⟩
    exact ⟨⟨p, hp.1, rfl⟩, ⟨p, hp.2, rfl⟩⟩
  · rintro x ⟨⟨p, hp, rfl⟩, ⟨q, hq, hqx⟩⟩
    have hpq : q = p :=
      injOn_fst_topGraph A (H.facetSet_subset_topGraph hk hq)
        (H.facetSet_subset_topGraph hj hp) hqx
    exact ⟨p, ⟨hp, hpq ▸ hq⟩, rfl⟩

include H in
/-- The cells of the top facets cover the base. -/
theorem iUnion_cell_eq_base [Nonempty J] :
    ⋃ (j : J) (_ : H.IsTopIndex j), H.cell j = A.base := by
  rw [← fst_image_topGraph A, H.topGraph_eq_iUnion_topFacet]
  simp only [image_iUnion, cell]

end FiniteHalfspacePresentation

/-! ### The dimension of a cell, and the exposed face of `Q` above it -/

namespace FiniteHalfspacePresentation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {J : Type*} [Finite J] {A : CompactConvexProjection E F}
  (H : FiniteHalfspacePresentation A (J := J))

omit [Finite J] in
/-- **The projection preserves the affine dimension of a top facet**: a cell has
the same affine rank as the facet above it. -/
theorem arank_cell {j : J} (hj : H.IsTopIndex j) :
    arank (H.cell j) = arank (H.facetSet j) := by
  refine arank_image_eq_of_leftInvOn
    (AffineMap.fst : (F × ℝ) →ᵃ[ℝ] F) (H.graphLift j) ?_
  intro p hp
  exact H.graphLift_fst hj hp.2

/-! ### The exposed face of `Q` above a facet -/

/-- The affine form of the `j`-th inequality as a continuous linear functional
on `F × ℝ`. -/
def formCLM (j : J) : (F × ℝ) →L[ℝ] ℝ :=
  (H.baseNormal j).comp (ContinuousLinearMap.fst ℝ F ℝ) +
    H.verticalCoeff j • (ContinuousLinearMap.snd ℝ F ℝ)

omit [Finite J] [FiniteDimensional ℝ F] in
@[simp] theorem formCLM_apply (j : J) (p : F × ℝ) : H.formCLM j p = H.form j p := by
  simp [formCLM, form, mul_comm]

/-- The part of `Q` lying over the `j`-th facet. -/
def carrierFace (j : J) : Set E :=
  {w ∈ A.carrier | H.IsActiveAt j (A.liftedMap w)}

omit [FiniteDimensional ℝ F] in
include H in
omit [Finite J] in
/-- **The preimage of a facet is an exposed face of `Q`.** -/
theorem carrierFace_eq_exposedBy {j : J} (hne : (H.carrierFace j).Nonempty) :
    H.carrierFace j =
      PolytopeFace.exposedBy A.carrier ((H.formCLM j).comp A.liftedMap) := by
  obtain ⟨w₀, hw₀carrier, hw₀active⟩ := hne
  have hbound : ∀ w ∈ A.carrier, H.form j (A.liftedMap w) ≤ H.bound j := fun w hw ↦
    H.le_bound_of_mem_liftedImage ⟨w, hw, rfl⟩ j
  ext w
  constructor
  · rintro ⟨hw, hactive⟩
    refine ⟨hw, fun y hy ↦ ?_⟩
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply, formCLM_apply]
    rw [show H.form j (A.liftedMap w) = H.bound j from hactive]
    exact hbound y hy
  · rintro ⟨hw, hmax⟩
    refine ⟨hw, ?_⟩
    have h1 : H.form j (A.liftedMap w₀) ≤ H.form j (A.liftedMap w) := by
      have := hmax w₀ hw₀carrier
      simpa using this
    have h2 : H.form j (A.liftedMap w₀) = H.bound j := hw₀active
    exact le_antisymm (hbound w hw) (by rw [← h2]; exact h1)

omit [FiniteDimensional ℝ F] in
include H in
omit [Finite J] in
/-- The exposed face of `Q` over a facet maps onto that facet. -/
theorem liftedMap_image_carrierFace (j : J) :
    A.liftedMap '' H.carrierFace j = H.facetSet j := by
  apply Subset.antisymm
  · rintro p ⟨w, ⟨hw, hactive⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, hactive⟩
  · rintro p ⟨⟨w, hw, rfl⟩, hactive⟩
    exact ⟨w, ⟨hw, hactive⟩, rfl⟩

omit [FiniteDimensional ℝ F] in
include H in
omit [Finite J] [FiniteDimensional ℝ F] in
include H in
/-- **The intersection of two facets is again an exposed face**, exposed by the
sum of the two forms.  This is the face along which two cells of the upper
subdivision are glued. -/
theorem facetSet_inter_eq_exposedBy {j k : J}
    (hne : (H.facetSet j ∩ H.facetSet k).Nonempty) :
    H.facetSet j ∩ H.facetSet k =
      PolytopeFace.exposedBy A.liftedImage (H.formCLM j + H.formCLM k) := by
  obtain ⟨p₀, ⟨hp₀R, hp₀j⟩, -, hp₀k⟩ := hne
  have hsum : ∀ q ∈ A.liftedImage,
      H.formCLM j q + H.formCLM k q ≤ H.bound j + H.bound k := by
    intro q hq
    have h1 := H.le_bound_of_mem_liftedImage hq j
    have h2 := H.le_bound_of_mem_liftedImage hq k
    simp only [formCLM_apply]
    linarith
  have hp₀val : H.formCLM j p₀ + H.formCLM k p₀ = H.bound j + H.bound k := by
    simp only [formCLM_apply]
    rw [show H.form j p₀ = H.bound j from hp₀j, show H.form k p₀ = H.bound k from hp₀k]
  ext q
  constructor
  · rintro ⟨⟨hqR, hqj⟩, -, hqk⟩
    refine ⟨hqR, fun y hy ↦ ?_⟩
    have hqval : H.formCLM j q + H.formCLM k q = H.bound j + H.bound k := by
      simp only [formCLM_apply]
      rw [show H.form j q = H.bound j from hqj, show H.form k q = H.bound k from hqk]
    simp only [add_apply] at hqval ⊢
    rw [hqval]
    exact hsum y hy
  · rintro ⟨hqR, hmax⟩
    have hge : H.bound j + H.bound k ≤ H.formCLM j q + H.formCLM k q := by
      have := hmax p₀ hp₀R
      simp only [add_apply] at this
      rw [← hp₀val]
      exact this
    have h1 := H.le_bound_of_mem_liftedImage hqR j
    have h2 := H.le_bound_of_mem_liftedImage hqR k
    simp only [formCLM_apply] at hge
    have hj : H.form j q = H.bound j := by linarith
    have hk : H.form k q = H.bound k := by linarith
    exact ⟨⟨hqR, hj⟩, ⟨hqR, hk⟩⟩

omit [Finite J] [FiniteDimensional ℝ F] in
/-- Preimages of facets intersect in the preimage of the intersection. -/
theorem carrierFace_inter (j k : J) :
    H.carrierFace j ∩ H.carrierFace k =
      {w ∈ A.carrier | H.IsActiveAt j (A.liftedMap w) ∧ H.IsActiveAt k (A.liftedMap w)} := by
  ext w
  constructor
  · rintro ⟨⟨hw, hj⟩, -, hk⟩
    exact ⟨hw, hj, hk⟩
  · rintro ⟨hw, hj, hk⟩
    exact ⟨⟨hw, hj⟩, ⟨hw, hk⟩⟩

end FiniteHalfspacePresentation

end CompactConvexProjection
end AffineTverberg
