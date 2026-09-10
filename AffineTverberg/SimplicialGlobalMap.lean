import AffineTverberg.SimplicialDeletedJoinModel
import Mathlib.Topology.LocallyFinite

set_option linter.style.header false

/-!
# The global piecewise-affine Sarkaria map on a simplicial deleted join

For a simplicial ball the map in the paper is affine on every join cell, but
need not be the restriction of one linear map on the whole Cayley ambient
space.  This file therefore defines it intrinsically on the concrete deleted
join.

For a Cayley component `(u,t)` with `t > 0`, the represented point of `K` is
`t⁻¹ • u`, and its contribution is `t • (φ(t⁻¹ • u),1)`.  When `t = 0`, the
contribution is zero.  Membership in the deleted join guarantees that the
normalized point belongs to `K.space` and that these are the only two cases.

The central compatibility theorem proves that, on every deleted-join cell,
this global definition agrees with the linear map obtained from any ambient
affine representatives of `φ` on the component faces.  Consequently a zero
of the global map gives exactly the witness-level zero required by
`simplicialBallZeroTheoremStatement`.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg

/-- The concrete simplicial deleted join as a topological subtype. -/
abbrev SimplicialDeletedJoinSpace {e : ℕ} (n : ℕ)
    (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)) (m : ℕ) :=
  simplicialDeletedJoinCarrier n K m

section ComponentGeometry

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- Every Cayley component of a point in the simplicial deleted join has a
nonnegative homogenizing coordinate. -/
theorem simplicialDeletedJoin_component_snd_nonnegative
    {z : PolytopalJoinAmbient e m}
    (hz : z ∈ simplicialDeletedJoinCarrier n K m) (i : Fin (m + 1)) :
    0 ≤ (z i).2 := by
  obtain ⟨f, _hf, hzf⟩ := (mem_simplicialDeletedJoinCarrier_iff K z).mp hz
  obtain ⟨t, x, ht0, _ht1, _hx, hrepr⟩ := exists_repr_of_mem_joinCellCarrier hzf
  have hi := congrFun hrepr i
  rw [sum_smul_copy_apply] at hi
  rw [hi]
  exact ht0 i

/-- A zero-weight Cayley component of a deleted-join point is the zero
vector in the spatial coordinate. -/
theorem simplicialDeletedJoin_component_fst_eq_zero_of_snd_eq_zero
    {z : PolytopalJoinAmbient e m}
    (hz : z ∈ simplicialDeletedJoinCarrier n K m) (i : Fin (m + 1))
    (hi : (z i).2 = 0) : (z i).1 = 0 := by
  obtain ⟨f, _hf, hzf⟩ := (mem_simplicialDeletedJoinCarrier_iff K z).mp hz
  obtain ⟨t, x, ht0, _ht1, _hx, hrepr⟩ := exists_repr_of_mem_joinCellCarrier hzf
  have hcoord := congrFun hrepr i
  rw [sum_smul_copy_apply] at hcoord
  have hti : t i = 0 := by simpa [hcoord] using hi
  rw [hcoord, hti, zero_smul]

/-- On a specified join cell, normalizing a positive-weight component lands
in the corresponding component face. -/
theorem normalized_component_mem_face_of_mem_joinCellCarrier
    {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    {z : PolytopalJoinAmbient e m} (hz : z ∈ joinCellCarrier f)
    (i : Fin (m + 1)) (hi : 0 < (z i).2) :
    (z i).2⁻¹ • (z i).1 ∈
      convexHull ℝ (f i : Set (CoordinateSpace e)) := by
  obtain ⟨t, x, _ht0, _ht1, hx, hrepr⟩ := exists_repr_of_mem_joinCellCarrier hz
  have hcoord := congrFun hrepr i
  rw [sum_smul_copy_apply] at hcoord
  have hti : 0 < t i := by simpa [hcoord] using hi
  rw [hcoord]
  change (t i)⁻¹ • (t i • x i) ∈
    convexHull ℝ (f i : Set (CoordinateSpace e))
  rw [smul_smul]
  rw [inv_mul_cancel₀ hti.ne', one_smul]
  exact hx i hti

/-- Normalizing a positive-weight component of a deleted-join point produces
a point of the realization of `K`. -/
theorem normalized_component_mem_space
    {z : PolytopalJoinAmbient e m}
    (hz : z ∈ simplicialDeletedJoinCarrier n K m)
    (i : Fin (m + 1)) (hi : 0 < (z i).2) :
    (z i).2⁻¹ • (z i).1 ∈ K.space := by
  obtain ⟨f, hf, hzf⟩ := (mem_simplicialDeletedJoinCarrier_iff K z).mp hz
  have hface := normalized_component_mem_face_of_mem_joinCellCarrier hzf i hi
  rcases hf.1 i with hempty | hboundary
  · rw [hempty] at hface
    simp at hface
  · exact convexHull_subset_space hboundary.1 hface

end ComponentGeometry

section Definition

variable {e n d m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- The normalized point represented by the `i`-th positive-weight Cayley
component. -/
def simplicialNormalizedPoint
    (z : SimplicialDeletedJoinSpace n K m) (i : Fin (m + 1))
    (hi : 0 < (z.val i).2) : K.space :=
  ⟨(z.val i).2⁻¹ • (z.val i).1,
    normalized_component_mem_space z.property i hi⟩

/-- The weighted homogenized image contributed by one Cayley component. -/
def simplicialWeightedComponent
    (φ : K.space → CoordinateSpace d)
    (z : SimplicialDeletedJoinSpace n K m) (i : Fin (m + 1)) :
    CoordinateSpace d × ℝ :=
  if hi : 0 < (z.val i).2 then
    (z.val i).2 • homogenize (φ (simplicialNormalizedPoint z i hi))
  else 0

/-- The genuine global Sarkaria map on the concrete simplicial deleted join.
It is cellwise linear, though generally not the restriction of one ambient
linear map. -/
def simplicialGlobalSarkariaMap
    (φ : K.space → CoordinateSpace d) :
    SimplicialDeletedJoinSpace n K m → SarkariaTarget d m :=
  fun z ↦ sarkariaMap fun i ↦ simplicialWeightedComponent φ z i

end Definition

section CellwiseCompatibility

variable {e n d m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- A positive-weight component is its weight times its normalized point. -/
theorem component_eq_smul_normalized
    (z : SimplicialDeletedJoinSpace n K m) (i : Fin (m + 1))
    (hi : 0 < (z.val i).2) :
    z.val i =
      ((z.val i).2 • (simplicialNormalizedPoint z i hi).val, (z.val i).2) := by
  apply Prod.ext
  · change (z.val i).1 =
      (z.val i).2 • ((z.val i).2⁻¹ • (z.val i).1)
    rw [smul_smul, mul_inv_cancel₀ hi.ne', one_smul]
  · rfl

/-- On a zero-weight component, both the global weighted contribution and
every homogenized affine-linear representative vanish. -/
theorem component_eq_zero_of_not_pos
    (z : SimplicialDeletedJoinSpace n K m) (i : Fin (m + 1))
    (hi : ¬ 0 < (z.val i).2) : z.val i = 0 := by
  have hnonneg := simplicialDeletedJoin_component_snd_nonnegative z.property i
  have hsnd : (z.val i).2 = 0 := le_antisymm (not_lt.mp hi) hnonneg
  apply Prod.ext
  · simpa [hsnd] using
      simplicialDeletedJoin_component_fst_eq_zero_of_snd_eq_zero z.property i hsnd
  · simpa using hsnd

/-- On a deleted-join cell, the global weighted component agrees with any
ambient affine representative of `φ` on that component face. -/
theorem simplicialWeightedComponent_eq_homogenizedAffineLinear
    (φ : K.space → CoordinateSpace d)
    (z : SimplicialDeletedJoinSpace n K m)
    {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hzf : z.val ∈ joinCellCarrier f)
    (ψ : Fin (m + 1) → CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ i, ∀ y : K.space,
      y.val ∈ convexHull ℝ (f i : Set (CoordinateSpace e)) →
        φ y = ψ i y.val)
    (i : Fin (m + 1)) :
    simplicialWeightedComponent φ z i =
      homogenizedAffineLinear (ψ i) (z.val i) := by
  by_cases hi : 0 < (z.val i).2
  · rw [simplicialWeightedComponent, dite_eq_left hi,
      component_eq_smul_normalized z i hi,
      homogenizedAffineLinear_smul_homogenize]
    congr 2
    exact hψ i (simplicialNormalizedPoint z i hi)
      (normalized_component_mem_face_of_mem_joinCellCarrier hzf i hi)
  · rw [simplicialWeightedComponent, dite_eq_right hi,
      component_eq_zero_of_not_pos z i hi, map_zero]

/-- The global map is exactly the cellwise linear Sarkaria map on every
deleted-join cell.  This is the coherence statement which makes the global
piecewise definition independent of all choices of affine representatives. -/
theorem simplicialGlobalSarkariaMap_eq_cellwise
    (φ : K.space → CoordinateSpace d)
    (z : SimplicialDeletedJoinSpace n K m)
    {f : Fin (m + 1) → Finset (CoordinateSpace e)}
    (hzf : z.val ∈ joinCellCarrier f)
    (ψ : Fin (m + 1) → CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ i, ∀ y : K.space,
      y.val ∈ convexHull ℝ (f i : Set (CoordinateSpace e)) →
        φ y = ψ i y.val) :
    simplicialGlobalSarkariaMap φ z = simplicialSarkariaLinear ψ z.val := by
  rw [simplicialGlobalSarkariaMap, simplicialSarkariaLinear_apply]
  congr 1
  funext i
  exact simplicialWeightedComponent_eq_homogenizedAffineLinear
    φ z hzf ψ hψ i

/-- A zero of the genuine global map on the concrete deleted join produces
the represented zero required by the simplicial zero theorem. -/
theorem exists_sarkariaValue_eq_zero_of_globalMap_eq_zero
    (φ : K.space → CoordinateSpace d)
    (hφ : IsAffineOnSimplicialFaces K φ)
    (z : SimplicialDeletedJoinSpace n K m)
    (hzero : simplicialGlobalSarkariaMap φ z = 0) :
    ∃ w : SimplicialDeletedJoinPoint (n := n) (m := m) K,
      SimplicialDeletedJoinPoint.sarkariaValue K w φ = 0 := by
  obtain ⟨f, hf, hzf⟩ :=
    (mem_simplicialDeletedJoinCarrier_iff K z.val).mp z.property
  obtain ⟨ψ, hψ⟩ := exists_cellwise_affine_extension hφ hf
  apply exists_sarkariaValue_eq_zero_of_simplicialSarkariaLinear_eq_zero
    hf hψ hzf
  rw [← simplicialGlobalSarkariaMap_eq_cellwise φ z hzf ψ hψ]
  exact hzero

end CellwiseCompatibility

section Continuity

variable {e n d m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- The finite indexing type for the closed cells of the concrete simplicial
deleted join.  It is kept local to the global-map construction so that this
file does not depend on any later incidence-space definitions. -/
abbrev SimplicialDeletedCellIndex
    (n : ℕ) (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)) (m : ℕ) :=
  {f : Fin (m + 1) → Finset (CoordinateSpace e) // IsBoundaryDeletedJoinCell n K f}

/-- A deleted-join cell, regarded as a closed subset of the concrete deleted
join rather than of its ambient vector space. -/
def simplicialDeletedJoinCellSet
    (F : SimplicialDeletedCellIndex n K m) :
    Set (SimplicialDeletedJoinSpace n K m) :=
  {z | z.val ∈ joinCellCarrier F.val}

theorem simplicialDeletedJoinCellSet_isClosed
    (F : SimplicialDeletedCellIndex n K m) :
    IsClosed (simplicialDeletedJoinCellSet F) := by
  exact (joinCellCarrier_isClosed F.val).preimage continuous_subtype_val

/-- The closed cell subsets cover the concrete deleted join. -/
theorem iUnion_simplicialDeletedJoinCellSet :
    ⋃ F : SimplicialDeletedCellIndex n K m,
      simplicialDeletedJoinCellSet F = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨f, hf, hzf⟩ :=
    (mem_simplicialDeletedJoinCarrier_iff K z.val).mp z.property
  exact Set.mem_iUnion.mpr ⟨⟨f, hf⟩, hzf⟩

/-- On each closed cell, the global Sarkaria map is continuous because it is
the restriction of the corresponding ambient linear Sarkaria map. -/
theorem continuousOn_simplicialGlobalSarkariaMap_cell
    (φ : K.space → CoordinateSpace d)
    (hφ : IsAffineOnSimplicialFaces K φ)
    (F : SimplicialDeletedCellIndex n K m) :
    ContinuousOn (simplicialGlobalSarkariaMap φ)
      (simplicialDeletedJoinCellSet F) := by
  obtain ⟨ψ, hψ⟩ := exists_cellwise_affine_extension hφ F.property
  have hcontinuous : Continuous
      (fun z : SimplicialDeletedJoinSpace n K m ↦
        simplicialSarkariaLinear ψ z.val) :=
    (simplicialSarkariaLinear ψ).toContinuousLinearMap.continuous.comp
      continuous_subtype_val
  apply hcontinuous.continuousOn.congr
  intro z hz
  exact simplicialGlobalSarkariaMap_eq_cellwise φ z hz ψ hψ

/-- The genuine piecewise-affine Sarkaria map is globally continuous.  The
proof is finite closed pasting over all deleted-join cells. -/
theorem continuous_simplicialGlobalSarkariaMap
    (φ : K.space → CoordinateSpace d)
    (hfin : K.faces.Finite)
    (hφ : IsAffineOnSimplicialFaces K φ) :
    Continuous (simplicialGlobalSarkariaMap (n := n) (m := m) φ) := by
  let : Fintype (SimplicialDeletedCellIndex n K m) :=
    Set.Finite.fintype (boundaryDeletedJoinCells_finite (n := n) (m := m) K hfin)
  apply (locallyFinite_of_finite
    (fun F : SimplicialDeletedCellIndex n K m ↦
      simplicialDeletedJoinCellSet F)).continuous
      iUnion_simplicialDeletedJoinCellSet
      simplicialDeletedJoinCellSet_isClosed
  intro F
  exact continuousOn_simplicialGlobalSarkariaMap_cell φ hφ F

/-- The global Sarkaria map bundled as a continuous map. -/
def simplicialGlobalSarkariaContinuousMap
    (φ : K.space → CoordinateSpace d)
    (hfin : K.faces.Finite)
    (hφ : IsAffineOnSimplicialFaces K φ) :
    C(SimplicialDeletedJoinSpace n K m, SarkariaTarget d m) :=
  ⟨simplicialGlobalSarkariaMap φ,
    continuous_simplicialGlobalSarkariaMap φ hfin hφ⟩

end Continuity

end AffineTverberg
