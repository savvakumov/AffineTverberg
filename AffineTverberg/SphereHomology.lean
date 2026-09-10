import AffineTverberg.SimplexBoundaryHomology
import AffineTverberg.PolytopalBoundaryTopology

set_option linter.style.header false

/-!
# Nonzero top homology of the actual norm sphere

Barycentric coordinates identify the boundary of an affine basis simplex
with the frontier of its convex hull. A gauge homeomorphism takes this
frontier to the unit sphere. The explicit nonbounding simplex-boundary
cycle therefore gives a nonzero class in genuine singular homology.
-/

noncomputable section

open Set Metric CategoryTheory CategoryTheory.Limits
open scoped BigOperators

namespace AffineTverberg.Simplicial

section Geometry

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem mem_barycentricBoundary_univ_iff (x : V → ℝ) :
    x ∈ barycentricCarrier (boundaryFamily (Finset.univ : Finset V)) ↔
      (∀ v, 0 ≤ x v) ∧ (∑ v, x v) = 1 ∧ ∃ v, x v = 0 := by
  constructor
  · rintro ⟨h0, h1, s, hs, hxs⟩
    obtain ⟨_, hne⟩ := mem_boundaryFamily.mp hs
    have hnot : ∃ v, v ∉ s := by
      by_contra! h
      exact hne (Finset.eq_univ_of_forall h)
    obtain ⟨v, hv⟩ := hnot
    exact ⟨h0, h1, v, hxs v hv⟩
  · rintro ⟨h0, h1, v, hv⟩
    refine ⟨h0, h1, Finset.univ.erase v,
      mem_boundaryFamily.mpr ⟨Finset.erase_subset _ _, ?_⟩, ?_⟩
    · exact Finset.erase_ne_self.mpr (Finset.mem_univ v)
    · intro w hw
      have hwv : w = v := by simpa using hw
      simpa [hwv] using hv

omit [DecidableEq V] [FiniteDimensional ℝ E] in
theorem affineBasis_coord_evaluation (b : AffineBasis V ℝ E)
    {x : V → ℝ} (hx : ∑ v, x v = 1) (v : V) :
    b.coord v (barycentricEvaluation b x) = x v := by
  change b.coord v (∑ i, x i • b i) = x v
  rw [← Finset.univ.affineCombination_eq_linear_combination b x hx]
  exact b.coord_apply_combination_of_mem (Finset.mem_univ v) hx

omit [Fintype V] [DecidableEq V] [FiniteDimensional ℝ E] in
theorem affineBasis_mem_frontier_iff [Finite V] (b : AffineBasis V ℝ E) (x : E) :
    x ∈ frontier (convexHull ℝ (range b)) ↔
      (∀ v, 0 ≤ b.coord v x) ∧ ∃ v, b.coord v x = 0 := by
  have hc := (Set.finite_range b).isCompact_convexHull ℝ
  rw [frontier, hc.isClosed.closure_eq, mem_sdiff,
    b.interior_convexHull, b.convexHull_eq_nonneg_coord]
  change ((∀ v, 0 ≤ b.coord v x) ∧ ¬ ∀ v, 0 < b.coord v x) ↔ _
  constructor
  · rintro ⟨h0, hn⟩
    push Not at hn
    obtain ⟨v, hv⟩ := hn
    exact ⟨h0, v, le_antisymm hv (h0 v)⟩
  · rintro ⟨h0, v, hv⟩
    exact ⟨h0, fun hp ↦ (ne_of_gt (hp v)) hv⟩

omit [FiniteDimensional ℝ E] in
theorem affineBasis_evaluation_mem_frontier (b : AffineBasis V ℝ E)
    {x : V → ℝ}
    (hx : x ∈ barycentricCarrier (boundaryFamily (Finset.univ : Finset V))) :
    barycentricEvaluation b x ∈ frontier (convexHull ℝ (range b)) := by
  obtain ⟨h0, h1, v, hv⟩ := (mem_barycentricBoundary_univ_iff x).mp hx
  apply (affineBasis_mem_frontier_iff b _).mpr
  refine ⟨fun w ↦ ?_, v, ?_⟩
  · rw [affineBasis_coord_evaluation b h1]
    exact h0 w
  · rw [affineBasis_coord_evaluation b h1]
    exact hv

omit [FiniteDimensional ℝ E] in
theorem affineBasis_coords_mem_boundary (b : AffineBasis V ℝ E)
    {x : E} (hx : x ∈ frontier (convexHull ℝ (range b))) :
    (fun v ↦ b.coord v x) ∈
      barycentricCarrier (boundaryFamily (Finset.univ : Finset V)) := by
  obtain ⟨h0, hz⟩ := (affineBasis_mem_frontier_iff b x).mp hx
  exact (mem_barycentricBoundary_univ_iff _).mpr
    ⟨h0, b.sum_coord_apply_eq_one x, hz⟩

/-- The actual boundary realization, not merely an abstract sphere model,
is the frontier of the affine simplex. -/
def affineBasisBoundaryHomeomorph (b : AffineBasis V ℝ E) :
    barycentricCarrier (boundaryFamily (Finset.univ : Finset V)) ≃ₜ
      frontier (convexHull ℝ (range b)) where
  toFun x := ⟨barycentricEvaluation b x, affineBasis_evaluation_mem_frontier b x.2⟩
  invFun x := ⟨fun v ↦ b.coord v x, affineBasis_coords_mem_boundary b x.2⟩
  left_inv x := by
    apply Subtype.ext
    funext v
    exact affineBasis_coord_evaluation b x.2.2.1 v
  right_inv x := by
    apply Subtype.ext
    exact b.linear_combination_coord_eq_self x
  continuous_toFun :=
    ((continuous_barycentricEvaluation b).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    (continuous_pi fun v ↦
      (continuous_barycentric_coord b v).comp continuous_subtype_val).subtype_mk _

omit [Fintype V] [DecidableEq V] in
theorem affineBasis_exists_frontier_sphere_homeomorph [Finite V] (b : AffineBasis V ℝ E) :
    ∃ h : E ≃ₜ E, h '' frontier (convexHull ℝ (range b)) = sphere 0 1 := by
  have hc := (Set.finite_range b).isCompact_convexHull ℝ
  have hint : (interior (convexHull ℝ (range b))).Nonempty := by
    apply (convex_convexHull ℝ (range b)).interior_nonempty_iff_affineSpan_eq_top.mpr
    rw [affineSpan_convexHull]
    exact b.tot
  obtain ⟨h, _, _, hs⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (convex_convexHull ℝ (range b)) hint hc.isBounded
  exact ⟨h, hs⟩

/-- A simplex boundary on an affine basis is homeomorphic to the unit sphere
in the ambient vector space, for any norm on that space. -/
def affineBasisBoundarySphereHomeomorph (b : AffineBasis V ℝ E) :
    barycentricCarrier (boundaryFamily (Finset.univ : Finset V)) ≃ₜ
      sphere (0 : E) 1 :=
  (affineBasisBoundaryHomeomorph b).trans
    (((affineBasis_exists_frontier_sphere_homeomorph b).choose.image _).trans
      (Homeomorph.setCongr (affineBasis_exists_frontier_sphere_homeomorph b).choose_spec))

end Geometry

section Homology

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The top positive-degree homology of a norm sphere is nonzero. -/
theorem nontrivial_singularHomology_sphere {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 2) :
    Nontrivial ((realSingularHomology (n + 1)).obj
      (TopCat.of (sphere (0 : E) 1))) := by
  obtain ⟨b⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional
    (ι := Fin (n + 3)) (k := ℝ) (V := E) (P := E) (by simp [hdim])
  have hn := nontrivial_singularHomology_boundaryFamily
    (s := (Finset.univ : Finset (Fin (n + 3)))) (n := n) (by simp)
  have hn' : Nontrivial ((realSingularHomology (n + 1)).obj (TopCat.of
      (barycentricCarrier (boundaryFamily (Finset.univ : Finset (Fin (n + 3))))))) := hn
  apply not_subsingleton_iff_nontrivial.mp
  intro hz
  have hs := (realSingularHomology_subsingleton_iff_of_homotopyEquiv
    (affineBasisBoundarySphereHomeomorph b).toHomotopyEquiv (n + 1)).mpr hz
  exact not_subsingleton _ hs

end Homology

end AffineTverberg.Simplicial
