import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Topology.Order.Compact

set_option linter.style.header false

/-!
# Upper envelopes of compact convex projections

This file formalizes the construction in lines 551--569 and 600--607 of
`affine-tverberg17.tex`.  From a compact convex set `Q` and two linear
coordinates `π` and `height`, it constructs the fiberwise maximum `h`, the
lifted image `R`, and its top locus `Γ`.  The maximum is attained on every
fiber, `h` is concave, and `Γ` projects onto the whole base.
-/

noncomputable section

open Set

namespace AffineTverberg

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The abstract data behind the polytope `R_y = (π, λ_y)(Q)`. -/
structure CompactConvexProjection where
  carrier : Set E
  carrier_compact : IsCompact carrier
  carrier_convex : Convex ℝ carrier
  projection : E →L[ℝ] F
  height : E →L[ℝ] ℝ

namespace CompactConvexProjection

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (A : CompactConvexProjection E F)

/-- The projected base `P = π(Q)`. -/
def base : Set F := A.projection '' A.carrier

/-- The part of `Q` lying over a base point. -/
def fiber (x : F) : Set E :=
  A.carrier ∩ A.projection ⁻¹' ({x} : Set F)

theorem fiber_nonempty {x : F} (hx : x ∈ A.base) : (A.fiber x).Nonempty := by
  obtain ⟨w, hw, rfl⟩ := hx
  exact ⟨w, hw, by simp⟩

theorem fiber_compact (x : F) : IsCompact (A.fiber x) :=
  A.carrier_compact.inter_right
    (isClosed_singleton.preimage A.projection.continuous)

/-- A chosen point at which `height` is maximal on the fiber over `x`. -/
noncomputable def fiberArgmax (x : A.base) : E :=
  Classical.choose
    ((A.fiber_compact x).exists_isMaxOn (A.fiber_nonempty x.property)
      A.height.continuous.continuousOn)

theorem fiberArgmax_mem (x : A.base) : A.fiber x (A.fiberArgmax x) :=
  (Classical.choose_spec
    ((A.fiber_compact x).exists_isMaxOn (A.fiber_nonempty x.property)
      A.height.continuous.continuousOn)).1

theorem fiberArgmax_isMaxOn (x : A.base) :
    IsMaxOn A.height (A.fiber x) (A.fiberArgmax x) :=
  (Classical.choose_spec
    ((A.fiber_compact x).exists_isMaxOn (A.fiber_nonempty x.property)
      A.height.continuous.continuousOn)).2

theorem fiberArgmax_mem_carrier (x : A.base) : A.fiberArgmax x ∈ A.carrier :=
  (A.fiberArgmax_mem x).1

@[simp]
theorem projection_fiberArgmax (x : A.base) : A.projection (A.fiberArgmax x) = x := by
  simpa using (A.fiberArgmax_mem x).2

/-- The fiberwise upper-envelope function `h`.  Its value away from the
projected base is immaterial. -/
noncomputable def upperEnvelope (x : F) : ℝ :=
  by
    classical
    exact if hx : x ∈ A.base then A.height (A.fiberArgmax ⟨x, hx⟩) else 0

theorem upperEnvelope_eq (x : F) (hx : x ∈ A.base) :
    A.upperEnvelope x = A.height (A.fiberArgmax ⟨x, hx⟩) := by
  simp [upperEnvelope, hx]

/-- Every point of `Q` lies at or below the upper envelope over its
projection. -/
theorem height_le_upperEnvelope {w : E} (hw : w ∈ A.carrier) :
    A.height w ≤ A.upperEnvelope (A.projection w) := by
  have hx : A.projection w ∈ A.base := ⟨w, hw, rfl⟩
  have hwfiber : w ∈ A.fiber (A.projection w) := ⟨hw, by simp⟩
  have hmax := A.fiberArgmax_isMaxOn ⟨A.projection w, hx⟩ hwfiber
  simpa [A.upperEnvelope_eq (A.projection w) hx] using hmax

/-- The upper-envelope value on each base fiber is attained. -/
theorem exists_height_eq_upperEnvelope {x : F} (hx : x ∈ A.base) :
    ∃ w ∈ A.carrier,
      A.projection w = x ∧ A.height w = A.upperEnvelope x := by
  refine ⟨A.fiberArgmax ⟨x, hx⟩, A.fiberArgmax_mem_carrier ⟨x, hx⟩, ?_, ?_⟩
  · exact A.projection_fiberArgmax ⟨x, hx⟩
  · exact (A.upperEnvelope_eq x hx).symm

/-- The combined linear map `(π, height)`. -/
def liftedMap : E →L[ℝ] F × ℝ :=
  A.projection.prod A.height

/-- The set `R = (π, height)(Q)`. -/
def liftedImage : Set (F × ℝ) :=
  A.liftedMap '' A.carrier

theorem liftedImage_compact : IsCompact A.liftedImage :=
  A.carrier_compact.image A.liftedMap.continuous

theorem liftedImage_convex : Convex ℝ A.liftedImage :=
  A.carrier_convex.linear_image A.liftedMap.toLinearMap

/-- The graph `Γ` of the upper envelope over the projected base. -/
def topGraph : Set (F × ℝ) :=
  {p | p.1 ∈ A.base ∧ p.2 = A.upperEnvelope p.1}

/-- The points of `Q` which map to the top graph. -/
def topLocus : Set E :=
  {w | w ∈ A.carrier ∧ A.height w = A.upperEnvelope (A.projection w)}

theorem topGraph_subset_liftedImage : A.topGraph ⊆ A.liftedImage := by
  intro p hp
  change p.1 ∈ A.base ∧ p.2 = A.upperEnvelope p.1 at hp
  obtain ⟨w, hw, hπ, hh⟩ := A.exists_height_eq_upperEnvelope hp.1
  refine ⟨w, hw, ?_⟩
  apply Prod.ext
  · simpa [liftedMap] using hπ
  · change A.height w = p.2
    exact hh.trans hp.2.symm

/-- Intrinsic characterization of the top of `R`: a point is on `Γ` exactly
when no point of `R` with the same first coordinate lies above it. -/
theorem mem_topGraph_iff (p : F × ℝ) :
    p ∈ A.topGraph ↔
      p ∈ A.liftedImage ∧
        ∀ q ∈ A.liftedImage, q.1 = p.1 → q.2 ≤ p.2 := by
  constructor
  · intro hp
    have hpImage := A.topGraph_subset_liftedImage hp
    change p.1 ∈ A.base ∧ p.2 = A.upperEnvelope p.1 at hp
    obtain ⟨_hpbase, hpheight⟩ := hp
    refine ⟨hpImage, ?_⟩
    rintro q ⟨w, hw, rfl⟩ hπ
    change A.height w ≤ p.2
    calc
      A.height w ≤ A.upperEnvelope (A.projection w) := A.height_le_upperEnvelope hw
      _ = A.upperEnvelope p.1 :=
        congrArg A.upperEnvelope (by simpa [liftedMap] using hπ)
      _ = p.2 := hpheight.symm
  · rintro ⟨hp, htop⟩
    obtain ⟨w, hw, rfl⟩ := hp
    have hx : A.projection w ∈ A.base := ⟨w, hw, rfl⟩
    obtain ⟨v, hv, hπ, hh⟩ := A.exists_height_eq_upperEnvelope hx
    have hvImage : A.liftedMap v ∈ A.liftedImage := ⟨v, hv, rfl⟩
    have hupper_le : A.upperEnvelope (A.projection w) ≤ A.height w := by
      rw [← hh]
      exact htop (A.liftedMap v) hvImage (by simpa [liftedMap] using hπ)
    have hw_le := A.height_le_upperEnvelope hw
    change A.projection w ∈ A.base ∧
      A.height w = A.upperEnvelope (A.projection w)
    exact ⟨hx, le_antisymm hw_le hupper_le⟩

/-- A point of `Q` belongs to the top locus exactly when it maximizes height
among all points with the same projection. -/
theorem mem_topLocus_iff {w : E} :
    w ∈ A.topLocus ↔
      w ∈ A.carrier ∧
        ∀ v ∈ A.carrier, A.projection v = A.projection w → A.height v ≤ A.height w := by
  constructor
  · rintro ⟨hw, hh⟩
    refine ⟨hw, ?_⟩
    intro v hv hπ
    calc
      A.height v ≤ A.upperEnvelope (A.projection v) := A.height_le_upperEnvelope hv
      _ = A.upperEnvelope (A.projection w) := congrArg A.upperEnvelope hπ
      _ = A.height w := hh.symm
  · rintro ⟨hw, hmax⟩
    have hx : A.projection w ∈ A.base := ⟨w, hw, rfl⟩
    obtain ⟨v, hv, hπ, hh⟩ := A.exists_height_eq_upperEnvelope hx
    refine ⟨hw, le_antisymm (A.height_le_upperEnvelope hw) ?_⟩
    rw [← hh]
    exact hmax v hv hπ

/-- The top locus projects onto the whole base.  This is the abstract
surjectivity assertion for the fibers `Y_y`. -/
theorem topLocus_projection_surjective :
    ∀ x ∈ A.base, ∃ w ∈ A.topLocus, A.projection w = x := by
  intro x hx
  obtain ⟨w, hw, hπ, hh⟩ := A.exists_height_eq_upperEnvelope hx
  exact ⟨w, ⟨hw, by rw [hπ]; exact hh⟩, hπ⟩

/-- The top graph is exactly the lifted image of the top locus. -/
theorem liftedMap_image_topLocus :
    A.liftedMap '' A.topLocus = A.topGraph := by
  apply Subset.antisymm
  · rintro p ⟨w, hw, rfl⟩
    change A.projection w ∈ A.base ∧
      A.height w = A.upperEnvelope (A.projection w)
    exact ⟨⟨w, hw.1, rfl⟩, hw.2⟩
  · intro p hp
    obtain ⟨w, hw, hwp⟩ := A.topGraph_subset_liftedImage hp
    refine ⟨w, ?_, hwp⟩
    change w ∈ A.carrier ∧
      A.height w = A.upperEnvelope (A.projection w)
    have hp' := hp
    change p.1 ∈ A.base ∧ p.2 = A.upperEnvelope p.1 at hp'
    rw [← hwp] at hp'
    exact ⟨hw, hp'.2⟩

/-- The fiberwise maximum of a linear height over a compact convex set is
concave on the projected base. -/
theorem upperEnvelope_concaveOn : ConcaveOn ℝ A.base A.upperEnvelope := by
  refine ⟨A.carrier_convex.linear_image A.projection.toLinearMap, ?_⟩
  intro x hx y hy a b ha hb hab
  let x' : A.base := ⟨x, hx⟩
  let y' : A.base := ⟨y, hy⟩
  let w : E := a • A.fiberArgmax x' + b • A.fiberArgmax y'
  have hw : w ∈ A.carrier :=
    A.carrier_convex (A.fiberArgmax_mem_carrier x')
      (A.fiberArgmax_mem_carrier y') ha hb hab
  calc
    a • A.upperEnvelope x + b • A.upperEnvelope y = A.height w := by
      change a • A.upperEnvelope x'.1 + b • A.upperEnvelope y'.1 = A.height w
      rw [A.upperEnvelope_eq x'.1 x'.2, A.upperEnvelope_eq y'.1 y'.2]
      simp [w]
    _ ≤ A.upperEnvelope (A.projection w) := A.height_le_upperEnvelope hw
    _ = A.upperEnvelope (a • x + b • y) := by
      congr 1
      simp [w, x', y']

end CompactConvexProjection

end AffineTverberg
