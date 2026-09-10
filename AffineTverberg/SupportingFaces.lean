import AffineTverberg.SimplicialFiber
import AffineTverberg.UpperEnvelope
import Mathlib.Analysis.Convex.Exposed

set_option linter.style.header false

/-!
# Supporting faces of the upper envelope

This file formalizes the supporting-face argument in lines 609--676 and the
nonnegativity argument in lines 728--742 of `affine-tverberg17.tex`.  An
affine upper support is represented by a continuous linear slope and an
intercept.  Its contact set is an exposed face of `Q`, lies in the top locus,
and is nonnegative whenever the diagonal relation supplies a nonnegative
point in every projection fiber.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg
namespace CompactConvexProjection

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- An affine function on the base which majorizes `height` on `Q` and is
tight somewhere.  This is the function `γ` in the definition of `S_F` in
the paper. -/
structure UpperSupportCertificate (A : CompactConvexProjection E F) where
  slope : F →L[ℝ] ℝ
  intercept : ℝ
  upper_bound : ∀ w ∈ A.carrier,
    A.height w ≤ slope (A.projection w) + intercept
  contact_nonempty : ∃ w ∈ A.carrier,
    A.height w = slope (A.projection w) + intercept

namespace UpperSupportCertificate

variable {A : CompactConvexProjection E F} (c : UpperSupportCertificate A)

/-- Evaluation of the affine upper-support function. -/
def eval (x : F) : ℝ := c.slope x + c.intercept

/-- The face on which the upper-support inequality is an equality. -/
def contactSet : Set E :=
  {w | w ∈ A.carrier ∧ A.height w = c.eval (A.projection w)}

theorem contactSet_nonempty : c.contactSet.Nonempty := by
  obtain ⟨w, hw, heq⟩ := c.contact_nonempty
  exact ⟨w, hw, heq⟩

/-- The linear functional whose maximum cuts out the contact face. -/
def exposingFunctional : StrongDual ℝ E :=
  A.height - c.slope.comp A.projection

theorem exposingFunctional_le_intercept {w : E} (hw : w ∈ A.carrier) :
    c.exposingFunctional w ≤ c.intercept := by
  have h := c.upper_bound w hw
  change A.height w - c.slope (A.projection w) ≤ c.intercept
  linarith

theorem exposingFunctional_eq_intercept {w : E} (hw : w ∈ c.contactSet) :
    c.exposingFunctional w = c.intercept := by
  change A.height w - c.slope (A.projection w) = c.intercept
  change w ∈ A.carrier ∧
    A.height w = c.slope (A.projection w) + c.intercept at hw
  linarith [hw.2]

/-- The contact set is exactly the maximizer set of its exposing linear
functional. -/
theorem contactSet_eq_toExposed :
    c.contactSet = c.exposingFunctional.toExposed A.carrier := by
  ext w
  constructor
  · intro hw
    refine ⟨hw.1, ?_⟩
    intro v hv
    calc
      c.exposingFunctional v ≤ c.intercept :=
        c.exposingFunctional_le_intercept hv
      _ = c.exposingFunctional w :=
        (c.exposingFunctional_eq_intercept hw).symm
  · rintro ⟨hw, hmax⟩
    obtain ⟨z, hz⟩ := c.contactSet_nonempty
    have hintercept_le : c.intercept ≤ c.exposingFunctional w := by
      rw [← c.exposingFunctional_eq_intercept hz]
      exact hmax z hz.1
    have heq : c.exposingFunctional w = c.intercept :=
      le_antisymm (c.exposingFunctional_le_intercept hw) hintercept_le
    refine ⟨hw, ?_⟩
    change A.height w = c.slope (A.projection w) + c.intercept
    change A.height w - c.slope (A.projection w) = c.intercept at heq
    linarith

/-- Every support contact set is an exposed face of `Q`. -/
theorem contactSet_isExposed : IsExposed ℝ A.carrier c.contactSet := by
  rw [c.contactSet_eq_toExposed]
  exact ContinuousLinearMap.toExposed.isExposed

theorem contactSet_compact : IsCompact c.contactSet :=
  c.contactSet_isExposed.isCompact A.carrier_compact

theorem contactSet_convex : Convex ℝ c.contactSet :=
  c.contactSet_isExposed.convex A.carrier_convex

/-- Equality with an affine upper support forces fiberwise maximality. -/
theorem contactSet_subset_topLocus : c.contactSet ⊆ A.topLocus := by
  intro w hw
  rw [A.mem_topLocus_iff]
  refine ⟨hw.1, ?_⟩
  intro v hv hπ
  calc
    A.height v ≤ c.eval (A.projection v) := c.upper_bound v hv
    _ = c.eval (A.projection w) := congrArg c.eval hπ
    _ = A.height w := hw.2.symm

/-- The lifted image of a support contact point lies on `Γ`. -/
theorem liftedMap_mem_topGraph {w : E} (hw : w ∈ c.contactSet) :
    A.liftedMap w ∈ A.topGraph := by
  have htop := c.contactSet_subset_topLocus hw
  change A.projection w ∈ A.base ∧
    A.height w = A.upperEnvelope (A.projection w)
  exact ⟨⟨w, hw.1, rfl⟩, htop.2⟩

/-- If a point in the same projection fiber has nonnegative height, every
point of a support contact face above that fiber also has nonnegative
height. -/
theorem height_nonnegative_of_fiber_witness {z : E} (hz : z ∈ c.contactSet)
    {w : E} (hw : w ∈ A.carrier)
    (hπ : A.projection w = A.projection z) (hheight : 0 ≤ A.height w) :
    0 ≤ A.height z := by
  calc
    0 ≤ A.height w := hheight
    _ ≤ c.eval (A.projection w) := c.upper_bound w hw
    _ = c.eval (A.projection z) := congrArg c.eval hπ
    _ = A.height z := hz.2.symm

end UpperSupportCertificate

variable (A : CompactConvexProjection E F)

/-- Every base point has some point of nonnegative height in its projection
fiber.  In the paper this follows from the diagonal relation. -/
def HasNonnegativeFiberWitness : Prop :=
  ∀ x ∈ A.base, ∃ w ∈ A.carrier,
    A.projection w = x ∧ 0 ≤ A.height w

/-- A finite family of copies whose heights sum to zero supplies the
nonnegative fiber witnesses used in the proof that `Y ⊆ X`. -/
theorem hasNonnegativeFiberWitness_of_diagonal
    {I : Type*} [Fintype I] [Nonempty I]
    (copy : A.base → I → E)
    (hcopy_mem : ∀ x i, copy x i ∈ A.carrier)
    (hcopy_projection : ∀ x i, A.projection (copy x i) = x)
    (hdiag : ∀ x, ∑ i, A.height (copy x i) = 0) :
    A.HasNonnegativeFiberWitness := by
  intro x hx
  let x' : A.base := ⟨x, hx⟩
  obtain ⟨i, hi⟩ := exists_nonnegative_of_sum_eq_zero
    (fun i ↦ A.height (copy x' i)) (hdiag x')
  exact ⟨copy x' i, hcopy_mem x' i, hcopy_projection x' i, hi⟩

/-- Under the diagonal nonnegativity condition, a support contact face is
nonnegative for the height functional. -/
theorem UpperSupportCertificate.height_nonnegative_on_contactSet
    (c : UpperSupportCertificate A) (hfiber : A.HasNonnegativeFiberWitness) :
    ∀ z ∈ c.contactSet, 0 ≤ A.height z := by
  intro z hz
  have hx : A.projection z ∈ A.base := ⟨z, hz.1, rfl⟩
  obtain ⟨w, hw, hπ, hheight⟩ := hfiber (A.projection z) hx
  exact c.height_nonnegative_of_fiber_witness hz hw hπ hheight

/-- The union of all support contact faces. -/
def supportedTopLocus : Set E :=
  ⋃ c : UpperSupportCertificate A, c.contactSet

theorem supportedTopLocus_subset_topLocus :
    A.supportedTopLocus ⊆ A.topLocus := by
  intro w hw
  simp only [supportedTopLocus, mem_iUnion] at hw
  obtain ⟨c, hw⟩ := hw
  exact c.contactSet_subset_topLocus hw

/-- The polyhedral supporting-face property needed for the converse
in the facewise description of `Y_y`. -/
def HasUpperSupportAtEveryTopPoint : Prop :=
  ∀ w ∈ A.topLocus, ∃ c : UpperSupportCertificate A, w ∈ c.contactSet

/-- When every top point admits an affine upper support—as it does for the
polytope `R_y`—the top locus is precisely the union of its support contact
faces.  This is Claim `Y-face-description` at the level of `Q`. -/
theorem supportedTopLocus_eq_topLocus
    (hsupport : A.HasUpperSupportAtEveryTopPoint) :
    A.supportedTopLocus = A.topLocus := by
  apply Subset.antisymm A.supportedTopLocus_subset_topLocus
  intro w hw
  obtain ⟨c, hc⟩ := hsupport w hw
  simp only [supportedTopLocus, mem_iUnion]
  exact ⟨c, hc⟩

/-- A finite list of supporting affine functions whose contact faces cover
the top locus.  A polytope has such a list, supplied by its finitely many
top facets. -/
structure FiniteUpperSupportCover where
  certificates : Finset (UpperSupportCertificate A)
  covers : ∀ w ∈ A.topLocus,
    ∃ c ∈ certificates, w ∈ c.contactSet

namespace FiniteUpperSupportCover

variable {A : CompactConvexProjection E F} (C : FiniteUpperSupportCover A)

include C

/-- The finite union of contact faces in a support cover. -/
def contactUnion : Set E :=
  {w | ∃ c ∈ C.certificates, w ∈ c.contactSet}

theorem contactUnion_eq_topLocus : C.contactUnion = A.topLocus := by
  apply Subset.antisymm
  · rintro w ⟨c, _hc, hw⟩
    exact c.contactSet_subset_topLocus hw
  · intro w hw
    obtain ⟨c, hc, hwc⟩ := C.covers w hw
    exact ⟨c, hc, hwc⟩

theorem contactUnion_compact : IsCompact C.contactUnion := by
  classical
  rw [show C.contactUnion = ⋃ c ∈ C.certificates, c.contactSet by
    ext w
    simp [contactUnion]]
  exact C.certificates.isCompact_biUnion fun c _hc ↦ c.contactSet_compact

/-- A finite supporting-face cover makes the top locus compact. -/
theorem topLocus_compact : IsCompact A.topLocus := by
  rw [← contactUnion_eq_topLocus C]
  exact contactUnion_compact C

theorem topLocus_closed : IsClosed A.topLocus :=
  (topLocus_compact C).isClosed

/-- Consequently the graph `Γ` is compact. -/
theorem topGraph_compact : IsCompact A.topGraph := by
  rw [← A.liftedMap_image_topLocus]
  exact (topLocus_compact C).image A.liftedMap.continuous

theorem topGraph_closed : IsClosed A.topGraph :=
  (topGraph_compact C).isClosed

/-- Combining a finite supporting-face cover with the diagonal witness
condition proves nonnegativity on the entire top locus.  This is the core of
the paper's inclusion `Y ⊆ X`. -/
theorem height_nonnegative_on_topLocus
    (hfiber : A.HasNonnegativeFiberWitness) :
  ∀ z ∈ A.topLocus, 0 ≤ A.height z := by
  intro z hz
  obtain ⟨c, _hc, hzc⟩ := FiniteUpperSupportCover.covers C z hz
  exact UpperSupportCertificate.height_nonnegative_on_contactSet A c hfiber z hzc

end FiniteUpperSupportCover

end CompactConvexProjection
end AffineTverberg
