import AffineTverberg.SupportingFaces
import AffineTverberg.FiniteFarkas

set_option linter.style.header false

/-!
# Finite top-facet presentations

This file turns the finitely many top facet inequalities of the polytope
`R_y` into the finite upper-support cover used in `SupportingFaces.lean`.
For an inequality

`a(x) + b t ≤ c`, with `b > 0`,

the associated affine upper support is `t ≤ (c - a(x)) / b`.  Active top
facets therefore cut out exactly the exposed contact faces used in the
facewise description of `Y_y`.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace CompactConvexProjection

variable {E F J : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [Finite J]
  (A : CompactConvexProjection E F)

/-- A finite collection of valid inequalities for `R`, with the property
that every point of the top graph lies on one whose vertical coefficient is
strictly positive. -/
structure FiniteTopHalfspacePresentation where
  baseNormal : J → F →L[ℝ] ℝ
  verticalCoeff : J → ℝ
  bound : J → ℝ
  valid : ∀ j p, p ∈ A.liftedImage →
    baseNormal j p.1 + verticalCoeff j * p.2 ≤ bound j
  top_has_positive_active : ∀ p, p ∈ A.topGraph →
    ∃ j, 0 < verticalCoeff j ∧
      baseNormal j p.1 + verticalCoeff j * p.2 = bound j

namespace FiniteTopHalfspacePresentation

variable {A : CompactConvexProjection E F}
  (H : FiniteTopHalfspacePresentation A (J := J))

include H

/-- An index is a top index when its inequality has positive vertical
coefficient and is active somewhere on the top graph. -/
def IsPositiveTopIndex (j : J) : Prop :=
  0 < H.verticalCoeff j ∧
    ∃ p ∈ A.topGraph,
      H.baseNormal j p.1 + H.verticalCoeff j * p.2 = H.bound j

/-- The finite type of positive top-facet indices. -/
abbrev PositiveTopIndex := {j : J // H.IsPositiveTopIndex j}

noncomputable instance : Fintype H.PositiveTopIndex :=
  Fintype.ofFinite H.PositiveTopIndex

/-- The affine upper-support slope associated to a positive top facet. -/
def supportSlope (j : H.PositiveTopIndex) : F →L[ℝ] ℝ :=
  (-(H.verticalCoeff j.1)⁻¹) • H.baseNormal j.1

/-- The affine upper-support intercept associated to a positive top facet. -/
def supportIntercept (j : H.PositiveTopIndex) : ℝ :=
  (H.verticalCoeff j.1)⁻¹ * H.bound j.1

omit [Finite J] in
private theorem support_value_eq_div (j : H.PositiveTopIndex) (x : F) :
    H.supportSlope j x + H.supportIntercept j =
      (H.bound j.1 - H.baseNormal j.1 x) / H.verticalCoeff j.1 := by
  have hb : H.verticalCoeff j.1 ≠ 0 := ne_of_gt j.2.1
  simp only [supportSlope, supportIntercept, smul_apply,
    smul_eq_mul]
  field_simp
  ring

/-- The upper-support certificate cut out by a positive top facet. -/
def supportCertificate (j : H.PositiveTopIndex) : UpperSupportCertificate A where
  slope := H.supportSlope j
  intercept := H.supportIntercept j
  upper_bound := by
    intro w hw
    have hvalid := H.valid j.1 (A.liftedMap w) ⟨w, hw, rfl⟩
    rw [H.support_value_eq_div j]
    apply (le_div_iff₀ j.2.1).2
    change H.baseNormal j.1 (A.projection w) +
      H.verticalCoeff j.1 * A.height w ≤ H.bound j.1 at hvalid
    nlinarith
  contact_nonempty := by
    obtain ⟨p, hp, hactive⟩ := j.2.2
    obtain ⟨w, hw, hwp⟩ := A.topGraph_subset_liftedImage hp
    refine ⟨w, hw, ?_⟩
    rw [H.support_value_eq_div j]
    apply (eq_div_iff (ne_of_gt j.2.1)).2
    have hactive' := hactive
    rw [← hwp] at hactive'
    change H.baseNormal j.1 (A.projection w) +
      H.verticalCoeff j.1 * A.height w = H.bound j.1 at hactive'
    linarith

omit [Finite J] in
/-- Contact with the support certificate is equivalent to activity of the
corresponding facet inequality. -/
theorem mem_supportCertificate_contactSet_iff
    (j : H.PositiveTopIndex) (w : E) :
    w ∈ (H.supportCertificate j).contactSet ↔
      w ∈ A.carrier ∧
        H.baseNormal j.1 (A.projection w) +
          H.verticalCoeff j.1 * A.height w = H.bound j.1 := by
  change (w ∈ A.carrier ∧
      A.height w = H.supportSlope j (A.projection w) + H.supportIntercept j) ↔ _
  constructor
  · intro hw
    refine ⟨hw.1, ?_⟩
    have heq := hw.2
    rw [H.support_value_eq_div j] at heq
    have hmul := (eq_div_iff (ne_of_gt j.2.1)).1 heq
    linarith
  · rintro ⟨hw, hactive⟩
    refine ⟨hw, ?_⟩
    rw [H.support_value_eq_div j]
    apply (eq_div_iff (ne_of_gt j.2.1)).2
    linarith

/-- The finitely many positive top facets canonically give a finite upper
support cover. -/
def finiteUpperSupportCover : FiniteUpperSupportCover A := by
  classical
  exact
    { certificates := Finset.univ.image H.supportCertificate
      covers := by
        intro w hw
        have hp : A.liftedMap w ∈ A.topGraph := by
          change A.projection w ∈ A.base ∧
            A.height w = A.upperEnvelope (A.projection w)
          exact ⟨⟨w, hw.1, rfl⟩, hw.2⟩
        obtain ⟨j, hb, hactive⟩ := H.top_has_positive_active (A.liftedMap w) hp
        let jtop : H.PositiveTopIndex :=
          ⟨j, hb, ⟨A.liftedMap w, hp, hactive⟩⟩
        refine ⟨H.supportCertificate jtop, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨jtop, Finset.mem_univ _, rfl⟩
        · rw [H.mem_supportCertificate_contactSet_iff]
          refine ⟨hw.1, ?_⟩
          simpa [liftedMap] using hactive }

/-- A finite top-halfspace presentation proves the polyhedral support
property used by the facewise description. -/
theorem hasUpperSupportAtEveryTopPoint :
    A.HasUpperSupportAtEveryTopPoint := by
  intro w hw
  obtain ⟨c, _hc, hwc⟩ :=
    FiniteUpperSupportCover.covers (finiteUpperSupportCover H) w hw
  exact ⟨c, hwc⟩

theorem supportedTopLocus_eq_topLocus :
    A.supportedTopLocus = A.topLocus :=
  CompactConvexProjection.supportedTopLocus_eq_topLocus A
    (hasUpperSupportAtEveryTopPoint H)

theorem topLocus_compact : IsCompact A.topLocus :=
  FiniteUpperSupportCover.topLocus_compact (finiteUpperSupportCover H)

theorem topLocus_closed : IsClosed A.topLocus :=
  FiniteUpperSupportCover.topLocus_closed (finiteUpperSupportCover H)

theorem topGraph_compact : IsCompact A.topGraph :=
  FiniteUpperSupportCover.topGraph_compact (finiteUpperSupportCover H)

theorem topGraph_closed : IsClosed A.topGraph :=
  FiniteUpperSupportCover.topGraph_closed (finiteUpperSupportCover H)

/-- With the diagonal witness condition, the finite top-facet presentation
implies nonnegativity on the whole top locus. -/
theorem height_nonnegative_on_topLocus
    (hfiber : A.HasNonnegativeFiberWitness) :
    ∀ z ∈ A.topLocus, 0 ≤ A.height z :=
  FiniteUpperSupportCover.height_nonnegative_on_topLocus
    (finiteUpperSupportCover H) hfiber

end FiniteTopHalfspacePresentation

/-- An exact finite halfspace description of the lifted image `R`. -/
structure FiniteHalfspacePresentation where
  baseNormal : J → F →L[ℝ] ℝ
  verticalCoeff : J → ℝ
  bound : J → ℝ
  mem_liftedImage_iff : ∀ p,
    p ∈ A.liftedImage ↔
      ∀ j, baseNormal j p.1 + verticalCoeff j * p.2 ≤ bound j

namespace FiniteHalfspacePresentation

variable [Nonempty J] {A : CompactConvexProjection E F}
  (H : FiniteHalfspacePresentation A (J := J))

include H

/-- At a top point of a set given by finitely many affine inequalities,
some active inequality has positive vertical coefficient. -/
theorem exists_positive_active (p : F × ℝ) (hp : p ∈ A.topGraph) :
    ∃ j, 0 < H.verticalCoeff j ∧
      H.baseNormal j p.1 + H.verticalCoeff j * p.2 = H.bound j := by
  classical
  have : Fintype J := Fintype.ofFinite J
  have hpImage : p ∈ A.liftedImage := A.topGraph_subset_liftedImage hp
  have hpIneq := (H.mem_liftedImage_iff p).1 hpImage
  by_contra hactive
  have hnotActive : ∀ j, 0 < H.verticalCoeff j →
      H.baseNormal j p.1 + H.verticalCoeff j * p.2 ≠ H.bound j := by
    intro j hb heq
    exact hactive ⟨j, hb, heq⟩
  let threshold : J → ℝ := fun j ↦
    if 0 < H.verticalCoeff j then
      (H.bound j -
        (H.baseNormal j p.1 + H.verticalCoeff j * p.2)) /
          H.verticalCoeff j
    else 1
  have hthreshold_pos (j : J) : 0 < threshold j := by
    by_cases hb : 0 < H.verticalCoeff j
    · rw [show threshold j =
          (H.bound j -
            (H.baseNormal j p.1 + H.verticalCoeff j * p.2)) /
              H.verticalCoeff j by simp [threshold, hb]]
      apply div_pos
      · exact sub_pos.mpr <| lt_of_le_of_ne (hpIneq j)
          (hnotActive j hb)
      · exact hb
    · simp [threshold, hb]
  let thresholds : Finset ℝ := Finset.univ.image threshold
  have hthresholds : thresholds.Nonempty := by
    obtain ⟨j⟩ := ‹Nonempty J›
    exact ⟨threshold j, by simp [thresholds]⟩
  let δ : ℝ := thresholds.min' hthresholds
  have hδ_pos : 0 < δ := by
    apply (Finset.lt_min'_iff thresholds hthresholds).2
    intro t ht
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp ht
    exact hthreshold_pos j
  have hδ_le (j : J) : δ ≤ threshold j := by
    apply Finset.min'_le
    simp [thresholds]
  let s : ℝ := δ / 2
  have hs_pos : 0 < s := div_pos hδ_pos (by norm_num)
  let q : F × ℝ := (p.1, p.2 + s)
  have hqIneq : ∀ j,
      H.baseNormal j q.1 + H.verticalCoeff j * q.2 ≤ H.bound j := by
    intro j
    change H.baseNormal j p.1 + H.verticalCoeff j * (p.2 + s) ≤ H.bound j
    by_cases hb : 0 < H.verticalCoeff j
    · have hs_lt_delta : s < δ := by
        dsimp [s]
        linarith
      have hs_lt_threshold : s < threshold j :=
        hs_lt_delta.trans_le (hδ_le j)
      rw [show threshold j =
          (H.bound j -
            (H.baseNormal j p.1 + H.verticalCoeff j * p.2)) /
              H.verticalCoeff j by simp [threshold, hb]] at hs_lt_threshold
      have hmul := (lt_div_iff₀ hb).1 hs_lt_threshold
      nlinarith
    · have hb' : H.verticalCoeff j ≤ 0 := le_of_not_gt hb
      nlinarith [hpIneq j, hs_pos.le]
  have hqImage : q ∈ A.liftedImage :=
    (H.mem_liftedImage_iff q).2 hqIneq
  have htop := (A.mem_topGraph_iff p).1 hp
  have hle : q.2 ≤ p.2 := htop.2 q hqImage rfl
  change p.2 + s ≤ p.2 at hle
  linarith

/-- An exact finite halfspace description automatically has the positive
active top-facet property. -/
def toFiniteTopHalfspacePresentation :
    FiniteTopHalfspacePresentation A (J := J) where
  baseNormal := H.baseNormal
  verticalCoeff := H.verticalCoeff
  bound := H.bound
  valid := fun j p hp ↦ (H.mem_liftedImage_iff p).1 hp j
  top_has_positive_active := H.exists_positive_active

/-- Hence an exact finite halfspace description canonically yields the
finite support cover used in the proof of closedness and `Y ⊆ X`. -/
def finiteUpperSupportCover : FiniteUpperSupportCover A :=
  H.toFiniteTopHalfspacePresentation.finiteUpperSupportCover

theorem topLocus_compact : IsCompact A.topLocus :=
  FiniteUpperSupportCover.topLocus_compact H.finiteUpperSupportCover

theorem topLocus_closed : IsClosed A.topLocus :=
  FiniteUpperSupportCover.topLocus_closed H.finiteUpperSupportCover

theorem topGraph_compact : IsCompact A.topGraph :=
  FiniteUpperSupportCover.topGraph_compact H.finiteUpperSupportCover

theorem topGraph_closed : IsClosed A.topGraph :=
  FiniteUpperSupportCover.topGraph_closed H.finiteUpperSupportCover

theorem height_nonnegative_on_topLocus
    (hfiber : A.HasNonnegativeFiberWitness) :
    ∀ z ∈ A.topLocus, 0 ≤ A.height z :=
  FiniteUpperSupportCover.height_nonnegative_on_topLocus
    H.finiteUpperSupportCover hfiber

end FiniteHalfspacePresentation

/-!
### The polytope `R_y`

For the polytope of the paper the carrier `Q` is the convex hull of a finite
vertex set `S`.  In that case no halfspace presentation has to be assumed:
the finite Farkas lemma of `AffineTverberg/FiniteFarkas.lean` produces an
affine upper support through *every* top point, and the finitely many
possible contact faces assemble into a `FiniteUpperSupportCover`.
-/

section Polytope

/-- **Separation at a top point of a polytope.**  If the carrier is the
convex hull of the finite set `S` and `w` maximizes the height in its own
projection fiber, then there is an affine function of the base which
majorizes the height on the carrier and is tight at `w`. -/
theorem exists_upperSupportCertificate_mem_contactSet_of_convexHull
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E))
    {w : E} (hw : w ∈ A.topLocus) :
    ∃ c : UpperSupportCertificate A, w ∈ c.contactSet := by
  classical
  obtain ⟨hwmem, hmax⟩ := A.mem_topLocus_iff.1 hw
  set d : E → F := fun v ↦ A.projection v - A.projection w with hd
  set ht : E → ℝ := fun v ↦ A.height v - A.height w with hht
  have hfarkas : ∀ l : E → ℝ, (∀ v ∈ S, 0 ≤ l v) → ∑ v ∈ S, l v • d v = 0 →
      ∑ v ∈ S, l v * ht v ≤ 0 := by
    intro l hl hzero
    set m : ℝ := ∑ v ∈ S, l v with hm_def
    have hmnn : 0 ≤ m := Finset.sum_nonneg hl
    rcases hmnn.eq_or_lt with hm0 | hmpos
    · have hzeros : ∀ v ∈ S, l v = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg hl).1 hm0.symm
      have hsum : ∑ v ∈ S, l v * ht v = 0 :=
        Finset.sum_eq_zero fun v hv ↦ by rw [hzeros v hv]; ring
      rw [hsum]
    · have humem : S.centerMass l id ∈ convexHull ℝ (S : Set E) :=
        S.centerMass_mem_convexHull hl hmpos fun i hi ↦ Finset.mem_coe.2 hi
      set u : E := S.centerMass l id with hu_def
      have hueq : u = ∑ v ∈ S, (m⁻¹ * l v) • v := by
        rw [hu_def, Finset.centerMass, ← hm_def, Finset.smul_sum]
        exact Finset.sum_congr rfl fun v _ ↦ by rw [smul_smul]; rfl
      have hprojsum : ∑ v ∈ S, l v • A.projection v = m • A.projection w := by
        have h0 : ∑ v ∈ S, (l v • A.projection v - l v • A.projection w) = 0 := by
          rw [← hzero]
          exact Finset.sum_congr rfl fun v _ ↦ by rw [← smul_sub]
        rw [Finset.sum_sub_distrib, ← Finset.sum_smul, ← hm_def] at h0
        exact sub_eq_zero.1 h0
      have hproju : A.projection u = A.projection w := by
        rw [hueq, map_sum]
        have : ∑ v ∈ S, A.projection ((m⁻¹ * l v) • v)
            = m⁻¹ • ∑ v ∈ S, l v • A.projection v := by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl fun v _ ↦ by
            rw [map_smul, smul_smul]
        rw [this, hprojsum, smul_smul, inv_mul_cancel₀ hmpos.ne', one_smul]
      have hheightu : A.height u = m⁻¹ * ∑ v ∈ S, l v * A.height v := by
        rw [hueq, map_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun v _ ↦ by
          rw [map_smul, smul_eq_mul, mul_assoc]
      have hle : A.height u ≤ A.height w := hmax u (by rw [hS]; exact humem) hproju
      rw [hheightu] at hle
      have hmul : ∑ v ∈ S, l v * A.height v ≤ m * A.height w := by
        have := mul_le_mul_of_nonneg_left hle hmnn
        rwa [← mul_assoc, mul_inv_cancel₀ hmpos.ne', one_mul] at this
      have hsplit : ∑ v ∈ S, l v * ht v
          = (∑ v ∈ S, l v * A.height v) - m * A.height w := by
        rw [hm_def, Finset.sum_mul, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun v _ ↦ by simp only [hht]; ring
      rw [hsplit]
      linarith
  obtain ⟨a, ha⟩ :=
    exists_continuousLinearMap_ge_of_forall_nonneg_combination S d ht hfarkas
  have hvertex : ∀ v ∈ S, A.height v ≤ a (A.projection v)
      + (A.height w - a (A.projection w)) := by
    intro v hv
    have hav := ha v hv
    simp only [hd, hht, map_sub] at hav
    linarith
  have hupper : ∀ x ∈ A.carrier, A.height x ≤ a (A.projection x)
      + (A.height w - a (A.projection w)) := by
    intro x hx
    set g : E →L[ℝ] ℝ := A.height - a.comp A.projection with hg
    have hgapply : ∀ z : E, g z = A.height z - a (A.projection z) := fun z ↦ rfl
    have hconv : Convex ℝ {z : E | g z ≤ A.height w - a (A.projection w)} :=
      convex_halfSpace_le g.toLinearMap.isLinear _
    have hsub : (S : Set E) ⊆ {z : E | g z ≤ A.height w - a (A.projection w)} := by
      intro v hv
      have := hvertex v (Finset.mem_coe.1 hv)
      rw [Set.mem_ofPred_eq, hgapply]
      linarith
    have hxhull : x ∈ convexHull ℝ (S : Set E) := by rw [← hS]; exact hx
    have := convexHull_min hsub hconv hxhull
    rw [Set.mem_ofPred_eq, hgapply] at this
    linarith
  refine ⟨{ slope := a
            intercept := A.height w - a (A.projection w)
            upper_bound := hupper
            contact_nonempty := ⟨w, hwmem, by ring⟩ }, hwmem, ?_⟩
  change A.height w = a (A.projection w) + (A.height w - a (A.projection w))
  ring

/-- **The polyhedral supporting-face property for a polytope.** -/
theorem hasUpperSupportAtEveryTopPoint_of_convexHull
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E)) :
    A.HasUpperSupportAtEveryTopPoint := fun _w hw ↦
  exists_upperSupportCertificate_mem_contactSet_of_convexHull A S hS hw

/-- For a polytope carrier the top locus is exactly the union of the
supporting contact faces. -/
theorem polytope_supportedTopLocus_eq_topLocus
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E)) :
    A.supportedTopLocus = A.topLocus :=
  CompactConvexProjection.supportedTopLocus_eq_topLocus A
    (hasUpperSupportAtEveryTopPoint_of_convexHull A S hS)

/-- Vertices of the polytope lie in its carrier. -/
theorem vertex_mem_carrier {S : Finset E}
    (hS : A.carrier = convexHull ℝ (S : Set E)) {v : E} (hv : v ∈ S) :
    v ∈ A.carrier := by
  rw [hS]
  exact subset_convexHull ℝ (S : Set E) (Finset.mem_coe.2 hv)

/-- **The contact face is the hull of its tight vertices.**  A point at
which an affine upper support is tight is a convex combination of the
vertices at which that same support is tight: the support gap is an affine
nonnegative function on the carrier, so it can only vanish on a convex
combination if it vanishes at every vertex occurring in it. -/
theorem mem_convexHull_tight_vertices
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E))
    (c : UpperSupportCertificate A) {w : E} (hw : w ∈ c.contactSet) :
    w ∈ convexHull ℝ {v : E | v ∈ (S : Set E) ∧ v ∈ c.contactSet} := by
  classical
  set L : E →L[ℝ] ℝ := c.slope.comp A.projection - A.height with hL
  set g : E → ℝ := fun z ↦ L z + c.intercept with hg
  have hgapply : ∀ z : E, g z =
      c.slope (A.projection z) + c.intercept - A.height z := fun z ↦ by
    simp only [hg, hL, FunLike.coe_sub, Pi.sub_apply,
      ContinuousLinearMap.coe_comp, Function.comp_apply]
    ring
  have hgnonneg : ∀ z ∈ A.carrier, 0 ≤ g z := by
    intro z hz
    have := c.upper_bound z hz
    rw [hgapply z]
    linarith
  have hgzero_iff : ∀ z ∈ A.carrier, (g z = 0 ↔ z ∈ c.contactSet) := by
    intro z hz
    rw [hgapply z]
    constructor
    · intro h
      exact ⟨hz, by
        change A.height z = c.slope (A.projection z) + c.intercept
        linarith⟩
    · intro h
      have : A.height z = c.slope (A.projection z) + c.intercept := h.2
      linarith
  have hwS : w ∈ convexHull ℝ (S : Set E) := by rw [← hS]; exact hw.1
  rw [Finset.convexHull_eq] at hwS
  obtain ⟨lam, hlam0, hlam1, hlamw⟩ := hwS
  rw [Finset.centerMass_eq_of_sum_1 S id hlam1] at hlamw
  have hwsum : ∑ v ∈ S, lam v • v = w := hlamw
  have haffine : ∑ v ∈ S, lam v * g v = g w := by
    have hLsum : ∑ v ∈ S, lam v * L v = L w := by
      rw [← hwsum, map_sum]
      exact Finset.sum_congr rfl fun v _ ↦ by rw [map_smul, smul_eq_mul]
    calc ∑ v ∈ S, lam v * g v
        = ∑ v ∈ S, (lam v * L v + lam v * c.intercept) :=
          Finset.sum_congr rfl fun v _ ↦ by rw [hg]; ring
      _ = (∑ v ∈ S, lam v * L v) + (∑ v ∈ S, lam v) * c.intercept := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
      _ = L w + c.intercept := by rw [hLsum, hlam1, one_mul]
      _ = g w := rfl
  have hgw : g w = 0 := (hgzero_iff w hw.1).2 hw
  have hterms : ∀ v ∈ S, lam v * g v = 0 := by
    refine (Finset.sum_eq_zero_iff_of_nonneg ?_).1 (by rw [haffine, hgw])
    intro v hv
    exact mul_nonneg (hlam0 v hv) (hgnonneg v (vertex_mem_carrier A hS hv))
  set T : Finset E := S.filter (fun v ↦ v ∈ c.contactSet) with hT
  have hlam_off : ∀ v ∈ S.filter (fun v ↦ v ∉ c.contactSet), lam v = 0 := by
    intro v hv
    obtain ⟨hvS, hvnot⟩ := Finset.mem_filter.1 hv
    have hgv : g v ≠ 0 := fun h ↦
      hvnot ((hgzero_iff v (vertex_mem_carrier A hS hvS)).1 h)
    have := hterms v hvS
    exact (mul_eq_zero.1 this).resolve_right hgv
  have hsumT : ∑ v ∈ T, lam v = 1 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not S
      (fun v ↦ v ∈ c.contactSet) lam
    have hzero : ∑ v ∈ S.filter (fun v ↦ v ∉ c.contactSet), lam v = 0 :=
      Finset.sum_eq_zero hlam_off
    rw [hzero, add_zero] at hsplit
    rw [hT, hsplit, hlam1]
  have hvecT : ∑ v ∈ T, lam v • v = w := by
    have hsplit := Finset.sum_filter_add_sum_filter_not S
      (fun v ↦ v ∈ c.contactSet) (fun v ↦ lam v • v)
    have hzero : ∑ v ∈ S.filter (fun v ↦ v ∉ c.contactSet), lam v • v = 0 :=
      Finset.sum_eq_zero fun v hv ↦ by rw [hlam_off v hv, zero_smul]
    rw [hzero, add_zero] at hsplit
    rw [hT, hsplit, hwsum]
  have hcm : T.centerMass lam id = w := by
    rw [Finset.centerMass_eq_of_sum_1 T id hsumT]
    exact hvecT
  have := T.centerMass_mem_convexHull
    (w := lam) (fun v hv ↦ hlam0 v (Finset.mem_filter.1 hv).1)
    (by rw [hsumT]; norm_num)
    (z := id) (s := {v : E | v ∈ (S : Set E) ∧ v ∈ c.contactSet})
    (fun v hv ↦ ⟨Finset.mem_coe.2 (Finset.mem_filter.1 hv).1,
      (Finset.mem_filter.1 hv).2⟩)
  rwa [hcm] at this

/-- **A finite supporting-face cover for a polytope.**  Contact faces are
hulls of subsets of the vertex set, so finitely many affine upper supports
already cover the whole top locus. -/
noncomputable def polytopeFiniteUpperSupportCover
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E)) :
    FiniteUpperSupportCover A := by
  classical
  set P : Finset (Finset E) :=
    S.powerset.filter
      (fun T ↦ ∃ c : UpperSupportCertificate A, ∀ v ∈ T, v ∈ c.contactSet) with hP
  have hchoice : ∀ T ∈ P, ∃ c : UpperSupportCertificate A,
      ∀ v ∈ T, v ∈ c.contactSet := fun T hT ↦ (Finset.mem_filter.1 hT).2
  refine
    { certificates := P.attach.image (fun T ↦ Classical.choose (hchoice T.1 T.2))
      covers := ?_ }
  intro w hw
  obtain ⟨c, hc⟩ :=
    exists_upperSupportCertificate_mem_contactSet_of_convexHull A S hS hw
  set T : Finset E := S.filter (fun v ↦ v ∈ c.contactSet) with hT
  have hTP : T ∈ P := by
    refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.filter_subset _ _),
      c, fun v hv ↦ (Finset.mem_filter.1 hv).2⟩
  have hspec := Classical.choose_spec (hchoice T hTP)
  have hwT : w ∈ convexHull ℝ (T : Set E) := by
    have hmem := mem_convexHull_tight_vertices A S hS c hc
    have hset : {v : E | v ∈ (S : Set E) ∧ v ∈ c.contactSet} = (T : Set E) := by
      ext v
      simp [hT]
    rwa [hset] at hmem
  refine ⟨Classical.choose (hchoice T hTP),
    Finset.mem_image.2 ⟨⟨T, hTP⟩, Finset.mem_attach _ _, rfl⟩, ?_⟩
  exact convexHull_min (fun v hv ↦ hspec v (Finset.mem_coe.1 hv))
    (Classical.choose (hchoice T hTP)).contactSet_convex hwT

/-- The top locus of a polytope projection is compact. -/
theorem polytope_topLocus_compact
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E)) :
    IsCompact A.topLocus :=
  FiniteUpperSupportCover.topLocus_compact (polytopeFiniteUpperSupportCover A S hS)

/-- The top locus of a polytope projection is closed. -/
theorem polytope_topLocus_closed
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E)) :
    IsClosed A.topLocus :=
  FiniteUpperSupportCover.topLocus_closed (polytopeFiniteUpperSupportCover A S hS)

/-- The graph of the upper envelope over a polytope is compact. -/
theorem polytope_topGraph_compact
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E)) :
    IsCompact A.topGraph :=
  FiniteUpperSupportCover.topGraph_compact (polytopeFiniteUpperSupportCover A S hS)

/-- The graph of the upper envelope over a polytope is closed. -/
theorem polytope_topGraph_closed
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E)) :
    IsClosed A.topGraph :=
  FiniteUpperSupportCover.topGraph_closed (polytopeFiniteUpperSupportCover A S hS)

/-- For a polytope carrier, the diagonal witness condition gives
nonnegativity of the height on the whole top locus. -/
theorem polytope_height_nonnegative_on_topLocus
    (S : Finset E) (hS : A.carrier = convexHull ℝ (S : Set E))
    (hfiber : A.HasNonnegativeFiberWitness) :
    ∀ z ∈ A.topLocus, 0 ≤ A.height z :=
  FiniteUpperSupportCover.height_nonnegative_on_topLocus
    (polytopeFiniteUpperSupportCover A S hS) hfiber

end Polytope

end CompactConvexProjection
end AffineTverberg
