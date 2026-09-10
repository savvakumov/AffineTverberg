import AffineTverberg.SimplicialHomology
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Retraction from the complement of an induced subcomplex

In a finite simplicial complex whose vertices are partitioned into good
and bad vertices, the complement of the bad induced realization retracts
onto the good induced realization.  In barycentric coordinates the map
discards all bad coordinates and divides by the total good weight.

The denominator is positive precisely on the complement.  Interpolating
linearly between the original coordinates and the normalized coordinates
stays in the original simplex, stays in the complement, and fixes every
point of the good realization.  This is the explicit construction used
in the paper's local acyclicity and Alexander-duality arguments.
-/

noncomputable section

open scoped BigOperators
open Set unitInterval

namespace AffineTverberg
namespace Simplicial

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Standard barycentric realization of a finite simplicial family.  A
point has nonnegative coordinates summing to one, supported on one face. -/
def barycentricCarrier (K : Finset (Finset V)) : Set (V → ℝ) :=
  {x | (∀ v, 0 ≤ x v) ∧ (∑ v, x v) = 1 ∧
    ∃ s ∈ K, ∀ v, v ∉ s → x v = 0}

/-- Restriction to the subcomplex induced by a set of vertices. -/
def inducedFaces (K : Finset (Finset V)) (G : Finset V) : Finset (Finset V) :=
  K.filter fun s ↦ s ⊆ G

omit [Fintype V] in
@[simp]
theorem mem_inducedFaces {K : Finset (Finset V)} {G s : Finset V} :
    s ∈ inducedFaces K G ↔ s ∈ K ∧ s ⊆ G := by
  simp [inducedFaces]

omit [Fintype V] in
theorem faceClosed_inducedFaces {K : Finset (Finset V)}
    (hK : FaceClosed K) (G : Finset V) : FaceClosed (inducedFaces K G) := by
  intro s hs t hts
  obtain ⟨hsK, hsG⟩ := mem_inducedFaces.mp hs
  exact mem_inducedFaces.mpr ⟨hK s hsK t hts, hts.trans hsG⟩

/-- The total barycentric mass assigned to the selected good vertices. -/
def goodWeight (G : Finset V) (x : V → ℝ) : ℝ := ∑ v ∈ G, x v

omit [Fintype V] [DecidableEq V] in
theorem continuous_goodWeight (G : Finset V) : Continuous (goodWeight G) := by
  unfold goodWeight
  fun_prop

omit [DecidableEq V] in
theorem goodWeight_nonneg {K : Finset (Finset V)} {G : Finset V} {x : V → ℝ}
    (hx : x ∈ barycentricCarrier K) : 0 ≤ goodWeight G x :=
  Finset.sum_nonneg fun v _ ↦ hx.1 v

theorem barycentricCarrier_induced_subset (K : Finset (Finset V)) (G : Finset V) :
    barycentricCarrier (inducedFaces K G) ⊆ barycentricCarrier K := by
  rintro x ⟨hx0, hx1, s, hs, hxs⟩
  exact ⟨hx0, hx1, s, (mem_inducedFaces.mp hs).1, hxs⟩

theorem coord_eq_zero_of_mem_induced {K : Finset (Finset V)} {G : Finset V}
    {x : V → ℝ} (hx : x ∈ barycentricCarrier (inducedFaces K G))
    (v : V) (hv : v ∉ G) : x v = 0 := by
  obtain ⟨s, hs, hxs⟩ := hx.2.2
  exact hxs v fun hvs ↦ hv ((mem_inducedFaces.mp hs).2 hvs)

theorem goodWeight_eq_one_of_mem_induced
    {K : Finset (Finset V)} {G : Finset V} {x : V → ℝ}
    (hx : x ∈ barycentricCarrier (inducedFaces K G)) : goodWeight G x = 1 := by
  calc
    goodWeight G x = ∑ v, x v :=
      Finset.sum_subset (Finset.subset_univ G)
        (fun v _ hv ↦ coord_eq_zero_of_mem_induced hx v hv)
    _ = 1 := hx.2.1

/-- Zero good weight is exactly membership in the bad induced realization. -/
theorem goodWeight_eq_zero_iff_mem_bad
    {K : Finset (Finset V)} (hK : FaceClosed K) (G : Finset V)
    {x : V → ℝ} (hx : x ∈ barycentricCarrier K) :
    goodWeight G x = 0 ↔ x ∈ barycentricCarrier (inducedFaces K Gᶜ) := by
  constructor
  · intro hw
    have hz : ∀ v ∈ G, x v = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun v _ ↦ hx.1 v)).mp hw
    obtain ⟨s, hs, hxs⟩ := hx.2.2
    refine ⟨hx.1, hx.2.1, s \ G, mem_inducedFaces.mpr ⟨?_, ?_⟩, ?_⟩
    · exact hK s hs (s \ G) Finset.sdiff_subset
    · intro v hv
      exact Finset.mem_compl.mpr (Finset.mem_sdiff.mp hv).2
    · intro v hv
      by_cases hvG : v ∈ G
      · exact hz v hvG
      · exact hxs v fun hvs ↦ hv (Finset.mem_sdiff.mpr ⟨hvs, hvG⟩)
  · intro hbad
    exact Finset.sum_eq_zero fun v hv ↦
      coord_eq_zero_of_mem_induced hbad v (by simpa using hv)

/-- The complement of the bad induced realization is the positive-good-mass
locus inside the original realization. -/
theorem barycentric_complement_eq_positive_goodWeight
    {K : Finset (Finset V)} (hK : FaceClosed K) (G : Finset V) :
    barycentricCarrier K \ barycentricCarrier (inducedFaces K Gᶜ) =
      {x | x ∈ barycentricCarrier K ∧ 0 < goodWeight G x} := by
  ext x
  constructor
  · rintro ⟨hx, hbad⟩
    refine ⟨hx, lt_of_le_of_ne (goodWeight_nonneg hx) ?_⟩
    intro hw
    exact hbad ((goodWeight_eq_zero_iff_mem_bad hK G hx).mp hw.symm)
  · rintro ⟨hx, hw⟩
    refine ⟨hx, ?_⟩
    intro hbad
    exact hw.ne' ((goodWeight_eq_zero_iff_mem_bad hK G hx).mpr hbad)

/-- The complement represented by its equivalent positive-good-mass condition. -/
abbrev BarycentricGoodComplement (K : Finset (Finset V)) (G : Finset V) :=
  {x : V → ℝ // x ∈ barycentricCarrier K ∧ 0 < goodWeight G x}

/-- Normalize the good coordinates and discard all bad coordinates. -/
def normalizeGood (G : Finset V) (x : V → ℝ) : V → ℝ :=
  fun v ↦ if v ∈ G then x v / goodWeight G x else 0

omit [Fintype V] in
theorem goodWeight_normalizeGood {G : Finset V} {x : V → ℝ}
    (hw : 0 < goodWeight G x) : goodWeight G (normalizeGood G x) = 1 := by
  unfold goodWeight
  calc
    ∑ v ∈ G, normalizeGood G x v = ∑ v ∈ G, x v / goodWeight G x :=
      Finset.sum_congr rfl fun v hv ↦ by simp [normalizeGood, hv]
    _ = (∑ v ∈ G, x v) / goodWeight G x := (Finset.sum_div _ _ _).symm
    _ = 1 := div_self hw.ne'

theorem sum_normalizeGood {G : Finset V} {x : V → ℝ}
    (hw : 0 < goodWeight G x) : (∑ v, normalizeGood G x v) = 1 := by
  calc
    ∑ v, normalizeGood G x v = goodWeight G (normalizeGood G x) :=
      (Finset.sum_subset (Finset.subset_univ G)
        (fun v _ hv ↦ by simp [normalizeGood, hv])).symm
    _ = 1 := goodWeight_normalizeGood hw

theorem normalizeGood_mem_induced {K : Finset (Finset V)} (hK : FaceClosed K)
    {G : Finset V} {x : V → ℝ} (hx : x ∈ barycentricCarrier K)
    (hw : 0 < goodWeight G x) :
    normalizeGood G x ∈ barycentricCarrier (inducedFaces K G) := by
  refine ⟨fun v ↦ ?_, sum_normalizeGood hw, ?_⟩
  · by_cases hv : v ∈ G
    · simpa [normalizeGood, hv] using div_nonneg (hx.1 v) hw.le
    · simp [normalizeGood, hv]
  · obtain ⟨s, hs, hxs⟩ := hx.2.2
    refine ⟨s ∩ G, mem_inducedFaces.mpr
      ⟨hK s hs (s ∩ G) Finset.inter_subset_left, Finset.inter_subset_right⟩, ?_⟩
    intro v hv
    by_cases hvG : v ∈ G
    · have hvs : v ∉ s := fun hvs ↦ hv (Finset.mem_inter.mpr ⟨hvs, hvG⟩)
      simp [normalizeGood, hvG, hxs v hvs]
    · simp [normalizeGood, hvG]

theorem normalizeGood_eq_self_of_mem_induced
    {K : Finset (Finset V)} {G : Finset V} {x : V → ℝ}
    (hx : x ∈ barycentricCarrier (inducedFaces K G)) : normalizeGood G x = x := by
  funext v
  by_cases hv : v ∈ G
  · simp [normalizeGood, hv, goodWeight_eq_one_of_mem_induced hx]
  · simp [normalizeGood, hv, coord_eq_zero_of_mem_induced hx v hv]

theorem continuous_normalizeGood_on_complement
    (K : Finset (Finset V)) (G : Finset V) :
    Continuous (fun x : BarycentricGoodComplement K G ↦ normalizeGood G x.val) := by
  apply continuous_pi
  intro v
  by_cases hv : v ∈ G
  · simp only [normalizeGood, hv, ↓reduceIte]
    exact ((continuous_apply v).comp continuous_subtype_val).div
      ((continuous_goodWeight G).comp continuous_subtype_val) (fun x ↦ x.property.2.ne')
  · simp only [normalizeGood, hv, ↓reduceIte]
    exact continuous_const

/-- Retraction from the bad complement to the good induced realization. -/
def goodRetraction {K : Finset (Finset V)} (hK : FaceClosed K) (G : Finset V) :
    C(BarycentricGoodComplement K G, barycentricCarrier (inducedFaces K G)) :=
  ⟨fun x ↦ ⟨normalizeGood G x.val,
      normalizeGood_mem_induced hK x.property.1 x.property.2⟩,
    (continuous_normalizeGood_on_complement K G).subtype_mk _⟩

/-- Inclusion of the good realization into the complement. -/
def goodInclusion (K : Finset (Finset V)) (G : Finset V) :
    C(barycentricCarrier (inducedFaces K G), BarycentricGoodComplement K G) :=
  ⟨fun x ↦ ⟨x.val, barycentricCarrier_induced_subset K G x.property,
      by rw [goodWeight_eq_one_of_mem_induced x.property]; norm_num⟩,
    continuous_subtype_val.subtype_mk _⟩

/-- The retraction fixes the good induced realization pointwise. -/
theorem goodRetraction_comp_inclusion {K : Finset (Finset V)}
    (hK : FaceClosed K) (G : Finset V) :
    (goodRetraction hK G).comp (goodInclusion K G) =
      ContinuousMap.id (barycentricCarrier (inducedFaces K G)) := by
  ext x v
  exact congrFun (normalizeGood_eq_self_of_mem_induced x.property) v

/-- Straight-line interpolation from a point to its good-coordinate
normalization. Both endpoints lie in the same original simplex. -/
def goodSegment (G : Finset V) (t : I) (x : V → ℝ) : V → ℝ :=
  fun v ↦ (1 - (t : ℝ)) * x v + (t : ℝ) * normalizeGood G x v

omit [Fintype V] in
@[simp]
theorem goodSegment_zero (G : Finset V) (x : V → ℝ) : goodSegment G 0 x = x := by
  ext v
  simp [goodSegment]

omit [Fintype V] in
@[simp]
theorem goodSegment_one (G : Finset V) (x : V → ℝ) :
    goodSegment G 1 x = normalizeGood G x := by
  ext v
  simp [goodSegment]

theorem goodSegment_eq_self_of_mem_induced
    {K : Finset (Finset V)} {G : Finset V} {x : V → ℝ}
    (hx : x ∈ barycentricCarrier (inducedFaces K G)) (t : I) :
    goodSegment G t x = x := by
  ext v
  simp only [goodSegment, normalizeGood_eq_self_of_mem_induced hx]
  ring

/-- The interpolation has nonnegative unit-sum coordinates supported
in the original supporting face; it does not cross a simplex boundary. -/
theorem goodSegment_mem_carrier {K : Finset (Finset V)} (hK : FaceClosed K)
    {G : Finset V} {x : V → ℝ} (hx : x ∈ barycentricCarrier K)
    (hw : 0 < goodWeight G x) (t : I) :
    goodSegment G t x ∈ barycentricCarrier K := by
  have hn := normalizeGood_mem_induced hK hx hw
  refine ⟨fun v ↦ add_nonneg
    (mul_nonneg (sub_nonneg.mpr t.property.2) (hx.1 v))
    (mul_nonneg t.property.1 (hn.1 v)), ?_, ?_⟩
  · simp only [goodSegment, Finset.sum_add_distrib, ← Finset.mul_sum,
      hx.2.1, sum_normalizeGood hw]
    ring
  · obtain ⟨s, hs, hxs⟩ := hx.2.2
    refine ⟨s, hs, fun v hv ↦ ?_⟩
    simp [goodSegment, normalizeGood, hxs v hv]

omit [Fintype V] in
theorem goodWeight_goodSegment {G : Finset V} {x : V → ℝ}
    (hw : 0 < goodWeight G x) (t : I) :
    goodWeight G (goodSegment G t x) =
      (1 - (t : ℝ)) * goodWeight G x + (t : ℝ) := by
  change (∑ v ∈ G, ((1 - (t : ℝ)) * x v + (t : ℝ) * normalizeGood G x v)) = _
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  change (1 - (t : ℝ)) * goodWeight G x +
    (t : ℝ) * goodWeight G (normalizeGood G x) = _
  rw [goodWeight_normalizeGood hw, mul_one]

omit [Fintype V] in
/-- Positive good mass is preserved throughout the homotopy, including
the endpoint where its value is exactly one. -/
theorem goodWeight_goodSegment_pos {G : Finset V} {x : V → ℝ}
    (hw : 0 < goodWeight G x) (t : I) : 0 < goodWeight G (goodSegment G t x) := by
  rw [goodWeight_goodSegment hw]
  by_cases ht : (t : ℝ) = 1
  · simp [ht]
  · have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 ht
    exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr htlt) hw) t.property.1

theorem continuous_goodSegment_on_complement
    (K : Finset (Finset V)) (G : Finset V) :
    Continuous (fun p : I × BarycentricGoodComplement K G ↦
      goodSegment G p.1 p.2.val) := by
  apply continuous_pi
  intro v
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      ((continuous_apply v).comp (continuous_subtype_val.comp continuous_snd))).add
    ((continuous_subtype_val.comp continuous_fst).mul
      ((continuous_apply v).comp
        ((continuous_normalizeGood_on_complement K G).comp continuous_snd)))

/-- A strong deformation retraction of the bad complement onto the good
induced realization: all points already in the good realization stay fixed. -/
def goodDeformationRetraction {K : Finset (Finset V)}
    (hK : FaceClosed K) (G : Finset V) :
    ContinuousMap.HomotopyRel (ContinuousMap.id (BarycentricGoodComplement K G))
      ((goodInclusion K G).comp (goodRetraction hK G))
      (Set.range (goodInclusion K G)) where
  toFun p := ⟨goodSegment G p.1 p.2.val,
    goodSegment_mem_carrier hK p.2.property.1 p.2.property.2 p.1,
    goodWeight_goodSegment_pos p.2.property.2 p.1⟩
  continuous_toFun := (continuous_goodSegment_on_complement K G).subtype_mk _
  map_zero_left x := Subtype.ext (goodSegment_zero G x.val)
  map_one_left x := Subtype.ext (goodSegment_one G x.val)
  prop' t x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact Subtype.ext (goodSegment_eq_self_of_mem_induced y.property t)

/-- The positive-good-mass model of the complement is homotopy equivalent
to the good induced realization, with the actual normalization and inclusion. -/
def goodComplementHomotopyEquiv {K : Finset (Finset V)}
    (hK : FaceClosed K) (G : Finset V) :
    ContinuousMap.HomotopyEquiv (BarycentricGoodComplement K G)
      (barycentricCarrier (inducedFaces K G)) where
  toFun := goodRetraction hK G
  invFun := goodInclusion K G
  left_inv := ⟨(goodDeformationRetraction hK G).toHomotopy.symm⟩
  right_inv := by
    rw [goodRetraction_comp_inclusion]

/-- The literal complement of the bad induced realization is homotopy
equivalent to the good induced realization. No nonemptiness assumption
on either vertex class is needed. -/
def inducedComplementHomotopyEquiv {K : Finset (Finset V)}
    (hK : FaceClosed K) (G : Finset V) :
    ContinuousMap.HomotopyEquiv
      ↥(barycentricCarrier K \ barycentricCarrier (inducedFaces K Gᶜ) : Set (V → ℝ))
      (barycentricCarrier (inducedFaces K G)) :=
  (Homeomorph.setCongr (barycentric_complement_eq_positive_goodWeight hK G)).toHomotopyEquiv.trans
    (goodComplementHomotopyEquiv hK G)

end Simplicial
end AffineTverberg
