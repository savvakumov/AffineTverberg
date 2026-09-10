import AffineTverberg.BarycentricOpenCover

set_option linter.style.header false

/-!
# Open-star contractions for finite facewise incidence spaces

An incidence piece is specified by allowed base vertices and a parameter set.
The base coordinate must be supported on those vertices. Over a nonempty
coordinate-positive open star, horizontal interpolation to its face center
preserves every incidence piece that contains the original point. Consequently
the full preimage is homotopy equivalent to the actual fiber at the center.
This is a direct geometric local input for the first incidence projection;
it makes no assertion of a general proper-map theorem.
-/

noncomputable section

open Set unitInterval

namespace AffineTverberg.Simplicial
namespace BarycentricIncidence

variable {V Y ι : Type*} [Fintype V] [DecidableEq V] [TopologicalSpace Y]
variable (K : Finset (Finset V)) (J : ι → Finset V) (C : ι → Set Y)

/-- The actual union of the support-restricted incidence pieces. -/
def carrier : Set ((V → ℝ) × Y) :=
  {z | z.1 ∈ barycentricCarrier K ∧
    ∃ i, (∀ v, v ∉ J i → z.1 v = 0) ∧ z.2 ∈ C i}

/-- The continuous projection to the base realization. -/
def projection : C(↥(carrier K J C), ↥(barycentricCarrier K)) :=
  ⟨fun z ↦ ⟨z.val.1, z.property.1⟩, by fun_prop⟩

/-- An open-star preimage written with one ambient subtype. -/
def starCarrier (s : Finset V) : Set ((V → ℝ) × Y) :=
  {z | z ∈ carrier K J C ∧ ∀ v ∈ s, 0 < z.1 v}

/-- The exact parameter fiber at the barycenter of `s`. -/
def centerFiber (s : Finset V) : Set Y :=
  {y | ∃ i, s ⊆ J i ∧ y ∈ C i}

variable {K J C}

omit [DecidableEq V] [TopologicalSpace Y] in
theorem subset_allowed_of_star {s : Finset V} {z : (V → ℝ) × Y}
    (hz : z ∈ starCarrier K J C s) {i : ι}
    (hi : ∀ v, v ∉ J i → z.1 v = 0) : s ⊆ J i :=
  subset_support_of_openStar (x := ⟨z.1, hz.1.1⟩) hz.2 hi

/-- Project an entire open-star preimage to the center's parameter fiber. -/
def starRetract (s : Finset V) :
    C(↥(starCarrier K J C s), ↥(centerFiber J C s)) :=
  ⟨fun z ↦ ⟨z.val.2, by
      obtain ⟨i, hi, hy⟩ := z.property.1.2
      exact ⟨i, subset_allowed_of_star z.property hi, hy⟩⟩,
    by fun_prop⟩

omit [TopologicalSpace Y] in
theorem center_mem_star {s : Finset V} (hs : s.Nonempty) (hsK : s ∈ K)
    {y : Y} (hy : y ∈ centerFiber J C s) :
    (faceCenter s, y) ∈ starCarrier K J C s := by
  obtain ⟨i, hsi, hyi⟩ := hy
  have hc := faceCenter_mem_barycentricFace hs
  refine ⟨⟨⟨hc.1, hc.2.1, s, hsK, hc.2.2⟩, i, ?_, hyi⟩,
    fun v hv ↦ faceCenter_pos hv⟩
  intro v hv
  exact hc.2.2 v (fun hvs ↦ hv (hsi hvs))

/-- Insert the fixed center while retaining the parameter. -/
def starSection {s : Finset V} (hs : s.Nonempty) (hsK : s ∈ K) :
    C(↥(centerFiber J C s), ↥(starCarrier K J C s)) :=
  ⟨fun y ↦ ⟨(faceCenter s, y.val), center_mem_star hs hsK y.property⟩,
    by fun_prop⟩

theorem starRetract_comp_section {s : Finset V} (hs : s.Nonempty) (hsK : s ∈ K) :
    (starRetract (K := K) (J := J) (C := C) s).comp (starSection hs hsK) =
      ContinuousMap.id _ := by
  ext y
  rfl

omit [TopologicalSpace Y] in
/-- Horizontal interpolation changes no parameter and crosses no incidence
constraint. Its base also stays in the same coordinate-positive intersection. -/
theorem segment_mem_star {s : Finset V} (hs : s.Nonempty)
    {z : (V → ℝ) × Y} (hz : z ∈ starCarrier K J C s) (t : I) :
    ((1 - (t : ℝ)) • z.1 + (t : ℝ) • faceCenter s, z.2) ∈
      starCarrier K J C s := by
  have hbase := starConvex_ambientOpenStar K hs ⟨hz.1.1, hz.2⟩
    t.property.1 (sub_nonneg.mpr t.property.2) (by ring : (t : ℝ) + (1 - t) = 1)
  rw [add_comm] at hbase
  refine ⟨⟨hbase.1, ?_⟩, hbase.2⟩
  obtain ⟨i, hi, hy⟩ := hz.1.2
  have hsi := subset_allowed_of_star hz hi
  refine ⟨i, ?_, hy⟩
  intro v hv
  have hc : faceCenter s v = 0 :=
    (faceCenter_mem_barycentricFace hs).2.2 v (fun hvs ↦ hv (hsi hvs))
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hi v hv, hc, mul_zero, add_zero]

/-- A deformation from the identity to horizontal retraction onto the fiber. -/
def starHomotopy {s : Finset V} (hs : s.Nonempty) (hsK : s ∈ K) :
    ContinuousMap.Homotopy (ContinuousMap.id ↥(starCarrier K J C s))
      ((starSection hs hsK).comp (starRetract s)) where
  toFun z := ⟨((1 - (z.1 : ℝ)) • z.2.val.1 + (z.1 : ℝ) • faceCenter s, z.2.val.2),
    segment_mem_star hs z.2.property z.1⟩
  continuous_toFun := by fun_prop
  map_zero_left z := by
    apply Subtype.ext
    change ((1 - (0 : ℝ)) • z.val.1 + (0 : ℝ) • faceCenter s, z.val.2) = z.val
    simp
  map_one_left z := by
    apply Subtype.ext
    change ((1 - (1 : ℝ)) • z.val.1 + (1 : ℝ) • faceCenter s, z.val.2) =
      (faceCenter s, z.val.2)
    simp

/-- Every open-star preimage is homotopy equivalent to its actual center
fiber. The parameter sets need not be convex or finite for this assertion. -/
def starHomotopyEquiv {s : Finset V} (hs : s.Nonempty) (hsK : s ∈ K) :
    ContinuousMap.HomotopyEquiv ↥(starCarrier K J C s) ↥(centerFiber J C s) where
  toFun := starRetract s
  invFun := starSection hs hsK
  left_inv := ⟨(starHomotopy hs hsK).symm⟩
  right_inv := by rw [starRetract_comp_section hs hsK]

/-- Identify the horizontal model with the genuine open-star preimage. -/
def starPreimageHomeomorph (s : Finset V) :
    ↥((projection K J C) ⁻¹' openStar K s) ≃ₜ ↥(starCarrier K J C s) where
  toFun z := ⟨z.val.val, z.val.property, z.property⟩
  invFun z := ⟨⟨z.val, z.property.1⟩, z.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [DecidableEq V] in
theorem contractibleSpace_starPreimage {s : Finset V} (hs : s.Nonempty) (hsK : s ∈ K)
    [ContractibleSpace ↥(centerFiber J C s)] :
    ContractibleSpace ↥((projection K J C) ⁻¹' openStar K s) := by
  classical
  have := (starHomotopyEquiv (J := J) (C := C) hs hsK).contractibleSpace
  exact (starPreimageHomeomorph s).contractibleSpace

/-- The center as a point of the base realization. -/
def centerPoint {s : Finset V} (hs : s.Nonempty) (hsK : s ∈ K) :
    ↥(barycentricCarrier K) :=
  ⟨faceCenter s, by
    have hc := faceCenter_mem_barycentricFace hs
    exact ⟨hc.1, hc.2.1, s, hsK, hc.2.2⟩⟩

/-- The parameter set used in the contraction is homeomorphic to the
genuine projection fiber, with no additional fiber-identification premise. -/
def centerFiberHomeomorph {s : Finset V} (hs : s.Nonempty) (hsK : s ∈ K) :
    ↥((projection K J C) ⁻¹' {centerPoint hs hsK}) ≃ₜ ↥(centerFiber J C s) where
  toFun z := ⟨z.val.val.2, by
    obtain ⟨i, hi, hy⟩ := z.val.property.2
    have hz : z.val.val.1 = faceCenter s :=
      congrArg Subtype.val (show projection K J C z.val = centerPoint hs hsK from z.property)
    refine ⟨i, ?_, hy⟩
    intro v hv
    by_contra hvi
    have hzero := hi v hvi
    rw [hz] at hzero
    exact (faceCenter_pos hv).ne' hzero⟩
  invFun y := ⟨⟨(faceCenter s, y.val), (center_mem_star hs hsK y.property).1⟩, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg Subtype.val
        (show projection K J C z.val = centerPoint hs hsK from z.property)).symm
    · rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [DecidableEq V] in
/-- Contractibility of the genuine fibers gives contractibility of every
nonempty open-star preimage for this facewise incidence model. -/
theorem contractibleSpace_starPreimage_of_fibers
    (hfib : ∀ x : ↥(barycentricCarrier K),
      ContractibleSpace ↥((projection K J C) ⁻¹' {x}))
    {s : Finset V} (hs : s.Nonempty) (hsK : s ∈ K) :
    ContractibleSpace ↥((projection K J C) ⁻¹' openStar K s) := by
  classical
  have := hfib (centerPoint hs hsK)
  have := (centerFiberHomeomorph (J := J) (C := C) hs hsK).symm.contractibleSpace
  exact contractibleSpace_starPreimage hs hsK

end BarycentricIncidence
end AffineTverberg.Simplicial
