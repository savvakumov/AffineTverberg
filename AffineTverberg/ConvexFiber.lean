import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option linter.style.header false

/-!
# Contractible nonnegative dual fibers

This file formalizes the strict-separation and contraction argument in lines
410--427 of `affine-tverberg17.tex`.  If a nonempty closed convex set avoids the
origin, then the unit continuous linear functionals which are nonnegative on
that set form a contractible space.
-/

noncomputable section

open Set unitInterval

namespace AffineTverberg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The closed hemisphere of unit dual functionals which are nonnegative on
every point of `C`.  This is the fiber occurring in the proof of
`theorem:zero`. -/
abbrev NonnegativeDualSphere (C : Set E) :=
  {y : StrongDual ℝ E // ‖y‖ = 1 ∧ ∀ z ∈ C, 0 ≤ y z}

/-- Strict separation from the origin, normalized to give a unit functional. -/
theorem exists_strictlyPositive_unitDual {C : Set E}
    (hCconvex : Convex ℝ C) (hCclosed : IsClosed C) (hCne : C.Nonempty)
    (hzero : (0 : E) ∉ C) :
    ∃ y₀ : StrongDual ℝ E, ‖y₀‖ = 1 ∧ ∀ z ∈ C, 0 < y₀ z := by
  obtain ⟨f, u, hfu, hfC⟩ :=
    geometric_hahn_banach_point_closed hCconvex hCclosed hzero
  have hu : 0 < u := by simpa using hfu
  have hfpos : ∀ z ∈ C, 0 < f z := fun z hz ↦ hu.trans (hfC z hz)
  have hfne : f ≠ 0 := by
    obtain ⟨z, hz⟩ := hCne
    intro hf
    simpa [hf] using hfpos z hz
  refine ⟨NormedSpace.normalize f, NormedSpace.norm_normalize hfne, ?_⟩
  intro z hz
  simp only [NormedSpace.normalize, smul_apply, smul_eq_mul]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hfne)) (hfpos z hz)

section Contraction

variable {C : Set E} (y₀ : StrongDual ℝ E)

/-- The unnormalized straight-line homotopy from `y` to the strict separator
`y₀`. -/
private def dualFiberSegment (p : I × NonnegativeDualSphere C) : StrongDual ℝ E :=
  (p.1 : ℝ) • y₀ + (1 - (p.1 : ℝ)) • p.2.1

private theorem dualFiberSegment_ne_zero (hCne : C.Nonempty)
    (hy₀pos : ∀ z ∈ C, 0 < y₀ z) (p : I × NonnegativeDualSphere C) :
    dualFiberSegment y₀ p ≠ 0 := by
  by_cases ht : (p.1 : ℝ) = 0
  · simp only [dualFiberSegment, ht, zero_smul, zero_add, sub_zero, one_smul]
    intro hy
    simpa [hy] using p.2.property.1
  · obtain ⟨z, hz⟩ := hCne
    intro hp
    have heval := congrArg (fun f : StrongDual ℝ E ↦ f z) hp
    have htpos : 0 < (p.1 : ℝ) := lt_of_le_of_ne p.1.property.1 (Ne.symm ht)
    have hone : 0 ≤ 1 - (p.1 : ℝ) := sub_nonneg.mpr p.1.property.2
    have hy : 0 ≤ p.2.1 z := p.2.property.2 z hz
    simp only [dualFiberSegment, add_apply, smul_apply, smul_eq_mul, zero_apply] at heval
    nlinarith [hy₀pos z hz]

private theorem dualFiberSegment_nonnegative
    (hy₀pos : ∀ z ∈ C, 0 < y₀ z) (p : I × NonnegativeDualSphere C)
    (z : E) (hz : z ∈ C) :
    0 ≤ dualFiberSegment y₀ p z := by
  have ht : 0 ≤ (p.1 : ℝ) := p.1.property.1
  have hone : 0 ≤ 1 - (p.1 : ℝ) := sub_nonneg.mpr p.1.property.2
  have hy : 0 ≤ p.2.1 z := p.2.property.2 z hz
  simp only [dualFiberSegment, add_apply, smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ht (hy₀pos z hz).le) (mul_nonneg hone hy)

/-- Normalization of the segment stays in the nonnegative dual sphere. -/
private def dualFiberContraction (hCne : C.Nonempty)
    (hy₀pos : ∀ z ∈ C, 0 < y₀ z) (p : I × NonnegativeDualSphere C) :
    NonnegativeDualSphere C :=
  ⟨NormedSpace.normalize (dualFiberSegment y₀ p),
    NormedSpace.norm_normalize (dualFiberSegment_ne_zero y₀ hCne hy₀pos p),
    fun z hz ↦ by
      simp only [NormedSpace.normalize, smul_apply, smul_eq_mul]
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _))
        (dualFiberSegment_nonnegative y₀ hy₀pos p z hz)⟩

/-- The nonnegative unit-dual fiber of a nonempty closed convex set avoiding
the origin is contractible.  The contraction is the normalized segment to a
strictly positive separator. -/
theorem nonnegativeDualSphere_contractible (hCconvex : Convex ℝ C)
    (hCclosed : IsClosed C) (hCne : C.Nonempty) (hzero : (0 : E) ∉ C) :
    ContractibleSpace (NonnegativeDualSphere C) := by
  obtain ⟨y₀, hy₀norm, hy₀pos⟩ :=
    exists_strictlyPositive_unitDual hCconvex hCclosed hCne hzero
  let c : NonnegativeDualSphere C :=
    ⟨y₀, hy₀norm, fun z hz ↦ (hy₀pos z hz).le⟩
  refine (contractible_iff_id_nullhomotopic (NonnegativeDualSphere C)).2 ⟨c, ⟨?H⟩⟩
  refine
    { toFun := dualFiberContraction y₀ hCne hy₀pos
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · apply Continuous.subtype_mk
    have hsegment : Continuous (dualFiberSegment y₀ :
        I × NonnegativeDualSphere C → StrongDual ℝ E) := by
      unfold dualFiberSegment
      fun_prop
    unfold NormedSpace.normalize
    exact (hsegment.norm.inv₀ fun p ↦
      norm_ne_zero_iff.mpr (dualFiberSegment_ne_zero y₀ hCne hy₀pos p)).smul hsegment
  · intro y
    apply Subtype.ext
    simp [dualFiberContraction, dualFiberSegment,
      NormedSpace.normalize_eq_self_of_norm_eq_one y.property.1]
  · intro y
    apply Subtype.ext
    simp [dualFiberContraction, dualFiberSegment, c,
      NormedSpace.normalize_eq_self_of_norm_eq_one hy₀norm]

end Contraction

end AffineTverberg
