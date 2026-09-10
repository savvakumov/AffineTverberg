import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic

set_option linter.style.header false

/-!
# Convex hulls of finite indexed families

A convenience description of the convex hull of the image of a finite index
set: a point lies in it exactly when it is a convex combination with weights
indexed by the index type and supported on the given finite set.  This is the
form used throughout the bad-edge subdivision files.
-/

open scoped BigOperators

namespace AffineTverberg

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι : Type*} [Fintype ι]

/-- Weights for a convex combination of the points `f i`, `i ∈ T`. -/
structure ConvexWeights (T : Finset ι) (c : ι → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ c i
  support : ∀ i, i ∉ T → c i = 0
  sum_one : ∑ i, c i = 1

theorem sum_smul_mem_convexHull_image (f : ι → E) {T : Finset ι} {c : ι → ℝ}
    (hc : ConvexWeights T c) : ∑ i, c i • f i ∈ convexHull ℝ (f '' (T : Set ι)) := by
  classical
  have hsumT : ∑ i ∈ T, c i = 1 := by
    rw [← hc.sum_one]
    exact Finset.sum_subset (Finset.subset_univ T) (fun i _ hi ↦ hc.support i hi)
  have hpt : ∑ i, c i • f i = T.centerMass c f := by
    rw [Finset.centerMass_eq_of_sum_1 _ _ hsumT]
    exact (Finset.sum_subset (Finset.subset_univ T) (fun i _ hi ↦ by
      rw [hc.support i hi, zero_smul])).symm
  rw [hpt]
  refine Finset.centerMass_mem_convexHull T (fun i _ ↦ hc.nonneg i) (by rw [hsumT]; norm_num) ?_
  intro i hi
  exact ⟨i, hi, rfl⟩

theorem mem_convexHull_image_iff (f : ι → E) (T : Finset ι) (x : E) :
    x ∈ convexHull ℝ (f '' (T : Set ι)) ↔
      ∃ c : ι → ℝ, ConvexWeights T c ∧ ∑ i, c i • f i = x := by
  classical
  constructor
  · intro hx
    have hsub : convexHull ℝ (f '' (T : Set ι)) ⊆
        {x | ∃ c : ι → ℝ, ConvexWeights T c ∧ ∑ i, c i • f i = x} := by
      refine convexHull_min ?_ ?_
      · rintro y ⟨i, hi, rfl⟩
        refine ⟨fun j ↦ if j = i then 1 else 0, ⟨fun j ↦ ?_, fun j hj ↦ ?_, ?_⟩, ?_⟩
        · split <;> norm_num
        · rw [ite_eq_right (fun hji : j = i ↦ hj (by rw [hji]; exact hi))]
        · simp
        · simp
      · rintro x ⟨cx, hcx, rfl⟩ y ⟨cy, hcy, rfl⟩ a b ha hb hab
        refine ⟨fun i ↦ a * cx i + b * cy i, ⟨fun i ↦ ?_, fun i hi ↦ ?_, ?_⟩, ?_⟩
        · exact add_nonneg (mul_nonneg ha (hcx.nonneg i)) (mul_nonneg hb (hcy.nonneg i))
        · rw [hcx.support i hi, hcy.support i hi]; ring
        · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            hcx.sum_one, hcy.sum_one, mul_one, mul_one, hab]
        · rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ ↦ by
            rw [add_smul, mul_smul, mul_smul, smul_smul, smul_smul]
    exact hsub hx
  · rintro ⟨c, hc, rfl⟩
    exact sum_smul_mem_convexHull_image f hc

end AffineTverberg
