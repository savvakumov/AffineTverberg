import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Full affine span from a vertical fiber

This file isolates the linear-algebra step in Claim `R_y-full-dimensional`.
If a subset of `F × ℝ` projects onto an affinely spanning subset of `F`
and contains two different points in one projection fiber, then it affinely
spans the whole product.
-/

noncomputable section

open Set

namespace AffineTverberg

variable {F : Type*} [AddCommGroup F] [Module ℝ F]

/-- An affinely spanning projection together with a nontrivial vertical
fiber forces full affine span in `F × ℝ`. -/
theorem affineSpan_prod_eq_top_of_fst_and_vertical
    {S : Set (F × ℝ)}
    (hproj : affineSpan ℝ (Prod.fst '' S) = ⊤)
    {p q : F × ℝ} (hp : p ∈ S) (hq : q ∈ S)
    (hfst : p.1 = q.1) (hsnd : p.2 ≠ q.2) :
    affineSpan ℝ S = ⊤ := by
  let D : Submodule ℝ (F × ℝ) := vectorSpan ℝ S
  have hprojDirection : vectorSpan ℝ (Prod.fst '' S) = ⊤ := by
    rw [← direction_affineSpan, hproj]
    exact AffineSubspace.direction_top ℝ F F
  have hmap : Submodule.map (LinearMap.fst ℝ F ℝ) D = ⊤ := by
    change Submodule.map ((AffineMap.fst : (F × ℝ) →ᵃ[ℝ] F).linear :
        (F × ℝ) →ₗ[ℝ] F)
      (vectorSpan ℝ S) = ⊤
    rw [AffineMap.map_vectorSpan]
    simpa only [AffineMap.coe_fst] using hprojDirection
  have hvertical : (0, 1) ∈ D := by
    have hpq : p - q ∈ D := by
      exact vsub_mem_vectorSpan ℝ hp hq
    have hscaled := D.smul_mem (p.2 - q.2)⁻¹ hpq
    have hdelta : p.2 - q.2 ≠ 0 := sub_ne_zero.mpr hsnd
    convert hscaled using 1
    ext <;> simp [hfst, hdelta]
  have hD : D = ⊤ := by
    apply top_unique
    intro z _hz
    have hx : z.1 ∈ Submodule.map (LinearMap.fst ℝ F ℝ) D := by
      rw [hmap]
      simp
    obtain ⟨v, hv, hvfst⟩ := hx
    have hcorrection : (0, z.2 - v.2) ∈ D := by
      convert D.smul_mem (z.2 - v.2) hvertical using 1
      ext <;> simp
    have hvadd := D.add_mem hv hcorrection
    convert hvadd using 1
    ext <;> simp_all
  apply top_unique
  intro z _hz
  rw [← AffineSubspace.vsub_right_mem_direction_iff_mem
    (mem_affineSpan ℝ hp)]
  rw [direction_affineSpan]
  change z - p ∈ D
  rw [hD]
  simp

end AffineTverberg
