import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

set_option linter.style.header false

/-!
# Diagonal relations and nondegeneracy

This file formalizes the algebraic contradiction in lines 576--589 of
`affine-tverberg17.tex`.  If a linear functional has the same value `β(x)`
on every factor over `x`, the diagonal sum relation forces `β = 0`.  If the
union of the factor images affinely spans the target, the functional itself
must then vanish.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg

section Diagonal

variable {I X V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The union of all factor images, indexed as the range of a function on
`I × X`. -/
def factorRange (factor : I → X → V) : Set V :=
  Set.range fun p : I × X ↦ factor p.1 p.2

/-- Linear nondegeneracy of a family of factor maps. -/
def FactorImagesLinearlySpan (factor : I → X → V) : Prop :=
  Submodule.span ℝ (factorRange factor) = ⊤

/-- The nondegeneracy condition used in the paper: the factor images
affinely span the whole target. -/
def FactorImagesAffinelySpan (factor : I → X → V) : Prop :=
  affineSpan ℝ (factorRange factor) = ⊤

/-- Affine spanning implies linear spanning for a vector-space target. -/
theorem factorImagesLinearlySpan_of_affinelySpan
    {factor : I → X → V} (hspan : FactorImagesAffinelySpan factor) :
    FactorImagesLinearlySpan factor := by
  apply top_unique
  intro v _hv
  apply affineSpan_subset_span
  rw [hspan]
  simp

/-- If the value of a linear functional on every factor over `x` is a
common scalar `β(x)`, the diagonal relation forces that scalar to be zero. -/
theorem commonFactorValue_eq_zero
    [Fintype I] [Nonempty I]
    (factor : I → X → V)
    (hdiag : ∀ x, ∑ i, factor i x = 0)
    (y : V →ₗ[ℝ] ℝ) (β : X → ℝ)
    (hcommon : ∀ i x, y (factor i x) = β x) :
    ∀ x, β x = 0 := by
  intro x
  have hsum : ∑ i : I, y (factor i x) = 0 := by
    rw [← map_sum, hdiag, map_zero]
  have hmultiple : Fintype.card I • β x = 0 := by
    simpa [hcommon] using hsum
  exact (nsmul_eq_zero_iff_right Fintype.card_ne_zero).mp hmultiple

/-- A functional vanishing on a linearly spanning family of factor images
is the zero functional. -/
theorem linearMap_eq_zero_of_factorRange
    (factor : I → X → V) (y : V →ₗ[ℝ] ℝ)
    (hspan : FactorImagesLinearlySpan factor)
    (hzero : ∀ i x, y (factor i x) = 0) :
    y = 0 := by
  have hrange : factorRange factor ⊆ LinearMap.ker y := by
    rintro v ⟨⟨i, x⟩, rfl⟩
    exact hzero i x
  have hspan_le : Submodule.span ℝ (factorRange factor) ≤ LinearMap.ker y :=
    Submodule.span_le.mpr hrange
  ext v
  have hvspan : v ∈ Submodule.span ℝ (factorRange factor) := by
    rw [hspan]
    simp
  exact hspan_le hvspan

/-- Under the diagonal relation and affine nondegeneracy, a nonzero linear
functional cannot factor through the diagonal projection with one common
value on all factors. -/
theorem no_commonFactorValue_of_affinelySpan
    [Fintype I] [Nonempty I]
    (factor : I → X → V)
    (hdiag : ∀ x, ∑ i, factor i x = 0)
    (hspan : FactorImagesAffinelySpan factor)
    (y : V →ₗ[ℝ] ℝ) (hy : y ≠ 0) (β : X → ℝ) :
    ¬ ∀ i x, y (factor i x) = β x := by
  intro hcommon
  have hβ := commonFactorValue_eq_zero factor hdiag y β hcommon
  apply hy
  apply linearMap_eq_zero_of_factorRange factor y
    (factorImagesLinearlySpan_of_affinelySpan hspan)
  intro i x
  rw [hcommon i x, hβ x]

/-- Equivalently, a nonzero functional must distinguish two factors over
at least one base point.  These two values produce the nontrivial vertical
fiber in the lifted polytope `R_y`. -/
theorem exists_factorValue_ne_of_affinelySpan
    [Fintype I] [Nonempty I]
    (factor : I → X → V)
    (hdiag : ∀ x, ∑ i, factor i x = 0)
    (hspan : FactorImagesAffinelySpan factor)
    (y : V →ₗ[ℝ] ℝ) (hy : y ≠ 0) :
    ∃ x i j, y (factor i x) ≠ y (factor j x) := by
  by_contra hne
  push Not at hne
  let i₀ : I := Classical.choice ‹Nonempty I›
  exact no_commonFactorValue_of_affinelySpan factor hdiag hspan y hy
    (fun x ↦ y (factor i₀ x)) fun i x ↦ hne x i i₀

end Diagonal

section ContinuousDiagonal

variable {I X V : Type*} [Fintype I] [Nonempty I]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Continuous-linear version for the unit functional `y` used in the
definition of `λ_y`. -/
theorem no_commonFactorValue_of_affinelySpan_continuous
    (factor : I → X → V)
    (hdiag : ∀ x, ∑ i, factor i x = 0)
    (hspan : FactorImagesAffinelySpan factor)
    (y : StrongDual ℝ V) (hy : y ≠ 0) (β : X → ℝ) :
    ¬ ∀ i x, y (factor i x) = β x := by
  exact no_commonFactorValue_of_affinelySpan factor hdiag hspan
    y.toLinearMap (by
      intro hzero
      apply hy
      ext v
      exact LinearMap.congr_fun hzero v) β

end ContinuousDiagonal

end AffineTverberg
