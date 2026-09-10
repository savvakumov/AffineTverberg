import AffineTverberg.AffineSpanProduct
import AffineTverberg.DiagonalNondegeneracy
import AffineTverberg.UpperEnvelope

set_option linter.style.header false

/-!
# Full-dimensionality of the lifted polytope

This file formalizes Claim `R_y-full-dimensional` in affine-span form.
The factor images satisfy the diagonal relation, affine nondegeneracy makes
a nonzero functional distinguish two factors over one base point, and those
two lifted points give a vertical direction.  Together with affine spanning
of the projected base, this makes `R_y` affinely span the full product.
-/

noncomputable section

open Set

namespace AffineTverberg
namespace CompactConvexProjection

variable {E F V I X : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [AddCommGroup V] [Module ℝ V]
  [Fintype I] [Nonempty I]

/-- The full-dimensionality claim for `R_y`, stated without a numerical
dimension: its affine span is all of `F × ℝ`.

The maps `copy i x` are the copies of `x` in the join, while `factor i x`
are their images under the nondegenerate Sarkaria map. -/
theorem liftedImage_affineSpan_eq_top_of_diagonal_factors
    (A : CompactConvexProjection E F)
    (baseMap : X → F) (factor : I → X → V) (copy : I → X → E)
    (hcopy_mem : ∀ i x, copy i x ∈ A.carrier)
    (hcopy_projection : ∀ i x, A.projection (copy i x) = baseMap x)
    (y : V →ₗ[ℝ] ℝ)
    (hcopy_height : ∀ i x, A.height (copy i x) = y (factor i x))
    (hbaseSpan : affineSpan ℝ (Set.range baseMap) = ⊤)
    (hdiag : ∀ x, ∑ i, factor i x = 0)
    (hfactorSpan : FactorImagesAffinelySpan factor)
    (hy : y ≠ 0) :
    affineSpan ℝ A.liftedImage = ⊤ := by
  let S : Set (F × ℝ) :=
    Set.range fun ix : I × X ↦ (baseMap ix.2, y (factor ix.1 ix.2))
  have hproj : Prod.fst '' S = Set.range baseMap := by
    ext x
    constructor
    · rintro ⟨p, ⟨⟨i, z⟩, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      let i₀ : I := Classical.choice ‹Nonempty I›
      exact ⟨(baseMap z, y (factor i₀ z)), ⟨⟨i₀, z⟩, rfl⟩, rfl⟩
  obtain ⟨x, i, j, hij⟩ :=
    exists_factorValue_ne_of_affinelySpan factor hdiag hfactorSpan y hy
  let p : F × ℝ := (baseMap x, y (factor i x))
  let q : F × ℝ := (baseMap x, y (factor j x))
  have hp : p ∈ S := ⟨(i, x), rfl⟩
  have hq : q ∈ S := ⟨(j, x), rfl⟩
  have hSspan : affineSpan ℝ S = ⊤ :=
    affineSpan_prod_eq_top_of_fst_and_vertical
      (by rw [hproj]; exact hbaseSpan) hp hq rfl hij
  have hsubset : S ⊆ A.liftedImage := by
    rintro _ ⟨⟨i, x⟩, rfl⟩
    refine ⟨copy i x, hcopy_mem i x, ?_⟩
    apply Prod.ext
    · simpa [liftedMap] using hcopy_projection i x
    · simpa [liftedMap] using hcopy_height i x
  apply top_unique
  rw [← hSspan]
  exact affineSpan_mono ℝ hsubset

end CompactConvexProjection
end AffineTverberg
