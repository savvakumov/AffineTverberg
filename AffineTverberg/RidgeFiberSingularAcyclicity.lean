import AffineTverberg.RidgeFiberComparison

set_option linter.style.header false

/-!
# The complete singular acyclicity range of the ridge fibers

This combines the actual path-connectedness of each fiber with the verified
simplicial-to-singular comparison in positive degrees. The conclusion has no
vertex enumeration or orientation hypotheses: those choices are internal to
the proof. All homology groups are Mathlib's actual singular homology groups.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg

variable {e m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem ridgeFiber_singular_acyclicity
    (L : Finset (CoordinateSpace e)) (Φ : PolytopalJoinAmbient e m →L[ℝ] E)
    (y : DualUnitSphere E) (hL : AffineIndependent ℝ ((↑) : L → CoordinateSpace e))
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    (hcard : 2 ≤ L.card) :
    Nonempty (RidgeIncidenceFiber L Φ y) ∧
      IsIso (realSingularAugmentation (TopCat.of (RidgeIncidenceFiber L Φ y))) ∧
      ∀ n, n ≠ 0 → n + 1 < L.card →
        IsZero ((realSingularHomology n).obj (TopCat.of (RidgeIncidenceFiber L Φ y))) := by
  classical
  have hpc := pathConnectedSpace_ridgeIncidenceFiber L Φ hdiag y hcard
  refine ⟨inferInstance, inferInstance, ?_⟩
  intro n hn hdegree
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  let := Fintype.ofFinite (NonnegativeColoredVertex L (ridgeEval Φ y.val))
  let := linearOrderOfSTO (α := NonnegativeColoredVertex L (ridgeEval Φ y.val)) WellOrderingRel
  exact isZero_ridgeFiberSingularHomology L Φ y hL hdiag hdegree

/-- The actual ridge projection for an affine Sarkaria map is surjective,
and its fibers have all the singular acyclicity needed in the paper's range.
This supplies fiber hypotheses, not a substitute for the proper-map theorem. -/
theorem ridgeIncidence_sarkaria_surjective_and_fibers_singularAcyclic
    {d : ℕ} (L : Finset (CoordinateSpace e))
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hL : AffineIndependent ℝ ((↑) : L → CoordinateSpace e)) (hcard : 2 ≤ L.card) :
    Function.Surjective
        (ridgeIncidenceDualProjection L (simplicialSarkariaMap (m := m) (fun _ ↦ ψ))) ∧
      ∀ y : DualUnitSphere (SarkariaTarget d m),
        IsIso (realSingularAugmentation (TopCat.of
          (RidgeIncidenceFiber L (simplicialSarkariaMap (m := m) (fun _ ↦ ψ)) y))) ∧
        ∀ n, n ≠ 0 → n + 1 < L.card →
          IsZero ((realSingularHomology n).obj (TopCat.of
            (RidgeIncidenceFiber L (simplicialSarkariaMap (m := m) (fun _ ↦ ψ)) y))) := by
  refine ⟨(ridgeIncidence_sarkaria_surjective_and_fibers_pathConnected L ψ hcard).1,
    fun y ↦ ?_⟩
  exact (ridgeFiber_singular_acyclicity L _ y hL
    (sum_simplicialSarkariaMap_copy_eq_zero ψ) hcard).2

end AffineTverberg
