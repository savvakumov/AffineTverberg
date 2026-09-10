import AffineTverberg.DualBlockDecomposition
import AffineTverberg.RelativeHomologyShift
import AffineTverberg.PuncturedBall

set_option linter.style.header false

/-!
# The relative homology of a dual block pair

A dual block is a geometric cone, hence contractible, so the connecting map of
the actual pair sequence identifies the relative homology of the pair
`(D(s), ∂D(s))` with the shifted homology of the block boundary in every
positive degree.  This is the first half of the *homology cell* property of the
dual blocks; the remaining half is the identification of `∂D(s)` with a link,
which is not claimed here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg

open AffChain _root_.AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [DecidableEq V] {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E} {s : Finset V}

/-- The relative homology of the dual block pair is the shifted homology of the
boundary of the block, in every positive degree. -/
def dualBlockRelativeHomologyIso (hs : s ∈ K) (hsne : s.Nonempty) (k : ℕ) (hk : k ≠ 0) :
    relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
        (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) (k + 1) ≅
      (realSingularHomology k).obj (TopCat.of ↥(dualBlockBoundarySpace K p s)) := by
  haveI : ContractibleSpace ↥(dualBlockSpace K p s) :=
    contractibleSpace_dualBlockSpace hs hsne
  exact relativeHomologyShiftIsoOfContractible _ k hk ≪≫
    realSingularHomologyIsoOfHomotopyEquiv
      (subsetSubtypeHomeomorph
        (dualBlockBoundarySpace_subset K p s)).toHomotopyEquiv k

/-- Consequently the pair is a homology cell in degree `k + 1` exactly when the
boundary of the block is acyclic in degree `k`. -/
theorem isZero_dualBlockRelativeHomology_of_isZero (hs : s ∈ K) (hsne : s.Nonempty)
    (k : ℕ) (hk : k ≠ 0)
    (hbd : IsZero ((realSingularHomology k).obj
      (TopCat.of ↥(dualBlockBoundarySpace K p s)))) :
    IsZero (relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
      (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) (k + 1)) :=
  hbd.of_iso (dualBlockRelativeHomologyIso hs hsne k hk)

end AffineTverberg

end
