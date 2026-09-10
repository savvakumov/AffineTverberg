import AffineTverberg.PuncturedBall

set_option linter.style.header false

/-!
# Punctured homology of the actual simplicial ball

Transport the punctured-ball computation along the homeomorphism required
by the existing IsSimplicialBall definition. These conclusions concern the
actual geometric realization, with no local-star or manifold assumption.
-/

noncomputable section

open CategoryTheory

namespace AffineTverberg.IsSimplicialBall

variable {e n : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  (hball : IsSimplicialBall n K)

include hball

/-- The homology of the actual ball with any one point removed is finite
dimensional in degree n-1. -/
theorem finiteDimensional_punctured (hn : 2 ≤ n) (p : K.space) :
    FiniteDimensional ℝ ((realSingularHomology (n - 1)).obj
      (TopCat.of {q : K.space | q ≠ p})) := by
  let h := hball.homeomorph_closedBall.some
  have hdim : Module.finrank ℝ (CoordinateSpace n) = (n - 2) + 2 := by
    simp only [CoordinateSpace, Module.finrank_pi, Fintype.card_fin]
    omega
  have hdeg : n - 2 + 1 = n - 1 := by omega
  have hf := finiteDimensional_homology_ballPunctured hdim (h p)
  rw [hdeg] at hf
  let he := (realSingularHomologyIsoOfHomotopyEquiv
    (puncturedHomeomorph h p).toHomotopyEquiv (n - 1)).toLinearEquiv
  exact @LinearEquiv.finiteDimensional ℝ _ _ _ _ _ _ _ he.symm hf

/-- The actual geometric ball has punctured homology of rank at most one.
Together with finiteDimensional_punctured, this is a usable upper bound
for the local ridge comparison. -/
theorem finrank_punctured_le_one (hn : 2 ≤ n) (p : K.space) :
    Module.finrank ℝ ((realSingularHomology (n - 1)).obj
      (TopCat.of {q : K.space | q ≠ p})) ≤ 1 := by
  let h := hball.homeomorph_closedBall.some
  have hdim : Module.finrank ℝ (CoordinateSpace n) = (n - 2) + 2 := by
    simp only [CoordinateSpace, Module.finrank_pi, Fintype.card_fin]
    omega
  have hdeg : n - 2 + 1 = n - 1 := by omega
  have hr := finrank_homology_ballPunctured_le_one hdim (h p)
  rw [hdeg] at hr
  let he := (realSingularHomologyIsoOfHomotopyEquiv
    (puncturedHomeomorph h p).toHomotopyEquiv (n - 1)).toLinearEquiv
  rw [he.finrank_eq]
  exact hr

end AffineTverberg.IsSimplicialBall
