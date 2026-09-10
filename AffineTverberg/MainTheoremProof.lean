import AffineTverberg.MainTheorem
import AffineTverberg.DeletedJoinAlexanderDuality
import AffineTverberg.SimplicialBallZeroReduction
import AffineTverberg.PolytopalGlobalProjection

set_option linter.style.header false

/-!
# Proof of the affine Tverberg main theorem

The statement and its definitions are in `MainTheorem`. This file assembles
the completed proof: deleted-join homology vanishing supplies the
simplicial-ball zero theorem, which gives the simplicial-ball conclusion;
the polytopal conclusion is already proved in `PolytopalGlobalProjection`.

The polytopal case includes every `r ≥ 2`. The simplicial-ball case includes
every `r ≥ 3`; the separately cited `r = 2` ball case is deliberately excluded.
-/

namespace AffineTverberg

/-- **The simplicial-ball case of `theorem:zero`**, in the paper's range
`r = m + 1 ≥ 3`. -/
theorem simplicialBallZeroTheorem : simplicialBallZeroTheoremStatement := by
  intro d m e hd hm K hball φ _hcont hφ
  refine exists_simplicialDeletedJoinPoint_zero_of_ball_deletedJoin_homology hd hm hball φ hφ ?_
  exact isZero_deletedJoin_homology_of_ball hball (by nlinarith) hm

/-- **The affine Tverberg theorem** of the paper: the polytopal half for every
`r ≥ 2`, and the simplicial-ball half for every `r ≥ 3`. -/
theorem mainTheorem : mainTheoremStatement :=
  ⟨polytopalMainTheorem, simplicialBallMainTheoremStatement_of_zero simplicialBallZeroTheorem⟩

end AffineTverberg
