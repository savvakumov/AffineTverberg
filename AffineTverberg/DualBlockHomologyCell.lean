import AffineTverberg.DualBlockLinkHomology
import AffineTverberg.DualBlockRelativeHomology

set_option linter.style.header false

/-!
# Dual blocks of a triangulated sphere are homology cells

Combining the two halves that are now available:

* a dual block is contractible, so the connecting map of the actual pair
  sequence identifies `H_{k+1}(D(s), ∂D(s))` with `H_k(∂D(s))`
  (`dualBlockRelativeHomologyIso`);
* the boundary `∂D(s)` is homeomorphic to the polyhedron of the ordinary link
  of `s`, which is a homology `(N - #s)`-sphere
  (`DualBlockLinkHomology`, `OrdinaryLinkHomology`).

Hence the pair `(D(s), ∂D(s))` is a homology cell: its relative homology
vanishes in every degree at least two except `N + 1 - #s`, where it does not
vanish.  No PL, shellability or ball hypothesis is used: `D(s)` is *not*
claimed to be a topological ball.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg

open AffChain _root_.AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V] {E : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E} {s : Finset V}
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- **Dual blocks are homology cells: the vanishing half.** -/
theorem isZero_dualBlockRelativeHomology_of_sphere
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K) (hsK : s ∈ K) (hs : s.Nonempty)
    {N : ℕ} (hdim : Module.finrank ℝ F = N + 1) (hN : 1 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1) (k : ℕ) (hk : k ≠ 0)
    (hne : k + 1 + s.card ≠ N + 1) :
    IsZero (relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
      (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) (k + 1)) :=
  isZero_dualBlockRelativeHomology_of_isZero hsK hs k hk
    (isZero_realSingularHomology_dualBlockBoundary_of_sphere hgeom hK hsK hs hdim hN e k
      (Nat.pos_of_ne_zero hk) hne)

/-- **Dual blocks are homology cells: the nonvanishing half.**  In the expected
degree `N + 1 - #s` the relative homology of the pair does not vanish. -/
theorem not_isZero_dualBlockRelativeHomology_of_sphere
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K) (hsK : s ∈ K) (hs : s.Nonempty)
    {N : ℕ} (hdim : Module.finrank ℝ F = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1) (k : ℕ) (hk : k ≠ 0)
    (heq : k + 1 + s.card = N + 1) :
    ¬ IsZero (relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
      (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) (k + 1)) := by
  intro hzero
  refine not_isZero_realSingularHomology_dualBlockBoundary_of_sphere hgeom hK hsK hs hdim hN e k
    (Nat.pos_of_ne_zero hk) heq ?_
  exact hzero.of_iso (dualBlockRelativeHomologyIso hsK hs k hk).symm

end AffineTverberg

end
