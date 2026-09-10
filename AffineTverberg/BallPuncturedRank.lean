import AffineTverberg.PuncturedBall

set_option linter.style.header false

/-!
# The exact local homology rank at an interior point of a closed ball

`AffineTverberg.PuncturedBall` proves that the singular homology of the closed
unit ball of an `(n + 2)`-dimensional normed space, punctured at any point, has
rank at most one in degree `n + 1`, and that it vanishes at a boundary point.

Here the interior case is sharpened to an equality: the punctured ball at an
interior point has homology of rank exactly one.  The lower bound comes from
the other exactness statement of the same Mayer-Vietoris sequence: the
connecting map into `Hₙ₊₁(A ∩ B)` starts at `Hₙ₊₂` of the contractible ball,
so it vanishes, and `Hₙ₊₁` of the small convex neighbourhood `B` vanishes as
well; hence `Hₙ₊₁(A ∩ B) → Hₙ₊₁(A)` is injective, and `A ∩ B` is homotopy
equivalent to a sphere of rank one.

Consequently the local homology distinguishes interior points from boundary
points of a closed ball: rank one versus rank zero.  This is what makes the
"homological boundary" of a space a topological invariant.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set

namespace AffineTverberg

section Ball

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The local homology at an interior point of the ball has rank at least
one**, by Mayer-Vietoris injectivity and the rank of the sphere. -/
theorem one_le_finrank_homology_ballPunctured_of_norm_lt_one {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 2)
    (p : ↥(closedBall (0 : E) 1)) (hp : ‖(p : E)‖ < 1) :
    1 ≤ Module.finrank ℝ ((realSingularHomology (n + 1)).obj
      (TopCat.of ↥(ballPunctured p))) := by
  classical
  set x : E := (p : E) with hx
  set ε : ℝ := (1 - ‖x‖) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  have hsubset : puncturedNbhd x ε ⊆ closedBall (0 : E) 1 := by
    rintro z ⟨-, hz⟩
    have htri : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
      have := norm_add_le (z - x) x
      simpa using this
    rw [hεdef] at hz
    rw [mem_closedBall_zero_iff]
    linarith
  set A : Set ↥(closedBall (0 : E) 1) := ballPunctured p with hA
  set B : Set ↥(closedBall (0 : E) 1) := {q | ‖(q : E) - x‖ < ε} with hB
  have hAopen : IsOpen A := isOpen_ballPunctured p
  have hBopen : IsOpen B := by
    have hcont : Continuous fun q : ↥(closedBall (0 : E) 1) => ‖(q : E) - x‖ :=
      continuous_norm.comp (continuous_subtype_val.sub continuous_const)
    exact isOpen_lt hcont continuous_const
  have hcov : ∀ q : ↥(closedBall (0 : E) 1), q ∈ A ∨ q ∈ B := by
    intro q
    by_cases h : q = p
    · refine Or.inr ?_
      change ‖(q : E) - x‖ < ε
      rw [h, ← hx, sub_self, norm_zero]
      exact hε
    · exact Or.inl h
  -- the ball is contractible, so its homology vanishes in every positive degree
  have hballne : (closedBall (0 : E) 1).Nonempty := ⟨0, by simp⟩
  have : ContractibleSpace ↥(closedBall (0 : E) 1) :=
    (convex_closedBall (0 : E) 1).contractibleSpace hballne
  have hXzero : IsZero ((realSingularHomology (n + 2)).obj
      (TopCat.of ↥(closedBall (0 : E) 1))) := by
    have : Subsingleton ((realSingularHomology (n + 2)).obj
        (TopCat.of ↥(closedBall (0 : E) 1))) :=
      realSingularHomology_subsingleton_of_contractible
        (↥(closedBall (0 : E) 1)) (n + 2) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  -- the small neighbourhood is convex, hence contractible
  have hBeq : B = Subtype.val ⁻¹' (closedBall (0 : E) 1 ∩ ball x ε) := by
    ext q
    constructor
    · intro hq
      exact ⟨q.2, mem_ball_iff_norm.mpr hq⟩
    · rintro ⟨-, hq⟩
      exact mem_ball_iff_norm.mp hq
  have hBne : (closedBall (0 : E) 1 ∩ ball x ε).Nonempty :=
    ⟨x, mem_closedBall_zero_iff.mpr (le_of_lt hp), by simp [hε]⟩
  have hBconv : Convex ℝ (closedBall (0 : E) 1 ∩ ball x ε) :=
    (convex_closedBall (0 : E) 1).inter (convex_ball x ε)
  have hBhomeo : ↥B ≃ₜ ↥(closedBall (0 : E) 1 ∩ ball x ε) :=
    (Homeomorph.setCongr hBeq).trans (subsetSubtypeHomeomorph Set.inter_subset_left)
  have : ContractibleSpace ↥(closedBall (0 : E) 1 ∩ ball x ε) :=
    hBconv.contractibleSpace hBne
  have hBcontr : ContractibleSpace ↥B := hBhomeo.toHomotopyEquiv.contractibleSpace
  have hBzero : IsZero ((realSingularHomology (n + 1)).obj (TopCat.of ↥B)) := by
    have : Subsingleton ((realSingularHomology (n + 1)).obj (TopCat.of ↥B)) :=
      realSingularHomology_subsingleton_of_contractible ↥B (n + 1) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  -- the intersection is a punctured neighbourhood, homotopy equivalent to a sphere
  have hinter : A ∩ B = Subtype.val ⁻¹' (puncturedNbhd x ε) := by
    ext q
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun hq => h1 (Subtype.ext (by rw [hq, hx])), h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun hq => h1 (by rw [hq, hx]), h2⟩
  have hhomeo : ↥(A ∩ B) ≃ₜ ↥(puncturedNbhd x ε) :=
    (Homeomorph.setCongr hinter).trans (subsetSubtypeHomeomorph hsubset)
  have hequiv : ContinuousMap.HomotopyEquiv ↥(A ∩ B) ↥(sphere (0 : E) 1) :=
    hhomeo.toHomotopyEquiv.trans (puncturedNbhdHomotopyEquiv x ε hε)
  have hiso := (realSingularHomologyIsoOfHomotopyEquiv hequiv (n + 1)).toLinearEquiv
  have hrank : Module.finrank ℝ ((realSingularHomology (n + 1)).obj
      (TopCat.of ↥(A ∩ B))) = 1 := by
    rw [hiso.finrank_eq]
    exact Simplicial.finrank_realSingularHomology_sphere (E := E) (n := n) hdim
  have hfdA : FiniteDimensional ℝ ((realSingularHomology (n + 1)).obj (TopCat.of ↥A)) :=
    (finiteDimensional_and_finrank_homology_ballPunctured_of_norm_lt_one hdim p hp).1
  have hle := AffChain.finrank_homology_inter_le_of_cover
    (X := TopCat.of ↥(closedBall (0 : E) 1)) A B hAopen hBopen hcov (n + 1) hXzero hBzero
  rw [hrank] at hle
  exact hle

/-- **The local homology at an interior point of the ball has rank exactly
one.** -/
theorem finrank_homology_ballPunctured_of_norm_lt_one_eq_one {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 2)
    (p : ↥(closedBall (0 : E) 1)) (hp : ‖(p : E)‖ < 1) :
    Module.finrank ℝ ((realSingularHomology (n + 1)).obj
      (TopCat.of ↥(ballPunctured p))) = 1 :=
  le_antisymm (finrank_homology_ballPunctured_of_norm_lt_one hdim p hp)
    (one_le_finrank_homology_ballPunctured_of_norm_lt_one hdim p hp)

/-- The punctured ball at an interior point has nontrivial homology; at a
boundary point it is subsingleton.  This is the homological detection of the
boundary of a ball. -/
theorem subsingleton_homology_ballPunctured_iff {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 2) (p : ↥(closedBall (0 : E) 1)) :
    Subsingleton ((realSingularHomology (n + 1)).obj (TopCat.of ↥(ballPunctured p))) ↔
      ‖(p : E)‖ = 1 := by
  constructor
  · intro hsub
    by_contra hne
    have hlt : ‖(p : E)‖ < 1 := lt_of_le_of_ne (mem_closedBall_zero_iff.mp p.2) hne
    have h1 := finrank_homology_ballPunctured_of_norm_lt_one_eq_one hdim p hlt
    rw [Module.finrank_zero_of_subsingleton] at h1
    exact zero_ne_one h1
  · intro hp
    have hcontr := contractibleSpace_ballPunctured_of_norm_eq_one p hp
    exact realSingularHomology_subsingleton_of_contractible
      (↥(ballPunctured p)) (n + 1) (by omega)

end Ball

end AffineTverberg
