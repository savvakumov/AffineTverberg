import AffineTverberg.SphereMiddleHomology

set_option linter.style.header false

/-!
# Vanishing of sphere homology above the sphere dimension

`AffineTverberg.SphereMiddleHomology` proves that the real singular homology of
an `N`-sphere vanishes in the degrees `0 < j < N`.  This file supplies the
complementary range `j > N`, again from the actual simplicial model: the
boundary of the full simplex on `N + 2` vertices has no face of cardinality
larger than `N + 1`, so its oriented chain groups vanish in all degrees above
`N`, and the project's comparison isomorphism transports this to the singular
homology of the norm sphere.

Together with the middle-degree vanishing this shows that a space presented as
an `N`-sphere is acyclic in every positive degree other than `N`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric Set

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V]

omit [Fintype V] [LinearOrder V] in
/-- The oriented chains of a family vanish in degrees where the family has no
face of the corresponding cardinality. -/
theorem subsingleton_chains_of_no_face {K : Finset (Finset V)} {j : ℕ}
    (h : ∀ s ∈ K, s.card ≠ j) : Subsingleton ↥(chains ℝ K j) := by
  constructor
  rintro ⟨c, hc⟩ ⟨d, hd⟩
  have hzero : ∀ (x : Finset V → ℝ), (∀ s, x s ≠ 0 → s ∈ K ∧ s.card = j) → x = 0 := by
    intro x hx
    funext s
    by_contra hs
    obtain ⟨hsK, hscard⟩ := hx s hs
    exact h s hsK hscard
  have hc0 : c = 0 := hzero c hc
  have hd0 : d = 0 := hzero d hd
  simp [hc0, hd0]

/-- The faces of the boundary of the full simplex have cardinality at most
`card V - 1`. -/
theorem card_lt_of_mem_boundaryFamily_univ {s : Finset V}
    (hs : s ∈ boundaryFamily (Finset.univ : Finset V)) : s.card < Fintype.card V := by
  obtain ⟨hsub, hne⟩ := mem_boundaryFamily.mp hs
  have hlt : s ⊂ (Finset.univ : Finset V) := ⟨hsub, fun h => hne (Finset.Subset.antisymm hsub h)⟩
  simpa using Finset.card_lt_card hlt

/-- **Vanishing above the top degree for the simplex boundary.**  The singular
homology of the realization of the boundary of the full simplex vanishes in
every degree `j` with `card V ≤ j + 1`. -/
theorem isZero_realSingularHomology_boundaryFamily_univ_of_gt (j : ℕ)
    (hj : Fintype.card V ≤ j + 1) :
    IsZero ((realSingularHomology j).obj
      (barySpace (boundaryFamily (Finset.univ : Finset V)))) := by
  have hK : FaceClosed (boundaryFamily (Finset.univ : Finset V)) :=
    faceClosed_boundaryFamily _
  have hXzero : IsZero ((simplicialChains hK).X j) := by
    rw [simplicialChains_X hK j]
    have hsub : Subsingleton ↥(chains ℝ (boundaryFamily (Finset.univ : Finset V)) (j + 1)) := by
      refine subsingleton_chains_of_no_face ?_
      intro s hs hcard
      have := card_lt_of_mem_boundaryFamily_univ hs
      omega
    exact ModuleCat.isZero_of_subsingleton _
  have hcycles : IsZero ((simplicialChains hK).cycles j) :=
    IsZero.of_mono ((simplicialChains hK).iCycles j) hXzero
  have hsim : IsZero ((simplicialChains hK).homology j) :=
    IsZero.of_epi ((simplicialChains hK).homologyπ j) hcycles
  have hiso : IsIso (comparisonHomologyMap hK j) := isIso_comparisonHomologyMap hK j
  exact IsZero.of_epi (comparisonHomologyMap hK j) hsim

section Sphere

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Vanishing above the sphere dimension.**  If the ambient space has
dimension `N + 1`, the real singular homology of the unit sphere vanishes in
every degree `j > N`. -/
theorem subsingleton_singularHomology_sphere_of_gt {N : ℕ}
    (hdim : Module.finrank ℝ E = N + 1) (j : ℕ) (hjN : N < j) :
    Subsingleton ((realSingularHomology j).obj (TopCat.of (sphere (0 : E) 1))) := by
  obtain ⟨b⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional
    (ι := Fin (N + 2)) (k := ℝ) (V := E) (P := E) (by simp [hdim])
  have hz : IsZero ((realSingularHomology j).obj
      (barySpace (boundaryFamily (Finset.univ : Finset (Fin (N + 2)))))) :=
    isZero_realSingularHomology_boundaryFamily_univ_of_gt j (by simp; omega)
  have hsub : Subsingleton ((realSingularHomology j).obj
      (TopCat.of ↥(barycentricCarrier (boundaryFamily (Finset.univ : Finset (Fin (N + 2))))))) :=
    ModuleCat.subsingleton_of_isZero hz
  exact (realSingularHomology_subsingleton_iff_of_homotopyEquiv
    (affineBasisBoundarySphereHomeomorph b).toHomotopyEquiv j).mp hsub

/-- The same statement for an arbitrary space presented as a sphere. -/
theorem subsingleton_singularHomology_of_homeomorph_sphere_of_gt
    {X : Type} [TopologicalSpace X] {N : ℕ} (hdim : Module.finrank ℝ E = N + 1)
    (h : X ≃ₜ sphere (0 : E) 1) (j : ℕ) (hjN : N < j) :
    Subsingleton ((realSingularHomology j).obj (TopCat.of X)) :=
  (realSingularHomology_subsingleton_iff_of_homotopyEquiv h.toHomotopyEquiv j).mpr
    (subsingleton_singularHomology_sphere_of_gt hdim j hjN)

end Sphere

end AffineTverberg.Simplicial
