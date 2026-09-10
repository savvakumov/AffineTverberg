import AffineTverberg.SphereHomology

set_option linter.style.header false

/-!
# Vanishing singular homology of a sphere in the middle degrees

`AffineTverberg.Simplicial.nontrivial_singularHomology_sphere` records the
nonvanishing top homology of a norm sphere. For every duality argument one
also needs the complementary fact: the singular homology of an `N`-sphere
vanishes in all degrees `j` with `1 ≤ j < N`.

This is proved here without any new geometric input: the boundary of the full
simplex on `N + 2` vertices has, in every cardinality degree `k` with
`k + 1 < N + 2`, exactly the chains of the full simplex, so it inherits the
cone acyclicity of the full simplex; the project's general simplicial to
singular comparison theorem transfers this to the singular homology of the
barycentric realization, and the gauge homeomorphism of `SphereHomology`
transfers it to the actual norm sphere.
-/

noncomputable section

open Set Metric CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

/-! ### The combinatorial input: a simplex boundary is acyclic below the top -/

section Combinatorial

variable {𝕜 V : Type*} [Field 𝕜] [Fintype V] [LinearOrder V]

/-- Below the cardinality of the vertex set, the chains of the boundary family
of the full simplex are exactly the chains of the full simplex. -/
theorem chains_boundaryFamily_univ (k : ℕ) (hk : k < Fintype.card V) :
    chains 𝕜 (boundaryFamily (Finset.univ : Finset V)) k =
      chains 𝕜 (Finset.univ : Finset V).powerset k := by
  refine le_antisymm (chains_mono (Finset.erase_subset _ _) k) ?_
  intro c hc s hs
  refine ⟨mem_boundaryFamily.mpr ⟨Finset.subset_univ s, ?_⟩, (hc s hs).2⟩
  intro hsu
  have hcard := (hc s hs).2
  rw [hsu, Finset.card_univ] at hcard
  omega

/-- **The boundary of a full simplex is reduced acyclic below its top degree.**
The proof is the equality of chain groups with the acyclic full simplex, in
the two degrees involved. -/
theorem isReducedAcyclicAt_boundaryFamily_univ (k : ℕ) (hk : k + 1 < Fintype.card V) :
    IsReducedAcyclicAt 𝕜 (boundaryFamily (Finset.univ : Finset V)) k := by
  have hne : (Finset.univ : Finset V).Nonempty := by
    rw [← Finset.card_pos, Finset.card_univ]
    omega
  obtain ⟨a, ha⟩ := hne
  have hfull : IsReducedAcyclicAt 𝕜 (Finset.univ : Finset V).powerset k :=
    isReducedAcyclic_powerset ha k
  intro c hc
  have hck : chains 𝕜 (boundaryFamily (Finset.univ : Finset V)) k =
      chains 𝕜 (Finset.univ : Finset V).powerset k :=
    chains_boundaryFamily_univ k (by omega)
  have hck1 : chains 𝕜 (boundaryFamily (Finset.univ : Finset V)) (k + 1) =
      chains 𝕜 (Finset.univ : Finset V).powerset (k + 1) :=
    chains_boundaryFamily_univ (k + 1) hk
  have hcyc : c ∈ cycles 𝕜 (Finset.univ : Finset V).powerset k := by
    refine ⟨?_, hc.2⟩
    rw [← hck]
    exact hc.1
  obtain ⟨d, hd, hdc⟩ := hfull hcyc
  exact ⟨d, by rw [hck1]; exact hd, hdc⟩

end Combinatorial

/-! ### Transfer to the singular homology of the realization -/

section Realization

variable {V : Type} [Fintype V] [LinearOrder V]

/-- Singular homology of the realization of the boundary of the full simplex
vanishes in every positive degree below the top one. -/
theorem isZero_realSingularHomology_boundaryFamily_univ (j : ℕ) (hj : 0 < j)
    (hjc : j + 2 < Fintype.card V) :
    IsZero ((realSingularHomology j).obj
      (barySpace (boundaryFamily (Finset.univ : Finset V)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  have hK : FaceClosed (boundaryFamily (Finset.univ : Finset V)) :=
    faceClosed_boundaryFamily _
  have hacyc : IsReducedAcyclicAt ℝ (boundaryFamily (Finset.univ : Finset V)) (m + 2) :=
    isReducedAcyclicAt_boundaryFamily_univ (m + 2) (by omega)
  have hsim : IsZero ((simplicialChains hK).homology (m + 1)) :=
    isZero_simplicialChains_homology hK m hacyc
  have hiso : IsIso (comparisonHomologyMap hK (m + 1)) := isIso_comparisonHomologyMap hK (m + 1)
  exact IsZero.of_epi (comparisonHomologyMap hK (m + 1)) hsim

end Realization

/-! ### The actual norm sphere -/

section Sphere

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Middle-degree vanishing for the actual norm sphere.** If the ambient
space has dimension `N + 1`, so that the unit sphere is an `N`-sphere, then
its real singular homology vanishes in every degree `j` with `1 ≤ j < N`. -/
theorem subsingleton_singularHomology_sphere_of_lt {N : ℕ}
    (hdim : Module.finrank ℝ E = N + 1) (j : ℕ) (hj : 0 < j) (hjN : j < N) :
    Subsingleton ((realSingularHomology j).obj (TopCat.of (sphere (0 : E) 1))) := by
  obtain ⟨b⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional
    (ι := Fin (N + 2)) (k := ℝ) (V := E) (P := E) (by simp [hdim])
  have hz : IsZero ((realSingularHomology j).obj
      (barySpace (boundaryFamily (Finset.univ : Finset (Fin (N + 2)))))) :=
    isZero_realSingularHomology_boundaryFamily_univ j hj (by simp; omega)
  have hsub : Subsingleton ((realSingularHomology j).obj
      (TopCat.of ↥(barycentricCarrier (boundaryFamily (Finset.univ : Finset (Fin (N + 2))))))) :=
    ModuleCat.subsingleton_of_isZero hz
  exact (realSingularHomology_subsingleton_iff_of_homotopyEquiv
    (affineBasisBoundarySphereHomeomorph b).toHomotopyEquiv j).mp hsub

end Sphere

/-! ### Any space homeomorphic to such a sphere -/

/-- Middle-degree vanishing for an arbitrary space presented as a sphere by an
explicit homeomorphism. This is the form in which the geometric input about
the boundary join is used. -/
theorem subsingleton_singularHomology_of_homeomorph_sphere
    {X : Type} [TopologicalSpace X] {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {N : ℕ} (hdim : Module.finrank ℝ E = N + 1)
    (h : X ≃ₜ sphere (0 : E) 1) (j : ℕ) (hj : 0 < j) (hjN : j < N) :
    Subsingleton ((realSingularHomology j).obj (TopCat.of X)) :=
  (realSingularHomology_subsingleton_iff_of_homotopyEquiv h.toHomotopyEquiv j).mpr
    (subsingleton_singularHomology_sphere_of_lt hdim j hj hjN)

end AffineTverberg.Simplicial
