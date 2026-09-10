import AffineTverberg.SphereHomology

set_option linter.style.header false

/-!
# The exact rank of the top homology of a simplex boundary and of a sphere

The previous files only proved that the top singular homology of a simplex
boundary, and hence of a norm sphere, is nonzero.  For the local homology of
a simplicial ball one needs the sharp statement that this homology group is
*one dimensional*.

The computation is purely combinatorial: in the top cardinality degree the
chain groups of the boundary family and of the full powerset agree, the
powerset is reduced acyclic, and the chain group one degree higher is the
line spanned by the fundamental simplex.  Hence the top cycles of the
boundary family are exactly the line spanned by the oriented boundary of that
simplex.  The general comparison theorem and the gauge homeomorphism transfer
this to Mathlib's singular homology of the actual unit sphere.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric
open scoped BigOperators

namespace AffineTverberg.Simplicial

section Combinatorial

variable {𝕜 V : Type*} [Field 𝕜] [Fintype V] [LinearOrder V]

omit [Fintype V] in
/-- In the top cardinality degree the chains of the full simplex form the line
spanned by the fundamental chain. -/
theorem chains_powerset_card_eq_span (s : Finset V) :
    chains 𝕜 s.powerset s.card = 𝕜 ∙ simplexChain 𝕜 s := by
  refine le_antisymm (fun c hc => ?_) ?_
  · have hval : c = c s • simplexChain 𝕜 s := by
      funext t
      by_cases hts : t = s
      · subst hts; simp [simplexChain]
      · have : c t = 0 := by
          by_contra hne
          obtain ⟨hmem, hcard⟩ := hc t hne
          exact hts (Finset.eq_of_subset_of_card_le (Finset.mem_powerset.mp hmem) hcard.ge)
        simp [this, simplexChain, hts]
    rw [hval]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact simplexChain_mem_chains s

/-- The top boundaries of the full simplex form the line spanned by the
oriented boundary of the fundamental chain. -/
theorem boundaries_powerset_eq_span (𝕜 : Type*) [Field 𝕜] {s : Finset V} {n : ℕ}
    (hs : s.card = n + 1) :
    boundaries 𝕜 s.powerset n = 𝕜 ∙ (boundary 𝕜 V (simplexChain 𝕜 s)) := by
  have hchains : chains 𝕜 s.powerset (n + 1) = 𝕜 ∙ simplexChain 𝕜 s := by
    rw [← hs]; exact chains_powerset_card_eq_span s
  rw [boundaries, hchains, Submodule.map_span]
  simp

omit [Fintype V] in
/-- In the top cardinality degree the boundary family and the full powerset
have the same chains. -/
theorem chains_boundaryFamily_eq_chains_powerset {s : Finset V} {n : ℕ} (hs : s.card = n + 1) :
    chains 𝕜 (boundaryFamily s) n = chains 𝕜 s.powerset n := by
  have hmem : ∀ t : Finset V, t.card = n → (t ∈ boundaryFamily s ↔ t ∈ s.powerset) := by
    intro t ht
    rw [mem_boundaryFamily, Finset.mem_powerset]
    constructor
    · exact fun h => h.1
    · refine fun h => ⟨h, ?_⟩
      intro hts
      rw [hts] at ht
      omega
  ext c
  constructor
  · intro hc t htc
    exact ⟨(hmem t (hc t htc).2).mp (hc t htc).1, (hc t htc).2⟩
  · intro hc t htc
    exact ⟨(hmem t (hc t htc).2).mpr (hc t htc).1, (hc t htc).2⟩

/-- **The top cycles of a simplex boundary form a line.** -/
theorem cycles_boundaryFamily_eq_span {s : Finset V} {n : ℕ} (hs : s.card = n + 1) :
    cycles 𝕜 (boundaryFamily s) n = 𝕜 ∙ (boundary 𝕜 V (simplexChain 𝕜 s)) := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hne
  refine le_antisymm ?_ ?_
  · have hcyc : cycles 𝕜 (boundaryFamily s) n = cycles 𝕜 s.powerset n := by
      unfold cycles
      rw [chains_boundaryFamily_eq_chains_powerset hs]
    rw [hcyc, ← boundaries_powerset_eq_span 𝕜 hs]
    exact isReducedAcyclic_powerset (𝕜 := 𝕜) ha n
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact boundary_simplexChain_mem_cycles hs

/-- **The top cycle space of a simplex boundary is one dimensional.** -/
theorem finrank_cycles_boundaryFamily {s : Finset V} {n : ℕ} (hs : s.card = n + 1) :
    Module.finrank 𝕜 (cycles 𝕜 (boundaryFamily s) n) = 1 := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  rw [cycles_boundaryFamily_eq_span hs]
  exact finrank_span_singleton (boundary_simplexChain_ne_zero hne)

end Combinatorial

section Singular

variable {V : Type} [Fintype V] [LinearOrder V]

/-- In the top degree the simplicial chain complex has no incoming
differential, so its homology **is** the cycle module. -/
def simplicialChainsHomologyTopEquiv {K : Finset (Finset V)} (hK : FaceClosed K)
    (j : ℕ) (htop : ∀ t ∈ K, t.card ≤ j + 2) :
    ((simplicialChains hK).homology (j + 1)) ≃ₗ[ℝ] ↥(cycles ℝ K (j + 2)) := by
  have hiso0 : (simplicialChains hK).homology (j + 1) ≅
      ((simplicialChains hK).sc' (j + 2) (j + 1) j).homology :=
    HomologicalComplex.homologyIsoSc' _ (j + 2) (j + 1) j (by simp) (by simp)
  set S := (simplicialChains hK).sc' (j + 2) (j + 1) j with hS
  -- the incoming module vanishes
  have hsub : Subsingleton ↥(chains ℝ K (j + 3)) := by
    constructor
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    have hz : ∀ c : Finset V → ℝ, c ∈ chains ℝ K (j + 3) → c = 0 := by
      intro c hc
      funext t
      by_contra hne
      obtain ⟨hmem, hcard⟩ := hc t hne
      have := htop t hmem
      omega
    simp [hz a ha, hz b hb]
  have hzeroX : IsZero ((simplicialChains hK).X (j + 2)) :=
    ModuleCat.isZero_of_subsingleton (ModuleCat.of ℝ ↥(chains ℝ K (j + 3)))
  have hf : S.f = 0 := hzeroX.eq_zero_of_src _
  -- homology is the cycles
  have hiso1 : S.homology ≅ S.cycles := (S.asIsoHomologyπ hf).symm
  have hiso2 : S.cycles ≅ ModuleCat.of ℝ ↥(LinearMap.ker S.g.hom) := S.moduleCatCyclesIso
  -- identify `S.g` with the chain boundary
  have hg : S.g = ModuleCat.ofHom (chainBoundary ℝ hK (j + 1)) := simplicialChains_d hK j
  -- the kernel is the cycle module
  have hker : LinearMap.ker S.g.hom =
      Submodule.comap (chains ℝ K (j + 2)).subtype (cycles ℝ K (j + 2)) := by
    ext c
    constructor
    · intro hc
      refine ⟨c.2, ?_⟩
      rw [hg] at hc
      exact congrArg Subtype.val hc
    · intro hc
      rw [hg]
      exact Subtype.ext hc.2
  have hequiv : ↥(LinearMap.ker S.g.hom) ≃ₗ[ℝ] ↥(cycles ℝ K (j + 2)) := by
    rw [hker]
    exact Submodule.comapSubtypeEquivOfLe (by
      intro c hc
      exact hc.1)
  exact ((hiso0.trans hiso1).trans hiso2).toLinearEquiv.trans hequiv

/-- **The top singular homology of the realization of a complex of bounded
dimension is the top cycle module.** -/
def realSingularHomologyTopEquiv {K : Finset (Finset V)} (hK : FaceClosed K)
    (j : ℕ) (htop : ∀ t ∈ K, t.card ≤ j + 2) :
    ((realSingularHomology (j + 1)).obj (barySpace K)) ≃ₗ[ℝ] ↥(cycles ℝ K (j + 2)) :=
  letI hiso : IsIso (comparisonHomologyMap hK (j + 1)) := isIso_comparisonHomologyMap hK (j + 1)
  ((@asIso _ _ _ _ (comparisonHomologyMap hK (j + 1)) hiso).toLinearEquiv).symm.trans
    (simplicialChainsHomologyTopEquiv hK j htop)

theorem finrank_realSingularHomology_top {K : Finset (Finset V)} (hK : FaceClosed K)
    (j : ℕ) (htop : ∀ t ∈ K, t.card ≤ j + 2) :
    Module.finrank ℝ ((realSingularHomology (j + 1)).obj (barySpace K)) =
      Module.finrank ℝ (cycles ℝ K (j + 2)) :=
  (realSingularHomologyTopEquiv hK j htop).finrank_eq

/-- The top singular homology of a realization of a bounded dimensional
complex is finite dimensional. -/
theorem finiteDimensional_realSingularHomology_top {K : Finset (Finset V)} (hK : FaceClosed K)
    (j : ℕ) (htop : ∀ t ∈ K, t.card ≤ j + 2) :
    FiniteDimensional ℝ ((realSingularHomology (j + 1)).obj (barySpace K)) := by
  have hfd : FiniteDimensional ℝ ↥(cycles ℝ K (j + 2)) := inferInstance
  exact @LinearEquiv.finiteDimensional ℝ _ _ _ _ _ _ _
    (realSingularHomologyTopEquiv hK j htop).symm hfd

/-- **The top singular homology of a simplex boundary realization is one
dimensional.** -/
theorem finrank_realSingularHomology_boundaryFamily {s : Finset V} {n : ℕ} (hs : s.card = n + 3) :
    Module.finrank ℝ ((realSingularHomology (n + 1)).obj (barySpace (boundaryFamily s))) = 1 := by
  rw [finrank_realSingularHomology_top (faceClosed_boundaryFamily s) n ?_]
  · exact finrank_cycles_boundaryFamily (by omega)
  · intro t ht
    obtain ⟨hts, hne⟩ := mem_boundaryFamily.mp ht
    have := Finset.card_lt_card (lt_of_le_of_ne hts hne)
    omega

end Singular

section Sphere

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The top singular homology of the actual unit sphere of an
`(n + 2)`-dimensional normed space is one dimensional.** -/
theorem finrank_realSingularHomology_sphere {n : ℕ} (hdim : Module.finrank ℝ E = n + 2) :
    Module.finrank ℝ ((realSingularHomology (n + 1)).obj (TopCat.of (sphere (0 : E) 1))) = 1 := by
  obtain ⟨b⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional
    (ι := Fin (n + 3)) (k := ℝ) (V := E) (P := E) (by simp [hdim])
  have he := (realSingularHomologyIsoOfHomotopyEquiv
    (affineBasisBoundarySphereHomeomorph b).toHomotopyEquiv (n + 1)).toLinearEquiv
  rw [← he.finrank_eq]
  exact finrank_realSingularHomology_boundaryFamily
    (s := (Finset.univ : Finset (Fin (n + 3)))) (n := n) (by simp)

/-- The top singular homology of the unit sphere is finite dimensional. -/
theorem finiteDimensional_realSingularHomology_sphere {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 2) :
    FiniteDimensional ℝ ((realSingularHomology (n + 1)).obj (TopCat.of (sphere (0 : E) 1))) := by
  obtain ⟨b⟩ := AffineBasis.exists_affineBasis_of_finiteDimensional
    (ι := Fin (n + 3)) (k := ℝ) (V := E) (P := E) (by simp [hdim])
  have he := (realSingularHomologyIsoOfHomotopyEquiv
    (affineBasisBoundarySphereHomeomorph b).toHomotopyEquiv (n + 1)).toLinearEquiv
  have hfd : FiniteDimensional ℝ ((realSingularHomology (n + 1)).obj
      (barySpace (boundaryFamily (Finset.univ : Finset (Fin (n + 3)))))) :=
    finiteDimensional_realSingularHomology_top (faceClosed_boundaryFamily _) n (by
      intro t ht
      obtain ⟨hts, hne⟩ := mem_boundaryFamily.mp ht
      have := Finset.card_lt_card (lt_of_le_of_ne hts hne)
      simp only [Finset.card_univ, Fintype.card_fin] at this ⊢
      omega)
  exact @LinearEquiv.finiteDimensional ℝ _ _ _ _ _ _ _ he hfd

end Sphere

end AffineTverberg.Simplicial
