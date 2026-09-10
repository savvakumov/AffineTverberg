import AffineTverberg.ReducedHomologyComparison

set_option linter.style.header false

/-!
# A nonzero fundamental cycle of a simplex boundary

The boundary of the oriented full simplex is a nonzero cycle in its proper
face family. There are no chains one degree higher in that family, so this
cycle cannot bound there. The general comparison transfers this fact to
actual singular homology of the boundary realization. Identifying this
realization with the target sphere is a separate geometric step.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

section OrientedCycle

variable {𝕜 V : Type*} [Field 𝕜] [Fintype V] [LinearOrder V]

/-- The oriented chain consisting of one simplex with coefficient one. -/
def simplexChain (𝕜 : Type*) [Field 𝕜] (s : Finset V) : Finset V → 𝕜 :=
  fun t ↦ if t = s then 1 else 0

omit [Fintype V] in
theorem simplexChain_mem_chains (s : Finset V) :
    simplexChain 𝕜 s ∈ chains 𝕜 s.powerset s.card := by
  intro t ht
  by_cases hts : t = s
  · subst t
    exact ⟨Finset.mem_powerset_self s, rfl⟩
  · simp [simplexChain, hts] at ht

theorem boundary_simplexChain_apply (s t : Finset V) :
    boundary 𝕜 V (simplexChain 𝕜 s) t = boundaryCoeff 𝕜 t s := by
  rw [boundary_eq_boundaryMatrix]
  simp [simplexChain]

theorem boundary_simplexChain_ne_zero {s : Finset V} (hs : s.Nonempty) :
    boundary 𝕜 V (simplexChain 𝕜 s) ≠ 0 := by
  obtain ⟨v, hv⟩ := hs
  have hpos := Finset.card_pos.mpr (show s.Nonempty from ⟨v, hv⟩)
  have hfacet : IsSimplexFacet (s.erase v) s :=
    ⟨Finset.erase_subset v s, by rw [Finset.card_erase_of_mem hv]; omega⟩
  have hcoeff := (boundaryCoeff_ne_zero_iff (𝕜 := 𝕜) (s.erase v) s).mpr hfacet
  intro hz
  apply hcoeff
  rw [← boundary_simplexChain_apply, hz]
  rfl

theorem boundary_simplexChain_mem_cycles {s : Finset V} {n : ℕ} (hs : s.card = n + 1) :
    boundary 𝕜 V (simplexChain 𝕜 s) ∈ cycles 𝕜 (boundaryFamily s) n := by
  have hchain : simplexChain 𝕜 s ∈ chains 𝕜 s.powerset (n + 1) :=
    hs ▸ simplexChain_mem_chains s
  have hbd := boundary_mem_chains (faceClosed_powerset s) hchain
  refine ⟨?_, boundary_boundary_apply _⟩
  intro t ht
  obtain ⟨htpow, htcard⟩ := hbd t ht
  refine ⟨mem_boundaryFamily.mpr ⟨Finset.mem_powerset.mp htpow, ?_⟩, htcard⟩
  intro heq
  subst t
  omega

/-- The top cycle on the boundary of any nonempty simplex does not bound. -/
theorem not_isReducedAcyclicAt_boundaryFamily {s : Finset V} (hs : s.Nonempty) :
    ¬ IsReducedAcyclicAt 𝕜 (boundaryFamily s) (s.card - 1) := by
  have hpos := Finset.card_pos.mpr hs
  have hcycle := boundary_simplexChain_mem_cycles (𝕜 := 𝕜)
    (s := s) (n := s.card - 1) (by omega)
  have hbound : boundaries 𝕜 (boundaryFamily s) (s.card - 1) = ⊥ := by
    apply boundaries_top_eq_bot
    intro t ht
    obtain ⟨hts, hne⟩ := mem_boundaryFamily.mp ht
    have hlt : t.card < s.card :=
      Finset.card_lt_card (lt_of_le_of_ne hts hne)
    omega
  intro hacyc
  have hzero := hacyc hcycle
  rw [hbound, Submodule.mem_bot] at hzero
  exact boundary_simplexChain_ne_zero hs hzero

end OrientedCycle

section SingularHomology

variable {V : Type} [Fintype V] [LinearOrder V] {s : Finset V}

/-- Nonzero ordinary singular homology in the positive-dimensional boundary
degree, from the explicit cycle and the general comparison theorem. -/
theorem not_isZero_singularHomology_boundaryFamily {n : ℕ} (hs : s.card = n + 3) :
    ¬ IsZero ((realSingularHomology (n + 1)).obj (barySpace (boundaryFamily s))) := by
  intro hz
  have hiso := isIso_comparisonHomologyMap (faceClosed_boundaryFamily s) (n + 1)
  have hsim := IsZero.of_mono
    (comparisonHomologyMap (faceClosed_boundaryFamily s) (n + 1)) hz
  have hacyc := isReducedAcyclicAt_of_isZero_simplicialHomology
    (faceClosed_boundaryFamily s) n hsim
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  apply not_isReducedAcyclicAt_boundaryFamily (𝕜 := ℝ) hne
  have hdegree : s.card - 1 = n + 2 := by omega
  rwa [hdegree]

theorem nontrivial_singularHomology_boundaryFamily {n : ℕ} (hs : s.card = n + 3) :
    Nontrivial ((realSingularHomology (n + 1)).obj (barySpace (boundaryFamily s))) := by
  apply not_subsingleton_iff_nontrivial.mp
  intro h
  exact not_isZero_singularHomology_boundaryFamily hs (ModuleCat.isZero_of_subsingleton _)

end SingularHomology

end AffineTverberg.Simplicial
