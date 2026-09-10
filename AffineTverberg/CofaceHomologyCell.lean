import AffineTverberg.CofaceRelativeNaturality
import AffineTverberg.CofaceOrientationClasses

set_option linter.style.header false

/-!
# The complete local relative homology calculation

Restriction from a face to a maximal coface is a quasi-isomorphism in every
degree. At a maximal face the coface complex is concentrated in that face's
dimension. This proves vanishing in ALL other ordinary degrees, including
zero and one, without a separate augmentation argument. Together with the
global-cycle generators this gives the complete relative homology-cell
property needed before removing the face from the coface chains.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.Simplicial

variable {V : Type} [LinearOrder V] {K : Finset (Finset V)} {F : Finset V}

theorem cofaceChains_eq_bot_of_maximal
    (hmax : ∀ t ∈ K, F ⊆ t → t = F) (n : ℕ) (hn : n ≠ F.card) :
    cofaceChains K F n = ⊥ := by
  apply le_antisymm _ bot_le
  intro c hc
  change c = 0
  funext t
  by_contra hct
  obtain ⟨ht, hcard⟩ := hc t hct
  obtain ⟨htK, hFt⟩ := Finset.mem_filter.mp ht
  exact hn (hcard.symm.trans (congrArg Finset.card (hmax t htK hFt)))

variable [Fintype V]

/-- A maximal face has no coface chains in any other dimension. -/
theorem isZero_cofaceComplex_X_of_maximal (hK : FaceClosed K)
    (hmax : ∀ t ∈ K, F ⊆ t → t = F) (q : ℕ) (hq : q + 1 ≠ F.card) :
    IsZero ((cofaceComplex hK F).X q) := by
  change IsZero (ModuleCat.of ℝ ↥(cofaceChains K F (q + 1)))
  rw [cofaceChains_eq_bot_of_maximal hmax (q + 1) hq]
  exact ModuleCat.isZero_of_subsingleton _

theorem isZero_cofaceHomology_of_maximal (hK : FaceClosed K)
    (hmax : ∀ t ∈ K, F ⊆ t → t = F) (q : ℕ) (hq : q + 1 ≠ F.card) :
    IsZero ((cofaceComplex hK F).homology q) := by
  have hX := isZero_cofaceComplex_X_of_maximal hK hmax q hq
  have hcycles : IsZero ((cofaceComplex hK F).cycles q) :=
    IsZero.of_mono ((cofaceComplex hK F).iCycles q) hX
  exact IsZero.of_epi ((cofaceComplex hK F).homologyπ q) hcycles

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- One maximal coface computes all local degrees, including zero and one. -/
theorem isZero_cofaceHomology_of_maximal_coface (hK : FaceClosed K)
    {L : Finset V} (hLF : L ⊆ F) (hF : F ∈ K) (hLne : L.Nonempty)
    (hmax : ∀ t ∈ K, F ⊆ t → t = F)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (q : ℕ) (hq : q + 1 ≠ F.card) :
    IsZero ((cofaceComplex hK L).homology q) := by
  have := quasiIso_cofaceTransition_of_homeomorph_sphere hK hLF hF hLne e
  let eH := asIso (HomologicalComplex.homologyMap (cofaceTransition hK hLF) q)
  exact (isZero_cofaceHomology_of_maximal hK hmax q hq).of_iso eH

/-- Local relative homology of a pure triangulated sphere vanishes off the ambient top degree. -/
theorem isZero_cofaceHomology_of_pure_sphere (hK : FaceClosed K) (N : ℕ)
    (htop : ∀ t ∈ K, t.card ≤ N + 1)
    (hext : ∀ L ∈ K, ∃ F ∈ K, L ⊆ F ∧ F.card = N + 1)
    {L : Finset V} (hL : L ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (q : ℕ) (hq : q ≠ N) :
    IsZero ((cofaceComplex hK L).homology q) := by
  obtain ⟨F, hF, hLF, hcard⟩ := hext L hL
  have hmax : ∀ t ∈ K, F ⊆ t → t = F := by
    intro t ht hFt
    exact (Finset.eq_of_subset_of_card_le hFt (by rw [hcard]; exact htop t ht)).symm
  exact isZero_cofaceHomology_of_maximal_coface hK hLF hF hLne hmax e q (by omega)

/-- The full homology-cell property: all off-top groups vanish, and the top group is a line. -/
theorem coface_homology_cell_of_pure_sphere (hK : FaceClosed K) (k : ℕ)
    (htop : ∀ t ∈ K, t.card ≤ k + 2)
    (hext : ∀ L ∈ K, ∃ F ∈ K, L ⊆ F ∧ F.card = k + 2)
    {L : Finset V} (hL : L ∈ K) (hLne : L.Nonempty)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (hdim : Module.finrank ℝ E = k + 2) (hk : k ≠ 0) :
    (∀ q : ℕ, q ≠ k + 1 → IsZero ((cofaceComplex hK L).homology q)) ∧
      Module.finrank ℝ ((cofaceComplex hK L).homology (k + 1)) = 1 :=
  ⟨fun q hq => isZero_cofaceHomology_of_pure_sphere hK (k + 1) htop hext hL hLne e q hq,
    finrank_coface_top_homology hK htop hL hLne e hdim hk⟩

end AffineTverberg.Simplicial
