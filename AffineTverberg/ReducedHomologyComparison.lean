import AffineTverberg.ComparisonInduction

set_option linter.style.header false

/-!
# Reduced endpoints of the general comparison

These bridges use the actual oriented augmented complex, not an alternative
definition of acyclicity. Ordinary positive homology vanishing gives reduced
exactness in the shifted degree. At degree zero the augmentation, rather
than ordinary homology vanishing, gives exactness. Nonemptiness handles the
empty-simplex degree separately.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V] {K : Finset (Finset V)}

theorem isReducedAcyclicAt_of_isZero_simplicialHomology (hK : FaceClosed K) (n : ℕ)
    (h : IsZero ((simplicialChains hK).homology (n + 1))) :
    IsReducedAcyclicAt ℝ K (n + 2) :=
  (simplicialChains_exactAt_iff hK n).mp
    ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr h)

/-- The injectivity of the induced augmentation kills all reduced zero cycles. -/
theorem isReducedAcyclicAt_one_of_isIso_augHomology (hK : FaceClosed K)
    (h : IsIso (augHomology (simplicialChains hK) (simplicialAug hK)
      (d_simplicialAug hK))) : IsReducedAcyclicAt ℝ K 1 := by
  let D := simplicialChains hK
  let desc := D.descOpcycles (simplicialAug hK) 1 (by simp) (d_simplicialAug hK)
  have hcomp : IsIso ((D.isoHomologyι₀).hom ≫ desc) := h
  have hdesc : IsIso desc := IsIso.of_isIso_comp_left (D.isoHomologyι₀).hom desc
  have hpd : D.pOpcycles 0 ≫ desc = simplicialAug hK :=
    D.p_descOpcycles (simplicialAug hK) 1 (by simp) (d_simplicialAug hK)
  intro c hc
  let c' : D.X 0 := (⟨c, hc.1⟩ : ↥(chains ℝ K 1))
  have haug : augmentation ℝ V c = 0 := by
    rw [← boundary_apply_empty, hc.2]
    rfl
  have hp : (D.pOpcycles 0).hom c' = 0 := by
    apply (ModuleCat.mono_iff_injective desc).mp inferInstance
    have heval := congrArg (fun f : D.X 0 ⟶ ModuleCat.of ℝ ℝ ↦ f.hom c') hpd
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, map_zero] using
      heval.trans haug
  have hrange := ((D.sc 0).moduleCat_pOpcycles_eq_zero_iff c').mp hp
  change c' ∈ LinearMap.range ((D.d ((ComplexShape.down ℕ).prev 0) 0).hom) at hrange
  rw [show (ComplexShape.down ℕ).prev 0 = 1 by simp] at hrange
  change c' ∈ LinearMap.range (((simplicialChains hK).d 1 0).hom) at hrange
  rw [simplicialChains_d hK 0] at hrange
  change ∃ b : ↥(chains ℝ K 2),
    (chainBoundary ℝ hK 1) b = (⟨c, hc.1⟩ : ↥(chains ℝ K 1)) at hrange
  obtain ⟨b, hb⟩ := hrange
  exact ⟨b.1, b.2, congrArg Subtype.val hb⟩

theorem isReducedAcyclicAt_one_of_isIso_singularAugmentation (hK : FaceClosed K)
    (h : IsIso (realSingularAugmentation (barySpace K))) :
    IsReducedAcyclicAt ℝ K 1 := by
  have hcomp := isIso_comparisonHomologyMap hK 0
  apply isReducedAcyclicAt_one_of_isIso_augHomology hK
  rw [← comparisonHomologyMap_zero_realSingularAugmentation hK]
  change IsIso (comparisonHomologyMap hK 0 ≫ realSingularAugmentation (barySpace K))
  infer_instance

/-- A vertex suffices for exactness in the empty-simplex degree. -/
theorem isReducedAcyclicAt_zero_of_vertex (hK : FaceClosed K) {v : V}
    (hv : ({v} : Finset V) ∈ K) : IsReducedAcyclicAt ℝ K 0 := by
  intro c hc
  have hcc : c ∈ chains ℝ ({v} : Finset V).powerset 0 := by
    intro s hs
    have hcard := (hc.1 s hs).2
    have heq := Finset.card_eq_zero.mp hcard
    exact ⟨by simp [heq], hcard⟩
  obtain ⟨b, hb, hbc⟩ := isReducedAcyclic_powerset (𝕜 := ℝ) (Finset.mem_singleton_self v)
    0 ⟨hcc, hc.2⟩
  exact ⟨b, chains_mono (fun s hs ↦ hK {v} hv s (Finset.mem_powerset.mp hs)) 1 hb, hbc⟩

theorem isReducedAcyclicAt_zero_of_nonempty_realization (hK : FaceClosed K)
    (hne : (barycentricCarrier K).Nonempty) : IsReducedAcyclicAt ℝ K 0 := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨h0, hsum, s, hsK, hsupp⟩ := hx
  have hs : s.Nonempty := by
    by_contra he
    have hs0 := Finset.not_nonempty_iff_eq_empty.mp he
    have hx0 : ∀ v, x v = 0 := fun v ↦ hsupp v (by simp [hs0])
    simp only [hx0, Finset.sum_const_zero] at hsum
    norm_num at hsum
  obtain ⟨v, hv⟩ := hs
  exact isReducedAcyclicAt_zero_of_vertex hK (hK s hsK {v} (Finset.singleton_subset_iff.mpr hv))

end AffineTverberg.Simplicial
