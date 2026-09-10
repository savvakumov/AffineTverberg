import AffineTverberg.OrdinaryLinkHomology

set_option linter.style.header false

/-!
# The shifted coface comparison including ordinary degree zero

For a nonempty face the coface complex has no empty-simplex term. Its
ordinary degree-zero differential is therefore exactly the zero augmented
differential, not a truncation that changes the homology. This extends the
existing positive-degree comparison with the augmented ordinary link to
every ordinary degree, including the empty-link endpoint at a maximal face.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

variable {V : Type} [LinearOrder V] {K : Finset (Finset V)} {L : Finset V}

theorem cofaceChains_eq_bot_of_lt_card (n : ℕ) (hn : n < L.card) :
    cofaceChains K L n = ⊥ := by
  apply le_antisymm _ bot_le
  intro c hc
  change c = 0
  funext F
  by_contra hF
  obtain ⟨hmem, hcard⟩ := hc F hF
  have hle := Finset.card_le_card (Finset.mem_filter.mp hmem).2
  omega

variable [Fintype V]

theorem cofaceBoundary_one_eq_zero (hK : FaceClosed K) (hL : L.Nonempty)
    {c : Finset V → ℝ} (hc : c ∈ cofaceChains K L 1) :
    cofaceBoundary L c = 0 := by
  have hmem := cofaceBoundary_mem hK L 0 hc
  simpa only [cofaceChains_eq_bot_of_lt_card 0 (Finset.card_pos.mpr hL),
    Submodule.mem_bot] using hmem

/-- The ordinary degree-zero homology uses the actual augmented coface
differential when the chosen face is nonempty. -/
theorem cofaceComplex_exactAt_zero_iff (hK : FaceClosed K) (hL : L.Nonempty) :
    (cofaceComplex hK L).ExactAt 0 ↔ IsCofaceAcyclicAt K L 1 := by
  rw [HomologicalComplex.exactAt_iff' _ 1 0 0 (by simp) (by simp)]
  have hg : (HomologicalComplex.sc' (cofaceComplex hK L) 1 0 0).g = 0 := by
    change (cofaceComplex hK L).d 0 0 = 0
    simp
  rw [ShortComplex.exact_iff_epi _ hg]
  change Epi ((cofaceComplex hK L).d 1 0) ↔ _
  rw [cofaceComplex_d]
  change Epi (ModuleCat.ofHom (cofaceDifferential hK L 1)) ↔ _
  rw [ModuleCat.epi_iff_surjective]
  constructor
  · intro h c hc _
    obtain ⟨d, hd⟩ := h (⟨c, hc⟩ : ↥(cofaceChains K L 1))
    exact ⟨d.val, d.property, congrArg Subtype.val hd⟩
  · intro h c
    obtain ⟨d, hd, hdc⟩ := h c.val c.property
      (cofaceBoundary_one_eq_zero hK hL c.property)
    exact ⟨⟨d, hd⟩, Subtype.ext hdc⟩

/-- Exactness of the coface complex in every ordinary degree, with no
exception at zero. -/
theorem cofaceComplex_exactAt_iff_all (hK : FaceClosed K) (hL : L.Nonempty) (q : ℕ) :
    (cofaceComplex hK L).ExactAt q ↔ IsCofaceAcyclicAt K L (q + 1) := by
  cases q with
  | zero => exact cofaceComplex_exactAt_zero_iff hK hL
  | succ q => exact cofaceComplex_exactAt_iff hK L q

/-- The actual relative coface homology vanishes exactly when the shifted
augmented ordinary-link homology does, including ordinary degree zero. -/
theorem isZero_cofaceHomology_iff_link_all (hK : FaceClosed K) (hL : L.Nonempty)
    (q n : ℕ) (hn : n + L.card = q + 1) :
    IsZero ((cofaceComplex hK L).homology q) ↔
      IsReducedAcyclicAt ℝ (link K L) n := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    cofaceComplex_exactAt_iff_all hK hL q, ← hn, isCofaceAcyclicAt_iff_link]

/-- The same all-degree equivalence for the genuine relative singular
homology of the realized costar pair. -/
theorem isZero_relativeCostarHomology_iff_link_all (hK : FaceClosed K) (hL : L.Nonempty)
    (q n : ℕ) (hn : n + L.card = q + 1) :
    IsZero (AffChain.relativeHomology (subcomplexRealization (costarFamily K L) K) q) ↔
      IsReducedAcyclicAt ℝ (link K L) n := by
  constructor
  · intro h
    exact (isZero_cofaceHomology_iff_link_all hK hL q n hn).mp
      (h.of_iso (cofaceRelativeHomologyIso hK L q))
  · intro h
    exact ((isZero_cofaceHomology_iff_link_all hK hL q n hn).mpr h).of_iso
      (cofaceRelativeHomologyIso hK L q).symm

end AffineTverberg.Simplicial
