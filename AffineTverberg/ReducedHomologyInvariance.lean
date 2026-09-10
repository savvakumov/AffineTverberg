import AffineTverberg.SimplicialSingularBridge
import AffineTverberg.AlexanderDualityGeometric

set_option linter.style.header false

/-!
# Reduced acyclicity is invariant under realization homotopy equivalences

The positive degrees use the actual singular comparison. The vertex degree
uses the actual augmentation and its naturality. The empty-simplex degree
is treated separately: the families must contain the empty face, since the
void family and the family consisting only of the empty face have the same
realization but different augmented homology in degree zero.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V] {K : Finset (Finset V)}

theorem barycentricCarrier_nonempty_iff_vertex (hK : FaceClosed K) :
    (barycentricCarrier K).Nonempty ↔ ∃ v, ({v} : Finset V) ∈ K := by
  constructor
  · rintro ⟨x, _, hsum, s, hsK, hsupp⟩
    have hs : s.Nonempty := by
      by_contra h
      have hs0 := Finset.not_nonempty_iff_eq_empty.mp h
      have hx0 : ∀ v, x v = 0 := fun v => hsupp v (by simp [hs0])
      simp only [hx0, Finset.sum_const_zero] at hsum
      norm_num at hsum
    obtain ⟨v, hv⟩ := hs
    exact ⟨v, hK s hsK {v} (Finset.singleton_subset_iff.mpr hv)⟩
  · rintro ⟨v, hv⟩
    refine ⟨Pi.single v 1, ?_⟩
    rw [barycentricCarrier_eq_union]
    exact Set.mem_iUnion₂.mpr ⟨{v}, hv, single_mem_barycentricFace (by simp)⟩

theorem family_eq_singleton_empty_of_empty_realization (hK : FaceClosed K)
    (he : (∅ : Finset V) ∈ K) (hne : ¬ (barycentricCarrier K).Nonempty) :
    K = {∅} := by
  ext s
  simp only [Finset.mem_singleton]
  constructor
  · intro hs
    by_contra h
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr h
    exact hne ((barycentricCarrier_nonempty_iff_vertex hK).mpr
      ⟨v, hK s hs {v} (Finset.singleton_subset_iff.mpr hv)⟩)
  · rintro rfl
    exact he

theorem chains_eq_bot_of_empty_realization (hK : FaceClosed K)
    (hne : ¬ (barycentricCarrier K).Nonempty) (n : ℕ) (hn : 0 < n) :
    chains ℝ K n = ⊥ := by
  apply le_antisymm _ bot_le
  intro c hc
  change c = 0
  funext s
  by_contra hcs
  obtain ⟨hs, hcard⟩ := hc s hcs
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (hcard ▸ hn)
  exact hne ((barycentricCarrier_nonempty_iff_vertex hK).mpr
    ⟨v, hK s hs {v} (Finset.singleton_subset_iff.mpr hv)⟩)

theorem isReducedAcyclicAt_of_empty_realization (hK : FaceClosed K)
    (hne : ¬ (barycentricCarrier K).Nonempty) (n : ℕ) (hn : 0 < n) :
    IsReducedAcyclicAt ℝ K n := by
  intro c hc
  have hc0 : c = 0 := by
    have hmem : c ∈ chains ℝ K n := hc.1
    rw [chains_eq_bot_of_empty_realization hK hne n hn] at hmem
    exact hmem
  exact hc0 ▸ (boundaries ℝ K n).zero_mem

theorem isReducedAcyclicAt_zero_iff_nonempty_realization (hK : FaceClosed K)
    (he : (∅ : Finset V) ∈ K) :
    IsReducedAcyclicAt ℝ K 0 ↔ (barycentricCarrier K).Nonempty := by
  constructor
  · intro h
    by_contra hne
    have hfamily := family_eq_singleton_empty_of_empty_realization hK he hne
    rw [hfamily] at h
    exact not_isReducedAcyclicAt_singleton_empty_zero h
  · exact isReducedAcyclicAt_zero_of_nonempty_realization hK

variable {W : Type} [Fintype W] [LinearOrder W] {J : Finset (Finset W)}

theorem isReducedAcyclicAt_one_of_realization_homotopyEquiv
    (hK : FaceClosed K) (hJ : FaceClosed J)
    (e : ContinuousMap.HomotopyEquiv ↥(barycentricCarrier K) ↥(barycentricCarrier J))
    (h : IsReducedAcyclicAt ℝ K 1) : IsReducedAcyclicAt ℝ J 1 := by
  by_cases hne : (barycentricCarrier K).Nonempty
  · obtain ⟨v, hv⟩ := (barycentricCarrier_nonempty_iff_vertex hK).mp hne
    have haug : IsIso (realSingularAugmentation (barySpace K)) :=
      isIso_realSingularAugmentation_of_simplicial hK
        (isIso_augHomology_of_isReducedAcyclicAt_one hK hv h)
    have hmap : IsIso ((realSingularHomology 0).map (TopCat.ofHom e.invFun)) :=
      (realSingularHomologyIsoOfHomotopyEquiv e.symm 0).isIso_hom
    have haugJ : IsIso (realSingularAugmentation (barySpace J)) := by
      change IsIso (realSingularAugmentation (TopCat.of ↥(barycentricCarrier J)))
      rw [← realSingularAugmentation_naturality (TopCat.ofHom e.invFun)]
      exact @IsIso.comp_isIso _ _ _ _ _ _ _ hmap haug
    exact isReducedAcyclicAt_one_of_isIso_singularAugmentation hJ haugJ
  · apply isReducedAcyclicAt_of_empty_realization hJ _ 1 (by omega)
    rintro ⟨x, hx⟩
    exact hne ⟨(e.invFun ⟨x, hx⟩).val, (e.invFun ⟨x, hx⟩).property⟩

/-- Reduced acyclicity in every cardinality degree is invariant under the
actual homotopy equivalence of realizations. The empty-face assumptions
are necessary only at the augmented degree-zero endpoint. -/
theorem isReducedAcyclicAt_iff_of_realization_homotopyEquiv
    (hK : FaceClosed K) (hJ : FaceClosed J)
    (heK : (∅ : Finset V) ∈ K) (heJ : (∅ : Finset W) ∈ J)
    (e : ContinuousMap.HomotopyEquiv ↥(barycentricCarrier K) ↥(barycentricCarrier J)) (n : ℕ) :
    IsReducedAcyclicAt ℝ K n ↔ IsReducedAcyclicAt ℝ J n := by
  match n with
  | 0 =>
    rw [isReducedAcyclicAt_zero_iff_nonempty_realization hK heK,
      isReducedAcyclicAt_zero_iff_nonempty_realization hJ heJ]
    exact ⟨fun ⟨x, hx⟩ => ⟨(e.toFun ⟨x, hx⟩).val, (e.toFun ⟨x, hx⟩).property⟩,
      fun ⟨x, hx⟩ => ⟨(e.invFun ⟨x, hx⟩).val, (e.invFun ⟨x, hx⟩).property⟩⟩
  | 1 =>
    exact ⟨isReducedAcyclicAt_one_of_realization_homotopyEquiv hK hJ e,
      isReducedAcyclicAt_one_of_realization_homotopyEquiv hJ hK e.symm⟩
  | n + 2 =>
    rw [← isZero_realSingularHomology_barySpace_iff hK n,
      ← isZero_realSingularHomology_barySpace_iff hJ n]
    let iso := realSingularHomologyIsoOfHomotopyEquiv e (n + 1)
    exact ⟨fun h => h.of_iso iso.symm, fun h => h.of_iso iso⟩

end AffineTverberg.Simplicial
