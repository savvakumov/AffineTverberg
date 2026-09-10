import AffineTverberg.CofaceHomologyCell

set_option linter.style.header false

/-!
# The actual homology line at a maximal face

At a maximal face the coface complex has one chain group: the line spanned
by that simplex. Both neighboring differentials vanish, so the canonical
homology-to-chain identification computes its rank also in ordinary degree
zero. This supplies the zero-dimensional dual-block endpoint.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

variable {V : Type} [LinearOrder V] {K : Finset (Finset V)} {F : Finset V}

theorem cofaceChains_eq_span_of_maximal (hF : F ∈ K)
    (hmax : ∀ t ∈ K, F ⊆ t → t = F) (n : ℕ) (hn : n = F.card) :
    cofaceChains K F n = ℝ ∙ simplexChain ℝ F := by
  apply le_antisymm
  · intro c hc
    have hval : c = c F • simplexChain ℝ F := by
      funext t
      by_cases ht : t = F
      · subst ht
        simp [simplexChain]
      · have hct : c t = 0 := by
          by_contra h
          have hmem := Finset.mem_filter.mp (hc t h).1
          exact ht (hmax t hmem.1 hmem.2)
        simp [simplexChain, ht, hct]
    rw [hval]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    intro t ht
    have heq : t = F := by
      by_contra h
      exact ht (by simp [simplexChain, h])
    subst heq
    exact ⟨Finset.mem_filter.mpr ⟨hF, Finset.Subset.rfl⟩, hn.symm⟩

theorem finrank_cofaceChains_of_maximal (hF : F ∈ K)
    (hmax : ∀ t ∈ K, F ⊆ t → t = F) (n : ℕ) (hn : n = F.card) :
    Module.finrank ℝ ↥(cofaceChains K F n) = 1 := by
  rw [cofaceChains_eq_span_of_maximal hF hmax n hn]
  apply finrank_span_singleton
  intro h
  have := congrFun h F
  simp [simplexChain] at this

variable [Fintype V]

/-- The canonical homology-to-chain isomorphism at a maximal face, in any
ordinary degree where that chain group is supported. -/
def cofaceHomologyMaximalIso (hK : FaceClosed K)
    (hmax : ∀ t ∈ K, F ⊆ t → t = F) (q : ℕ) (hq : q + 1 = F.card) :
    (cofaceComplex hK F).homology q ≅ (cofaceComplex hK F).X q := by
  let C := cofaceComplex hK F
  have hf : (C.sc q).f = 0 := by
    change C.d ((ComplexShape.down ℕ).prev q) q = 0
    rw [show (ComplexShape.down ℕ).prev q = q + 1 by simp]
    exact (isZero_cofaceComplex_X_of_maximal hK hmax (q + 1) (by omega)).eq_zero_of_src _
  have hg : (C.sc q).g = 0 := by
    cases q with
    | zero =>
      change C.d 0 ((ComplexShape.down ℕ).next 0) = 0
      simp
    | succ q =>
      change C.d (q + 1) ((ComplexShape.down ℕ).next (q + 1)) = 0
      rw [show (ComplexShape.down ℕ).next (q + 1) = q by simp]
      exact (isZero_cofaceComplex_X_of_maximal hK hmax q (by omega)).eq_zero_of_tgt _
  exact (ShortComplex.HomologyData.ofZeros (C.sc q) hf hg).left.homologyIso

theorem finrank_cofaceHomology_of_maximal (hK : FaceClosed K) (hF : F ∈ K)
    (hmax : ∀ t ∈ K, F ⊆ t → t = F) (q : ℕ) (hq : q + 1 = F.card) :
    Module.finrank ℝ ((cofaceComplex hK F).homology q) = 1 := by
  rw [(cofaceHomologyMaximalIso hK hmax q hq).toLinearEquiv.finrank_eq]
  exact finrank_cofaceChains_of_maximal hF hmax (q + 1) hq

end AffineTverberg.Simplicial
