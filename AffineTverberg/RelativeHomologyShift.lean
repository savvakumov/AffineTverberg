import AffineTverberg.RelativeExcision

set_option linter.style.header false

/-!
# The connecting isomorphism for a contractible ambient space

The connecting map in the actual relative homology sequence is an isomorphism
when the two adjacent ambient groups vanish. In a contractible space this
identifies `H_(k+1)(X,A)` with `H_k(A)` for positive `k`. The degree-zero
augmentation issue is deliberately not suppressed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.AffChain

variable {X : TopCat.{0}}

theorem isIso_relDelta_of_isZero (A : Set X) (k : ℕ)
    (hXnext : IsZero ((singChains X).homology (k + 1)))
    (hX : IsZero ((singChains X).homology k)) : IsIso (relDelta A k) := by
  have hπ : relPi A (k + 1) = 0 := hXnext.eq_zero_of_src _
  have hι : relIota A k = 0 := hX.eq_zero_of_tgt _
  have : Mono (relDelta A k) :=
    (ShortComplex.exact_iff_mono _ hπ).mp (relExact_relative A k)
  have : Epi (relDelta A k) :=
    (ShortComplex.exact_iff_epi _ hι).mp (relExact_sub A k)
  exact isIso_of_mono_of_epi _

/-- The isomorphism is the connecting map of the genuine pair sequence. -/
def relativeHomologyShiftIso (A : Set X) (k : ℕ)
    (hXnext : IsZero ((singChains X).homology (k + 1)))
    (hX : IsZero ((singChains X).homology k)) :
    relativeHomology A (k + 1) ≅ (singChains (subSpace A)).homology k := by
  have := isIso_relDelta_of_isZero A k hXnext hX
  exact asIso (relDelta A k)

theorem isIso_relDelta_of_contractible [ContractibleSpace X] (A : Set X)
    (k : ℕ) (hk : k ≠ 0) : IsIso (relDelta A k) := by
  apply isIso_relDelta_of_isZero A k
  · have : Subsingleton ((singChains X).homology (k + 1)) :=
      realSingularHomology_subsingleton_of_contractible X (k + 1) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  · have : Subsingleton ((singChains X).homology k) :=
      realSingularHomology_subsingleton_of_contractible X k hk
    exact ModuleCat.isZero_of_subsingleton _

/-- Positive-degree relative homology of a contractible space is shifted
homology of the actual subspace. -/
def relativeHomologyShiftIsoOfContractible [ContractibleSpace X] (A : Set X)
    (k : ℕ) (hk : k ≠ 0) :
    relativeHomology A (k + 1) ≅ (realSingularHomology k).obj (subSpace A) := by
  have : IsIso (relDelta A k) := isIso_relDelta_of_contractible A k hk
  change relativeHomology A (k + 1) ≅ (singChains (subSpace A)).homology k
  exact asIso (relDelta A k)

/-- If the adjacent subspace groups vanish, the actual absolute-to-relative
projection is an isomorphism. -/
theorem isIso_relPi_of_isZero (A : Set X) (k : ℕ)
    (hAnext : IsZero ((singChains (subSpace A)).homology (k + 1)))
    (hA : IsZero ((singChains (subSpace A)).homology k)) : IsIso (relPi A (k + 1)) := by
  have hι : relIota A (k + 1) = 0 := hAnext.eq_zero_of_src _
  have hδ : relDelta A k = 0 := hA.eq_zero_of_tgt _
  have : Mono (relPi A (k + 1)) :=
    (ShortComplex.exact_iff_mono _ hι).mp (relExact_space A (k + 1))
  have : Epi (relPi A (k + 1)) :=
    (ShortComplex.exact_iff_epi _ hδ).mp (relExact_relative A k)
  exact isIso_of_mono_of_epi _

theorem isIso_relPi_of_contractible (A : Set X) [ContractibleSpace ↥A]
    (k : ℕ) (hk : k ≠ 0) : IsIso (relPi A (k + 1)) := by
  apply isIso_relPi_of_isZero A k
  · have : Subsingleton ((singChains (subSpace A)).homology (k + 1)) :=
      realSingularHomology_subsingleton_of_contractible ↥A (k + 1) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  · have : Subsingleton ((singChains (subSpace A)).homology k) :=
      realSingularHomology_subsingleton_of_contractible ↥A k hk
    exact ModuleCat.isZero_of_subsingleton _

end AffineTverberg.AffChain
