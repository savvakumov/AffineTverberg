import AffineTverberg.SimplicialHomology

set_option linter.style.header false

/-!
# The mod two fundamental cycle of a pure complex

Over a field of characteristic two all incidence signs are `1`, so the sum of
all top simplices of a pure complex is a chain whose boundary at a
codimension one face `f` is the *number* of top simplices having `f` as a
facet, reduced mod two.

Consequently a pure `n`-complex in which every codimension one face lies in an
even number of top simplices carries a nonzero top cycle, hence has nonvanishing
reduced homology over a field of characteristic two.  Contrapositively, a pure
complex whose reduced homology vanishes in the top degree over such a field has
a codimension one face contained in an *odd* number of top simplices; combined
with an upper bound of two on the number of such simplices this produces a face
contained in exactly one top simplex, that is, a free (boundary) ridge.

This isolates the combinatorial content of boundary-ridge existence. The
comparison with actual singular homology over `ZMod 2` is supplied by
`CoefficientComparisonInduction.lean`; `BoundaryRidgeExistence.lean` applies
it to the ball. Characteristic two avoids an orientability hypothesis.
-/

noncomputable section

open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {𝕜 V : Type*} [Field 𝕜] [Fintype V] [LinearOrder V]

/-- The number of `n`-vertex simplices of `K` having `f` as a codimension one
face.  The predicate is `IsSimplexFacet f s` spelled out, so that it is
decidable. -/
def facetCount (K : Finset (Finset V)) (n : ℕ) (f : Finset V) : ℕ :=
  ((topSimplices K n).filter (fun s => f ⊆ s ∧ f.card + 1 = s.card)).card

omit [Fintype V] in
theorem mem_filter_facetCount {K : Finset (Finset V)} {n : ℕ} {f s : Finset V} :
    s ∈ (topSimplices K n).filter (fun s => f ⊆ s ∧ f.card + 1 = s.card)
      ↔ s ∈ topSimplices K n ∧ IsSimplexFacet f s := Finset.mem_filter

/-- The mod two fundamental chain of a pure complex: the sum of all its
`n`-vertex simplices, each with coefficient one. -/
def fundamentalChain (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (n : ℕ) :
    Finset V → 𝕜 :=
  fun t => if t ∈ topSimplices K n then 1 else 0

omit [Fintype V] in
theorem fundamentalChain_mem_chains (K : Finset (Finset V)) (n : ℕ) :
    fundamentalChain 𝕜 K n ∈ chains 𝕜 K n := by
  intro s hs
  by_cases h : s ∈ topSimplices K n
  · exact ⟨(mem_topSimplices.mp h).1, (mem_topSimplices.mp h).2⟩
  · simp [fundamentalChain, h] at hs

omit [Fintype V] in
/-- The fundamental chain is nonzero as soon as there is a top simplex. -/
theorem fundamentalChain_ne_zero {K : Finset (Finset V)} {n : ℕ}
    (h : (topSimplices K n).Nonempty) : fundamentalChain 𝕜 K n ≠ 0 := by
  obtain ⟨s, hs⟩ := h
  intro hzero
  have h1 := congrFun hzero s
  simp only [fundamentalChain, Pi.zero_apply, hs, ite_true] at h1
  exact one_ne_zero h1

/-- The vertices which can be added to `f` inside a top simplex are in bijection
with the top simplices having `f` as a facet. -/
theorem card_filter_insert_eq_facetCount (K : Finset (Finset V)) (n : ℕ) (f : Finset V) :
    ((fᶜ : Finset V).filter (fun v => insert v f ∈ topSimplices K n)).card
      = facetCount K n f := by
  rw [facetCount]
  refine Finset.card_bij (fun v _ => insert v f) ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_filter] at hv
    have hvf : v ∉ f := by simpa using hv.1
    exact mem_filter_facetCount.mpr ⟨hv.2, isSimplexFacet_insert hvf⟩
  · intro v hv w hw hvw
    rw [Finset.mem_filter] at hv hw
    have hvf : v ∉ f := by simpa using hv.1
    have hmem : v ∈ insert w f := hvw ▸ Finset.mem_insert_self v f
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · exact absurd h hvf
  · intro s hs
    obtain ⟨hstop, hsfacet⟩ := mem_filter_facetCount.mp hs
    obtain ⟨v, hv, rfl⟩ := exists_insert_of_isSimplexFacet hsfacet
    exact ⟨v, Finset.mem_filter.mpr ⟨by simpa using hv, hstop⟩, rfl⟩

section CharTwo

variable (h2 : (2 : 𝕜) = 0)

include h2

omit [Fintype V] in
theorem orientedSign_eq_one_of_two_eq_zero (f : Finset V) (v : V) :
    orientedSign 𝕜 f v = 1 := by
  have hsum : (1 : 𝕜) + 1 = 0 := by
    have h : (2 : 𝕜) = 1 + 1 := by norm_num
    rw [← h]; exact h2
  have hneg : (-1 : 𝕜) = 1 := neg_eq_of_add_eq_zero_left hsum
  rw [orientedSign, hneg, one_pow]

/-- **The mod two boundary counts cofacets.** -/
theorem boundary_fundamentalChain_apply (K : Finset (Finset V)) (n : ℕ) (f : Finset V) :
    boundary 𝕜 V (fundamentalChain 𝕜 K n) f = (facetCount K n f : 𝕜) := by
  rw [boundary_apply]
  have hsum : ∑ v ∈ (fᶜ : Finset V), orientedSign 𝕜 f v * fundamentalChain 𝕜 K n (insert v f)
      = ∑ v ∈ (fᶜ : Finset V), if insert v f ∈ topSimplices K n then (1 : 𝕜) else 0 := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [orientedSign_eq_one_of_two_eq_zero h2, one_mul, fundamentalChain]
  rw [hsum, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
    card_filter_insert_eq_facetCount K n f]

/-- **The fundamental cycle.**  If every codimension one face lies in an even
number of top simplices, the mod two fundamental chain is a cycle. -/
theorem fundamentalChain_mem_cycles {K : Finset (Finset V)} {n : ℕ}
    (heven : ∀ f : Finset V, Even (facetCount K n f)) :
    fundamentalChain 𝕜 K n ∈ cycles 𝕜 K n := by
  refine ⟨fundamentalChain_mem_chains K n, ?_⟩
  funext f
  rw [boundary_fundamentalChain_apply h2]
  obtain ⟨k, hk⟩ := heven f
  have hcast : ((facetCount K n f : ℕ) : 𝕜) = (k : 𝕜) * 2 := by
    rw [hk]; push_cast; ring
  rw [hcast, h2, mul_zero]
  rfl

/-- **A pure complex all of whose codimension one faces are even is not acyclic
in the top degree** (over a field of characteristic two). -/
theorem not_isReducedAcyclicAt_of_even_facetCount {K : Finset (Finset V)} {n : ℕ}
    (hmax : ∀ s ∈ K, s.card ≤ n) (hne : (topSimplices K n).Nonempty)
    (heven : ∀ f : Finset V, Even (facetCount K n f)) :
    ¬ IsReducedAcyclicAt 𝕜 K n := by
  intro hacyc
  have hmem := hacyc (fundamentalChain_mem_cycles h2 heven)
  rw [boundaries_top_eq_bot hmax, Submodule.mem_bot] at hmem
  exact fundamentalChain_ne_zero hne hmem

/-- **Free ridges from top acyclicity, mod two.**  If a pure complex has no
simplex with more than `n` vertices, has a top simplex, and its reduced
homology over a field of characteristic two vanishes in degree `n`, then some
face of `K` of codimension one lies in an odd number of top simplices. -/
theorem exists_odd_facetCount_of_isReducedAcyclicAt {K : Finset (Finset V)} {n : ℕ}
    (hK : FaceClosed K) (hmax : ∀ s ∈ K, s.card ≤ n) (hne : (topSimplices K n).Nonempty)
    (hacyc : IsReducedAcyclicAt 𝕜 K n) :
    ∃ f ∈ K, f.card + 1 = n ∧ Odd (facetCount K n f) := by
  by_contra hcon
  refine not_isReducedAcyclicAt_of_even_facetCount h2 hmax hne (fun f => ?_) hacyc
  rcases Nat.even_or_odd (facetCount K n f) with h | h
  · exact h
  · exfalso
    have hpos : 0 < facetCount K n f := Nat.pos_of_ne_zero (by
      intro h0
      rw [h0] at h
      simp [Nat.odd_iff] at h)
    obtain ⟨s, hs⟩ := Finset.card_pos.mp hpos
    obtain ⟨hstop, hsfacet⟩ := mem_filter_facetCount.mp hs
    obtain ⟨hsK, hscard⟩ := mem_topSimplices.mp hstop
    have hcard := hsfacet.2
    exact hcon ⟨f, hK s hsK f hsfacet.1, by omega, h⟩

end CharTwo

end AffineTverberg.Simplicial
