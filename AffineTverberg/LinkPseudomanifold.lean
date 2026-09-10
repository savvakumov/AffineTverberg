import AffineTverberg.PseudomanifoldCycle

set_option linter.style.header false

/-!
# Links, and the mod two top cycle of a link with no free ridge

This file adds the combinatorial link of a face to the oriented simplicial
framework and isolates the exact combinatorial content of the still-open case of
the boundary identification for a simplicial ball: a face all of whose
codimension-one cofaces lie in *two* top simplices has a link whose reduced
homology over a field of characteristic two does **not** vanish in the top
degree.

* `link K s = {u | u ∪ s ∈ K and u is disjoint from s}` with the exact
  membership criterion `mem_link_iff` and face-closedness.
* `facetCount_link` — the number of top simplices of the link above a face `u`
  is the number of top simplices of `K` above the coface `u ∪ s`.
* `not_isReducedAcyclicAt_link` — **the top mod two homology of the link does not
  vanish** when every codimension-one coface of `s` lies in an even number of
  top simplices (in particular, in exactly two, i.e. when no coface of `s` is a
  free ridge).

What is deliberately not done here is the passage from this simplicial mod two
statement to the singular homology of the geometric link: that needs the
comparison theorem with characteristic-two coefficients, now completed in
the `Coefficients.*` modules. Over `ℝ` the statement is
false for non-orientable closed pseudomanifolds, so the characteristic-two
hypothesis is essential and is kept explicit.
-/

noncomputable section

open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {𝕜 V : Type*} [Field 𝕜] [Fintype V] [LinearOrder V]

/-- The combinatorial link of a face `s` in a family `K`. -/
def link (K : Finset (Finset V)) (s : Finset V) : Finset (Finset V) :=
  (K.filter (fun t ↦ s ⊆ t)).image (fun t ↦ t \ s)

omit [Fintype V] in
@[simp]
theorem mem_link_iff {K : Finset (Finset V)} {s u : Finset V} :
    u ∈ link K s ↔ u ∪ s ∈ K ∧ Disjoint u s := by
  classical
  constructor
  · intro hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨htK, hst⟩ := Finset.mem_filter.mp ht
    refine ⟨?_, Finset.sdiff_disjoint⟩
    rwa [Finset.sdiff_union_of_subset hst]
  · rintro ⟨hmem, hdisj⟩
    refine Finset.mem_image.mpr ⟨u ∪ s, Finset.mem_filter.mpr ⟨hmem, Finset.subset_union_right⟩, ?_⟩
    ext v
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hv | hv, hvs⟩
      · exact hv
      · exact absurd hv hvs
    · intro hv
      exact ⟨Or.inl hv, fun hvs ↦ (Finset.disjoint_left.mp hdisj hv) hvs⟩

omit [Fintype V] in
theorem faceClosed_link {K : Finset (Finset V)} (hK : FaceClosed K) (s : Finset V) :
    FaceClosed (link K s) := by
  intro u hu v hvu
  rw [mem_link_iff] at hu ⊢
  refine ⟨hK _ hu.1 _ (Finset.union_subset_union_left hvu), ?_⟩
  exact hu.2.mono_left hvu

omit [Fintype V] in
theorem card_union_of_mem_link {K : Finset (Finset V)} {s u : Finset V}
    (hu : u ∈ link K s) : (u ∪ s).card = u.card + s.card :=
  Finset.card_union_of_disjoint (mem_link_iff.mp hu).2

omit [Fintype V] in
/-- The top simplices of the link are the top simplices of `K` through `s`,
with `s` removed. -/
theorem facetCount_link {K : Finset (Finset V)} {s u : Finset V} {N : ℕ}
    (hu : u ∈ link K s) (hs : s.card ≤ N) :
    facetCount (link K s) (N - s.card) u = facetCount K N (u ∪ s) := by
  classical
  obtain ⟨huK, hdisj⟩ := mem_link_iff.mp hu
  refine Finset.card_bij (fun v _ ↦ v ∪ s) ?_ ?_ ?_
  · intro v hv
    obtain ⟨hvtop, hsub, hcard⟩ : v ∈ topSimplices (link K s) (N - s.card) ∧
        u ⊆ v ∧ u.card + 1 = v.card := by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hv
      exact ⟨h1, h2.1, h2.2⟩
    obtain ⟨hvlink, hvcard⟩ := mem_topSimplices.mp hvtop
    obtain ⟨hvK, hvdisj⟩ := mem_link_iff.mp hvlink
    refine Finset.mem_filter.mpr ⟨mem_topSimplices.mpr ⟨hvK, ?_⟩, ?_, ?_⟩
    · rw [Finset.card_union_of_disjoint hvdisj, hvcard]
      omega
    · exact Finset.union_subset_union_left hsub
    · rw [Finset.card_union_of_disjoint hvdisj, Finset.card_union_of_disjoint hdisj]
      omega
  · intro v hv w hw hvw
    obtain ⟨hvtop, _⟩ := Finset.mem_filter.mp hv
    obtain ⟨hwtop, _⟩ := Finset.mem_filter.mp hw
    obtain ⟨hvlink, _⟩ := mem_topSimplices.mp hvtop
    obtain ⟨hwlink, _⟩ := mem_topSimplices.mp hwtop
    have hvd := (mem_link_iff.mp hvlink).2
    have hwd := (mem_link_iff.mp hwlink).2
    ext x
    constructor
    · intro hx
      have hxw : x ∈ w ∪ s := hvw ▸ Finset.mem_union_left s hx
      rcases Finset.mem_union.mp hxw with h | h
      · exact h
      · exact absurd h (Finset.disjoint_left.mp hvd hx)
    · intro hx
      have hxv : x ∈ v ∪ s := hvw.symm ▸ Finset.mem_union_left s hx
      rcases Finset.mem_union.mp hxv with h | h
      · exact h
      · exact absurd h (Finset.disjoint_left.mp hwd hx)
  · intro w hw
    obtain ⟨hwtop, hsub, hcard⟩ : w ∈ topSimplices K N ∧
        u ∪ s ⊆ w ∧ (u ∪ s).card + 1 = w.card := by
      obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hw
      exact ⟨h1, h2.1, h2.2⟩
    obtain ⟨hwK, hwcard⟩ := mem_topSimplices.mp hwtop
    have hsw : s ⊆ w := (Finset.subset_union_right).trans hsub
    have huw : u ⊆ w := (Finset.subset_union_left).trans hsub
    have hlink : w \ s ∈ link K s := by
      rw [mem_link_iff, Finset.sdiff_union_of_subset hsw]
      exact ⟨hwK, Finset.sdiff_disjoint⟩
    have hcards : (w \ s).card = N - s.card := by
      rw [Finset.card_sdiff_of_subset hsw, hwcard]
    have husub : u ⊆ w \ s := by
      intro x hx
      exact Finset.mem_sdiff.mpr ⟨huw hx, fun hxs ↦ (Finset.disjoint_left.mp hdisj hx) hxs⟩
    refine ⟨w \ s, Finset.mem_filter.mpr ⟨mem_topSimplices.mpr ⟨hlink, hcards⟩, husub, ?_⟩, ?_⟩
    · rw [hcards]
      rw [Finset.card_union_of_disjoint hdisj] at hcard
      omega
    · rw [Finset.sdiff_union_of_subset hsw]

section CharTwo

variable (h2 : (2 : 𝕜) = 0)

include h2

/-- **The link of a face with no free codimension-one coface carries a mod two
fundamental cycle.**  If `K` has no simplex with more than `N` vertices, `s` is
contained in some top simplex, and every coface of `s` of cardinality `N - 1`
lies in an even number of top simplices, then the reduced homology of the link
of `s` over a field of characteristic two does not vanish in its top degree. -/
theorem not_isReducedAcyclicAt_link {K : Finset (Finset V)} (hK : FaceClosed K)
    {s : Finset V} {N : ℕ} (hs : s.card ≤ N)
    (hmax : ∀ t ∈ K, t.card ≤ N)
    (hface : ∃ w ∈ K, s ⊆ w ∧ w.card = N)
    (heven : ∀ f ∈ K, s ⊆ f → f.card + 1 = N → Even (facetCount K N f)) :
    ¬ IsReducedAcyclicAt 𝕜 (link K s) (N - s.card) := by
  classical
  have hmaxL : ∀ u ∈ link K s, u.card ≤ N - s.card := by
    intro u hu
    have hcard := card_union_of_mem_link hu
    have := hmax _ (mem_link_iff.mp hu).1
    omega
  have hneL : (topSimplices (link K s) (N - s.card)).Nonempty := by
    obtain ⟨w, hwK, hsw, hwcard⟩ := hface
    refine ⟨w \ s, mem_topSimplices.mpr ⟨?_, ?_⟩⟩
    · rw [mem_link_iff, Finset.sdiff_union_of_subset hsw]
      exact ⟨hwK, Finset.sdiff_disjoint⟩
    · rw [Finset.card_sdiff_of_subset hsw, hwcard]
  have hevenL : ∀ u : Finset V, Even (facetCount (link K s) (N - s.card) u) := by
    intro u
    by_cases hu : u ∈ link K s
    · rw [facetCount_link hu hs]
      by_cases hcard : (u ∪ s).card + 1 = N
      · exact heven _ (mem_link_iff.mp hu).1 Finset.subset_union_right hcard
      · have : facetCount K N (u ∪ s) = 0 := by
          rw [facetCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro w hw hcon
          exact hcard (by rw [hcon.2, (mem_topSimplices.mp hw).2])
        rw [this]
        exact Even.zero
    · have : facetCount (link K s) (N - s.card) u = 0 := by
        rw [facetCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro w hw hcon
        exact hu (faceClosed_link hK s _ (mem_topSimplices.mp hw).1 _ hcon.1)
      rw [this]
      exact Even.zero
  exact not_isReducedAcyclicAt_of_even_facetCount h2 hmaxL hneL hevenL

/-- The same conclusion under the hypothesis actually available for a simplicial
ball: every codimension-one coface of `s` lies in exactly two top simplices,
i.e. no coface of `s` is a free ridge. -/
theorem not_isReducedAcyclicAt_link_of_two {K : Finset (Finset V)} (hK : FaceClosed K)
    {s : Finset V} {N : ℕ} (hs : s.card ≤ N)
    (hmax : ∀ t ∈ K, t.card ≤ N)
    (hface : ∃ w ∈ K, s ⊆ w ∧ w.card = N)
    (htwo : ∀ f ∈ K, s ⊆ f → f.card + 1 = N → facetCount K N f = 2) :
    ¬ IsReducedAcyclicAt 𝕜 (link K s) (N - s.card) :=
  not_isReducedAcyclicAt_link h2 hK hs hmax hface
    (fun f hf hsf hcard ↦ by rw [htwo f hf hsf hcard]; exact even_two)

end CharTwo

end AffineTverberg.Simplicial
