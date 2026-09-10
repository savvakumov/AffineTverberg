import AffineTverberg.CofaceDoubleComplexDuality
import AffineTverberg.LinkTopCycleRank

set_option linter.style.header false

/-!
# Alexander duality for induced subcomplexes of a triangulated sphere

The algebraic core of `CofaceDoubleComplexDuality` is instantiated here with
the geometric input available for a triangulated topological sphere:

* the coface complexes are exact away from the top degree, because the
  ordinary links are homology spheres (`isReducedAcyclicAt_link_of_sphere`);
* the top cycles of every coface complex are one dimensional and are spanned by
  the restriction of a *single* global fundamental cycle
  (`bijective_linkTopRestriction`), so all the local orientations used in the
  comparison come from one global choice.

The result is genuine Alexander duality for a pair of complementary induced
subcomplexes of a triangulated sphere: if `K[Gᶜ]` — which is a deformation
retract of the complement of `|K[G]|` in `|K|` — is reduced acyclic in
cardinality degree `k + 1`, then `K[G]` is reduced acyclic in the
complementary cardinality degree.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V] {K : Finset (Finset V)}

omit [Fintype V] in
@[simp]
theorem link_empty (K : Finset (Finset V)) : link K ∅ = K := by
  ext u
  simp

section Sphere

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Away from the top cardinality degree, every coface complex of a
triangulated topological sphere is exact.  For a nonempty face this is the
homology-sphere property of the ordinary link; for the empty face it is
acyclicity of the sphere itself. -/
theorem isCofaceAcyclicAt_of_sphere (hK : FaceClosed K) {N : ℕ}
    (hdim : Module.finrank ℝ E = N + 1) (hN : 1 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (s : Finset V) (hsK : s ∈ K) (j : ℕ) (hj : j ≠ N + 1) :
    IsCofaceAcyclicAt K s j := by
  classical
  by_cases hjs : s.card ≤ j
  · obtain ⟨n, hn⟩ : ∃ n, j = n + s.card := ⟨j - s.card, by omega⟩
    subst hn
    refine (isCofaceAcyclicAt_iff_link s n).mpr ?_
    rcases Finset.eq_empty_or_nonempty s with rfl | hs
    · rw [link_empty]
      exact isReducedAcyclicAt_of_homeomorph_sphere hK hdim hN e n (by simpa using hj)
    · exact isReducedAcyclicAt_link_of_sphere hK hsK hs hdim hN e n hj
  · intro c hc _
    have hc0 : c = 0 := by
      funext t
      by_contra hne
      obtain ⟨htmem, htcard⟩ := hc t hne
      have hsub : s ⊆ t := (Finset.mem_filter.mp htmem).2
      have := Finset.card_le_card hsub
      omega
    exact ⟨0, Submodule.zero_mem _, by rw [hc0, map_zero]⟩

/-- **Alexander duality for complementary induced subcomplexes of a
triangulated topological sphere.**  No PL, shellability or manifold hypothesis
is used: the only geometric input is a homeomorphism of the polyhedron with a
norm sphere of the expected dimension. -/
theorem isReducedAcyclicAt_inducedFaces_of_sphere (hK : FaceClosed K) {N : ℕ}
    (hdim : Module.finrank ℝ E = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (htop : ∀ t ∈ K, t.card ≤ N + 1)
    (G : Finset V) {A L : Finset (Finset V)}
    (hA : ∀ s, s ∈ A ↔ s ∈ K ∧ ∀ v ∈ s, v ∈ G)
    (hL : ∀ s, s ∈ L ↔ s ∈ K ∧ ∀ v ∈ s, v ∉ G)
    {q k : ℕ} (hk : 1 ≤ k) (hQ : q + 2 + k = N + 1)
    (hbad : IsReducedAcyclicAt ℝ L (k + 1)) :
    IsReducedAcyclicAt ℝ A (q + 1) := by
  classical
  have hAeq : A = inducedFaces K G := by
    refine Finset.ext fun s => ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨hsK, hsG⟩ := (hA s).mp h
      exact mem_inducedFaces.mpr ⟨hsK, fun v hv => hsG v hv⟩
    · obtain ⟨hsK, hsG⟩ := mem_inducedFaces.mp h
      exact (hA s).mpr ⟨hsK, fun v hv => hsG hv⟩
  rw [hAeq]
  obtain ⟨M, hM⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  subst hM
  have htop' : ∀ t ∈ K, t.card ≤ M + 2 := htop
  have hdim' : Module.finrank ℝ E = M + 2 := hdim
  obtain ⟨z, hz, hznz, -⟩ := exists_fundamental_sphere_cycle hK M htop' e hdim'
  -- one global fundamental cycle spans all top cycles
  have hrank : Module.finrank ℝ ↥(cycles ℝ K (M + 2)) = 1 :=
    finrank_top_cycles_of_homeomorph_sphere hK M htop' e hdim'
  have hspanTop : ∀ w ∈ cycles ℝ K (M + 2), ∃ r : ℝ, w = r • z := by
    intro w hw
    have hzsub : (⟨z, hz⟩ : ↥(cycles ℝ K (M + 2))) ≠ 0 := fun h =>
      hznz (congrArg Subtype.val h)
    have hspan : (ℝ ∙ (⟨z, hz⟩ : ↥(cycles ℝ K (M + 2)))) = ⊤ :=
      (finrank_eq_one_iff_of_nonzero _ hzsub).mp hrank
    have hmem : (⟨w, hw⟩ : ↥(cycles ℝ K (M + 2))) ∈
        (ℝ ∙ (⟨z, hz⟩ : ↥(cycles ℝ K (M + 2)))) := by
      rw [hspan]
      trivial
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hmem
    exact ⟨r, (congrArg Subtype.val hr).symm⟩
  -- the restriction of the global cycle to the cofaces of a face is nonzero
  have hgen : ∀ s ∈ K, s.Nonempty → cofaceRestriction s z ≠ 0 := by
    intro s hsK hs hzero
    have hcard : s.card ≤ M + 2 := htop' s hsK
    obtain ⟨n, hn⟩ : ∃ n, n + s.card = M + 2 := ⟨M + 2 - s.card, by omega⟩
    have hbij := bijective_linkTopRestriction hK hsK hs hdim' hN e htop' hn
    have h0 : linkTopRestriction (K := K) hn ⟨z, hz⟩ = linkTopRestriction (K := K) hn 0 := by
      refine Subtype.ext ?_
      rw [linkTopRestriction_apply, hzero, map_zero, map_zero]
      rfl
    exact hznz (congrArg Subtype.val (hbij.1 h0))
  -- and it spans the top cycles of every coface complex
  have hspan : ∀ s ∈ K, s.Nonempty → ∀ x ∈ cofaceChains K s (M + 2),
      cofaceBoundary s x = 0 → ∃ r : ℝ, x = r • cofaceRestriction s z := by
    intro s hsK hs x hx hxb
    have hcard : s.card ≤ M + 2 := htop' s hsK
    obtain ⟨n, hn⟩ : ∃ n, n + s.card = M + 2 := ⟨M + 2 - s.card, by omega⟩
    have hxc : linkShift s x ∈ cycles ℝ (link K s) n := by
      refine mem_cycles_iff.mpr ⟨linkShift_mem_chains (hn ▸ hx), ?_⟩
      rw [← linkShift_cofaceBoundary, hxb, map_zero]
    obtain ⟨w, hw⟩ :=
      (bijective_linkTopRestriction hK hsK hs hdim' hN e htop' hn).2 ⟨linkShift s x, hxc⟩
    have hval : linkShift s (cofaceRestriction s w.val) = linkShift s x := by
      have hv := congrArg Subtype.val hw
      rw [linkTopRestriction_apply] at hv
      exact hv
    have heq : cofaceRestriction s w.val = x := by
      refine linkShift_injOn (fun F hF => ?_) (mem_cofaceChains_subset hx) hval
      by_contra hcon
      exact hF (by simp [cofaceRestriction_apply, hcon])
    obtain ⟨r, hr⟩ := hspanTop w.val w.property
    refine ⟨r, ?_⟩
    rw [← heq, hr, map_smul]
  have hcol : ∀ s ∈ K, ∀ j, j ≠ M + 2 → IsCofaceAcyclicAt K s j := fun s hsK j hj =>
    isCofaceAcyclicAt_of_sphere hK hdim' (by omega) e s hsK j hj
  have hKac : IsReducedAcyclicAt ℝ K (q + 1) :=
    isReducedAcyclicAt_of_homeomorph_sphere hK hdim' (by omega) e (q + 1) (by omega)
  refine isReducedAcyclicAt_inducedFaces_of_relExact hK hKac ?_
  intro a ha hco
  exact exists_relCoboundary_of_relCocycle hK hk (by omega) htop' hcol hz hgen hspan hL hbad
    ha hco

end Sphere

end AffineTverberg.Simplicial
