import AffineTverberg.OrdinaryLinkHomology

set_option linter.style.header false

/-!
# Rank one in the top degree of the ordinary link

For a triangulated topological `N`-sphere `K` of the expected dimension and a
nonempty face `s`, the top reduced homology of the ordinary combinatorial link
of `s` is one dimensional.  The proof is an actual isomorphism of cycle
spaces: restriction of coefficients to the cofaces of `s`, followed by the
shift of `LinkCofaceShift`, is a linear bijection from the top cycles of `K`
onto the top cycles of the link.  Its inverse adds back a costar correction
supplied by the contractibility of the costar.  Combined with the rank-one
computation of the global fundamental cycle space this gives the missing
"rank one" part of the homology-sphere property.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V]
  {K : Finset (Finset V)} {s : Finset V}

omit [Fintype V] in
/-- Under a dimension bound on `K` the faces of a link are correspondingly
bounded. -/
theorem card_le_of_mem_link {N : ℕ} (htop : ∀ t ∈ K, t.card ≤ N + 1) {u : Finset V}
    (hu : u ∈ link K s) : u.card + s.card ≤ N + 1 := by
  have hcard : (u ∪ s).card = u.card + s.card :=
    Finset.card_union_of_disjoint (mem_link_iff.mp hu).2
  have := htop _ (mem_link_iff.mp hu).1
  omega

/-- Restriction to the cofaces of `s`, followed by the shift, sends a top cycle
of `K` to a top cycle of the link. -/
theorem linkShift_cofaceRestriction_mem_cycles {n N : ℕ}
    (hn : n + s.card = N + 1) {z : Finset V → ℝ} (hz : z ∈ cycles ℝ K (N + 1)) :
    linkShift s (cofaceRestriction s z) ∈ cycles ℝ (link K s) n := by
  refine mem_cycles_iff.mpr ⟨?_, ?_⟩
  · exact linkShift_mem_chains (hn ▸ cofaceRestriction_mem_cofaceChains hz.1 s)
  · rw [← linkShift_cofaceBoundary]
    have hzero : cofaceBoundary s (cofaceRestriction s z) = 0 := by
      change cofaceRestriction s (boundary ℝ V (cofaceRestriction s z)) = 0
      rw [cofaceRestriction_boundary_cofaceRestriction, hz.2, map_zero]
    rw [hzero, map_zero]

/-- The actual restriction map from global top cycles to top cycles of the
ordinary link. -/
def linkTopRestriction {n N : ℕ} (hn : n + s.card = N + 1) :
    ↥(cycles ℝ K (N + 1)) →ₗ[ℝ] ↥(cycles ℝ (link K s) n) :=
  LinearMap.codRestrict _ (((linkShift s).comp (cofaceRestriction s)).comp
      (cycles ℝ K (N + 1)).subtype)
    (fun z ↦ linkShift_cofaceRestriction_mem_cycles hn z.property)

theorem linkTopRestriction_apply {n N : ℕ} (hn : n + s.card = N + 1)
    (z : ↥(cycles ℝ K (N + 1))) :
    (linkTopRestriction hn z : Finset V → ℝ) = linkShift s (cofaceRestriction s z.val) := rfl

section Sphere

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- Under the sphere hypothesis every nonempty face has a top-dimensional
coface: purity at `s` is a consequence of the nonvanishing of the top homology
of the link, not an extra assumption. -/
theorem exists_top_coface_of_sphere (hK : FaceClosed K) (hsK : s ∈ K) (hs : s.Nonempty)
    {N : ℕ} (hdim : Module.finrank ℝ E = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) {n : ℕ} (hn : n + s.card = N + 1) :
    ∃ F ∈ K, s ⊆ F ∧ F.card = N + 1 := by
  by_contra hcon
  have hcon' : ∀ F ∈ K, s ⊆ F → F.card ≠ N + 1 := by
    intro F hF hsF hcard
    exact hcon ⟨F, hF, hsF, hcard⟩
  have hbot : chains ℝ (link K s) n = ⊥ := by
    refine le_antisymm (fun c hc ↦ ?_) bot_le
    have hc0 : c = 0 := by
      funext u
      by_contra hu
      obtain ⟨hmem, hcard⟩ := hc u hu
      obtain ⟨hunion, hdisj⟩ := mem_link_iff.mp hmem
      have hcardu : (u ∪ s).card = u.card + s.card := Finset.card_union_of_disjoint hdisj
      exact hcon' _ hunion Finset.subset_union_right (by omega)
    simpa using hc0
  have hacyc : IsReducedAcyclicAt ℝ (link K s) n := by
    intro c hc
    have hc0 : c = 0 := by simpa [hbot] using hc.1
    simp only [hc0]
    exact (boundaries ℝ (link K s) n).zero_mem
  exact not_isReducedAcyclicAt_link_of_sphere hK hsK hs hdim e n hN hn hacyc

/-- **The top cycles of the ordinary link are exactly the restrictions of the
global fundamental cycles.** -/
theorem bijective_linkTopRestriction (hK : FaceClosed K) (hsK : s ∈ K) (hs : s.Nonempty)
    {N : ℕ} (hdim : Module.finrank ℝ E = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (htop : ∀ t ∈ K, t.card ≤ N + 1) {n : ℕ} (hn : n + s.card = N + 1) :
    Function.Bijective (linkTopRestriction (K := K) hn) := by
  classical
  have hcontr : ContractibleSpace ↥(barycentricCarrier (costarFamily K s)) :=
    contractibleSpace_costar_of_homeomorph_sphere hK hsK hs e
  have hcostar : IsReducedAcyclicAt ℝ (costarFamily K s) N :=
    isReducedAcyclicAt_of_contractible_realization (faceClosed_costarFamily hK s) N
  constructor
  · intro z z' hzz'
    have hdiff : linkShift s (cofaceRestriction s (z.val - z'.val)) = 0 := by
      have hval := congrArg (fun w : ↥(cycles ℝ (link K s) n) ↦ w.val) hzz'
      rw [linkTopRestriction_apply, linkTopRestriction_apply] at hval
      rw [map_sub, map_sub, hval, sub_self]
    have hres : cofaceRestriction s (z.val - z'.val) = 0 :=
      (linkShift_eq_zero_iff (fun F hF ↦ by
        by_contra hcon
        exact hF (by simp [cofaceRestriction_apply, hcon]))).mp hdiff
    obtain ⟨F, hFK, hsF, hFcard⟩ := exists_top_coface_of_sphere hK hsK hs hdim hN e hn
    have hzero : (z.val - z'.val) F = 0 := by
      have hval := congrFun hres F
      simpa only [cofaceRestriction_apply, hsF, ite_true, Pi.zero_apply] using hval
    have hmemcyc : z.val - z'.val ∈ cycles ℝ K (N + 1) :=
      (cycles ℝ K (N + 1)).sub_mem z.property z'.property
    obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
    exact Subtype.ext (sub_eq_zero.mp
      (top_cycle_eq_zero_of_coefficient_eq_zero hK M htop e hFK hFcard hmemcyc hzero))
  · intro b
    have hb := b.property
    have hc : cofaceUnshift s b.val ∈ cofaceChains K s (N + 1) :=
      hn ▸ cofaceUnshift_mem_cofaceChains hb.1
    have hshift : linkShift s (cofaceUnshift s b.val) = b.val :=
      linkShift_cofaceUnshift (chains_link_disjoint hb.1)
    have hcbd : cofaceBoundary s (cofaceUnshift s b.val) = 0 := by
      refine (linkShift_eq_zero_iff (cofaceBoundary_subset s _)).mp ?_
      rw [linkShift_cofaceBoundary, hshift]
      exact hb.2
    have hcycle : boundary ℝ V (cofaceUnshift s b.val) ∈ cycles ℝ (costarFamily K s) N :=
      mem_cycles_iff.mpr ⟨boundary_mem_chains_costar hK hc hcbd, boundary_boundary_apply _⟩
    obtain ⟨w, hw, hwc⟩ := hcostar hcycle
    have hwK : w ∈ chains ℝ K (N + 1) := chains_mono (costarFamily_subset K s) (N + 1) hw
    have hz : cofaceUnshift s b.val - w ∈ cycles ℝ K (N + 1) := by
      refine mem_cycles_iff.mpr ⟨Submodule.sub_mem _ (cofaceChains_le s (N + 1) hc) hwK, ?_⟩
      rw [map_sub, hwc, sub_self]
    refine ⟨⟨_, hz⟩, Subtype.ext ?_⟩
    rw [linkTopRestriction_apply]
    change linkShift s (cofaceRestriction s (cofaceUnshift s b.val - w)) = b.val
    rw [map_sub, map_sub, cofaceRestriction_eq_self hc,
      (cofaceRestriction_eq_zero_iff_costar hwK).mpr hw, map_zero, sub_zero, hshift]

/-- **Rank one in the top degree.**  The top cycle space of the ordinary link
of a nonempty face of a triangulated topological `N`-sphere is one
dimensional. -/
theorem finrank_top_cycles_link (hK : FaceClosed K) (hsK : s ∈ K) (hs : s.Nonempty)
    {N : ℕ} (hdim : Module.finrank ℝ E = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (htop : ∀ t ∈ K, t.card ≤ N + 1) {n : ℕ} (hn : n + s.card = N + 1) :
    Module.finrank ℝ ↥(cycles ℝ (link K s) n) = 1 := by
  have hequiv := LinearEquiv.ofBijective (linkTopRestriction (K := K) hn)
    (bijective_linkTopRestriction hK hsK hs hdim hN e htop hn)
  rw [← hequiv.finrank_eq]
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  exact finrank_top_cycles_of_homeomorph_sphere hK M htop e hdim

/-- The top reduced homology of the ordinary link is one dimensional: in the
top degree there are no boundaries, so the cycle computation is the homology
computation. -/
theorem finrank_top_homology_link (hK : FaceClosed K) (hsK : s ∈ K) (hs : s.Nonempty)
    {N : ℕ} (hdim : Module.finrank ℝ E = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1)
    (htop : ∀ t ∈ K, t.card ≤ N + 1) {n : ℕ} (hn : n + s.card = N + 1) :
    Module.finrank ℝ (homology ℝ (link K s) n) = 1 := by
  have hbd : boundaries ℝ (link K s) n = ⊥ :=
    boundaries_top_eq_bot fun u hu ↦ by
      have := card_le_of_mem_link htop hu
      have hcard : 1 ≤ s.card := Finset.card_pos.mpr hs
      omega
  have hquot : (boundaries ℝ (link K s) n).comap (cycles ℝ (link K s) n).subtype = ⊥ := by
    rw [hbd, Submodule.comap_bot, LinearMap.ker_eq_bot]
    exact Subtype.val_injective
  have hequiv : homology ℝ (link K s) n ≃ₗ[ℝ] ↥(cycles ℝ (link K s) n) :=
    Submodule.quotEquivOfEqBot _ hquot
  rw [hequiv.finrank_eq]
  exact finrank_top_cycles_link hK hsK hs hdim hN e htop hn

end Sphere

end AffineTverberg.Simplicial
