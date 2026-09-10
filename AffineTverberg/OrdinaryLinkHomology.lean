import Mathlib.Analysis.Normed.Module.Connected
import AffineTverberg.CofaceAcyclicity
import AffineTverberg.CostarRetraction
import AffineTverberg.GeneralPositionHomotopy
import AffineTverberg.SphereMiddleHomology
import AffineTverberg.SphereTopHomology

set_option linter.style.header false

/-!
# The ordinary link of a face of a triangulated topological sphere

`CostarRetraction` computes the homology of the concrete coface complex of a
face of a triangulated topological sphere in every degree at least two, and
`LinkCofaceShift` identifies that complex with the augmented (reduced)
oriented chain complex of the *ordinary* combinatorial link, shifted by the
cardinality of the face.  Combining the two computes the reduced simplicial
homology of the ordinary link: it vanishes except in the expected degree, in
which it is nonzero.  This is the homology-sphere property of the link, in
the range that the global-to-relative isomorphism covers.

No PL structure, shellability, orientability or ball-shaped dual block is
assumed anywhere: the only geometric input is the given homeomorphism of the
polyhedron with a norm sphere.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.Simplicial

variable {V : Type} [Fintype V] [LinearOrder V]
  {K : Finset (Finset V)} {s : Finset V}

/-! ### Exactness of the coface complex in terms of the link -/

theorem ker_cofaceDifferential_le_range_iff (hK : FaceClosed K) (L : Finset V) (j : ℕ) :
    (LinearMap.ker (cofaceDifferential hK L (j + 1)) ≤
      LinearMap.range (cofaceDifferential hK L (j + 2))) ↔ IsCofaceAcyclicAt K L (j + 2) := by
  constructor
  · intro h c hc hcbd
    obtain ⟨d, hd⟩ := h (show (⟨c, hc⟩ : ↥(cofaceChains K L (j + 2))) ∈
      LinearMap.ker (cofaceDifferential hK L (j + 1)) from Subtype.ext hcbd)
    exact ⟨d.val, d.property, congrArg Subtype.val hd⟩
  · intro h c hc
    have hc0 : cofaceBoundary L (c : Finset V → ℝ) = 0 := congrArg Subtype.val hc
    obtain ⟨d, hd, hdc⟩ := h (c : Finset V → ℝ) c.property hc0
    exact ⟨⟨d, hd⟩, Subtype.ext hdc⟩

theorem cofaceComplex_exactAt_iff (hK : FaceClosed K) (L : Finset V) (j : ℕ) :
    (cofaceComplex hK L).ExactAt (j + 1) ↔ IsCofaceAcyclicAt K L (j + 2) := by
  rw [HomologicalComplex.exactAt_iff' _ (j + 2) (j + 1) j (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff_ker_sub_range]
  have hg : (HomologicalComplex.sc' (cofaceComplex hK L) (j + 2) (j + 1) j).g
      = ModuleCat.ofHom (cofaceDifferential hK L (j + 1)) := cofaceComplex_d hK L j
  have hf : (HomologicalComplex.sc' (cofaceComplex hK L) (j + 2) (j + 1) j).f
      = ModuleCat.ofHom (cofaceDifferential hK L (j + 2)) := cofaceComplex_d hK L (j + 1)
  rw [hf, hg]
  exact ker_cofaceDifferential_le_range_iff hK L j

/-- Vanishing of the homology of the concrete relative complex is exactly
reduced acyclicity of the ordinary link, in the shifted degree. -/
theorem isReducedAcyclicAt_link_of_isZero_cofaceHomology (hK : FaceClosed K) (L : Finset V)
    {j n : ℕ} (hn : n + L.card = j + 2)
    (h : IsZero ((cofaceComplex hK L).homology (j + 1))) :
    IsReducedAcyclicAt ℝ (link K L) n := by
  have hexact : (cofaceComplex hK L).ExactAt (j + 1) :=
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mpr h
  have hacyc : IsCofaceAcyclicAt K L (n + L.card) := by
    rw [hn]
    exact (cofaceComplex_exactAt_iff hK L j).mp hexact
  exact (isCofaceAcyclicAt_iff_link L n).mp hacyc

/-- Conversely, reduced acyclicity of the link makes the relative homology vanish. -/
theorem isZero_cofaceHomology_of_isReducedAcyclicAt_link (hK : FaceClosed K) (L : Finset V)
    {j n : ℕ} (hn : n + L.card = j + 2)
    (h : IsReducedAcyclicAt ℝ (link K L) n) :
    IsZero ((cofaceComplex hK L).homology (j + 1)) := by
  have hacyc : IsCofaceAcyclicAt K L (j + 2) := by
    rw [← hn]
    exact (isCofaceAcyclicAt_iff_link L n).mpr h
  exact (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
    ((cofaceComplex_exactAt_iff hK L j).mpr hacyc)

/-! ### The link of a face of a triangulated topological sphere -/

section Sphere

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The relative homology of the coface complex vanishes away from the sphere
dimension, in degrees at least two. -/
theorem isZero_cofaceComplex_homology_of_sphere (hK : FaceClosed K) (hsK : s ∈ K)
    (hs : s.Nonempty) {N : ℕ} (hdim : Module.finrank ℝ E = N + 1)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (k : ℕ) (hk : k ≠ 0) (hkN : k + 1 ≠ N) :
    IsZero ((cofaceComplex hK s).homology (k + 1)) := by
  have hsub : Subsingleton ((realSingularHomology (k + 1)).obj (barySpace K)) := by
    rcases lt_or_gt_of_ne hkN with hlt | hgt
    · exact subsingleton_singularHomology_of_homeomorph_sphere hdim e (k + 1)
        (Nat.succ_pos k) hlt
    · exact subsingleton_singularHomology_of_homeomorph_sphere_of_gt hdim e (k + 1) hgt
  have hzero : IsZero ((realSingularHomology (k + 1)).obj (barySpace K)) :=
    ModuleCat.isZero_of_subsingleton _
  exact hzero.of_iso (sphereHomologyIsoCoface hK hsK hs e k hk).symm

omit [LinearOrder V] in
/-- The polyhedron of a triangulated topological sphere of dimension at least
one is path connected. -/
theorem pathConnectedSpace_of_homeomorph_sphere {N : ℕ}
    (hdim : Module.finrank ℝ E = N + 1) (hN : 1 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) :
    PathConnectedSpace ↥(barycentricCarrier K) := by
  have hrank : 1 < Module.rank ℝ E := by
    have h : Module.rank ℝ E = (Module.finrank ℝ E : Cardinal) :=
      (Module.finrank_eq_rank ℝ E).symm
    rw [h, hdim]
    exact_mod_cast Nat.lt_of_lt_of_le Nat.one_lt_two (by omega : 2 ≤ N + 1)
  have hsph : PathConnectedSpace ↥(sphere (0 : E) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere hrank 0 zero_le_one)
  exact GeneralPosition.pathConnectedSpace_of_homotopyEquiv e.symm.toHomotopyEquiv

/-- A triangulated topological `N`-sphere is reduced acyclic in every
cardinality degree except `N + 1`, including the two low endpoints. -/
theorem isReducedAcyclicAt_of_homeomorph_sphere (hK : FaceClosed K) {N : ℕ}
    (hdim : Module.finrank ℝ E = N + 1) (hN : 1 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (m : ℕ) (hm : m ≠ N + 1) :
    IsReducedAcyclicAt ℝ K m := by
  have hpath : PathConnectedSpace ↥(barycentricCarrier K) :=
    pathConnectedSpace_of_homeomorph_sphere hdim hN e
  match m with
  | 0 =>
    obtain ⟨x⟩ := (inferInstance : Nonempty ↥(barycentricCarrier K))
    exact isReducedAcyclicAt_zero_of_nonempty_realization hK ⟨x.val, x.property⟩
  | 1 =>
    have hpc' : PathConnectedSpace ↥(barySpace K) := hpath
    exact isReducedAcyclicAt_one_of_isIso_singularAugmentation hK inferInstance
  | (j + 2) =>
    refine (isZero_realSingularHomology_barySpace_iff hK j).mp ?_
    have hsub : Subsingleton ((realSingularHomology (j + 1)).obj (barySpace K)) := by
      rcases lt_or_gt_of_ne (show j + 1 ≠ N by omega) with hlt | hgt
      · exact subsingleton_singularHomology_of_homeomorph_sphere hdim e (j + 1)
          (Nat.succ_pos j) hlt
      · exact subsingleton_singularHomology_of_homeomorph_sphere_of_gt hdim e (j + 1) hgt
    exact ModuleCat.isZero_of_subsingleton _

/-- **The ordinary link of a face of a triangulated topological sphere is a
homology sphere: the vanishing half, in every degree.**  If `|K|` is
homeomorphic to an `N`-sphere with `N ≥ 1` and `s` is a nonempty face, the
reduced simplicial homology of the ordinary combinatorial link `link K s`
vanishes in every cardinality degree `n` with `n + #s ≠ N + 1`, that is, in
every degree other than the geometric degree `N - #s`.  The two low endpoints
(`n + #s = 1`, the empty simplex, and `n + #s = 2`, connectivity) are included:
the proof goes through the elementary costar chase rather than the
global-to-relative comparison, which only covers degrees at least two. -/
theorem isReducedAcyclicAt_link_of_sphere (hK : FaceClosed K) (hsK : s ∈ K)
    (hs : s.Nonempty) {N : ℕ} (hdim : Module.finrank ℝ E = N + 1) (hN : 1 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (n : ℕ)
    (hne : n + s.card ≠ N + 1) :
    IsReducedAcyclicAt ℝ (link K s) n := by
  have hcard : 1 ≤ s.card := Finset.card_pos.mpr hs
  obtain ⟨j, hj⟩ : ∃ j, n + s.card = j + 1 := ⟨n + s.card - 1, by omega⟩
  have hcontr : ContractibleSpace ↥(barycentricCarrier (costarFamily K s)) :=
    contractibleSpace_costar_of_homeomorph_sphere hK hsK hs e
  refine isReducedAcyclicAt_link_of_acyclic hK s n j hj ?_ ?_
  · exact isReducedAcyclicAt_of_contractible_realization (faceClosed_costarFamily hK s) j
  · exact isReducedAcyclicAt_of_homeomorph_sphere hK hdim hN e (j + 1) (by omega)

/-- **The ordinary link of a face of a triangulated topological sphere is a
homology sphere: the nonvanishing half.**  In the expected degree
`n + #s = N + 1` the reduced homology of the ordinary link does not vanish
(for `N ≥ 2`, the range in which the global-to-relative comparison applies). -/
theorem not_isReducedAcyclicAt_link_of_sphere (hK : FaceClosed K) (hsK : s ∈ K)
    (hs : s.Nonempty) {N : ℕ} (hdim : Module.finrank ℝ E = N + 1)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : E) 1) (n : ℕ)
    (hlow : 2 ≤ N) (hn : n + s.card = N + 1) :
    ¬ IsReducedAcyclicAt ℝ (link K s) n := by
  intro hacyc
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  have hzero : IsZero ((cofaceComplex hK s).homology (k + 2)) :=
    isZero_cofaceHomology_of_isReducedAcyclicAt_link hK s (j := k + 1) (by omega) hacyc
  have hzero' : IsZero ((realSingularHomology (k + 2)).obj (barySpace K)) :=
    hzero.of_iso (sphereHomologyIsoCoface hK hsK hs e (k + 1) (Nat.succ_ne_zero k))
  have hnt : Nontrivial ((realSingularHomology (k + 2)).obj (barySpace K)) := by
    have hsphere : Nontrivial ((realSingularHomology (k + 2)).obj
        (TopCat.of (sphere (0 : E) 1))) := nontrivial_singularHomology_sphere hdim
    apply not_subsingleton_iff_nontrivial.mp
    intro hsub
    exact not_subsingleton _
      ((realSingularHomology_subsingleton_iff_of_homotopyEquiv e.toHomotopyEquiv (k + 2)).mp hsub)
  have hsub := ModuleCat.subsingleton_of_isZero hzero'
  exact not_subsingleton _ hsub

end Sphere

end AffineTverberg.Simplicial
