import AffineTverberg.DualBlockRelativeRank
import AffineTverberg.LinkOrientationNaturality

set_option linter.style.header false

/-!
# Actual positive-degree dual-block classes from a single global cycle

The class in a dual-block pair is the inverse image of the signed global
cycle restriction under the actual connecting and link-comparison maps.
Thus the choices do not consist of unrelated generators of rank-one groups.
Their link-coordinate restrictions have exactly the simplex incidence signs.

This file does not identify the connecting maps of triples with those link
restrictions. That geometric incidence comparison is still required by the
global duality argument. Degree-zero dual blocks are not assigned orientations
here; their actual rank-one calculation is in DualBlockRelativeRank.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.Simplicial

open AffineTverberg.AffChain

variable {V : Type} [Fintype V] [LinearOrder V]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E} {s : Finset V}

/-- A uniform positive-relative-degree version of the actual link-cycle
comparison, using the augmentation kernel in relative degree one. -/
def dualBlockRelativeHomologySuccEquivLinkCycles
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty) (q : ℕ)
    (htop : ∀ t ∈ link K s, t.card ≤ q + 1) :
    relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
      (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) (q + 1) ≃ₗ[ℝ]
      ↥(cycles ℝ (link K s) (q + 1)) := by
  cases q with
  | zero => exact dualBlockRelativeHomologyOneEquivLinkCycles hgeom hK hsK hs htop
  | succ q => exact dualBlockRelativeHomologyPositiveEquivLinkCycles hgeom hK hsK hs q htop

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- The actual link restriction, followed by the inverse genuine relative
comparison, transports global top cycles to dual-block relative classes. -/
def dualBlockGlobalOrientationEquiv
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty) {N : ℕ}
    (hdim : Module.finrank ℝ F = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1)
    (htop : ∀ t ∈ K, t.card ≤ N + 1) (q : ℕ) (hq : q + 1 + s.card = N + 1) :
    ↥(cycles ℝ K (N + 1)) ≃ₗ[ℝ]
      relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
        (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) (q + 1) := by
  have hlink : ∀ t ∈ link K s, t.card ≤ q + 1 := by
    intro t ht
    have := card_le_of_mem_link htop ht
    omega
  exact (LinearEquiv.ofBijective (linkTopRestriction hq)
    (bijective_linkTopRestriction hK hsK hs hdim hN e htop hq)).trans
      (dualBlockRelativeHomologySuccEquivLinkCycles hgeom hK hsK hs q hlink).symm

/-- The class is represented in link coordinates by the literal signed
coefficient restriction of the given global cycle. -/
theorem dualBlockGlobalOrientationEquiv_link
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty) {N : ℕ}
    (hdim : Module.finrank ℝ F = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1)
    (htop : ∀ t ∈ K, t.card ≤ N + 1) (q : ℕ) (hq : q + 1 + s.card = N + 1)
    (hlink : ∀ t ∈ link K s, t.card ≤ q + 1) (z : ↥(cycles ℝ K (N + 1))) :
    dualBlockRelativeHomologySuccEquivLinkCycles hgeom hK hsK hs q hlink
      (dualBlockGlobalOrientationEquiv hgeom hK hsK hs hdim hN e htop q hq z) =
      linkTopRestriction hq z := by
  unfold dualBlockGlobalOrientationEquiv
  exact LinearEquiv.apply_symm_apply _ _

/-- A nonzero global cycle gives a nonzero actual relative class. -/
theorem dualBlockGlobalOrientationEquiv_ne_zero
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty) {N : ℕ}
    (hdim : Module.finrank ℝ F = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1)
    (htop : ∀ t ∈ K, t.card ≤ N + 1) (q : ℕ) (hq : q + 1 + s.card = N + 1)
    (z : ↥(cycles ℝ K (N + 1))) (hz : z ≠ 0) :
    dualBlockGlobalOrientationEquiv hgeom hK hsK hs hdim hN e htop q hq z ≠ 0 :=
  (dualBlockGlobalOrientationEquiv hgeom hK hsK hs hdim hN e htop q hq).map_ne_zero_iff.mpr hz

/-- That same actual relative class spans the entire dual-block group. -/
theorem span_dualBlockGlobalOrientationEquiv
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty) {N : ℕ}
    (hdim : Module.finrank ℝ F = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1)
    (htop : ∀ t ∈ K, t.card ≤ N + 1) (q : ℕ) (hq : q + 1 + s.card = N + 1)
    (z : ↥(cycles ℝ K (N + 1))) (hz : z ≠ 0) :
    Submodule.span ℝ
      {dualBlockGlobalOrientationEquiv hgeom hK hsK hs hdim hN e htop q hq z} = ⊤ :=
  (finrank_eq_one_iff_of_nonzero _
    (dualBlockGlobalOrientationEquiv_ne_zero hgeom hK hsK hs hdim hN e htop q hq z hz)).mp
      (finrank_dualBlockRelativeHomology_of_sphere hgeom hK hsK hs hdim hN e htop (q + 1) hq)

/-- The link-coordinate orientation of each actual relative class has the
prescribed incidence sign on restriction at another vertex. This is a
coefficient identity, not an unproved assertion about a triple boundary map. -/
theorem dualBlockGlobalOrientationEquiv_insert
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty) {N : ℕ}
    (hdim : Module.finrank ℝ F = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1)
    (htop : ∀ t ∈ K, t.card ≤ N + 1) (q : ℕ) (hq : q + 1 + s.card = N + 1)
    (hlink : ∀ t ∈ link K s, t.card ≤ q + 1) (z : ↥(cycles ℝ K (N + 1)))
    {v : V} (hv : v ∉ s) :
    linkShift {v}
      (dualBlockRelativeHomologySuccEquivLinkCycles hgeom hK hsK hs q hlink
        (dualBlockGlobalOrientationEquiv hgeom hK hsK hs hdim hN e htop q hq z) :
          Finset V → ℝ) = orientedSign ℝ s v • linkShift (insert v s) z.val := by
  rw [dualBlockGlobalOrientationEquiv_link]
  exact linkTopRestriction_insert hv hq z

end AffineTverberg.Simplicial
