import AffineTverberg.DualBlockCofaceModel
import AffineTverberg.ReducedHomologyInvariance

set_option linter.style.header false

/-!
# The actual dual-block relative homology calculation in every degree

The apex costar model gives reduced boundary homology in every ordinary
degree, including zero. The actual boundary-to-ordinary-link homeomorphism
and reduced homotopy invariance identify this with the ordinary link of the
original face. Thus the sphere calculation has no relative degree-zero/one
gap and includes the empty-boundary dual block at a maximal face.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg.Simplicial

open AffineTverberg.AffChain

variable {V : Type} [Fintype V] [LinearOrder V] [inst : LinearOrder (Finset V)]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : Finset (Finset V)} {p : V → E} {s : Finset V}

local instance : DecidableEq (Finset V) := inst.toDecidableEq

/-- The standard realization of the boundary face family and the ordinary
link realization are related by the actual geometric boundary homeomorphism. -/
def dualBlockBoundaryRealizationHomeomorph (hgeom : IsGeometricRealization K p)
    (hK : FaceClosed K) (s : Finset V) :
    ↥(barycentricCarrier (dualBlockBoundaryFaces K s)) ≃ₜ
      ↥(barycentricCarrier (link K s)) := by
  have hBg : IsGeometricRealization (dualBlockBoundaryFaces K s) (faceBarycenter p) := by
    have h := @IsGeometricRealization.mono (Finset V) (fun a b => a.decidableEq b)
      E _ _ _ _ _ (isGeometricRealization_subdivisionFaces hgeom)
      ((dualBlockBoundaryFaces_subset K s).trans (dualBlockFaces_subset K s))
    convert h using 1
  exact (geometricRealizationHomeomorph hBg).trans (dualBlockBoundaryHomeomorph hgeom hK s)

theorem isReducedAcyclicAt_dualBlockBoundary_iff_link
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K) (hsK : s ∈ K) (q : ℕ) :
    IsReducedAcyclicAt ℝ (dualBlockBoundaryFaces K s) q ↔
      IsReducedAcyclicAt ℝ (link K s) q := by
  have hB : FaceClosed (dualBlockBoundaryFaces K s) := by
    convert faceClosed_dualBlockBoundaryFaces K s using 1
  have heB : (∅ : Finset (Finset V)) ∈ dualBlockBoundaryFaces K s := by
    simp [mem_dualBlockBoundaryFaces, mem_subdivisionFaces, IsFaceChain]
  have heL : (∅ : Finset V) ∈ link K s :=
    mem_link_iff.mpr ⟨by simpa using hsK, by simp⟩
  exact isReducedAcyclicAt_iff_of_realization_homotopyEquiv hB (faceClosed_link hK s)
    heB heL (dualBlockBoundaryRealizationHomeomorph hgeom hK s).toHomotopyEquiv q

/-- Actual relative singular homology vanishes precisely when the reduced
ordinary-link homology does in the corresponding degree. This includes
q=0 and the augmented empty-simplex group of the ordinary link. -/
theorem isZero_dualBlockRelativeHomology_iff_link_all
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty) (q : ℕ) :
    IsZero (relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
      (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) q) ↔
      IsReducedAcyclicAt ℝ (link K s) q :=
  (isZero_dualBlockRelativeHomology_iff_boundary_acyclic hgeom hsK hs q).trans
    (isReducedAcyclicAt_dualBlockBoundary_iff_link hgeom hK hsK q)

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

/-- All off-top relative dual-block homology vanishes, including zero and
one, for an arbitrary triangulated topological sphere. -/
theorem isZero_dualBlockRelativeHomology_of_sphere_all
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty) {N : ℕ}
    (hdim : Module.finrank ℝ F = N + 1) (hN : 1 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1) (q : ℕ)
    (hne : q + s.card ≠ N + 1) :
    IsZero (relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
      (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) q) :=
  (isZero_dualBlockRelativeHomology_iff_link_all hgeom hK hsK hs q).mpr
    (isReducedAcyclicAt_link_of_sphere hK hsK hs hdim hN e q hne)

/-- The top relative group does not vanish, including the zero-dimensional
dual block whose boundary is empty. No positive-degree restriction is used. -/
theorem not_isZero_dualBlockRelativeHomology_of_sphere_all
    (hgeom : IsGeometricRealization K p) (hK : FaceClosed K)
    (hsK : s ∈ K) (hs : s.Nonempty) {N : ℕ}
    (hdim : Module.finrank ℝ F = N + 1) (hN : 2 ≤ N)
    (e : ↥(barycentricCarrier K) ≃ₜ sphere (0 : F) 1) (q : ℕ)
    (heq : q + s.card = N + 1) :
    ¬ IsZero (relativeHomology (X := TopCat.of ↥(dualBlockSpace K p s))
      (Subtype.val ⁻¹' dualBlockBoundarySpace K p s) q) := by
  intro h
  exact not_isReducedAcyclicAt_link_of_sphere hK hsK hs hdim e q hN heq
    ((isZero_dualBlockRelativeHomology_iff_link_all hgeom hK hsK hs q).mp h)

end AffineTverberg.Simplicial
