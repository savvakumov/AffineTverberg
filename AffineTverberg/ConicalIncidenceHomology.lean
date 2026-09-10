import AffineTverberg.ConicalFineNeighborhood
import AffineTverberg.SingularHomologyBasisDescent

set_option linter.style.header false

/-!
# Global homology for finite conical incidence

The fine conical neighborhoods and the verified basis descent give the sharp
global range for arbitrary finite conical incidence data. The actual ridge
projection is an instance, with cones of nonnegative dual functionals.
-/

noncomputable section

open CategoryTheory AffineTverberg.AffChain

namespace AffineTverberg.ConicalIncidence

variable {X E ι : Type} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι]

/-- The global singular homology range of a finite conical incidence
projection, from the actual singular acyclicity of its literal fibers. -/
theorem homologyRange_projection (A : ι → Set X) (C : ι → Set E)
    (hcl : ∀ i, IsClosed (C i)) (hcv : ∀ i, Convex ℝ (C i))
    (h0 : ∀ i, (0 : E) ∈ C i)
    (hsmul : ∀ i (t : ℝ), 0 ≤ t → ∀ x ∈ C i, t • x ∈ C i)
    (q : ℕ)
    (hfib : ∀ y : UnitSphere E,
      SingularAcyclicBelow (TopCat.of ↥((projection A C) ⁻¹' {y})) q) :
    HomologyRange (singChainsMap (TopCat.ofHom (projection A C))) q := by
  let f := TopCat.ofHom (projection A C)
  let G : Set (Set (UnitSphere E)) :=
    {U | IsOpen U ∧ HomologyRange (singChainsMap (preimageRestriction f U)) q}
  apply homologyRange_of_basis f G q (fun _ h ↦ h.1) _ (fun _ h ↦ h.2)
  intro y W hW hyW
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hW y hyW
  obtain ⟨U, ho, hyU, hsmall, hrange⟩ :=
    exists_fine_open_homologyRange A C hcl hcv h0 hsmul y hε (hfib y)
  refine ⟨U, ⟨ho, hrange⟩, hyU, fun x hx ↦ hball ?_⟩
  rw [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm]
  exact hsmall x hx

end AffineTverberg.ConicalIncidence
