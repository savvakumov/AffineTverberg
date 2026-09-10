import AffineTverberg.PolytopalLocalProjection
import AffineTverberg.ConicalFineNeighborhood
import AffineTverberg.SingularHomologyBasisDescent
import AffineTverberg.PolytopalIncidenceHomology

set_option linter.style.header false

/-!
# The global homology range of the actual polytopal sphere projection

The conical model of `Y` gives, around every sphere parameter, an open
neighborhood whose full projection preimage deformation retracts to the
literal fiber; the upper-face shelling gives acyclicity of that fiber below
`n`. The neighborhoods obtained from the separating functionals can moreover
be taken arbitrarily small, so the resulting family of opens is a basis of
the topology of the parameter sphere.

Their finite intersections need not have a dominating center, so the finite
good-cover theorem is not available. The descent theorem of
`SingularHomologyBasisDescent` — Mayer--Vietoris with the shifted
intersection hypothesis, combined with compact supports — applies instead
and yields the global range for the actual map with no further hypothesis.
-/

noncomputable section

open Set CategoryTheory HomologicalComplex AffineTverberg.AffChain

namespace AffineTverberg.PolytopalJoinMap

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Φ : PolytopalJoinMap P m V)

/-- **Arbitrarily small actual local fiber regularity of `Y → S`.** -/
theorem exists_fine_open_topIncidenceFiberHomotopyEquiv (y : DualUnitSphere V)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (DualUnitSphere V), IsOpen U ∧ y ∈ U ∧
      (∀ x ∈ U, ‖x.val - y.val‖ < ε) ∧ ContractibleSpace U ∧
      Nonempty (ContinuousMap.HomotopyEquiv ↥(Φ.topIncidenceProjection ⁻¹' U)
        (Φ.TopIncidenceFiber y)) := by
  obtain ⟨U, ho, hy, hsmall, hU, ⟨e⟩⟩ := ConicalIncidence.exists_fine_open_fiberHomotopyEquiv
    (topConicalPiece (P := P) (m := m)) Φ.faceParameterSet
    Φ.faceParameterSet_isClosed Φ.convex_faceParameterSet Φ.zero_mem_faceParameterSet
    Φ.smul_mem_faceParameterSet y hε
  let eU : ↥((ConicalIncidence.projection
      (topConicalPiece (P := P) (m := m)) Φ.faceParameterSet) ⁻¹' U) ≃ₜ
      ↥(Φ.topIncidenceProjection ⁻¹' U) :=
    Φ.topConicalHomeomorph.subtype (fun _ ↦ Iff.rfl)
  let eF : ↥((ConicalIncidence.projection
      (topConicalPiece (P := P) (m := m)) Φ.faceParameterSet) ⁻¹' {y}) ≃ₜ
      Φ.TopIncidenceFiber y :=
    Φ.topConicalHomeomorph.subtype (fun _ ↦ Iff.rfl)
  exact ⟨U, ho, hy, hsmall, hU,
    ⟨(eU.symm.toHomotopyEquiv.trans e).trans eF.toHomotopyEquiv⟩⟩

/-- The corresponding arbitrarily small local homology range. -/
theorem exists_fine_open_topIncidence_homologyRange {q : ℕ} (y : DualUnitSphere V)
    {ε : ℝ} (hε : 0 < ε)
    (hfib : SingularAcyclicBelow (TopCat.of (Φ.TopIncidenceFiber y)) q) :
    ∃ U : Set (DualUnitSphere V), IsOpen U ∧ y ∈ U ∧ (∀ x ∈ U, ‖x.val - y.val‖ < ε) ∧
      HomologyRange (singChainsMap
        (preimageRestriction Φ.topIncidenceProjectionTopHom U)) q := by
  obtain ⟨U, ho, hy, hsmall, hU, ⟨e⟩⟩ :=
    Φ.exists_fine_open_topIncidenceFiberHomotopyEquiv y hε
  exact ⟨U, ho, hy, hsmall,
    homologyRange_of_acyclic_contractible _ (hfib.of_homotopyEquiv e)⟩

/-- For a nondegenerate join map every parameter has arbitrarily small open
neighborhoods carrying the sharp homology range of the actual projection. -/
theorem exists_fine_open_topIncidence_homologyRange_of_nondegenerate
    (hn : 1 ≤ n) (hspan : FactorImagesAffinelySpan Φ.factor)
    (y : DualUnitSphere V) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (DualUnitSphere V), IsOpen U ∧ y ∈ U ∧ (∀ x ∈ U, ‖x.val - y.val‖ < ε) ∧
      HomologyRange (singChainsMap
        (preimageRestriction Φ.topIncidenceProjectionTopHom U)) n :=
  Φ.exists_fine_open_topIncidence_homologyRange y hε
    (BadVertex.singularAcyclicBelow_topIncidenceFiber hn hspan y)

/-- **The global homology range of the actual sphere projection.** The map
`Y → S^{n-1}` induces isomorphisms on singular homology in all degrees below
`n` and an epimorphism in degree `n`. No cover, triangulation or fiber
hypothesis is assumed: the fibers are handled by the upper-face argument and
the descent is genuine Mayer--Vietoris with compact supports. -/
theorem homologyRange_topIncidenceProjection
    (hn : 1 ≤ n) (hspan : FactorImagesAffinelySpan Φ.factor) :
    HomologyRange (singChainsMap Φ.topIncidenceProjectionTopHom) n := by
  classical
  set f := Φ.topIncidenceProjectionTopHom with hf
  set G : Set (Set (DualUnitSphere V)) :=
    {U | IsOpen U ∧ HomologyRange (singChainsMap (preimageRestriction f U)) n} with hG
  refine homologyRange_of_basis f G n (fun A hA => hA.1) ?_ (fun A hA => hA.2)
  intro y W hW hyW
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hW y hyW
  obtain ⟨U, ho, hyU, hsmall, hrange⟩ :=
    Φ.exists_fine_open_topIncidence_homologyRange_of_nondegenerate hn hspan y hε
  refine ⟨U, ⟨ho, hrange⟩, hyU, fun x hx => hball ?_⟩
  have hdist : dist x y = ‖x.val - y.val‖ := by
    rw [Subtype.dist_eq, dist_eq_norm]
  rw [Metric.mem_ball, hdist]
  exact hsmall x hx

/-- **Surjectivity of the actual sphere projection in the top degree.** -/
theorem surjective_topIncidenceProjection_homology
    (hn : 1 ≤ n) (hspan : FactorImagesAffinelySpan Φ.factor) :
    Function.Surjective ((realSingularHomology (n - 1)).map
      Φ.topIncidenceProjectionTopHom) := by
  have hrange := Φ.homologyRange_topIncidenceProjection hn hspan
  have hepi : Epi ((realSingularHomology (n - 1)).map Φ.topIncidenceProjectionTopHom) :=
    hrange.2 (n - 1) (by omega)
  exact (ModuleCat.epi_iff_surjective _).1 hepi

end AffineTverberg.PolytopalJoinMap

namespace AffineTverberg

/-- **The polytopal nondegenerate zero theorem.** For a nondegenerate
polytopal join map into the Sarkaria target the linear join map has an actual
zero on the deleted join. -/
theorem polytopalNondegenerateZero : polytopalNondegenerateZeroStatement := by
  intro d m hd hm P Φ hspan
  have hn : 1 ≤ (d + 1) * m := Nat.one_le_iff_ne_zero.2 (by positivity)
  have hsurj := Φ.surjective_topIncidenceProjection_homology hn hspan
  obtain ⟨w, hw⟩ :=
    Φ.exists_deletedJoinPoint_zero_of_singular_sphere_map hd hm hsurj
  exact (Φ.exists_mem_deletedJoinCarrier_joinMap_eq_zero_iff).mpr ⟨w, hw⟩

/-- **The polytopal half of the paper's main theorem, unconditionally.** -/
theorem polytopalMainTheorem : polytopalMainTheoremStatement :=
  polytopalMainTheoremStatement_of_nondegenerateZero polytopalNondegenerateZero

/-- The polytopal zero theorem in the form of the paper. -/
theorem polytopalZeroTheorem : polytopalZeroTheoremStatement :=
  polytopalZeroTheoremStatement_of_nondegenerate polytopalNondegenerateZero

end AffineTverberg
