import AffineTverberg.ConicalIncidenceHomology
import AffineTverberg.RidgeFiberSingularAcyclicity
import AffineTverberg.SimplicialCohomologicalObstruction

set_option linter.style.header false

/-!
# The actual ridge projection on singular homology

The ridge incidence is an exact finite conical model: for each ridge cell the
parameter cone consists of dual functionals nonnegative on its image. The
already proved fiber acyclicity and global conical descent establish the
epimorphism in degree `L.card - 1`, including the sharp endpoint required by
the simplicial-ball argument.
-/

noncomputable section

open Set CategoryTheory AffineTverberg.AffChain

namespace AffineTverberg

variable {e m : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (L : Finset (CoordinateSpace e)) (Φ : PolytopalJoinAmbient e m →L[ℝ] E)

/-- The closed convex cone of parameters nonnegative on a ridge cell. -/
def ridgeParameterCone (F : RidgeDeletedCellIndex L m) : Set (StrongDual ℝ E) :=
  {y | ∀ z ∈ F.carrier, 0 ≤ y (Φ z)}

theorem isClosed_ridgeParameterCone (F : RidgeDeletedCellIndex L m) :
    IsClosed (ridgeParameterCone L Φ F) := by
  have h : ridgeParameterCone L Φ F =
      ⋂ z ∈ F.carrier, {y : StrongDual ℝ E | 0 ≤ y (Φ z)} := by
    ext y
    simp [ridgeParameterCone]
  rw [h]
  exact isClosed_iInter fun z ↦ isClosed_iInter fun _ ↦
    isClosed_le continuous_const (by fun_prop)

theorem convex_ridgeParameterCone (F : RidgeDeletedCellIndex L m) :
    Convex ℝ (ridgeParameterCone L Φ F) := by
  intro y hy z hz a b ha hb _ w hw
  simp only [add_apply, smul_apply, smul_eq_mul]
  exact add_nonneg (mul_nonneg ha (hy w hw)) (mul_nonneg hb (hz w hw))

theorem zero_mem_ridgeParameterCone (F : RidgeDeletedCellIndex L m) :
    (0 : StrongDual ℝ E) ∈ ridgeParameterCone L Φ F := by
  intro z _
  simp

theorem smul_mem_ridgeParameterCone (F : RidgeDeletedCellIndex L m)
    (t : ℝ) (ht : 0 ≤ t) (y : StrongDual ℝ E) (hy : y ∈ ridgeParameterCone L Φ F) :
    t • y ∈ ridgeParameterCone L Φ F := by
  intro z hz
  simpa only [smul_apply, smul_eq_mul] using mul_nonneg ht (hy z hz)

/-- Exact model of the actual ridge incidence, preserving both coordinates. -/
def ridgeConicalHomeomorph :
    ConicalIncidence.Space (fun F : RidgeDeletedCellIndex L m ↦ F.carrier)
      (ridgeParameterCone L Φ) ≃ₜ RidgeIncidenceSpace L Φ where
  toFun z := ⟨(⟨z.val.1, by
      obtain ⟨F, hz, _⟩ := z.property
      exact carrier_subset_ridgeDeletedJoinCarrier F hz⟩, z.val.2.val),
    z.val.2.property, z.property⟩
  invFun z := ⟨(z.val.1.val, ⟨z.val.2, z.property.1⟩), z.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- This model equivalence restricts to the literal projection fibers. -/
def ridgeConicalFiberHomeomorph (y : DualUnitSphere E) :
    ↥((ConicalIncidence.projection (fun F : RidgeDeletedCellIndex L m ↦ F.carrier)
      (ridgeParameterCone L Φ)) ⁻¹' {y}) ≃ₜ RidgeIncidenceFiber L Φ y :=
  (ridgeConicalHomeomorph L Φ).subtype (fun _ ↦ Iff.rfl)

/-- **The actual ridge projection has the sharp global homology range.**
No map theorem or geometric comparison is assumed. -/
theorem homologyRange_ridgeIncidenceProjection
    (hL : AffineIndependent ℝ ((↑) : L → CoordinateSpace e))
    (hdiag : ∀ x : CoordinateSpace e, ∑ i : Fin (m + 1), Φ (polytopalJoinCopy i x) = 0)
    (hcard : 2 ≤ L.card) :
    HomologyRange (singChainsMap (TopCat.ofHom
      (⟨ridgeIncidenceDualProjection L Φ, continuous_ridgeIncidenceDualProjection L Φ⟩ :
        C(RidgeIncidenceSpace L Φ, DualUnitSphere E)))) (L.card - 1) := by
  have hmodel := ConicalIncidence.homologyRange_projection
    (fun F : RidgeDeletedCellIndex L m ↦ F.carrier) (ridgeParameterCone L Φ)
    (isClosed_ridgeParameterCone L Φ) (convex_ridgeParameterCone L Φ)
    (zero_mem_ridgeParameterCone L Φ) (smul_mem_ridgeParameterCone L Φ) (L.card - 1)
    (fun y ↦ ?_)
  · let f := TopCat.ofHom (ConicalIncidence.projection
      (fun F : RidgeDeletedCellIndex L m ↦ F.carrier) (ridgeParameterCone L Φ))
    let g := TopCat.ofHom
      (⟨ridgeIncidenceDualProjection L Φ, continuous_ridgeIncidenceDualProjection L Φ⟩ :
        C(RidgeIncidenceSpace L Φ, DualUnitSphere E))
    exact (homologyRange_singChainsMap_iff_of_iso f g
      (TopCat.isoOfHomeo (ridgeConicalHomeomorph L Φ)) (Iso.refl _) rfl (L.card - 1)).mp hmodel
  · obtain ⟨_, haug, hvan⟩ := ridgeFiber_singular_acyclicity L Φ y hL hdiag hcard
    have hfib : SingularAcyclicBelow (TopCat.of (RidgeIncidenceFiber L Φ y)) (L.card - 1) :=
      ⟨haug, fun k hk hkn ↦ hvan k hk (by omega)⟩
    exact hfib.of_homotopyEquiv (ridgeConicalFiberHomeomorph L Φ y).toHomotopyEquiv

/-- In the paper's degree, the actual Sarkaria ridge projection is
surjective on singular homology, including the top endpoint. -/
theorem surjective_ridgeIncidenceProjection_homology
    {d : ℕ} (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hL : AffineIndependent ℝ ((↑) : L → CoordinateSpace e)) (hcard : 2 ≤ L.card) :
    Function.Surjective ((realSingularHomology (L.card - 1)).map
      (ridgeIncidenceDualProjectionTopHom (L := L) (m := m) ψ)) := by
  have h := homologyRange_ridgeIncidenceProjection L
    (simplicialSarkariaMap (m := m) (fun _ ↦ ψ)) hL
    (sum_simplicialSarkariaMap_copy_eq_zero ψ) hcard
  exact (ModuleCat.epi_iff_surjective _).mp (h.2 _ le_rfl)

end AffineTverberg
