import AffineTverberg.ConicalIncidence
import AffineTverberg.PolytopalCohomologicalObstruction

set_option linter.style.header false

/-!
# Actual conical parameter neighborhoods for the polytopal Y projection

The finite face description of Y and its closed parameter cones give direct
local deformations of the actual projection preimages onto the actual fibers.
This proves local regularity; global homology descent is a separate step.
-/

noncomputable section

open Set

namespace AffineTverberg.PolytopalJoinMap

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Φ : PolytopalJoinMap P m V)

theorem zero_mem_faceParameterSet (T : PolytopalJoinFaceIndex P m) :
    (0 : StrongDual ℝ V) ∈ Φ.faceParameterSet T := by
  rw [Φ.faceParameterSet_eq_iInter]
  simp

theorem convex_faceParameterSet (T : PolytopalJoinFaceIndex P m) :
    Convex ℝ (Φ.faceParameterSet T) := by
  rw [Φ.faceParameterSet_eq_iInter]
  intro y hy z hz a b ha hb _
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hy hz ⊢
  intro u hu w hw hp
  simp only [add_apply, smul_apply, smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left (hy u hu w hw hp) ha)
    (mul_le_mul_of_nonneg_left (hz u hu w hw hp) hb)

theorem smul_mem_faceParameterSet (T : PolytopalJoinFaceIndex P m)
    (t : ℝ) (ht : 0 ≤ t) (y : StrongDual ℝ V) (hy : y ∈ Φ.faceParameterSet T) :
    t • y ∈ Φ.faceParameterSet T := by
  rw [Φ.faceParameterSet_eq_iInter] at hy ⊢
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hy ⊢
  intro u hu w hw hp
  simp only [smul_apply, smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (hy u hu w hw hp) ht

/-- The geometric pieces of the exact finite conical model of Y. -/
def topConicalPiece (T : PolytopalJoinFaceIndex P m) : Set (PolytopalJoinAmbient n m) :=
  polytopalDeletedJoinCarrier P m ∩ polytopalJoinFaceCarrier T

/-- The exact finite conical model is homeomorphic to the actual incidence
space Y, with both coordinates unchanged. -/
def topConicalHomeomorph :
    ConicalIncidence.Space (topConicalPiece (P := P) (m := m)) Φ.faceParameterSet ≃ₜ
      Φ.TopIncidenceSpace where
  toFun z := ⟨(⟨z.val.1, (Classical.choose_spec z.property).1.1⟩, z.val.2), by
    obtain ⟨i, hx, hy⟩ := z.property
    exact hy hx.2⟩
  invFun z := ⟨(z.val.1.val, z.val.2), by
    obtain ⟨i, hi, hy, _⟩ :=
      Φ.exists_joinFace_mem_of_mem_topLocus z.val.2.val z.property
    exact ⟨i, ⟨z.val.1.property, hi⟩, hy⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The model identification preserves the actual sphere projection. -/
theorem topConicalHomeomorph_projection
    (z : ConicalIncidence.Space (topConicalPiece (P := P) (m := m)) Φ.faceParameterSet) :
    Φ.topIncidenceProjection (Φ.topConicalHomeomorph z) =
      ConicalIncidence.projection (topConicalPiece (P := P) (m := m)) Φ.faceParameterSet z :=
  rfl

/-- **Actual local fiber regularity of Y->sphere.** Every parameter has an
open contractible neighborhood whose full projection preimage is homotopy
equivalent to its genuine fiber. No shelling or fiber-acyclicity input is
needed for this geometric assertion. -/
theorem exists_open_topIncidenceFiberHomotopyEquiv (y : DualUnitSphere V) :
    ∃ U : Set (DualUnitSphere V), IsOpen U ∧ y ∈ U ∧ ContractibleSpace U ∧
      Nonempty (ContinuousMap.HomotopyEquiv ↥(Φ.topIncidenceProjection ⁻¹' U)
        (Φ.TopIncidenceFiber y)) := by
  obtain ⟨U, ho, hy, hU, ⟨e⟩⟩ := ConicalIncidence.exists_open_fiberHomotopyEquiv
    (topConicalPiece (P := P) (m := m)) Φ.faceParameterSet
    Φ.faceParameterSet_isClosed Φ.convex_faceParameterSet Φ.zero_mem_faceParameterSet
    Φ.smul_mem_faceParameterSet y
  let eU : ↥((ConicalIncidence.projection
      (topConicalPiece (P := P) (m := m)) Φ.faceParameterSet) ⁻¹' U) ≃ₜ
      ↥(Φ.topIncidenceProjection ⁻¹' U) :=
    Φ.topConicalHomeomorph.subtype (fun _ ↦ Iff.rfl)
  let eF : ↥((ConicalIncidence.projection
      (topConicalPiece (P := P) (m := m)) Φ.faceParameterSet) ⁻¹' {y}) ≃ₜ
      Φ.TopIncidenceFiber y :=
    Φ.topConicalHomeomorph.subtype (fun _ ↦ Iff.rfl)
  exact ⟨U, ho, hy, hU, ⟨(eU.symm.toHomotopyEquiv.trans e).trans eF.toHomotopyEquiv⟩⟩

open CategoryTheory HomologicalComplex AffChain

/-- The corresponding local conclusion on the actual singular homology map.
Global descent is deliberately not asserted from this local statement alone. -/
theorem exists_open_topIncidence_homologyRange {q : ℕ} (y : DualUnitSphere V)
    (hfib : SingularAcyclicBelow (TopCat.of (Φ.TopIncidenceFiber y)) q) :
    ∃ U : Set (DualUnitSphere V), IsOpen U ∧ y ∈ U ∧
      HomologyRange (singChainsMap (preimageRestriction Φ.topIncidenceProjectionTopHom U)) q := by
  obtain ⟨U, ho, hy, hU, ⟨e⟩⟩ := Φ.exists_open_topIncidenceFiberHomotopyEquiv y
  exact ⟨U, ho, hy, homologyRange_of_acyclic_contractible _ (hfib.of_homotopyEquiv e)⟩

end AffineTverberg.PolytopalJoinMap
