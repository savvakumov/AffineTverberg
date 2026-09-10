import AffineTverberg.SimplicialCellStructure
import AffineTverberg.SimplicialLemmaY

set_option linter.style.header false

/-!
# The actual cell incidence space in the simplicial-ball case

The global Sarkaria map of a simplexwise-affine map is defined only on the
concrete deleted join and is merely piecewise linear.  For the generic
incidence machinery it is convenient to extend it by zero off that carrier;
only its restrictions to deleted cells are ever used.  Those restrictions
agree with continuous linear Sarkaria maps.

This file constructs the incidence space `X` for that genuine global map,
proves compactness and contractibility of the first-projection fibers under
zero avoidance, and maps the ridge incidence space `Y` into this `X`.
-/

noncomputable section

open Set

namespace AffineTverberg

section AmbientExtension

variable {e n d m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- An auxiliary total extension of the genuine global Sarkaria map.  Its
values off the deleted join are irrelevant; on every deleted cell it is a
continuous linear map. -/
def simplicialGlobalSarkariaAmbient
    (φ : K.space → CoordinateSpace d) :
    PolytopalJoinAmbient e m → SarkariaTarget d m := by
  classical
  intro z
  exact if hz : z ∈ simplicialDeletedJoinCarrier n K m then
    simplicialGlobalSarkariaMap φ ⟨z, hz⟩ else 0

theorem simplicialGlobalSarkariaAmbient_eq
    (φ : K.space → CoordinateSpace d)
    (z : SimplicialDeletedJoinSpace n K m) :
    simplicialGlobalSarkariaAmbient (n := n) φ z.val =
      simplicialGlobalSarkariaMap φ z := by
  rw [simplicialGlobalSarkariaAmbient, dite_eq_left z.property]

/-- On a deleted cell, the auxiliary ambient extension agrees with every
cellwise affine representative of `φ`. -/
theorem simplicialGlobalSarkariaAmbient_eq_cellwise
    (φ : K.space → CoordinateSpace d)
    (F : SimplicialDeletedCellIndex n K m)
    (ψ : Fin (m + 1) → CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ i, ∀ y : K.space,
      y.val ∈ convexHull ℝ (F.val i : Set (CoordinateSpace e)) →
        φ y = ψ i y.val)
    {z : PolytopalJoinAmbient e m} (hz : z ∈ joinCellCarrier F.val) :
    simplicialGlobalSarkariaAmbient (n := n) φ z = simplicialSarkariaLinear ψ z := by
  have hzD : z ∈ simplicialDeletedJoinCarrier n K m :=
    joinCellCarrier_subset_simplicialDeletedJoinCarrier K F.property hz
  rw [simplicialGlobalSarkariaAmbient, dite_eq_left hzD]
  exact simplicialGlobalSarkariaMap_eq_cellwise φ ⟨z, hzD⟩ hz ψ hψ

theorem image_simplicialGlobalSarkariaAmbient_cell_eq
    (φ : K.space → CoordinateSpace d)
    (F : SimplicialDeletedCellIndex n K m)
    (ψ : Fin (m + 1) → CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ i, ∀ y : K.space,
      y.val ∈ convexHull ℝ (F.val i : Set (CoordinateSpace e)) →
        φ y = ψ i y.val) :
    simplicialGlobalSarkariaAmbient (n := n) φ '' joinCellCarrier F.val =
      simplicialSarkariaLinear ψ '' joinCellCarrier F.val := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, (simplicialGlobalSarkariaAmbient_eq_cellwise φ F ψ hψ hz).symm⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z, hz, simplicialGlobalSarkariaAmbient_eq_cellwise φ F ψ hψ hz⟩

theorem convex_image_simplicialGlobalSarkariaAmbient_cell
    (φ : K.space → CoordinateSpace d)
    (F : SimplicialDeletedCellIndex n K m)
    (ψ : Fin (m + 1) → CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ i, ∀ y : K.space,
      y.val ∈ convexHull ℝ (F.val i : Set (CoordinateSpace e)) →
        φ y = ψ i y.val) :
    Convex ℝ (simplicialGlobalSarkariaAmbient (n := n) φ '' joinCellCarrier F.val) := by
  rw [image_simplicialGlobalSarkariaAmbient_cell_eq φ F ψ hψ]
  exact (joinCellCarrier_convex F.val).is_linear_image
    (simplicialSarkariaLinear ψ).isLinear

theorem compact_image_simplicialGlobalSarkariaAmbient_cell
    (φ : K.space → CoordinateSpace d)
    (F : SimplicialDeletedCellIndex n K m)
    (ψ : Fin (m + 1) → CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ i, ∀ y : K.space,
      y.val ∈ convexHull ℝ (F.val i : Set (CoordinateSpace e)) →
        φ y = ψ i y.val) :
    IsCompact (simplicialGlobalSarkariaAmbient (n := n) φ '' joinCellCarrier F.val) := by
  rw [image_simplicialGlobalSarkariaAmbient_cell_eq φ F ψ hψ]
  exact (joinCellCarrier_compact F.val).image
    (simplicialSarkariaLinear ψ).toContinuousLinearMap.continuous

end AmbientExtension

section Incidence

variable {e n d m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- The cell incidence space `X` for the genuine piecewise Sarkaria map. -/
abbrev SimplicialDeletedCellIncidenceSpace
    (φ : K.space → CoordinateSpace d) :=
  FaceIncidenceSpace (simplicialDeletedJoinCarrier n K m)
    (fun F : SimplicialDeletedCellIndex n K m ↦ joinCellCarrier F.val)
    (simplicialGlobalSarkariaAmbient (n := n) φ)

/-- The second projection `X → S(V*)`. -/
def simplicialCellIncidenceDual
    (φ : K.space → CoordinateSpace d)
    (p : SimplicialDeletedCellIncidenceSpace (n := n) (m := m) φ) :
    DualUnitSphere (SarkariaTarget d m) :=
  ⟨p.1.2, p.2.1⟩

theorem continuous_simplicialCellIncidenceDual
    (φ : K.space → CoordinateSpace d) :
    Continuous (simplicialCellIncidenceDual (n := n) (m := m) φ) := by
  apply Continuous.subtype_mk
  exact continuous_snd.comp continuous_subtype_val

/-- The actual simplicial incidence space is compact. -/
theorem simplicialDeletedCellIncidenceSpace_compactSpace
    (φ : K.space → CoordinateSpace d) (hfin : K.faces.Finite) :
    CompactSpace (SimplicialDeletedCellIncidenceSpace (n := n) (m := m) φ) := by
  let : Fintype (SimplicialDeletedCellIndex n K m) :=
    Set.Finite.fintype (boundaryDeletedJoinCells_finite (n := n) (m := m) K hfin)
  let : Finite (SimplicialDeletedCellIndex n K m) :=
    Finite.of_fintype (SimplicialDeletedCellIndex n K m)
  exact faceIncidenceSpace_compactSpace
    (simplicialDeletedJoinCarrier_compact K hfin)
    fun F ↦ joinCellCarrier_isClosed F.val

/-- Minimal-cell data for a first-projection fiber of the actual simplicial
incidence space. -/
def simplicialCellIncidenceFiberData
    (φ : K.space → CoordinateSpace d)
    (hfin : K.faces.Finite)
    (hφ : IsAffineOnSimplicialFaces K φ)
    (hzero : ∀ z : SimplicialDeletedJoinSpace n K m,
      simplicialGlobalSarkariaMap φ z ≠ 0)
    (x : simplicialDeletedJoinCarrier n K m) :
    FaceIncidenceFiberData
      (fun F : SimplicialDeletedCellIndex n K m ↦ joinCellCarrier F.val)
      (simplicialGlobalSarkariaAmbient (n := n) φ)
      (x : PolytopalJoinAmbient e m) := by
  let F := simplicialMinimalCell hfin x.property
  let ψ := Classical.choose (exists_cellwise_affine_extension hφ F.property)
  have hψ := Classical.choose_spec (exists_cellwise_affine_extension hφ F.property)
  refine
    { index := F
      mem_face := mem_simplicialMinimalCell hfin x.property
      minimal := fun G hxG ↦ simplicialMinimalCell_subset hfin x.property G hxG
      image_convex := convex_image_simplicialGlobalSarkariaAmbient_cell φ F ψ hψ
      image_compact := compact_image_simplicialGlobalSarkariaAmbient_cell φ F ψ hψ
      image_nonempty := ?_
      image_avoids_zero := ?_ }
  · exact ⟨simplicialGlobalSarkariaAmbient (n := n) φ x,
      ⟨x, mem_simplicialMinimalCell hfin x.property, rfl⟩⟩
  · rintro ⟨w, hwF, hw0⟩
    have hwD : w ∈ simplicialDeletedJoinCarrier n K m :=
      joinCellCarrier_subset_simplicialDeletedJoinCarrier K F.property hwF
    have hne := hzero ⟨w, hwD⟩
    apply hne
    rw [← simplicialGlobalSarkariaAmbient_eq φ ⟨w, hwD⟩]
    exact hw0

theorem simplicialCellIncidenceFiber_contractible
    (φ : K.space → CoordinateSpace d)
    (hfin : K.faces.Finite)
    (hφ : IsAffineOnSimplicialFaces K φ)
    (hzero : ∀ z : SimplicialDeletedJoinSpace n K m,
      simplicialGlobalSarkariaMap φ z ≠ 0)
    (x : simplicialDeletedJoinCarrier n K m) :
    ContractibleSpace
      (FaceIncidenceFiber (simplicialDeletedJoinCarrier n K m)
        (fun F : SimplicialDeletedCellIndex n K m ↦ joinCellCarrier F.val)
        (simplicialGlobalSarkariaAmbient (n := n) φ) x) :=
  faceIncidenceFiber_contractible_of_data x
    (simplicialCellIncidenceFiberData φ hfin hφ hzero x)

theorem simplicialCellIncidenceProjection_surjective
    (φ : K.space → CoordinateSpace d)
    (hfin : K.faces.Finite)
    (hφ : IsAffineOnSimplicialFaces K φ)
    (hzero : ∀ z : SimplicialDeletedJoinSpace n K m,
      simplicialGlobalSarkariaMap φ z ≠ 0) :
    Function.Surjective
      (faceIncidenceProjection
        (D := simplicialDeletedJoinCarrier n K m)
        (G := fun F : SimplicialDeletedCellIndex n K m ↦ joinCellCarrier F.val)
        (Φ := simplicialGlobalSarkariaAmbient (n := n) φ)) :=
  faceIncidenceProjection_surjective
    (simplicialCellIncidenceFiberData φ hfin hφ hzero)

end Incidence

section RidgeInclusion

variable {e n d m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  {L : Finset (CoordinateSpace e)}

/-- The ridge incidence space `Y` maps into the actual cell incidence space
for the global piecewise Sarkaria map. -/
def ridgeToSimplicialCellIncidence
    (φ : K.space → CoordinateSpace d)
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ y : K.space,
      y.val ∈ convexHull ℝ (L : Set (CoordinateSpace e)) → φ y = ψ y.val)
    (hL : IsBoundaryRidge n K L) :
    RidgeIncidenceSpace L
        (simplicialSarkariaMap (m := m) fun _ : Fin (m + 1) ↦ ψ) →
      SimplicialDeletedCellIncidenceSpace (n := n) (m := m) φ := by
  intro p
  refine ⟨(⟨p.1.1.1, ridgeDeletedJoinCarrier_subset hL p.1.1.2⟩, p.1.2),
    p.2.1, ?_⟩
  obtain ⟨R, hzR, hnonneg⟩ := p.2.2
  let F : SimplicialDeletedCellIndex n K m :=
    ⟨R.faces, isBoundaryDeletedJoinCell_of_ridgeCell hL R⟩
  refine ⟨F, hzR, fun w hw ↦ ?_⟩
  have hface : ∀ i, ∀ y : K.space,
      y.val ∈ convexHull ℝ (F.val i : Set (CoordinateSpace e)) →
        φ y = ψ y.val := by
    intro i y hy
    apply hψ y
    apply convexHull_mono (𝕜 := ℝ) _ hy
    exact_mod_cast R.faces_subset i
  rw [simplicialGlobalSarkariaAmbient_eq_cellwise φ F (fun _ ↦ ψ) hface hw]
  exact hnonneg w hw

theorem continuous_ridgeToSimplicialCellIncidence
    (φ : K.space → CoordinateSpace d)
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ y : K.space,
      y.val ∈ convexHull ℝ (L : Set (CoordinateSpace e)) → φ y = ψ y.val)
    (hL : IsBoundaryRidge n K L) :
    Continuous (ridgeToSimplicialCellIncidence (m := m) φ ψ hψ hL) := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact Continuous.subtype_mk
      (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)) _
  · exact continuous_snd.comp continuous_subtype_val

theorem simplicialCellIncidenceDual_ridgeTo
    (φ : K.space → CoordinateSpace d)
    (ψ : CoordinateSpace e →ᵃ[ℝ] CoordinateSpace d)
    (hψ : ∀ y : K.space,
      y.val ∈ convexHull ℝ (L : Set (CoordinateSpace e)) → φ y = ψ y.val)
    (hL : IsBoundaryRidge n K L)
    (p : RidgeIncidenceSpace L
      (simplicialSarkariaMap (m := m) fun _ : Fin (m + 1) ↦ ψ)) :
    simplicialCellIncidenceDual (n := n) (m := m) φ
      (ridgeToSimplicialCellIncidence (m := m) φ ψ hψ hL p) =
        ridgeIncidenceDualProjection L
          (simplicialSarkariaMap (m := m) fun _ : Fin (m + 1) ↦ ψ) p := by
  apply Subtype.ext
  rfl

end RidgeInclusion

end AffineTverberg
