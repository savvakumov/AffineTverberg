import AffineTverberg.SingularHomology
import AffineTverberg.PolytopalCellIncidence
import AffineTverberg.SimplicialCellIncidence

set_option linter.style.header false

/-!
# Singular acyclicity of the first incidence-projection fibers

The geometric minimal-cell constructions give the actual reduced singular
acyclicity information for the fibers of `X → D`: an invertible augmentation
in degree zero and zero singular homology in every positive degree. This
supplies fiber information only; the global proper-map theorem is not
assumed or proved by this file.
-/

noncomputable section

open CategoryTheory

namespace AffineTverberg

/-- Minimal-face geometry gives the full singular-acyclicity data for
the corresponding incidence fiber, including degree zero. -/
theorem faceIncidenceFiber_singularAcyclic
    {Z E ι : Type} [TopologicalSpace Z] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : Set Z} {G : ι → Set Z} {Φ : Z → E}
    (x : D) (h : FaceIncidenceFiberData G Φ x) :
    IsIso (realSingularAugmentation (TopCat.of (FaceIncidenceFiber D G Φ x))) ∧
      ∀ q, q ≠ 0 → Subsingleton
        ((realSingularHomology q).obj (TopCat.of (FaceIncidenceFiber D G Φ x))) := by
  let : ContractibleSpace (FaceIncidenceFiber D G Φ x) :=
    faceIncidenceFiber_contractible_of_data x h
  exact realSingularHomology_contractible _

/-- The actual polytopal first-projection fibers are singular acyclic
under the zero-avoidance assumption used in the contradiction argument. -/
theorem PolytopalJoinMap.cellIncidenceFiber_singularAcyclic
    {n m : ℕ} {P : FullDimensionalPolytope n}
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Φ : PolytopalJoinMap P m E)
    (hzero : ∀ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z ≠ 0)
    (x : polytopalDeletedJoinCarrier P m) :
    let F := FaceIncidenceFiber (polytopalDeletedJoinCarrier P m)
      (fun C : PolytopalDeletedCellIndex P m ↦ C.carrier) (fun z ↦ Φ.joinMap z) x
    IsIso (realSingularAugmentation (TopCat.of F)) ∧
      ∀ q, q ≠ 0 → Subsingleton ((realSingularHomology q).obj (TopCat.of F)) :=
  faceIncidenceFiber_singularAcyclic x (Φ.cellIncidenceFiberData hzero x)

/-- The actual simplicial first-projection fibers are singular acyclic
for the global piecewise-affine Sarkaria map. -/
theorem simplicialCellIncidenceFiber_singularAcyclic
    {e n d m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
    (φ : K.space → CoordinateSpace d) (hfin : K.faces.Finite)
    (hφ : IsAffineOnSimplicialFaces K φ)
    (hzero : ∀ z : SimplicialDeletedJoinSpace n K m, simplicialGlobalSarkariaMap φ z ≠ 0)
    (x : simplicialDeletedJoinCarrier n K m) :
    let F := FaceIncidenceFiber (simplicialDeletedJoinCarrier n K m)
      (fun F : SimplicialDeletedCellIndex n K m ↦ joinCellCarrier F.val)
      (simplicialGlobalSarkariaAmbient (n := n) φ) x
    IsIso (realSingularAugmentation (TopCat.of F)) ∧
      ∀ q, q ≠ 0 → Subsingleton ((realSingularHomology q).obj (TopCat.of F)) :=
  faceIncidenceFiber_singularAcyclic x (simplicialCellIncidenceFiberData φ hfin hφ hzero x)

end AffineTverberg
