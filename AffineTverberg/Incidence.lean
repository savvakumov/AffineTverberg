import AffineTverberg.ConvexFiber
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Bilinear

set_option linter.style.header false

/-!
# The incidence space in the proof of the zero theorem

This file formalizes the space `X` and its fibers from lines 390--429 of
`affine-tverberg17.tex`, for an abstract family of faces.  At a point with a
minimal face, the projection fiber is homeomorphic to the nonnegative dual
sphere of the image of that face.  Compactness, convexity, and avoidance of
zero then make the fiber contractible by `ConvexFiber.lean`.
-/

noncomputable section

open Set

namespace AffineTverberg

variable {Z E ι : Type*} [TopologicalSpace Z]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The union, over the designated faces `G i`, of the products of the face
with the unit dual functionals nonnegative on its image under `Φ`. -/
abbrev FaceIncidenceSpace (D : Set Z) (G : ι → Set Z) (Φ : Z → E) :=
  {p : D × StrongDual ℝ E //
    ‖p.2‖ = 1 ∧ ∃ i, (p.1 : Z) ∈ G i ∧ ∀ z ∈ G i, 0 ≤ p.2 (Φ z)}

/-- First projection of the face incidence space. -/
def faceIncidenceProjection {D : Set Z} {G : ι → Set Z} {Φ : Z → E} :
    FaceIncidenceSpace D G Φ → D :=
  fun p ↦ p.1.1

theorem continuous_faceIncidenceProjection {D : Set Z} {G : ι → Set Z}
    {Φ : Z → E} :
    Continuous (faceIncidenceProjection (D := D) (G := G) (Φ := Φ)) := by
  exact continuous_fst.comp continuous_subtype_val

/-- The fiber of the first projection over `x`. -/
abbrev FaceIncidenceFiber (D : Set Z) (G : ι → Set Z) (Φ : Z → E) (x : D) :=
  {p : FaceIncidenceSpace D G Φ // faceIncidenceProjection p = x}

/-- If `G iₓ` is the minimal designated face containing `x`, the incidence
fiber over `x` is homeomorphic to the unit functionals nonnegative on
`Φ '' G iₓ`. -/
def faceIncidenceFiberHomeomorph {D : Set Z} {G : ι → Set Z} {Φ : Z → E}
    (x : D) (iₓ : ι) (hx : (x : Z) ∈ G iₓ)
    (hminimal : ∀ i, (x : Z) ∈ G i → G iₓ ⊆ G i) :
    FaceIncidenceFiber D G Φ x ≃ₜ NonnegativeDualSphere (Φ '' G iₓ) where
  toFun p :=
    ⟨p.1.1.2, p.1.2.1, fun w hw ↦ by
      obtain ⟨z, hz, rfl⟩ := hw
      obtain ⟨i, hxi, hnonneg⟩ := p.1.2.2
      have hxi' : (x : Z) ∈ G i := by
        rw [← p.2]
        exact hxi
      exact hnonneg z (hminimal i hxi' hz)⟩
  invFun y :=
    ⟨⟨(x, y.1), y.2.1, iₓ, hx, fun z hz ↦ y.2.2 (Φ z) ⟨z, hz, rfl⟩⟩, rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact p.2.symm
    · rfl
  right_inv y := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Under the hypotheses used in the paper, every first-projection fiber of
the incidence space is contractible. -/
theorem faceIncidenceFiber_contractible {D : Set Z} {G : ι → Set Z} {Φ : Z → E}
    (x : D) (iₓ : ι) (hx : (x : Z) ∈ G iₓ)
    (hminimal : ∀ i, (x : Z) ∈ G i → G iₓ ⊆ G i)
    (hconvex : Convex ℝ (Φ '' G iₓ)) (hcompact : IsCompact (Φ '' G iₓ))
    (hne : (Φ '' G iₓ).Nonempty) (hzero : (0 : E) ∉ Φ '' G iₓ) :
    ContractibleSpace (FaceIncidenceFiber D G Φ x) := by
  let _ : ContractibleSpace (NonnegativeDualSphere (Φ '' G iₓ)) :=
    nonnegativeDualSphere_contractible hconvex hcompact.isClosed hne hzero
  exact (faceIncidenceFiberHomeomorph x iₓ hx hminimal).contractibleSpace

/-- The local geometric data supplied by the minimal face containing `x` in
the deleted join. -/
structure FaceIncidenceFiberData (G : ι → Set Z) (Φ : Z → E) (x : Z) where
  index : ι
  mem_face : x ∈ G index
  minimal : ∀ i, x ∈ G i → G index ⊆ G i
  image_convex : Convex ℝ (Φ '' G index)
  image_compact : IsCompact (Φ '' G index)
  image_nonempty : (Φ '' G index).Nonempty
  image_avoids_zero : (0 : E) ∉ Φ '' G index

/-- Packaged version of fiber contractibility using the minimal-face data. -/
theorem faceIncidenceFiber_contractible_of_data {D : Set Z} {G : ι → Set Z}
    {Φ : Z → E} (x : D) (h : FaceIncidenceFiberData G Φ x) :
    ContractibleSpace (FaceIncidenceFiber D G Φ x) :=
  faceIncidenceFiber_contractible x h.index h.mem_face h.minimal
    h.image_convex h.image_compact h.image_nonempty h.image_avoids_zero

/-- If every point has the minimal-face data used in the paper, the first
projection from the incidence space is surjective. -/
theorem faceIncidenceProjection_surjective {D : Set Z} {G : ι → Set Z} {Φ : Z → E}
    (hdata : ∀ x : D, FaceIncidenceFiberData G Φ x) :
    Function.Surjective
      (faceIncidenceProjection (D := D) (G := G) (Φ := Φ)) := by
  intro x
  let _ : ContractibleSpace (FaceIncidenceFiber D G Φ x) :=
    faceIncidenceFiber_contractible_of_data x (hdata x)
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit (FaceIncidenceFiber D G Φ x)
  let p := e.invFun ()
  exact ⟨p.1, p.2⟩

/-- For a finite closed face family over a compact base in finite dimension,
the incidence space `X` is compact. -/
theorem faceIncidenceSpace_compactSpace [Finite ι] [FiniteDimensional ℝ E]
    {D : Set Z} {G : ι → Set Z} {Φ : Z → E}
    (hD : IsCompact D) (hG : ∀ i, IsClosed (G i)) :
    CompactSpace (FaceIncidenceSpace D G Φ) := by
  let _ : CompactSpace D := isCompact_iff_compactSpace.mp hD
  have hnonnegative (i : ι) : IsClosed
      {p : D × StrongDual ℝ E | ∀ z ∈ G i, 0 ≤ p.2 (Φ z)} := by
    rw [show {p : D × StrongDual ℝ E | ∀ z ∈ G i, 0 ≤ p.2 (Φ z)} =
        ⋂ z, ⋂ (_hz : z ∈ G i), {p : D × StrongDual ℝ E | 0 ≤ p.2 (Φ z)} by
      ext p
      simp]
    exact isClosed_iInter fun z ↦ isClosed_iInter fun _hz ↦
      isClosed_le (continuous_const : Continuous (fun _ : D × StrongDual ℝ E ↦ (0 : ℝ)))
        ((ContinuousLinearMap.apply ℝ ℝ (Φ z)).continuous.comp
          (continuous_snd : Continuous (fun p : D × StrongDual ℝ E ↦ p.2)))
  have hface (i : ι) : IsClosed
      {p : D × StrongDual ℝ E |
        (p.1 : Z) ∈ G i ∧ ∀ z ∈ G i, 0 ≤ p.2 (Φ z)} :=
    ((hG i).preimage (continuous_subtype_val.comp continuous_fst)).inter
      (hnonnegative i)
  have hfaces : IsClosed
      {p : D × StrongDual ℝ E |
        ∃ i, (p.1 : Z) ∈ G i ∧ ∀ z ∈ G i, 0 ≤ p.2 (Φ z)} := by
    rw [show {p : D × StrongDual ℝ E |
        ∃ i, (p.1 : Z) ∈ G i ∧ ∀ z ∈ G i, 0 ≤ p.2 (Φ z)} =
        ⋃ i, {p : D × StrongDual ℝ E |
          (p.1 : Z) ∈ G i ∧ ∀ z ∈ G i, 0 ≤ p.2 (Φ z)} by
      ext p
      simp]
    exact isClosed_iUnion_of_finite hface
  have hsphere : IsCompact
      {p : D × StrongDual ℝ E | ‖p.2‖ = 1} := by
    rw [show {p : D × StrongDual ℝ E | ‖p.2‖ = 1} =
        Set.univ ×ˢ Metric.sphere (0 : StrongDual ℝ E) 1 by
      ext p
      simp]
    exact (isCompact_univ : IsCompact (Set.univ : Set D)).prod
      (isCompact_sphere (0 : StrongDual ℝ E) 1)
  exact isCompact_iff_compactSpace.mp (hsphere.inter_right hfaces)

end AffineTverberg
