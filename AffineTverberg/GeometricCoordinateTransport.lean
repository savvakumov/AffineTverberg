import AffineTverberg.GeometricComplex
import AffineTverberg.GeometricRelativeHomologyComparison

set_option linter.style.header false

/-!
# Changing coordinates in a finite geometric simplicial pair

A continuous linear equivalence preserves the actual geometric realization,
including its subcomplex and relative homology. This lets the Cayley join
model use the already proved local homology theorems in coordinate space.
No PL or local-link assumption is introduced.
-/

noncomputable section

open Set CategoryTheory

namespace AffineTverberg.Simplicial

variable {V E F : Type}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K L : Finset (Finset V)} {p : V → E}

/-- The geometric carrier is transported by the literal linear change of coordinates. -/
theorem geometricCarrier_image_linearEquiv (e : E ≃L[ℝ] F) :
    e '' geometricCarrier K p = geometricCarrier K (e ∘ p) := by
  change e.toLinearMap '' geometricCarrier K p = _
  have he : (e.toLinearMap : E → F) = e := rfl
  simp only [geometricCarrier, Set.image_iUnion, LinearMap.image_convexHull,
    Set.image_image, Function.comp_def]
  simp only [he]

/-- Coordinate changes preserve both simplex independence and the gluing axiom. -/
theorem IsGeometricRealization.linearEquiv [DecidableEq V]
    (hgeom : IsGeometricRealization K p)
    (e : E ≃L[ℝ] F) : IsGeometricRealization K (e ∘ p) := by
  constructor
  · intro s hs
    exact (hgeom.independent s hs).map' e.toLinearMap.toAffineMap e.injective
  · intro s hs t ht x hx
    have himage (u : Finset V) :
        convexHull ℝ ((e ∘ p) '' (u : Set V)) =
          e '' convexHull ℝ (p '' (u : Set V)) := by
      have he : (e.toLinearMap : E → F) = e := rfl
      simpa only [Set.image_image, he, Function.comp_def] using
        (e.toLinearMap.image_convexHull (p '' (u : Set V))).symm
    rw [himage s, himage t] at hx
    obtain ⟨y, hy, rfl⟩ := hx.1
    obtain ⟨z, hz, hzy⟩ := hx.2
    have hzy' : z = y := e.injective hzy
    rw [himage (s ∩ t)]
    exact ⟨y, hgeom.intersection s hs t ht ⟨hy, hzy' ▸ hz⟩, rfl⟩

/-- The homeomorphism is the restriction of the ambient coordinate change. -/
def geometricCarrierLinearHomeomorph (e : E ≃L[ℝ] F) :
    ↥(geometricCarrier K p) ≃ₜ ↥(geometricCarrier K (e ∘ p)) :=
  (e.toHomeomorph.image (geometricCarrier K p)).trans
    (Homeomorph.setCongr (geometricCarrier_image_linearEquiv e))

@[simp]
theorem geometricCarrierLinearHomeomorph_apply (e : E ≃L[ℝ] F)
    (x : ↥(geometricCarrier K p)) :
    (geometricCarrierLinearHomeomorph e x).val = e x.val := rfl

/-- Every subcomplex is carried to the corresponding subcomplex, not just the ambient carrier. -/
theorem geometricCarrierLinearHomeomorph_mem_subcomplex (e : E ≃L[ℝ] F)
    (x : ↥(geometricCarrier K p)) :
    x ∈ geometricSubcomplexRealization L K p ↔
      geometricCarrierLinearHomeomorph e x ∈
        geometricSubcomplexRealization L K (e ∘ p) := by
  change x.val ∈ geometricCarrier L p ↔ e x.val ∈ geometricCarrier L (e ∘ p)
  rw [← geometricCarrier_image_linearEquiv e]
  constructor
  · intro hx
    exact ⟨x.val, hx, rfl⟩
  · rintro ⟨y, hy, heq⟩
    simpa only [e.injective heq] using hy

/-- Consequently the actual relative singular homology is coordinate invariant. -/
def geometricRelativeCoordinateHomologyIso (e : E ≃L[ℝ] F) (k : ℕ) :
    AffChain.relativeHomology
      (X := TopCat.of ↥(geometricCarrier K p))
      (geometricSubcomplexRealization L K p) k ≅
    AffChain.relativeHomology
      (X := TopCat.of ↥(geometricCarrier K (e ∘ p)))
      (geometricSubcomplexRealization L K (e ∘ p)) k :=
  AffChain.relativeHomologyIsoOfHomeomorph
    (X := TopCat.of ↥(geometricCarrier K p))
    (Y := TopCat.of ↥(geometricCarrier K (e ∘ p)))
    (geometricCarrierLinearHomeomorph e)
    (geometricCarrierLinearHomeomorph_mem_subcomplex e) k

end AffineTverberg.Simplicial
