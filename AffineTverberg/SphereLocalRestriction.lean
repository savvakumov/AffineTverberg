import AffineTverberg.PuncturedSphere
import AffineTverberg.LocalStarRelativeHomology

set_option linter.style.header false

/-!
# The actual local restriction isomorphism on a geometric sphere

On a space homeomorphic to a norm sphere, the absolute-to-local-relative map
is an isomorphism in degrees at least two: the punctured sphere is
contractible. For a geometric triangulation, composing with excision and the
star-link identification computes this local homology on the actual link.
In particular, this supplies the local restriction of a global top class
without assuming PL links or ball-shaped dual blocks.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Metric

namespace AffineTverberg

open AffChain

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The actual global-to-local map, not merely an abstract isomorphism of groups. -/
theorem isIso_localRelativeProjection_of_homeomorph_sphere {X : TopCat.{0}}
    (e : X ≃ₜ sphere (0 : E) 1) (p : X) (k : ℕ) (hk : k ≠ 0) :
    IsIso (relPi ({p} : Set X)ᶜ (k + 1)) := by
  have : ContractibleSpace ↥(({p} : Set X)ᶜ) :=
    contractibleSpace_punctured_of_homeomorph_normSphere e p
  exact isIso_relPi_of_contractible _ k hk

variable {d : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace d)}
  {L : Finset (CoordinateSpace d)} {p : CoordinateSpace d}

/-- On a finite geometric sphere, every carrier link computes the shifted
global sphere homology via the actual local restriction and ray projection. -/
def sphereHomologyIsoClosedStarLink (hfin : K.faces.Finite) (hL : L ∈ K.faces)
    (hp : IsCarrierPoint K L p) (e : ↥K.space ≃ₜ sphere (0 : E) 1)
    (k : ℕ) (hk : k ≠ 0) :
    (realSingularHomology (k + 1)).obj (TopCat.of ↥K.space) ≅
      (realSingularHomology k).obj (TopCat.of ↥(closedStarLink K L)) := by
  have : IsIso (relPi (X := TopCat.of ↥K.space)
      ({(⟨p, hp.mem_space hL⟩ : ↥K.space)} : Set ↥K.space)ᶜ (k + 1)) :=
    isIso_localRelativeProjection_of_homeomorph_sphere (X := TopCat.of ↥K.space)
      e ⟨p, hp.mem_space hL⟩ k hk
  let eLocal := asIso (relPi (X := TopCat.of ↥K.space)
    ({(⟨p, hp.mem_space hL⟩ : ↥K.space)} : Set ↥K.space)ᶜ (k + 1))
  exact eLocal ≪≫ localRelativeHomologyIsoClosedStarLink hfin hL hp k hk

end AffineTverberg
