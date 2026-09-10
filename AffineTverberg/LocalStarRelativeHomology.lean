import AffineTverberg.RelativeHomologyShift
import AffineTverberg.StarLinkHomotopy

set_option linter.style.header false

/-!
# Actual local relative homology and closed-star links

For every carrier point in a finite geometric simplicial complex, excision,
the contractible open star, and the ray homotopy give an isomorphism
`H_(k+1)(|K|, |K| \ {p}) ≅ H_k(closedStarLink K L)` for positive `k`.
No PL or combinatorial-manifold condition is imposed on the complex.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg

open AffChain

variable {e : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  {L : Finset (CoordinateSpace e)} {p : CoordinateSpace e}

/-- The actual open star, as a subset of the actual polyhedron. -/
def openStarInSpace (K : Geometry.SimplicialComplex ℝ (CoordinateSpace e))
    (L : Finset (CoordinateSpace e)) : Set ↥K.space := Subtype.val ⁻¹' openStarCone K L

theorem contractibleSpace_openStarInSpace (hfin : K.faces.Finite) (hL : L ∈ K.faces)
    (hp : IsCarrierPoint K L p) : ContractibleSpace ↥(openStarInSpace K L) := by
  have : ContractibleSpace ↥(openStarCone K L) :=
    (starConvex_openStarCone hL hp).contractibleSpace ⟨p, mem_openStarCone_apex hfin hL hp⟩
  exact (subsetSubtypeHomeomorph
    (openStarCone_subset_space (K := K) (L := L))).toHomotopyEquiv.contractibleSpace

/-- The punctured open star in the double-subspace notation used by relative chains. -/
def puncturedStarSubspaceHomeomorph (hL : L ∈ K.faces) (hp : IsCarrierPoint K L p) :
    ↥(intersectionInLeft (X := TopCat.of ↥K.space) (openStarInSpace K L)
      ({(⟨p, hp.mem_space hL⟩ : ↥K.space)} : Set ↥K.space)ᶜ) ≃ₜ
      ↥(puncturedOpenStar K L p) where
  toFun x := ⟨x.1.1.1, x.1.2, fun h => x.2 (Subtype.ext h)⟩
  invFun x := ⟨⟨⟨x.1, puncturedOpenStar_subset_space x.2⟩, x.2.1⟩,
    fun h => x.2.2 (congrArg Subtype.val h)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The actual relative local homology is shifted homology of the closed-star link. -/
def localRelativeHomologyIsoClosedStarLink (hfin : K.faces.Finite) (hL : L ∈ K.faces)
    (hp : IsCarrierPoint K L p) (k : ℕ) (hk : k ≠ 0) :
    relativeHomology (X := TopCat.of ↥K.space)
      ({(⟨p, hp.mem_space hL⟩ : ↥K.space)} : Set ↥K.space)ᶜ (k + 1) ≅
      (realSingularHomology k).obj (TopCat.of ↥(closedStarLink K L)) := by
  have : ContractibleSpace ↥(openStarInSpace K L) :=
    contractibleSpace_openStarInSpace hfin hL hp
  exact
    (puncturedRelativeHomologyIso (X := TopCat.of ↥K.space) (U := openStarInSpace K L)
      ⟨p, hp.mem_space hL⟩ (isOpen_preimage_openStarCone hfin)
      (mem_openStarCone_apex hfin hL hp) (k + 1)).symm ≪≫
    relativeHomologyShiftIsoOfContractible _ k hk ≪≫
    realSingularHomologyIsoOfHomotopyEquiv
      (puncturedStarSubspaceHomeomorph hL hp).toHomotopyEquiv k ≪≫
    realSingularHomologyIsoOfHomotopyEquiv
      (puncturedOpenStarLinkHomotopyEquiv hfin hL hp) k

end AffineTverberg
