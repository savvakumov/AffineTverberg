import AffineTverberg.RelativeHomologyComparison
import AffineTverberg.RelativeHomologyMaps
import AffineTverberg.BarycentricRealization

set_option linter.style.header false

/-!
# Relative comparison for actual geometric simplicial pairs

The relative comparison for barycentric realizations is transported along the
actual affine realization homeomorphism. It identifies relative simplicial
homology with the genuine relative singular homology of the given geometric
pair, in every degree.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Simplicial

open AffineTverberg.AffChain

variable {V E : Type} [Fintype V] [LinearOrder V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {L K : Finset (Finset V)} {p : V → E}

/-- The geometric subcomplex as a literal subset of the ambient realization. -/
def geometricSubcomplexRealization (L K : Finset (Finset V)) (p : V → E) :
    Set ↥(geometricCarrier K p) := Subtype.val ⁻¹' geometricCarrier L p

theorem geometricRealizationHomeomorph_mem_subcomplex
    (hgeom : IsGeometricRealization K p) (h : L ⊆ K) (x : barySpace K) :
    x ∈ subcomplexRealization L K ↔
      geometricRealizationHomeomorph hgeom x ∈ geometricSubcomplexRealization L K p :=
  (evaluation_mem_subfamily_iff hgeom h x.property).symm

/-- The actual affine realization map induces the relative chain map. -/
def geometricRelativeRealizationMap (hgeom : IsGeometricRealization K p) (h : L ⊆ K) :
    relCx (subcomplexRealization L K) ⟶
      relCx (X := TopCat.of ↥(geometricCarrier K p)) (geometricSubcomplexRealization L K p) :=
  relativeMap (TopCat.ofHom (geometricRealizationHomeomorph hgeom).toHomotopyEquiv.toFun)
    (fun x hx => (geometricRealizationHomeomorph_mem_subcomplex hgeom h x).mp hx)

theorem quasiIso_geometricRelativeRealizationMap
    (hgeom : IsGeometricRealization K p) (h : L ⊆ K) :
    QuasiIso (geometricRelativeRealizationMap hgeom h) :=
  quasiIso_relativeMap_of_homeomorph (X := barySpace K)
    (Y := TopCat.of ↥(geometricCarrier K p)) (geometricRealizationHomeomorph hgeom)
    (geometricRealizationHomeomorph_mem_subcomplex hgeom h)

/-- The comparison into the actual relative singular complex of the geometric pair. -/
def geometricRelativeComparisonChainMap (hL : FaceClosed L) (hK : FaceClosed K)
    (h : L ⊆ K) (hgeom : IsGeometricRealization K p) :
    simplicialRelativeCx hL hK h ⟶
      relCx (X := TopCat.of ↥(geometricCarrier K p)) (geometricSubcomplexRealization L K p) :=
  relativeComparisonChainMap hL hK h ≫ geometricRelativeRealizationMap hgeom h

theorem quasiIso_geometricRelativeComparisonChainMap (hL : FaceClosed L) (hK : FaceClosed K)
    (h : L ⊆ K) (hgeom : IsGeometricRealization K p) :
    QuasiIso (geometricRelativeComparisonChainMap hL hK h hgeom) := by
  have := quasiIso_relativeComparisonChainMap hL hK h
  have := quasiIso_geometricRelativeRealizationMap hgeom h
  dsimp only [geometricRelativeComparisonChainMap]
  infer_instance

/-- Relative simplicial homology agrees with actual geometric relative singular
homology, with no topological regularity beyond geometric realization. -/
def geometricRelativeComparisonHomologyIso (hL : FaceClosed L) (hK : FaceClosed K)
    (h : L ⊆ K) (hgeom : IsGeometricRealization K p) (k : ℕ) :
    (simplicialRelativeCx hL hK h).homology k ≅
      relativeHomology (X := TopCat.of ↥(geometricCarrier K p))
        (geometricSubcomplexRealization L K p) k := by
  have := quasiIso_geometricRelativeComparisonChainMap hL hK h hgeom
  exact asIso (HomologicalComplex.homologyMap
    (geometricRelativeComparisonChainMap hL hK h hgeom) k)

end AffineTverberg.Simplicial
