import AffineTverberg.UpperFiberAcyclicity
import AffineTverberg.PolytopalParameterCones

set_option linter.style.header false

/-!
# Local homology of the actual polytopal sphere projection

The upper-face shelling proves acyclicity of the genuine fibers. The conical
neighborhood deformation transports it to whole open preimages, giving the
local homology range with all geometric and fiber hypotheses discharged.
The global sphere-projection conclusion still requires a descent argument.
-/

noncomputable section

open CategoryTheory AffineTverberg.AffChain

namespace AffineTverberg.PolytopalJoinMap

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
  (Φ : PolytopalJoinMap P m V)

/-- For a nondegenerate join map, every parameter has an open neighborhood
on which the actual projection induces isomorphisms below `n` and an
epimorphism in degree `n`. No acyclicity assumption remains. -/
theorem exists_open_topIncidence_homologyRange_of_nondegenerate
    (hn : 1 ≤ n) (hspan : FactorImagesAffinelySpan Φ.factor)
    (y : DualUnitSphere V) :
    ∃ U : Set (DualUnitSphere V), IsOpen U ∧ y ∈ U ∧
      HomologyRange (singChainsMap (preimageRestriction Φ.topIncidenceProjectionTopHom U)) n :=
  Φ.exists_open_topIncidence_homologyRange y
    (BadVertex.singularAcyclicBelow_topIncidenceFiber hn hspan y)

end AffineTverberg.PolytopalJoinMap
