import AffineTverberg.BarycentricIncidence
import AffineTverberg.SingularHomologyGluing

set_option linter.style.header false

/-!
# A direct homology theorem for finite facewise incidence projections

The open-star contractions and finite-open descent apply to the actual
projection map. This proves a special fiber theorem for support-restricted
incidence unions, not a general singular-cohomology proper-map theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace AffineTverberg
namespace AffChain

/-- Any continuous map between contractible spaces is a singular homology
equivalence, including ordinary degree zero. -/
theorem quasiIso_singChainsMap_of_contractible {X Y : TopCat.{0}}
    [ContractibleSpace X] [ContractibleSpace Y] (f : X ⟶ Y) :
    QuasiIso (singChainsMap f) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv X Y
  obtain ⟨y, h⟩ := id_nullhomotopic Y
  have h1 : f.hom.Homotopic (ContinuousMap.const X y) := by
    simpa using h.comp (ContinuousMap.Homotopic.refl f.hom)
  have h2 : e.toFun.Homotopic (ContinuousMap.const X y) := by
    simpa using h.comp (ContinuousMap.Homotopic.refl e.toFun)
  have hfg := h1.trans h2.symm
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  change IsIso ((realSingularHomology n).map f)
  rw [realSingularHomology_map_eq_of_homotopy
    (show TopCat.Homotopy f (TopCat.ofHom e.toFun) from hfg.some) n]
  exact (realSingularHomologyIsoOfHomotopyEquiv e n).isIso_hom

end AffChain

namespace Simplicial.BarycentricIncidence

open AffChain

variable {V Y ι : Type} [Fintype V] [TopologicalSpace Y]
variable {K : Finset (Finset V)} {J : ι → Finset V} {C : ι → Set Y}

/-- All finite nonempty coordinate-star restrictions are genuine homology
equivalences when all genuine incidence fibers are contractible. -/
theorem quasiIso_starRestriction (hK : FaceClosed K)
    (hfib : ∀ x : ↥(barycentricCarrier K),
      ContractibleSpace ↥((projection K J C) ⁻¹' {x}))
    {s : Finset V} (hs : s.Nonempty) :
    QuasiIso (singChainsMap (preimageRestriction
      (TopCat.ofHom (projection K J C)) (openStar K s))) := by
  classical
  by_cases hsK : s ∈ K
  · have := contractibleSpace_openStar hs hsK
    have := contractibleSpace_starPreimage_of_fibers hfib hs hsK
    exact quasiIso_singChainsMap_of_contractible _
  · have he : openStar K s = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp (fun hne ↦ hsK ((openStar_nonempty_iff hK hs).mp hne))
    rw [he]
    exact quasiIso_preimageRestriction_empty _

/-- The first-projection fiber theorem for finite support-restricted
incidence unions. There are no properness or semialgebraicity assumptions:
the special facewise form gives explicit contractions on an actual good cover. -/
theorem quasiIso_projection (hK : FaceClosed K)
    (hfib : ∀ x : ↥(barycentricCarrier K),
      ContractibleSpace ↥((projection K J C) ⁻¹' {x})) :
    QuasiIso (singChainsMap (TopCat.ofHom (projection K J C))) := by
  classical
  apply quasiIso_singChainsMap_of_finite_open_cover
    (TopCat.ofHom (projection K J C)) Finset.univ (fun v ↦ openStar K {v})
    (fun v _ ↦ isOpen_openStar K {v})
  · simpa using iUnion_openStar_singleton K
  · intro s _ hs
    rw [← openStar_eq_vertex_inter K s]
    exact quasiIso_starRestriction hK hfib hs

end Simplicial.BarycentricIncidence
end AffineTverberg
