import AffineTverberg.SingularHomologyRangeGluing
import AffineTverberg.BarycentricIncidenceHomology

set_option linter.style.header false

/-!
# Acyclic fibers and the sharp homology range for incidence projections

The explicit open-star deformation identifies a whole open-star preimage
with its genuine center fiber. Finite descent then gives isomorphisms below
the acyclicity cutoff and an epimorphism at the cutoff.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex

namespace AffineTverberg

open AffChain

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of Mathlib's actual degree-zero singular augmentation. -/
theorem realSingularAugmentation_naturality {X Y : TopCat.{0}} (f : X ⟶ Y) :
    (realSingularHomology 0).map f ≫ realSingularAugmentation Y =
      realSingularAugmentation X := by
  change homologyMap (singChainsMap f) 0 ≫ _ = _
  refine (cancel_epi ((singChains X).homologyπ 0)).mp ?_
  refine (cancel_epi ((singChains X).cycles₀Iso.inv)).mp ?_
  apply SSet.chainComplex_hom_ext
  intro x
  have hlift : ιs x ≫ (singChains X).cycles₀Iso.inv =
      (singChains X).liftCycles (ιs x) 0 (by simp) (by simp) := by
    rw [← cancel_mono ((singChains X).iCycles 0)]
    simp
  simp only [← Category.assoc (ιs x) (singChains X).cycles₀Iso.inv, hlift]
  rw [homologyπ_naturality_assoc, ← Category.assoc,
    liftCycles_comp_cyclesMap, SSet.ι_chainComplexMap_f]
  exact (SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε _ _ _).trans
    (SSet.liftCycles_ιChainComplex_homologyπ_homology₀ε _ _ x).symm

/-- Reduced singular acyclicity in degrees strictly below `q`, with
the actual augmentation in degree zero. -/
def SingularAcyclicBelow (X : TopCat.{0}) (q : ℕ) : Prop :=
  IsIso (realSingularAugmentation X) ∧
    ∀ k, k ≠ 0 → k < q → IsZero ((realSingularHomology k).obj X)

theorem SingularAcyclicBelow.of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {q : ℕ}
    (e : ContinuousMap.HomotopyEquiv X Y)
    (h : SingularAcyclicBelow (TopCat.of Y) q) :
    SingularAcyclicBelow (TopCat.of X) q := by
  constructor
  · have := h.1
    have he : IsIso ((realSingularHomology 0).map (TopCat.ofHom e.toFun)) :=
      (realSingularHomologyIsoOfHomotopyEquiv e 0).isIso_hom
    rw [← realSingularAugmentation_naturality (TopCat.ofHom e.toFun)]
    infer_instance
  · intro k hk hq
    exact (h.2 k hk hq).of_iso (realSingularHomologyIsoOfHomotopyEquiv e k)

/-- Any map from an acyclic space to a contractible space has the sharp
homology range. Positive-degree target homology is zero even at the cutoff. -/
theorem homologyRange_of_acyclic_contractible {X Y : TopCat.{0}}
    [ContractibleSpace Y] {q : ℕ} (f : X ⟶ Y)
    (hX : SingularAcyclicBelow X q) : HomologyRange (singChainsMap f) q := by
  have hzero : IsIso ((realSingularHomology 0).map f) := by
    have := hX.1
    have hcomp : IsIso ((realSingularHomology 0).map f ≫ realSingularAugmentation Y) := by
      rw [realSingularAugmentation_naturality]
      infer_instance
    exact (isIso_comp_right_iff _ _).mp hcomp
  have hY : ∀ k, k ≠ 0 → IsZero ((realSingularHomology k).obj Y) :=
    fun k hk ↦ ModuleCat.isZero_iff_subsingleton.mpr
      (realSingularHomology_subsingleton_of_contractible Y k hk)
  constructor
  · intro k hk
    change IsIso ((realSingularHomology k).map f)
    by_cases hk0 : k = 0
    · subst k
      exact hzero
    · exact (hX.2 k hk0 hk).isIso (hY k hk0) _
  · intro k _
    change Epi ((realSingularHomology k).map f)
    by_cases hk0 : k = 0
    · subst k
      infer_instance
    · exact (hY k hk0).epi _

namespace Simplicial.BarycentricIncidence

variable {V Y ι : Type} [Fintype V] [TopologicalSpace Y]
  {K : Finset (Finset V)} {J : ι → Finset V} {C : ι → Set Y}

/-- The full open-star preimage is homotopy equivalent to the genuine
fiber over the barycenter, not just to an auxiliary parameter model. -/
def starPreimageFiberHomotopyEquiv [DecidableEq V]
    {s : Finset V} (hs : s.Nonempty) (hsK : s ∈ K) :
    ContinuousMap.HomotopyEquiv
      ↥((projection K J C) ⁻¹' openStar K s)
      ↥((projection K J C) ⁻¹' {centerPoint hs hsK}) := by
  classical
  exact ((starPreimageHomeomorph (J := J) (C := C) s).toHomotopyEquiv.trans
    (starHomotopyEquiv hs hsK)).trans (centerFiberHomeomorph hs hsK).symm.toHomotopyEquiv

theorem homologyRange_starRestriction (hK : FaceClosed K) {q : ℕ}
    (hfib : ∀ x : ↥(barycentricCarrier K),
      SingularAcyclicBelow (TopCat.of ↥((projection K J C) ⁻¹' {x})) q)
    {s : Finset V} (hs : s.Nonempty) :
    HomologyRange (singChainsMap (preimageRestriction
      (TopCat.ofHom (projection K J C)) (openStar K s))) q := by
  classical
  by_cases hsK : s ∈ K
  · have := contractibleSpace_openStar hs hsK
    exact homologyRange_of_acyclic_contractible _
      ((hfib (centerPoint hs hsK)).of_homotopyEquiv (starPreimageFiberHomotopyEquiv hs hsK))
  · have he : openStar K s = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp (fun hne ↦ hsK ((openStar_nonempty_iff hK hs).mp hne))
    rw [he]
    have := quasiIso_preimageRestriction_empty (TopCat.ofHom (projection K J C))
    exact homologyRange_of_quasiIso _ q

/-- **The sharp acyclic-fiber theorem for finite support incidence.** The
actual projection is an isomorphism on homology below `q` and surjective in
degree `q`; no general singular-cohomology proper-map theorem is assumed. -/
theorem homologyRange_projection (hK : FaceClosed K) {q : ℕ}
    (hfib : ∀ x : ↥(barycentricCarrier K),
      SingularAcyclicBelow (TopCat.of ↥((projection K J C) ⁻¹' {x})) q) :
    HomologyRange (singChainsMap (TopCat.ofHom (projection K J C))) q := by
  classical
  apply homologyRange_singChainsMap_of_finite_open_cover
    (TopCat.ofHom (projection K J C)) q Finset.univ (fun v ↦ openStar K {v})
    (fun v _ ↦ isOpen_openStar K {v})
  · simpa using iUnion_openStar_singleton K
  · intro s _ hs
    rw [← openStar_eq_vertex_inter K s]
    exact homologyRange_starRestriction hK hfib hs

end Simplicial.BarycentricIncidence

end AffineTverberg
