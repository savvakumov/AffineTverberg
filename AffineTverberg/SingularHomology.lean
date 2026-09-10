import AffineTverberg.BarycentricRealization
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.AlgebraicTopology.SingularHomology.HomologyZero
import Mathlib.Topology.Homotopy.Contractible

set_option linter.style.header false

/-!
# Singular homology consequences of the geometric constructions

The groups in this file are Mathlib's singular homology groups with real
coefficients. Homotopy invariance turns the explicit induced-complement
retraction into an isomorphism of these groups. We also obtain the positive-
degree vanishing needed for contractible incidence fibers. These results
do not assume a simplicial-to-singular comparison theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg

/-- Ordinary singular homology with real coefficients, using Mathlib's
singular simplicial set and alternating-face-map chain complex. -/
def realSingularHomology (n : ℕ) : TopCat.{0} ⥤ ModuleCat.{0} ℝ :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℝ) n).obj (ModuleCat.of ℝ ℝ)

/-- The genuine augmentation on degree-zero singular homology. Its
invertibility expresses reduced degree-zero acyclicity. -/
def realSingularAugmentation (X : TopCat.{0}) :
    (realSingularHomology 0).obj X ⟶ ModuleCat.of ℝ ℝ :=
  X.singularHomology₀ε (ModuleCat.of ℝ ℝ)

instance (X : TopCat.{0}) [PathConnectedSpace X] : IsIso (realSingularAugmentation X) := by
  exact TopCat.instIsIsoSingularHomology₀εOfPathConnectedSpaceCarrier X (ModuleCat.of ℝ ℝ)

/-- Homotopic maps induce exactly the same map on these homology groups. -/
theorem realSingularHomology_map_eq_of_homotopy {X Y : TopCat.{0}}
    {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (n : ℕ) :
    (realSingularHomology n).map f = (realSingularHomology n).map g :=
  H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of ℝ ℝ) n

/-- A homotopy equivalence induces inverse isomorphisms on singular homology. -/
def realSingularHomologyIsoOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (realSingularHomology n).obj (TopCat.of X) ≅
      (realSingularHomology n).obj (TopCat.of Y) where
  hom := (realSingularHomology n).map (TopCat.ofHom e.toFun)
  inv := (realSingularHomology n).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp]
    have h := realSingularHomology_map_eq_of_homotopy
      (show TopCat.Homotopy ((TopCat.ofHom e.toFun) ≫ (TopCat.ofHom e.invFun))
        (𝟙 (TopCat.of X)) from e.left_inv.some) n
    exact h.trans (CategoryTheory.Functor.map_id _ _)
  inv_hom_id := by
    rw [← Functor.map_comp]
    have h := realSingularHomology_map_eq_of_homotopy
      (show TopCat.Homotopy ((TopCat.ofHom e.invFun) ≫ (TopCat.ofHom e.toFun))
        (𝟙 (TopCat.of Y)) from e.right_inv.some) n
    exact h.trans (CategoryTheory.Functor.map_id _ _)

/-- Vanishing of singular homology is invariant under the concrete
homotopy equivalences used here. -/
theorem realSingularHomology_subsingleton_iff_of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Subsingleton ((realSingularHomology n).obj (TopCat.of X)) ↔
      Subsingleton ((realSingularHomology n).obj (TopCat.of Y)) := by
  let i := realSingularHomologyIsoOfHomotopyEquiv e n
  constructor
  · intro h
    let := h
    exact Function.Injective.subsingleton
      (show Function.Injective i.inv from fun x y hxy ↦ by
        have h := congrArg i.hom hxy
        simpa using h)
  · intro h
    let := h
    exact Function.Injective.subsingleton
      (show Function.Injective i.hom from fun x y hxy ↦ by
        have h := congrArg i.inv hxy
        simpa using h)

/-- Contractible spaces have zero ordinary singular homology in positive
degrees. The restriction `n ≠ 0` is essential for a nonempty space. -/
theorem realSingularHomology_subsingleton_of_contractible
    (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) :
    Subsingleton ((realSingularHomology n).obj (TopCat.of X)) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  apply (realSingularHomology_subsingleton_iff_of_homotopyEquiv e n).mpr
  exact ModuleCat.subsingleton_of_isZero
    (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} ℝ) n (ModuleCat.of ℝ ℝ) (TopCat.of Unit) hn)

/-- Full reduced-acyclicity information for a contractible space, including
the augmentation endpoint rather than incorrectly asserting `H₀ = 0`. -/
theorem realSingularHomology_contractible
    (X : Type) [TopologicalSpace X] [ContractibleSpace X] :
    IsIso (realSingularAugmentation (TopCat.of X)) ∧
      ∀ n, n ≠ 0 → Subsingleton ((realSingularHomology n).obj (TopCat.of X)) :=
  ⟨inferInstance, realSingularHomology_subsingleton_of_contractible X⟩

namespace Simplicial

variable {V E : Type} [Fintype V] [DecidableEq V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The induced-complement lemma on actual singular homology, in all
ordinary degrees, obtained from the verified geometric homotopy. -/
def singularHomologyIso_inducedComplement
    {K : Finset (Finset V)} {p : V → E}
    (hK : FaceClosed K) (hgeom : IsGeometricRealization K p) (G : Finset V) (n : ℕ) :
    (realSingularHomology n).obj
      (TopCat.of ↥(geometricCarrier K p \ geometricCarrier (inducedFaces K Gᶜ) p)) ≅
    (realSingularHomology n).obj (TopCat.of ↥(geometricCarrier (inducedFaces K G) p)) :=
  realSingularHomologyIsoOfHomotopyEquiv (geometricInducedComplementHomotopyEquiv hK hgeom G) n

end Simplicial

end AffineTverberg
