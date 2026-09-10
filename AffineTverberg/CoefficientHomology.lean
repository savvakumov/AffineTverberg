import AffineTverberg.SingularHomology

set_option linter.style.header false

/-!
# Singular homology with arbitrary field coefficients

The geometric spaces remain real spaces. Only the coefficient field varies.
In particular this layer permits characteristic two, which is essential for
the unoriented fundamental-cycle argument used to find a boundary ridge.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.Coefficients

variable (𝕜 : Type) [Field 𝕜]

/-- Mathlib's actual singular homology with the specified coefficient field. -/
def singularHomology (n : ℕ) : TopCat.{0} ⥤ ModuleCat.{0} 𝕜 :=
  (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} 𝕜) n).obj (ModuleCat.of 𝕜 𝕜)

/-- The actual degree-zero augmentation, not a vanishing assertion about H0. -/
def singularAugmentation (X : TopCat.{0}) :
    (singularHomology 𝕜 0).obj X ⟶ ModuleCat.of 𝕜 𝕜 :=
  X.singularHomology₀ε (ModuleCat.of 𝕜 𝕜)

instance (X : TopCat.{0}) [PathConnectedSpace X] : IsIso (singularAugmentation 𝕜 X) := by
  exact TopCat.instIsIsoSingularHomology₀εOfPathConnectedSpaceCarrier X (ModuleCat.of 𝕜 𝕜)

theorem singularHomology_map_eq_of_homotopy {X Y : TopCat.{0}}
    {f g : X ⟶ Y} (H : TopCat.Homotopy f g) (n : ℕ) :
    (singularHomology 𝕜 n).map f = (singularHomology 𝕜 n).map g :=
  H.congr_homologyMap_singularChainComplexFunctor (ModuleCat.of 𝕜 𝕜) n

/-- The actual homology maps of a homotopy equivalence are inverse. -/
def singularHomologyIsoOfHomotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    (singularHomology 𝕜 n).obj (TopCat.of X) ≅
      (singularHomology 𝕜 n).obj (TopCat.of Y) where
  hom := (singularHomology 𝕜 n).map (TopCat.ofHom e.toFun)
  inv := (singularHomology 𝕜 n).map (TopCat.ofHom e.invFun)
  hom_inv_id := by
    rw [← Functor.map_comp]
    have h := singularHomology_map_eq_of_homotopy 𝕜
      (show TopCat.Homotopy ((TopCat.ofHom e.toFun) ≫ (TopCat.ofHom e.invFun))
        (𝟙 (TopCat.of X)) from e.left_inv.some) n
    exact h.trans (CategoryTheory.Functor.map_id _ _)
  inv_hom_id := by
    rw [← Functor.map_comp]
    have h := singularHomology_map_eq_of_homotopy 𝕜
      (show TopCat.Homotopy ((TopCat.ofHom e.invFun) ≫ (TopCat.ofHom e.toFun))
        (𝟙 (TopCat.of Y)) from e.right_inv.some) n
    exact h.trans (CategoryTheory.Functor.map_id _ _)

theorem singularHomology_subsingleton_iff_of_homotopyEquiv
    {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (e : ContinuousMap.HomotopyEquiv X Y) (n : ℕ) :
    Subsingleton ((singularHomology 𝕜 n).obj (TopCat.of X)) ↔
      Subsingleton ((singularHomology 𝕜 n).obj (TopCat.of Y)) := by
  let i := singularHomologyIsoOfHomotopyEquiv 𝕜 e n
  constructor
  · intro h
    let := h
    exact Function.Injective.subsingleton (ConcreteCategory.bijective_of_isIso i.inv).1
  · intro h
    let := h
    exact Function.Injective.subsingleton (ConcreteCategory.bijective_of_isIso i.hom).1

/-- Contractibility implies vanishing with every field of coefficients,
in positive degrees only. -/
theorem singularHomology_subsingleton_of_contractible
    (X : Type) [TopologicalSpace X] [ContractibleSpace X]
    (n : ℕ) (hn : n ≠ 0) :
    Subsingleton ((singularHomology 𝕜 n).obj (TopCat.of X)) := by
  obtain ⟨e⟩ := ContractibleSpace.hequiv_unit X
  apply (singularHomology_subsingleton_iff_of_homotopyEquiv 𝕜 e n).mpr
  exact ModuleCat.subsingleton_of_isZero
    (AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      (ModuleCat.{0} 𝕜) n (ModuleCat.of 𝕜 𝕜) (TopCat.of Unit) hn)

/-- The real specialization is definitionally the previously audited theory. -/
theorem singularHomology_real (n : ℕ) : singularHomology ℝ n = realSingularHomology n := rfl

end AffineTverberg.Coefficients
