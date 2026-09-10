import AffineTverberg.SingularCohomology
import Mathlib.CategoryTheory.Abelian.Exact

set_option linter.style.header false

/-!
# Natural field duality for actual singular cohomology

Dualization over a field is exact even for the infinite-dimensional singular
chain groups. Its homology comparison is natural, so actual cochain pullbacks
can be tested using the duals of actual singular homology maps.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg
namespace RealCochain

/-- The ordinary algebraic dual functor over the coefficient field. -/
def dualFunctor : (ModuleCat.{0} ℝ)ᵒᵖ ⥤ ModuleCat.{0} ℝ where
  obj X := ModuleCat.of ℝ (Module.Dual ℝ X.unop)
  map f := ModuleCat.ofHom f.unop.hom.dualMap
  map_id X := by ext c x; rfl
  map_comp f g := by ext c x; rfl

instance : dualFunctor.Additive where
  map_add {X Y} {f g} := by
    apply ModuleCat.hom_ext
    change (f.unop.hom + g.unop.hom).dualMap =
      f.unop.hom.dualMap + g.unop.hom.dualMap
    ext c x
    exact map_add c _ _

/-- Exactness of field dualization, without a finite-dimensionality assumption. -/
instance : dualFunctor.PreservesHomology :=
  Functor.preservesHomology_of_map_exact dualFunctor fun S hS ↦
    (dualShortComplex_exact_iff S.unop).mpr hS.unop

/-- The canonical universal-coefficient isomorphism for a short chain complex. -/
def dualHomologyIso (S : ShortComplex (ModuleCat.{0} ℝ)) :
    (dualShortComplex S).homology ≅ ModuleCat.of ℝ (Module.Dual ℝ S.homology) :=
  S.op.mapHomologyIso dualFunctor ≪≫ dualFunctor.mapIso S.homologyOpIso

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility with the actual dual cochain map, not just an abstract
isomorphism of the cohomology vector spaces. -/
theorem dualHomologyIso_naturality {S T : ShortComplex (ModuleCat.{0} ℝ)}
    (f : S ⟶ T) :
    ShortComplex.homologyMap (dualShortComplexMap f) ≫ (dualHomologyIso S).hom =
      (dualHomologyIso T).hom ≫
        ModuleCat.ofHom (ShortComplex.homologyMap f).hom.dualMap := by
  change ShortComplex.homologyMap (dualFunctor.mapShortComplex.map
      (ShortComplex.opMap f)) ≫ _ = _ ≫ dualFunctor.map (ShortComplex.homologyMap f).op
  change ShortComplex.homologyMap (dualFunctor.mapShortComplex.map
      (ShortComplex.opMap f)) ≫
      ((S.op.mapHomologyIso dualFunctor).hom ≫ dualFunctor.map S.homologyOpIso.hom) =
    ((T.op.mapHomologyIso dualFunctor).hom ≫ dualFunctor.map T.homologyOpIso.hom) ≫
      dualFunctor.map (ShortComplex.homologyMap f).op
  rw [← Category.assoc, ShortComplex.mapHomologyIso_hom_naturality,
    Category.assoc, ← Functor.map_comp, ShortComplex.homologyOpIso_hom_naturality,
    Functor.map_comp, Category.assoc]

end RealCochain

/-- Actual singular cohomology is naturally the algebraic dual of actual
singular homology, over the real coefficient field. -/
def realSingularCohomologyDualIso (X : TopCat.{0}) (n : ℕ) :
    (realSingularCohomology n).obj (Opposite.op X) ≅
      ModuleCat.of ℝ (Module.Dual ℝ ((realSingularHomology n).obj X)) :=
  RealCochain.dualHomologyIso _

/-- The universal-coefficient square commutes for every continuous map. -/
theorem realSingularCohomologyDualIso_naturality {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) :
    (realSingularCohomology n).map f.op ≫ (realSingularCohomologyDualIso X n).hom =
      (realSingularCohomologyDualIso Y n).hom ≫
        ModuleCat.ofHom ((realSingularHomology n).map f).hom.dualMap :=
  RealCochain.dualHomologyIso_naturality
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℝ)
      (ComplexShape.down ℕ) n).map
        (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℝ)).obj
          (ModuleCat.of ℝ ℝ)).map f))

/-- The naturality square as an equality of the underlying functions. -/
theorem realSingularCohomologyDualIso_naturality_function {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) :
    (realSingularCohomologyDualIso X n).toLinearEquiv.toEquiv ∘
      (realSingularCohomology n).map f.op =
    ((realSingularHomology n).map f).hom.dualMap ∘
      (realSingularCohomologyDualIso Y n).toLinearEquiv.toEquiv := by
  funext c
  exact congrArg (fun g : (realSingularCohomology n).obj (Opposite.op Y) ⟶
      ModuleCat.of ℝ (Module.Dual ℝ ((realSingularHomology n).obj X)) ↦ g c)
    (realSingularCohomologyDualIso_naturality f n)

/-- Injectivity of the actual cohomology pullback is equivalent to
surjectivity on actual singular homology. -/
theorem realSingularCohomology_map_injective_iff {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) :
    Function.Injective ((realSingularCohomology n).map f.op) ↔
      Function.Surjective ((realSingularHomology n).map f) := by
  rw [← Equiv.comp_injective _ (realSingularCohomologyDualIso X n).toLinearEquiv.toEquiv,
    realSingularCohomologyDualIso_naturality_function f n,
    Equiv.injective_comp, LinearMap.dualMap_injective_iff]

/-- Surjectivity of the actual cohomology pullback is equivalent to
injectivity on actual singular homology. -/
theorem realSingularCohomology_map_surjective_iff {X Y : TopCat.{0}}
    (f : X ⟶ Y) (n : ℕ) :
    Function.Surjective ((realSingularCohomology n).map f.op) ↔
      Function.Injective ((realSingularHomology n).map f) := by
  rw [← Equiv.comp_surjective _ (realSingularCohomologyDualIso X n).toLinearEquiv.toEquiv,
    realSingularCohomologyDualIso_naturality_function f n,
    Equiv.surjective_comp, LinearMap.dualMap_surjective_iff]

end AffineTverberg
