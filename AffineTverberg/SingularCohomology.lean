import AffineTverberg.SarkariaSphereHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

set_option linter.style.header false

/-!
# Actual singular cochains and their cohomology

The cochain differential is precomposition with the singular boundary. We
dualize the three-term chain complex in each degree and take its actual
homology (cocycles modulo coboundaries). Dualization also gives the
contravariant functor on spaces, with the two commuting squares proved.

Over the real field, annihilator identities show that this cohomology
vanishes exactly when singular homology does. This gives the nonzero class
on the actual Sarkaria dual sphere in the cohomology functor used by the
final obstruction. No proper-map or Alexander-duality conclusion is assumed
or proved in this file.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg

namespace RealCochain

/-- Dualizing `A → B → C` produces the cochain complex `C* → B* → A*`.
The zero-composite identity follows from the original chain identity. -/
def dualShortComplex (S : ShortComplex (ModuleCat.{0} ℝ)) :
    ShortComplex (ModuleCat.{0} ℝ) :=
  ShortComplex.moduleCatMk S.g.hom.dualMap S.f.hom.dualMap (by
    ext c x
    change c (S.g (S.f x)) = 0
    rw [S.moduleCat_zero_apply, map_zero])

/-- The cochain map is literally precomposition in all three degrees. -/
def dualShortComplexMap {S T : ShortComplex (ModuleCat.{0} ℝ)} (f : S ⟶ T) :
    dualShortComplex T ⟶ dualShortComplex S where
  τ₁ := ModuleCat.ofHom f.τ₃.hom.dualMap
  τ₂ := ModuleCat.ofHom f.τ₂.hom.dualMap
  τ₃ := ModuleCat.ofHom f.τ₁.hom.dualMap
  comm₁₂ := by
    apply ModuleCat.hom_ext
    change S.g.hom.dualMap.comp f.τ₃.hom.dualMap =
      f.τ₂.hom.dualMap.comp T.g.hom.dualMap
    ext c x
    change c (f.τ₃ (S.g x)) = c (T.g (f.τ₂ x))
    exact congrArg c (congrArg (fun k : S.X₂ ⟶ T.X₃ ↦ k x) f.comm₂₃).symm
  comm₂₃ := by
    apply ModuleCat.hom_ext
    change S.f.hom.dualMap.comp f.τ₂.hom.dualMap =
      f.τ₁.hom.dualMap.comp T.f.hom.dualMap
    ext c x
    change c (f.τ₂ (S.f x)) = c (T.f (f.τ₁ x))
    exact congrArg c (congrArg (fun k : S.X₁ ⟶ T.X₂ ↦ k x) f.comm₁₂).symm

/-- Dualization of short chain complexes as a genuine contravariant functor. -/
def dualShortComplexFunctor :
    (ShortComplex (ModuleCat.{0} ℝ))ᵒᵖ ⥤ ShortComplex (ModuleCat.{0} ℝ) where
  obj S := dualShortComplex S.unop
  map f := dualShortComplexMap f.unop
  map_id S := by
    apply ShortComplex.hom_ext <;> ext c <;> rfl
  map_comp f g := by
    apply ShortComplex.hom_ext <;> ext c <;> rfl

/-- Field duality detects exactness, without any finite-dimensionality
assumption on the chain groups. In particular it applies to singular chains. -/
theorem dualShortComplex_exact_iff (S : ShortComplex (ModuleCat.{0} ℝ)) :
    (dualShortComplex S).Exact ↔ S.Exact := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker,
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change LinearMap.range S.g.hom.dualMap = LinearMap.ker S.f.hom.dualMap ↔ _
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    LinearMap.ker_dualMap_eq_dualAnnihilator_range, Subspace.dualAnnihilator_inj]
  exact eq_comm

theorem isZero_dualShortComplex_homology_iff (S : ShortComplex (ModuleCat.{0} ℝ)) :
    IsZero (dualShortComplex S).homology ↔ IsZero S.homology := by
  rw [← ShortComplex.exact_iff_isZero_homology,
    ← ShortComplex.exact_iff_isZero_homology, dualShortComplex_exact_iff]

end RealCochain

/-- Ordinary singular cohomology with real coefficients, defined using
the actual dual singular chain differentials. -/
def realSingularCohomology (n : ℕ) : TopCat.{0}ᵒᵖ ⥤ ModuleCat.{0} ℝ :=
  (((AlgebraicTopology.singularChainComplexFunctor (ModuleCat.{0} ℝ)).obj
      (ModuleCat.of ℝ ℝ)) ⋙
    HomologicalComplex.shortComplexFunctor (ModuleCat.{0} ℝ) (ComplexShape.down ℕ) n).op ⋙
      RealCochain.dualShortComplexFunctor ⋙ ShortComplex.homologyFunctor _

/-- The universal-coefficient vanishing equivalence for the actual singular
cochain complex over the real field. -/
theorem isZero_realSingularCohomology_iff (X : TopCat.{0}) (n : ℕ) :
    IsZero ((realSingularCohomology n).obj (Opposite.op X)) ↔
      IsZero ((realSingularHomology n).obj X) :=
  RealCochain.isZero_dualShortComplex_homology_iff _

theorem subsingleton_realSingularCohomology_iff (X : TopCat.{0}) (n : ℕ) :
    Subsingleton ((realSingularCohomology n).obj (Opposite.op X)) ↔
      Subsingleton ((realSingularHomology n).obj X) := by
  rw [← ModuleCat.isZero_iff_subsingleton, ← ModuleCat.isZero_iff_subsingleton,
    isZero_realSingularCohomology_iff]

/-- The concrete nonzero cohomology group required by the final incidence
obstruction, with no sphere-class hypothesis left over. -/
theorem nontrivial_sarkariaDualSphereCohomology {d m : ℕ}
    (hd : 1 ≤ d) (hm : 1 ≤ m) :
    Nontrivial ((realSingularCohomology ((d + 1) * m - 1)).obj
      (Opposite.op (TopCat.of (DualUnitSphere (SarkariaTarget d m))))) := by
  have hn := nontrivial_sarkariaDualSphereHomology hd hm
  apply not_subsingleton_iff_nontrivial.mp
  intro hz
  exact not_subsingleton _ ((subsingleton_realSingularCohomology_iff _ _).mp hz)

end AffineTverberg
