import AffineTverberg.SphereHomology
import AffineTverberg.PolytopalPerturbation
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option linter.style.header false

/-!
# The nonzero class on the actual Sarkaria dual sphere

The incidence spaces use norm-one continuous functionals, rather than a
separately chosen Euclidean sphere. This file transports the explicit
simplex-boundary class to exactly that space in degree `(d + 1) * m - 1`.
The ordinary degree is positive in the main theorem's range.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem finrank_strongDual :
    Module.finrank ℝ (StrongDual ℝ E) = Module.finrank ℝ E := by
  have he := (LinearMap.toContinuousLinearMap :
    Module.Dual ℝ E ≃ₗ[ℝ] StrongDual ℝ E).finrank_eq
  rw [← he, Subspace.dual_finrank_eq]

/-- Compatibility of the project's norm-one subtype with `Metric.sphere`. -/
def dualUnitSphereHomeomorph :
    DualUnitSphere E ≃ₜ Metric.sphere (0 : StrongDual ℝ E) 1 :=
  Homeomorph.setCongr (by
    ext y
    change (‖y‖ = 1) ↔ y ∈ Metric.sphere (0 : StrongDual ℝ E) 1
    simp)

theorem nontrivial_dualUnitSphere_singularHomology {n : ℕ}
    (hdim : Module.finrank ℝ E = n + 2) :
    Nontrivial ((realSingularHomology (n + 1)).obj (TopCat.of (DualUnitSphere E))) := by
  have hn := Simplicial.nontrivial_singularHomology_sphere
    (E := StrongDual ℝ E) (n := n) (finrank_strongDual.trans hdim)
  apply not_subsingleton_iff_nontrivial.mp
  intro hz
  have hs := (realSingularHomology_subsingleton_iff_of_homotopyEquiv
    (dualUnitSphereHomeomorph (E := E)).toHomotopyEquiv (n + 1)).mp hz
  exact not_subsingleton _ hs

/-- The exact nonzero sphere group in the final Sarkaria incidence argument. -/
theorem nontrivial_sarkariaDualSphereHomology {d m : ℕ}
    (hd : 1 ≤ d) (hm : 1 ≤ m) :
    Nontrivial ((realSingularHomology ((d + 1) * m - 1)).obj
      (TopCat.of (DualUnitSphere (SarkariaTarget d m)))) := by
  have hN : 2 ≤ (d + 1) * m := by nlinarith
  have hdim : Module.finrank ℝ (SarkariaTarget d m) = (d + 1) * m - 2 + 2 := by
    rw [finrank_sarkariaTarget, Module.finrank_fin_fun]
    omega
  have hn := nontrivial_dualUnitSphere_singularHomology hdim
  have hdegree : (d + 1) * m - 2 + 1 = (d + 1) * m - 1 := by omega
  rwa [hdegree] at hn

end AffineTverberg
