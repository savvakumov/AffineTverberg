import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Data.Real.Basic

set_option linter.style.header false

/-!
# Compactness lemmas for perturbing the join map

The proof of `theorem:zero` first perturbs a possibly degenerate map while
keeping its image of the deleted join away from the origin.  This file
formalizes the two compactness facts behind that reduction: avoidance of
zero is stable under a sufficiently small uniform perturbation, and zeros
of approximating maps have a limiting zero on a compact domain.
-/

noncomputable section

open Filter Set Topology

namespace AffineTverberg

variable {E V : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup V]

/-- A continuous map from a compact set which avoids zero is uniformly
bounded away from zero.  Consequently every sufficiently close map also
avoids zero on that set. -/
theorem compact_zero_avoidance_stable
    {K : Set E} (hK : IsCompact K) {f : E → V} (hf : Continuous f)
    (havoid : (0 : V) ∉ f '' K) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ g : E → V,
      (∀ x ∈ K, ‖g x - f x‖ < ε) → (0 : V) ∉ g '' K := by
  by_cases hne : K.Nonempty
  · obtain ⟨x, hx, hxmin⟩ :=
      hK.exists_isMinOn hne ((continuous_norm.comp hf).continuousOn)
    have hfx_ne : f x ≠ 0 := by
      intro hfx
      exact havoid ⟨x, hx, hfx⟩
    have heps : 0 < ‖f x‖ := norm_pos_iff.mpr hfx_ne
    refine ⟨‖f x‖, heps, ?_⟩
    intro g hclose hzero
    obtain ⟨z, hz, hgz⟩ := hzero
    have hmin : ‖f x‖ ≤ ‖f z‖ := hxmin hz
    have hlt := hclose z hz
    rw [hgz, zero_sub, norm_neg] at hlt
    exact (not_lt_of_ge hmin) hlt
  · have hKempty : K = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨1, zero_lt_one, ?_⟩
    simp [hKempty]

/-- If values of a continuous map along a sequence in a compact set tend
to zero, then the map has an actual zero in the compact set. -/
theorem exists_zero_of_values_tendsto_zero
    {K : Set E} (hK : IsCompact K) {f : E → V} (hf : Continuous f)
    (x : ℕ → E) (hx : ∀ n, x n ∈ K)
    (hvalues : Tendsto (fun n ↦ f (x n)) atTop (𝓝 0)) :
    ∃ z ∈ K, f z = 0 := by
  obtain ⟨z, hz, ψ, hψ, hxz⟩ := hK.tendsto_subseq hx
  refine ⟨z, hz, ?_⟩
  apply tendsto_nhds_unique
    ((hf.continuousAt.tendsto.comp hxz))
  simpa [Function.comp_def] using hvalues.comp hψ.tendsto_atTop

/-- A convenient moving-map version: approximate maps have zeros on a
fixed compact set, and their errors at those zeros tend to zero.  Then the
limit map has a zero as well. -/
theorem exists_zero_of_approximate_maps
    {K : Set E} (hK : IsCompact K) {f : E → V} (hf : Continuous f)
    (g : ℕ → E → V) (x : ℕ → E) (hx : ∀ n, x n ∈ K)
    (hzero : ∀ n, g n (x n) = 0)
    (herror : Tendsto (fun n ↦ ‖g n (x n) - f (x n)‖) atTop (𝓝 0)) :
    ∃ z ∈ K, f z = 0 := by
  apply exists_zero_of_values_tendsto_zero hK hf x hx
  rw [tendsto_zero_iff_norm_tendsto_zero]
  convert herror using 1
  funext n
  rw [hzero n, zero_sub, norm_neg]

end AffineTverberg
