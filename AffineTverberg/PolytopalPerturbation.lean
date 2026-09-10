import AffineTverberg.PolytopalDeletedJoinRealization
import AffineTverberg.Perturbation
import AffineTverberg.DiagonalNondegeneracy
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option linter.style.header false

/-!
# The nondegenerate perturbation reduction for `theorem:zero`

The polytopal proof of `theorem:zero` in `affine-tverberg17.tex` first treats
the case of a *nondegenerate* affine join map, i.e. one whose factor images
affinely span the target, and then removes the nondegeneracy assumption by a
compactness/perturbation argument.  This file formalizes that reduction in the
concrete join model of `AffineTverberg/PolytopalJoin.lean`.

The three ingredients are:

* an explicit finite-dimensional approximation construction: given a join map
  `Φ` satisfying the diagonal relation, and a real parameter `c ≠ 0`, we build a
  join map `Φ.perturb` which still satisfies the diagonal relation, differs from
  `Φ` by the fixed linear correction `c • N` in two factors only, and whose
  factor images affinely span the target (`Φ.perturb` is nondegenerate);
* the exact formula `(Φ.perturb).joinMap = Φ.joinMap + perturbationCLM`, which
  makes the convergence on the compact concrete deleted join immediate;
* the limiting argument: zeros of the approximants live in the compact set
  `polytopalDeletedJoinCarrier P m`, a convergent subsequence produces a zero of
  `Φ.joinMap` there, and `PolytopalDeletedJoinRealization` converts that zero
  into a witness-level zero, which is the form of `theorem:zero`.

The correction `N` is produced by `exists_linearMap_add_smul_surjective`: for
linear maps between real vector spaces of equal finite dimension, every `A` can
be corrected to a surjective `A + c • N` for all `c ≠ 0`, by mapping a
complement of `ker A` by `A` and `ker A` isomorphically onto a complement of
`range A`.  The dimension bookkeeping works because
`finrank (SarkariaTarget d m) = (d + 1) * m` is exactly the dimension of the
ambient space of the polytope.
-/

noncomputable section

open Filter Set Topology Module
open scoped BigOperators

namespace AffineTverberg

section LinearCorrection

variable {E V : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup V] [Module ℝ V]

/-- Every linear map between real vector spaces of the same finite dimension can
be made surjective by an arbitrarily small linear correction: there is a fixed
`N` such that `A + c • N` is surjective for every nonzero scalar `c`.

The correction maps a complement of `ker A` to zero and `ker A` isomorphically
onto a complement of `range A`. -/
theorem exists_linearMap_add_smul_surjective [FiniteDimensional ℝ E] [FiniteDimensional ℝ V]
    (hdim : finrank ℝ V = finrank ℝ E) (A : E →ₗ[ℝ] V) :
    ∃ N : E →ₗ[ℝ] V, ∀ c : ℝ, c ≠ 0 → Function.Surjective ⇑(A + c • N) := by
  classical
  obtain ⟨K, hK⟩ := (LinearMap.ker A).exists_isCompl
  obtain ⟨C, hC⟩ := (LinearMap.range A).exists_isCompl
  have h1 := LinearMap.finrank_range_add_finrank_ker A
  have h2 := Submodule.finrank_add_eq_of_isCompl hC
  have hrank : finrank ℝ (LinearMap.ker A) = finrank ℝ C := by omega
  let e := LinearEquiv.ofFinrankEq (R := ℝ) (LinearMap.ker A) C hrank
  let pr := Submodule.projectionOnto (LinearMap.ker A) K hK
  refine ⟨C.subtype ∘ₗ (e.toLinearMap ∘ₗ pr), ?_⟩
  intro c hc v
  have hv : v ∈ LinearMap.range A ⊔ C := by rw [hC.sup_eq_top]; trivial
  rw [Submodule.mem_sup] at hv
  obtain ⟨a, ha, c₀, hc₀, rfl⟩ := hv
  obtain ⟨u, hu⟩ := ha
  set w : LinearMap.ker A := e.symm ⟨c₀, hc₀⟩ with hw
  refine ⟨(u - (pr u : E)) + c⁻¹ • (w : E), ?_⟩
  have hprpr : pr (pr u : E) = pr u := Submodule.projectionOnto_apply_left hK (pr u)
  have hprw : pr (w : E) = w := Submodule.projectionOnto_apply_left hK w
  have hAw : A (w : E) = 0 := w.2
  have hAp : A (pr u : E) = 0 := (pr u).2
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_sub, map_smul,
    LinearMap.comp_apply, Submodule.subtype_apply, hprpr, hprw, hAw, hAp, hu,
    zero_add, smul_smul, inv_mul_cancel₀ hc, one_smul]
  simp [hw]

/-- An affine map with surjective linear part is surjective. -/
theorem affineMap_surjective_of_linear_surjective (f : E →ᵃ[ℝ] V)
    (hf : Function.Surjective f.linear) : Function.Surjective f := by
  intro v
  obtain ⟨u, hu⟩ := hf (v - f 0)
  refine ⟨u, ?_⟩
  have h2 : f u = f.linear u + f 0 := congrFun (AffineMap.decomp f) u
  rw [h2, hu]
  abel

/-- The affine image of an affinely spanning set under a map with surjective
linear part affinely spans the target. -/
theorem affineSpan_image_eq_top_of_linear_surjective (f : E →ᵃ[ℝ] V)
    (hf : Function.Surjective f.linear) {s : Set E} (hs : affineSpan ℝ s = ⊤) :
    affineSpan ℝ (f '' s) = ⊤ := by
  rw [← AffineSubspace.map_span, hs]
  exact AffineMap.map_top_of_surjective f
    (affineMap_surjective_of_linear_surjective f hf)

end LinearCorrection

section PolytopeSpan

variable {n : ℕ} (P : FullDimensionalPolytope n)

/-- A full-dimensional polytope affinely spans its ambient space. -/
theorem FullDimensionalPolytope.affineSpan_carrier :
    affineSpan ℝ P.carrier = ⊤ := by
  rw [FullDimensionalPolytope.carrier, affineSpan_convexHull, P.affineSpan_vertices]

end PolytopeSpan

namespace PolytopalJoinMap

variable {n m : ℕ} {P : FullDimensionalPolytope n}
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The affine extension of a factor of a join map is unique, because the
polytope affinely spans the ambient space. -/
theorem affineExtension_eq (Φ : PolytopalJoinMap P m V) (i : Fin (m + 1))
    (ψ : CoordinateSpace n →ᵃ[ℝ] V) (hψ : ∀ x : P.carrier, Φ.factor i x = ψ x.1) :
    Φ.affineExtension i = ψ := by
  apply AffineMap.ext_on P.affineSpan_carrier
  intro x hx
  have h := (Φ.factor_eq_affineExtension i ⟨x, hx⟩).symm
  rw [hψ ⟨x, hx⟩] at h
  exact h

variable (c : Fin (m + 1) → ℝ) (N : CoordinateSpace n →ₗ[ℝ] V)

/-- The linear map by which the join map moves under the factorwise correction
`x ↦ c i • N x`.  It is the linear extension of the correction to the
homogenized Cayley ambient space. -/
def perturbationLinear :
    PolytopalJoinAmbient n m →ₗ[ℝ] V where
  toFun z := ∑ i : Fin (m + 1), c i • N (z i).1
  map_add' z w := by
    simp only [Pi.add_apply, Prod.fst_add, map_add, smul_add]
    exact Finset.sum_add_distrib
  map_smul' a z := by
    simp only [Pi.smul_apply, Prod.smul_fst, map_smul, RingHom.id_apply]
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _hi ↦ by rw [smul_comm]

/-- The continuous version of `perturbationLinear`. -/
def perturbationCLM : PolytopalJoinAmbient n m →L[ℝ] V :=
  (perturbationLinear c N).toContinuousLinearMap

@[simp]
theorem perturbationCLM_apply (z : PolytopalJoinAmbient n m) :
    perturbationCLM c N z = ∑ i : Fin (m + 1), c i • N (z i).1 :=
  rfl

theorem perturbationCLM_smul_coeff (a : ℝ) (z : PolytopalJoinAmbient n m) :
    perturbationCLM (fun i ↦ a * c i) N z = a • perturbationCLM c N z := by
  simp only [perturbationCLM_apply, Finset.smul_sum, mul_smul]

/-- The perturbation of a join map by a factorwise linear correction whose
coefficients sum to zero.  The diagonal relation is preserved. -/
def perturb (Φ : PolytopalJoinMap P m V) (hc : ∑ i, c i = 0) :
    PolytopalJoinMap P m V where
  factor i x := Φ.factor i x + c i • N x.1
  factor_affine i := by
    obtain ⟨ψ, hψ⟩ := Φ.factor_affine i
    exact ⟨ψ + (c i • N).toAffineMap, fun x ↦ by simp [hψ]⟩
  diagonal_relation x := by
    rw [Finset.sum_add_distrib, Φ.diagonal_relation, ← Finset.sum_smul, hc,
      zero_smul, add_zero]

@[simp]
theorem perturb_factor (Φ : PolytopalJoinMap P m V) (hc : ∑ i, c i = 0)
    (i : Fin (m + 1)) (x : P.carrier) :
    (Φ.perturb c N hc).factor i x = Φ.factor i x + c i • N x.1 :=
  rfl

/-- The chosen affine extension of a perturbed factor is the perturbed affine
extension. -/
theorem perturb_affineExtension (Φ : PolytopalJoinMap P m V) (hc : ∑ i, c i = 0)
    (i : Fin (m + 1)) :
    (Φ.perturb c N hc).affineExtension i =
      Φ.affineExtension i + (c i • N).toAffineMap := by
  apply affineExtension_eq
  intro x
  simp [Φ.factor_eq_affineExtension i x]

/-- The exact effect of the perturbation on the linear join map. -/
theorem joinMap_perturb (Φ : PolytopalJoinMap P m V) (hc : ∑ i, c i = 0)
    (z : PolytopalJoinAmbient n m) :
    (Φ.perturb c N hc).joinMap z = Φ.joinMap z + perturbationCLM c N z := by
  change (∑ i : Fin (m + 1),
      (((Φ.perturb c N hc).affineExtension i).linear (z i).1 +
        (z i).2 • (Φ.perturb c N hc).affineExtension i 0)) =
    (∑ i : Fin (m + 1),
      ((Φ.affineExtension i).linear (z i).1 + (z i).2 • Φ.affineExtension i 0)) +
      ∑ i : Fin (m + 1), c i • N (z i).1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _hi ↦ ?_
  rw [perturb_affineExtension c N Φ hc i]
  simp only [AffineMap.add_linear, LinearMap.toAffineMap_linear, LinearMap.add_apply,
    AffineMap.coe_add, LinearMap.coe_toAffineMap, Pi.add_apply, LinearMap.smul_apply,
    map_zero, add_zero]
  abel

/-- The perturbed join map is nondegenerate as soon as the correction makes the
linear part of one factor surjective: its factor images then affinely span the
whole target. -/
theorem factorImagesAffinelySpan_perturb (Φ : PolytopalJoinMap P m V)
    (hc : ∑ i, c i = 0) (i : Fin (m + 1))
    (hsurj : Function.Surjective
      ⇑((Φ.affineExtension i).linear + c i • N)) :
    FactorImagesAffinelySpan (Φ.perturb c N hc).factor := by
  set ψ : CoordinateSpace n →ᵃ[ℝ] V := Φ.affineExtension i + (c i • N).toAffineMap
    with hψdef
  have hlin : ψ.linear = (Φ.affineExtension i).linear + c i • N := by
    rw [hψdef]
    simp [AffineMap.add_linear]
  have hspan : affineSpan ℝ (ψ '' P.carrier) = ⊤ :=
    affineSpan_image_eq_top_of_linear_surjective ψ (by rw [hlin]; exact hsurj)
      P.affineSpan_carrier
  have hsubset : ψ '' P.carrier ⊆ factorRange (Φ.perturb c N hc).factor := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨(i, ⟨x, hx⟩), ?_⟩
    change Φ.factor i ⟨x, hx⟩ + c i • N x = ψ x
    rw [Φ.factor_eq_affineExtension i ⟨x, hx⟩, hψdef]
    simp
  refine top_unique ?_
  rw [← hspan]
  exact affineSpan_mono ℝ hsubset

end PolytopalJoinMap

section NondegenerateZero

/-- The nondegenerate concrete form of the polytopal case of `theorem:zero`:
for `n = (d + 1) * m`, every affine join map on the concrete Cayley join whose
factor images affinely span the target has a zero of its linear join map on the
concrete compact deleted join. -/
def polytopalNondegenerateZeroStatement : Prop :=
  ∀ (d m : ℕ), 1 ≤ d → 1 ≤ m →
    ∀ (P : FullDimensionalPolytope ((d + 1) * m))
      (Φ : PolytopalJoinMap P m (SarkariaTarget d m)),
      FactorImagesAffinelySpan Φ.factor →
      ∃ z ∈ polytopalDeletedJoinCarrier P m, Φ.joinMap z = 0

/-- The target of the Sarkaria map has the dimension of the ambient space of the
polytope in the range `n = (d + 1) * m` of `theorem:zero`. -/
theorem finrank_sarkariaTarget (d m : ℕ) :
    finrank ℝ (SarkariaTarget d m) = finrank ℝ (CoordinateSpace ((d + 1) * m)) := by
  have h1 : finrank ℝ (SarkariaTarget d m) = m * (d + 1) := by
    change finrank ℝ (Fin m → CoordinateSpace d × ℝ) = m * (d + 1)
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_prod]
  rw [h1, Module.finrank_fin_fun]
  ring

/-- The finite-dimensional approximation step of the perturbation paragraph:
every admissible join map is approximated, uniformly on the compact concrete
deleted join, by join maps which still satisfy the diagonal relation and whose
factor images affinely span the target.

The approximating map differs from `Φ` by the correction `± a • N` in the two
factors `0` and `1` only, where `N` is chosen once and for all so that the
linear part of factor `0` becomes surjective after the correction, for every
`a ≠ 0`. -/
theorem exists_nondegenerate_uniform_approximation {d m : ℕ} (hm : 1 ≤ m)
    (P : FullDimensionalPolytope ((d + 1) * m))
    (Φ : PolytopalJoinMap P m (SarkariaTarget d m)) {ε : ℝ} (hε : 0 < ε) :
    ∃ Ψ : PolytopalJoinMap P m (SarkariaTarget d m),
      FactorImagesAffinelySpan Ψ.factor ∧
        ∀ z ∈ polytopalDeletedJoinCarrier P m,
          ‖Ψ.joinMap z - Φ.joinMap z‖ < ε := by
  classical
  -- Two distinct join factors carry the correction.
  have hm1 : 1 < m + 1 := by omega
  set i₀ : Fin (m + 1) := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin (m + 1) := ⟨1, hm1⟩ with hi₁
  have hine : i₀ ≠ i₁ := by
    rw [hi₀, hi₁]
    simp [Fin.ext_iff]
  -- The fixed linear correction making factor `i₀` surjective.
  obtain ⟨N, hN⟩ := exists_linearMap_add_smul_surjective
    (E := CoordinateSpace ((d + 1) * m)) (V := SarkariaTarget d m)
    (finrank_sarkariaTarget d m) (Φ.affineExtension i₀).linear
  -- The coefficient pattern: `+1` on factor `i₀`, `-1` on factor `i₁`.
  set c₁ : Fin (m + 1) → ℝ := fun i ↦ if i = i₀ then 1 else if i = i₁ then -1 else 0
    with hc₁
  have hsplit : ∀ i, c₁ i =
      (if i = i₀ then (1 : ℝ) else 0) + (if i = i₁ then (-1 : ℝ) else 0) := by
    intro i
    by_cases h0 : i = i₀
    · subst h0
      simp [hc₁, hine]
    · by_cases h1 : i = i₁
      · subst h1
        simp [hc₁, h0]
      · simp [hc₁, h0, h1]
  have hc₁sum : ∑ i, c₁ i = 0 := by
    rw [Finset.sum_congr rfl fun i _ ↦ hsplit i, Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ i₀ (fun _ ↦ (1 : ℝ)),
      Finset.sum_ite_eq' Finset.univ i₁ (fun _ ↦ (-1 : ℝ))]
    simp
  have hcsum : ∀ a : ℝ, ∑ i, a * c₁ i = 0 := by
    intro a
    rw [← Finset.mul_sum, hc₁sum, mul_zero]
  -- A uniform bound for the correction on the compact deleted join.
  set T := PolytopalJoinMap.perturbationCLM (m := m) c₁ N with hT
  obtain ⟨M, hM⟩ :=
    (polytopalDeletedJoinCarrier_compact (m := m) P).exists_bound_of_continuousOn
      T.continuous.continuousOn
  set M' : ℝ := |M| + 1 with hM'
  have hM'pos : 0 < M' := by positivity
  have hMbound : ∀ z ∈ polytopalDeletedJoinCarrier P m, ‖T z‖ ≤ M' := by
    intro z hz
    exact (hM z hz).trans (by rw [hM']; linarith [le_abs_self M])
  -- The size of the correction.
  set a : ℝ := ε / (2 * M') with ha
  have hapos : 0 < a := by
    rw [ha]
    positivity
  refine ⟨Φ.perturb (fun i ↦ a * c₁ i) N (hcsum a), ?_, ?_⟩
  · apply PolytopalJoinMap.factorImagesAffinelySpan_perturb _ N Φ (hcsum a) i₀
    have hci₀ : a * c₁ i₀ = a := by simp [hc₁]
    rw [hci₀]
    exact hN a hapos.ne'
  · intro z hz
    have hj := PolytopalJoinMap.joinMap_perturb (fun i ↦ a * c₁ i) N Φ (hcsum a) z
    have hpert : PolytopalJoinMap.perturbationCLM (fun i ↦ a * c₁ i) N z = a • T z := by
      rw [hT]
      exact PolytopalJoinMap.perturbationCLM_smul_coeff c₁ N a z
    rw [hpert] at hj
    have hdiff : (Φ.perturb (fun i ↦ a * c₁ i) N (hcsum a)).joinMap z - Φ.joinMap z
        = a • T z := by
      rw [hj]
      abel
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_pos hapos]
    have hstep : a * ‖T z‖ ≤ a * M' :=
      mul_le_mul_of_nonneg_left (hMbound z hz) hapos.le
    have hhalf : a * M' = ε / 2 := by
      rw [ha]
      field_simp
    rw [hhalf] at hstep
    linarith

/-- The nondegenerate zero statement implies the general polytopal zero
statement.

For every `k`, the map `Φ` is approximated within `1 / (k + 1)`, uniformly on
the compact concrete deleted join, by a nondegenerate join map `Ψ k` satisfying
the diagonal relation.  Each `Ψ k` has a zero `z k` in the deleted join, so
`‖Φ.joinMap (z k)‖ < 1 / (k + 1)`.  Passing to a convergent subsequence of the
`z k` inside the compact deleted join produces a zero of `Φ.joinMap` there, and
`PolytopalDeletedJoinRealization` turns that zero into a witness-level zero,
which is the form in which `theorem:zero` is stated. -/
theorem polytopalZeroTheoremStatement_of_nondegenerate
    (hnd : polytopalNondegenerateZeroStatement) : polytopalZeroTheoremStatement := by
  classical
  intro d m hd hm P Φ
  -- The approximating nondegenerate maps and their zeros.
  have hex : ∀ k : ℕ, ∃ z ∈ polytopalDeletedJoinCarrier P m,
      ‖Φ.joinMap z‖ < 1 / (k + 1 : ℝ) := by
    intro k
    have hpos : (0 : ℝ) < 1 / (k + 1 : ℝ) := by positivity
    obtain ⟨Ψ, hspan, happrox⟩ :=
      exists_nondegenerate_uniform_approximation hm P Φ hpos
    obtain ⟨z, hzD, hz0⟩ := hnd d m hd hm P Ψ hspan
    refine ⟨z, hzD, ?_⟩
    have := happrox z hzD
    rwa [hz0, zero_sub, norm_neg] at this
  choose z hzD hzval using hex
  -- The values tend to zero, so a subsequential limit is an actual zero.
  have htend : Tendsto (fun k : ℕ ↦ Φ.joinMap (z k)) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k ↦ (hzval k).le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨w, hwD, hw0⟩ := exists_zero_of_values_tendsto_zero
    (polytopalDeletedJoinCarrier_compact (m := m) P) Φ.joinMap.continuous z hzD htend
  exact Φ.exists_value_eq_zero_of_joinMap_eq_zero hwD hw0

/-- Combining with the deduction of `AffineTverberg/DeletedJoin.lean`: the
nondegenerate polytopal zero statement implies the polytopal half of
`theorem:main`. -/
theorem polytopalMainTheoremStatement_of_nondegenerateZero
    (hnd : polytopalNondegenerateZeroStatement) : polytopalMainTheoremStatement :=
  polytopalMainTheoremStatement_of_zero
    (polytopalZeroTheoremStatement_of_nondegenerate hnd)

end NondegenerateZero

end AffineTverberg

