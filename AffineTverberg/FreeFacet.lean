import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Pi

set_option linter.style.header false

/-!
# Free facets and top-dimensional cycles

This file formalizes the algebraic endpoint of the simplicial-ball proof of
`lemma:diagonal_acyclicity` in `affine-tverberg17.tex`.  A boundary matrix in
which every top simplex has a private facet with nonzero incidence coefficient
is injective.  Consequently there are no nonzero top-dimensional cycles.
-/

noncomputable section

open scoped BigOperators

namespace AffineTverberg

section BoundaryMatrix

variable {𝕜 T F : Type*} [Field 𝕜] [Fintype T]

/-- A boundary matrix has private rows if each column has a row where its entry
is nonzero and every other column vanishes. -/
def HasPrivateBoundaryRows (boundary : F → T → 𝕜) : Prop :=
  ∀ t, ∃ f, boundary f t ≠ 0 ∧ ∀ t', t' ≠ t → boundary f t' = 0

/-- The linear map represented by a finite boundary matrix. -/
def boundaryMatrixLinearMap (boundary : F → T → 𝕜) :
    (T → 𝕜) →ₗ[𝕜] (F → 𝕜) where
  toFun c f := ∑ t, c t * boundary f t
  map_add' c d := by
    funext f
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' a c := by
    funext f
    simp [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

@[simp]
theorem boundaryMatrixLinearMap_apply (boundary : F → T → 𝕜) (c : T → 𝕜) (f : F) :
    boundaryMatrixLinearMap boundary c f = ∑ t, c t * boundary f t :=
  rfl

/-- Private boundary rows force every coefficient of a cycle to vanish. -/
theorem coefficients_eq_zero_of_privateBoundaryRows {boundary : F → T → 𝕜}
    (hprivate : HasPrivateBoundaryRows boundary) {c : T → 𝕜}
    (hcycle : ∀ f, ∑ t, c t * boundary f t = 0) :
    c = 0 := by
  funext t
  obtain ⟨f, hft, hother⟩ := hprivate t
  have hsingle : ∑ t', c t' * boundary f t' = c t * boundary f t := by
    apply Finset.sum_eq_single t
    · intro t' _ ht'
      simp [hother t' ht']
    · simp
  have hproduct : c t * boundary f t = 0 := by
    rw [← hsingle]
    exact hcycle f
  exact (mul_eq_zero.mp hproduct).resolve_right hft

/-- A boundary matrix with private rows is injective. -/
theorem boundaryMatrixLinearMap_injective {boundary : F → T → 𝕜}
    (hprivate : HasPrivateBoundaryRows boundary) :
    Function.Injective (boundaryMatrixLinearMap boundary) := by
  rw [← LinearMap.ker_eq_bot]
  apply LinearMap.ker_eq_bot'.mpr
  intro c hc
  apply coefficients_eq_zero_of_privateBoundaryRows hprivate
  intro f
  exact congrFun hc f

/-- Equivalently, the space of top-dimensional cycles is zero. -/
theorem boundaryMatrixLinearMap_ker_eq_bot {boundary : F → T → 𝕜}
    (hprivate : HasPrivateBoundaryRows boundary) :
    (boundaryMatrixLinearMap boundary).ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr (boundaryMatrixLinearMap_injective hprivate)

end BoundaryMatrix

section SimplicialFreeFacets

variable {𝕜 V : Type*} [Field 𝕜] [DecidableEq V]

/-- `f` is a codimension-one face of the finite simplex `t`. -/
def IsSimplexFacet (f t : Finset V) : Prop :=
  f ⊆ t ∧ f.card + 1 = t.card

/-- Each selected top simplex has a facet belonging to no other selected top
simplex. -/
def HasFreeFacets (top : Finset (Finset V)) : Prop :=
  ∀ t : {t // t ∈ top}, ∃ f, IsSimplexFacet f t.1 ∧
    ∀ t' : {t // t ∈ top}, IsSimplexFacet f t'.1 → t' = t

omit [DecidableEq V] in
/-- The free-facet condition supplies private rows for any oriented simplicial
boundary matrix whose entries are nonzero exactly on facets. -/
theorem hasPrivateBoundaryRows_of_hasFreeFacets
    {top : Finset (Finset V)} (hfree : HasFreeFacets top)
    (boundary : Finset V → {t // t ∈ top} → 𝕜)
    (hboundary : ∀ f t, boundary f t ≠ 0 ↔ IsSimplexFacet f t.1) :
    HasPrivateBoundaryRows boundary := by
  intro t
  obtain ⟨f, hfacet, hunique⟩ := hfree t
  refine ⟨f, (hboundary f t).mpr hfacet, ?_⟩
  intro t' ht'
  by_contra hne
  exact ht' (hunique t' ((hboundary f t').mp hne))

omit [DecidableEq V] in
/-- A finite top-dimensional simplicial boundary with a free facet for every
top simplex has no nonzero cycles. -/
theorem topBoundary_injective_of_hasFreeFacets
    {top : Finset (Finset V)} (hfree : HasFreeFacets top)
    (boundary : Finset V → {t // t ∈ top} → 𝕜)
    (hboundary : ∀ f t, boundary f t ≠ 0 ↔ IsSimplexFacet f t.1) :
    Function.Injective (boundaryMatrixLinearMap boundary) :=
  boundaryMatrixLinearMap_injective
    (hasPrivateBoundaryRows_of_hasFreeFacets hfree boundary hboundary)

end SimplicialFreeFacets

section DimensionArithmetic

/-- The strict dimension estimate in the `r ≥ 3` part of the simplicial-ball
deleted-join argument. -/
theorem bad_facet_dimension_lt (r N a : ℕ) (hr : 3 ≤ r) (hN : 1 ≤ N)
    (ha : a ≤ N - 1) :
    a * (r - 1) < (r - 1) * N - 1 := by
  have ha' : a + 1 ≤ N := by omega
  have hk : 2 ≤ r - 1 := by omega
  have hmul := Nat.mul_le_mul_left (r - 1) ha'
  simp only [mul_add, mul_one] at hmul
  rw [Nat.mul_comm (r - 1) a] at hmul
  omega

/-- The vertex-count identity used for the other possible coface of a bad
simplex. -/
theorem bad_simplex_vertex_count (r N : ℕ) (hr : 2 ≤ r) (hN : 1 ≤ N) :
    N + ((r - 1) * N - 1) + 2 = r * N + 1 := by
  have hk : 1 ≤ r - 1 := by omega
  have hprod : 1 ≤ (r - 1) * N := Nat.one_le_iff_ne_zero.mpr <|
    mul_ne_zero (by omega) (by omega)
  have hmul : r * N = (r - 1) * N + N := by
    conv_lhs => rw [show r = (r - 1) + 1 by omega]
    rw [add_mul, one_mul]
  omega

end DimensionArithmetic

end AffineTverberg
