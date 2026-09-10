import Mathlib.Algebra.BigOperators.Field
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Quotient.Basic
import AffineTverberg.FreeFacet

set_option linter.style.header false

/-!
# Reduced oriented simplicial chains and homology over a field

This file builds a genuine (small but complete) reduced simplicial homology
foundation for finite simplicial complexes on a finite, linearly ordered vertex
type `V`, with coefficients in an arbitrary field `𝕜`.

## Conventions

* A simplex is a `Finset V`; we grade **by cardinality**, so a simplex `s` with
  `s.card = n` lives in `chains K n`.  The geometric dimension is `n - 1`.  In
  particular `chains K 0` is spanned by the empty simplex `∅`, so the complex
  built here is the *augmented* chain complex and its homology is *reduced*
  homology.
* The orientation is the one induced by the given linear order on `V`: for a
  simplex `s = {v₀ < v₁ < ⋯ < v_n}`, the boundary is
  `∂ s = ∑ i, (-1)^i (s.erase vᵢ)`.  Dually (which is the form used here, since
  chains are represented as coefficient functions `Finset V → 𝕜`), the
  coefficient of `∂c` at a face `f` is `∑_{v ∉ f} (-1)^{#{u ∈ f | u < v}} c (insert v f)`.

## Main definitions

* `AffineTverberg.Simplicial.orientedSign` : the incidence sign `(-1)^{#{u ∈ f | u < v}}`.
* `AffineTverberg.Simplicial.boundaryCoeff` : the entries of the oriented boundary matrix.
* `AffineTverberg.Simplicial.boundary` : the boundary operator on `Finset V → 𝕜`,
  which in cardinality-degree `1 → 0` is exactly the augmentation.
* `AffineTverberg.Simplicial.chains`, `cycles`, `boundaries`, `homology` : the
  reduced chain groups of a face-closed family `K`, its reduced cycles,
  boundaries and homology.
* `AffineTverberg.Simplicial.IsReducedAcyclicAt`, `IsReducedAcyclic` : the
  exactness predicates.
* `AffineTverberg.Simplicial.IsConeWithApex`, `coneHomotopy` : cones and the
  cone contraction chain homotopy.

## Main results

* `boundary_boundary` : `∂ ∘ ∂ = 0`.
* `boundaries_le_cycles` : boundaries are cycles.
* `homology_subsingleton_iff` : the homology module vanishes iff the exactness
  predicate holds.
* `cycles_top_eq_bot_of_hasFreeFacets` and
  `homology_top_subsingleton_of_hasFreeFacets` : if every top-dimensional
  simplex of `K` has a private codimension-one face (`HasFreeFacets`), then the
  reduced top homology of `K` vanishes, computed with the genuine oriented
  boundary coefficients.
* `coneHomotopy_identity` and `isReducedAcyclic_of_cone` : a cone (in
  particular the star of a vertex, or a full simplex) is reduced acyclic.
* `chains_inter`, `chains_union` : the module-theoretic input for a later
  Mayer-Vietoris argument.
-/

noncomputable section

open scoped BigOperators

namespace AffineTverberg

namespace Simplicial

section Signs

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder V]

/-! ### Incidence signs -/

/-- The incidence sign of the vertex `v` with respect to the face `f`:
`(-1) ^ #{u ∈ f | u < v}`.  If `v ∉ f` this is the sign with which `f` occurs in
the oriented boundary of `insert v f`. -/
def orientedSign (𝕜 : Type*) [Field 𝕜] (f : Finset V) (v : V) : 𝕜 :=
  (-1) ^ (f.filter (· < v)).card

theorem orientedSign_ne_zero (f : Finset V) (v : V) : orientedSign 𝕜 f v ≠ 0 := by
  unfold orientedSign
  exact pow_ne_zero _ (by norm_num)

@[simp]
theorem orientedSign_empty (v : V) : orientedSign 𝕜 (∅ : Finset V) v = 1 := by
  simp [orientedSign]

theorem orientedSign_insert_of_lt {f : Finset V} {v w : V} (hv : v ∉ f) (hvw : v < w) :
    orientedSign 𝕜 (insert v f) w = -orientedSign 𝕜 f w := by
  unfold orientedSign
  simp only [Finset.filter_insert, hvw, ite_true]
  rw [Finset.card_insert_of_notMem (fun h => hv (Finset.mem_filter.mp h).1), pow_succ]
  ring

theorem orientedSign_insert_of_not_lt {f : Finset V} {v w : V} (hvw : ¬ v < w) :
    orientedSign 𝕜 (insert v f) w = orientedSign 𝕜 f w := by
  unfold orientedSign
  simp only [Finset.filter_insert, hvw, ite_false]

/-- The fundamental sign cancellation underlying `∂ ∘ ∂ = 0`. -/
theorem orientedSign_antisymm {f : Finset V} {v w : V} (hv : v ∉ f) (hw : w ∉ f) (hvw : v ≠ w) :
    orientedSign 𝕜 f v * orientedSign 𝕜 (insert v f) w
      + orientedSign 𝕜 f w * orientedSign 𝕜 (insert w f) v = 0 := by
  rcases lt_or_gt_of_ne hvw with h | h
  · rw [orientedSign_insert_of_lt hv h, orientedSign_insert_of_not_lt (not_lt_of_gt h)]
    ring
  · rw [orientedSign_insert_of_lt hw h, orientedSign_insert_of_not_lt (not_lt_of_gt h)]
    ring

/-- A codimension one face is obtained by deleting a single vertex. -/
theorem exists_insert_of_isSimplexFacet {f t : Finset V} (h : IsSimplexFacet f t) :
    ∃ v ∉ f, t = insert v f := by
  obtain ⟨hsub, hcard⟩ := h
  have hc : (t \ f).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub]; omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hc
  have hvt : v ∈ t \ f := by rw [hv]; simp
  rw [Finset.mem_sdiff] at hvt
  refine ⟨v, hvt.2, ?_⟩
  refine (Finset.eq_of_subset_of_card_le (Finset.insert_subset hvt.1 hsub) ?_).symm
  rw [Finset.card_insert_of_notMem hvt.2]
  omega

/-- Deleting a vertex produces a codimension one face. -/
theorem isSimplexFacet_insert {f : Finset V} {v : V} (hv : v ∉ f) :
    IsSimplexFacet f (insert v f) :=
  ⟨Finset.subset_insert _ _, by rw [Finset.card_insert_of_notMem hv]⟩

/-! ### The oriented boundary matrix -/

/-- The entry of the oriented simplicial boundary matrix in row `f` and column
`t`: it is `± 1` exactly when `f` is a codimension one face of `t`, and `0`
otherwise. -/
def boundaryCoeff (𝕜 : Type*) [Field 𝕜] (f t : Finset V) : 𝕜 :=
  ∑ v ∈ t \ f, if insert v f = t then orientedSign 𝕜 f v else 0

theorem boundaryCoeff_insert {f : Finset V} {v : V} (hv : v ∉ f) :
    boundaryCoeff 𝕜 f (insert v f) = orientedSign 𝕜 f v := by
  unfold boundaryCoeff
  rw [Finset.insert_sdiff_cancel hv]
  simp

theorem boundaryCoeff_eq_zero_of_not_isSimplexFacet {f t : Finset V}
    (h : ¬ IsSimplexFacet f t) : boundaryCoeff 𝕜 f t = 0 := by
  unfold boundaryCoeff
  refine Finset.sum_eq_zero fun v hv => ?_
  rw [Finset.mem_sdiff] at hv
  by_cases hins : insert v f = t
  · exact absurd (hins ▸ isSimplexFacet_insert hv.2) h
  · simp [hins]

/-- The oriented boundary coefficient is nonzero exactly on codimension one
faces.  This is the hypothesis required by `hasPrivateBoundaryRows_of_hasFreeFacets`. -/
theorem boundaryCoeff_ne_zero_iff (f t : Finset V) :
    boundaryCoeff 𝕜 f t ≠ 0 ↔ IsSimplexFacet f t := by
  constructor
  · intro h
    by_contra hfacet
    exact h (boundaryCoeff_eq_zero_of_not_isSimplexFacet hfacet)
  · intro h
    obtain ⟨v, hv, rfl⟩ := exists_insert_of_isSimplexFacet h
    rw [boundaryCoeff_insert hv]
    exact orientedSign_ne_zero f v

/-- The sign cancellation underlying the cone contraction. -/
theorem orientedSign_cone_antisymm {w : Finset V} {a v : V} (ha : a ∉ w) (hv : v ∉ w)
    (hav : a ≠ v) :
    orientedSign 𝕜 (insert a w) v * orientedSign 𝕜 (insert v w) a
      + orientedSign 𝕜 w a * orientedSign 𝕜 w v = 0 := by
  rcases lt_or_gt_of_ne hav with h | h
  · rw [orientedSign_insert_of_lt ha h, orientedSign_insert_of_not_lt (not_lt_of_gt h)]
    ring
  · rw [orientedSign_insert_of_lt hv h, orientedSign_insert_of_not_lt (not_lt_of_gt h)]
    ring

theorem orientedSign_sq (f : Finset V) (v : V) : orientedSign 𝕜 f v * orientedSign 𝕜 f v = 1 := by
  unfold orientedSign
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

end Signs

section Boundary

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder V] [Fintype V]

/-! ### The boundary operator -/

/-- The reduced (augmented) simplicial boundary operator, acting on coefficient
functions.  The coefficient of `∂ c` at a simplex `f` is the signed sum of the
coefficients of `c` at the cofaces of `f`. -/
def boundary (𝕜 V : Type*) [Field 𝕜] [LinearOrder V] [Fintype V] :
    (Finset V → 𝕜) →ₗ[𝕜] (Finset V → 𝕜) where
  toFun c f := ∑ v ∈ fᶜ, orientedSign 𝕜 f v * c (insert v f)
  map_add' c d := by
    funext f
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    funext f
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring

@[simp]
theorem boundary_apply (c : Finset V → 𝕜) (f : Finset V) :
    boundary 𝕜 V c f = ∑ v ∈ fᶜ, orientedSign 𝕜 f v * c (insert v f) :=
  rfl

/-- The boundary operator is given by the oriented boundary matrix, i.e. it
agrees with `boundaryMatrixLinearMap` applied to `boundaryCoeff`. -/
theorem boundary_eq_boundaryMatrix (c : Finset V → 𝕜) (f : Finset V) :
    boundary 𝕜 V c f = ∑ t : Finset V, boundaryCoeff 𝕜 f t * c t := by
  have hinj : Set.InjOn (fun v => insert v f) (fᶜ : Finset V) := by
    intro v hv w hw h
    simp only [Finset.coe_compl, Set.mem_compl_iff, Finset.mem_coe] at hv hw
    simp only at h
    have hmem : v ∈ insert w f := h ▸ Finset.mem_insert_self v f
    exact (Finset.mem_insert.mp hmem).resolve_right hv
  have h0 : ∀ t ∈ (Finset.univ : Finset (Finset V)),
      t ∉ (fᶜ).image (fun v => insert v f) → boundaryCoeff 𝕜 f t * c t = 0 := by
    intro t _ ht
    have hnf : ¬ IsSimplexFacet f t := by
      intro hfacet
      obtain ⟨v, hv, rfl⟩ := exists_insert_of_isSimplexFacet hfacet
      exact ht (Finset.mem_image.mpr ⟨v, by simpa using hv, rfl⟩)
    rw [boundaryCoeff_eq_zero_of_not_isSimplexFacet hnf, zero_mul]
  calc boundary 𝕜 V c f
      = ∑ v ∈ fᶜ, boundaryCoeff 𝕜 f (insert v f) * c (insert v f) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [boundaryCoeff_insert (by simpa using hv)]
    _ = ∑ t ∈ (fᶜ).image (fun v => insert v f), boundaryCoeff 𝕜 f t * c t :=
        (Finset.sum_image (f := fun t => boundaryCoeff 𝕜 f t * c t) hinj).symm
    _ = ∑ t : Finset V, boundaryCoeff 𝕜 f t * c t :=
        Finset.sum_subset (Finset.subset_univ _) h0

/-- In cardinality-degree `1 → 0` the boundary map is the augmentation
`c ↦ ∑ v, c {v}`; this is what makes the homology below *reduced*. -/
def augmentation (𝕜 V : Type*) [Field 𝕜] [LinearOrder V] [Fintype V] :
    (Finset V → 𝕜) →ₗ[𝕜] 𝕜 where
  toFun c := ∑ v : V, c {v}
  map_add' c d := by simp [Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.mul_sum]

@[simp]
theorem augmentation_apply (c : Finset V → 𝕜) : augmentation 𝕜 V c = ∑ v : V, c {v} := rfl

@[simp]
theorem boundary_apply_empty (c : Finset V → 𝕜) :
    boundary 𝕜 V c ∅ = augmentation 𝕜 V c := by
  simp

/-- `∂ ∘ ∂ = 0`, computed from the genuine oriented incidence signs. -/
theorem boundary_boundary_apply (c : Finset V → 𝕜) : boundary 𝕜 V (boundary 𝕜 V c) = 0 := by
  funext f
  set s : Finset V := fᶜ with hs
  set G : V × V → 𝕜 := fun p =>
    if p.2 = p.1 then 0
    else orientedSign 𝕜 f p.1 * (orientedSign 𝕜 (insert p.1 f) p.2 * c (insert p.2 (insert p.1 f)))
    with hG
  have key : boundary 𝕜 V (boundary 𝕜 V c) f = ∑ p ∈ s ×ˢ s, G p := by
    rw [Finset.sum_product, boundary_apply]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [boundary_apply, Finset.mul_sum, Finset.compl_insert, ← hs]
    have h1 : ∑ w ∈ s.erase v, G (v, w) = ∑ w ∈ s, G (v, w) :=
      Finset.sum_subset (Finset.erase_subset _ _) (by
        intro w hws hnw
        have hwv : w = v := by
          by_contra hne
          exact hnw (Finset.mem_erase.mpr ⟨hne, hws⟩)
        simp [hG, hwv])
    rw [← h1]
    refine Finset.sum_congr rfl fun w hw => ?_
    have hne : w ≠ v := (Finset.mem_erase.mp hw).1
    simp [hG, hne]
  rw [Pi.zero_apply, key]
  refine Finset.sum_involution (fun p _ => (p.2, p.1)) ?_ ?_ ?_ ?_
  · rintro ⟨v, w⟩ hp
    simp only [Finset.mem_product] at hp
    by_cases hvw : w = v
    · simp [hG, hvw]
    · have hvw' : ¬ (v = w) := fun h => hvw h.symm
      have hv : v ∉ f := by simpa [hs] using hp.1
      have hw : w ∉ f := by simpa [hs] using hp.2
      have hcomm : insert v (insert w f) = insert w (insert v f) := Finset.insert_comm v w f
      simp only [hG, hvw, hvw', ite_false, hcomm]
      have hsign := orientedSign_antisymm (𝕜 := 𝕜) hv hw hvw'
      calc orientedSign 𝕜 f v * (orientedSign 𝕜 (insert v f) w * c (insert w (insert v f)))
            + orientedSign 𝕜 f w * (orientedSign 𝕜 (insert w f) v * c (insert w (insert v f)))
          = (orientedSign 𝕜 f v * orientedSign 𝕜 (insert v f) w
              + orientedSign 𝕜 f w * orientedSign 𝕜 (insert w f) v)
            * c (insert w (insert v f)) := by ring
        _ = 0 := by rw [hsign, zero_mul]
  · rintro ⟨v, w⟩ _ hne0 hcontra
    simp only [Prod.mk.injEq] at hcontra
    simp [hG, hcontra.1] at hne0
  · rintro ⟨v, w⟩ hp
    simp only [Finset.mem_product] at hp ⊢
    exact ⟨hp.2, hp.1⟩
  · rintro ⟨v, w⟩ _
    rfl

/-- `∂ ∘ ∂ = 0` as an identity of linear maps. -/
theorem boundary_boundary : (boundary 𝕜 V) ∘ₗ (boundary 𝕜 V) = 0 := by
  refine LinearMap.ext fun c => ?_
  simpa using boundary_boundary_apply c

/-! ### Face-closed families and chain groups -/

/-- A face-closed family of simplices: an abstract simplicial complex in the
augmented convention, where the empty simplex is a face of every simplex. -/
def FaceClosed (K : Finset (Finset V)) : Prop := ∀ s ∈ K, ∀ t ⊆ s, t ∈ K

/-- The chains of `K` in cardinality-degree `n`: coefficient functions supported
on the simplices of `K` with exactly `n` vertices. -/
def chains (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (n : ℕ) :
    Submodule 𝕜 (Finset V → 𝕜) where
  carrier := {c | ∀ s, c s ≠ 0 → s ∈ K ∧ s.card = n}
  add_mem' := by
    intro c d hc hd s hs
    by_cases h : c s = 0
    · exact hd s (by simpa [h] using hs)
    · exact hc s h
  zero_mem' := by intro s hs; simp at hs
  smul_mem' := by
    intro a c hc s hs
    exact hc s (by
      intro h
      exact hs (by simp [Pi.smul_apply, h]))

omit [LinearOrder V] [Fintype V] in
theorem mem_chains_iff {K : Finset (Finset V)} {n : ℕ} {c : Finset V → 𝕜} :
    c ∈ chains 𝕜 K n ↔ ∀ s, c s ≠ 0 → s ∈ K ∧ s.card = n := Iff.rfl

omit [LinearOrder V] [Fintype V] in
theorem chains_mono {K L : Finset (Finset V)} (h : K ⊆ L) (n : ℕ) :
    chains 𝕜 K n ≤ chains 𝕜 L n := by
  intro c hc s hs
  exact ⟨h (hc s hs).1, (hc s hs).2⟩

omit [Fintype V] in
theorem chains_inter (K L : Finset (Finset V)) (n : ℕ) :
    chains 𝕜 (K ∩ L) n = chains 𝕜 K n ⊓ chains 𝕜 L n := by
  ext c
  simp only [Submodule.mem_inf, mem_chains_iff, Finset.mem_inter]
  constructor
  · intro h
    exact ⟨fun s hs => ⟨(h s hs).1.1, (h s hs).2⟩, fun s hs => ⟨(h s hs).1.2, (h s hs).2⟩⟩
  · intro h s hs
    exact ⟨⟨(h.1 s hs).1, (h.2 s hs).1⟩, (h.1 s hs).2⟩

omit [Fintype V] in
/-- Chains of a union split as a sum of chains; together with `chains_inter`
this is the module-theoretic input of a Mayer-Vietoris argument. -/
theorem chains_union (K L : Finset (Finset V)) (n : ℕ) :
    chains 𝕜 (K ∪ L) n = chains 𝕜 K n ⊔ chains 𝕜 L n := by
  refine le_antisymm (fun c hc => ?_) ?_
  · classical
    refine Submodule.mem_sup.mpr ⟨fun s => if s ∈ K then c s else 0,
      ?_, fun s => if s ∈ K then 0 else c s, ?_, ?_⟩
    · intro s hs
      by_cases hsK : s ∈ K
      · simp only [hsK, ite_true] at hs
        exact ⟨hsK, (hc s hs).2⟩
      · simp [hsK] at hs
    · intro s hs
      by_cases hsK : s ∈ K
      · simp [hsK] at hs
      · simp only [hsK, ite_false] at hs
        exact ⟨(Finset.mem_union.mp (hc s hs).1).resolve_left hsK, (hc s hs).2⟩
    · funext s
      by_cases hsK : s ∈ K <;> simp [hsK]
  · exact sup_le (chains_mono Finset.subset_union_left n) (chains_mono Finset.subset_union_right n)

/-- The boundary of an `(n+1)`-chain of a face-closed family is an `n`-chain. -/
theorem boundary_mem_chains {K : Finset (Finset V)} (hK : FaceClosed K) {n : ℕ}
    {c : Finset V → 𝕜} (hc : c ∈ chains 𝕜 K (n + 1)) :
    boundary 𝕜 V c ∈ chains 𝕜 K n := by
  intro f hf
  rw [boundary_apply] at hf
  obtain ⟨v, hv, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hf
  have hcv : c (insert v f) ≠ 0 := fun h => hne (by rw [h, mul_zero])
  obtain ⟨hmem, hcard⟩ := hc _ hcv
  have hvf : v ∉ f := by simpa using hv
  refine ⟨hK _ hmem f (Finset.subset_insert _ _), ?_⟩
  rw [Finset.card_insert_of_notMem hvf] at hcard
  omega

/-! ### Reduced cycles, boundaries and homology -/

/-- Reduced `n`-cycles of `K`. -/
def cycles (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (n : ℕ) :
    Submodule 𝕜 (Finset V → 𝕜) :=
  chains 𝕜 K n ⊓ LinearMap.ker (boundary 𝕜 V)

/-- Reduced `n`-boundaries of `K`. -/
def boundaries (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (n : ℕ) :
    Submodule 𝕜 (Finset V → 𝕜) :=
  (chains 𝕜 K (n + 1)).map (boundary 𝕜 V)

theorem mem_cycles_iff {K : Finset (Finset V)} {n : ℕ} {c : Finset V → 𝕜} :
    c ∈ cycles 𝕜 K n ↔ c ∈ chains 𝕜 K n ∧ boundary 𝕜 V c = 0 := Iff.rfl

theorem boundaries_le_cycles {K : Finset (Finset V)} (hK : FaceClosed K) (n : ℕ) :
    boundaries 𝕜 K n ≤ cycles 𝕜 K n := by
  rintro c ⟨d, hd, rfl⟩
  exact ⟨boundary_mem_chains hK hd, boundary_boundary_apply d⟩

/-- Reduced homology of `K` in cardinality-degree `n` (geometric dimension
`n - 1`), as the quotient of the cycles by the boundaries. -/
def homology (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (n : ℕ) :=
  (cycles 𝕜 K n) ⧸ ((boundaries 𝕜 K n).comap (cycles 𝕜 K n).subtype)

instance (K : Finset (Finset V)) (n : ℕ) : AddCommGroup (homology 𝕜 K n) :=
  Submodule.Quotient.addCommGroup _

instance (K : Finset (Finset V)) (n : ℕ) : Module 𝕜 (homology 𝕜 K n) :=
  Submodule.Quotient.module _

/-- Exactness of the reduced chain complex of `K` in degree `n`. -/
def IsReducedAcyclicAt (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (n : ℕ) : Prop :=
  cycles 𝕜 K n ≤ boundaries 𝕜 K n

/-- The reduced chain complex of `K` is exact in every degree, i.e. `K` is
`𝕜`-acyclic. -/
def IsReducedAcyclic (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) : Prop :=
  ∀ n, IsReducedAcyclicAt 𝕜 K n

theorem homology_subsingleton_iff (K : Finset (Finset V)) (n : ℕ) :
    Subsingleton (homology 𝕜 K n) ↔ IsReducedAcyclicAt 𝕜 K n := by
  rw [homology, Submodule.Quotient.subsingleton_iff]
  constructor
  · intro h c hc
    have hmem : (⟨c, hc⟩ : cycles 𝕜 K n) ∈ (boundaries 𝕜 K n).comap (cycles 𝕜 K n).subtype := by
      rw [h]; trivial
    simpa using hmem
  · intro h
    refine eq_top_iff.mpr fun x _ => ?_
    simpa using h x.2

/-! ### Top-dimensional simplices and free facets -/

/-- The simplices of `K` with exactly `n` vertices. -/
def topSimplices (K : Finset (Finset V)) (n : ℕ) : Finset (Finset V) :=
  K.filter (fun s => s.card = n)

omit [LinearOrder V] [Fintype V] in
@[simp]
theorem mem_topSimplices {K : Finset (Finset V)} {n : ℕ} {s : Finset V} :
    s ∈ topSimplices K n ↔ s ∈ K ∧ s.card = n := by
  simp [topSimplices]

/-- If `K` has no simplex with more than `n` vertices, there are no `n`-boundaries. -/
theorem boundaries_top_eq_bot {K : Finset (Finset V)} {n : ℕ}
    (hmax : ∀ s ∈ K, s.card ≤ n) : boundaries 𝕜 K n = ⊥ := by
  have hchains : chains 𝕜 K (n + 1) = (⊥ : Submodule 𝕜 (Finset V → 𝕜)) := by
    refine le_antisymm (fun c hc => ?_) bot_le
    have hc0 : c = 0 := by
      funext s
      by_contra hs
      obtain ⟨hmem, hcard⟩ := hc s hs
      have := hmax s hmem
      omega
    simpa using hc0
  rw [boundaries, hchains, Submodule.map_bot]

/-- **Free facets kill top cycles.**  If every simplex of `K` with `n` vertices
has a codimension one face contained in no other such simplex, then there is no
nonzero reduced `n`-cycle. -/
theorem cycles_top_eq_bot_of_hasFreeFacets {K : Finset (Finset V)} {n : ℕ}
    (hfree : HasFreeFacets (topSimplices K n)) : cycles 𝕜 K n = ⊥ := by
  refine le_antisymm (fun c hc => ?_) bot_le
  obtain ⟨hsupp, hcyc⟩ := hc
  have hzero : ∀ t ∈ topSimplices K n, c t = 0 := by
    intro t ht
    obtain ⟨f, hfacet, huniq⟩ := hfree ⟨t, ht⟩
    obtain ⟨v, hv, rfl⟩ := exists_insert_of_isSimplexFacet hfacet
    have h0 : boundary 𝕜 V c f = 0 := congrFun hcyc f
    rw [boundary_apply] at h0
    have hsingle : ∑ w ∈ fᶜ, orientedSign 𝕜 f w * c (insert w f)
        = orientedSign 𝕜 f v * c (insert v f) := by
      refine Finset.sum_eq_single v ?_ ?_
      · intro w hw hwv
        by_cases hcw : c (insert w f) = 0
        · rw [hcw, mul_zero]
        · exfalso
          have hwf : w ∉ f := by simpa using hw
          obtain ⟨hmem, hcard⟩ := hsupp _ hcw
          have hmemtop : insert w f ∈ topSimplices K n := by simp [hmem, hcard]
          have heq : insert w f = insert v f :=
            congrArg Subtype.val (huniq ⟨insert w f, hmemtop⟩ (isSimplexFacet_insert hwf))
          have hmemw : w ∈ insert v f := heq ▸ Finset.mem_insert_self w f
          rcases Finset.mem_insert.mp hmemw with h1 | h1
          · exact hwv h1
          · exact hwf h1
      · intro hv'
        exact absurd (by simpa using hv) hv'
    rw [hsingle] at h0
    exact (mul_eq_zero.mp h0).resolve_left (orientedSign_ne_zero f v)
  have hc0 : c = 0 := by
    funext s
    by_cases hs : c s = 0
    · simpa using hs
    · obtain ⟨hmem, hcard⟩ := hsupp s hs
      simpa using hzero s (by simp [hmem, hcard])
  simpa using hc0

/-- **Vanishing of reduced top homology.**  If `K` has no simplex with more than
`n` vertices and every `n`-vertex simplex of `K` has a private codimension one
face, then the reduced homology of `K` in degree `n` vanishes.  The boundary map
used here is the genuine oriented simplicial boundary. -/
theorem homology_top_subsingleton_of_hasFreeFacets {K : Finset (Finset V)} {n : ℕ}
    (hfree : HasFreeFacets (topSimplices K n)) :
    Subsingleton (homology 𝕜 K n) := by
  rw [homology_subsingleton_iff]
  intro c hc
  have hc0 : c = 0 := by
    rw [cycles_top_eq_bot_of_hasFreeFacets hfree] at hc
    simpa using hc
  rw [hc0]
  exact Submodule.zero_mem _

omit [Fintype V] in
/-- The link with the abstract boundary-matrix endpoint of `FreeFacet.lean`: the
matrix of genuine oriented boundary coefficients of the top simplices has
private rows, hence is injective. -/
theorem boundaryMatrix_top_injective {K : Finset (Finset V)} {n : ℕ}
    (hfree : HasFreeFacets (topSimplices K n)) :
    Function.Injective
      (boundaryMatrixLinearMap
        (fun (f : Finset V) (t : {t // t ∈ topSimplices K n}) => boundaryCoeff 𝕜 f t.1)) :=
  topBoundary_injective_of_hasFreeFacets hfree _ (fun f t => boundaryCoeff_ne_zero_iff f t.1)

/-! ### Cones are reduced acyclic

The star of a vertex in a simplicial complex is a cone, so this is the algebraic
core of any local-acyclicity argument. -/

/-- `K` is a cone with apex `a`: adding `a` to a simplex of `K` stays in `K`. -/
def IsConeWithApex (K : Finset (Finset V)) (a : V) : Prop := ∀ s ∈ K, insert a s ∈ K

/-- The cone contraction operator with apex `a`, a chain homotopy between the
identity and zero on the augmented chain complex. -/
def coneHomotopy (𝕜 V : Type*) [Field 𝕜] [LinearOrder V] [Fintype V] (a : V) :
    (Finset V → 𝕜) →ₗ[𝕜] (Finset V → 𝕜) where
  toFun c u := if a ∈ u then orientedSign 𝕜 (u.erase a) a * c (u.erase a) else 0
  map_add' c d := by
    funext u
    by_cases h : a ∈ u <;> simp [h, mul_add]
  map_smul' r c := by
    funext u
    by_cases h : a ∈ u <;> simp [h, mul_assoc, mul_comm]

@[simp]
theorem coneHomotopy_apply (a : V) (c : Finset V → 𝕜) (u : Finset V) :
    coneHomotopy 𝕜 V a c u = if a ∈ u then orientedSign 𝕜 (u.erase a) a * c (u.erase a) else 0 :=
  rfl

/-- The cone homotopy identity `∂ ∘ h + h ∘ ∂ = id` on the augmented chain
complex of the full simplex on `V`. -/
theorem coneHomotopy_identity (a : V) (c : Finset V → 𝕜) (u : Finset V) :
    boundary 𝕜 V (coneHomotopy 𝕜 V a c) u + coneHomotopy 𝕜 V a (boundary 𝕜 V c) u = c u := by
  by_cases hau : a ∈ u
  · set w := u.erase a with hw
    have haw : a ∉ w := Finset.notMem_erase a u
    have huw : insert a w = u := Finset.insert_erase hau
    have hcompl : wᶜ = insert a uᶜ := Finset.compl_erase
    have hanot : a ∉ (uᶜ : Finset V) := by simpa using hau
    have h2 : coneHomotopy 𝕜 V a (boundary 𝕜 V c) u
        = c u + ∑ v ∈ uᶜ, orientedSign 𝕜 w a * (orientedSign 𝕜 w v * c (insert v w)) := by
      simp only [coneHomotopy_apply, hau, ite_true, boundary_apply, ← hw]
      rw [hcompl, Finset.sum_insert hanot, mul_add, huw]
      congr 1
      · rw [← mul_assoc, orientedSign_sq, one_mul]
      · rw [Finset.mul_sum]
    have h1 : boundary 𝕜 V (coneHomotopy 𝕜 V a c) u
        = ∑ v ∈ uᶜ, orientedSign 𝕜 u v * (orientedSign 𝕜 (insert v w) a * c (insert v w)) := by
      rw [boundary_apply]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hvu : v ∉ u := by simpa using hv
      have hva : v ≠ a := fun h => hvu (h ▸ hau)
      have herase : (insert v u).erase a = insert v w := Finset.erase_insert_of_ne hva
      have hmem : a ∈ insert v u := Finset.mem_insert_of_mem hau
      simp only [coneHomotopy_apply, hmem, ite_true, herase]
    have hzero : ∑ v ∈ uᶜ, orientedSign 𝕜 u v * (orientedSign 𝕜 (insert v w) a * c (insert v w))
        + ∑ v ∈ uᶜ, orientedSign 𝕜 w a * (orientedSign 𝕜 w v * c (insert v w)) = 0 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_eq_zero fun v hv => ?_
      have hvu : v ∉ u := by simpa using hv
      have hva : v ≠ a := fun h => hvu (h ▸ hau)
      have hvw : v ∉ w := fun h => hvu (Finset.mem_of_mem_erase h)
      have hsign := orientedSign_cone_antisymm (𝕜 := 𝕜) haw hvw (Ne.symm hva)
      have hu : orientedSign 𝕜 u v = orientedSign 𝕜 (insert a w) v := by rw [huw]
      rw [hu]
      calc orientedSign 𝕜 (insert a w) v * (orientedSign 𝕜 (insert v w) a * c (insert v w))
            + orientedSign 𝕜 w a * (orientedSign 𝕜 w v * c (insert v w))
          = (orientedSign 𝕜 (insert a w) v * orientedSign 𝕜 (insert v w) a
              + orientedSign 𝕜 w a * orientedSign 𝕜 w v) * c (insert v w) := by ring
        _ = 0 := by rw [hsign, zero_mul]
    rw [h1, h2, add_comm (c u), ← add_assoc, hzero, zero_add]
  · have h2 : coneHomotopy 𝕜 V a (boundary 𝕜 V c) u = 0 := by
      simp only [coneHomotopy_apply, hau, ite_false]
    have h1 : boundary 𝕜 V (coneHomotopy 𝕜 V a c) u = c u := by
      rw [boundary_apply]
      have hsingle : ∑ v ∈ uᶜ, orientedSign 𝕜 u v * coneHomotopy 𝕜 V a c (insert v u)
          = orientedSign 𝕜 u a * coneHomotopy 𝕜 V a c (insert a u) := by
        refine Finset.sum_eq_single a ?_ ?_
        · intro v _ hva
          have hnot : a ∉ insert v u := by
            simp only [Finset.mem_insert, not_or]
            exact ⟨fun h => hva h.symm, hau⟩
          simp only [coneHomotopy_apply, hnot, ite_false, mul_zero]
        · intro hcon
          exact absurd (by simpa using hau) hcon
      rw [hsingle]
      have hmem : a ∈ insert a u := Finset.mem_insert_self a u
      have herase : (insert a u).erase a = u := Finset.erase_insert hau
      simp only [coneHomotopy_apply, hmem, ite_true, herase]
      rw [← mul_assoc, orientedSign_sq, one_mul]
    rw [h1, h2, add_zero]

/-- The cone contraction raises the degree of a chain of a cone by one. -/
theorem coneHomotopy_mem_chains {K : Finset (Finset V)} {a : V} (hK : IsConeWithApex K a)
    {n : ℕ} {c : Finset V → 𝕜} (hc : c ∈ chains 𝕜 K n) :
    coneHomotopy 𝕜 V a c ∈ chains 𝕜 K (n + 1) := by
  intro u hu
  rw [coneHomotopy_apply] at hu
  by_cases hau : a ∈ u
  · simp only [hau, ite_true] at hu
    have hcu : c (u.erase a) ≠ 0 := fun h => hu (by rw [h, mul_zero])
    obtain ⟨hmem, hcard⟩ := hc _ hcu
    have hins : insert a (u.erase a) = u := Finset.insert_erase hau
    refine ⟨hins ▸ hK _ hmem, ?_⟩
    have := Finset.card_erase_of_mem hau
    have hpos : 1 ≤ u.card := Finset.card_pos.mpr ⟨a, hau⟩
    omega
  · simp [hau] at hu

/-- **Cones are reduced acyclic.**  If `K` is a cone with apex `a`, then every
reduced cycle of `K` is a boundary, in every degree. -/
theorem isReducedAcyclic_of_cone {K : Finset (Finset V)} {a : V} (hK : IsConeWithApex K a) :
    IsReducedAcyclic 𝕜 K := by
  intro n c hc
  obtain ⟨hsupp, hcyc⟩ := hc
  refine ⟨coneHomotopy 𝕜 V a c, coneHomotopy_mem_chains hK hsupp, ?_⟩
  funext u
  have h := coneHomotopy_identity (𝕜 := 𝕜) a c u
  rw [hcyc] at h
  simpa using h

/-- The full simplex on a nonempty finite vertex set is reduced acyclic. -/
theorem isReducedAcyclic_powerset {S : Finset V} {a : V} (ha : a ∈ S) :
    IsReducedAcyclic 𝕜 S.powerset :=
  isReducedAcyclic_of_cone (fun _s hs =>
    Finset.mem_powerset.mpr (Finset.insert_subset ha (Finset.mem_powerset.mp hs)))

/-! ### Sanity checks

The boundary operator is not degenerate: the boundary of an edge is nonzero. -/

example : boundary ℚ (Fin 2) (fun s => if s = {0, 1} then 1 else 0) ≠ 0 := by
  intro h
  have h0 := congrFun h ({0} : Finset (Fin 2))
  rw [boundary_apply] at h0
  have hc : ({0} : Finset (Fin 2))ᶜ = {1} := by decide
  have hins : insert (1 : Fin 2) ({0} : Finset (Fin 2)) = {0, 1} := by decide
  rw [hc, Finset.sum_singleton, hins] at h0
  simp [orientedSign] at h0

/-! ### Next steps

The layer above is complete and self-contained.  The first statement *not* yet
formalized here, and the natural next target for the acyclic gluing part of the
argument, is Mayer-Vietoris for two face-closed families `K` and `L`:  the short
exact sequence of chain complexes
`0 → chains 𝕜 (K ∩ L) n → chains 𝕜 K n × chains 𝕜 L n → chains 𝕜 (K ∪ L) n → 0`
(whose exactness at the two ends is `chains_inter` and `chains_union` above)
should be turned into the connecting homomorphism and the resulting gluing
statement: if `K`, `L` and `K ∩ L` are reduced acyclic and `K ∩ L` is nonempty,
then `K ∪ L` is reduced acyclic. -/

end Boundary

end Simplicial

end AffineTverberg

