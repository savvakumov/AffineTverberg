import AffineTverberg.CayleyJoinFaces

set_option linter.style.header false

/-!
# Affine rank and the projected-span step

This file contains the linear algebra behind the good-vertex count of the
bad-vertex triangulation.

* `arank s` is the affine rank `dim (aff s) + 1` of a set, with `arank ∅ = 0`.
* `affineSpan_insert_eq_of_arank_step`: if `G ⊆ S` and `arank G + 1 = arank S`,
  then adjoining to `G` *any* point of `S` off the affine span of `G` already
  spans `S`.  The case `G = ∅` (then `S` is a single point) is included.
* `affineSpan_iUnion_le_insert` and its two corollaries
  `arank_iUnion_le_succ`, `arank_iUnion_le_of_shared`: **the paper's
  projected-span step.**  If one factor of a family grows by a facet step, the
  affine span of the union grows by at most one dimension, and does not grow at
  all if the extra point already lies in the affine span of another (unchanged)
  factor.  This is what makes a bad apex cost nothing.
* `exists_unique_index_of_sum_step`: on a rank step of a sum exactly one summand
  changes, and it changes by one.

No factor is assumed nonempty anywhere.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg
namespace CayleyJoin

open PolytopeFace

/-! ### Affine rank -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The affine rank of a set: one more than the dimension of its affine span,
and `0` for the empty set. -/
def arank (s : Set E) : ℕ :=
  if s = ∅ then 0 else Module.finrank ℝ (vectorSpan ℝ s) + 1

omit [FiniteDimensional ℝ E] in
@[simp]
theorem arank_empty : arank (∅ : Set E) = 0 := by simp [arank]

omit [FiniteDimensional ℝ E] in
theorem arank_eq_zero_iff {s : Set E} : arank s = 0 ↔ s = ∅ := by
  unfold arank
  split <;> simp_all

omit [FiniteDimensional ℝ E] in
theorem arank_pos {s : Set E} (hs : s.Nonempty) : 0 < arank s := by
  rcases Nat.eq_zero_or_pos (arank s) with h | h
  · exact absurd (arank_eq_zero_iff.mp h) hs.ne_empty
  · exact h

omit [FiniteDimensional ℝ E] in
theorem arank_of_nonempty {s : Set E} (hs : s.Nonempty) :
    arank s = Module.finrank ℝ (vectorSpan ℝ s) + 1 := by
  simp [arank, hs.ne_empty]

omit [FiniteDimensional ℝ E] in
@[simp]
theorem arank_singleton (x : E) : arank ({x} : Set E) = 1 := by
  rw [arank_of_nonempty (singleton_nonempty x)]
  simp

omit [FiniteDimensional ℝ E] in
theorem nonempty_of_subset_affineSpan {s t : Set E} (hs : s.Nonempty)
    (h : s ⊆ affineSpan ℝ t) : t.Nonempty := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · obtain ⟨x, hx⟩ := hs
    have := h hx
    simp at this
  · exact ht

/-- Affine rank is monotone along inclusion into an affine span. -/
theorem arank_le_of_subset_affineSpan {s t : Set E} (h : s ⊆ affineSpan ℝ t) :
    arank s ≤ arank t := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have ht : t.Nonempty := nonempty_of_subset_affineSpan hs h
  have hle : affineSpan ℝ s ≤ affineSpan ℝ t := affineSpan_le.mpr h
  have hdir : vectorSpan ℝ s ≤ vectorSpan ℝ t := by
    have := AffineSubspace.direction_le hle
    rwa [direction_affineSpan, direction_affineSpan] at this
  rw [arank_of_nonempty hs, arank_of_nonempty ht]
  exact Nat.succ_le_succ (Submodule.finrank_mono hdir)

theorem arank_mono {s t : Set E} (h : s ⊆ t) : arank s ≤ arank t :=
  arank_le_of_subset_affineSpan (h.trans (subset_affineSpan ℝ t))

theorem arank_eq_of_affineSpan_eq {s t : Set E}
    (h : affineSpan ℝ s = affineSpan ℝ t) : arank s = arank t :=
  le_antisymm (arank_le_of_subset_affineSpan (h ▸ subset_affineSpan ℝ s))
    (arank_le_of_subset_affineSpan (h ▸ subset_affineSpan ℝ t))

@[simp]
theorem arank_convexHull (s : Set E) : arank (convexHull ℝ s) = arank s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · exact arank_eq_of_affineSpan_eq (affineSpan_convexHull s)

/-- Equality of the affine spans of nested sets of equal rank. -/
theorem affineSpan_eq_of_subset_of_arank_le {s t : Set E} (hs : s.Nonempty)
    (hst : s ⊆ t) (h : arank t ≤ arank s) : affineSpan ℝ s = affineSpan ℝ t := by
  have ht : t.Nonempty := hs.mono hst
  have hle : vectorSpan ℝ s ≤ vectorSpan ℝ t := vectorSpan_mono ℝ hst
  have hfin : Module.finrank ℝ (vectorSpan ℝ t) ≤ Module.finrank ℝ (vectorSpan ℝ s) := by
    rw [arank_of_nonempty hs, arank_of_nonempty ht] at h; omega
  have hdir : vectorSpan ℝ s = vectorSpan ℝ t :=
    Submodule.eq_of_le_of_finrank_le hle hfin
  refine AffineSubspace.ext_of_direction_eq ?_ ?_
  · rw [direction_affineSpan, direction_affineSpan, hdir]
  · obtain ⟨x, hx⟩ := hs
    exact ⟨x, subset_affineSpan ℝ s hx, subset_affineSpan ℝ t (hst hx)⟩

/-- A point of `t` outside the affine span of `s ⊆ t` strictly raises the rank. -/
theorem arank_lt_of_notMem_affineSpan {s t : Set E} (hst : s ⊆ t) {v : E} (hv : v ∈ t)
    (hvs : v ∉ affineSpan ℝ s) : arank s < arank t := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using arank_pos ⟨v, hv⟩
  · by_contra hcon
    push Not at hcon
    exact hvs ((affineSpan_eq_of_subset_of_arank_le hs hst hcon).symm ▸
      subset_affineSpan ℝ t hv)

/-- A set of affine rank at most one has at most one point. -/
theorem eq_of_arank_le_one {s : Set E} (h : arank s ≤ 1) {a b : E} (ha : a ∈ s)
    (hb : b ∈ s) : a = b := by
  by_contra hne
  have hsub : ({a, b} : Set E) ⊆ s := by
    intro x hx
    rcases hx with rfl | hx
    · exact ha
    · rw [mem_singleton_iff] at hx; subst hx; exact hb
  have hlt : arank ({a} : Set E) < arank ({a, b} : Set E) := by
    refine arank_lt_of_notMem_affineSpan (t := ({a, b} : Set E)) (v := b)
      (by simp) (by simp) ?_
    intro hcon
    rw [← AffineSubspace.mem_coe, AffineSubspace.coe_affineSpan_singleton ℝ E a,
      mem_singleton_iff] at hcon
    exact hne hcon.symm
  have := arank_mono hsub
  rw [arank_singleton] at hlt
  omega

theorem arank_insert_le (x : E) (s : Set E) : arank (insert x s) ≤ arank s + 1 := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨p, hp⟩ := hs
  have hp' : p ∈ insert x s := mem_insert_of_mem _ hp
  have h1 : vectorSpan ℝ (insert x s) = Submodule.span ℝ ((· -ᵥ p) '' insert x s) :=
    vectorSpan_eq_span_vsub_set_right ℝ hp'
  have h2 : vectorSpan ℝ s = Submodule.span ℝ ((· -ᵥ p) '' s) :=
    vectorSpan_eq_span_vsub_set_right ℝ hp
  have himg : (· -ᵥ p) '' insert x s = insert (x -ᵥ p) ((· -ᵥ p) '' s) := by
    rw [image_insert_eq]
  have h3 : vectorSpan ℝ (insert x s)
      = Submodule.span ℝ {x -ᵥ p} ⊔ vectorSpan ℝ s := by
    rw [h1, himg, h2, ← Submodule.span_union, ← Set.singleton_union]
  have h4 : Module.finrank ℝ (vectorSpan ℝ (insert x s))
      ≤ Module.finrank ℝ (Submodule.span ℝ ({x -ᵥ p} : Set E))
        + Module.finrank ℝ (vectorSpan ℝ s) := by
    rw [h3]
    have := Submodule.finrank_sup_add_finrank_inf_eq
      (Submodule.span ℝ ({x -ᵥ p} : Set E)) (vectorSpan ℝ s)
    omega
  have h5 : Module.finrank ℝ (Submodule.span ℝ ({x -ᵥ p} : Set E)) ≤ 1 := by
    rcases eq_or_ne (x -ᵥ p) (0 : E) with h0 | h0
    · have hbot : (Submodule.span ℝ ({x -ᵥ p} : Set E)) = ⊥ := by
        rw [h0]; exact Submodule.span_zero_singleton ℝ
      rw [hbot]; simp
    · rw [show (Submodule.span ℝ ({x -ᵥ p} : Set E)) = ℝ ∙ (x -ᵥ p) from rfl,
        finrank_span_singleton h0]
  rw [arank_of_nonempty ⟨x, mem_insert _ _⟩, arank_of_nonempty ⟨p, hp⟩]
  omega

/-! ### A facet step is spanned by any point off the smaller span -/

/-- **A facet plus one outside point spans.**  If `G ⊆ S` has rank one less than
`S`, then adding to `G` any point of `S` off the affine span of `G` spans `S`.
The case `G = ∅`, i.e. `S` a single point, is included. -/
theorem affineSpan_insert_eq_of_arank_step {G S : Set E} (hGS : G ⊆ S)
    (hstep : arank G + 1 = arank S) {v : E} (hv : v ∈ S) (hvG : v ∉ affineSpan ℝ G) :
    affineSpan ℝ (insert v G) = affineSpan ℝ S := by
  have hsub : insert v G ⊆ S := insert_subset hv hGS
  have hlt : arank G < arank (insert v G) :=
    arank_lt_of_notMem_affineSpan (subset_insert v G) (mem_insert _ _) hvG
  have hle : arank (insert v G) ≤ arank G + 1 := arank_insert_le v G
  have heq : arank (insert v G) = arank S := by omega
  exact affineSpan_eq_of_subset_of_arank_le ⟨v, mem_insert _ _⟩ hsub (le_of_eq heq.symm)

/-- Existence form of the previous lemma. -/
theorem exists_insert_affineSpan_eq {G S : Set E} (hGS : G ⊆ S)
    (hstep : arank G + 1 = arank S) :
    ∃ v ∈ S, affineSpan ℝ (insert v G) = affineSpan ℝ S := by
  have : ∃ v ∈ S, v ∉ affineSpan ℝ G := by
    by_contra hcon
    push Not at hcon
    have := arank_le_of_subset_affineSpan hcon
    omega
  obtain ⟨v, hv, hvG⟩ := this
  exact ⟨v, hv, affineSpan_insert_eq_of_arank_step hGS hstep hv hvG⟩

/-! ### The projected-span step -/

omit [FiniteDimensional ℝ E] in
/-- If all factors but one are affinely contained in the corresponding smaller
factors, and the exceptional factor is contained in the span of its smaller
factor together with one extra point `v`, then the union is contained in the
span of the smaller union together with `v`. -/
theorem affineSpan_iUnion_le_insert {ι : Type*} (A B : ι → Set E) (i : ι) (v : E)
    (hother : ∀ k, k ≠ i → affineSpan ℝ (A k) ≤ affineSpan ℝ (B k))
    (hi : affineSpan ℝ (A i) ≤ affineSpan ℝ (insert v (B i))) :
    affineSpan ℝ (⋃ k, A k) ≤ affineSpan ℝ (insert v (⋃ k, B k)) := by
  refine affineSpan_le.mpr ?_
  rintro x hx
  obtain ⟨k, hk⟩ := mem_iUnion.mp hx
  by_cases hki : k = i
  · subst hki
    have : x ∈ affineSpan ℝ (insert v (B k)) := hi (subset_affineSpan ℝ _ hk)
    exact affineSpan_mono ℝ
      (insert_subset_insert (subset_iUnion B k)) this
  · have : x ∈ affineSpan ℝ (B k) := hother k hki (subset_affineSpan ℝ _ hk)
    exact affineSpan_mono ℝ
      ((subset_iUnion B k).trans (subset_insert _ _)) this

/-- **The union gains at most one dimension from a facet step in one factor.** -/
theorem arank_iUnion_le_succ {ι : Type*} (A B : ι → Set E) (i : ι) (v : E)
    (hother : ∀ k, k ≠ i → affineSpan ℝ (A k) ≤ affineSpan ℝ (B k))
    (hi : affineSpan ℝ (A i) ≤ affineSpan ℝ (insert v (B i))) :
    arank (⋃ k, A k) ≤ arank (⋃ k, B k) + 1 := by
  have h := affineSpan_iUnion_le_insert A B i v hother hi
  have h1 : arank (⋃ k, A k) ≤ arank (insert v (⋃ k, B k)) :=
    arank_le_of_subset_affineSpan ((subset_affineSpan ℝ _).trans h)
  have h2 := arank_insert_le v (⋃ k, B k)
  omega

/-- **A bad apex costs nothing**: if moreover the extra point `v` already lies in
the affine span of the smaller union, the rank of the union does not grow. -/
theorem arank_iUnion_le_of_shared {ι : Type*} (A B : ι → Set E) (i : ι) (v : E)
    (hother : ∀ k, k ≠ i → affineSpan ℝ (A k) ≤ affineSpan ℝ (B k))
    (hi : affineSpan ℝ (A i) ≤ affineSpan ℝ (insert v (B i)))
    (hv : v ∈ affineSpan ℝ (⋃ k, B k)) :
    arank (⋃ k, A k) ≤ arank (⋃ k, B k) := by
  have h := affineSpan_iUnion_le_insert A B i v hother hi
  have hins : affineSpan ℝ (insert v (⋃ k, B k)) = affineSpan ℝ (⋃ k, B k) := by
    refine le_antisymm (affineSpan_le.mpr ?_) (affineSpan_mono ℝ (subset_insert _ _))
    rintro x hx
    rcases hx with rfl | hx
    · exact hv
    · exact subset_affineSpan ℝ _ hx
  rw [hins] at h
  exact arank_le_of_subset_affineSpan ((subset_affineSpan ℝ _).trans h)

/-! ### One summand changes on a rank step -/

/-- On a rank step of a sum exactly one summand changes, and by one. -/
theorem exists_unique_index_of_sum_step {ι : Type*} [Fintype ι]
    (a b : ι → ℕ) (hle : ∀ k, b k ≤ a k) (hstep : ∑ k, b k + 1 = ∑ k, a k) :
    ∃ i, b i + 1 = a i ∧ ∀ k, k ≠ i → b k = a k := by
  classical
  have hlt : ∑ k, b k < ∑ k, a k := by omega
  obtain ⟨i, -, hi⟩ := Finset.exists_lt_of_sum_lt hlt
  refine ⟨i, ?_, ?_⟩
  · have hsum : ∑ k ∈ Finset.univ.erase i, b k ≤ ∑ k ∈ Finset.univ.erase i, a k :=
      Finset.sum_le_sum fun k _ ↦ hle k
    have hb : ∑ k, b k = b i + ∑ k ∈ Finset.univ.erase i, b k :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    have ha : ∑ k, a k = a i + ∑ k ∈ Finset.univ.erase i, a k :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    omega
  · intro k hk
    have hsum : ∑ k ∈ Finset.univ.erase i, b k ≤ ∑ k ∈ Finset.univ.erase i, a k :=
      Finset.sum_le_sum fun k _ ↦ hle k
    have hb : ∑ k, b k = b i + ∑ k ∈ Finset.univ.erase i, b k :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    have ha : ∑ k, a k = a i + ∑ k ∈ Finset.univ.erase i, a k :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm
    have heq : ∑ k ∈ Finset.univ.erase i, b k = ∑ k ∈ Finset.univ.erase i, a k := by
      omega
    have := (Finset.sum_eq_sum_iff_of_le (fun k _ ↦ hle k)).mp heq
    exact this k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)

end CayleyJoin
end AffineTverberg
