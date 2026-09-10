import AffineTverberg.CayleyJoinRank

set_option linter.style.header false

/-!
# The dimension formula for the Cayley join

The affine rank of a Cayley join is the sum of the affine ranks of its factors:

`arank (cayleyJoin Fs) = ∑ i, arank (Fs i)`.

Empty factors are allowed and contribute `0`.  Equivalently, the dimension of a
nonempty Cayley join is `∑ (dim Fᵢ + 1) - 1`, the classical join dimension
formula.

The upper bound is a union bound (`arank_biUnion_le_sum`) applied to the
description of the Cayley join as the convex hull of the copied factors.  The
lower bound is obtained by exhibiting, in the join, an affinely independent
family of `∑ arank (Fs i)` points: affinely independent spanning families in the
factors, copied into their slots.  A dependence would restrict, slot by slot, to
a dependence inside one factor, because the Cayley slot carries the homogenizing
coordinate `1`.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg
namespace CayleyJoin

/-! ### General bounds on the affine rank -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
/-- The affine rank of an affinely independent family is its cardinality. -/
theorem arank_range_of_affineIndependent {ι : Type*} [Fintype ι] {p : ι → E}
    (hp : AffineIndependent ℝ p) : arank (range p) = Fintype.card ι := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h0 | hpos
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp h0
    rw [h0, arank_eq_zero_iff, range_eq_empty_iff]
    exact this
  · obtain ⟨N, hN⟩ : ∃ N, Fintype.card ι = N + 1 := ⟨Fintype.card ι - 1, by omega⟩
    have hne : (range p).Nonempty := by
      have : Nonempty ι := Fintype.card_pos_iff.mp hpos
      obtain ⟨i⟩ := this
      exact ⟨p i, mem_range_self i⟩
    rw [arank_of_nonempty hne, hp.finrank_vectorSpan hN, hN]

/-- The affine rank does not grow under an affine map. -/
theorem arank_image_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (f : E →ᵃ[ℝ] F) (s : Set E) : arank (f '' s) ≤ arank s := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hne : (f '' s).Nonempty := hs.image f
  have hdir : vectorSpan ℝ (f '' s) = (vectorSpan ℝ s).map f.linear := by
    rw [← direction_affineSpan, ← AffineSubspace.map_span, AffineSubspace.map_direction,
      direction_affineSpan]
  rw [arank_of_nonempty hne, arank_of_nonempty hs, hdir]
  exact Nat.succ_le_succ (Submodule.finrank_map_le _ _)

/-- The affine rank of a union is at most the sum of the affine ranks. -/
theorem arank_union_le (s t : Set E) : arank (s ∪ t) ≤ arank s + arank t := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simp
  obtain ⟨p, hp⟩ := hs
  obtain ⟨q, hq⟩ := ht
  have hpu : p ∈ s ∪ t := Or.inl hp
  have h1 : vectorSpan ℝ (s ∪ t) = Submodule.span ℝ ((· -ᵥ p) '' (s ∪ t)) :=
    vectorSpan_eq_span_vsub_set_right ℝ hpu
  have h2 : vectorSpan ℝ s = Submodule.span ℝ ((· -ᵥ p) '' s) :=
    vectorSpan_eq_span_vsub_set_right ℝ hp
  have h3 : (· -ᵥ p) '' t
      ⊆ (Submodule.span ℝ ({q -ᵥ p} : Set E) ⊔ vectorSpan ℝ t : Submodule ℝ E) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxq : x -ᵥ q ∈ vectorSpan ℝ t := vsub_mem_vectorSpan ℝ hx hq
    have hxeq : (x -ᵥ p : E) = (q -ᵥ p) + (x -ᵥ q) := by
      simp only [vsub_eq_sub]; abel
    change (x -ᵥ p : E) ∈ _
    rw [hxeq]
    exact Submodule.add_mem_sup (Submodule.subset_span rfl) hxq
  have hle : vectorSpan ℝ (s ∪ t)
      ≤ vectorSpan ℝ s ⊔ (Submodule.span ℝ ({q -ᵥ p} : Set E) ⊔ vectorSpan ℝ t) := by
    rw [h1]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with hx | hx
    · exact Submodule.mem_sup_left (by rw [h2]; exact Submodule.subset_span ⟨x, hx, rfl⟩)
    · exact Submodule.mem_sup_right (h3 ⟨x, hx, rfl⟩)
  have hfin1 := Submodule.finrank_sup_add_finrank_inf_eq (vectorSpan ℝ s)
    (Submodule.span ℝ ({q -ᵥ p} : Set E) ⊔ vectorSpan ℝ t)
  have hfin2 := Submodule.finrank_sup_add_finrank_inf_eq
    (Submodule.span ℝ ({q -ᵥ p} : Set E)) (vectorSpan ℝ t)
  have hspan1 : Module.finrank ℝ (Submodule.span ℝ ({q -ᵥ p} : Set E)) ≤ 1 := by
    rcases eq_or_ne (q -ᵥ p) (0 : E) with h0 | h0
    · have hbot : (Submodule.span ℝ ({q -ᵥ p} : Set E)) = ⊥ := by
        rw [h0]; exact Submodule.span_zero_singleton ℝ
      rw [hbot]; simp
    · rw [show (Submodule.span ℝ ({q -ᵥ p} : Set E)) = ℝ ∙ (q -ᵥ p) from rfl,
        finrank_span_singleton h0]
  have hmono := Submodule.finrank_mono hle
  rw [arank_of_nonempty ⟨p, hpu⟩, arank_of_nonempty ⟨p, hp⟩, arank_of_nonempty ⟨q, hq⟩]
  omega

/-- The affine rank of a finite union is at most the sum of the affine ranks. -/
theorem arank_biUnion_le_sum {ι : Type*} (s : Finset ι) (A : ι → Set E) :
    arank (⋃ i ∈ s, A i) ≤ ∑ i ∈ s, arank (A i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      have hunion : (⋃ i ∈ insert a s, A i) = A a ∪ ⋃ i ∈ s, A i := by
        ext x; simp [Finset.mem_insert]
      rw [hunion, Finset.sum_insert ha]
      exact le_trans (arank_union_le _ _) (Nat.add_le_add_left ih _)

end General

/-! ### The dimension formula -/

variable {n m : ℕ}

/-- **Upper bound**: the affine rank of a Cayley join is at most the sum of the
affine ranks of its factors. -/
theorem arank_cayleyJoin_le (Fs : Fin (m + 1) → Set (CoordinateSpace n))
    (hconv : ∀ i, Convex ℝ (Fs i)) :
    arank (cayleyJoin Fs) ≤ ∑ i, arank (Fs i) := by
  rw [cayleyJoin_eq_convexHull hconv, arank_convexHull]
  have hunion : (⋃ i, polytopalJoinCopy i '' Fs i)
      = ⋃ i ∈ (Finset.univ : Finset (Fin (m + 1))), polytopalJoinCopy i '' Fs i := by
    ext x; simp
  rw [hunion]
  refine le_trans (arank_biUnion_le_sum _ _) (Finset.sum_le_sum fun i _ ↦ ?_)
  have himg : (polytopalJoinCopyAffine (n := n) (m := m) i) '' Fs i
      = polytopalJoinCopy i '' Fs i := by
    ext y
    simp [polytopalJoinCopyAffine_apply]
  rw [← himg]
  exact arank_image_le _ _

/-- **Lower bound**: the affine rank of a Cayley join is at least the sum of the
affine ranks of its factors.  No convexity is needed. -/
theorem sum_arank_le_arank_cayleyJoin (Fs : Fin (m + 1) → Set (CoordinateSpace n)) :
    ∑ i, arank (Fs i) ≤ arank (cayleyJoin Fs) := by
  classical
  -- affinely independent spanning families in the factors
  have hfam : ∀ i : Fin (m + 1), ∃ (d : ℕ) (q : Fin d → CoordinateSpace n),
      AffineIndependent ℝ q ∧ (∀ k, q k ∈ Fs i) ∧ d = arank (Fs i) := by
    intro i
    obtain ⟨t, hts, hspan, hind⟩ := exists_affineIndependent ℝ (CoordinateSpace n) (Fs i)
    have hfinite : Finite t := finite_of_fin_dim_affineIndependent ℝ hind
    have hft : Fintype t := Fintype.ofFinite t
    let e := (Fintype.equivFin t).symm
    refine ⟨Fintype.card t, fun k ↦ ((e k : CoordinateSpace n)), ?_, ?_, ?_⟩
    · exact hind.comp_embedding e.toEmbedding
    · intro k; exact hts (e k).2
    · have hrange : range (fun k ↦ ((e k : CoordinateSpace n))) = t := by
        ext x
        constructor
        · rintro ⟨k, rfl⟩; exact (e k).2
        · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp [e]⟩
      have h1 : arank (range (fun k ↦ ((e k : CoordinateSpace n))))
          = Fintype.card (Fin (Fintype.card t)) :=
        arank_range_of_affineIndependent (hind.comp_embedding e.toEmbedding)
      rw [hrange] at h1
      have h2 : arank t = arank (Fs i) := arank_eq_of_affineSpan_eq hspan
      simp only [Fintype.card_fin] at h1
      omega
  choose d q hqind hqmem hqcard using hfam
  -- the copied family in the join
  set v : ((i : Fin (m + 1)) × Fin (d i)) → PolytopalJoinAmbient n m :=
    fun e ↦ polytopalJoinCopy e.1 (q e.1 e.2) with hv
  have hvmem : ∀ e, v e ∈ cayleyJoin Fs := by
    intro e
    exact copy_mem_cayleyJoin_iff.mpr (hqmem e.1 e.2)
  have hind : AffineIndependent ℝ v := by
    rw [affineIndependent_iff_of_fintype]
    intro w hw hvsub
    rw [Finset.weightedVSub_eq_linear_combination Finset.univ hw] at hvsub
    have hslot : ∀ j : Fin (m + 1),
        ∑ k : Fin (d j), w ⟨j, k⟩ • ((q j k, 1) : CoordinateSpace n × ℝ) = 0 := by
      intro j
      have h0 := congrFun hvsub j
      rw [Finset.sum_apply] at h0
      have hterm : ∀ e : (i : Fin (m + 1)) × Fin (d i),
          (w e • v e) j
            = if j = e.1 then w e • ((q e.1 e.2, 1) : CoordinateSpace n × ℝ) else 0 := by
        intro e
        by_cases h : j = e.1
        · subst h; simp [hv, polytopalJoinCopy]
        · simp [hv, polytopalJoinCopy, h]
      rw [Finset.sum_congr rfl fun e _ ↦ hterm e, Fintype.sum_sigma] at h0
      have hswap : ∀ i : Fin (m + 1),
          (∑ k : Fin (d i),
              if j = i then w ⟨i, k⟩ • ((q i k, 1) : CoordinateSpace n × ℝ) else 0)
            = if j = i then
                (∑ k : Fin (d i), w ⟨i, k⟩ • ((q i k, 1) : CoordinateSpace n × ℝ)) else 0 := by
        intro i
        by_cases h : j = i <;> simp [h]
      rw [Finset.sum_congr rfl fun i _ ↦ hswap i, Finset.sum_ite_eq] at h0
      simpa using h0
    intro e₀
    set j := e₀.1 with hj
    have hs2 : ∑ k : Fin (d j), w ⟨j, k⟩ = 0 := by
      have := congrArg Prod.snd (hslot j)
      simpa [Prod.snd_sum] using this
    have hs1 : ∑ k : Fin (d j), w ⟨j, k⟩ • q j k = 0 := by
      have := congrArg Prod.fst (hslot j)
      simpa [Prod.fst_sum] using this
    have hzero := (affineIndependent_iff_of_fintype ℝ (q j)).mp (hqind j)
      (fun k ↦ w ⟨j, k⟩) hs2
      (by rw [Finset.weightedVSub_eq_linear_combination Finset.univ hs2]; exact hs1)
    have := hzero e₀.2
    simpa using this
  have hsub : range v ⊆ cayleyJoin Fs := by
    rintro _ ⟨e, rfl⟩; exact hvmem e
  have hcard : arank (range v) = ∑ i, arank (Fs i) := by
    rw [arank_range_of_affineIndependent hind, Fintype.card_sigma]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Fintype.card_fin, hqcard i]
  rw [← hcard]
  exact arank_mono hsub

/-- **The dimension formula for the Cayley join.** -/
theorem arank_cayleyJoin (Fs : Fin (m + 1) → Set (CoordinateSpace n))
    (hconv : ∀ i, Convex ℝ (Fs i)) :
    arank (cayleyJoin Fs) = ∑ i, arank (Fs i) :=
  le_antisymm (arank_cayleyJoin_le Fs hconv) (sum_arank_le_arank_cayleyJoin Fs)

end CayleyJoin
end AffineTverberg
