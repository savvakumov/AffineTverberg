import AffineTverberg.BadEdgeSubdivision

set_option linter.style.header false

/-!
# Barycentric coordinates of the bad-edge subdivision

A vertex `s` of the bad-edge subdivision is a nonempty set of at most two join
vertices; geometrically it is the barycentre of `s`, so its barycentric
coordinate vector with respect to the original join vertices is `coordVec s`,
the normalized indicator function of `s`.  A nonnegative weight function `l` on
the subdivision vertices is sent to the coordinate vector `coeffPoint l`.

The two main results are purely about these coordinate vectors, and are the
combinatorial heart of the statement that the subdivision is a genuine
triangulation:

* `coordVec_linearIndependent` : the coordinate vectors of the vertices of a
  single simplex of the subdivision are linearly independent (hence, since they
  all have coordinate sum one, affinely independent);
* `coeffPoint_injective` : *distinct* simplices of the subdivision assign
  distinct coordinate vectors to distinct weight functions.  Equivalently, the
  weights of a point of the subdivision are unique, which gives both the
  intersection property and the fact that a point lies in the relative interior
  of a unique simplex.
-/

open scoped BigOperators

namespace AffineTverberg
namespace BadEdge

variable {W V : Type*} [Fintype W] [DecidableEq W] [LinearOrder W] [DecidableEq V]

/-- The barycentric coordinate vector of the subdivision vertex `s`: the
normalized indicator function of `s`. -/
noncomputable def coordVec (s : Finset W) : W → ℝ :=
  fun w ↦ if w ∈ s then (s.card : ℝ)⁻¹ else 0

omit [Fintype W] [LinearOrder W] in
theorem coordVec_nonneg (s : Finset W) (w : W) : 0 ≤ coordVec s w := by
  unfold coordVec
  split
  · positivity
  · exact le_refl 0

omit [Fintype W] [LinearOrder W] in
theorem coordVec_eq_zero {s : Finset W} {w : W} (h : w ∉ s) : coordVec s w = 0 := by
  simp [coordVec, h]

omit [Fintype W] [LinearOrder W] in
theorem coordVec_of_mem {s : Finset W} {w : W} (h : w ∈ s) :
    coordVec s w = (s.card : ℝ)⁻¹ := by
  simp [coordVec, h]

omit [Fintype W] [LinearOrder W] in
theorem coordVec_pos {s : Finset W} {w : W} (h : w ∈ s) : 0 < coordVec s w := by
  rw [coordVec_of_mem h]
  have : 0 < s.card := Finset.card_pos.mpr ⟨w, h⟩
  positivity

omit [LinearOrder W] in
/-- The coordinate vectors have coordinate sum one. -/
theorem sum_coordVec {s : Finset W} (hs : s.Nonempty) : ∑ w, coordVec s w = 1 := by
  classical
  rw [Finset.sum_congr rfl (fun w _ ↦ rfl)]
  rw [show (∑ w, coordVec s w) = ∑ w ∈ s, (s.card : ℝ)⁻¹ by
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ s)]
    have h1 : Finset.univ.filter (· ∈ s) = s := by ext w; simp
    have h2 : ∑ w ∈ Finset.univ.filter (fun w ↦ ¬ w ∈ s), coordVec s w = 0 := by
      apply Finset.sum_eq_zero
      intro w hw
      exact coordVec_eq_zero (Finset.mem_filter.mp hw).2
    rw [h1, h2, add_zero]
    exact Finset.sum_congr rfl fun w hw ↦ coordVec_of_mem hw]
  rw [Finset.sum_const, nsmul_eq_mul]
  have : (s.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero_of_mem hs.choose_spec)
  field_simp

/-- The coordinate vector of a weight function on subdivision vertices. -/
noncomputable def coeffPoint (l : Finset W → ℝ) : W → ℝ :=
  fun w ↦ ∑ s : Finset W, l s * coordVec s w

omit [LinearOrder W] in
theorem coeffPoint_nonneg {l : Finset W → ℝ} (hl : ∀ s, 0 ≤ l s) (w : W) :
    0 ≤ coeffPoint l w :=
  Finset.sum_nonneg fun s _ ↦ mul_nonneg (hl s) (coordVec_nonneg s w)

omit [LinearOrder W] in
theorem coeffPoint_erase (l : Finset W → ℝ) (a : Finset W) (w : W) :
    coeffPoint (Function.update l a 0) w =
      coeffPoint l w - l a * coordVec a w := by
  unfold coeffPoint
  rw [← Finset.add_sum_erase _ (fun s ↦ Function.update l a 0 s * coordVec s w)
      (Finset.mem_univ a),
    ← Finset.add_sum_erase _ (fun s ↦ l s * coordVec s w) (Finset.mem_univ a)]
  simp only [Function.update_self, zero_mul, zero_add]
  rw [Finset.sum_congr rfl (fun s hs ↦ by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)])]
  ring

/-! ### Linear independence of the vertices of a simplex -/

/-- The barycentric coordinate vectors of the vertices of a single simplex of
the subdivision are linearly independent.  The proof is the recursion of the
construction: the apex is the only vertex meeting the erased join vertex. -/
theorem coordVec_linearIndependent (orig : W → V) (S : Finset W)
    {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S) :
    ∀ l : Finset W → ℝ, (∀ s, s ∉ σ → l s = 0) →
      (∀ w, ∑ s : Finset W, l s * coordVec s w = 0) → ∀ s, l s = 0 := by
  induction S using Finset.strongInduction generalizing σ with
  | _ S ih =>
    intro l hls hl
    rcases S.eq_empty_or_nonempty with rfl | hS
    · rw [sdFaces_empty, Finset.mem_singleton] at hσ
      subst hσ
      intro s
      exact hls s (Finset.notMem_empty s)
    · set a := apexSet orig S with ha
      obtain ⟨u, hu, hmem⟩ := exists_erase_apex_mem hS hσ
      have hno : ∀ s, s ≠ a → l s ≠ 0 → u ∉ s := by
        intro s hsa hs0 hus
        have hsσ : s ∈ σ := by
          by_contra hc
          exact hs0 (hls s hc)
        have : s ∈ σ.erase a := Finset.mem_erase.mpr ⟨hsa, hsσ⟩
        have hsub := (sdFaces_vertex orig _ hmem s this).2.1
        exact (Finset.mem_erase.mp (hsub hus)).1 rfl
      -- the coefficient of the apex vanishes, by looking at the coordinate `u`
      have hau : coordVec a u = (a.card : ℝ)⁻¹ := coordVec_of_mem hu
      have hla : l a = 0 := by
        have hsum : ∑ s : Finset W, l s * coordVec s u = l a * coordVec a u := by
          refine Finset.sum_eq_single a (fun s _ hsa ↦ ?_) (fun hc ↦ absurd (Finset.mem_univ a) hc)
          by_cases hs0 : l s = 0
          · rw [hs0, zero_mul]
          · rw [coordVec_eq_zero (hno s hsa hs0), mul_zero]
        rw [hl u, hau] at hsum
        have hcard : (0 : ℝ) < (a.card : ℝ) := by
          exact_mod_cast Finset.card_pos.mpr (apexSet_nonempty hS)
        have : l a * (a.card : ℝ)⁻¹ = 0 := hsum.symm
        rcases mul_eq_zero.mp this with h | h
        · exact h
        · exact absurd h (inv_ne_zero (ne_of_gt hcard))
      -- the remaining vertices lie in the subdivision of a smaller face
      have hlt : S.erase u ⊂ S := Finset.erase_ssubset (apexSet_subset orig S hu)
      have hsupp : ∀ s, s ∉ σ.erase a → l s = 0 := by
        intro s hs
        by_cases hsa : s = a
        · rw [hsa]; exact hla
        · exact hls s fun hc ↦ hs (Finset.mem_erase.mpr ⟨hsa, hc⟩)
      exact ih _ hlt hmem l hsupp hl

/-! ### Uniqueness of the barycentric weights -/

/-- The side of the apex on which a weight function lives, together with the
value of its coordinate vector at the corresponding join vertex. -/
theorem exists_apex_side (orig : W → V) {S : Finset W} (hS : S.Nonempty)
    {ρ : Finset (Finset W)} (hρ : ρ ∈ sdFaces orig S) {c : Finset W → ℝ}
    (hc : ∀ s, s ∉ ρ → c s = 0) :
    ∃ u ∈ apexSet orig S,
      ρ.erase (apexSet orig S) ∈ sdFaces orig (S.erase u) ∧
      (∀ s, s ≠ apexSet orig S → c s ≠ 0 → u ∉ s) ∧
      coeffPoint c u = c (apexSet orig S) * ((apexSet orig S).card : ℝ)⁻¹ := by
  obtain ⟨u, hu, hmem⟩ := exists_erase_apex_mem hS hρ
  refine ⟨u, hu, hmem, ?_, ?_⟩
  · intro s hsa hs0 hus
    have hsρ : s ∈ ρ := by
      by_contra hcon
      exact hs0 (hc s hcon)
    have hsub := (sdFaces_vertex orig _ hmem s (Finset.mem_erase.mpr ⟨hsa, hsρ⟩)).2.1
    exact (Finset.mem_erase.mp (hsub hus)).1 rfl
  · unfold coeffPoint
    rw [Finset.sum_eq_single (apexSet orig S)]
    · rw [coordVec_of_mem hu]
    · intro s _ hsa
      by_cases hs0 : c s = 0
      · rw [hs0, zero_mul]
      · have hus : u ∉ s := by
          intro hus
          have hsρ : s ∈ ρ := by
            by_contra hcon
            exact hs0 (hc s hcon)
          have hsub := (sdFaces_vertex orig _ hmem s (Finset.mem_erase.mpr ⟨hsa, hsρ⟩)).2.1
          exact (Finset.mem_erase.mp (hsub hus)).1 rfl
        rw [coordVec_eq_zero hus, mul_zero]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon

/-- **Uniqueness of barycentric weights on the subdivision.**  If two
nonnegative weight functions supported on simplices of the subdivision of `S`
define the same coordinate vector, they are equal.  In particular a point of the
subdivision determines its weights, so two simplices meet exactly in their
common face. -/
theorem coeffPoint_injective (orig : W → V) (S : Finset W) :
    ∀ {σ τ : Finset (Finset W)} {l n : Finset W → ℝ},
      σ ∈ sdFaces orig S → τ ∈ sdFaces orig S →
      (∀ s, 0 ≤ l s) → (∀ s, 0 ≤ n s) →
      (∀ s, s ∉ σ → l s = 0) → (∀ s, s ∉ τ → n s = 0) →
      coeffPoint l = coeffPoint n → l = n := by
  induction S using Finset.strongInduction with
  | _ S ih =>
    intro σ τ l n hσ hτ hl0 hn0 hls hns heq
    rcases S.eq_empty_or_nonempty with rfl | hS
    · rw [sdFaces_empty, Finset.mem_singleton] at hσ hτ
      subst hσ; subst hτ
      funext s
      rw [hls s (Finset.notMem_empty s), hns s (Finset.notMem_empty s)]
    · set a := apexSet orig S with ha
      have hane : a.Nonempty := apexSet_nonempty hS
      have hacard : (0 : ℝ) < (a.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr hane
      obtain ⟨u, hu, hmemσ, hlno, hlu⟩ := exists_apex_side orig hS hσ hls
      obtain ⟨u', hu', hmemτ, hnno, hnu'⟩ := exists_apex_side orig hS hτ hns
      -- the coordinate at `u'` seen from the `l` side
      have hsplit : ∀ (c : Finset W → ℝ) (w : W),
          coeffPoint c w = c a * coordVec a w +
            ∑ s ∈ Finset.univ.erase a, c s * coordVec s w := by
        intro c w
        unfold coeffPoint
        rw [← Finset.add_sum_erase _ (fun s ↦ c s * coordVec s w) (Finset.mem_univ a)]
      have hRl : 0 ≤ ∑ s ∈ Finset.univ.erase a, l s * coordVec s u' :=
        Finset.sum_nonneg fun s _ ↦ mul_nonneg (hl0 s) (coordVec_nonneg s u')
      have hRn : 0 ≤ ∑ s ∈ Finset.univ.erase a, n s * coordVec s u :=
        Finset.sum_nonneg fun s _ ↦ mul_nonneg (hn0 s) (coordVec_nonneg s u)
      have hcoordau : coordVec a u = (a.card : ℝ)⁻¹ := coordVec_of_mem hu
      have hcoordau' : coordVec a u' = (a.card : ℝ)⁻¹ := coordVec_of_mem hu'
      have hxu : coeffPoint l u = l a * (a.card : ℝ)⁻¹ := hlu
      have hxu' : coeffPoint n u' = n a * (a.card : ℝ)⁻¹ := hnu'
      have hlu' : coeffPoint l u' = l a * (a.card : ℝ)⁻¹ +
          ∑ s ∈ Finset.univ.erase a, l s * coordVec s u' := by
        rw [hsplit l u', hcoordau']
      have hnu : coeffPoint n u = n a * (a.card : ℝ)⁻¹ +
          ∑ s ∈ Finset.univ.erase a, n s * coordVec s u := by
        rw [hsplit n u, hcoordau]
      have h1 : coeffPoint l u = coeffPoint n u := by rw [heq]
      have h2 : coeffPoint l u' = coeffPoint n u' := by rw [heq]
      -- both apex coefficients are equal and the residual sums vanish
      have hlan : l a * (a.card : ℝ)⁻¹ = n a * (a.card : ℝ)⁻¹ := by
        have hle1 : l a * (a.card : ℝ)⁻¹ ≤ n a * (a.card : ℝ)⁻¹ := by
          rw [← hxu, h1, hnu]
          linarith
        have hle2 : n a * (a.card : ℝ)⁻¹ ≤ l a * (a.card : ℝ)⁻¹ := by
          rw [← hxu', ← h2, hlu']
          linarith
        linarith
      have hla : l a = n a :=
        mul_right_cancel₀ (inv_ne_zero (ne_of_gt hacard)) hlan
      have hRl0 : ∑ s ∈ Finset.univ.erase a, l s * coordVec s u' = 0 := by
        have := hlu'
        rw [h2, hxu', ← hlan] at this
        linarith
      have hRn0 : ∑ s ∈ Finset.univ.erase a, n s * coordVec s u = 0 := by
        have := hnu
        rw [← h1, hxu, hlan] at this
        linarith
      have hlzero : ∀ s, s ≠ a → u' ∈ s → l s = 0 := by
        intro s hsa hus
        have hmem : s ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hsa, Finset.mem_univ s⟩
        have hterm : l s * coordVec s u' = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun t _ ↦ mul_nonneg (hl0 t) (coordVec_nonneg t u'))).mp hRl0 s hmem
        rcases mul_eq_zero.mp hterm with h | h
        · exact h
        · exact absurd h (ne_of_gt (coordVec_pos hus))
      have hnzero : ∀ s, s ≠ a → u ∈ s → n s = 0 := by
        intro s hsa hus
        have hmem : s ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨hsa, Finset.mem_univ s⟩
        have hterm : n s * coordVec s u = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg
            (fun t _ ↦ mul_nonneg (hn0 t) (coordVec_nonneg t u))).mp hRn0 s hmem
        rcases mul_eq_zero.mp hterm with h | h
        · exact h
        · exact absurd h (ne_of_gt (coordVec_pos hus))
      -- pass to the subdivision of `S.erase u`
      have hlt : S.erase u ⊂ S := Finset.erase_ssubset (apexSet_subset orig S hu)
      set σ' := (σ.erase a).filter (fun s ↦ u' ∉ s) with hσ'
      set τ' := (τ.erase a).filter (fun s ↦ u ∉ s) with hτ'
      have hσ'mem : σ' ∈ sdFaces orig (S.erase u) :=
        sdFaces_faceClosed orig _ hmemσ (Finset.filter_subset _ _)
      have hτ'mem : τ' ∈ sdFaces orig (S.erase u) := by
        have h1 : τ' ∈ sdFaces orig (S.erase u') :=
          sdFaces_faceClosed orig _ hmemτ (Finset.filter_subset _ _)
        have h2 : τ' ∈ sdFaces orig ((S.erase u').erase u) :=
          mem_sdFaces_erase_of_avoid h1 fun s hs ↦ (Finset.mem_filter.mp hs).2
        exact sdFaces_mono orig
          (by rw [Finset.erase_right_comm]; exact Finset.erase_subset _ _) h2
      have hl'supp : ∀ s, s ∉ σ' → Function.update l a 0 s = 0 := by
        intro s hs
        by_cases hsa : s = a
        · rw [hsa, Function.update_self]
        · rw [Function.update_of_ne hsa]
          by_cases hu's : u' ∈ s
          · exact hlzero s hsa hu's
          · refine hls s fun hcon ↦ hs ?_
            rw [hσ']
            exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hsa, hcon⟩, hu's⟩
      have hn'supp : ∀ s, s ∉ τ' → Function.update n a 0 s = 0 := by
        intro s hs
        by_cases hsa : s = a
        · rw [hsa, Function.update_self]
        · rw [Function.update_of_ne hsa]
          by_cases hus : u ∈ s
          · exact hnzero s hsa hus
          · refine hns s fun hcon ↦ hs ?_
            rw [hτ']
            exact Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨hsa, hcon⟩, hus⟩
      have hupdate : Function.update l a 0 = Function.update n a 0 := by
        refine ih _ hlt hσ'mem hτ'mem ?_ ?_ hl'supp hn'supp ?_
        · intro s
          by_cases hsa : s = a
          · rw [hsa, Function.update_self]
          · rw [Function.update_of_ne hsa]; exact hl0 s
        · intro s
          by_cases hsa : s = a
          · rw [hsa, Function.update_self]
          · rw [Function.update_of_ne hsa]; exact hn0 s
        · funext w
          rw [coeffPoint_erase, coeffPoint_erase, heq, hla]
      funext s
      by_cases hsa : s = a
      · rw [hsa]; exact hla
      · have := congrFun hupdate s
        rwa [Function.update_of_ne hsa, Function.update_of_ne hsa] at this

end BadEdge
end AffineTverberg
