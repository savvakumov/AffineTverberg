import AffineTverberg.BarycentricSubdivision

set_option linter.style.header false

/-!
# Affine independence of the barycenters of a chain

The barycenters of a chain of faces of a geometrically realized complex are
affinely independent.  The proof is the standard staircase argument: the
largest member of the chain carrying a nonzero coefficient owns a vertex which
no smaller member of the chain contains, and the coordinate of that vertex sees
only that one coefficient.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg.Simplicial

variable {V : Type*} [Fintype V] [DecidableEq V]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype V] [DecidableEq V] in
/-- Inside a chain, every member owns a vertex avoided by all strictly smaller
members. -/
theorem IsFaceChain.exists_private_vertex {C : Finset (Finset V)} (hC : IsFaceChain C)
    {t₀ : Finset V} (ht₀ : t₀ ∈ C) :
    ∃ v ∈ t₀, ∀ t ∈ C, t ⊂ t₀ → v ∉ t := by
  classical
  by_cases hB : (C.filter fun t ↦ t ⊂ t₀).Nonempty
  · obtain ⟨t₁, ht₁, hmax⟩ := (hC.mono (Finset.filter_subset _ _)).exists_max hB
    have ht₁lt : t₁ ⊂ t₀ := (Finset.mem_filter.mp ht₁).2
    obtain ⟨v, hvt₀, hvt₁⟩ := Finset.exists_of_ssubset ht₁lt
    exact ⟨v, hvt₀, fun t ht htlt hvt ↦
      hvt₁ (hmax t (Finset.mem_filter.mpr ⟨ht, htlt⟩) hvt)⟩
  · obtain ⟨v, hv⟩ := hC.1 t₀ ht₀
    refine ⟨v, hv, fun t ht htlt _ ↦ ?_⟩
    exact hB ⟨t, Finset.mem_filter.mpr ⟨ht, htlt⟩⟩

omit [Fintype V] in
/-- The barycenter of a face expanded in the coordinates of a larger face. -/
theorem faceBarycenter_eq_sum (p : V → E) {t T : Finset V} (htT : t ⊆ T) :
    faceBarycenter p t = ∑ v ∈ T, uniformCoord t v • p v := by
  rw [faceBarycenter, Finset.smul_sum]
  rw [← Finset.sum_subset htT (fun v _ hv ↦ by rw [uniformCoord_eq_zero hv, zero_smul])]
  exact Finset.sum_congr rfl fun v hv ↦ by rw [uniformCoord, ite_eq_left hv]

omit [Fintype V] in
/-- The staircase lemma: an affine dependence among the barycenters of a chain
of faces has all coefficients zero. -/
theorem eq_zero_of_sum_faceBarycenter_eq_zero {K : Finset (Finset V)} {p : V → E}
    (hgeom : IsGeometricRealization K p) {D : Finset (Finset V)} (hDK : D ⊆ K)
    (hD : IsFaceChain D) {W : Finset V → ℝ} (hsum : ∑ t ∈ D, W t = 0)
    (hcomb : ∑ t ∈ D, W t • faceBarycenter p t = 0) : ∀ t ∈ D, W t = 0 := by
  classical
  rcases Finset.eq_empty_or_nonempty D with rfl | hDne
  · simp
  obtain ⟨T, hTD, hTmax⟩ := hD.exists_max hDne
  have hTK : T ∈ K := hDK hTD
  set g : V → ℝ := fun v ↦ ∑ t ∈ D, W t * uniformCoord t v with hg
  -- the coefficients of the dependence in the coordinates of `T`
  have hgsum : ∑ v ∈ T, g v = 0 := by
    have hswap : ∑ v ∈ T, g v = ∑ t ∈ D, ∑ v ∈ T, W t * uniformCoord t v := by
      rw [hg]; exact Finset.sum_comm
    rw [hswap, ← hsum]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [← Finset.mul_sum, sum_uniformCoord_subset (hTmax t ht) (hD.1 t ht), mul_one]
  have hgcomb : ∑ v ∈ T, g v • p v = 0 := by
    have hswap : ∑ v ∈ T, g v • p v
        = ∑ t ∈ D, ∑ v ∈ T, (W t * uniformCoord t v) • p v := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v _ ↦ ?_
      rw [hg, Finset.sum_smul]
    rw [hswap, ← hcomb]
    refine Finset.sum_congr rfl fun t ht ↦ ?_
    rw [faceBarycenter_eq_sum p (hTmax t ht), Finset.smul_sum]
    exact Finset.sum_congr rfl fun v _ ↦ by rw [smul_smul]
  have hgzero : ∀ v ∈ T, g v = 0 := by
    have hind := hgeom.independent T hTK
    have := affineIndependent_iff.mp hind Finset.univ (fun v : T ↦ g v.val) ?_ ?_
    · intro v hv
      exact this ⟨v, hv⟩ (Finset.mem_univ _)
    · rw [Finset.sum_coe_sort T g]; exact hgsum
    · rw [← hgcomb]
      exact (Finset.sum_coe_sort T (fun v ↦ g v • p v))
  -- the staircase argument
  by_contra hcon
  push Not at hcon
  obtain ⟨t', ht'D, ht'⟩ := hcon
  have hSne : (D.filter fun t ↦ W t ≠ 0).Nonempty := ⟨t', Finset.mem_filter.mpr ⟨ht'D, ht'⟩⟩
  obtain ⟨t₀, ht₀, hmax⟩ := (hD.mono (Finset.filter_subset _ _)).exists_max hSne
  have ht₀D : t₀ ∈ D := (Finset.mem_filter.mp ht₀).1
  have hW₀ : W t₀ ≠ 0 := (Finset.mem_filter.mp ht₀).2
  obtain ⟨v, hvt₀, hvpriv⟩ := hD.exists_private_vertex ht₀D
  have hgv : g v = W t₀ * uniformCoord t₀ v := by
    rw [hg]
    refine Finset.sum_eq_single t₀ (fun t ht hne ↦ ?_) (fun h ↦ absurd ht₀D h)
    by_cases hvt : v ∈ t
    · -- `t` is comparable with `t₀`, and cannot be strictly smaller
      have hnotlt : ¬ t ⊂ t₀ := fun hlt ↦ hvpriv t ht hlt hvt
      have hsubset : t₀ ⊆ t := by
        rcases hD.2 t ht t₀ ht₀D with h | h
        · exact absurd (lt_of_le_of_ne h hne) hnotlt
        · exact h
      have hWt : W t = 0 := by
        by_contra hWt
        have : t ⊆ t₀ := hmax t (Finset.mem_filter.mpr ⟨ht, hWt⟩)
        exact hne (Finset.Subset.antisymm this hsubset)
      rw [hWt, zero_mul]
    · rw [uniformCoord_eq_zero hvt, mul_zero]
  have := hgzero v (hTmax t₀ ht₀D hvt₀)
  rw [hgv] at this
  exact absurd this (mul_ne_zero hW₀ (ne_of_gt (uniformCoord_pos hvt₀)))

omit [Fintype V] in
/-- The barycenters of a chain of faces are affinely independent. -/
theorem affineIndependent_faceBarycenter {K : Finset (Finset V)} {p : V → E}
    (hgeom : IsGeometricRealization K p) {C : Finset (Finset V)}
    (hCK : C ⊆ K) (hC : IsFaceChain C) :
    AffineIndependent ℝ (fun t : C ↦ faceBarycenter p t.val) := by
  classical
  rw [affineIndependent_iff]
  intro s w hsum hcomb e he
  set W : Finset V → ℝ := fun t ↦ if ht : t ∈ C then (if (⟨t, ht⟩ : C) ∈ s then w ⟨t, ht⟩ else 0)
    else 0 with hW
  have hWval : ∀ e : C, e ∈ s → W e.val = w e := by
    intro e hes
    rw [hW]
    simp only [e.property, dite_eq_left]
    rw [ite_eq_left (by simpa using hes)]
  have hinj : ∀ x ∈ s, ∀ y ∈ s, (x : Finset V) = y → x = y :=
    fun x _ y _ h ↦ Subtype.ext h
  set D : Finset (Finset V) := s.image Subtype.val with hD
  have hDC : D ⊆ C := by
    intro t ht
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp ht
    exact e.property
  have hsumD : ∑ t ∈ D, W t = 0 := by
    rw [hD, Finset.sum_image hinj, ← hsum]
    exact Finset.sum_congr rfl fun e he ↦ hWval e he
  have hcombD : ∑ t ∈ D, W t • faceBarycenter p t = 0 := by
    rw [hD, Finset.sum_image hinj, ← hcomb]
    exact Finset.sum_congr rfl fun e he ↦ by rw [hWval e he]
  have := eq_zero_of_sum_faceBarycenter_eq_zero hgeom (hDC.trans hCK) (hC.mono hDC)
    hsumD hcombD e.val (Finset.mem_image.mpr ⟨e, he, rfl⟩)
  rwa [hWval e he] at this

end AffineTverberg.Simplicial

end
