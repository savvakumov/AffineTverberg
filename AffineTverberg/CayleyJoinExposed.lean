import AffineTverberg.CayleyJoinFaces

set_option linter.style.header false

/-!
# The Cayley join of exposed faces is an exposed face

`CayleyJoinFaces.lean` classifies the exposed faces of a Cayley join: they are
Cayley joins of exposed faces of the factors.  Here we prove the converse
direction, which is what identifies the carriers of the combinatorial face
family with genuine faces of the join:

* `isExposed_cayleyJoin` — if `Gs i` is an exposed face of `Fs i` for every `i`,
  then `cayleyJoin Gs` is an exposed face of `cayleyJoin Fs`.  Empty factors are
  allowed and are exposed by the homogenizing coordinate.
* `cayleyJoin_inter` — the Cayley join commutes with intersections.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg
namespace CayleyJoin

open PolytopeFace

variable {n m : ℕ}

/-- The continuous linear functional `z ↦ ∑ i, (l i (z i).1 - c i * (z i).2)` on
the ambient space of the Cayley join. -/
def joinFunctional (l : Fin (m + 1) → (CoordinateSpace n →L[ℝ] ℝ)) (c : Fin (m + 1) → ℝ) :
    PolytopalJoinAmbient n m →L[ℝ] ℝ :=
  ∑ i, ((l i).comp ((ContinuousLinearMap.fst ℝ (CoordinateSpace n) ℝ).comp
      (ContinuousLinearMap.proj i))
    - (c i) • ((ContinuousLinearMap.snd ℝ (CoordinateSpace n) ℝ).comp
      (ContinuousLinearMap.proj i)))

theorem joinFunctional_apply (l : Fin (m + 1) → (CoordinateSpace n →L[ℝ] ℝ))
    (c : Fin (m + 1) → ℝ) (z : PolytopalJoinAmbient n m) :
    joinFunctional l c z = ∑ i, (l i (z i).1 - c i * (z i).2) := by
  simp [joinFunctional]

/-- **The Cayley join of exposed faces is an exposed face of the Cayley join.** -/
theorem isExposed_cayleyJoin {Fs Gs : Fin (m + 1) → Set (CoordinateSpace n)}
    (h : ∀ i, IsExposed ℝ (Fs i) (Gs i)) :
    IsExposed ℝ (cayleyJoin Fs) (cayleyJoin Gs) := by
  classical
  intro hne
  -- factorwise data
  have hchoice : ∀ i, ∃ p : (CoordinateSpace n →L[ℝ] ℝ) × ℝ,
      (∀ x ∈ Fs i, p.1 x - p.2 ≤ 0) ∧ (∀ x ∈ Fs i, (p.1 x - p.2 = 0 ↔ x ∈ Gs i)) := by
    intro i
    rcases (Gs i).eq_empty_or_nonempty with he | hgne
    · refine ⟨(0, 1), fun x _ ↦ by norm_num, fun x _ ↦ ?_⟩
      simp only [zero_apply, zero_sub, he]
      constructor
      · intro hcon; norm_num at hcon
      · intro hcon; exact absurd hcon (by simp)
    · obtain ⟨l, hl⟩ := h i hgne
      obtain ⟨p₀, hp₀⟩ := hgne
      have hp₀' : p₀ ∈ Fs i ∧ ∀ y ∈ Fs i, l y ≤ l p₀ := by rw [hl] at hp₀; exact hp₀
      refine ⟨(l, l p₀), fun x hx ↦ by simpa using sub_nonpos.mpr (hp₀'.2 x hx),
        fun x hx ↦ ?_⟩
      simp only
      constructor
      · intro hzero
        have hxeq : l x = l p₀ := by linarith [hzero]
        rw [hl]
        exact ⟨hx, fun y hy ↦ by rw [hxeq]; exact hp₀'.2 y hy⟩
      · intro hxG
        rw [hl] at hxG
        have h1 : l p₀ ≤ l x := hxG.2 p₀ hp₀'.1
        have h2 : l x ≤ l p₀ := hp₀'.2 x hx
        linarith
  choose data hle heq using hchoice
  set L := joinFunctional (fun i ↦ (data i).1) (fun i ↦ (data i).2) with hL
  have hLapply : ∀ z : PolytopalJoinAmbient n m,
      L z = ∑ i, ((data i).1 (z i).1 - (data i).2 * (z i).2) := by
    intro z
    rw [hL, joinFunctional_apply]
  -- the value of `L` on the join
  have hterm : ∀ z ∈ cayleyJoin Fs, ∀ i,
      (data i).1 (z i).1 - (data i).2 * (z i).2 ≤ 0 := by
    intro z hz i
    rcases eq_or_lt_of_le (hz.1 i).1 with h0 | hpos
    · have hz1 : (z i).1 = 0 := (hz.1 i).2.1 h0.symm
      rw [hz1, ← h0]
      simp
    · have hx : (z i).2⁻¹ • (z i).1 ∈ Fs i := (hz.1 i).2.2 hpos
      have hkey : (data i).1 (z i).1
          = (z i).2 * (data i).1 ((z i).2⁻¹ • (z i).1) := by
        conv_lhs => rw [show (z i).1 = (z i).2 • ((z i).2⁻¹ • (z i).1) by
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]]
        rw [map_smul, smul_eq_mul]
      rw [hkey]
      nlinarith [hle i _ hx, hpos]
  have hzero_iff : ∀ z ∈ cayleyJoin Fs, ∀ i,
      ((data i).1 (z i).1 - (data i).2 * (z i).2 = 0 ↔ (z i) ∈ homogenizedCone (Gs i)) := by
    intro z hz i
    rcases eq_or_lt_of_le (hz.1 i).1 with h0 | hpos
    · have hz1 : (z i).1 = 0 := (hz.1 i).2.1 h0.symm
      constructor
      · intro _
        refine ⟨le_of_eq h0, fun _ ↦ hz1, fun hcon ↦ absurd hcon ?_⟩
        rw [← h0]; exact lt_irrefl 0
      · intro _
        rw [hz1, ← h0]
        simp
    · have hx : (z i).2⁻¹ • (z i).1 ∈ Fs i := (hz.1 i).2.2 hpos
      have hkey : (data i).1 (z i).1
          = (z i).2 * (data i).1 ((z i).2⁻¹ • (z i).1) := by
        conv_lhs => rw [show (z i).1 = (z i).2 • ((z i).2⁻¹ • (z i).1) by
          rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hpos), one_smul]]
        rw [map_smul, smul_eq_mul]
      rw [hkey]
      constructor
      · intro hzz
        refine ⟨le_of_lt hpos, fun hcon ↦ absurd hcon (ne_of_gt hpos), fun _ ↦ ?_⟩
        refine (heq i _ hx).mp ?_
        have hfac : (z i).2 * ((data i).1 ((z i).2⁻¹ • (z i).1) - (data i).2) = 0 := by
          nlinarith [hzz]
        rcases mul_eq_zero.mp hfac with h' | h'
        · exact absurd h' (ne_of_gt hpos)
        · exact h'
      · intro hmem
        have hG : (z i).2⁻¹ • (z i).1 ∈ Gs i := hmem.2.2 hpos
        nlinarith [(heq i _ hx).mpr hG]
  have hLle : ∀ z ∈ cayleyJoin Fs, L z ≤ 0 := by
    intro z hz
    rw [hLapply]
    exact Finset.sum_nonpos fun i _ ↦ hterm z hz i
  have hLzero : ∀ z ∈ cayleyJoin Fs, (L z = 0 ↔ z ∈ cayleyJoin Gs) := by
    intro z hz
    rw [hLapply]
    constructor
    · intro hsum
      refine ⟨fun i ↦ (hzero_iff z hz i).mp ?_, hz.2⟩
      by_contra hcon
      have hlt : (data i).1 (z i).1 - (data i).2 * (z i).2 < 0 :=
        lt_of_le_of_ne (hterm z hz i) hcon
      have hsum' : ∑ j, ((data j).1 (z j).1 - (data j).2 * (z j).2)
          < ∑ _j : Fin (m + 1), (0 : ℝ) :=
        Finset.sum_lt_sum (fun j _ ↦ hterm z hz j) ⟨i, Finset.mem_univ i, hlt⟩
      rw [Finset.sum_const_zero] at hsum'
      exact absurd hsum (ne_of_lt hsum')
    · intro hzG
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      exact (hzero_iff z hz i).mpr (hzG.1 i)
  obtain ⟨z₀, hz₀⟩ := hne
  have hz₀F : z₀ ∈ cayleyJoin Fs :=
    cayleyJoin_mono (fun i ↦ (h i).subset) hz₀
  refine ⟨L, ?_⟩
  ext z
  constructor
  · intro hzG
    have hzF : z ∈ cayleyJoin Fs := cayleyJoin_mono (fun i ↦ (h i).subset) hzG
    refine ⟨hzF, fun y hy ↦ ?_⟩
    rw [(hLzero z hzF).mpr hzG]
    exact hLle y hy
  · rintro ⟨hzF, hzmax⟩
    have h0 : L z₀ = 0 := (hLzero z₀ hz₀F).mpr hz₀
    have : (0 : ℝ) ≤ L z := by rw [← h0]; exact hzmax z₀ hz₀F
    exact (hLzero z hzF).mp (le_antisymm (hLle z hzF) this)

/-- The Cayley join commutes with intersections of the factors. -/
theorem cayleyJoin_inter (Fs Gs : Fin (m + 1) → Set (CoordinateSpace n)) :
    cayleyJoin (fun i ↦ Fs i ∩ Gs i) = cayleyJoin Fs ∩ cayleyJoin Gs := by
  ext z
  constructor
  · intro hz
    exact ⟨⟨fun i ↦ homogenizedCone_mono inter_subset_left (hz.1 i), hz.2⟩,
      ⟨fun i ↦ homogenizedCone_mono inter_subset_right (hz.1 i), hz.2⟩⟩
  · rintro ⟨hzF, hzG⟩
    refine ⟨fun i ↦ ⟨(hzF.1 i).1, (hzF.1 i).2.1, fun hpos ↦ ⟨(hzF.1 i).2.2 hpos,
      (hzG.1 i).2.2 hpos⟩⟩, hzF.2⟩

end CayleyJoin
end AffineTverberg
