import AffineTverberg.StarBoundaryCycle
import AffineTverberg.SphereFundamentalCycle

set_option linter.style.header false

/-!
# Local orientation cycles obtained from one global cycle

Restrict a global real cycle to simplices containing a face L. Its boundary
is supported on the existing starBoundaryFamily K L. At F.erase u, where
F contains L and u belongs to L, the coefficient is precisely the oriented
incidence sign times the coefficient of F in the global cycle. Thus a
full-support global fundamental cycle produces nonzero local orientation
cycles simultaneously for every nonempty face.

These are actual coefficient functions and boundaries, not independently
chosen nonzero homology classes. The earlier mod-two boundary-detection proof
is left unchanged.
-/

noncomputable section

namespace AffineTverberg.Simplicial

variable {V : Type} [LinearOrder V]

/-- Restrict a chain to the simplices containing the given face. -/
def cofaceRestriction (L : Finset V) : (Finset V → ℝ) →ₗ[ℝ] (Finset V → ℝ) where
  toFun c s := if L ⊆ s then c s else 0
  map_add' c d := by
    funext s
    by_cases h : L ⊆ s <;> simp [h]
  map_smul' a c := by
    funext s
    by_cases h : L ⊆ s <;> simp [h]

@[simp]
theorem cofaceRestriction_apply (L : Finset V) (c : Finset V → ℝ) (s : Finset V) :
    cofaceRestriction L c s = if L ⊆ s then c s else 0 := rfl

/-- Restriction choices are compatible on nested faces, in fact on arbitrary unions. -/
theorem cofaceRestriction_cofaceRestriction (L M : Finset V) (c : Finset V → ℝ) :
    cofaceRestriction M (cofaceRestriction L c) = cofaceRestriction (L ∪ M) c := by
  funext s
  by_cases hL : L ⊆ s <;> by_cases hM : M ⊆ s <;>
    simp [cofaceRestriction_apply, Finset.union_subset_iff, hL, hM]

theorem cofaceRestriction_mem_chains {K : Finset (Finset V)} {N : ℕ}
    {c : Finset V → ℝ} (hc : c ∈ chains ℝ K N) (L : Finset V) :
    cofaceRestriction L c ∈ chains ℝ K N := by
  intro s hs
  by_cases hLs : L ⊆ s
  · apply hc s
    simpa only [cofaceRestriction_apply, hLs, ite_true] using hs
  · simp only [cofaceRestriction_apply, hLs, ite_false, ne_eq, not_true_eq_false] at hs

variable [Fintype V]

/-- On a coface of L, restriction does not change the boundary coefficient. -/
theorem boundary_cofaceRestriction_of_subset {L s : Finset V} (hLs : L ⊆ s)
    (c : Finset V → ℝ) :
    boundary ℝ V (cofaceRestriction L c) s = boundary ℝ V c s := by
  simp only [boundary_apply]
  apply Finset.sum_congr rfl
  intro v _
  simp only [cofaceRestriction_apply, hLs.trans (Finset.subset_insert v s), ite_true]

/-- The boundary of the restricted global cycle lies on the actual closed-star boundary. -/
theorem boundary_cofaceRestriction_mem_cycles {K : Finset (Finset V)}
    (hK : FaceClosed K) {N : ℕ} {c : Finset V → ℝ}
    (hc : c ∈ cycles ℝ K (N + 1)) (L : Finset V) :
    boundary ℝ V (cofaceRestriction L c) ∈ cycles ℝ (starBoundaryFamily K L) N := by
  refine ⟨?_, boundary_boundary_apply _⟩
  intro s hs
  have hs' := hs
  rw [boundary_apply] at hs'
  obtain ⟨v, hv, hterm⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs'
  have hres : cofaceRestriction L c (insert v s) ≠ 0 :=
    fun h => hterm (by rw [h, mul_zero])
  have hL : L ⊆ insert v s := by
    by_contra h
    exact hres (by simp only [cofaceRestriction_apply, h, ite_false])
  have hcv : c (insert v s) ≠ 0 := by
    simpa only [cofaceRestriction_apply, hL, ite_true] using hres
  obtain ⟨hvsK, hvscard⟩ := hc.1 (insert v s) hcv
  have hvs : v ∉ s := by simpa using hv
  have hsK := hK _ hvsK s (Finset.subset_insert _ _)
  have hsL := hK _ hvsK (s ∪ L) (Finset.union_subset (Finset.subset_insert _ _) hL)
  have hnot : ¬ L ⊆ s := by
    intro hLs
    exact hs ((boundary_cofaceRestriction_of_subset hLs c).trans (congrFun hc.2 s))
  refine ⟨mem_starBoundaryFamily.mpr ⟨hsK, hsL, hnot⟩, ?_⟩
  rw [Finset.card_insert_of_notMem hvs] at hvscard
  omega

/-- An explicit coefficient of the local cycle is the global coefficient
times its incidence sign. -/
theorem boundary_cofaceRestriction_erase {L F : Finset V} (hLF : L ⊆ F)
    {u : V} (hu : u ∈ L) (c : Finset V → ℝ) :
    boundary ℝ V (cofaceRestriction L c) (F.erase u) =
      orientedSign ℝ (F.erase u) u * c F := by
  rw [boundary_apply, Finset.sum_eq_single u]
  · rw [Finset.insert_erase (hLF hu)]
    simp only [cofaceRestriction_apply, hLF, ite_true]
  · intro v _ hvu
    have hnot : ¬ L ⊆ insert v (F.erase u) := by
      intro h
      rcases Finset.mem_insert.mp (h hu) with huv | huerase
      · exact hvu huv.symm
      · exact Finset.notMem_erase u F huerase
    simp only [cofaceRestriction_apply, hnot, ite_false, mul_zero]
  · intro hu'
    exact (hu' (by simp)).elim

/-- A nonzero global coefficient on one coface gives a nonzero local boundary cycle. -/
theorem boundary_cofaceRestriction_ne_zero {L F : Finset V} (hLF : L ⊆ F)
    (hL : L.Nonempty) {c : Finset V → ℝ} (hF : c F ≠ 0) :
    boundary ℝ V (cofaceRestriction L c) ≠ 0 := by
  obtain ⟨u, hu⟩ := hL
  intro hzero
  have hcoeff := congrFun hzero (F.erase u)
  rw [boundary_cofaceRestriction_erase hLF hu] at hcoeff
  exact mul_ne_zero (orientedSign_ne_zero _ _) hF hcoeff

/-- In top degree the local cycle is not a boundary, by the actual dimension bound. -/
theorem boundary_cofaceRestriction_notMem_boundaries {K : Finset (Finset V)} {N : ℕ}
    (htop : ∀ s ∈ K, s.card ≤ N + 1) {L F : Finset V} (hLF : L ⊆ F)
    (hL : L.Nonempty) {c : Finset V → ℝ} (hF : c F ≠ 0) :
    boundary ℝ V (cofaceRestriction L c) ∉ boundaries ℝ (starBoundaryFamily K L) N := by
  rw [boundaries_top_eq_bot (fun s hs => by
    simpa using (card_le_starBoundaryFamily htop hs)), Submodule.mem_bot]
  exact boundary_cofaceRestriction_ne_zero hLF hL hF

/-- This supplies a specific nonzero local homology cycle, not an acyclicity premise. -/
theorem not_isReducedAcyclicAt_starBoundaryFamily_of_cycle
    {K : Finset (Finset V)} (hK : FaceClosed K) {N : ℕ}
    (htop : ∀ s ∈ K, s.card ≤ N + 1) {c : Finset V → ℝ}
    (hc : c ∈ cycles ℝ K (N + 1)) {L F : Finset V}
    (hLF : L ⊆ F) (hL : L.Nonempty) (hF : c F ≠ 0) :
    ¬ IsReducedAcyclicAt ℝ (starBoundaryFamily K L) N := by
  intro hacyc
  exact boundary_cofaceRestriction_notMem_boundaries htop hLF hL hF
    (hacyc (boundary_cofaceRestriction_mem_cycles hK hc L))

end AffineTverberg.Simplicial
