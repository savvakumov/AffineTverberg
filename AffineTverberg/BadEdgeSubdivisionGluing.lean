import AffineTverberg.BadEdgeSubdivisionRetraction

set_option linter.style.header false

/-!
# Gluing the bad-edge subdivisions of different join faces

The subdivisions of the individual join faces are compatible combinatorially
(`sdFaces_mono`).  This file proves the *geometric* compatibility needed to see
the assembled subdivision of the whole join complex as a geometric simplicial
complex: two simplices coming from two different join faces meet in a common
face.

The argument has three steps.

* `joinCellCarrier_inter_subset` : two join cells meet inside the join cell of
  their factorwise intersection.  The factor weights and the factor points of a
  point of a join cell are determined by the point.
* `mem_sdFaces_of_subset` : a simplex of the subdivision of `S` all of whose
  vertices lie in a subface `R` is a simplex of the subdivision of `R`.
* `sdRealize_inter_joinCell` : the part of a simplex of the subdivision of `S`
  lying in the cell of a subface `R` is the realization of the subsimplex on
  the vertices contained in `R`.  This uses uniqueness of the barycentric
  weights on the join face.
-/

noncomputable section

open scoped BigOperators
open Set

namespace AffineTverberg
namespace BadEdge

/-! ### Intersections of join cells -/

section JoinCells

variable {e m : ℕ}

/-- **Two join cells meet inside the cell of their factorwise intersection**,
provided the component faces intersect properly in each factor. -/
theorem joinCellCarrier_inter_subset (f g : Fin (m + 1) → Finset (CoordinateSpace e))
    (hfg : ∀ i, convexHull ℝ (f i : Set (CoordinateSpace e)) ∩
        convexHull ℝ (g i : Set (CoordinateSpace e)) ⊆
      convexHull ℝ (((f i ∩ g i : Finset (CoordinateSpace e)) : Set (CoordinateSpace e)))) :
    joinCellCarrier f ∩ joinCellCarrier g ⊆ joinCellCarrier fun i ↦ f i ∩ g i := by
  classical
  rintro z ⟨hzf, hzg⟩
  obtain ⟨t, x, ht0, ht1, hx, hzx⟩ := exists_repr_of_mem_joinCellCarrier hzf
  obtain ⟨t', x', ht0', ht1', hx', hzx'⟩ := exists_repr_of_mem_joinCellCarrier hzg
  have hcoord : ∀ j, (t j • x j, t j) = (t' j • x' j, t' j) := by
    intro j
    have h1 : z j = (t j • x j, t j) := by rw [hzx]; exact sum_smul_copy_apply t x j
    have h2 : z j = (t' j • x' j, t' j) := by rw [hzx']; exact sum_smul_copy_apply t' x' j
    rw [← h1, ← h2]
  have htt : t = t' := funext fun j ↦ congrArg Prod.snd (hcoord j)
  have hxx : ∀ j, 0 < t j → x j = x' j := by
    intro j hj
    have := congrArg Prod.fst (hcoord j)
    simp only at this
    rw [← htt] at this
    exact smul_right_injective _ (ne_of_gt hj) this
  rw [hzx]
  refine sum_smul_copy_mem_joinCellCarrier t x ht0 ht1 fun i hi ↦ ?_
  refine hfg i ⟨hx i hi, ?_⟩
  rw [hxx i hi]
  exact hx' i (by rw [← htt]; exact hi)

end JoinCells

/-! ### Restricting a simplex of the subdivision to a subface -/

section Restriction

variable {W V E : Type*} [Fintype W] [DecidableEq W] [LinearOrder W] [DecidableEq V]
variable [AddCommGroup E] [Module ℝ E]

omit [Fintype W] in
/-- A simplex of the subdivision of `S` all of whose vertices are contained in
a subset `R ⊆ S` is a simplex of the subdivision of `R`. -/
theorem mem_sdFaces_of_subset {orig : W → V} {R : Finset W} {σ : Finset (Finset W)}
    (hsub : ∀ s ∈ σ, s ⊆ R) :
    ∀ {S : Finset W}, R ⊆ S → σ ∈ sdFaces orig S → σ ∈ sdFaces orig R := by
  classical
  suffices h : ∀ k : ℕ, ∀ S : Finset W, (S \ R).card = k → R ⊆ S →
      σ ∈ sdFaces orig S → σ ∈ sdFaces orig R by
    intro S hRS hσ
    exact h _ S rfl hRS hσ
  intro k
  induction k with
  | zero =>
    intro S hcard hRS hσ
    have : S \ R = ∅ := Finset.card_eq_zero.mp hcard
    have hSR : S ⊆ R := by
      intro w hw
      by_contra hwR
      exact absurd (Finset.mem_sdiff.mpr ⟨hw, hwR⟩) (by rw [this]; exact Finset.notMem_empty w)
    have : S = R := Finset.Subset.antisymm hSR hRS
    exact this ▸ hσ
  | succ k ih =>
    intro S hcard hRS hσ
    obtain ⟨u, hu⟩ : (S \ R).Nonempty := by
      rw [← Finset.card_pos, hcard]; omega
    obtain ⟨huS, huR⟩ := Finset.mem_sdiff.mp hu
    have havoid : ∀ s ∈ σ, u ∉ s := fun s hs hus ↦ huR (hsub s hs hus)
    have hσ' : σ ∈ sdFaces orig (S.erase u) := mem_sdFaces_erase_of_avoid hσ havoid
    refine ih (S.erase u) ?_ ?_ hσ'
    · have : S.erase u \ R = (S \ R).erase u := by
        ext w
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        tauto
      rw [this, Finset.card_erase_of_mem hu, hcard]
      omega
    · exact fun w hw ↦ Finset.mem_erase.mpr ⟨fun h ↦ huR (h ▸ hw), hRS hw⟩

end Restriction

/-! ### The part of a simplex lying in a subface -/

section CayleyRestriction

variable {e m : ℕ} {W : Type*} [Fintype W] [DecidableEq W] [LinearOrder W]
variable (idx : W → Fin (m + 1)) (vert : W → CoordinateSpace e)

omit [DecidableEq W] [LinearOrder W] in
/-- Affine independence in the weight formulation is inherited by subsets. -/
theorem affIndepOn_mono {E : Type*} [AddCommGroup E] [Module ℝ E] {ρ : W → E}
    {S T : Finset W} (h : AffIndepOn ρ S) (hTS : T ⊆ S) : AffIndepOn ρ T :=
  fun c hsupp hsum hcomb ↦ h c (fun w hw ↦ hsupp w fun hwT ↦ hw (hTS hwT)) hsum hcomb

/-- **Restriction of a simplex to a subface.**  The part of the realization of
a simplex of the subdivision of `S` lying in the join cell of a subface `R` is
the realization of the subsimplex on the vertices contained in `R`. -/
theorem sdRealize_inter_joinCell {S R : Finset W} (hRS : R ⊆ S)
    (hindep : AffIndepOn (cayleyPt idx vert) S) {σ : Finset (Finset W)}
    (hσ : σ ∈ sdFaces vert S) :
    sdRealize (cayleyPt idx vert) σ ∩ joinCellCarrier (joinFactor idx vert R) ⊆
      sdRealize (cayleyPt idx vert) (σ.filter fun s ↦ s ⊆ R) := by
  classical
  rintro x ⟨hxσ, hxR⟩
  obtain ⟨l, hl, hlx⟩ := (mem_convexHull_image_iff (sdPt (cayleyPt idx vert)) σ x).mp hxσ
  set c : W → ℝ := coeffPoint l with hc
  have hcx : ∑ w, c w • cayleyPt idx vert w = x := by
    rw [hc, ← sum_smul_sdPt]; exact hlx
  have hne : ∀ s ∈ σ, s.Nonempty := fun s hs ↦ (sdFaces_vertex vert S hσ s hs).1
  have hcw : ConvexWeights S c :=
    { nonneg := fun w ↦ coeffPoint_nonneg hl.nonneg w
      support := fun w hw ↦ coeffPoint_support hσ hl.support w hw
      sum_one := by rw [hc, sum_coeffPoint hne hl.support]; exact hl.sum_one }
  have hxR' : x ∈ convexHull ℝ (cayleyPt idx vert '' (R : Set W)) := by
    rw [convexHull_cayleyPt_eq_joinCellCarrier]; exact hxR
  obtain ⟨c', hc', hc'x⟩ :=
    (mem_convexHull_image_iff (cayleyPt idx vert) R x).mp hxR'
  have hcc : c = c' := by
    have hzero : ∀ w, (c w - c' w) = 0 := by
      refine hindep (fun w ↦ c w - c' w) (fun w hw ↦ ?_) ?_ ?_
      · rw [hcw.support w hw, hc'.support w (fun hwR ↦ hw (hRS hwR)), sub_zero]
      · rw [Finset.sum_sub_distrib, hcw.sum_one, hc'.sum_one, sub_self]
      · simp_rw [sub_smul]
        rw [Finset.sum_sub_distrib, hcx, hc'x, sub_self]
    exact funext fun w ↦ sub_eq_zero.mp (hzero w)
  have hcR : ∀ w, w ∉ R → c w = 0 := fun w hw ↦ by rw [hcc]; exact hc'.support w hw
  have hlfilter : ∀ s, s ∉ σ.filter (fun s ↦ s ⊆ R) → l s = 0 := by
    intro s hs
    by_cases hsσ : s ∈ σ
    · have hsR : ¬ s ⊆ R := fun h ↦ hs (Finset.mem_filter.mpr ⟨hsσ, h⟩)
      obtain ⟨w, hws, hwR⟩ := Finset.not_subset.mp hsR
      have hsum0 : ∑ s' : Finset W, l s' * coordVec s' w = 0 := hcR w hwR
      have hterm : l s * coordVec s w = 0 := by
        by_contra hne0
        have hnonneg : ∀ s' ∈ (Finset.univ : Finset (Finset W)),
            0 ≤ l s' * coordVec s' w :=
          fun s' _ ↦ mul_nonneg (hl.nonneg s') (coordVec_nonneg s' w)
        have := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum0 s (Finset.mem_univ s)
        exact hne0 this
      rcases mul_eq_zero.mp hterm with h | h
      · exact h
      · exact absurd h (ne_of_gt (coordVec_pos hws))
    · exact hl.support s hsσ
  have : x = ∑ s : Finset W, l s • sdPt (cayleyPt idx vert) s := hlx.symm
  rw [this]
  exact sum_smul_mem_convexHull_image _
    { nonneg := hl.nonneg, support := hlfilter, sum_one := hl.sum_one }

end CayleyRestriction

end BadEdge
end AffineTverberg
