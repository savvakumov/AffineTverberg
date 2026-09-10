import AffineTverberg.BadEdgeSubdivisionCoords
import AffineTverberg.ConvexCombination

set_option linter.style.header false

/-!
# Geometric realization of the bad-edge subdivision

Let `ρ : W → E` place the join vertices in a real vector space.  A vertex `s` of
the bad-edge subdivision (a singleton or a bad pair) is realized as the
barycentre `sdPt ρ s` of its join vertices — so original vertices are realized
by themselves and the inserted vertices are exactly the *midpoints of bad
edges* — and a simplex `σ` of the subdivision is realized as the convex hull
`sdRealize ρ σ` of the realizations of its vertices.

## Main results

Assume `ρ` is affinely independent on the join face `S` (`AffIndepOn ρ S`),
which is what a geometric simplicial complex provides for each of its faces.

* `sdRealize_subset_convexHull` : every simplex of the subdivision of `S` is
  realized inside `conv (ρ '' S)`;
* `affineIndependent_sdPt` : the realized vertices of a simplex of the
  subdivision are affinely independent;
* `sdRealize_inter` : two simplices of the subdivision meet exactly in the
  realization of their common face;
* `injOn_sdPt` : distinct vertices of the subdivision have distinct
  realizations.
-/

open scoped BigOperators
open Set

namespace AffineTverberg
namespace BadEdge

variable {W V E : Type*} [Fintype W] [DecidableEq W] [LinearOrder W] [DecidableEq V]
variable [AddCommGroup E] [Module ℝ E]

/-- The realization of a subdivision vertex: the barycentre of its join
vertices.  Singletons give original vertices and pairs give bad-edge
midpoints. -/
noncomputable def sdPt (ρ : W → E) (s : Finset W) : E := ∑ w, coordVec s w • ρ w

/-- The realization of a simplex of the subdivision. -/
noncomputable def sdRealize (ρ : W → E) (σ : Finset (Finset W)) : Set E :=
  convexHull ℝ (sdPt ρ '' (σ : Set (Finset W)))

omit [LinearOrder W] in
theorem sdPt_singleton (ρ : W → E) (u : W) : sdPt ρ {u} = ρ u := by
  rw [sdPt, Finset.sum_eq_single u]
  · rw [coordVec_of_mem (Finset.mem_singleton_self u)]
    simp
  · intro w _ hwu
    rw [coordVec_eq_zero (by simpa using hwu), zero_smul]
  · intro hc
    exact absurd (Finset.mem_univ u) hc

omit [LinearOrder W] in
/-- The realization of a bad pair is the midpoint of the corresponding bad
edge. -/
theorem sdPt_pair (ρ : W → E) {u w : W} (huw : u ≠ w) :
    sdPt ρ {u, w} = (2 : ℝ)⁻¹ • ρ u + (2 : ℝ)⁻¹ • ρ w := by
  classical
  have hcard : ({u, w} : Finset W).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using huw), Finset.card_singleton]
  have hsum : ∑ x, coordVec ({u, w} : Finset W) x • ρ x =
      coordVec ({u, w} : Finset W) u • ρ u + coordVec ({u, w} : Finset W) w • ρ w := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ u),
      ← Finset.add_sum_erase _ (fun x ↦ coordVec ({u, w} : Finset W) x • ρ x)
        (Finset.mem_erase.mpr ⟨Ne.symm huw, Finset.mem_univ w⟩)]
    have hz : ∑ x ∈ (Finset.univ.erase u).erase w,
        coordVec ({u, w} : Finset W) x • ρ x = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      obtain ⟨hxw, hx'⟩ := Finset.mem_erase.mp hx
      obtain ⟨hxu, -⟩ := Finset.mem_erase.mp hx'
      rw [coordVec_eq_zero (by simp [hxu, hxw]), zero_smul]
    rw [hz, add_zero]
  rw [sdPt, hsum, coordVec_of_mem (by simp), coordVec_of_mem (by simp), hcard]
  norm_num

omit [LinearOrder W] in
theorem sdPt_mem_convexHull {ρ : W → E} {S s : Finset W} (hs : s.Nonempty) (hsS : s ⊆ S) :
    sdPt ρ s ∈ convexHull ℝ (ρ '' (S : Set W)) := by
  refine sum_smul_mem_convexHull_image ρ ⟨fun w ↦ coordVec_nonneg s w, fun w hw ↦ ?_,
    sum_coordVec hs⟩
  exact coordVec_eq_zero fun hws ↦ hw (hsS hws)

omit [LinearOrder W] in
theorem sdRealize_mono {ρ : W → E} {σ τ : Finset (Finset W)} (h : σ ⊆ τ) :
    sdRealize ρ σ ⊆ sdRealize ρ τ :=
  convexHull_mono (Set.image_mono (by exact_mod_cast h))

omit [LinearOrder W] in
theorem sdRealize_convex (ρ : W → E) (σ : Finset (Finset W)) : Convex ℝ (sdRealize ρ σ) :=
  convex_convexHull ℝ _

omit [LinearOrder W] in
theorem sdPt_mem_sdRealize {ρ : W → E} {σ : Finset (Finset W)} {s : Finset W} (hs : s ∈ σ) :
    sdPt ρ s ∈ sdRealize ρ σ :=
  subset_convexHull ℝ _ ⟨s, hs, rfl⟩

/-- Each simplex of the subdivision of `S` is realized inside the face. -/
theorem sdRealize_subset_convexHull (orig : W → V) {ρ : W → E} {S : Finset W}
    {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S) :
    sdRealize ρ σ ⊆ convexHull ℝ (ρ '' (S : Set W)) := by
  refine convexHull_min ?_ (convex_convexHull ℝ _)
  rintro y ⟨s, hs, rfl⟩
  obtain ⟨hne, hsub, -⟩ := sdFaces_vertex orig S hσ s (by exact_mod_cast hs)
  exact sdPt_mem_convexHull hne hsub

/-! ### Affine independence -/

/-- Affine independence of the realizations of the join vertices of `S`, in the
elementary weight formulation. -/
def AffIndepOn (ρ : W → E) (S : Finset W) : Prop :=
  ∀ c : W → ℝ, (∀ w, w ∉ S → c w = 0) → (∑ w, c w = 0) → (∑ w, c w • ρ w = 0) → ∀ w, c w = 0

omit [DecidableEq W] [LinearOrder W] in
theorem affIndepOn_of_affineIndependent {ρ : W → E} {S : Finset W}
    (h : AffineIndependent ℝ fun w : {x // x ∈ S} ↦ ρ (w : W)) : AffIndepOn ρ S := by
  classical
  intro c hsupp hsum hcomb w
  by_cases hw : w ∈ S
  · have h' := affineIndependent_iff.mp h Finset.univ (fun x ↦ c (x : W))
    have hsum' : ∑ x : {x // x ∈ S}, c (x : W) = 0 := by
      rw [Finset.sum_coe_sort S c, Finset.sum_subset (Finset.subset_univ S)
        (fun i _ hi ↦ hsupp i hi)]
      exact hsum
    have hcomb' : ∑ x : {x // x ∈ S}, c (x : W) • ρ (x : W) = 0 := by
      rw [Finset.sum_coe_sort S (fun i ↦ c i • ρ i),
        Finset.sum_subset (Finset.subset_univ S)
          (fun i _ hi ↦ by rw [hsupp i hi, zero_smul])]
      exact hcomb
    exact h' hsum' hcomb' ⟨w, hw⟩ (Finset.mem_univ _)
  · exact hsupp w hw

omit [LinearOrder W] in
/-- The coordinate vector attached to a weight function on subdivision
vertices computes the realized point. -/
theorem sum_smul_sdPt (ρ : W → E) (l : Finset W → ℝ) :
    ∑ s : Finset W, l s • sdPt ρ s = ∑ w, coeffPoint l w • ρ w := by
  classical
  unfold sdPt coeffPoint
  simp_rw [Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

omit [LinearOrder W] in
theorem sum_coeffPoint {σ : Finset (Finset W)} {l : Finset W → ℝ}
    (hne : ∀ s ∈ σ, s.Nonempty) (hsupp : ∀ s, s ∉ σ → l s = 0) :
    ∑ w, coeffPoint l w = ∑ s : Finset W, l s := by
  classical
  unfold coeffPoint
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  by_cases hs : s ∈ σ
  · rw [← Finset.mul_sum, sum_coordVec (hne s hs), mul_one]
  · rw [hsupp s hs]
    simp
theorem coeffPoint_support {orig : W → V} {S : Finset W} {σ : Finset (Finset W)}
    (hσ : σ ∈ sdFaces orig S) {l : Finset W → ℝ} (hsupp : ∀ s, s ∉ σ → l s = 0) :
    ∀ w, w ∉ S → coeffPoint l w = 0 := by
  intro w hw
  unfold coeffPoint
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : s ∈ σ
  · have hsub := (sdFaces_vertex orig S hσ s hs).2.1
    rw [coordVec_eq_zero (fun hws ↦ hw (hsub hws)), mul_zero]
  · rw [hsupp s hs, zero_mul]

/-- **Affine independence of the subdivision.**  The realized vertices of a
simplex of the subdivision of `S` are affinely independent as soon as the join
vertices of `S` are. -/
theorem affineIndependent_sdPt (orig : W → V) {ρ : W → E} {S : Finset W}
    (hindep : AffIndepOn ρ S) {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S) :
    AffineIndependent ℝ fun s : (σ : Set (Finset W)) ↦ sdPt ρ s := by
  classical
  rw [affineIndependent_iff]
  intro t v hv0 hvcomb e he
  set l : Finset W → ℝ := fun s ↦ ∑ x ∈ t, if (x : Finset W) = s then v x else 0 with hl
  have hlval : ∀ x ∈ t, l (x : Finset W) = v x := by
    intro x hx
    rw [hl]
    simp only
    rw [Finset.sum_eq_single x]
    · rw [ite_eq_left rfl]
    · intro y _ hyx
      exact ite_eq_right fun hcon ↦ hyx (Subtype.ext hcon)
    · intro hcon
      exact absurd hx hcon
  have hlsupp : ∀ s, s ∉ σ → l s = 0 := by
    intro s hs
    rw [hl]
    apply Finset.sum_eq_zero
    intro x _
    refine ite_eq_right fun hcon ↦ hs ?_
    rw [← hcon]
    exact_mod_cast x.2
  have hsuml : ∑ s : Finset W, l s = 0 := by
    rw [hl]
    simp only
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun x _ ↦ ?_) hv0
    rw [Finset.sum_ite_eq Finset.univ (x : Finset W) (fun _ ↦ v x),
      ite_eq_left (Finset.mem_univ _)]
  have hcomb : ∑ s : Finset W, l s • sdPt ρ s = 0 := by
    rw [hl]
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Eq.trans (Finset.sum_congr rfl fun x _ ↦ ?_) hvcomb
    rw [Finset.sum_eq_single (x : Finset W)]
    · rw [ite_eq_left rfl]
    · intro y _ hyx
      rw [ite_eq_right (fun hcon ↦ hyx hcon.symm), zero_smul]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have hne : ∀ s ∈ σ, s.Nonempty := fun s hs ↦ (sdFaces_vertex orig S hσ s hs).1
  have hcoeffsum : ∑ w, coeffPoint l w = 0 := by
    rw [sum_coeffPoint (σ := σ) hne hlsupp, hsuml]
  have hcoeffcomb : ∑ w, coeffPoint l w • ρ w = 0 := by
    rw [← sum_smul_sdPt, hcomb]
  have hcoeff0 : ∀ w, coeffPoint l w = 0 :=
    hindep _ (coeffPoint_support hσ hlsupp) hcoeffsum hcoeffcomb
  have hl0 : ∀ s, l s = 0 :=
    coordVec_linearIndependent orig S hσ l hlsupp (fun w ↦ hcoeff0 w)
  rw [← hlval e he]
  exact hl0 _

/-! ### The intersection property -/

/-- **The subdivision is a genuine triangulation**: two of its simplices meet
exactly in the realization of their common face. -/
theorem sdRealize_inter (orig : W → V) {ρ : W → E} {S : Finset W}
    (hindep : AffIndepOn ρ S) {σ τ : Finset (Finset W)}
    (hσ : σ ∈ sdFaces orig S) (hτ : τ ∈ sdFaces orig S) :
    sdRealize ρ σ ∩ sdRealize ρ τ = sdRealize ρ (σ ∩ τ) := by
  classical
  apply Set.Subset.antisymm
  · rintro x ⟨hxσ, hxτ⟩
    obtain ⟨l, hl, hlx⟩ := (mem_convexHull_image_iff (sdPt ρ) σ x).mp hxσ
    obtain ⟨n, hn, hnx⟩ := (mem_convexHull_image_iff (sdPt ρ) τ x).mp hxτ
    have hneσ : ∀ s ∈ σ, s.Nonempty := fun s hs ↦ (sdFaces_vertex orig S hσ s hs).1
    have hneτ : ∀ s ∈ τ, s.Nonempty := fun s hs ↦ (sdFaces_vertex orig S hτ s hs).1
    have hsumeq : ∑ w, (coeffPoint l w - coeffPoint n w) = 0 := by
      rw [Finset.sum_sub_distrib, sum_coeffPoint (σ := σ) hneσ hl.support,
        sum_coeffPoint (σ := τ) hneτ hn.support, hl.sum_one, hn.sum_one, sub_self]
    have hcombeq : ∑ w, (coeffPoint l w - coeffPoint n w) • ρ w = 0 := by
      simp_rw [sub_smul]
      rw [Finset.sum_sub_distrib, ← sum_smul_sdPt, ← sum_smul_sdPt, hlx, hnx, sub_self]
    have hzero := hindep _ (fun w hw ↦ by
      rw [coeffPoint_support hσ hl.support w hw, coeffPoint_support hτ hn.support w hw,
        sub_zero]) hsumeq hcombeq
    have hcoeff : coeffPoint l = coeffPoint n := by
      funext w
      have := hzero w
      linarith [this]
    have hln : l = n :=
      coeffPoint_injective orig S hσ hτ hl.nonneg hn.nonneg hl.support hn.support hcoeff
    subst hln
    rw [← hlx]
    refine sum_smul_mem_convexHull_image (sdPt ρ) ⟨hl.nonneg, fun s hs ↦ ?_, hl.sum_one⟩
    rw [Finset.mem_inter] at hs
    push Not at hs
    by_cases hsσ : s ∈ σ
    · exact hn.support s (hs hsσ)
    · exact hl.support s hsσ
  · exact Set.subset_inter (sdRealize_mono Finset.inter_subset_left)
      (sdRealize_mono Finset.inter_subset_right)

/-- Distinct subdivision vertices of a simplex have distinct realizations. -/
theorem injOn_sdPt (orig : W → V) {ρ : W → E} {S : Finset W} (hindep : AffIndepOn ρ S)
    {σ : Finset (Finset W)} (hσ : σ ∈ sdFaces orig S) :
    Set.InjOn (sdPt ρ) (σ : Set (Finset W)) := by
  have h := affineIndependent_sdPt orig hindep hσ
  intro s hs t ht hst
  have hinj : (⟨s, hs⟩ : (σ : Set (Finset W))) = ⟨t, ht⟩ := h.injective hst
  exact congrArg Subtype.val hinj

end BadEdge
end AffineTverberg
