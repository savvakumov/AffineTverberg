import Mathlib.Analysis.Convex.Join
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option linter.style.header false

/-!
# Coning in the complement of a low-dimensional finite polyhedron

A generic apex avoids the affine spans of all pairs of a filling simplex
and a bad simplex. Coning to this apex then misses the bad polyhedron.
This supplies the geometric general-position step for the local argument;
passing arbitrary singular cycles to such finite affine chains is separate.
-/

noncomputable section

open Set

namespace AffineTverberg.GeneralPosition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem dense_compl_affineSubspace {L : AffineSubspace ℝ E} (hL : L ≠ ⊤) :
    Dense ((L : Set E)ᶜ) := by
  apply interior_eq_empty_iff_dense_compl.mp
  apply Set.not_nonempty_iff_eq_empty.mp
  intro hi
  have ht := isOpen_interior.affineSpan_eq_top hi
  have hl : affineSpan ℝ (interior (L : Set E)) ≤ L :=
    affineSpan_le.mpr interior_subset
  rw [ht] at hl
  exact hL (top_le_iff.mp hl)

theorem dense_avoid_affineSubspaces {ι : Type*} (s : Finset ι)
    (L : ι → AffineSubspace ℝ E) (hL : ∀ i ∈ s, L i ≠ ⊤) :
    Dense {p : E | ∀ i ∈ s, p ∉ L i} := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hd := dense_compl_affineSubspace (hL i (Finset.mem_insert_self i s))
    have ht := ih (fun j hj ↦ hL j (Finset.mem_insert_of_mem hj))
    have ho := (L i).closed_of_finiteDimensional.isOpen_compl
    have heq : {p : E | ∀ j ∈ insert i s, p ∉ L j} =
        (L i : Set E)ᶜ ∩ {p : E | ∀ j ∈ s, p ∉ L j} := by
      ext p
      simp
    rw [heq]
    exact hd.inter_of_isOpen_left ht ho

omit [FiniteDimensional ℝ E] in
theorem affineSpan_ne_top_of_card_le {s : Finset E}
    (hs : s.card ≤ Module.finrank ℝ E) : affineSpan ℝ (s : Set E) ≠ ⊤ := by
  classical
  intro ht
  rcases s.eq_empty_or_nonempty with rfl | hn
  · simp at ht
  · have hc : s.card = (s.card - 1) + 1 := by have := hn.card_pos; omega
    have hb := finrank_vectorSpan_image_finset_le ℝ (fun x : E ↦ x) s hc
    have himg : s.image (fun x : E ↦ x) = s := Finset.image_id
    rw [himg] at hb
    have hv := AffineSubspace.vectorSpan_eq_top_of_affineSpan_eq_top ℝ E E ht
    rw [hv, finrank_top] at hb
    have := hn.card_pos
    omega

omit [FiniteDimensional ℝ E] in
/-- If a cone meets the bad hull, its apex lies in the affine span of the
two vertex sets, unless the base already meets the bad hull. -/
theorem disjoint_cone_of_not_mem_affineSpan {s t : Set E} {p : E}
    (hst : Disjoint (convexHull ℝ s) (convexHull ℝ t))
    (hp : p ∉ affineSpan ℝ (s ∪ t)) :
    Disjoint (convexHull ℝ (insert p s)) (convexHull ℝ t) := by
  apply Set.disjoint_left.mpr
  intro z hzs hzt
  have hzL : z ∈ affineSpan ℝ (s ∪ t) :=
    (affineSpan_mono ℝ Set.subset_union_right) (convexHull_subset_affineSpan t hzt)
  rcases s.eq_empty_or_nonempty with rfl | hs
  · rw [insert_empty_eq, convexHull_singleton, Set.mem_singleton_iff] at hzs
    exact hp (hzs ▸ hzL)
  · rw [convexHull_insert hs] at hzs
    obtain ⟨x, hx, y, hy, a, b, ha, hb, hab, hz⟩ := mem_convexJoin.mp hzs
    simp only [Set.mem_singleton_iff] at hx
    subst x
    have hyL : y ∈ affineSpan ℝ (s ∪ t) :=
      (affineSpan_mono ℝ Set.subset_union_left) (convexHull_subset_affineSpan s hy)
    by_cases ha0 : a = 0
    · have hb1 : b = 1 := by linarith
      have hyz : y = z := by simpa [ha0, hb1] using hz
      exact Set.disjoint_left.mp hst (hyz ▸ hy) hzt
    · have hb' : b = 1 - a := by linarith
      have hdiff : z - y = a • (p - y) := by rw [← hz, hb']; module
      have hm := (affineSpan ℝ (s ∪ t)).smul_vsub_vadd_mem a⁻¹ hzL hyL hyL
      change a⁻¹ • (z - y) + y ∈ affineSpan ℝ (s ∪ t) at hm
      rw [hdiff, smul_smul, inv_mul_cancel₀ ha0, one_smul, sub_add_cancel] at hm
      exact hp hm

/-- The union of the finite convex hulls in a family. -/
def hullCarrier (K : Finset (Finset E)) : Set E :=
  ⋃ s ∈ K, convexHull ℝ (s : Set E)

/-- A generic cone apex can be chosen in any prescribed nonempty open set. -/
theorem exists_conePoint [DecidableEq E] {K B : Finset (Finset E)} {U : Set E}
    (hU : IsOpen U) (hne : U.Nonempty)
    (hdisj : Disjoint (hullCarrier K) (hullCarrier B))
    (hcard : ∀ s ∈ K, ∀ t ∈ B, (s ∪ t).card ≤ Module.finrank ℝ E) :
    ∃ p ∈ U, ∀ s ∈ K, ∀ t ∈ B,
      Disjoint (convexHull ℝ (insert p (s : Set E))) (convexHull ℝ (t : Set E)) := by
  let L : Finset E × Finset E → AffineSubspace ℝ E :=
    fun st ↦ affineSpan ℝ ((st.1 ∪ st.2 : Finset E) : Set E)
  have hd := dense_avoid_affineSubspaces (K ×ˢ B) L (by
    intro st hst
    obtain ⟨hs, ht⟩ := Finset.mem_product.mp hst
    exact affineSpan_ne_top_of_card_le (hcard st.1 hs st.2 ht))
  obtain ⟨p, hpU, hp⟩ := hd.inter_open_nonempty U hU hne
  refine ⟨p, hpU, fun s hs t ht ↦ disjoint_cone_of_not_mem_affineSpan ?_ ?_⟩
  · exact hdisj.mono (Set.subset_iUnion₂_of_subset s hs Subset.rfl)
      (Set.subset_iUnion₂_of_subset t ht Subset.rfl)
  · simpa only [L, Finset.coe_union] using hp (s, t) (Finset.mem_product.mpr ⟨hs, ht⟩)

/-- The finite coned carrier. All its constituent convex sets contain `p`. -/
def coneCarrier (K : Finset (Finset E)) (p : E) : Set E :=
  ⋃ s ∈ K, convexHull ℝ (insert p (s : Set E))

omit [FiniteDimensional ℝ E] in
theorem starConvex_coneCarrier (K : Finset (Finset E)) (p : E) :
    StarConvex ℝ p (coneCarrier K p) := by
  exact starConvex_iUnion₂ fun s _ ↦
    (convex_convexHull ℝ _).starConvex (subset_convexHull ℝ _ (Set.mem_insert p _))

omit [FiniteDimensional ℝ E] in
theorem contractibleSpace_coneCarrier {K : Finset (Finset E)} (hK : K.Nonempty) (p : E) :
    ContractibleSpace ↥(coneCarrier K p) := by
  obtain ⟨s, hs⟩ := hK
  exact (starConvex_coneCarrier K p).contractibleSpace ⟨p,
    Set.mem_iUnion₂.mpr ⟨s, hs, subset_convexHull ℝ _ (Set.mem_insert p _)⟩⟩

/-- A finite low-dimensional carrier in the complement of a bad polyhedron
is contained in a contractible coned carrier in the same complement. -/
theorem exists_contractible_filling [DecidableEq E] {K B : Finset (Finset E)}
    {P : Set E} (hP : Convex ℝ P) (hfull : affineSpan ℝ P = ⊤)
    (hK : K.Nonempty) (hKP : hullCarrier K ⊆ P)
    (hdisj : Disjoint (hullCarrier K) (hullCarrier B))
    (hcard : ∀ s ∈ K, ∀ t ∈ B, (s ∪ t).card ≤ Module.finrank ℝ E) :
    ∃ C : Set E, hullCarrier K ⊆ C ∧ C ⊆ P \ hullCarrier B ∧ ContractibleSpace C := by
  obtain ⟨p, hp, hcone⟩ := exists_conePoint isOpen_interior
    (hP.interior_nonempty_iff_affineSpan_eq_top.mpr hfull) hdisj hcard
  refine ⟨coneCarrier K p, ?_, ?_, contractibleSpace_coneCarrier hK p⟩
  · intro x hx
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
    exact Set.mem_iUnion₂.mpr ⟨s, hs, convexHull_mono (Set.subset_insert p _) hx⟩
  · intro x hx
    obtain ⟨s, hs, hx⟩ := Set.mem_iUnion₂.mp hx
    refine ⟨?_, ?_⟩
    · apply convexHull_min _ hP hx
      refine Set.insert_subset (interior_subset hp) ?_
      exact (subset_convexHull ℝ _).trans ((Set.subset_iUnion₂_of_subset s hs Subset.rfl).trans hKP)
    · intro hxb
      obtain ⟨t, ht, hxt⟩ := Set.mem_iUnion₂.mp hxb
      exact Set.disjoint_left.mp (hcone s hs t ht) hx hxt

end AffineTverberg.GeneralPosition
