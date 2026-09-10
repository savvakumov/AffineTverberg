import AffineTverberg.PolytopalBadVertexTriangulation
import AffineTverberg.CayleyJoinRank
import AffineTverberg.CayleyJoinDimension

set_option linter.style.header false

/-!
# The sharp affine-dimension good-vertex bound

For the general polytopal bad-vertex triangulation of the Cayley join
`Q = P * ⋯ * P` built in `PolytopalBadVertexTriangulation.lean` we prove the
paper's good-vertex count.

For a face `S` of `Q` (recorded by its set of Cayley vertices) put

* `factorPts S i` — the actual vertices of `P` occurring in `S` in the copy `i`;
* `jrank S = ∑ i, arank (factorPts S i)` — the affine rank of `S`, the sum of
  the affine ranks of its factors;
* `projPts S = ⋃ i, factorPts S i` — the union of the *projected* factors, a
  subset of `P`, and `projDim S = arank (projPts S) - 1` its affine dimension.
  This is the paper's `m(F)`: the dimension of the affine span of the union of
  the projected factors, **not** the number of generators.

## Main results

* `mem_of_mem_affineSpan_exposed` — a point of a convex set lying in the affine
  span of an exposed face lies in that face.  This is what makes a missing
  vertex genuinely raise the rank of its factor, and is where the fact that the
  Cayley vertices are *actual* vertices (extreme points) is used.
* `exists_step_index` — on a rank step exactly one factor changes, and its
  affine span grows by adjoining any point off the smaller span.
* `arank_projPts_le_succ_of_step` — the projected span grows by at most one on a
  rank step (`hdrop`).
* `arank_projPts_le_of_bad_step` — **a bad apex costs nothing**: on a rank step
  whose apex is a bad edge not contained in the smaller face, the projected span
  does not grow at all (`hbad`).
* `card_goodVertices_ge_projDim_succ` — **the good-vertex bound**: every full
  simplex of the triangulation of a face `S` has at least `projDim S + 1` good
  vertices.
* `jrank_eq_arank_sdCarrier` — `jrank` is the affine rank of the actual carrier
  of the face, by the Cayley join dimension formula.
* `card_goodVertices_ge_of_top` — for the whole Cayley join this gives at least
  `n + 1` good vertices, `n` being the dimension of `P`.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg
namespace BadVertex

open CayleyJoin PolytopeFace BadEdge

/-! ### Points of a convex set in the affine span of an exposed face -/

section Exposed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **A point of `A` in the affine span of an exposed face lies in the face.**
Consequently a vertex of a polytope missing from a face is off the affine span
of that face. -/
theorem mem_of_mem_affineSpan_exposed {A F : Set E} (hF : IsExposed ℝ A F) {x : E}
    (hx : x ∈ A) (hxs : x ∈ affineSpan ℝ F) : x ∈ F := by
  rcases F.eq_empty_or_nonempty with rfl | hne
  · rw [AffineSubspace.span_empty, ← AffineSubspace.mem_coe,
      AffineSubspace.bot_coe] at hxs
    exact absurd hxs (notMem_empty x)
  obtain ⟨l, hl⟩ := hF hne
  obtain ⟨p, hp⟩ := hne
  have hconst : ∀ y ∈ F, l y = l p := by
    intro y hy
    rw [hl] at hy hp
    exact le_antisymm (hp.2 y hy.1) (hy.2 p hp.1)
  have hker : vectorSpan ℝ F ≤ LinearMap.ker (l : E →ₗ[ℝ] ℝ) := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ hp]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      vsub_eq_sub, map_sub]
    rw [hconst y hy, sub_self]
  have hvsub : x -ᵥ p ∈ vectorSpan ℝ F := by
    have := AffineSubspace.vsub_mem_direction hxs (subset_affineSpan ℝ F hp)
    rwa [direction_affineSpan] at this
  have hlx : l x = l p := by
    have := hker hvsub
    simp only [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, vsub_eq_sub, map_sub] at this
    linarith [this]
  rw [hl]
  refine ⟨hx, fun y hy ↦ ?_⟩
  rw [hlx]
  rw [hl] at hp
  exact hp.2 y hy

end Exposed

variable {n : ℕ} (P : FullDimensionalPolytope n) (m : ℕ)

/-! ### The factors of a face and their affine ranks -/

/-- The actual vertices of `P` occurring in the copy `i` of a set `S` of Cayley
vertices. -/
def factorPts (S : Finset (JoinVertex P m)) (i : Fin (m + 1)) : Set (CoordinateSpace n) :=
  {v | ∃ w ∈ S, w.1 = i ∧ vtx P w.2 = v}

/-- The union of the projected factors of `S`, a subset of the vertex set of
`P`. -/
def projPts (S : Finset (JoinVertex P m)) : Set (CoordinateSpace n) :=
  ⋃ i, factorPts P m S i

/-- The affine rank of a face of the Cayley join: the sum of the affine ranks of
its factors. -/
def jrank (S : Finset (JoinVertex P m)) : ℕ :=
  ∑ i, arank (factorPts P m S i)

/-- The paper's `m(F)`: the affine dimension of the union of the projected
factors. -/
def projDim (S : Finset (JoinVertex P m)) : ℕ :=
  arank (projPts P m S) - 1

variable {P m}

theorem mem_factorPts {S : Finset (JoinVertex P m)} {i : Fin (m + 1)}
    {v : CoordinateSpace n} :
    v ∈ factorPts P m S i ↔ ∃ w ∈ S, w.1 = i ∧ vtx P w.2 = v := Iff.rfl

theorem vtx_mem_factorPts {S : Finset (JoinVertex P m)} {w : JoinVertex P m}
    (hw : w ∈ S) : vtx P w.2 ∈ factorPts P m S w.1 := ⟨w, hw, rfl, rfl⟩

theorem factorPts_mono {S T : Finset (JoinVertex P m)} (h : S ⊆ T) (i : Fin (m + 1)) :
    factorPts P m S i ⊆ factorPts P m T i := by
  rintro v ⟨w, hw, hw1, rfl⟩
  exact ⟨w, h hw, hw1, rfl⟩

theorem factorPts_subset_projPts (S : Finset (JoinVertex P m)) (i : Fin (m + 1)) :
    factorPts P m S i ⊆ projPts P m S := subset_iUnion _ i

theorem jrank_eq_zero_iff {S : Finset (JoinVertex P m)} : jrank P m S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    rw [Finset.eq_empty_iff_forall_notMem]
    intro w hw
    have hz : arank (factorPts P m S w.1) = 0 := by
      have := Finset.sum_eq_zero_iff.mp h w.1 (Finset.mem_univ _)
      exact this
    have hne : (factorPts P m S w.1).Nonempty := ⟨_, vtx_mem_factorPts hw⟩
    rw [arank_eq_zero_iff.mp hz] at hne
    exact absurd hne (by simp)
  · rintro rfl
    refine Finset.sum_eq_zero fun i _ ↦ ?_
    have : factorPts P m (∅ : Finset (JoinVertex P m)) i = ∅ := by
      ext v; simp [mem_factorPts]
    rw [this, arank_empty]

theorem jrank_mono {S T : Finset (JoinVertex P m)} (h : S ⊆ T) :
    jrank P m S ≤ jrank P m T :=
  Finset.sum_le_sum fun i _ ↦ arank_mono (factorPts_mono h i)

/-- The factors of a face of the Cayley join are the actual vertices of `P` in
the corresponding factor faces. -/
theorem factorPts_faceVertexSet (C : Fin (m + 1) → PolytopeFaceIndex P) (i : Fin (m + 1)) :
    factorPts P m (faceVertexSet P m C) i
      = (C i).carrier ∩ (P.actualVertices : Set (CoordinateSpace n)) := by
  ext v
  constructor
  · rintro ⟨w, hw, hw1, rfl⟩
    rw [mem_faceVertexSet] at hw
    subst hw1
    exact ⟨hw, P.mem_actualVertices.mpr (P.mem_actualVertices.mp (vtx_mem P w.2))⟩
  · rintro ⟨hv, hvv⟩
    obtain ⟨k, rfl⟩ := exists_vtx P (Finset.mem_coe.mp hvv)
    exact ⟨((i, k) : JoinVertex P m), (mem_faceVertexSet P m).mpr hv, rfl, rfl⟩

/-- The affine span of a factor of a face is the affine span of the actual
factor face. -/
theorem affineSpan_factorPts_faceVertexSet (C : Fin (m + 1) → PolytopeFaceIndex P)
    (i : Fin (m + 1)) :
    affineSpan ℝ (factorPts P m (faceVertexSet P m C) i) = affineSpan ℝ (C i).carrier := by
  rw [factorPts_faceVertexSet]
  conv_rhs => rw [P.face_eq_convexHull_actualVertices (C i).isFace]
  rw [affineSpan_convexHull]

/-- **A Cayley vertex missing from a face is off the affine span of the
corresponding factor.**  This is where the extremality of the actual vertices
enters. -/
theorem notMem_affineSpan_factorPts {S : Finset (JoinVertex P m)}
    (hS : S ∈ faceFamily P m) {w : JoinVertex P m} (hw : w ∉ S) :
    vtx P w.2 ∉ affineSpan ℝ (factorPts P m S w.1) := by
  obtain ⟨C, rfl⟩ := (mem_faceFamily_iff P m).mp hS
  rw [affineSpan_factorPts_faceVertexSet]
  intro hmem
  have hx : vtx P w.2 ∈ P.carrier := by
    have := P.mem_actualVertices.mp (vtx_mem P w.2)
    exact this.1
  exact hw ((mem_faceVertexSet P m).mpr
    (mem_of_mem_affineSpan_exposed (C w.1).isFace hx hmem))

/-- **`jrank` is the actual affine rank of the geometric carrier of the face**:
by the dimension formula for the Cayley join, the sum of the affine ranks of the
factors is the affine rank of the face of `Q` itself.  So an apex flag really is
a flag of faces of dimensions `0, 1, …, k`. -/
theorem jrank_eq_arank_sdCarrier {S : Finset (JoinVertex P m)} (hS : S ∈ faceFamily P m) :
    jrank P m S = arank (sdCarrier P m S) := by
  obtain ⟨C, rfl⟩ := (mem_faceFamily_iff P m).mp hS
  rw [sdCarrier_faceVertexSet, arank_cayleyJoin _ fun i ↦ (C i).convex]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact arank_eq_of_affineSpan_eq (affineSpan_factorPts_faceVertexSet C i)

/-! ### One factor changes on a rank step -/

/-- **On a rank step exactly one factor changes.** -/
theorem exists_step_index {S G : Finset (JoinVertex P m)} (hGS : G ⊆ S)
    (hstep : jrank P m G + 1 = jrank P m S) :
    ∃ i, arank (factorPts P m G i) + 1 = arank (factorPts P m S i) ∧
      (∀ k, k ≠ i → arank (factorPts P m G k) = arank (factorPts P m S k)) ∧
      (∀ k, k ≠ i → affineSpan ℝ (factorPts P m S k)
        = affineSpan ℝ (factorPts P m G k)) := by
  obtain ⟨i, hi, hother⟩ := exists_unique_index_of_sum_step
    (fun k ↦ arank (factorPts P m S k)) (fun k ↦ arank (factorPts P m G k))
    (fun k ↦ arank_mono (factorPts_mono hGS k)) hstep
  refine ⟨i, hi, hother, fun k hk ↦ ?_⟩
  rcases (factorPts P m G k).eq_empty_or_nonempty with hemp | hne
  · have hz : arank (factorPts P m S k) = 0 := by rw [← hother k hk, hemp, arank_empty]
    rw [arank_eq_zero_iff.mp hz, hemp]
  · exact (affineSpan_eq_of_subset_of_arank_le hne (factorPts_mono hGS k)
      (le_of_eq (hother k hk).symm)).symm

/-- **The projected span grows by at most one on a rank step.** -/
theorem arank_projPts_le_succ_of_step {S G : Finset (JoinVertex P m)} (hGS : G ⊆ S)
    (hstep : jrank P m G + 1 = jrank P m S) :
    arank (projPts P m S) ≤ arank (projPts P m G) + 1 := by
  obtain ⟨i, hi, -, hspan⟩ := exists_step_index hGS hstep
  obtain ⟨v, -, hv⟩ := exists_insert_affineSpan_eq (factorPts_mono hGS i) hi
  exact arank_iUnion_le_succ _ _ i v (fun k hk ↦ le_of_eq (hspan k hk)) (le_of_eq hv.symm)

/-- **A bad apex costs nothing.**  If two Cayley vertices of `S` are copies of
the same actual vertex of `P` and one of them is missing from the facet `G`,
then the projected span of `S` is the projected span of `G`. -/
theorem arank_projPts_le_of_shared {S G : Finset (JoinVertex P m)}
    (hG : G ∈ faceFamily P m) (hGS : G ⊆ S)
    (hstep : jrank P m G + 1 = jrank P m S) {u w : JoinVertex P m}
    (huS : u ∈ S) (hwS : w ∈ S) (huw1 : u.1 ≠ w.1) (huw2 : u.2 = w.2)
    (huG : u ∉ G) :
    arank (projPts P m S) ≤ arank (projPts P m G) := by
  obtain ⟨i, hi, hrk, hspan⟩ := exists_step_index hGS hstep
  -- the copy of `u` is the factor which steps
  have hstepindex : ∀ x : JoinVertex P m, x ∈ S → x ∉ G → x.1 = i := by
    intro x hxS hxG
    by_contra hne
    have hlt : arank (factorPts P m G x.1) < arank (factorPts P m S x.1) :=
      arank_lt_of_notMem_affineSpan (factorPts_mono hGS x.1) (vtx_mem_factorPts hxS)
        (notMem_affineSpan_factorPts hG hxG)
    exact absurd (hrk x.1 hne) (Nat.ne_of_lt hlt)
  have hui : u.1 = i := hstepindex u huS huG
  have hwG : w ∈ G := by
    by_contra hwG
    exact huw1 (hui.trans (hstepindex w hwS hwG).symm)
  -- the missing vertex spans the step
  have hv : affineSpan ℝ (insert (vtx P u.2) (factorPts P m G i))
      = affineSpan ℝ (factorPts P m S i) := by
    refine affineSpan_insert_eq_of_arank_step (factorPts_mono hGS i) hi ?_ ?_
    · rw [← hui]; exact vtx_mem_factorPts huS
    · rw [← hui]; exact notMem_affineSpan_factorPts hG huG
  refine arank_iUnion_le_of_shared _ _ i (vtx P u.2)
    (fun k hk ↦ le_of_eq (hspan k hk)) (le_of_eq hv.symm) ?_
  refine subset_affineSpan ℝ _ ?_
  refine factorPts_subset_projPts G w.1 ?_
  rw [huw2]
  exact vtx_mem_factorPts hwG

/-! ### The good-vertex count -/

/-- `hdrop` for the abstract good-vertex count. -/
theorem projDim_le_succ_of_step {S G : Finset (JoinVertex P m)} (hGS : G ⊆ S)
    (hstep : jrank P m G + 1 = jrank P m S) :
    projDim P m S ≤ projDim P m G + 1 := by
  have := arank_projPts_le_succ_of_step hGS hstep
  unfold projDim
  omega

/-- `hbad` for the abstract good-vertex count: a bad apex does not raise the
projected dimension. -/
theorem projDim_le_of_bad_step {S G : Finset (JoinVertex P m)}
    (hG : G ∈ faceFamily P m) (hGS : G ⊆ S) (hstep : jrank P m G + 1 = jrank P m S)
    (hapex : ¬ apexSet (origIndex P m) S ⊆ G)
    (hcard : (apexSet (origIndex P m) S).card = 2) :
    projDim P m S ≤ projDim P m G := by
  have hbad : (badElts (origIndex P m) S).Nonempty := by
    by_contra hcon
    rw [Finset.not_nonempty_iff_eq_empty] at hcon
    rcases S.eq_empty_or_nonempty with rfl | hSne
    · rw [apexSet_empty] at hcard; simp at hcard
    · rw [apexSet_card_eq_one hcon hSne] at hcard; omega
  obtain ⟨u, w, hpair, huw, horig, huS, hwS⟩ := exists_apexSet_pair hbad
  have huw2 : u.2 = w.2 := horig
  have huw1 : u.1 ≠ w.1 := by
    intro h
    exact huw (Prod.ext h huw2)
  have hmissing : u ∉ G ∨ w ∉ G := by
    by_contra hcon
    push Not at hcon
    refine hapex ?_
    rw [hpair]
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hcon.1
    · rw [Finset.mem_singleton] at hx; subst hx; exact hcon.2
  have hkey : arank (projPts P m S) ≤ arank (projPts P m G) := by
    rcases hmissing with hu | hw
    · exact arank_projPts_le_of_shared hG hGS hstep huS hwS huw1 huw2 hu
    · exact arank_projPts_le_of_shared hG hGS hstep hwS huS (Ne.symm huw1)
        huw2.symm hw
  unfold projDim
  omega

/-- A face of rank one is a single Cayley vertex. -/
theorem eq_singleton_of_jrank_eq_one {S : Finset (JoinVertex P m)}
    (h : jrank P m S = 1) : ∃ w : JoinVertex P m, S = {w} := by
  classical
  obtain ⟨i, hi, hother⟩ := exists_unique_index_of_sum_step
    (fun k ↦ arank (factorPts P m S k)) (fun _ ↦ 0) (fun _ ↦ Nat.zero_le _)
    (by simpa [jrank] using h.symm)
  have hone : arank (factorPts P m S i) = 1 := by omega
  have hne : (factorPts P m S i).Nonempty := by
    rcases (factorPts P m S i).eq_empty_or_nonempty with hemp | hne
    · rw [hemp, arank_empty] at hone; omega
    · exact hne
  obtain ⟨v, w, hwS, hw1, -⟩ := hne
  refine ⟨w, ?_⟩
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hwS, fun x hxS ↦ ?_⟩
  have hxi : x.1 = i := by
    by_contra hne
    have hz : arank (factorPts P m S x.1) = 0 := (hother x.1 hne).symm
    have hx : (factorPts P m S x.1).Nonempty := ⟨_, vtx_mem_factorPts hxS⟩
    rw [arank_eq_zero_iff.mp hz] at hx
    exact absurd hx (by simp)
  have hxmem : vtx P x.2 ∈ factorPts P m S i := by
    rw [← hxi]; exact vtx_mem_factorPts hxS
  have hwmem : vtx P w.2 ∈ factorPts P m S i := by
    rw [← hw1]; exact vtx_mem_factorPts hwS
  have heq2 : vtx P x.2 = vtx P w.2 := eq_of_arank_le_one (le_of_eq hone) hxmem hwmem
  exact Prod.ext (hxi.trans hw1.symm) (vtx_injective P heq2)

/-- `hrank1` for the abstract good-vertex count. -/
theorem projDim_eq_zero_of_jrank_eq_one {S : Finset (JoinVertex P m)}
    (h : jrank P m S = 1) :
    projDim P m S = 0 ∧ (apexSet (origIndex P m) S).card = 1 := by
  classical
  obtain ⟨w, rfl⟩ := eq_singleton_of_jrank_eq_one h
  have hbad : badElts (origIndex P m) {w} = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [mem_badElts] at hx
    obtain ⟨hxs, y, hy, hyx, -⟩ := hx
    rw [Finset.mem_singleton] at hxs hy
    exact hyx (hy.trans hxs.symm)
  refine ⟨?_, apexSet_card_eq_one hbad ⟨w, Finset.mem_singleton_self w⟩⟩
  have hproj : projPts P m {w} = {vtx P w.2} := by
    ext v
    simp only [projPts, mem_iUnion, mem_factorPts, Finset.mem_singleton, mem_singleton_iff]
    constructor
    · rintro ⟨i, x, rfl, -, rfl⟩; rfl
    · rintro rfl; exact ⟨w.1, w, rfl, rfl, rfl⟩
  rw [projDim, hproj, arank_singleton]

/-- **The good-vertex count of a full simplex of the general polytopal
bad-vertex triangulation**: at least `projDim S + 1 = m(S) + 1` of its vertices
are original Cayley vertices. -/
theorem card_goodVertices_ge_projDim_succ {S : Finset (JoinVertex P m)}
    (hS : S ∈ faceFamily P m) (hS1 : 1 ≤ jrank P m S)
    {σ : Finset (Finset (JoinVertex P m))}
    (hσ : IsApexFlag (origIndex P m) (faceFamily P m) (jrank P m) S σ) :
    projDim P m S + 1 ≤ (goodVertices σ).card :=
  BadEdge.card_goodVertices_ge
    (fun _ _ _ _ hGS hstep ↦ projDim_le_succ_of_step hGS hstep)
    (fun _ _ _ hG' hGS hstep hapex hcard ↦
      projDim_le_of_bad_step hG' hGS hstep hapex hcard)
    (fun _ _ h ↦ projDim_eq_zero_of_jrank_eq_one h) hS hS1 hσ

/-! ### The whole Cayley join -/

theorem factorPts_topFace (i : Fin (m + 1)) :
    factorPts P m (topFace P m) i = (P.actualVertices : Set (CoordinateSpace n)) := by
  ext v
  constructor
  · rintro ⟨w, -, -, rfl⟩
    exact Finset.mem_coe.mpr (vtx_mem P w.2)
  · intro hv
    obtain ⟨k, rfl⟩ := exists_vtx P (Finset.mem_coe.mp hv)
    exact ⟨((i, k) : JoinVertex P m), Finset.mem_univ _, rfl, rfl⟩

theorem projPts_topFace :
    projPts P m (topFace P m) = (P.actualVertices : Set (CoordinateSpace n)) := by
  ext v
  simp only [projPts, mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    rw [factorPts_topFace] at hi
    exact hi
  · intro hv
    exact ⟨0, by rw [factorPts_topFace]; exact hv⟩

/-- The actual vertices of a full-dimensional polytope have full affine rank. -/
theorem arank_actualVertices :
    arank ((P.actualVertices : Set (CoordinateSpace n))) = n + 1 := by
  have hne : ((P.actualVertices : Set (CoordinateSpace n))).Nonempty := by
    obtain ⟨v, hv⟩ := P.actualVertices_nonempty
    exact ⟨v, Finset.mem_coe.mpr hv⟩
  have hspan : affineSpan ℝ ((P.actualVertices : Set (CoordinateSpace n))) = ⊤ := by
    rw [← affineSpan_convexHull, P.convexHull_actualVertices,
      FullDimensionalPolytope.carrier, affineSpan_convexHull, P.affineSpan_vertices]
  have hdir : vectorSpan ℝ ((P.actualVertices : Set (CoordinateSpace n))) = ⊤ := by
    rw [← direction_affineSpan, hspan, AffineSubspace.direction_top]
  rw [arank_of_nonempty hne, hdir]
  simp

theorem projDim_topFace : projDim P m (topFace P m) = n := by
  rw [projDim, projPts_topFace, arank_actualVertices]
  omega

theorem one_le_jrank_topFace : 1 ≤ jrank P m (topFace P m) := by
  have h : arank (factorPts P m (topFace P m) 0) = n + 1 := by
    rw [factorPts_topFace, arank_actualVertices]
  calc 1 ≤ arank (factorPts P m (topFace P m) 0) := by omega
    _ ≤ jrank P m (topFace P m) :=
        Finset.single_le_sum (f := fun i ↦ arank (factorPts P m (topFace P m) i))
          (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ 0)

/-- **The sharp good-vertex bound for the whole Cayley join**: every full
simplex of the bad-vertex triangulation of `Q = P * ⋯ * P` has at least
`n + 1` good vertices, `n` being the dimension of `P`. -/
theorem card_goodVertices_ge_of_top {σ : Finset (Finset (JoinVertex P m))}
    (hσ : IsApexFlag (origIndex P m) (faceFamily P m) (jrank P m) (topFace P m) σ) :
    n + 1 ≤ (goodVertices σ).card := by
  have := card_goodVertices_ge_projDim_succ (topFace_mem_faceFamily P m)
    (one_le_jrank_topFace) hσ
  rwa [projDim_topFace] at this

/-!
## Subsequent purity and geometric realization

The good-vertex bound here is stated for apex flags. `PolytopeFacet` proves
facet avoidance, `PullingPurity` proves the recursive purity criterion, and
`PolytopalPurity` instantiates it for the actual Cayley join and extends every
simplex to an apex flag. `PolytopalIntersection` supplies the actual geometric
realization, and `PolytopalLocalAcyclicity` consumes these results and the sharp
count above. These results are in subsequent modules to avoid an import cycle.
-/

end BadVertex
end AffineTverberg
