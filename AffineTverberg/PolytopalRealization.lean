import AffineTverberg.PolytopalPurity
import AffineTverberg.CayleyJoinExposed

set_option linter.style.header false

/-!
# The polytopal bad-vertex triangulation as a geometric realization

The carriers of the combinatorial face family of the Cayley join are genuine
exposed faces of the join (`sdCarrier_isExposed`), and the intersection of two
of them is the carrier of the intersection (`sdCarrier_inter`).  From this we
obtain the two geometric ingredients of a triangulation:

* `subset_of_sdPoint_mem_sdCarrier` — a vertex of the subdivision whose
  barycentre lies in a face of the join is a subset of that face (the apex of a
  face is off the affine span of any face of the family missing it,
  `sdPoint_notMem_affineSpan`);
* `affineIndependent_sdPoint` — **each simplex of the triangulation is affinely
  independent**, proved by induction along the cone structure of the pulling
  subdivision.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg
namespace BadVertex

open CayleyJoin PolytopeFace BadEdge

variable {n : ℕ} {P : FullDimensionalPolytope n} {m : ℕ}

/-! ### Carriers of the face family are faces of the join -/

/-- **The carrier of a face of the family is an exposed face of the Cayley
join.** -/
theorem sdCarrier_isExposed {S : Finset (JoinVertex P m)} (hS : S ∈ faceFamily P m) :
    IsExposed ℝ (polytopalJoinCarrier P m) (sdCarrier P m S) := by
  obtain ⟨C, rfl⟩ := (mem_faceFamily_iff P m).mp hS
  rw [sdCarrier_faceVertexSet, cayleyJoin_polytopalJoinCarrier P]
  exact isExposed_cayleyJoin fun i ↦ (C i).isFace

/-- The intersection of two faces of the family is a face of the family, and its
carrier is the intersection of the carriers. -/
theorem sdCarrier_inter {S T : Finset (JoinVertex P m)} (hS : S ∈ faceFamily P m)
    (hT : T ∈ faceFamily P m) :
    S ∩ T ∈ faceFamily P m ∧
      sdCarrier P m (S ∩ T) = sdCarrier P m S ∩ sdCarrier P m T := by
  classical
  obtain ⟨C, rfl⟩ := (mem_faceFamily_iff P m).mp hS
  obtain ⟨D, rfl⟩ := (mem_faceFamily_iff P m).mp hT
  have hface : ∀ i, P.IsFace ((C i).carrier ∩ (D i).carrier) :=
    fun i ↦ ((C i).isFace).inter ((D i).isFace)
  set E : Fin (m + 1) → PolytopeFaceIndex P :=
    fun i ↦ PolytopeFaceIndex.ofFace ((C i).carrier ∩ (D i).carrier) (hface i) with hE
  have hEcar : ∀ i, (E i).carrier = (C i).carrier ∩ (D i).carrier := by
    intro i
    rw [hE, PolytopeFaceIndex.carrier_ofFace]
  have hvert : faceVertexSet P m E = faceVertexSet P m C ∩ faceVertexSet P m D := by
    ext w
    simp only [Finset.mem_inter, mem_faceVertexSet, hEcar, mem_inter_iff]
  refine ⟨hvert ▸ (mem_faceFamily_iff P m).mpr ⟨E, rfl⟩, ?_⟩
  rw [← hvert, sdCarrier_faceVertexSet, sdCarrier_faceVertexSet, sdCarrier_faceVertexSet]
  simp only [hEcar]
  exact cayleyJoin_inter _ _

/-- A Cayley vertex lies in the carrier of a face of the family exactly when it
belongs to that face. -/
theorem pt_mem_sdCarrier_iff {S : Finset (JoinVertex P m)} (hS : S ∈ faceFamily P m)
    {w : JoinVertex P m} : pt P m w ∈ sdCarrier P m S ↔ w ∈ S := by
  obtain ⟨C, rfl⟩ := (mem_faceFamily_iff P m).mp hS
  rw [sdCarrier_faceVertexSet, pt, copy_mem_cayleyJoin_iff, mem_faceVertexSet]

/-! ### Subdivision vertices -/

theorem sdPoint_singleton (w : JoinVertex P m) : sdPoint P m {w} = pt P m w := by
  simp [sdPoint]

theorem sdPoint_pair {u w : JoinVertex P m} (huw : u ≠ w) :
    sdPoint P m {u, w} = (2 : ℝ)⁻¹ • pt P m u + (2 : ℝ)⁻¹ • pt P m w := by
  rw [sdPoint, Finset.sum_pair huw, Finset.card_insert_of_notMem (by simpa using huw),
    Finset.card_singleton]
  norm_num

theorem apexSet_card_le_two (S : Finset (JoinVertex P m)) :
    (apexSet (origIndex P m) S).card ≤ 2 := by
  by_cases h : (badElts (origIndex P m) S).Nonempty
  · exact le_of_eq (apexSet_card_eq_two h)
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    rcases S.eq_empty_or_nonempty with rfl | hne
    · simp [apexSet_empty]
    · rw [apexSet_card_eq_one h hne]; norm_num

theorem sdPoint_mem_join (a : Finset (JoinVertex P m)) (hne : a.Nonempty) :
    sdPoint P m a ∈ polytopalJoinCarrier P m := by
  rw [← sdCarrier_topFace]
  exact sdPoint_mem_sdCarrier P m (Finset.subset_univ a) hne

/-- **A subdivision vertex inside a face of the family is a subset of it.** -/
theorem subset_of_sdPoint_mem_sdCarrier {a G : Finset (JoinVertex P m)}
    (hG : G ∈ faceFamily P m) (hne : a.Nonempty) (hcard : a.card ≤ 2)
    (hmem : sdPoint P m a ∈ sdCarrier P m G) : a ⊆ G := by
  classical
  interval_cases h : a.card
  · exact absurd h (by simpa using (Finset.card_pos.mpr hne).ne')
  · obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp h
    rw [sdPoint_singleton] at hmem
    have := (pt_mem_sdCarrier_iff hG).mp hmem
    simpa using this
  · obtain ⟨u, w, huw, rfl⟩ := Finset.card_eq_two.mp h
    rw [sdPoint_pair huw] at hmem
    have hu : pt P m u ∈ polytopalJoinCarrier P m := by
      rw [← sdPoint_singleton u]
      exact sdPoint_mem_join {u} (Finset.singleton_nonempty u)
    have hw : pt P m w ∈ polytopalJoinCarrier P m := by
      rw [← sdPoint_singleton w]
      exact sdPoint_mem_join {w} (Finset.singleton_nonempty w)
    have hextreme : IsExtreme ℝ (polytopalJoinCarrier P m) (sdCarrier P m G) :=
      (sdCarrier_isExposed hG).isExtreme
    have hopen : (2 : ℝ)⁻¹ • pt P m u + (2 : ℝ)⁻¹ • pt P m w ∈
        openSegment ℝ (pt P m u) (pt P m w) :=
      ⟨(2 : ℝ)⁻¹, (2 : ℝ)⁻¹, by norm_num, by norm_num, by norm_num, rfl⟩
    have hopen' : (2 : ℝ)⁻¹ • pt P m u + (2 : ℝ)⁻¹ • pt P m w ∈
        openSegment ℝ (pt P m w) (pt P m u) := by
      rw [openSegment_symm]; exact hopen
    have huG := hextreme.left_mem_of_mem_openSegment hu hw hmem hopen
    have hwG := hextreme.left_mem_of_mem_openSegment hw hu hmem hopen'
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact (pt_mem_sdCarrier_iff hG).mp huG
    · rw [Finset.mem_singleton] at hx'
      subst hx'
      exact (pt_mem_sdCarrier_iff hG).mp hwG

/-- **The apex of a face is off the affine span of any face of the family
missing it.** -/
theorem sdPoint_notMem_affineSpan {S G : Finset (JoinVertex P m)}
    (hG : G ∈ faceFamily P m) (hna : ¬ apexSet (origIndex P m) S ⊆ G) :
    sdPoint P m (apexSet (origIndex P m) S) ∉ affineSpan ℝ (sdCarrier P m G) := by
  intro hspan
  have hne : (apexSet (origIndex P m) S).Nonempty := apexSet_nonempty_of_not_subset hna
  have hjoin : sdPoint P m (apexSet (origIndex P m) S) ∈ polytopalJoinCarrier P m :=
    sdPoint_mem_join _ hne
  have hmem := mem_of_mem_affineSpan_exposed (sdCarrier_isExposed hG) hjoin hspan
  exact hna (subset_of_sdPoint_mem_sdCarrier hG hne (apexSet_card_le_two S) hmem)

/-! ### Affine independence of the simplices -/

section Insert

variable {V E : Type*} [DecidableEq V] [AddCommGroup E] [Module ℝ E]

/-- Inserting a point off the affine span preserves affine independence of a
family indexed by a finite set. -/
theorem affineIndependent_insert_finset {p : V → E} {a : V} {τ : Finset V}
    (hτ : AffineIndependent ℝ (fun v : τ ↦ p v.val)) (ha : a ∉ τ)
    (hspan : p a ∉ affineSpan ℝ (p '' (τ : Set V))) :
    AffineIndependent ℝ (fun v : (insert a τ : Finset V) ↦ p v.val) := by
  classical
  set i : ↑(insert a τ : Finset V) := ⟨a, Finset.mem_insert_self a τ⟩ with hi
  refine AffineIndependent.affineIndependent_of_notMem_span (i := i) ?_ ?_
  · have hmap : ∀ x : {x : ↑(insert a τ : Finset V) // x ≠ i}, (x.1).val ∈ τ := by
      rintro ⟨⟨y, hy⟩, hne⟩
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact absurd (Subtype.ext rfl) hne
      · exact hy'
    let g : {x : ↑(insert a τ : Finset V) // x ≠ i} → ↑τ :=
      fun x ↦ ⟨(x.1).val, hmap x⟩
    have hginj : Function.Injective g := by
      rintro ⟨⟨x, hx⟩, hxne⟩ ⟨⟨y, hy⟩, hyne⟩ hxy
      simp only [g, Subtype.mk.injEq] at hxy
      subst hxy
      rfl
    exact hτ.comp_embedding ⟨g, hginj⟩
  · intro hmem
    refine hspan ?_
    have hsub : (fun v : ↑(insert a τ : Finset V) ↦ p v.val) ''
        {x | x ≠ i} ⊆ p '' (τ : Set V) := by
      rintro _ ⟨⟨y, hy⟩, hne, rfl⟩
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · exact absurd (Subtype.ext rfl) hne
      · exact ⟨y, hy', rfl⟩
    exact affineSpan_mono ℝ hsub hmem

end Insert

/-- **Every simplex of the polytopal bad-vertex triangulation is affinely
independent.** -/
theorem affineIndependent_sdPoint {S : Finset (JoinVertex P m)}
    {σ : Finset (Finset (JoinVertex P m))} (hσ : σ ∈ sdQ P m S) :
    AffineIndependent ℝ (fun a : σ ↦ sdPoint P m a.val) := by
  classical
  induction hk : S.card using Nat.strong_induction_on generalizing S σ with
  | _ k ih =>
    subst hk
    rcases mem_sdPoset_iff.mp hσ with rfl | ⟨G, hGfam, hGS, hna, hcase⟩
    · have : IsEmpty ↑(∅ : Finset (Finset (JoinVertex P m))) :=
        ⟨fun x ↦ Finset.notMem_empty x.1 x.2⟩
      exact affineIndependent_of_subsingleton ℝ _
    · have hlt : G.card < S.card := card_lt_of_apexSet_not_subset (orig := origIndex P m) hGS hna
      rcases hcase with h | ⟨τ, hτ, rfl⟩
      · exact ih G.card hlt h rfl
      · have hτind := ih G.card hlt hτ rfl
        have hτsub : ∀ b ∈ τ, b ⊆ G := fun b hb ↦ sdPoset_vertex_subset hτ hb
        have hanot : apexSet (origIndex P m) S ∉ τ := by
          intro hmem
          exact hna (hτsub _ hmem)
        refine affineIndependent_insert_finset hτind hanot ?_
        have himg : sdPoint P m '' (τ : Set (Finset (JoinVertex P m))) ⊆
            sdCarrier P m G := by
          rintro _ ⟨b, hb, rfl⟩
          exact sdPoint_mem_sdCarrier P m (hτsub b hb)
            (sdPoset_vertex_nonempty hτ hb)
        intro hspan
        exact sdPoint_notMem_affineSpan hGfam hna (affineSpan_mono ℝ himg hspan)

end BadVertex
end AffineTverberg
