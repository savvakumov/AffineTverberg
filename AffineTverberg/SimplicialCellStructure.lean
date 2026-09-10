import AffineTverberg.SimplicialGlobalMap

set_option linter.style.header false

/-!
# The cell structure of the simplicial deleted join

This file records the intersection property needed for the incidence-space
fibers in the simplicial-ball proof.  Deleted-join cells are joins of tuples
of boundary simplices.  Two such cells meet in the join of the componentwise
intersections of their vertex sets, and that tuple is again a deleted-join
cell.  This is the geometric reason that every point has a least cell.
-/

noncomputable section

open Set
open scoped BigOperators

namespace AffineTverberg

section Intersections

variable {e n m : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- A nonempty subface of a boundary simplex is again a boundary simplex. -/
theorem IsBoundarySimplicialFace.mono
    {s t : Finset (CoordinateSpace e)}
    (hs : IsBoundarySimplicialFace n K s) (hts : t ⊆ s)
    (ht : t.Nonempty) : IsBoundarySimplicialFace n K t := by
  obtain ⟨hsK, ridge, hridge, hsridge⟩ := hs
  exact ⟨K.down_closed hsK hts ht, ridge, hridge, hts.trans hsridge⟩

/-- Componentwise intersection preserves the deleted-cell conditions. -/
def simplicialDeletedCellInter
    (F G : SimplicialDeletedCellIndex n K m) :
    SimplicialDeletedCellIndex n K m := by
  refine ⟨fun i ↦ F.val i ∩ G.val i, ?_⟩
  constructor
  · intro i
    rcases (F.val i ∩ G.val i).eq_empty_or_nonempty with hempty | hne
    · exact Or.inl hempty
    · right
      rcases F.property.1 i with hFempty | hF
      · rw [hFempty] at hne
        simp at hne
      · exact hF.mono Finset.inter_subset_left hne
  · intro i j hij
    exact Disjoint.mono Finset.inter_subset_left Finset.inter_subset_left
      (F.property.2 hij)

@[simp]
theorem simplicialDeletedCellInter_val
    (F G : SimplicialDeletedCellIndex n K m) :
    (simplicialDeletedCellInter F G).val = fun i ↦ F.val i ∩ G.val i :=
  rfl

/-- The geometric intersection of two deleted-join cells is their
componentwise simplicial intersection. -/
theorem joinCellCarrier_simplicialDeletedCellInter
    (F G : SimplicialDeletedCellIndex n K m) :
    joinCellCarrier (simplicialDeletedCellInter F G).val =
      joinCellCarrier F.val ∩ joinCellCarrier G.val := by
  apply Set.Subset.antisymm
  · exact Set.subset_inter
      (joinCellCarrier_mono fun i ↦ Finset.inter_subset_left)
      (joinCellCarrier_mono fun i ↦ Finset.inter_subset_right)
  · rintro z ⟨hzF, hzG⟩
    obtain ⟨t, x, ht0, ht1, hxF, hrepr⟩ :=
      exists_repr_of_mem_joinCellCarrier hzF
    rw [hrepr]
    apply sum_smul_copy_mem_joinCellCarrier t x ht0 ht1
    intro i hti
    have hcoord := congrFun hrepr i
    rw [sum_smul_copy_apply] at hcoord
    have hsnd : (z i).2 = t i := by simp [hcoord]
    have hzpos : 0 < (z i).2 := by simpa [hsnd] using hti
    have hnorm : (z i).2⁻¹ • (z i).1 = x i := by
      rw [hcoord]
      rw [smul_smul, inv_mul_cancel₀ hti.ne', one_smul]
    have hxG : x i ∈ convexHull ℝ (G.val i : Set (CoordinateSpace e)) := by
      rw [← hnorm]
      exact normalized_component_mem_face_of_mem_joinCellCarrier hzG i hzpos
    have hxFi := hxF i hti
    have hFi : F.val i ∈ K.faces := by
      rcases F.property.1 i with hempty | hboundary
      · rw [hempty] at hxFi
        simp at hxFi
      · exact hboundary.1
    have hGi : G.val i ∈ K.faces := by
      rcases G.property.1 i with hempty | hboundary
      · rw [hempty] at hxG
        simp at hxG
      · exact hboundary.1
    change x i ∈ convexHull ℝ ((F.val i ∩ G.val i : Finset (CoordinateSpace e)) :
      Set (CoordinateSpace e))
    have hinter : x i ∈
        convexHull ℝ (F.val i : Set (CoordinateSpace e)) ∩
          convexHull ℝ (G.val i : Set (CoordinateSpace e)) := ⟨hxFi, hxG⟩
    rw [K.convexHull_inter_convexHull hFi hGi] at hinter
    simpa only [Finset.coe_inter] using hinter

/-- The componentwise intersection of a nonempty finite family of simplicial
deleted cells. -/
def simplicialInterCell
    {S : Finset (SimplicialDeletedCellIndex n K m)} (hS : S.Nonempty) :
    SimplicialDeletedCellIndex n K m := by
  refine ⟨S.inf' hS (fun F ↦ F.val), ?_⟩
  apply Finset.inf'_mem (BoundaryDeletedJoinCells n K m)
  · intro f hf g hg
    exact (simplicialDeletedCellInter (⟨f, hf⟩ : SimplicialDeletedCellIndex n K m)
      (⟨g, hg⟩ : SimplicialDeletedCellIndex n K m)).property
  · intro F _hF
    exact F.property

theorem simplicialInterCell_carrier
    {S : Finset (SimplicialDeletedCellIndex n K m)} (hS : S.Nonempty) :
    joinCellCarrier (simplicialInterCell hS).val =
      ⋂ F ∈ S, joinCellCarrier F.val := by
  classical
  induction S using Finset.induction_on with
  | empty => simp at hS
  | @insert F S hFS ih =>
      by_cases hS' : S.Nonempty
      · have hcell : simplicialInterCell (Finset.insert_nonempty F S) =
            simplicialDeletedCellInter F (simplicialInterCell hS') := by
          apply Subtype.ext
          change (insert F S).inf' (Finset.insert_nonempty F S)
              (fun C : SimplicialDeletedCellIndex n K m ↦ C.val) =
            F.val ⊓ S.inf' hS' (fun C ↦ C.val)
          rw [show (insert F S).inf' (Finset.insert_nonempty F S)
              (fun C : SimplicialDeletedCellIndex n K m ↦ C.val) =
                F.val ⊓ S.inf' hS' (fun C ↦ C.val) from
              Finset.inf'_insert hS' (fun C : SimplicialDeletedCellIndex n K m ↦ C.val)]
        rw [hcell, joinCellCarrier_simplicialDeletedCellInter,
          ih hS']
        ext z
        simp
      · have hSempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS'
        subst S
        have hcell : simplicialInterCell (Finset.insert_nonempty F ∅) = F := by
          apply Subtype.ext
          simp [simplicialInterCell]
        rw [hcell]
        ext z
        simp

/-! ## The least cell through a point -/

/-- The finite set of simplicial deleted cells which contain `z`. -/
def simplicialCellsThrough (hfin : K.faces.Finite)
    (z : PolytopalJoinAmbient e m) :
    Finset (SimplicialDeletedCellIndex n K m) := by
  classical
  letI : Fintype (SimplicialDeletedCellIndex n K m) :=
    Set.Finite.fintype (boundaryDeletedJoinCells_finite (n := n) (m := m) K hfin)
  exact Finset.univ.filter fun F ↦ z ∈ joinCellCarrier F.val

theorem mem_simplicialCellsThrough_iff
    (hfin : K.faces.Finite) {z : PolytopalJoinAmbient e m}
    {F : SimplicialDeletedCellIndex n K m} :
    F ∈ simplicialCellsThrough (n := n) hfin z ↔ z ∈ joinCellCarrier F.val := by
  classical
  let : Fintype (SimplicialDeletedCellIndex n K m) :=
    Set.Finite.fintype (boundaryDeletedJoinCells_finite (n := n) (m := m) K hfin)
  unfold simplicialCellsThrough
  rw [Finset.mem_filter]
  constructor
  · exact And.right
  · intro hF
    exact ⟨Finset.mem_univ F, hF⟩

theorem simplicialCellsThrough_nonempty
    (hfin : K.faces.Finite) {z : PolytopalJoinAmbient e m}
    (hz : z ∈ simplicialDeletedJoinCarrier n K m) :
    (simplicialCellsThrough (n := n) hfin z).Nonempty := by
  obtain ⟨f, hf, hzf⟩ := (mem_simplicialDeletedJoinCarrier_iff K z).mp hz
  exact ⟨⟨f, hf⟩, (mem_simplicialCellsThrough_iff (n := n) hfin).2 hzf⟩

/-- The least simplicial deleted cell through `z`, obtained by intersecting
all cells which contain it. -/
def simplicialMinimalCell (hfin : K.faces.Finite)
    {z : PolytopalJoinAmbient e m}
  (hz : z ∈ simplicialDeletedJoinCarrier n K m) :
    SimplicialDeletedCellIndex n K m :=
  simplicialInterCell (simplicialCellsThrough_nonempty (n := n) hfin hz)

theorem simplicialMinimalCell_carrier
    (hfin : K.faces.Finite) {z : PolytopalJoinAmbient e m}
    (hz : z ∈ simplicialDeletedJoinCarrier n K m) :
    joinCellCarrier (simplicialMinimalCell hfin hz).val =
      ⋂ F ∈ simplicialCellsThrough (n := n) hfin z, joinCellCarrier F.val :=
  simplicialInterCell_carrier _

theorem mem_simplicialMinimalCell
    (hfin : K.faces.Finite) {z : PolytopalJoinAmbient e m}
    (hz : z ∈ simplicialDeletedJoinCarrier n K m) :
    z ∈ joinCellCarrier (simplicialMinimalCell hfin hz).val := by
  rw [simplicialMinimalCell_carrier]
  exact Set.mem_iInter₂.2 fun F hF ↦
    (mem_simplicialCellsThrough_iff (n := n) hfin).1 hF

theorem simplicialMinimalCell_subset
    (hfin : K.faces.Finite) {z : PolytopalJoinAmbient e m}
    (hz : z ∈ simplicialDeletedJoinCarrier n K m)
    (F : SimplicialDeletedCellIndex n K m)
    (hF : z ∈ joinCellCarrier F.val) :
    joinCellCarrier (simplicialMinimalCell hfin hz).val ⊆
      joinCellCarrier F.val := by
  rw [simplicialMinimalCell_carrier]
  exact Set.biInter_subset_of_mem
    ((mem_simplicialCellsThrough_iff (n := n) hfin).2 hF)

end Intersections

end AffineTverberg
