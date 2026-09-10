import AffineTverberg.CellShellingTransport

set_option linter.style.header false

/-!
# Supported forms of the cell-shelling combinatorics

A `ShellableGluing.CellShelling` certificate displays a family `S` of maximal
cells, and recursively the overlap families of the attaching steps.  Every cell
occurring anywhere in such a certificate lies below one of the initially
displayed cells, i.e. in `cellSupport S`: this is the content of the overlap
condition, since the overlap family has the same support as the family of
intersections with the new cell.

Consequently a hypothesis on the dimension function only has to be imposed on
`cellSupport S`, not on the whole cell poset.  `CellShelling.dimShift` is the
form used by the polytopal application: the geometric shelling of the visible
facets is graded by the *affine rank* `arank` of a face, while the acyclic
gluing theorem for the good subcomplexes is graded by its *dimension*, one
less.  The shift is legitimate exactly because every cell occurring in the
certificate is a face of the polytope, where the two gradings differ by one.
-/

noncomputable section

namespace AffineTverberg
namespace Simplicial

variable {C : Type*} [SemilatticeInf C] [OrderBot C] [DecidableEq C]

omit [DecidableEq C] in
/-- A displayed nonempty cell lies in the support of its family. -/
theorem mem_cellSupport_of_mem {S : Finset C} {c : C} (hc : c ∈ S) (hne : c ≠ ⊥) :
    c ∈ cellSupport S :=
  ⟨hne, c, hc, le_rfl⟩

omit [DecidableEq C] in
theorem cellSupport_mono {S T : Finset C} (h : S ⊆ T) : cellSupport S ⊆ cellSupport T := by
  rintro e ⟨hne, c, hc, hec⟩
  exact ⟨hne, c, h hc, hec⟩

/-- The support of the family of intersections with a new cell is contained in
the support of the enlarged family. -/
theorem cellSupport_image_inf_subset (S : Finset C) (c : C) :
    cellSupport (S.image fun d ↦ c ⊓ d) ⊆ cellSupport (insert c S) := by
  rintro e ⟨hne, d, hd, hed⟩
  obtain ⟨d', -, rfl⟩ := Finset.mem_image.mp hd
  exact ⟨hne, c, Finset.mem_insert_self c S, hed.trans inf_le_left⟩

/-- **Shifting the grading of a cell shelling.**  If the two dimension
functions differ by one on every cell below a displayed cell, the certificate
transports to the shifted grading.  Positivity of the original dimension on
those cells is automatic from the hypothesis. -/
theorem CellShelling.dimShift {dim dim' : C → ℕ} {n : ℕ} {S : Finset C}
    (h : CellShelling dim n S)
    (hdim : ∀ c ∈ cellSupport S, dim' c + 1 = dim c) :
    CellShelling dim' (n - 1) S := by
  induction h with
  | single c hc =>
      have hc' := hdim c (mem_cellSupport_of_mem (Finset.mem_singleton_self c) hc)
      have : dim c - 1 = dim' c := by omega
      rw [this]
      exact CellShelling.single c hc
  | @attach n S T c hS hc hdimc hnew hT hoverlap ihS ihT =>
      -- every cell of `T` lies below the new cell, hence in the support
      have hTsupp : cellSupport T ⊆ cellSupport (insert c S) := by
        rw [← hoverlap]
        exact cellSupport_image_inf_subset S c
      have hSsupp : cellSupport S ⊆ cellSupport (insert c S) :=
        cellSupport_mono (Finset.subset_insert c S)
      -- the ambient degree is positive
      obtain ⟨t, ht⟩ := hT.nonempty
      obtain ⟨htne, htdim⟩ := hT.pure t ht
      have htsupp : t ∈ cellSupport (insert c S) :=
        hTsupp (mem_cellSupport_of_mem ht htne)
      have hn1 : 1 ≤ n := by
        have := hdim t htsupp
        omega
      have hcdim : dim' c = n := by
        have := hdim c (mem_cellSupport_of_mem (Finset.mem_insert_self c S) hc)
        omega
      have hS' : CellShelling dim' ((n - 1) + 1) S := by
        have := ihS fun e he ↦ hdim e (hSsupp he)
        simpa [show (n - 1) + 1 = n by omega, show n + 1 - 1 = n by omega] using this
      have hT' : CellShelling dim' (n - 1) T := by
        have := ihT fun e he ↦ hdim e (hTsupp he)
        simpa using this
      have := CellShelling.attach (dim := dim') (n := n - 1) c hS' hc
        (by omega) hnew hT' hoverlap
      simpa [show (n - 1) + 1 = n by omega, show n + 1 - 1 = n by omega] using this

end Simplicial
end AffineTverberg
