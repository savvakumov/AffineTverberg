import AffineTverberg.ShellableGluing

set_option linter.style.header false

/-!
# Transporting a cell shelling along a map of cell posets

A `ShellableGluing.CellShelling` certificate is purely combinatorial: it refers
to the meet, the bottom element, the dimension function and the cell supports.
Consequently it transports along any map of cell posets preserving these data.

The exact hypotheses used here are:

* `f` is injective and preserves binary meets;
* `f c = ⊥` exactly when `c = ⊥`;
* `f` preserves the dimension function.

No downward-surjectivity assumption is needed for the shelling transport:
equality of source supports expresses cofinality of the two finite families,
and monotonicity carries that cofinality to the target. The stronger formula
`cellSupport_image` does need downward surjectivity and is recorded separately.
In particular, a face preimage under a noninjective linear projection need not
have all its subfaces in the image of the face map.

This is the interface used to turn the geometric shelling of the visible facets
of a polytope (`VisibleShelling.lean`) into a shelling certificate for another
indexing of the same faces, for instance the faces of a Cayley join used by
`BadVertex.dimCell` and `BadVertex.goodAssign`.
-/

noncomputable section

namespace AffineTverberg
namespace Simplicial

variable {C D : Type*} [SemilatticeInf C] [OrderBot C] [DecidableEq C]
  [SemilatticeInf D] [OrderBot D] [DecidableEq D]

section Map

variable {f : C → D}

omit [OrderBot C] [DecidableEq C] [OrderBot D] [DecidableEq D] in
/-- A meet-preserving map is monotone. -/
theorem monotone_of_map_inf (hinf : ∀ c d, f (c ⊓ d) = f c ⊓ f d) : Monotone f := by
  intro a b hab
  have : f a = f a ⊓ f b := by rw [← hinf, inf_eq_left.mpr hab]
  exact le_of_eq_of_le this inf_le_right

omit [DecidableEq C] in
/-- **Cell supports transport**: the support of an image family is the image of
the support. -/
theorem cellSupport_image (hinf : ∀ c d, f (c ⊓ d) = f c ⊓ f d)
    (hbot : ∀ c, f c = ⊥ ↔ c = ⊥)
    (hdown : ∀ (c : C) (e : D), e ≤ f c → ∃ e' : C, e' ≤ c ∧ f e' = e)
    (X : Finset C) : cellSupport (X.image f) = f '' cellSupport X := by
  have hmono := monotone_of_map_inf hinf
  ext e
  simp only [cellSupport, Set.mem_ofPred_eq, Set.mem_image, Finset.mem_image]
  constructor
  · rintro ⟨hne, d, ⟨c, hc, rfl⟩, hed⟩
    obtain ⟨e', hle, rfl⟩ := hdown c e hed
    exact ⟨e', ⟨fun h ↦ hne (by rw [h]; exact (hbot ⊥).2 rfl), c, hc, hle⟩, rfl⟩
  · rintro ⟨e', ⟨hne, c, hc, hle⟩, rfl⟩
    exact ⟨fun h ↦ hne ((hbot e').1 h), f c, ⟨c, hc, rfl⟩, hmono hle⟩

omit [DecidableEq C] in
/-- Equal cell supports remain equal after any monotone bottom-preserving map.
Only cofinality of the displayed families is needed; target faces need not
all be images of source faces. -/
theorem cellSupport_image_eq_of_eq (hmono : Monotone f) (hbot : f ⊥ = ⊥)
    {S T : Finset C} (h : cellSupport S = cellSupport T) :
    cellSupport (S.image f) = cellSupport (T.image f) := by
  have hsub {U W : Finset C} (hUW : cellSupport U ⊆ cellSupport W) :
      cellSupport (U.image f) ⊆ cellSupport (W.image f) := by
    rintro e ⟨he, c, hc, hec⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hc
    have ha0 : a ≠ ⊥ := by
      intro ha0
      rw [ha0, hbot] at hec
      exact he (le_bot_iff.mp hec)
    obtain ⟨_, b, hb, hab⟩ := hUW ⟨ha0, a, ha, le_rfl⟩
    exact ⟨he, f b, Finset.mem_image_of_mem f hb, hec.trans (hmono hab)⟩
  exact Set.Subset.antisymm (hsub h.subset) (hsub h.symm.subset)

/-- **A cell shelling transports along a map of cell posets.** No downward
surjectivity is imposed on the image of the cell map. -/
theorem CellShelling.map {dimC : C → ℕ} {dimD : D → ℕ}
    (hinj : Function.Injective f)
    (hinf : ∀ c d, f (c ⊓ d) = f c ⊓ f d)
    (hbot : ∀ c, f c = ⊥ ↔ c = ⊥)
    (hdim : ∀ c, dimD (f c) = dimC c)
    {n : ℕ} {S : Finset C} (h : CellShelling dimC n S) :
    CellShelling dimD n (S.image f) := by
  induction h with
  | single c hc =>
      rw [Finset.image_singleton, ← hdim c]
      exact CellShelling.single (f c) fun hcon ↦ hc ((hbot c).1 hcon)
  | attach c hS hc hdimc hnew hT hoverlap ihS ihT =>
      rw [Finset.image_insert]
      refine CellShelling.attach (f c) ihS (fun hcon ↦ hc ((hbot c).1 hcon))
        (by rw [hdim, hdimc]) ?_ ihT ?_
      · intro hcon
        obtain ⟨c', hc', hcc⟩ := Finset.mem_image.mp hcon
        exact hnew (hinj hcc ▸ hc')
      · have himg : ∀ X : Finset C, ((X.image f).image fun d ↦ f c ⊓ d)
            = (X.image fun d ↦ c ⊓ d).image f := by
          intro X
          rw [Finset.image_image, Finset.image_image]
          exact Finset.image_congr fun d _ ↦ (hinf c d).symm
        rw [himg]
        exact cellSupport_image_eq_of_eq (monotone_of_map_inf hinf)
          ((hbot ⊥).mpr rfl) hoverlap

end Map

end Simplicial
end AffineTverberg
