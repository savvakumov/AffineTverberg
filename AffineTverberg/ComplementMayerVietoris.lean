import AffineTverberg.DeletedJoinDualityReduction

set_option linter.style.header false

/-!
# Mayer-Vietoris for complements of two closed sets

This is the complement side of the classical induction that proves Alexander
duality for a subpolyhedron of a sphere: for closed subsets `S`, `T` of a
space `X` the two open sets `Sᶜ` and `Tᶜ` cover `(S ∩ T)ᶜ` and intersect in
`(S ∪ T)ᶜ`, so the project's singular Mayer-Vietoris sequence of an open
cover applies verbatim.

The consequence proved here is the induction step in vanishing form:

`isZero_homology_compl_union` : if the complements of `S` and of `T` have
vanishing homology in degree `i`, and the complement of `S ∩ T` has vanishing
homology in degree `i + 1`, then the complement of `S ∪ T` has vanishing
homology in degree `i`.

Nothing about duality is used or claimed; this is one verified ingredient of
the missing `FinitePolyhedralAlexanderDualityStatement`, whose other main
ingredient is the base case (acyclicity of the complement of a topologically
embedded closed cell), not proved here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg

namespace AffChain

variable {X : Type} [TopologicalSpace X] (S T : Set X)

/-- The ambient space of the complement Mayer-Vietoris sequence. -/
abbrev complAmbient : TopCat.{0} := TopCat.of ↥(S ∩ T)ᶜ

/-- The first piece of the complement cover: the points outside `S`. -/
def complPieceLeft : Set ↥(complAmbient S T) := Subtype.val ⁻¹' Sᶜ

/-- The second piece of the complement cover: the points outside `T`. -/
def complPieceRight : Set ↥(complAmbient S T) := Subtype.val ⁻¹' Tᶜ

theorem isOpen_complPieceLeft (hS : IsClosed S) : IsOpen (complPieceLeft S T) :=
  hS.isOpen_compl.preimage continuous_subtype_val

theorem isOpen_complPieceRight (hT : IsClosed T) : IsOpen (complPieceRight S T) :=
  hT.isOpen_compl.preimage continuous_subtype_val

theorem complPiece_cover (x : ↥(complAmbient S T)) :
    x ∈ complPieceLeft S T ∨ x ∈ complPieceRight S T := by
  by_cases hx : (x : X) ∈ S
  · exact Or.inr fun hT ↦ x.property ⟨hx, hT⟩
  · exact Or.inl hx

theorem complPiece_inter :
    complPieceLeft S T ∩ complPieceRight S T = Subtype.val ⁻¹' (S ∪ T)ᶜ := by
  ext x
  constructor
  · rintro ⟨hS, hT⟩ hx
    rcases hx with hx | hx
    · exact hS hx
    · exact hT hx
  · intro hx
    exact ⟨fun h ↦ hx (Or.inl h), fun h ↦ hx (Or.inr h)⟩

/-- The left piece is the actual complement of `S`. -/
def complPieceLeftHomeomorph : ↥(complPieceLeft S T) ≃ₜ ↥(Sᶜ) :=
  subtypePreimageHomeomorph fun _ hx h ↦ hx h.1

/-- The right piece is the actual complement of `T`. -/
def complPieceRightHomeomorph : ↥(complPieceRight S T) ≃ₜ ↥(Tᶜ) :=
  subtypePreimageHomeomorph fun _ hx h ↦ hx h.2

/-- The intersection of the two pieces is the actual complement of `S ∪ T`. -/
def complPieceInterHomeomorph :
    ↥(complPieceLeft S T ∩ complPieceRight S T) ≃ₜ ↥((S ∪ T)ᶜ) :=
  (Homeomorph.setCongr (complPiece_inter S T)).trans
    (subtypePreimageHomeomorph fun _ hx h ↦ hx (Or.inl h.1))

/-- The middle term of the Mayer-Vietoris sequence vanishes as soon as the
homology of both pieces does. -/
theorem isZero_pairCx_homology {C D : ChainComplex (ModuleCat.{0} ℝ) ℕ} (i : ℕ)
    (hC : IsZero (C.homology i)) (hD : IsZero (D.homology i)) :
    IsZero ((pairCx C D).homology i) := by
  refine IsZero.of_iso ?_ (homologyPairIso C D i)
  rw [IsZero.iff_id_eq_zero, ← biprod.total, hC.eq_of_tgt biprod.fst 0,
    hD.eq_of_tgt biprod.snd 0]
  simp

/-- **The complement induction step.** If the complements of the closed sets
`S` and `T` have vanishing real singular homology in degree `i`, and the
complement of `S ∩ T` has vanishing homology in degree `i + 1`, then the
complement of `S ∪ T` has vanishing homology in degree `i`. -/
theorem isZero_homology_compl_union (hS : IsClosed S) (hT : IsClosed T) (i : ℕ)
    (hSc : IsZero ((realSingularHomology i).obj (TopCat.of ↥(Sᶜ))))
    (hTc : IsZero ((realSingularHomology i).obj (TopCat.of ↥(Tᶜ))))
    (hinter : IsZero ((realSingularHomology (i + 1)).obj (TopCat.of ↥(S ∩ T)ᶜ))) :
    IsZero ((realSingularHomology i).obj (TopCat.of ↥((S ∪ T)ᶜ))) := by
  have hU : IsZero ((realSingularHomology i).obj
      (TopCat.of ↥(complPieceLeft S T))) :=
    ModuleCat.isZero_iff_subsingleton.mpr
      ((realSingularHomology_subsingleton_iff_of_homotopyEquiv
        (complPieceLeftHomeomorph S T).toHomotopyEquiv i).mpr
          (ModuleCat.subsingleton_of_isZero hSc))
  have hV : IsZero ((realSingularHomology i).obj
      (TopCat.of ↥(complPieceRight S T))) :=
    ModuleCat.isZero_iff_subsingleton.mpr
      ((realSingularHomology_subsingleton_iff_of_homotopyEquiv
        (complPieceRightHomeomorph S T).toHomotopyEquiv i).mpr
          (ModuleCat.subsingleton_of_isZero hTc))
  have hpair : IsZero ((pairCx (singChains (subSpace (complPieceLeft S T)))
      (singChains (subSpace (complPieceRight S T)))).homology i) :=
    isZero_pairCx_homology i hU hV
  have hex := mv_exact_inter (complPieceLeft S T) (complPieceRight S T)
    (isOpen_complPieceLeft S T hS) (isOpen_complPieceRight S T hT)
    (complPiece_cover S T) i
  have hf : (ShortComplex.mk
      (mvDelta (complPieceLeft S T) (complPieceRight S T)
        (isOpen_complPieceLeft S T hS) (isOpen_complPieceRight S T hT)
        (complPiece_cover S T) i)
      (mvAlpha (complPieceLeft S T) (complPieceRight S T) i)
      (mvDelta_comp_mvAlpha (complPieceLeft S T) (complPieceRight S T)
        (isOpen_complPieceLeft S T hS) (isOpen_complPieceRight S T hT)
        (complPiece_cover S T) i)).f = 0 :=
    hinter.eq_of_src _ _
  have hmono : Mono (mvAlpha (complPieceLeft S T) (complPieceRight S T) i) :=
    (ShortComplex.exact_iff_mono _ hf).mp hex
  have hzero : IsZero ((singChains (subSpace
      (complPieceLeft S T ∩ complPieceRight S T))).homology i) :=
    IsZero.of_mono (mvAlpha (complPieceLeft S T) (complPieceRight S T) i) hpair
  exact ModuleCat.isZero_iff_subsingleton.mpr
    ((realSingularHomology_subsingleton_iff_of_homotopyEquiv
      (complPieceInterHomeomorph S T).toHomotopyEquiv i).mp
        (ModuleCat.subsingleton_of_isZero hzero))

end AffChain

end AffineTverberg
