import AffineTverberg.CoefficientSimplicialMayerVietorisSES
import AffineTverberg.CoefficientReducedHomologyComparison
import AffineTverberg.StarLinkRetract
import Mathlib.Data.ZMod.Basic

set_option linter.style.header false

/-!
# Mod-two vanishing at a boundary point

The existing ball homeomorphism and cone retraction are reused unchanged.
At a homology-boundary point the punctured ball is contractible. Applying
the existing Mayer–Vietoris sequence with `ZMod 2` coefficients shows that
the closed-star link has zero positive homology over `ZMod 2`.
This is the topological input needed to contradict the unoriented link cycle.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Set Metric

namespace AffineTverberg

namespace IsSimplicialBall

variable {e n : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}

/-- The existing detection of the ball boundary upgrades vanishing of the
top real homology to actual contractibility of the punctured polyhedron. -/
theorem contractibleSpace_punctured_of_mem_homologyBoundary
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n) {P : ↥K.space}
    (hP : P ∈ homologyBoundary ↥K.space (n - 1)) :
    ContractibleSpace ↥{q : ↥K.space | q ≠ P} := by
  let h := hball.homeomorph_closedBall.some
  have hdim : Module.finrank ℝ (CoordinateSpace n) = (n - 2) + 2 := by
    simp only [CoordinateSpace, Module.finrank_pi, Fintype.card_fin]
    omega
  have hdeg : n - 2 + 1 = n - 1 := by omega
  have hnorm : ‖(h P).val‖ = 1 := by
    have hp' := (homologyBoundary_congr h (n - 1) P).mp hP
    rw [← hdeg, homologyBoundary_closedBall hdim] at hp'
    exact mem_sphere_zero_iff_norm.mp hp'
  have : ContractibleSpace ↥{q : ↥(closedBall (0 : CoordinateSpace n) 1) | q ≠ h P} := by
    change ContractibleSpace ↥(ballPunctured (h P))
    exact contractibleSpace_ballPunctured_of_norm_eq_one (h P) hnorm
  exact (puncturedHomeomorph h P).toHomotopyEquiv.contractibleSpace

end IsSimplicialBall

namespace ModTwo

open AffineTverberg.Coefficients AffineTverberg.Coefficients.AffChain
open AffineTverberg.AffChain

/-- Positive mod-two homology of the intersection of two contractible opens
covering a contractible space vanishes, by the already proved sequence. -/
theorem subsingleton_homology_inter_of_contractible_cover
    {X : TopCat.{0}} (A B : Set X) (hA : IsOpen A) (hB : IsOpen B)
    (hcov : ∀ x, x ∈ A ∨ x ∈ B)
    [ContractibleSpace X] [ContractibleSpace ↥A] [ContractibleSpace ↥B]
    (k : ℕ) (hk : k ≠ 0) :
    Subsingleton ((singularHomology (ZMod 2) k).obj (subSpace (A ∩ B))) := by
  have hX : IsZero ((singularHomology (ZMod 2) (k + 1)).obj X) := by
    have := singularHomology_subsingleton_of_contractible (ZMod 2) X (k + 1) (by omega)
    exact ModuleCat.isZero_of_subsingleton _
  have hAzero : IsZero ((singularHomology (ZMod 2) k).obj (subSpace A)) := by
    have := singularHomology_subsingleton_of_contractible (ZMod 2) ↥A k hk
    exact ModuleCat.isZero_of_subsingleton _
  have hBzero : IsZero ((singularHomology (ZMod 2) k).obj (subSpace B)) := by
    have := singularHomology_subsingleton_of_contractible (ZMod 2) ↥B k hk
    exact ModuleCat.isZero_of_subsingleton _
  have hdelta : Coefficients.AffChain.mvDelta (ZMod 2) A B hA hB hcov k = 0 :=
    hX.eq_zero_of_src _
  have hmono : Mono (Coefficients.AffChain.mvAlpha (ZMod 2) A B k) :=
    (ShortComplex.exact_iff_mono
      (ShortComplex.mk (Coefficients.AffChain.mvDelta (ZMod 2) A B hA hB hcov k)
        (Coefficients.AffChain.mvAlpha (ZMod 2) A B k)
        (Coefficients.AffChain.mvDelta_comp_mvAlpha (ZMod 2) A B hA hB hcov k))
      hdelta).mp (Coefficients.AffChain.mv_exact_inter (ZMod 2) A B hA hB hcov k)
  let C := Coefficients.AffChain.singChains (ZMod 2) (subSpace A)
  let D := Coefficients.AffChain.singChains (ZMod 2) (subSpace B)
  have hpair : IsZero ((Coefficients.AffChain.pairCx (ZMod 2) C D).homology k) := by
    have hfst : HomologicalComplex.homologyMap
        (Coefficients.AffChain.pairFst (ZMod 2) C D) k = 0 := hAzero.eq_zero_of_tgt _
    have hsnd : HomologicalComplex.homologyMap
        (Coefficients.AffChain.pairSnd (ZMod 2) C D) k = 0 := hBzero.eq_zero_of_tgt _
    rw [IsZero.iff_id_eq_zero,
      ← Coefficients.AffChain.homology_pair_total (ZMod 2) C D k,
      hfst, hsnd, zero_comp, zero_comp, zero_add]
  have := ModuleCat.subsingleton_of_isZero hpair
  exact Function.Injective.subsingleton
    ((ModuleCat.mono_iff_injective _).mp hmono)

/-- A retraction injects actual mod-two singular homology. No new geometric
construction is involved. -/
theorem injective_homology_of_retract {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (i : C(X, Y)) (r : C(Y, X)) (hri : ∀ x, r (i x) = x) (k : ℕ) :
    Function.Injective ((singularHomology (ZMod 2) k).map (TopCat.ofHom i)).hom := by
  have hcomp : (TopCat.ofHom i ≫ TopCat.ofHom r) = 𝟙 (TopCat.of X) := by
    apply TopCat.hom_ext
    ext x
    exact hri x
  have hmap : (singularHomology (ZMod 2) k).map (TopCat.ofHom i) ≫
      (singularHomology (ZMod 2) k).map (TopCat.ofHom r) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, hcomp]
    exact (singularHomology (ZMod 2) k).map_id _
  have hmono : Mono ((singularHomology (ZMod 2) k).map (TopCat.ofHom i)) :=
    @IsSplitMono.mono _ _ _ _ _ ⟨⟨SplitMono.mk _ hmap⟩⟩
  exact (ModuleCat.mono_iff_injective _).mp hmono

end ModTwo

namespace IsSimplicialBall

open AffineTverberg.Coefficients

variable {e n : ℕ} {K : Geometry.SimplicialComplex ℝ (CoordinateSpace e)}
  {L : Finset (CoordinateSpace e)} {p : CoordinateSpace e}

/-- At every carrier point on the topological boundary, the actual closed-star
link has zero positive mod-two singular homology. -/
theorem subsingleton_modTwo_homology_closedStarLink_of_mem_homologyBoundary
    (hball : IsSimplicialBall n K) (hn : 2 ≤ n) (hL : L ∈ K.faces)
    (hp : IsCarrierPoint K L p)
    (hmem : (⟨p, hp.mem_space hL⟩ : ↥K.space) ∈ homologyBoundary ↥K.space (n - 1))
    (k : ℕ) (hk : k ≠ 0) :
    Subsingleton ((singularHomology (ZMod 2) k).obj
      (TopCat.of ↥(closedStarLink K L))) := by
  classical
  have hpspace : p ∈ K.space := hp.mem_space hL
  have hBopen : IsOpen (Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space) :=
    isOpen_preimage_openStarCone hball.finite_faces
  have hapex : p ∈ openStarCone K L := mem_openStarCone_apex hball.finite_faces hL hp
  have hBcontr : ContractibleSpace ↥(Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space) := by
    have : ContractibleSpace ↥(openStarCone K L) :=
      (starConvex_openStarCone hL hp).contractibleSpace ⟨p, hapex⟩
    exact (subsetSubtypeHomeomorph
      (openStarCone_subset_space (K := K) (L := L))).toHomotopyEquiv.contractibleSpace
  have : ContractibleSpace ↥K.space := hball.contractibleSpace_space
  have : ContractibleSpace ↥{q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)} :=
    hball.contractibleSpace_punctured_of_mem_homologyBoundary hn hmem
  have hcov : ∀ q : ↥K.space, q ≠ (⟨p, hpspace⟩ : ↥K.space) ∨
      q ∈ (Subtype.val ⁻¹' (openStarCone K L) : Set ↥K.space) := by
    intro q
    by_cases hq : q = (⟨p, hpspace⟩ : ↥K.space)
    · exact Or.inr (hq ▸ hapex)
    · exact Or.inl hq
  have hsub := ModTwo.subsingleton_homology_inter_of_contractible_cover
    (X := TopCat.of ↥K.space) {q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)}
    (Subtype.val ⁻¹' (openStarCone K L)) isOpen_compl_singleton hBopen hcov k hk
  have hinter : ({q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)} ∩
      (Subtype.val ⁻¹' (openStarCone K L))) =
      Subtype.val ⁻¹' (puncturedOpenStar K L p) := by
    ext q
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, fun h => h1 (Subtype.ext h)⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h2 (by simp [h]), h1⟩
  have hWhomeo : ↥({q : ↥K.space | q ≠ (⟨p, hpspace⟩ : ↥K.space)} ∩
      (Subtype.val ⁻¹' (openStarCone K L))) ≃ₜ ↥(puncturedOpenStar K L p) :=
    (Homeomorph.setCongr hinter).trans
      (subsetSubtypeHomeomorph (puncturedOpenStar_subset_space (K := K) (L := L) (p := p)))
  have : Subsingleton ((singularHomology (ZMod 2) k).obj
      (TopCat.of ↥(puncturedOpenStar K L p))) :=
    (singularHomology_subsingleton_iff_of_homotopyEquiv
      (ZMod 2) hWhomeo.toHomotopyEquiv k).mp hsub
  exact Function.Injective.subsingleton (ModTwo.injective_homology_of_retract
    (⟨linkInclusion hL hp, continuous_linkInclusion hL hp⟩ :
      C(↥(closedStarLink K L), ↥(puncturedOpenStar K L p)))
    ⟨linkRetraction hL hp, continuous_linkRetraction hball.finite_faces hL hp⟩
    (linkRetraction_linkInclusion hL hp) k)

end IsSimplicialBall

end AffineTverberg
