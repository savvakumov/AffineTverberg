import AffineTverberg.RelativeHomologyMaps
import AffineTverberg.ComparisonInduction
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

set_option linter.style.header false

/-!
# Excision through the actual small-chain complex

The Mayer-Vietoris short exact sequence makes the square of chains of the
intersection, the two subspaces, and the small-chain complex a pushout.
Its cokernels therefore agree. The small-chain theorem then gives the
relative quasi-isomorphism for an open cover, without assuming excision.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AffineTverberg.AffChain

variable {C D E F : ChainComplex (ModuleCat.{0} ℝ) ℕ}

theorem pairInl_comp_pairDesc (f : C ⟶ E) (g : D ⟶ E) :
    pairInl C D ≫ pairDesc f g = f := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (f.f n).hom x + (g.f n).hom 0 = (f.f n).hom x
  simp

theorem pairInr_comp_pairDesc (f : C ⟶ E) (g : D ⟶ E) :
    pairInr C D ≫ pairDesc f g = g := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (f.f n).hom 0 + (g.f n).hom x = (g.f n).hom x
  simp

theorem pairLift_comp_pairDesc (f : C ⟶ D) (g : C ⟶ E) (h : D ⟶ F) (i : E ⟶ F) :
    pairLift f g ≫ pairDesc h i = f ≫ h + g ≫ i := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

/-- Exactness of the difference/sum sequence is the pushout property. -/
theorem isPushout_of_pair_exact (f : C ⟶ D) (g : C ⟶ E) (i : D ⟶ F) (j : E ⟶ F)
    (w : f ≫ i = g ≫ j)
    (hz : pairLift f (-g) ≫ pairDesc i j = 0)
    (hex : (ShortComplex.mk (pairLift f (-g)) (pairDesc i j) hz).Exact)
    [Epi (pairDesc i j)] : IsPushout f g i j := by
  let S := ShortComplex.mk (pairLift f (-g)) (pairDesc i j) hz
  have hzero {G : ChainComplex (ModuleCat.{0} ℝ) ℕ} (a : D ⟶ G) (b : E ⟶ G)
      (hab : f ≫ a = g ≫ b) : S.f ≫ pairDesc a b = 0 := by
    change pairLift f (-g) ≫ pairDesc a b = 0
    rw [pairLift_comp_pairDesc, Preadditive.neg_comp, hab, add_neg_cancel]
  let desc {G : ChainComplex (ModuleCat.{0} ℝ) ℕ} (a : D ⟶ G) (b : E ⟶ G)
      (hab : f ≫ a = g ≫ b) := hex.desc (pairDesc a b) (hzero a b hab)
  have hfac {G : ChainComplex (ModuleCat.{0} ℝ) ℕ} (a : D ⟶ G) (b : E ⟶ G)
      (hab : f ≫ a = g ≫ b) : pairDesc i j ≫ desc a b hab = pairDesc a b :=
    hex.g_desc _ _
  refine ⟨⟨w⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s => desc s.inl s.inr s.condition) ?_ ?_ ?_⟩⟩
  · intro s
    have h := congrArg (fun k => pairInl D E ≫ k) (hfac s.inl s.inr s.condition)
    simpa only [← Category.assoc, pairInl_comp_pairDesc] using h
  · intro s
    have h := congrArg (fun k => pairInr D E ≫ k) (hfac s.inl s.inr s.condition)
    simpa only [← Category.assoc, pairInr_comp_pairDesc] using h
  · intro s m hm₁ hm₂
    apply (cancel_epi (pairDesc i j)).mp
    rw [hfac s.inl s.inr s.condition, pairDesc_comp, hm₁, hm₂]

variable {X : TopCat.{0}} (A B : Set X)

/-- The inclusion of the right-hand member into the small-chain complex. -/
abbrev smallRight := toSmallCx A B B (chainsIn_le_smallChains_right A B)

/-- The inclusion of the left-hand member into the small-chain complex. -/
abbrev smallLeft := toSmallCx A B A (chainsIn_le_smallChains_left A B)

theorem toSmallCx_comp_smallInc (S : Set X)
    (h : ∀ n, chainsIn S n ≤ smallChains (mvCover A B) n) :
    toSmallCx A B S h ≫ smallInc (mvCover A B) = chainsInclusion S := by
  apply HomologicalComplex.hom_ext
  intro n
  rfl

theorem smallChainSquare_comm :
    subMap (Set.inter_subset_left (s := A) (t := B)) ≫ smallLeft A B =
      subMap (Set.inter_subset_right (s := A) (t := B)) ≫ smallRight A B := by
  apply (cancel_mono (smallInc (mvCover A B))).mp
  simp only [Category.assoc, smallLeft, smallRight, toSmallCx_comp_smallInc,
    subMap_comp_chainsInclusion]

/-- This pushout is established from the actual chain basis and its exact sequence. -/
theorem smallChainSquare_isPushout :
    IsPushout (subMap (Set.inter_subset_left (s := A) (t := B)))
      (subMap (Set.inter_subset_right (s := A) (t := B))) (smallLeft A B) (smallRight A B) := by
  have : Epi (pairDesc (smallLeft A B) (smallRight A B)) := (mvShortExact A B).epi_g
  exact isPushout_of_pair_exact _ _ _ _ (smallChainSquare_comm A B)
    (mvF_comp_mvG A B) (mvShortExact A B).exact

/-- The two relative cokernels are canonically isomorphic, even before using a cover. -/
def smallRelativeMap :
    cokernel (subMap (Set.inter_subset_left (s := A) (t := B))) ⟶ cokernel (smallRight A B) :=
  cokernel.map _ _ (subMap Set.inter_subset_right) (smallLeft A B) (smallChainSquare_comm A B)

theorem isIso_smallRelativeMap : IsIso (smallRelativeMap A B) :=
  isIso_cokernel_map_of_isPushout (smallChainSquare_isPushout A B)

/-- The exact sequence defining relative small chains. -/
def smallRelativeShortComplex : ShortComplex (ChainComplex (ModuleCat.{0} ℝ) ℕ) :=
  ShortComplex.mk (smallRight A B) (cokernel.π (smallRight A B)) (cokernel.condition _)

theorem smallRelativeShortExact : (smallRelativeShortComplex A B).ShortExact where
  exact := ShortComplex.exact_cokernel _
  mono_f := by
    apply HomologicalComplex.mono_of_mono_f
    intro n
    apply (ModuleCat.mono_iff_injective _).mpr
    intro a b hab
    exact chainsInclusion_injective B n (congrArg Subtype.val hab)
  epi_g := coequalizer.π_epi

/-- The inclusion of small chains induces the map on relative cokernels. -/
def relativeSmallInc : cokernel (smallRight A B) ⟶ relCx B :=
  cokernel.map _ _ (𝟙 _) (smallInc (mvCover A B)) (by
    rw [Category.id_comp]
    exact toSmallCx_comp_smallInc A B B _)

theorem relativeSmallInc_proj :
    cokernel.π (smallRight A B) ≫ relativeSmallInc A B =
      smallInc (mvCover A B) ≫ relProj B := cokernel.π_desc _ _ _

def relativeSmallShortComplexMap : smallRelativeShortComplex A B ⟶ relShortComplex B where
  τ₁ := 𝟙 _
  τ₂ := smallInc (mvCover A B)
  τ₃ := relativeSmallInc A B
  comm₁₂ := by
    change 𝟙 (singChains (subSpace B)) ≫ chainsInclusion B =
      smallRight A B ≫ smallInc (mvCover A B)
    rw [Category.id_comp]
    exact (toSmallCx_comp_smallInc A B B _).symm
  comm₂₃ := (relativeSmallInc_proj A B).symm

/-- The relative small-chain theorem for the actual open cover. -/
theorem quasiIso_relativeSmallInc (hA : IsOpen A) (hB : IsOpen B)
    (hcov : ∀ x : X, x ∈ A ∨ x ∈ B) : QuasiIso (relativeSmallInc A B) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (relativeSmallShortComplexMap A B)
    (smallRelativeShortExact A B) (relShortExact B)
    (by change QuasiIso (𝟙 (singChains (subSpace B))); infer_instance)
    (quasiIso_smallInc (mvCover A B) (isOpen_mvCover A B hA hB) (exists_mem_mvCover A B hcov))

/-- Excision, in the flat intersection presentation of the source cokernel. -/
def flatExcisionMap :
    cokernel (subMap (Set.inter_subset_left (s := A) (t := B))) ⟶ relCx B :=
  smallRelativeMap A B ≫ relativeSmallInc A B

theorem quasiIso_flatExcisionMap (hA : IsOpen A) (hB : IsOpen B)
    (hcov : ∀ x : X, x ∈ A ∨ x ∈ B) : QuasiIso (flatExcisionMap A B) := by
  have := isIso_smallRelativeMap A B
  have := quasiIso_relativeSmallInc A B hA hB hcov
  dsimp only [flatExcisionMap]
  infer_instance

end AffineTverberg.AffChain
