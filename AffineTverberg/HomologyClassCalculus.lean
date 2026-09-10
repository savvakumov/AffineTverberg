import AffineTverberg.SmallChainQuasiIso

set_option linter.style.header false

/-!
# Cycle level calculus for homology classes

The descent arguments for the actual sphere projection have to move between
homology classes and honest cycles: a class of the target is represented by a
cycle, that cycle is supported in a member of a directed family of opens, and
the resulting class in the smaller space is pushed forward again.

This file provides the three elementary facts which make such arguments
possible for chain complexes of real vector spaces indexed by `ℕ`:
`homClass_surjective`, `homClass_map` and `homClass_eq_zero_iff`.
Nothing here is specific to singular chains.
-/

noncomputable section

open CategoryTheory HomologicalComplex

namespace AffineTverberg.AffChain

variable {C D : ChainComplex (ModuleCat.{0} ℝ) ℕ}

/-- A chain annihilated by every differential leaving its degree. -/
def IsCycleAt (C : ChainComplex (ModuleCat.{0} ℝ) ℕ) (k : ℕ) (z : C.X k) : Prop :=
  ∀ j, (C.d k j).hom z = 0

theorem isCycleAt_zero (z : C.X 0) : IsCycleAt C 0 z := by
  intro j
  rw [C.shape 0 j (by simp)]
  simp

theorem isCycleAt_succ {k : ℕ} {z : C.X (k + 1)} (h : (C.d (k + 1) k).hom z = 0) :
    IsCycleAt C (k + 1) z := by
  intro j
  by_cases hj : j = k
  · subst hj
    exact h
  · rw [C.shape (k + 1) j (by simp only [ComplexShape.down_Rel]; omega)]
    simp

theorem IsCycleAt.map (φ : C ⟶ D) {k : ℕ} {z : C.X k} (hz : IsCycleAt C k z) :
    IsCycleAt D k ((φ.f k).hom z) := by
  intro j
  have h := congrArg (fun g : C.X k ⟶ D.X j => g.hom z) (φ.comm k j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  rw [h, hz j, map_zero]

/-- The cycle of the cycles object determined by a cycle chain. -/
def cycleOf {k : ℕ} (z : C.X k) (hz : IsCycleAt C k z) : C.cycles k :=
  HomologicalComplex.cyclesMk C z ((ComplexShape.down ℕ).next k) rfl (hz _)

theorem i_cycleOf {k : ℕ} (z : C.X k) (hz : IsCycleAt C k z) :
    (C.iCycles k).hom (cycleOf z hz) = z :=
  HomologicalComplex.i_cyclesMk C z ((ComplexShape.down ℕ).next k) rfl (hz _)

theorem cycleOf_eq {k : ℕ} (z : C.X k) (hz : IsCycleAt C k z) (c : C.cycles k)
    (h : (C.iCycles k).hom c = z) : cycleOf z hz = c := by
  apply (ModuleCat.mono_iff_injective (C.iCycles k)).1 inferInstance
  rw [i_cycleOf, h]

/-- The homology class of a cycle. -/
def homClass {k : ℕ} (z : C.X k) (hz : IsCycleAt C k z) : C.homology k :=
  (C.homologyπ k).hom (cycleOf z hz)

theorem homClass_congr {k : ℕ} {z w : C.X k} (hz : IsCycleAt C k z) (hw : IsCycleAt C k w)
    (h : z = w) : homClass z hz = homClass w hw := by
  subst h
  rfl

/-- A cycle whose class is that of a given homology element. -/
theorem homClass_surjective {k : ℕ} (h : C.homology k) :
    ∃ (z : C.X k) (hz : IsCycleAt C k z), homClass z hz = h := by
  obtain ⟨c, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (C.homologyπ k)).1 inferInstance h
  have hz : IsCycleAt C k ((C.iCycles k).hom c) := by
    intro j
    have h2 := congrArg (fun g : C.cycles k ⟶ C.X j => g.hom c) (C.iCycles_d k j)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h2
  exact ⟨_, hz, by rw [homClass, cycleOf_eq _ hz c rfl]⟩

/-- Chain maps send the class of a cycle to the class of its image. -/
theorem homClass_map (φ : C ⟶ D) {k : ℕ} (z : C.X k) (hz : IsCycleAt C k z) :
    (HomologicalComplex.homologyMap φ k).hom (homClass z hz) =
      homClass ((φ.f k).hom z) (hz.map φ) := by
  have hcm : (HomologicalComplex.cyclesMap φ k).hom (cycleOf z hz) =
      cycleOf ((φ.f k).hom z) (hz.map φ) := by
    refine (cycleOf_eq _ (hz.map φ) _ ?_).symm
    have h1 := congrArg (fun g : C.cycles k ⟶ D.X k => g.hom (cycleOf z hz))
      (HomologicalComplex.cyclesMap_i φ k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    rw [h1, i_cycleOf]
  have hnat := congrArg (fun g : C.cycles k ⟶ D.homology k => g.hom (cycleOf z hz))
    (HomologicalComplex.homologyπ_naturality φ k)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  rw [homClass, hnat, homClass, hcm]

/-- A cycle has vanishing class exactly when it is a boundary. -/
theorem homClass_eq_zero_iff {k : ℕ} (z : C.X k) (hz : IsCycleAt C k z) :
    homClass z hz = 0 ↔ ∃ w : C.X (k + 1), (C.d (k + 1) k).hom w = z := by
  constructor
  · intro h
    obtain ⟨w, hw⟩ := exists_toCycles_of_homologyπ_eq_zero C k (cycleOf z hz) h
    refine ⟨w, ?_⟩
    have h2 := congrArg (fun g : C.X (k + 1) ⟶ C.X k => g.hom w) (C.toCycles_i (k + 1) k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    rw [← h2, hw, i_cycleOf]
  · rintro ⟨w, rfl⟩
    have h2 := congrArg (fun g : C.X (k + 1) ⟶ C.X k => g.hom w) (C.toCycles_i (k + 1) k)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    have hcyc : cycleOf ((C.d (k + 1) k).hom w) hz = (C.toCycles (k + 1) k).hom w :=
      cycleOf_eq _ hz _ h2
    rw [homClass, hcyc]
    have h3 := congrArg (fun g : C.X (k + 1) ⟶ C.homology k => g.hom w)
      (C.toCycles_comp_homologyπ (k + 1) k)
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] using h3

/-- Surjectivity of an induced homology map, in cycle terms. -/
theorem epi_homologyMap_of_forall_cycle (φ : C ⟶ D) (k : ℕ)
    (h : ∀ (z : D.X k) (hz : IsCycleAt D k z), ∃ (w : C.X k) (hw : IsCycleAt C k w),
      (HomologicalComplex.homologyMap φ k).hom (homClass w hw) = homClass z hz) :
    Epi (HomologicalComplex.homologyMap φ k) := by
  rw [ModuleCat.epi_iff_surjective]
  intro a
  obtain ⟨z, hz, rfl⟩ := homClass_surjective a
  obtain ⟨w, hw, hwz⟩ := h z hz
  exact ⟨homClass w hw, hwz⟩

/-- Injectivity of an induced homology map, in cycle terms. -/
theorem mono_homologyMap_of_forall_cycle (φ : C ⟶ D) (k : ℕ)
    (h : ∀ (z : C.X k), IsCycleAt C k z →
      (∃ w : D.X (k + 1), (D.d (k + 1) k).hom w = (φ.f k).hom z) →
      ∃ w : C.X (k + 1), (C.d (k + 1) k).hom w = z) :
    Mono (HomologicalComplex.homologyMap φ k) := by
  rw [ModuleCat.mono_iff_injective]
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  obtain ⟨z, hz, rfl⟩ := homClass_surjective a
  rw [homClass_map] at ha
  rw [homClass_eq_zero_iff]
  exact h z hz ((homClass_eq_zero_iff _ (hz.map φ)).1 ha)

end AffineTverberg.AffChain
