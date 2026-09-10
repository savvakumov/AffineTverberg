import AffineTverberg.HomologyClassCalculus
import AffineTverberg.SingularHomologyRangeGluing

set_option linter.style.header false

/-!
# Compact supports and directed unions of opens

A singular chain is a finite combination of singular simplices, each with
compact image. Consequently every chain of a space covered by a directed
family of opens is already carried by one member of the family. This file
proves that (`exists_mem_chainsIn_of_directed`) and deduces that the sharp
homology range `HomologyRange` for the restrictions of a map to the members
of a directed open family passes to their union.

This is the mechanism which replaces a good-cover hypothesis in the descent
for the actual sphere projection: no member of the family needs to be closed
under intersection, and no compactness of the total space is used.
-/

noncomputable section

open CategoryTheory HomologicalComplex

namespace AffineTverberg.AffChain

/-! ### One member of a directed family carries a given chain -/

section CompactSupport

variable {X : TopCat.{0}}

theorem exists_mem_of_finset_directed {β : Type*} {𝒟 : Set (Set X)} (hne : 𝒟.Nonempty)
    (hdir : ∀ A ∈ 𝒟, ∀ B ∈ 𝒟, ∃ D ∈ 𝒟, A ∪ B ⊆ D)
    (s : Finset β) (g : β → Set X) (hg : ∀ b ∈ s, ∃ A ∈ 𝒟, g b ⊆ A) :
    ∃ A ∈ 𝒟, ∀ b ∈ s, g b ⊆ A := by
  classical
  induction s using Finset.induction with
  | empty =>
    obtain ⟨A, hA⟩ := hne
    exact ⟨A, hA, by simp⟩
  | insert b s hb ih =>
    obtain ⟨A, hA, hAs⟩ := ih (fun c hc => hg c (Finset.mem_insert_of_mem hc))
    obtain ⟨B, hB, hBb⟩ := hg b (Finset.mem_insert_self b s)
    obtain ⟨D, hD, hDsub⟩ := hdir A hA B hB
    refine ⟨D, hD, fun c hc => ?_⟩
    rcases Finset.mem_insert.1 hc with rfl | hc
    · exact hBb.trans (Set.subset_union_right.trans hDsub)
    · exact (hAs c hc).trans (Set.subset_union_left.trans hDsub)

/-- A compact subset of a directed union of opens lies in one member. -/
theorem exists_mem_of_isCompact_directed {K : Set X} (hK : IsCompact K)
    {𝒟 : Set (Set X)} (hne : 𝒟.Nonempty) (hopen : ∀ A ∈ 𝒟, IsOpen A)
    (hdir : ∀ A ∈ 𝒟, ∀ B ∈ 𝒟, ∃ D ∈ 𝒟, A ∪ B ⊆ D)
    (hcov : K ⊆ ⋃₀ 𝒟) :
    ∃ A ∈ 𝒟, K ⊆ A := by
  have hnonempty : Nonempty ↥𝒟 := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hsub : K ⊆ ⋃ i : ↥𝒟, (i : Set X) := by
    intro x hx
    obtain ⟨A, hA, hxA⟩ := hcov hx
    exact Set.mem_iUnion.2 ⟨⟨A, hA⟩, hxA⟩
  have hdirected : Directed (· ⊆ ·) (fun i : ↥𝒟 => (i : Set X)) := by
    rintro ⟨A, hA⟩ ⟨B, hB⟩
    obtain ⟨D, hD, hDsub⟩ := hdir A hA B hB
    exact ⟨⟨D, hD⟩, Set.subset_union_left.trans hDsub,
      Set.subset_union_right.trans hDsub⟩
  obtain ⟨i, hi⟩ := hK.elim_directed_cover _ (fun i : ↥𝒟 => hopen i.1 i.2) hsub hdirected
  exact ⟨i.1, i.2, hi⟩

/-- **Compact support.** Every singular chain of a space covered by a directed
family of opens is carried by a single member of that family. -/
theorem exists_mem_chainsIn_of_directed {n : ℕ} (c : (singChains X).X n)
    {𝒟 : Set (Set X)} (hne : 𝒟.Nonempty) (hopen : ∀ A ∈ 𝒟, IsOpen A)
    (hdir : ∀ A ∈ 𝒟, ∀ B ∈ 𝒟, ∃ D ∈ 𝒟, A ∪ B ⊆ D)
    (hcov : (⋃₀ 𝒟) = Set.univ) :
    ∃ A ∈ 𝒟, c ∈ chainsIn A n := by
  classical
  set s := (chainEquiv X n c).support with hs
  have hstep : ∀ x ∈ s, ∃ A ∈ 𝒟, Set.range (simplexMap x) ⊆ A := by
    intro x _
    refine exists_mem_of_isCompact_directed (isCompact_range (simplexMap x).continuous)
      hne hopen hdir ?_
    rw [hcov]
    exact Set.subset_univ _
  obtain ⟨A, hA, hAs⟩ := exists_mem_of_finset_directed hne hdir s
    (fun x => Set.range (simplexMap x)) hstep
  refine ⟨A, hA, ?_⟩
  rw [mem_chainsIn_iff]
  intro x hx
  by_contra hne0
  have hxs : x ∈ s := by
    rw [hs, Finsupp.mem_support_iff]
    exact hne0
  exact hx fun t => hAs x hxs ⟨t, rfl⟩

end CompactSupport

/-! ### Cycles carried by a subspace -/

section Carried

variable {X : TopCat.{0}}

theorem chainsInclusion_d {S : Set X} {i j : ℕ} (z : (singChains (subSpace S)).X i) :
    ((chainsInclusion S).f j).hom (((singChains (subSpace S)).d i j).hom z) =
      ((singChains X).d i j).hom (((chainsInclusion S).f i).hom z) := by
  have h := congrArg (fun g : (singChains (subSpace S)).X i ⟶ (singChains X).X j => g.hom z)
    ((chainsInclusion S).comm i j)
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using h.symm

/-- A cycle carried by a subspace comes from a cycle of that subspace. -/
theorem exists_cycle_of_mem_chainsIn {S : Set X} {k : ℕ} (z : (singChains X).X k)
    (hz : IsCycleAt (singChains X) k z) (hmem : z ∈ chainsIn S k) :
    ∃ (zS : (singChains (subSpace S)).X k) (_ : IsCycleAt (singChains (subSpace S)) k zS),
      ((chainsInclusion S).f k).hom zS = z := by
  rw [← range_chainsInclusion S k] at hmem
  obtain ⟨zS, hzS⟩ := hmem
  refine ⟨zS, ?_, hzS⟩
  intro j
  apply chainsInclusion_injective S j
  rw [chainsInclusion_d, hzS, hz j, map_zero]

end Carried

/-! ### The directed union theorem -/

section Descent

variable {X Y : TopCat.{0}}

theorem chainsInclusion_naturality_preimage (f : X ⟶ Y) (A : Set Y) :
    chainsInclusion ((ConcreteCategory.hom f) ⁻¹' A) ≫ singChainsMap f =
      singChainsMap (preimageRestriction f A) ≫ chainsInclusion A :=
  (chainsInclusion_naturality f (fun _ hx => hx)).symm

/-- Pushing a class of the restricted map forward along the two subspace
inclusions gives the class of the original cycle. -/
theorem homClass_pushforward_eq (f : X ⟶ Y) (A : Set Y) {k : ℕ}
    (w : (singChains (subSpace ((ConcreteCategory.hom f) ⁻¹' A))).X k)
    (hw : IsCycleAt (singChains (subSpace ((ConcreteCategory.hom f) ⁻¹' A))) k w)
    (zA : (singChains (subSpace A)).X k)
    (hzA : IsCycleAt (singChains (subSpace A)) k zA)
    (z : (singChains Y).X k) (hz : IsCycleAt (singChains Y) k z)
    (hu : (homologyMap (singChainsMap (preimageRestriction f A)) k).hom (homClass w hw) =
      homClass zA hzA)
    (hzAeq : ((chainsInclusion A).f k).hom zA = z) :
    (homologyMap (singChainsMap f) k).hom
        (homClass (((chainsInclusion ((ConcreteCategory.hom f) ⁻¹' A)).f k).hom w)
          (hw.map (chainsInclusion ((ConcreteCategory.hom f) ⁻¹' A)))) =
      homClass z hz := by
  have hnat := congrArg
    (fun g : singChains (subSpace ((ConcreteCategory.hom f) ⁻¹' A)) ⟶ singChains Y =>
      (homologyMap g k).hom (homClass w hw)) (chainsInclusion_naturality_preimage f A)
  simp only [homologyMap_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
  calc (homologyMap (singChainsMap f) k).hom
        (homClass (((chainsInclusion ((ConcreteCategory.hom f) ⁻¹' A)).f k).hom w)
          (hw.map (chainsInclusion ((ConcreteCategory.hom f) ⁻¹' A))))
      = (homologyMap (singChainsMap f) k).hom
          ((homologyMap (chainsInclusion ((ConcreteCategory.hom f) ⁻¹' A)) k).hom
            (homClass w hw)) := by
        simp only [homClass_map]
    _ = (homologyMap (chainsInclusion A) k).hom
          ((homologyMap (singChainsMap (preimageRestriction f A)) k).hom
            (homClass w hw)) := hnat
    _ = (homologyMap (chainsInclusion A) k).hom (homClass zA hzA) := by rw [hu]
    _ = homClass (((chainsInclusion A).f k).hom zA) (hzA.map (chainsInclusion A)) :=
        homClass_map _ _ _
    _ = homClass z hz := homClass_congr (hzA.map (chainsInclusion A)) hz hzAeq

/-- **Descent along a directed family of opens.** If the restriction of `f`
over every member of a directed open cover of the target has the sharp
homology range, then so does `f` itself. -/
theorem homologyRange_of_directed_open_cover (f : X ⟶ Y) (q : ℕ)
    {𝒟 : Set (Set Y)} (hne : 𝒟.Nonempty) (hopen : ∀ A ∈ 𝒟, IsOpen A)
    (hdir : ∀ A ∈ 𝒟, ∀ B ∈ 𝒟, ∃ D ∈ 𝒟, A ∪ B ⊆ D)
    (hcov : (⋃₀ 𝒟) = Set.univ)
    (hrange : ∀ A ∈ 𝒟, HomologyRange (singChainsMap (preimageRestriction f A)) q) :
    HomologyRange (singChainsMap f) q := by
  classical
  -- the directed family of preimages
  set 𝒟X : Set (Set X) := (fun A => (ConcreteCategory.hom f) ⁻¹' A) '' 𝒟 with h𝒟X
  have hneX : 𝒟X.Nonempty := ⟨_, ⟨hne.choose, hne.choose_spec, rfl⟩⟩
  have hopenX : ∀ A ∈ 𝒟X, IsOpen A := by
    rintro _ ⟨A, hA, rfl⟩
    exact (hopen A hA).preimage f.hom.continuous
  have hdirX : ∀ A ∈ 𝒟X, ∀ B ∈ 𝒟X, ∃ D ∈ 𝒟X, A ∪ B ⊆ D := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    obtain ⟨D, hD, hDsub⟩ := hdir A hA B hB
    exact ⟨_, ⟨D, hD, rfl⟩, by
      rintro x (hx | hx)
      · exact hDsub (Or.inl hx)
      · exact hDsub (Or.inr hx)⟩
  have hcovX : (⋃₀ 𝒟X) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    have : (ConcreteCategory.hom f) x ∈ (⋃₀ 𝒟) := by rw [hcov]; trivial
    obtain ⟨A, hA, hxA⟩ := this
    exact ⟨_, ⟨A, hA, rfl⟩, hxA⟩
  constructor
  · -- isomorphisms below `q`
    intro k hk
    have hmono : Mono (homologyMap (singChainsMap f) k) := by
      apply mono_homologyMap_of_forall_cycle
      rintro z hz ⟨b, hb⟩
      -- the cycle and the bounding chain are carried by one member
      obtain ⟨A₀, ⟨A₀', hA₀', rfl⟩, hzA⟩ :=
        exists_mem_chainsIn_of_directed z hneX hopenX hdirX hcovX
      obtain ⟨A₁, hA₁, hbA⟩ := exists_mem_chainsIn_of_directed b hne hopen hdir hcov
      obtain ⟨A, hA, hAsub⟩ := hdir A₀' hA₀' A₁ hA₁
      have hzA' : z ∈ chainsIn ((ConcreteCategory.hom f) ⁻¹' A) k := by
        refine chainsIn_mono ?_ k hzA
        exact fun x hx => hAsub (Or.inl hx)
      have hbA' : b ∈ chainsIn A (k + 1) :=
        chainsIn_mono (fun x hx => hAsub (Or.inr hx)) (k + 1) hbA
      obtain ⟨zA, hzAcyc, hzAeq⟩ := exists_cycle_of_mem_chainsIn z hz hzA'
      rw [← range_chainsInclusion A (k + 1)] at hbA'
      obtain ⟨bA, hbAeq⟩ := hbA'
      -- the boundary relation descends
      have hnat := chainsInclusion_naturality_preimage f A
      have hdb : ((singChains (subSpace A)).d (k + 1) k).hom bA =
          ((singChainsMap (preimageRestriction f A)).f k).hom zA := by
        apply chainsInclusion_injective A k
        have h1 : ((chainsInclusion A).f k).hom
            (((singChains (subSpace A)).d (k + 1) k).hom bA) =
            ((singChains Y).d (k + 1) k).hom b := by
          rw [chainsInclusion_d, hbAeq]
        have h2 : ((chainsInclusion A).f k).hom
            (((singChainsMap (preimageRestriction f A)).f k).hom zA) =
            ((singChainsMap f).f k).hom z := by
          have := congrArg
            (fun g : singChains (subSpace ((ConcreteCategory.hom f) ⁻¹' A)) ⟶ singChains Y =>
              (g.f k).hom zA) hnat
          simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp,
            LinearMap.comp_apply] at this
          rw [← this, hzAeq]
        rw [h1, h2, hb]
      -- the class of the descended cycle vanishes, hence so does its lift
      have hclass : (homologyMap (singChainsMap (preimageRestriction f A)) k).hom
          (homClass zA hzAcyc) = 0 := by
        rw [homClass_map]
        exact (homClass_eq_zero_iff _ (hzAcyc.map _)).2 ⟨bA, hdb⟩
      have hiso := (hrange A hA).1 k hk
      have hmonoA : Mono (homologyMap (singChainsMap (preimageRestriction f A)) k) :=
        inferInstance
      have hzero : homClass zA hzAcyc = 0 := by
        have hinj := (ModuleCat.mono_iff_injective
          (homologyMap (singChainsMap (preimageRestriction f A)) k)).1 hmonoA
        exact hinj (by rw [hclass, map_zero])
      obtain ⟨wA, hwA⟩ := (homClass_eq_zero_iff _ hzAcyc).1 hzero
      refine ⟨((chainsInclusion ((ConcreteCategory.hom f) ⁻¹' A)).f (k + 1)).hom wA, ?_⟩
      rw [← chainsInclusion_d, hwA, hzAeq]
    have hepi : Epi (homologyMap (singChainsMap f) k) := by
      apply epi_homologyMap_of_forall_cycle
      intro z hz
      obtain ⟨A, hA, hzA⟩ := exists_mem_chainsIn_of_directed z hne hopen hdir hcov
      obtain ⟨zA, hzAcyc, hzAeq⟩ := exists_cycle_of_mem_chainsIn z hz hzA
      have hepiA := (hrange A hA).2 k hk.le
      obtain ⟨u, hu⟩ := (ModuleCat.epi_iff_surjective
        (homologyMap (singChainsMap (preimageRestriction f A)) k)).1 hepiA
        (homClass zA hzAcyc)
      obtain ⟨w, hwcyc, rfl⟩ := homClass_surjective u
      exact ⟨((chainsInclusion ((ConcreteCategory.hom f) ⁻¹' A)).f k).hom w,
        hwcyc.map _, homClass_pushforward_eq f A w hwcyc zA hzAcyc z hz hu hzAeq⟩
    exact isIso_of_mono_of_epi _
  · -- epimorphisms through `q`
    intro k hk
    apply epi_homologyMap_of_forall_cycle
    intro z hz
    obtain ⟨A, hA, hzA⟩ := exists_mem_chainsIn_of_directed z hne hopen hdir hcov
    obtain ⟨zA, hzAcyc, hzAeq⟩ := exists_cycle_of_mem_chainsIn z hz hzA
    have hepiA := (hrange A hA).2 k hk
    obtain ⟨u, hu⟩ := (ModuleCat.epi_iff_surjective
      (homologyMap (singChainsMap (preimageRestriction f A)) k)).1 hepiA
      (homClass zA hzAcyc)
    obtain ⟨w, hwcyc, rfl⟩ := homClass_surjective u
    exact ⟨((chainsInclusion ((ConcreteCategory.hom f) ⁻¹' A)).f k).hom w,
      hwcyc.map _, homClass_pushforward_eq f A w hwcyc zA hzAcyc z hz hu hzAeq⟩

end Descent

end AffineTverberg.AffChain
