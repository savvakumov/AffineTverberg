import AffineTverberg.SingularHomologyDirectedUnion
import AffineTverberg.SingularHomologyRangeShift

set_option linter.style.header false

/-!
# Local to global descent from an arbitrarily fine family of opens

The local theorem for the actual sphere projection produces, around every
parameter, arbitrarily small opens over which the map has the sharp homology
range. Those opens are *not* closed under intersection with the same local
property, so the finite good-cover theorem does not apply.

This file proves the descent that does apply. Write `Q q` for the statement
that the map restricted over *every* open subset has range `q`. Binary gluing
with the shifted intersection hypothesis shows that `Q (q-1)` implies range
`q` for every finite union of basis opens, and compact supports upgrade that
to every open. Induction on `q` therefore gives `Q q` for all `q ≤ N`, and
`V = univ` is the global statement.
-/

noncomputable section

open CategoryTheory HomologicalComplex

namespace AffineTverberg.AffChain

variable {X Y : TopCat.{0}}

theorem HomologyRange.mono {C D : ChainComplex (ModuleCat.{0} ℝ) ℕ} {φ : C ⟶ D} {q q' : ℕ}
    (h : HomologyRange φ q) (hq : q' ≤ q) : HomologyRange φ q' :=
  ⟨fun k hk => h.1 k (lt_of_lt_of_le hk hq), fun k hk => h.2 k (le_trans hk hq)⟩

/-- The finite unions of members of `G` lying inside `V`. -/
def finiteUnionsIn (G : Set (Set Y)) (V : Set Y) : Set (Set Y) :=
  {W | ∃ 𝒮 : Set (Set Y), 𝒮 ⊆ G ∧ 𝒮.Finite ∧ (∀ A ∈ 𝒮, A ⊆ V) ∧ W = ⋃₀ 𝒮}

theorem empty_mem_finiteUnionsIn (G : Set (Set Y)) (V : Set Y) :
    (∅ : Set Y) ∈ finiteUnionsIn G V :=
  ⟨∅, by simp, Set.finite_empty, by simp, by simp⟩

theorem subset_of_mem_finiteUnionsIn {G : Set (Set Y)} {V W : Set Y}
    (h : W ∈ finiteUnionsIn G V) : W ⊆ V := by
  obtain ⟨𝒮, -, -, hsub, rfl⟩ := h
  rintro x ⟨A, hA, hxA⟩
  exact hsub A hA hxA

theorem isOpen_of_mem_finiteUnionsIn {G : Set (Set Y)} {V W : Set Y}
    (hopen : ∀ A ∈ G, IsOpen A) (h : W ∈ finiteUnionsIn G V) : IsOpen W := by
  obtain ⟨𝒮, hG, hfin, -, rfl⟩ := h
  exact isOpen_sUnion fun A hA => hopen A (hG hA)

theorem directed_finiteUnionsIn (G : Set (Set Y)) (V : Set Y) :
    ∀ A ∈ finiteUnionsIn G V, ∀ B ∈ finiteUnionsIn G V,
      ∃ D ∈ finiteUnionsIn G V, A ∪ B ⊆ D := by
  rintro _ ⟨𝒮, h𝒮G, h𝒮fin, h𝒮V, rfl⟩ _ ⟨𝒯, h𝒯G, h𝒯fin, h𝒯V, rfl⟩
  refine ⟨⋃₀ (𝒮 ∪ 𝒯), ⟨𝒮 ∪ 𝒯, Set.union_subset h𝒮G h𝒯G, h𝒮fin.union h𝒯fin, ?_, rfl⟩, ?_⟩
  · rintro A (hA | hA)
    · exact h𝒮V A hA
    · exact h𝒯V A hA
  · rintro x (⟨A, hA, hxA⟩ | ⟨A, hA, hxA⟩)
    · exact ⟨A, Or.inl hA, hxA⟩
    · exact ⟨A, Or.inr hA, hxA⟩

/-- Every open set of a fine family is covered by the finite unions inside it. -/
theorem sUnion_finiteUnionsIn {G : Set (Set Y)} {V : Set Y}
    (hbasis : ∀ y ∈ V, ∃ A ∈ G, y ∈ A ∧ A ⊆ V) :
    (⋃₀ finiteUnionsIn G V) = V := by
  apply Set.Subset.antisymm
  · rintro x ⟨W, hW, hxW⟩
    exact subset_of_mem_finiteUnionsIn hW hxW
  · intro x hx
    obtain ⟨A, hA, hxA, hAV⟩ := hbasis x hx
    exact ⟨A, ⟨{A}, by simpa using hA, Set.finite_singleton A, by simpa using hAV, by simp⟩, hxA⟩

section Descent

variable (f : X ⟶ Y) (G : Set (Set Y)) (N : ℕ)

/-- Range `q` for the finite unions of basis opens, from range `q` for each
basis open and the shifted range for arbitrary opens. -/
theorem homologyRange_finiteUnion_of_shift {q : ℕ} (hq : q ≤ N)
    (hopen : ∀ A ∈ G, IsOpen A)
    (hG : ∀ A ∈ G, HomologyRange (singChainsMap (preimageRestriction f A)) N)
    (hshift : ∀ V : Set Y, IsOpen V →
      HomologyRangeShift (singChainsMap (preimageRestriction f V)) q)
    (𝒮 : Set (Set Y)) (hfin : 𝒮.Finite) :
    𝒮 ⊆ G → HomologyRange (singChainsMap (preimageRestriction f (⋃₀ 𝒮))) q := by
  induction 𝒮, hfin using Set.Finite.induction_on with
  | empty =>
    intro _
    rw [Set.sUnion_empty]
    have := quasiIso_preimageRestriction_empty f
    exact homologyRange_of_quasiIso
      (singChainsMap (preimageRestriction f (∅ : Set Y))) q
  | @insert A 𝒮 _hA _hfin ih =>
    intro hins
    have hAG : A ∈ G := hins (Set.mem_insert A 𝒮)
    have h𝒮G : 𝒮 ⊆ G := fun B hB => hins (Set.mem_insert_of_mem A hB)
    have hAopen : IsOpen A := hopen A hAG
    have hSopen : IsOpen (⋃₀ 𝒮) := isOpen_sUnion fun B hB => hopen B (h𝒮G hB)
    have hunion : ⋃₀ (insert A 𝒮) = A ∪ ⋃₀ 𝒮 := Set.sUnion_insert A 𝒮
    rw [hunion]
    exact homologyRange_preimageRestriction_union_shift f hAopen hSopen
      ((hG A hAG).mono hq) (ih h𝒮G) (hshift (A ∩ ⋃₀ 𝒮) (hAopen.inter hSopen))

/-- Range `q` for every open set, from range `q` for the finite unions of
basis opens. -/
theorem homologyRange_open_of_finiteUnion {q : ℕ}
    (hopen : ∀ A ∈ G, IsOpen A)
    (hbasis : ∀ (y : Y) (W : Set Y), IsOpen W → y ∈ W → ∃ A ∈ G, y ∈ A ∧ A ⊆ W)
    (hfinite : ∀ 𝒮 : Set (Set Y), 𝒮.Finite → 𝒮 ⊆ G →
      HomologyRange (singChainsMap (preimageRestriction f (⋃₀ 𝒮))) q)
    (V : Set Y) (hV : IsOpen V) :
    HomologyRange (singChainsMap (preimageRestriction f V)) q := by
  set g := preimageRestriction f V with hg
  set 𝒟 : Set (Set (subSpace V)) :=
    (fun W => (Subtype.val : V → Y) ⁻¹' W) '' finiteUnionsIn G V with h𝒟
  have hne : 𝒟.Nonempty := ⟨_, ⟨∅, empty_mem_finiteUnionsIn G V, rfl⟩⟩
  have hopen𝒟 : ∀ A ∈ 𝒟, IsOpen A := by
    rintro _ ⟨W, hW, rfl⟩
    exact (isOpen_of_mem_finiteUnionsIn hopen hW).preimage continuous_subtype_val
  have hdir𝒟 : ∀ A ∈ 𝒟, ∀ B ∈ 𝒟, ∃ D ∈ 𝒟, A ∪ B ⊆ D := by
    rintro _ ⟨W, hW, rfl⟩ _ ⟨W', hW', rfl⟩
    obtain ⟨D, hD, hDsub⟩ := directed_finiteUnionsIn G V W hW W' hW'
    refine ⟨_, ⟨D, hD, rfl⟩, ?_⟩
    rintro x (hx | hx)
    · exact hDsub (Or.inl hx)
    · exact hDsub (Or.inr hx)
  have hcov𝒟 : (⋃₀ 𝒟) = Set.univ := by
    apply Set.eq_univ_of_forall
    rintro ⟨x, hx⟩
    have hxV : x ∈ (⋃₀ finiteUnionsIn G V) := by
      rw [sUnion_finiteUnionsIn (fun y hy => hbasis y V hV hy)]
      exact hx
    obtain ⟨W, hW, hxW⟩ := hxV
    exact ⟨_, ⟨W, hW, rfl⟩, hxW⟩
  have hrange : ∀ A ∈ 𝒟, HomologyRange (singChainsMap (preimageRestriction g A)) q := by
    rintro _ ⟨W, hW, rfl⟩
    obtain ⟨𝒮, h𝒮G, h𝒮fin, h𝒮V, rfl⟩ := hW
    have hsub : (⋃₀ 𝒮) ⊆ V := subset_of_mem_finiteUnionsIn
      ⟨𝒮, h𝒮G, h𝒮fin, h𝒮V, rfl⟩
    exact (homologyRange_preimageRestriction_nested f hsub q).mpr
      (hfinite 𝒮 h𝒮fin h𝒮G)
  exact homologyRange_of_directed_open_cover g q hne hopen𝒟 hdir𝒟 hcov𝒟 hrange

/-- **The descent theorem.** If a fine family of opens has the sharp homology
range `N`, then every open subset does, in every degree up to `N`. -/
theorem homologyRange_open_of_basis
    (hopen : ∀ A ∈ G, IsOpen A)
    (hbasis : ∀ (y : Y) (W : Set Y), IsOpen W → y ∈ W → ∃ A ∈ G, y ∈ A ∧ A ⊆ W)
    (hG : ∀ A ∈ G, HomologyRange (singChainsMap (preimageRestriction f A)) N) :
    ∀ q, q ≤ N → ∀ V : Set Y, IsOpen V →
      HomologyRange (singChainsMap (preimageRestriction f V)) q := by
  intro q
  induction q with
  | zero =>
    intro _ V hV
    refine homologyRange_open_of_finiteUnion f G hopen hbasis ?_ V hV
    intro 𝒮 hfin h𝒮
    exact homologyRange_finiteUnion_of_shift f G N (Nat.zero_le N) hopen hG
      (fun W _ => homologyRangeShift_zero _) 𝒮 hfin h𝒮
  | succ q ih =>
    intro hq V hV
    have hprev : ∀ W : Set Y, IsOpen W →
        HomologyRange (singChainsMap (preimageRestriction f W)) q :=
      ih (Nat.le_of_succ_le hq)
    refine homologyRange_open_of_finiteUnion f G hopen hbasis ?_ V hV
    intro 𝒮 hfin h𝒮
    refine homologyRange_finiteUnion_of_shift f G N hq hopen hG ?_ 𝒮 hfin h𝒮
    intro W hW
    exact (homologyRangeShift_succ_iff _ q).mpr (hprev W hW)

/-- **The global range for the map itself.** -/
theorem homologyRange_of_basis
    (hopen : ∀ A ∈ G, IsOpen A)
    (hbasis : ∀ (y : Y) (W : Set Y), IsOpen W → y ∈ W → ∃ A ∈ G, y ∈ A ∧ A ⊆ W)
    (hG : ∀ A ∈ G, HomologyRange (singChainsMap (preimageRestriction f A)) N) :
    HomologyRange (singChainsMap f) N :=
  (homologyRange_preimageRestriction_univ_iff f N).mp
    (homologyRange_open_of_basis f G N hopen hbasis hG N le_rfl Set.univ isOpen_univ)

end Descent

end AffineTverberg.AffChain
