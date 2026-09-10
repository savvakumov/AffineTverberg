import AffineTverberg.ComparisonSubspace

set_option linter.style.header false

/-!
# The simplicial Mayer-Vietoris short exact sequence of chain complexes

For face-closed families `A`, `B`, `Cc`, `K` with `Cc = A ∩ B`, `A ∪ B ⊇ K`
and `A, B ⊆ K`, the sequence

`0 ⟶ C(Cc) ⟶ C(A) ⊕ C(B) ⟶ C(K) ⟶ 0`

of oriented simplicial chain complexes is short exact.  This is the simplicial
half of the Mayer-Vietoris comparison; the singular half is
`AffineTverberg.AffChain.mvShortExact`.

The file also contains the two general facts about the degreewise direct sum
`pairCx` that the comparison argument needs: a map of pairs whose two
components are quasi-isomorphisms is a quasi-isomorphism, and the
compatibilities of `pairMap` with `pairDesc`.
-/

noncomputable section

open CategoryTheory Limits

namespace AffineTverberg

namespace AffChain

variable {C D C' D' : ChainComplex (ModuleCat.{0} ℝ) ℕ}

/-! ### Maps of degreewise direct sums -/

theorem pairMap_comp_pairFst (φ : C ⟶ C') (ψ : D ⟶ D') :
    pairMap φ ψ ≫ pairFst C' D' = pairFst C D ≫ φ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  rfl

theorem pairMap_comp_pairSnd (φ : C ⟶ C') (ψ : D ⟶ D') :
    pairMap φ ψ ≫ pairSnd C' D' = pairSnd C D ≫ ψ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  rfl

theorem pairInl_comp_pairMap (φ : C ⟶ C') (ψ : D ⟶ D') :
    pairInl C D ≫ pairMap φ ψ = φ ≫ pairInl C' D' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact Prod.ext rfl (map_zero ((ψ.f n).hom))

theorem pairInr_comp_pairMap (φ : C ⟶ C') (ψ : D ⟶ D') :
    pairInr C D ≫ pairMap φ ψ = ψ ≫ pairInr C' D' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact Prod.ext (map_zero ((φ.f n).hom)) rfl

theorem pairMap_comp_pairDesc {E : ChainComplex (ModuleCat.{0} ℝ) ℕ} (φ : C ⟶ C') (ψ : D ⟶ D')
    (α : C' ⟶ E) (β : D' ⟶ E) :
    pairMap φ ψ ≫ pairDesc α β = pairDesc (φ ≫ α) (ψ ≫ β) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  rfl

theorem pairDesc_comp {E E' : ChainComplex (ModuleCat.{0} ℝ) ℕ} (α : C ⟶ E) (β : D ⟶ E)
    (γ : E ⟶ E') : pairDesc α β ≫ γ = pairDesc (α ≫ γ) (β ≫ γ) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  exact map_add ((γ.f n).hom) _ _

theorem pairLift_comp {E : ChainComplex (ModuleCat.{0} ℝ) ℕ} (α : E ⟶ C) (β : E ⟶ D)
    (φ : C ⟶ C') (ψ : D ⟶ D') :
    pairLift α β ≫ pairMap φ ψ = pairLift (α ≫ φ) (β ≫ ψ) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-! ### Homology of a degreewise direct sum -/

/-- The homology functor takes the total identity of the direct sum bicone to
the identity. -/
theorem homology_pair_total (C D : ChainComplex (ModuleCat.{0} ℝ) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap (pairFst C D) n ≫
        HomologicalComplex.homologyMap (pairInl C D) n +
      HomologicalComplex.homologyMap (pairSnd C D) n ≫
        HomologicalComplex.homologyMap (pairInr C D) n = 𝟙 _ := by
  have h := congrArg
    (fun φ => (HomologicalComplex.homologyFunctor (ModuleCat.{0} ℝ) (ComplexShape.down ℕ) n).map φ)
    (pairBicone_total C D)
  simp only [Functor.map_add, Functor.map_comp] at h
  exact h.trans
    ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℝ) (ComplexShape.down ℕ) n).map_id _)

/-- **A map of direct sums with quasi-isomorphic components is a
quasi-isomorphism.** -/
theorem isIso_homologyMap_pairMap (φ : C ⟶ C') (ψ : D ⟶ D') (n : ℕ)
    (hφ : IsIso (HomologicalComplex.homologyMap φ n))
    (hψ : IsIso (HomologicalComplex.homologyMap ψ n)) :
    IsIso (HomologicalComplex.homologyMap (pairMap φ ψ) n) := by
  have hfst : HomologicalComplex.homologyMap (pairMap φ ψ) n ≫
      HomologicalComplex.homologyMap (pairFst C' D') n =
      HomologicalComplex.homologyMap (pairFst C D) n ≫
        HomologicalComplex.homologyMap φ n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      pairMap_comp_pairFst]
  have hsnd : HomologicalComplex.homologyMap (pairMap φ ψ) n ≫
      HomologicalComplex.homologyMap (pairSnd C' D') n =
      HomologicalComplex.homologyMap (pairSnd C D) n ≫
        HomologicalComplex.homologyMap ψ n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      pairMap_comp_pairSnd]
  have hinl : HomologicalComplex.homologyMap (pairInl C D) n ≫
      HomologicalComplex.homologyMap (pairMap φ ψ) n =
      HomologicalComplex.homologyMap φ n ≫
        HomologicalComplex.homologyMap (pairInl C' D') n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      pairInl_comp_pairMap]
  have hinr : HomologicalComplex.homologyMap (pairInr C D) n ≫
      HomologicalComplex.homologyMap (pairMap φ ψ) n =
      HomologicalComplex.homologyMap ψ n ≫
        HomologicalComplex.homologyMap (pairInr C' D') n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      pairInr_comp_pairMap]
  refine ⟨⟨HomologicalComplex.homologyMap (pairFst C' D') n ≫
      inv (HomologicalComplex.homologyMap φ n) ≫
        HomologicalComplex.homologyMap (pairInl C D) n +
      HomologicalComplex.homologyMap (pairSnd C' D') n ≫
        inv (HomologicalComplex.homologyMap ψ n) ≫
          HomologicalComplex.homologyMap (pairInr C D) n, ?_, ?_⟩⟩
  · rw [Preadditive.comp_add]
    rw [← Category.assoc (HomologicalComplex.homologyMap (pairMap φ ψ) n)
      (HomologicalComplex.homologyMap (pairFst C' D') n),
      ← Category.assoc (HomologicalComplex.homologyMap (pairMap φ ψ) n)
      (HomologicalComplex.homologyMap (pairSnd C' D') n), hfst, hsnd]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact homology_pair_total C D n
  · rw [Preadditive.add_comp]
    simp only [Category.assoc, hinl, hinr]
    simp only [IsIso.inv_hom_id_assoc]
    exact homology_pair_total C' D' n

theorem quasiIso_pairMap (φ : C ⟶ C') (ψ : D ⟶ D') [QuasiIso φ] [QuasiIso ψ] :
    QuasiIso (pairMap φ ψ) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  refine isIso_homologyMap_pairMap φ ψ n ?_ ?_
  · rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact (quasiIso_iff φ).1 inferInstance n
  · rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact (quasiIso_iff ψ).1 inferInstance n

end AffChain

namespace Simplicial

open AffChain

variable {V : Type} [Fintype V] [LinearOrder V]
variable {A B Cc K : Finset (Finset V)}

/-! ### Coefficients of simplicial chains -/

/-- The coefficient function of a chain of the shifted simplicial complex. -/
def chainCoeff {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ}
    (c : (simplicialChains hK).X m) : Finset V → ℝ :=
  Subtype.val (p := fun x : Finset V → ℝ => x ∈ chains ℝ K (m + 1)) c

/-- A chain of the shifted simplicial complex from its coefficient function. -/
def chainMk {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ} (x : Finset V → ℝ)
    (hx : x ∈ chains ℝ K (m + 1)) : (simplicialChains hK).X m :=
  (⟨x, hx⟩ : ↥(chains ℝ K (m + 1)))

@[simp] theorem chainCoeff_mk {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ}
    (x : Finset V → ℝ) (hx : x ∈ chains ℝ K (m + 1)) :
    chainCoeff hK (chainMk hK x hx) = x := rfl

theorem chainCoeff_mem {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ}
    (c : (simplicialChains hK).X m) : chainCoeff hK c ∈ chains ℝ K (m + 1) :=
  Subtype.property (p := fun x : Finset V → ℝ => x ∈ chains ℝ K (m + 1)) c

theorem chainCoeff_injective {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ}
    {c d : (simplicialChains hK).X m} (h : chainCoeff hK c = chainCoeff hK d) : c = d :=
  Subtype.ext h

@[simp] theorem chainCoeff_add {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ}
    (c d : (simplicialChains hK).X m) :
    chainCoeff hK (c + d) = chainCoeff hK c + chainCoeff hK d := rfl

@[simp] theorem chainCoeff_neg {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ}
    (c : (simplicialChains hK).X m) : chainCoeff hK (-c) = -chainCoeff hK c := rfl

@[simp] theorem chainCoeff_zero {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    chainCoeff hK (0 : (simplicialChains hK).X m) = 0 := rfl

/-! ### The simplicial Mayer-Vietoris maps -/

/-- The first simplicial Mayer-Vietoris map `c ↦ (c, -c)`. -/
def simpMvF (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) :
    simplicialChains hCc ⟶ pairCx (simplicialChains hA) (simplicialChains hB) :=
  pairLift (simplicialChainsInclusion hCc hA hCA) (-(simplicialChainsInclusion hCc hB hCB))

/-- The second simplicial Mayer-Vietoris map `(a, b) ↦ a + b`. -/
def simpMvG (hA : FaceClosed A) (hB : FaceClosed B) (hK : FaceClosed K)
    (hAK : A ⊆ K) (hBK : B ⊆ K) :
    pairCx (simplicialChains hA) (simplicialChains hB) ⟶ simplicialChains hK :=
  pairDesc (simplicialChainsInclusion hA hK hAK) (simplicialChainsInclusion hB hK hBK)

@[simp] theorem chainCoeff_inclusion (hA : FaceClosed A) (hK : FaceClosed K) (hAK : A ⊆ K)
    (m : ℕ) (c : (simplicialChains hA).X m) :
    chainCoeff hK (((simplicialChainsInclusion hA hK hAK).f m).hom c) = chainCoeff hA c := rfl

@[simp] theorem chainCoeff_simpMvG (hA : FaceClosed A) (hB : FaceClosed B) (hK : FaceClosed K)
    (hAK : A ⊆ K) (hBK : B ⊆ K) (m : ℕ)
    (x : (pairCx (simplicialChains hA) (simplicialChains hB)).X m) :
    chainCoeff hK (((simpMvG hA hB hK hAK hBK).f m).hom x) =
      chainCoeff hA x.1 + chainCoeff hB x.2 := rfl

@[simp] theorem simpMvF_fst (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (m : ℕ) (c : (simplicialChains hCc).X m) :
    chainCoeff hA (((simpMvF hCc hA hB hCA hCB).f m).hom c).1 = chainCoeff hCc c := rfl

@[simp] theorem simpMvF_snd (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (m : ℕ) (c : (simplicialChains hCc).X m) :
    chainCoeff hB (((simpMvF hCc hA hB hCA hCB).f m).hom c).2 = -chainCoeff hCc c := rfl

theorem simpMvF_comp_simpMvG (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hK : FaceClosed K) (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (hAK : A ⊆ K) (hBK : B ⊆ K) :
    simpMvF hCc hA hB hCA hCB ≫ simpMvG hA hB hK hAK hBK = 0 := by
  apply HomologicalComplex.hom_ext
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  refine chainCoeff_injective hK ?_
  change chainCoeff hCc c + -chainCoeff hCc c = (0 : Finset V → ℝ)
  ring

/-- The simplicial Mayer-Vietoris short complex. -/
def simpMvShortComplex (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hK : FaceClosed K) (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (hAK : A ⊆ K) (hBK : B ⊆ K) :
    ShortComplex (ChainComplex (ModuleCat.{0} ℝ) ℕ) :=
  ShortComplex.mk (simpMvF hCc hA hB hCA hCB) (simpMvG hA hB hK hAK hBK)
    (simpMvF_comp_simpMvG hCc hA hB hK hCA hCB hAK hBK)

theorem simpMvF_f_injective (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (m : ℕ) :
    Function.Injective ((simpMvF hCc hA hB hCA hCB).f m).hom := by
  intro c d hcd
  have h1 := congrArg (fun z => chainCoeff hA (Prod.fst z)) hcd
  simp only [simpMvF_fst] at h1
  exact chainCoeff_injective hCc h1

theorem simpMvG_f_surjective (hA : FaceClosed A) (hB : FaceClosed B) (hK : FaceClosed K)
    (hAK : A ⊆ K) (hBK : B ⊆ K) (hKAB : K ⊆ A ∪ B) (m : ℕ) :
    Function.Surjective ((simpMvG hA hB hK hAK hBK).f m).hom := by
  intro c
  have hc : chainCoeff hK c ∈ chains ℝ (A ∪ B) (m + 1) :=
    chains_mono hKAB (m + 1) (chainCoeff_mem hK c)
  refine ⟨(chainMk hA (restrictTo ℝ A (chainCoeff hK c)) (restrictTo_mem_chains hc),
    chainMk hB (chainCoeff hK c - restrictTo ℝ A (chainCoeff hK c))
      (sub_restrictTo_mem_chains hc)), ?_⟩
  refine chainCoeff_injective hK ?_
  change restrictTo ℝ A (chainCoeff hK c) +
      (chainCoeff hK c - restrictTo ℝ A (chainCoeff hK c)) = chainCoeff hK c
  abel

theorem exists_simpMvF_eq (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hK : FaceClosed K) (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (hAK : A ⊆ K) (hBK : B ⊆ K)
    (hABC : ∀ t, t ∈ A → t ∈ B → t ∈ Cc) (m : ℕ)
    (x : (pairCx (simplicialChains hA) (simplicialChains hB)).X m)
    (hx : ((simpMvG hA hB hK hAK hBK).f m).hom x = 0) :
    ∃ y, ((simpMvF hCc hA hB hCA hCB).f m).hom y = x := by
  obtain ⟨a, b⟩ := x
  have hsum : chainCoeff hA a + chainCoeff hB b = 0 := by
    exact congrArg (fun z => chainCoeff hK z) hx
  have hb : chainCoeff hB b = -chainCoeff hA a := by
    linear_combination (norm := module) hsum
  have hmem : chainCoeff hA a ∈ chains ℝ Cc (m + 1) := by
    intro t ht
    have hA' := chainCoeff_mem hA a t ht
    have hB' : chainCoeff hB b t ≠ 0 := by
      rw [hb]
      simpa using ht
    exact ⟨hABC t hA'.1 (chainCoeff_mem hB b t hB').1, hA'.2⟩
  refine ⟨chainMk hCc (chainCoeff hA a) hmem, ?_⟩
  refine Prod.ext (chainCoeff_injective hA ?_) (chainCoeff_injective hB ?_)
  · rw [simpMvF_fst, chainCoeff_mk]
  · rw [simpMvF_snd, chainCoeff_mk, ← hb]

/-- **The simplicial Mayer-Vietoris sequence of chain complexes is short
exact.** -/
theorem simpMv_shortExact (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hK : FaceClosed K) (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (hAK : A ⊆ K) (hBK : B ⊆ K)
    (hKAB : K ⊆ A ∪ B) (hABC : ∀ t, t ∈ A → t ∈ B → t ∈ Cc) :
    (simpMvShortComplex hCc hA hB hK hCA hCB hAK hBK).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro m
  have hexact : ((simpMvShortComplex hCc hA hB hK hCA hCB hAK hBK).map
      (HomologicalComplex.eval (ModuleCat.{0} ℝ) (ComplexShape.down ℕ) m)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact exists_simpMvF_eq hCc hA hB hK hCA hCB hAK hBK hABC m x hx
  exact ShortComplex.ShortExact.mk' hexact
    ((ModuleCat.mono_iff_injective _).2 (simpMvF_f_injective hCc hA hB hCA hCB m))
    ((ModuleCat.epi_iff_surjective _).2 (simpMvG_f_surjective hA hB hK hAK hBK hKAB m))

end Simplicial

end AffineTverberg
