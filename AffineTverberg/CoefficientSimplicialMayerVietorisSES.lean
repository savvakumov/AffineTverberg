import AffineTverberg.CoefficientComparisonSubspace
import AffineTverberg.SimplicialMayerVietorisSES

set_option linter.style.header false

/-!
# Simplicial Mayer–Vietoris over arbitrary fields

The exact simplicial sequence and the direct-sum homology comparison are
constructed with the specified field. All maps retain their actual coefficient
formulas, preparing the comparison of short exact sequences.
-/

noncomputable section

open CategoryTheory Limits AffineTverberg.Simplicial

namespace AffineTverberg.Coefficients

variable (𝕜 : Type) [Field 𝕜]

namespace AffChain

variable {C D C' D' : ChainComplex (ModuleCat.{0} 𝕜) ℕ}

/-! ### Maps of degreewise direct sums -/

theorem pairMap_comp_pairFst (φ : C ⟶ C') (ψ : D ⟶ D') :
    pairMap 𝕜 φ ψ ≫ pairFst 𝕜 C' D' = pairFst 𝕜 C D ≫ φ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  rfl

theorem pairMap_comp_pairSnd (φ : C ⟶ C') (ψ : D ⟶ D') :
    pairMap 𝕜 φ ψ ≫ pairSnd 𝕜 C' D' = pairSnd 𝕜 C D ≫ ψ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  rfl

theorem pairInl_comp_pairMap (φ : C ⟶ C') (ψ : D ⟶ D') :
    pairInl 𝕜 C D ≫ pairMap 𝕜 φ ψ = φ ≫ pairInl 𝕜 C' D' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact Prod.ext rfl (map_zero ((ψ.f n).hom))

theorem pairInr_comp_pairMap (φ : C ⟶ C') (ψ : D ⟶ D') :
    pairInr 𝕜 C D ≫ pairMap 𝕜 φ ψ = ψ ≫ pairInr 𝕜 C' D' := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  exact Prod.ext (map_zero ((φ.f n).hom)) rfl

theorem pairMap_comp_pairDesc {E : ChainComplex (ModuleCat.{0} 𝕜) ℕ} (φ : C ⟶ C') (ψ : D ⟶ D')
    (α : C' ⟶ E) (β : D' ⟶ E) :
    pairMap 𝕜 φ ψ ≫ pairDesc 𝕜 α β = pairDesc 𝕜 (φ ≫ α) (ψ ≫ β) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  rfl

theorem pairDesc_comp {E E' : ChainComplex (ModuleCat.{0} 𝕜) ℕ} (α : C ⟶ E) (β : D ⟶ E)
    (γ : E ⟶ E') : pairDesc 𝕜 α β ≫ γ = pairDesc 𝕜 (α ≫ γ) (β ≫ γ) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  rintro ⟨a, b⟩
  exact map_add ((γ.f n).hom) _ _

theorem pairLift_comp {E : ChainComplex (ModuleCat.{0} 𝕜) ℕ} (α : E ⟶ C) (β : E ⟶ D)
    (φ : C ⟶ C') (ψ : D ⟶ D') :
    pairLift 𝕜 α β ≫ pairMap 𝕜 φ ψ = pairLift 𝕜 (α ≫ φ) (β ≫ ψ) := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  rfl

/-! ### Homology of a degreewise direct sum -/

/-- The homology functor takes the total identity of the direct sum bicone to
the identity. -/
theorem homology_pair_total (C D : ChainComplex (ModuleCat.{0} 𝕜) ℕ) (n : ℕ) :
    HomologicalComplex.homologyMap (pairFst 𝕜 C D) n ≫
        HomologicalComplex.homologyMap (pairInl 𝕜 C D) n +
      HomologicalComplex.homologyMap (pairSnd 𝕜 C D) n ≫
        HomologicalComplex.homologyMap (pairInr 𝕜 C D) n = 𝟙 _ := by
  have h := congrArg
    (fun φ => (HomologicalComplex.homologyFunctor (ModuleCat.{0} 𝕜) (ComplexShape.down ℕ) n).map φ)
    (pairBicone_total 𝕜 C D)
  simp only [Functor.map_add, Functor.map_comp] at h
  exact h.trans
    ((HomologicalComplex.homologyFunctor (ModuleCat.{0} 𝕜) (ComplexShape.down ℕ) n).map_id _)

/-- **A map of direct sums with quasi-isomorphic components is a
quasi-isomorphism.** -/
theorem isIso_homologyMap_pairMap (φ : C ⟶ C') (ψ : D ⟶ D') (n : ℕ)
    (hφ : IsIso (HomologicalComplex.homologyMap φ n))
    (hψ : IsIso (HomologicalComplex.homologyMap ψ n)) :
    IsIso (HomologicalComplex.homologyMap (pairMap 𝕜 φ ψ) n) := by
  have hfst : HomologicalComplex.homologyMap (pairMap 𝕜 φ ψ) n ≫
      HomologicalComplex.homologyMap (pairFst 𝕜 C' D') n =
      HomologicalComplex.homologyMap (pairFst 𝕜 C D) n ≫
        HomologicalComplex.homologyMap φ n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      pairMap_comp_pairFst 𝕜]
  have hsnd : HomologicalComplex.homologyMap (pairMap 𝕜 φ ψ) n ≫
      HomologicalComplex.homologyMap (pairSnd 𝕜 C' D') n =
      HomologicalComplex.homologyMap (pairSnd 𝕜 C D) n ≫
        HomologicalComplex.homologyMap ψ n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      pairMap_comp_pairSnd 𝕜]
  have hinl : HomologicalComplex.homologyMap (pairInl 𝕜 C D) n ≫
      HomologicalComplex.homologyMap (pairMap 𝕜 φ ψ) n =
      HomologicalComplex.homologyMap φ n ≫
        HomologicalComplex.homologyMap (pairInl 𝕜 C' D') n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      pairInl_comp_pairMap 𝕜]
  have hinr : HomologicalComplex.homologyMap (pairInr 𝕜 C D) n ≫
      HomologicalComplex.homologyMap (pairMap 𝕜 φ ψ) n =
      HomologicalComplex.homologyMap ψ n ≫
        HomologicalComplex.homologyMap (pairInr 𝕜 C' D') n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      pairInr_comp_pairMap 𝕜]
  refine ⟨⟨HomologicalComplex.homologyMap (pairFst 𝕜 C' D') n ≫
      inv (HomologicalComplex.homologyMap φ n) ≫
        HomologicalComplex.homologyMap (pairInl 𝕜 C D) n +
      HomologicalComplex.homologyMap (pairSnd 𝕜 C' D') n ≫
        inv (HomologicalComplex.homologyMap ψ n) ≫
          HomologicalComplex.homologyMap (pairInr 𝕜 C D) n, ?_, ?_⟩⟩
  · rw [Preadditive.comp_add]
    rw [← Category.assoc (HomologicalComplex.homologyMap (pairMap 𝕜 φ ψ) n)
      (HomologicalComplex.homologyMap (pairFst 𝕜 C' D') n),
      ← Category.assoc (HomologicalComplex.homologyMap (pairMap 𝕜 φ ψ) n)
      (HomologicalComplex.homologyMap (pairSnd 𝕜 C' D') n), hfst, hsnd]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    exact homology_pair_total 𝕜 C D n
  · rw [Preadditive.add_comp]
    simp only [Category.assoc, hinl, hinr]
    simp only [IsIso.inv_hom_id_assoc]
    exact homology_pair_total 𝕜 C' D' n

theorem quasiIso_pairMap (φ : C ⟶ C') (ψ : D ⟶ D') [QuasiIso φ] [QuasiIso ψ] :
    QuasiIso (pairMap 𝕜 φ ψ) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  refine isIso_homologyMap_pairMap 𝕜 φ ψ n ?_ ?_
  · rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact (quasiIso_iff φ).1 inferInstance n
  · rw [← quasiIsoAt_iff_isIso_homologyMap]
    exact (quasiIso_iff ψ).1 inferInstance n

end AffChain

section SimplicialSection

open AffineTverberg.Coefficients.AffChain

variable {V : Type} [Fintype V] [LinearOrder V]
variable {A B Cc K : Finset (Finset V)}

/-! ### Coefficients of simplicial chains -/

/-- The coefficient function of a chain of the shifted simplicial complex. -/
def chainCoeff {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ}
    (c : (simplicialChains 𝕜 hK).X m) : Finset V → 𝕜 :=
  Subtype.val (p := fun x : Finset V → 𝕜 => x ∈ chains 𝕜 K (m + 1)) c

/-- A chain of the shifted simplicial complex from its coefficient function. -/
def chainMk {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ} (x : Finset V → 𝕜)
    (hx : x ∈ chains 𝕜 K (m + 1)) : (simplicialChains 𝕜 hK).X m :=
  (⟨x, hx⟩ : ↥(chains 𝕜 K (m + 1)))

@[simp] theorem chainCoeff_mk {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ}
    (x : Finset V → 𝕜) (hx : x ∈ chains 𝕜 K (m + 1)) :
    chainCoeff 𝕜 hK (chainMk 𝕜 hK x hx) = x := rfl

theorem chainCoeff_mem {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ}
    (c : (simplicialChains 𝕜 hK).X m) : chainCoeff 𝕜 hK c ∈ chains 𝕜 K (m + 1) :=
  Subtype.property (p := fun x : Finset V → 𝕜 => x ∈ chains 𝕜 K (m + 1)) c

theorem chainCoeff_injective {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ}
    {c d : (simplicialChains 𝕜 hK).X m} (h : chainCoeff 𝕜 hK c = chainCoeff 𝕜 hK d) : c = d :=
  Subtype.ext h

@[simp] theorem chainCoeff_add {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ}
    (c d : (simplicialChains 𝕜 hK).X m) :
    chainCoeff 𝕜 hK (c + d) = chainCoeff 𝕜 hK c + chainCoeff 𝕜 hK d := rfl

@[simp] theorem chainCoeff_neg {K : Finset (Finset V)} (hK : FaceClosed K) {m : ℕ}
    (c : (simplicialChains 𝕜 hK).X m) : chainCoeff 𝕜 hK (-c) = -chainCoeff 𝕜 hK c := rfl

@[simp] theorem chainCoeff_zero {K : Finset (Finset V)} (hK : FaceClosed K) (m : ℕ) :
    chainCoeff 𝕜 hK (0 : (simplicialChains 𝕜 hK).X m) = 0 := rfl

/-! ### The simplicial Mayer-Vietoris maps -/

/-- The first simplicial Mayer-Vietoris map `c ↦ (c, -c)`. -/
def simpMvF (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) :
    simplicialChains 𝕜 hCc ⟶ pairCx 𝕜 (simplicialChains 𝕜 hA) (simplicialChains 𝕜 hB) :=
  pairLift 𝕜 (simplicialChainsInclusion 𝕜 hCc hA hCA) (-(simplicialChainsInclusion 𝕜 hCc hB hCB))

/-- The second simplicial Mayer-Vietoris map `(a, b) ↦ a + b`. -/
def simpMvG (hA : FaceClosed A) (hB : FaceClosed B) (hK : FaceClosed K)
    (hAK : A ⊆ K) (hBK : B ⊆ K) :
    pairCx 𝕜 (simplicialChains 𝕜 hA) (simplicialChains 𝕜 hB) ⟶ simplicialChains 𝕜 hK :=
  pairDesc 𝕜 (simplicialChainsInclusion 𝕜 hA hK hAK) (simplicialChainsInclusion 𝕜 hB hK hBK)

@[simp] theorem chainCoeff_inclusion (hA : FaceClosed A) (hK : FaceClosed K) (hAK : A ⊆ K)
    (m : ℕ) (c : (simplicialChains 𝕜 hA).X m) :
    chainCoeff 𝕜 hK (((simplicialChainsInclusion 𝕜 hA hK hAK).f m).hom c) = chainCoeff 𝕜 hA c := rfl

@[simp] theorem chainCoeff_simpMvG (hA : FaceClosed A) (hB : FaceClosed B) (hK : FaceClosed K)
    (hAK : A ⊆ K) (hBK : B ⊆ K) (m : ℕ)
    (x : (pairCx 𝕜 (simplicialChains 𝕜 hA) (simplicialChains 𝕜 hB)).X m) :
    chainCoeff 𝕜 hK (((simpMvG 𝕜 hA hB hK hAK hBK).f m).hom x) =
      chainCoeff 𝕜 hA x.1 + chainCoeff 𝕜 hB x.2 := rfl

@[simp] theorem simpMvF_fst (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (m : ℕ) (c : (simplicialChains 𝕜 hCc).X m) :
    chainCoeff 𝕜 hA (((simpMvF 𝕜 hCc hA hB hCA hCB).f m).hom c).1 = chainCoeff 𝕜 hCc c := rfl

@[simp] theorem simpMvF_snd (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (m : ℕ) (c : (simplicialChains 𝕜 hCc).X m) :
    chainCoeff 𝕜 hB (((simpMvF 𝕜 hCc hA hB hCA hCB).f m).hom c).2 = -chainCoeff 𝕜 hCc c := rfl

theorem simpMvF_comp_simpMvG (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hK : FaceClosed K) (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (hAK : A ⊆ K) (hBK : B ⊆ K) :
    simpMvF 𝕜 hCc hA hB hCA hCB ≫ simpMvG 𝕜 hA hB hK hAK hBK = 0 := by
  apply HomologicalComplex.hom_ext
  intro m
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro c
  refine chainCoeff_injective 𝕜 hK ?_
  change chainCoeff 𝕜 hCc c + -chainCoeff 𝕜 hCc c = (0 : Finset V → 𝕜)
  ring

/-- The simplicial Mayer-Vietoris short complex. -/
def simpMvShortComplex (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hK : FaceClosed K) (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (hAK : A ⊆ K) (hBK : B ⊆ K) :
    ShortComplex (ChainComplex (ModuleCat.{0} 𝕜) ℕ) :=
  ShortComplex.mk (simpMvF 𝕜 hCc hA hB hCA hCB) (simpMvG 𝕜 hA hB hK hAK hBK)
    (simpMvF_comp_simpMvG 𝕜 hCc hA hB hK hCA hCB hAK hBK)

theorem simpMvF_f_injective (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (m : ℕ) :
    Function.Injective ((simpMvF 𝕜 hCc hA hB hCA hCB).f m).hom := by
  intro c d hcd
  have h1 := congrArg (fun z => chainCoeff 𝕜 hA (Prod.fst z)) hcd
  simp only [simpMvF_fst 𝕜] at h1
  exact chainCoeff_injective 𝕜 hCc h1

theorem simpMvG_f_surjective (hA : FaceClosed A) (hB : FaceClosed B) (hK : FaceClosed K)
    (hAK : A ⊆ K) (hBK : B ⊆ K) (hKAB : K ⊆ A ∪ B) (m : ℕ) :
    Function.Surjective ((simpMvG 𝕜 hA hB hK hAK hBK).f m).hom := by
  intro c
  have hc : chainCoeff 𝕜 hK c ∈ chains 𝕜 (A ∪ B) (m + 1) :=
    chains_mono hKAB (m + 1) (chainCoeff_mem 𝕜 hK c)
  refine ⟨(chainMk 𝕜 hA (restrictTo 𝕜 A (chainCoeff 𝕜 hK c)) (restrictTo_mem_chains hc),
    chainMk 𝕜 hB (chainCoeff 𝕜 hK c - restrictTo 𝕜 A (chainCoeff 𝕜 hK c))
      (sub_restrictTo_mem_chains hc)), ?_⟩
  refine chainCoeff_injective 𝕜 hK ?_
  change restrictTo 𝕜 A (chainCoeff 𝕜 hK c) +
      (chainCoeff 𝕜 hK c - restrictTo 𝕜 A (chainCoeff 𝕜 hK c)) = chainCoeff 𝕜 hK c
  abel

theorem exists_simpMvF_eq (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hK : FaceClosed K) (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (hAK : A ⊆ K) (hBK : B ⊆ K)
    (hABC : ∀ t, t ∈ A → t ∈ B → t ∈ Cc) (m : ℕ)
    (x : (pairCx 𝕜 (simplicialChains 𝕜 hA) (simplicialChains 𝕜 hB)).X m)
    (hx : ((simpMvG 𝕜 hA hB hK hAK hBK).f m).hom x = 0) :
    ∃ y, ((simpMvF 𝕜 hCc hA hB hCA hCB).f m).hom y = x := by
  obtain ⟨a, b⟩ := x
  have hsum : chainCoeff 𝕜 hA a + chainCoeff 𝕜 hB b = 0 := by
    exact congrArg (fun z => chainCoeff 𝕜 hK z) hx
  have hb : chainCoeff 𝕜 hB b = -chainCoeff 𝕜 hA a := by
    linear_combination (norm := module) hsum
  have hmem : chainCoeff 𝕜 hA a ∈ chains 𝕜 Cc (m + 1) := by
    intro t ht
    have hA' := chainCoeff_mem 𝕜 hA a t ht
    have hB' : chainCoeff 𝕜 hB b t ≠ 0 := by
      rw [hb]
      simpa using ht
    exact ⟨hABC t hA'.1 (chainCoeff_mem 𝕜 hB b t hB').1, hA'.2⟩
  refine ⟨chainMk 𝕜 hCc (chainCoeff 𝕜 hA a) hmem, ?_⟩
  refine Prod.ext (chainCoeff_injective 𝕜 hA ?_) (chainCoeff_injective 𝕜 hB ?_)
  · rw [simpMvF_fst 𝕜, chainCoeff_mk 𝕜]
  · rw [simpMvF_snd 𝕜, chainCoeff_mk 𝕜, ← hb]

/-- **The simplicial Mayer-Vietoris sequence of chain complexes is short
exact.** -/
theorem simpMv_shortExact (hCc : FaceClosed Cc) (hA : FaceClosed A) (hB : FaceClosed B)
    (hK : FaceClosed K) (hCA : Cc ⊆ A) (hCB : Cc ⊆ B) (hAK : A ⊆ K) (hBK : B ⊆ K)
    (hKAB : K ⊆ A ∪ B) (hABC : ∀ t, t ∈ A → t ∈ B → t ∈ Cc) :
    (simpMvShortComplex 𝕜 hCc hA hB hK hCA hCB hAK hBK).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro m
  have hexact : ((simpMvShortComplex 𝕜 hCc hA hB hK hCA hCB hAK hBK).map
      (HomologicalComplex.eval (ModuleCat.{0} 𝕜) (ComplexShape.down ℕ) m)).Exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact exists_simpMvF_eq 𝕜 hCc hA hB hK hCA hCB hAK hBK hABC m x hx
  exact ShortComplex.ShortExact.mk' hexact
    ((ModuleCat.mono_iff_injective _).2 (simpMvF_f_injective 𝕜 hCc hA hB hCA hCB m))
    ((ModuleCat.epi_iff_surjective _).2 (simpMvG_f_surjective 𝕜 hA hB hK hAK hBK hKAB m))

end SimplicialSection

end AffineTverberg.Coefficients
