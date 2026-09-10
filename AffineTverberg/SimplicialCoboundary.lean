import AffineTverberg.SimplicialCohomology

set_option linter.style.header false

/-!
# The oriented coboundary on coefficient functions

`SimplicialCohomology` models cochains as the linear dual of the chain groups.
For the dual block / double complex arguments it is much more convenient to
have the *function* model: a cochain is again a coefficient function
`Finset V → 𝕜`, and the coboundary is the transpose of the oriented boundary,

`(δ a) g = ∑ v ∈ g, orientedSign (g.erase v) v * a (g.erase v)`.

This file develops that model: the adjunction formula with the boundary for the
standard pairing, `δ ∘ δ = 0`, the family-restricted coboundary `coboundaryOn`
of a face-closed family, and the fact that exactness of the cochain complex of
a family in a degree is *equivalent* to reduced acyclicity of the family in the
same degree.  Nothing new is assumed: the equivalence is finite-dimensional
linear algebra over a field.
-/

noncomputable section

namespace AffineTverberg.Simplicial

variable {𝕜 V : Type*} [Field 𝕜] [Fintype V] [LinearOrder V]

/-! ### The coboundary -/

/-- The oriented coboundary on coefficient functions: the transpose of the
oriented boundary `boundary`. -/
def coboundaryFun (𝕜 V : Type*) [Field 𝕜] [Fintype V] [LinearOrder V] :
    (Finset V → 𝕜) →ₗ[𝕜] (Finset V → 𝕜) where
  toFun a g := ∑ v ∈ g, orientedSign 𝕜 (g.erase v) v * a (g.erase v)
  map_add' a b := by
    funext g
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' r a := by
    funext g
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring

@[simp]
theorem coboundaryFun_apply (a : Finset V → 𝕜) (g : Finset V) :
    coboundaryFun 𝕜 V a g = ∑ v ∈ g, orientedSign 𝕜 (g.erase v) v * a (g.erase v) := rfl

/-- **Adjointness**: the coboundary is the transpose of the boundary for the
standard pairing on coefficient functions. -/
theorem sum_coboundaryFun_mul (a c : Finset V → 𝕜) :
    ∑ g : Finset V, coboundaryFun 𝕜 V a g * c g = ∑ f : Finset V, a f * boundary 𝕜 V c f := by
  classical
  have h1 : ∑ g : Finset V, coboundaryFun 𝕜 V a g * c g
      = ∑ g : Finset V, ∑ v ∈ g, orientedSign 𝕜 (g.erase v) v * a (g.erase v) * c g := by
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [coboundaryFun_apply, Finset.sum_mul]
  have h2 : ∑ f : Finset V, a f * boundary 𝕜 V c f
      = ∑ f : Finset V, ∑ v ∈ fᶜ, orientedSign 𝕜 f v * a f * c (insert v f) := by
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [boundary_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [h1, h2]
  rw [Finset.sum_sigma' Finset.univ (fun g : Finset V => g)
    (fun g v => orientedSign 𝕜 (Finset.erase g v) v * a (g.erase v) * c g)]
  rw [Finset.sum_sigma' Finset.univ (fun f : Finset V => fᶜ)
    (fun f v => orientedSign 𝕜 f v * a f * c (insert v f))]
  refine Finset.sum_nbij' (fun x => ⟨x.1.erase x.2, x.2⟩) (fun y => ⟨insert y.2 y.1, y.2⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨g, v⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_compl] at hx ⊢
    exact Finset.notMem_erase v g
  · rintro ⟨f, v⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_compl] at hy ⊢
    exact Finset.mem_insert_self v f
  · rintro ⟨g, v⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hx
    simp [Finset.insert_erase hx]
  · rintro ⟨f, v⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Finset.mem_compl] at hy
    simp [Finset.erase_insert hy]
  · rintro ⟨g, v⟩ hx
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and] at hx
    simp [Finset.insert_erase hx]

/-- The standard pairing on coefficient functions is nondegenerate. -/
theorem eq_zero_of_sum_mul_eq_zero {x : Finset V → 𝕜}
    (h : ∀ c : Finset V → 𝕜, ∑ g : Finset V, x g * c g = 0) : x = 0 := by
  classical
  funext g₀
  have hx := h (Pi.single g₀ 1)
  rw [Finset.sum_eq_single g₀] at hx
  · simpa using hx
  · intro b _ hb
    simp [hb]
  · intro h'
    simp at h'

/-- `δ ∘ δ = 0`, by transposing `∂ ∘ ∂ = 0`. -/
theorem coboundaryFun_coboundaryFun (a : Finset V → 𝕜) :
    coboundaryFun 𝕜 V (coboundaryFun 𝕜 V a) = 0 := by
  apply eq_zero_of_sum_mul_eq_zero
  intro c
  rw [sum_coboundaryFun_mul, sum_coboundaryFun_mul a (boundary 𝕜 V c)]
  have h0 : boundary 𝕜 V (boundary 𝕜 V c) = 0 := boundary_boundary_apply c
  simp only [h0, Pi.zero_apply, mul_zero, Finset.sum_const_zero]

/-! ### The coboundary of a face-closed family -/

/-- The restriction of a coefficient function to a family of simplices. -/
def restrictFamily (K : Finset (Finset V)) (x : Finset V → 𝕜) : Finset V → 𝕜 :=
  fun g => if g ∈ K then x g else 0

omit [Fintype V] in
@[simp]
theorem restrictFamily_apply (K : Finset (Finset V)) (x : Finset V → 𝕜) (g : Finset V) :
    restrictFamily K x g = if g ∈ K then x g else 0 := rfl

/-- Restriction to a family, as a linear map. -/
def restrictFamilyLinear (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) :
    (Finset V → 𝕜) →ₗ[𝕜] (Finset V → 𝕜) where
  toFun x := restrictFamily K x
  map_add' x y := by
    funext g
    by_cases h : g ∈ K <;> simp [restrictFamily, h]
  map_smul' r x := by
    funext g
    by_cases h : g ∈ K <;> simp [restrictFamily, h]

/-- The coboundary of the cochain complex of the family `K`: the ambient
coboundary followed by restriction to `K`. -/
def coboundaryOn (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) :
    (Finset V → 𝕜) →ₗ[𝕜] (Finset V → 𝕜) :=
  (restrictFamilyLinear 𝕜 K).comp (coboundaryFun 𝕜 V)

@[simp]
theorem coboundaryOn_apply (K : Finset (Finset V)) (a : Finset V → 𝕜) (g : Finset V) :
    coboundaryOn 𝕜 K a g = if g ∈ K then coboundaryFun 𝕜 V a g else 0 := rfl

theorem coboundaryOn_mem_chains {K : Finset (Finset V)} {n : ℕ} {a : Finset V → 𝕜}
    (ha : a ∈ chains 𝕜 K n) : coboundaryOn 𝕜 K a ∈ chains 𝕜 K (n + 1) := by
  classical
  intro g hg
  rw [coboundaryOn_apply] at hg
  by_cases hK : g ∈ K
  · refine ⟨hK, ?_⟩
    simp only [hK, ↓reduceIte] at hg
    -- some term of the defining sum is nonzero
    have : ∃ v ∈ g, orientedSign 𝕜 (g.erase v) v * a (g.erase v) ≠ 0 := by
      by_contra hcon
      simp only [not_exists, not_and, ne_eq, not_not] at hcon
      exact hg (by rw [coboundaryFun_apply]; exact Finset.sum_eq_zero fun v hv => hcon v hv)
    obtain ⟨v, hv, hne⟩ := this
    have hav : a (g.erase v) ≠ 0 := fun h => hne (by rw [h, mul_zero])
    have hcard := (ha _ hav).2
    rw [Finset.card_erase_of_mem hv] at hcard
    have hpos : 1 ≤ g.card := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  · simp [hK] at hg

theorem coboundaryOn_coboundaryOn {K : Finset (Finset V)} (hK : FaceClosed K)
    (a : Finset V → 𝕜) : coboundaryOn 𝕜 K (coboundaryOn 𝕜 K a) = 0 := by
  classical
  funext g
  rw [coboundaryOn_apply]
  by_cases hg : g ∈ K
  · simp only [hg, ↓reduceIte, coboundaryFun_apply]
    have hstep : ∀ v ∈ g, orientedSign 𝕜 (g.erase v) v * coboundaryOn 𝕜 K a (g.erase v)
        = orientedSign 𝕜 (g.erase v) v * coboundaryFun 𝕜 V a (g.erase v) := by
      intro v hv
      rw [coboundaryOn_apply]
      simp only [hK g hg _ (Finset.erase_subset v g), ↓reduceIte]
    rw [Finset.sum_congr rfl hstep]
    have := congrFun (coboundaryFun_coboundaryFun (𝕜 := 𝕜) (V := V) a) g
    rw [coboundaryFun_apply] at this
    simpa using this
  · simp [hg]

/-! ### Cochain exactness equals chain exactness -/

section Bridge

variable {K : Finset (Finset V)}

/-- The bundled coboundary on the chain groups of `K`. -/
def cochainCoboundary (𝕜 : Type*) [Field 𝕜] {K : Finset (Finset V)} (_hK : FaceClosed K)
    (n : ℕ) : chains 𝕜 K n →ₗ[𝕜] chains 𝕜 K (n + 1) :=
  LinearMap.codRestrict _ ((coboundaryOn 𝕜 K).comp (chains 𝕜 K n).subtype)
    (fun a => coboundaryOn_mem_chains a.2)

@[simp]
theorem cochainCoboundary_coe (hK : FaceClosed K) (n : ℕ) (a : chains 𝕜 K n) :
    (cochainCoboundary 𝕜 hK n a : Finset V → 𝕜) = coboundaryOn 𝕜 K a := rfl

/-- Exactness of the cochain complex of `K` in degree `n + 1`. -/
def IsCoacyclicAt (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (n : ℕ) : Prop :=
  ∀ a ∈ chains 𝕜 K (n + 1), coboundaryOn 𝕜 K a = 0 →
    ∃ b ∈ chains 𝕜 K n, coboundaryOn 𝕜 K b = a

omit [Fintype V] in
theorem single_mem_chains {n : ℕ} {s : Finset V} (hs : s ∈ K) (hcard : s.card = n) :
    (Pi.single s (1 : 𝕜) : Finset V → 𝕜) ∈ chains 𝕜 K n := by
  classical
  intro t ht
  have hts : t = s := by
    by_contra hne
    exact ht (by simp [hne])
  exact hts ▸ ⟨hs, hcard⟩

/-- The standard pairing, as a map into the linear dual of the chain group. -/
def chainPairing (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (n : ℕ) :
    chains 𝕜 K n →ₗ[𝕜] Module.Dual 𝕜 (chains 𝕜 K n) where
  toFun a :=
    { toFun := fun c => ∑ s : Finset V, (a : Finset V → 𝕜) s * (c : Finset V → 𝕜) s
      map_add' := fun c d => by
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
        rw [Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
          Finset.mul_sum]
        exact Finset.sum_congr rfl fun s _ => by ring }
  map_add' a b := by
    ext c
    simp only [Submodule.coe_add, Pi.add_apply, add_mul, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.add_apply]
    rw [Finset.sum_add_distrib]
  map_smul' r a := by
    ext c
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, LinearMap.coe_mk, AddHom.coe_mk,
      RingHom.id_apply, LinearMap.smul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring

omit [LinearOrder V] in
theorem chainPairing_apply (n : ℕ) (a c : chains 𝕜 K n) :
    chainPairing 𝕜 K n a c = ∑ s : Finset V, (a : Finset V → 𝕜) s * (c : Finset V → 𝕜) s := rfl

theorem chainPairing_injective (n : ℕ) : Function.Injective (chainPairing 𝕜 K n) := by
  classical
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun a ha => ?_
  refine Subtype.ext (funext fun s => ?_)
  by_cases hs : (a : Finset V → 𝕜) s = 0
  · simpa using hs
  · exfalso
    obtain ⟨hsK, hscard⟩ := a.2 s hs
    have h := congrArg (fun φ : Module.Dual 𝕜 (chains 𝕜 K n) =>
      φ ⟨Pi.single s 1, single_mem_chains hsK hscard⟩) (LinearMap.mem_ker.mp ha)
    simp only [chainPairing_apply] at h
    rw [Finset.sum_eq_single s] at h
    · simp only [Pi.single_eq_same, mul_one, LinearMap.zero_apply] at h
      exact hs h
    · intro t _ hts
      simp [Ne.symm hts]
    · intro hcon
      exact absurd (Finset.mem_univ s) hcon

theorem chainPairing_bijective (n : ℕ) : Function.Bijective (chainPairing 𝕜 K n) := by
  refine ⟨chainPairing_injective n, ?_⟩
  have hinj := chainPairing_injective (𝕜 := 𝕜) (K := K) n
  have hker : LinearMap.ker (chainPairing 𝕜 K n) = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hrank : Module.finrank 𝕜 (LinearMap.range (chainPairing 𝕜 K n))
      = Module.finrank 𝕜 (Module.Dual 𝕜 (chains 𝕜 K n)) := by
    have h := LinearMap.finrank_range_add_finrank_ker (chainPairing 𝕜 K n)
    rw [hker] at h
    simp only [finrank_bot, add_zero] at h
    rw [h, Subspace.dual_finrank_eq]
  have htop : LinearMap.range (chainPairing 𝕜 K n) = ⊤ :=
    Submodule.eq_top_of_finrank_eq hrank
  exact LinearMap.range_eq_top.mp htop

/-- The pairing intertwines the coboundary with the dual of the boundary. -/
theorem chainPairing_cochainCoboundary (hK : FaceClosed K) (n : ℕ) :
    (chainPairing 𝕜 K (n + 1)).comp (cochainCoboundary 𝕜 hK n)
      = (chainBoundary 𝕜 hK n).dualMap.comp (chainPairing 𝕜 K n) := by
  classical
  refine LinearMap.ext fun a => ?_
  refine LinearMap.ext fun c => ?_
  simp only [LinearMap.comp_apply, chainPairing_apply, cochainCoboundary_coe,
    LinearMap.dualMap_apply, chainBoundary_coe]
  have hc : ∀ s : Finset V, coboundaryOn 𝕜 K (a : Finset V → 𝕜) s * (c : Finset V → 𝕜) s
      = coboundaryFun 𝕜 V (a : Finset V → 𝕜) s * (c : Finset V → 𝕜) s := by
    intro s
    by_cases hsK : s ∈ K
    · simp [coboundaryOn_apply, hsK]
    · have hcs : (c : Finset V → 𝕜) s = 0 := by
        by_contra hne
        exact hsK (c.2 s hne).1
      simp [hcs]
  rw [Finset.sum_congr rfl fun s _ => hc s]
  exact sum_coboundaryFun_mul _ _

theorem finrank_range_cochainCoboundary (hK : FaceClosed K) (n : ℕ) :
    Module.finrank 𝕜 (LinearMap.range (cochainCoboundary 𝕜 hK n))
      = Module.finrank 𝕜 (LinearMap.range (chainBoundary 𝕜 hK n)) := by
  have hcomp := chainPairing_cochainCoboundary (𝕜 := 𝕜) hK n
  have h1 : LinearMap.range ((chainPairing 𝕜 K (n + 1)).comp (cochainCoboundary 𝕜 hK n))
      = (LinearMap.range (cochainCoboundary 𝕜 hK n)).map (chainPairing 𝕜 K (n + 1)) := by
    rw [LinearMap.range_comp]
  have h2 : LinearMap.range ((chainBoundary 𝕜 hK n).dualMap.comp (chainPairing 𝕜 K n))
      = LinearMap.range (chainBoundary 𝕜 hK n).dualMap := by
    rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr (chainPairing_bijective n).2,
      Submodule.map_top]
  have h3 : Module.finrank 𝕜
      (LinearMap.range ((chainPairing 𝕜 K (n + 1)).comp (cochainCoboundary 𝕜 hK n)))
      = Module.finrank 𝕜
        (LinearMap.range ((chainBoundary 𝕜 hK n).dualMap.comp (chainPairing 𝕜 K n))) := by
    rw [hcomp]
  rw [h1, h2] at h3
  rw [← LinearMap.finrank_range_dualMap_eq_finrank_range (chainBoundary 𝕜 hK n), ← h3]
  exact (Submodule.equivMapOfInjective (chainPairing 𝕜 K (n + 1))
    (chainPairing_injective (n + 1)) (LinearMap.range (cochainCoboundary 𝕜 hK n))).finrank_eq

/-- Exactness of a two-step complex is a dimension identity. -/
theorem exact_iff_finrank_add {A B C : Type*} [AddCommGroup A] [Module 𝕜 A]
    [AddCommGroup B] [Module 𝕜 B] [AddCommGroup C] [Module 𝕜 C] [FiniteDimensional 𝕜 B]
    (f : A →ₗ[𝕜] B) (g : B →ₗ[𝕜] C) (h : LinearMap.range f ≤ LinearMap.ker g) :
    LinearMap.range f = LinearMap.ker g ↔
      Module.finrank 𝕜 (LinearMap.range f) + Module.finrank 𝕜 (LinearMap.range g)
        = Module.finrank 𝕜 B := by
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  constructor
  · intro heq
    rw [heq]
    omega
  · intro hsum
    refine Submodule.eq_of_le_of_finrank_eq h ?_
    omega

theorem range_cochainCoboundary_le_ker (hK : FaceClosed K) (n : ℕ) :
    LinearMap.range (cochainCoboundary 𝕜 hK n) ≤
      LinearMap.ker (cochainCoboundary 𝕜 hK (n + 1)) := by
  rintro a ⟨b, rfl⟩
  refine LinearMap.mem_ker.mpr (Subtype.ext ?_)
  simp only [cochainCoboundary_coe, ZeroMemClass.coe_zero]
  exact coboundaryOn_coboundaryOn hK _

theorem cochain_exact_iff_isCoacyclicAt (hK : FaceClosed K) (n : ℕ) :
    LinearMap.range (cochainCoboundary 𝕜 hK n) =
      LinearMap.ker (cochainCoboundary 𝕜 hK (n + 1)) ↔ IsCoacyclicAt 𝕜 K n := by
  constructor
  · intro heq a ha hzero
    have hmem : (⟨a, ha⟩ : chains 𝕜 K (n + 1)) ∈
        LinearMap.ker (cochainCoboundary 𝕜 hK (n + 1)) :=
      LinearMap.mem_ker.mpr (Subtype.ext (by simpa using hzero))
    rw [← heq] at hmem
    obtain ⟨b, hb⟩ := hmem
    exact ⟨b.1, b.2, congrArg Subtype.val hb⟩
  · intro hco
    refine le_antisymm (range_cochainCoboundary_le_ker hK n) fun a ha => ?_
    obtain ⟨b, hb, hba⟩ := hco a.1 a.2
      (by simpa using congrArg Subtype.val (LinearMap.mem_ker.mp ha))
    exact ⟨⟨b, hb⟩, Subtype.ext hba⟩

/-- **Cochain exactness is chain exactness.**  For a finite face-closed family
over a field, the cochain complex of coefficient functions is exact in a degree
if and only if the reduced chain complex is exact in that degree. -/
theorem isCoacyclicAt_iff_isReducedAcyclicAt (hK : FaceClosed K) (n : ℕ) :
    IsCoacyclicAt 𝕜 K n ↔ IsReducedAcyclicAt 𝕜 K (n + 1) := by
  have hco : IsCoacyclicAt 𝕜 K n ↔
      Module.finrank 𝕜 (LinearMap.range (cochainCoboundary 𝕜 hK n))
        + Module.finrank 𝕜 (LinearMap.range (cochainCoboundary 𝕜 hK (n + 1)))
        = Module.finrank 𝕜 (chains 𝕜 K (n + 1)) := by
    rw [← cochain_exact_iff_isCoacyclicAt hK n]
    exact exact_iff_finrank_add (cochainCoboundary 𝕜 hK n) (cochainCoboundary 𝕜 hK (n + 1))
      (range_cochainCoboundary_le_ker hK n)
  have hch : IsReducedAcyclicAt 𝕜 K (n + 1) ↔
      Module.finrank 𝕜 (LinearMap.range (chainBoundary 𝕜 hK (n + 1)))
        + Module.finrank 𝕜 (LinearMap.range (chainBoundary 𝕜 hK n))
        = Module.finrank 𝕜 (chains 𝕜 K (n + 1)) := by
    rw [← chain_exact_iff_isReducedAcyclicAt hK (n + 1)]
    exact exact_iff_finrank_add (chainBoundary 𝕜 hK (n + 1)) (chainDifferential 𝕜 hK (n + 1))
      (range_chainBoundary_le_ker_chainDifferential hK (n + 1))
  rw [hco, hch, finrank_range_cochainCoboundary hK n,
    finrank_range_cochainCoboundary hK (n + 1)]
  omega


end Bridge

end AffineTverberg.Simplicial
