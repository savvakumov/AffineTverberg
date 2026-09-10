import AffineTverberg.SimplicialCohomology

set_option linter.style.header false

/-!
# Complementation of oriented simplicial chains

This file sets up the algebraic engine of combinatorial Alexander duality for
the oriented augmented chain complex of `AffineTverberg.Simplicial`.

For a finite linearly ordered vertex type `V` with `q = |V|` vertices, taking
complements of simplices, with the sign

`compSign t = (-1) ^ (∑ v ∈ t, #{u : u < v})`,

is a linear automorphism `dualize` of the space of coefficient functions
`Finset V → 𝕜` which **interchanges the oriented boundary with the oriented
coboundary**:

`cochainDelta (dualize c) = dualize (boundary c)`

(`cochainDelta_dualize`), with no leftover sign.  Under it the chains of the
Alexander dual family

`alexanderDual K = {s | sᶜ ∉ K}`

in cardinality-degree `c` correspond exactly to the *relative cochains*
`relCochains K d` — the coefficient functions supported on the non-faces of `K`
of cardinality `d` — for `c + d = q`.

Nothing here assumes anything about `K` beyond face-closedness where stated,
and every sign is computed from the actual incidence signs of
`AffineTverberg/SimplicialHomology.lean`.
-/

noncomputable section

open scoped BigOperators

namespace AffineTverberg
namespace Simplicial

section Dualize

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder V] [Fintype V]

/-- The number of vertices strictly below `v`. -/
def rankBelow (v : V) : ℕ := (Finset.univ.filter (fun u ↦ u < v)).card

/-- The sign attached to a simplex by the complementation involution. -/
def compSign (𝕜 : Type*) [Field 𝕜] (t : Finset V) : 𝕜 :=
  (-1) ^ (∑ v ∈ t, rankBelow v)

theorem compSign_ne_zero (t : Finset V) : compSign 𝕜 t ≠ 0 :=
  pow_ne_zero _ (by norm_num)

theorem compSign_erase {t : Finset V} {v : V} (hv : v ∈ t) :
    compSign 𝕜 t = (-1) ^ rankBelow v * compSign 𝕜 (t.erase v) := by
  unfold compSign
  rw [← pow_add, ← Finset.sum_erase_add t _ hv, Nat.add_comm]

theorem compSign_mul_compl (t : Finset V) :
    compSign 𝕜 t * compSign 𝕜 tᶜ = compSign 𝕜 (Finset.univ : Finset V) := by
  unfold compSign
  rw [← pow_add, Finset.sum_add_sum_compl]

theorem compSign_univ_sq :
    compSign 𝕜 (Finset.univ : Finset V) * compSign 𝕜 (Finset.univ : Finset V) = 1 := by
  unfold compSign
  rw [← pow_add, ← two_mul, pow_mul]
  norm_num

/-- Complementation of coefficient functions, with the orientation sign. -/
def dualize (𝕜 V : Type*) [Field 𝕜] [LinearOrder V] [Fintype V] :
    (Finset V → 𝕜) →ₗ[𝕜] (Finset V → 𝕜) where
  toFun c := fun t ↦ compSign 𝕜 t * c tᶜ
  map_add' c d := by funext t; simp [mul_add]
  map_smul' a c := by funext t; simp [mul_left_comm]

@[simp]
theorem dualize_apply (c : Finset V → 𝕜) (t : Finset V) :
    dualize 𝕜 V c t = compSign 𝕜 t * c tᶜ := rfl

theorem dualize_dualize (c : Finset V → 𝕜) :
    dualize 𝕜 V (dualize 𝕜 V c) = compSign 𝕜 (Finset.univ : Finset V) • c := by
  funext t
  simp only [dualize_apply, compl_compl, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, compSign_mul_compl]

theorem dualize_injective : Function.Injective (dualize 𝕜 V) := by
  intro c d h
  have h2 : compSign 𝕜 (Finset.univ : Finset V) • c
      = compSign 𝕜 (Finset.univ : Finset V) • d := by
    rw [← dualize_dualize, ← dualize_dualize, h]
  exact smul_right_injective _ (compSign_ne_zero _) h2

/-- The inverse of `dualize`, again complementation up to the global sign. -/
theorem dualize_leftInverse (c : Finset V → 𝕜) :
    dualize 𝕜 V (compSign 𝕜 (Finset.univ : Finset V) • dualize 𝕜 V c) = c := by
  rw [map_smul, dualize_dualize, smul_smul, compSign_univ_sq, one_smul]

theorem dualize_surjective : Function.Surjective (dualize 𝕜 V) :=
  fun c ↦ ⟨compSign 𝕜 (Finset.univ : Finset V) • dualize 𝕜 V c, dualize_leftInverse c⟩

/-! ### The oriented coboundary -/

/-- The oriented simplicial coboundary: the transpose of `boundary`. -/
def cochainDelta (𝕜 V : Type*) [Field 𝕜] [LinearOrder V] [Fintype V] :
    (Finset V → 𝕜) →ₗ[𝕜] (Finset V → 𝕜) where
  toFun c := fun t ↦ ∑ v ∈ t, orientedSign 𝕜 (t.erase v) v * c (t.erase v)
  map_add' c d := by
    funext t
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' a c := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ ↦ by ring

theorem cochainDelta_apply (c : Finset V → 𝕜) (t : Finset V) :
    cochainDelta 𝕜 V c t = ∑ v ∈ t, orientedSign 𝕜 (t.erase v) v * c (t.erase v) := rfl

/-- The number of vertices below `v` splits along a simplex and its complement. -/
theorem rankBelow_eq_add (t : Finset V) (v : V) :
    rankBelow v = ((t.erase v).filter (fun u ↦ u < v)).card
      + (tᶜ.filter (fun u ↦ u < v)).card := by
  classical
  unfold rankBelow
  have hsplit :
      ((Finset.univ.filter (fun u ↦ u < v)).filter (fun u ↦ u ∈ t)).card
        + ((Finset.univ.filter (fun u ↦ u < v)).filter (fun u ↦ ¬ u ∈ t)).card
        = (Finset.univ.filter (fun u ↦ u < v)).card :=
    Finset.card_filter_add_card_filter_not _
  have h1 : (Finset.univ.filter (fun u ↦ u < v)).filter (fun u ↦ u ∈ t)
      = (t.erase v).filter (fun u ↦ u < v) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨hlt, hut⟩
      exact ⟨⟨ne_of_lt hlt, hut⟩, hlt⟩
    · rintro ⟨⟨_, hut⟩, hlt⟩
      exact ⟨hlt, hut⟩
  have h2 : (Finset.univ.filter (fun u ↦ u < v)).filter (fun u ↦ ¬ u ∈ t)
      = tᶜ.filter (fun u ↦ u < v) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    exact ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩
  rw [h1, h2] at hsplit
  omega

/-- The sign identity making complementation exchange boundary and coboundary. -/
theorem orientedSign_compSign_erase {t : Finset V} {v : V} (hv : v ∈ t) :
    orientedSign 𝕜 (t.erase v) v * compSign 𝕜 (t.erase v)
      = compSign 𝕜 t * orientedSign 𝕜 tᶜ v := by
  have hsplit : ((-1 : 𝕜)) ^ rankBelow v
      = orientedSign 𝕜 (t.erase v) v * orientedSign 𝕜 tᶜ v := by
    unfold orientedSign
    rw [← pow_add, rankBelow_eq_add t v]
  rw [compSign_erase hv, hsplit]
  have hsq := orientedSign_sq (𝕜 := 𝕜) tᶜ v
  calc orientedSign 𝕜 (t.erase v) v * compSign 𝕜 (t.erase v)
      = orientedSign 𝕜 (t.erase v) v * compSign 𝕜 (t.erase v) *
          (orientedSign 𝕜 tᶜ v * orientedSign 𝕜 tᶜ v) := by rw [hsq, mul_one]
    _ = orientedSign 𝕜 (t.erase v) v * orientedSign 𝕜 tᶜ v * compSign 𝕜 (t.erase v) *
          orientedSign 𝕜 tᶜ v := by ring

/-- **Complementation exchanges the oriented boundary and coboundary.** -/
theorem cochainDelta_dualize (c : Finset V → 𝕜) :
    cochainDelta 𝕜 V (dualize 𝕜 V c) = dualize 𝕜 V (boundary 𝕜 V c) := by
  funext t
  rw [cochainDelta_apply, dualize_apply, boundary_apply, compl_compl, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv ↦ ?_
  rw [dualize_apply, Finset.compl_erase]
  have := orientedSign_compSign_erase (𝕜 := 𝕜) hv
  calc orientedSign 𝕜 (t.erase v) v * (compSign 𝕜 (t.erase v) * c (insert v tᶜ))
      = (orientedSign 𝕜 (t.erase v) v * compSign 𝕜 (t.erase v)) * c (insert v tᶜ) := by ring
    _ = (compSign 𝕜 t * orientedSign 𝕜 tᶜ v) * c (insert v tᶜ) := by rw [this]
    _ = compSign 𝕜 t * (orientedSign 𝕜 tᶜ v * c (insert v tᶜ)) := by ring

/-- The coboundary squares to zero, from `∂ ∘ ∂ = 0`. -/
theorem cochainDelta_cochainDelta (c : Finset V → 𝕜) :
    cochainDelta 𝕜 V (cochainDelta 𝕜 V c) = 0 := by
  obtain ⟨b, rfl⟩ := dualize_surjective (𝕜 := 𝕜) (V := V) c
  rw [cochainDelta_dualize, cochainDelta_dualize, boundary_boundary_apply, map_zero]

end Dualize

section AlexanderDual

variable {𝕜 V : Type*} [Field 𝕜] [LinearOrder V] [Fintype V]

/-- The Alexander dual family: the simplices whose complement is **not** a face. -/
def alexanderDual (K : Finset (Finset V)) : Finset (Finset V) :=
  (Finset.univ : Finset (Finset V)).filter (fun s ↦ sᶜ ∉ K)

@[simp]
theorem mem_alexanderDual {K : Finset (Finset V)} {s : Finset V} :
    s ∈ alexanderDual K ↔ sᶜ ∉ K := by
  simp [alexanderDual]

theorem faceClosed_alexanderDual {K : Finset (Finset V)} (hK : FaceClosed K) :
    FaceClosed (alexanderDual K) := by
  intro s hs t hts
  rw [mem_alexanderDual] at hs ⊢
  intro htK
  exact hs (hK _ htK _ (Finset.compl_subset_compl.mpr hts))

theorem alexanderDual_alexanderDual (K : Finset (Finset V)) :
    alexanderDual (alexanderDual K) = K := by
  ext s
  simp

/-- Relative cochains: coefficient functions supported on the non-faces of `K`
of cardinality `d`.  This is the kernel of restriction to `K`. -/
def relCochains (𝕜 : Type*) [Field 𝕜] (K : Finset (Finset V)) (d : ℕ) :
    Submodule 𝕜 (Finset V → 𝕜) where
  carrier := {f | ∀ t, f t ≠ 0 → t ∉ K ∧ t.card = d}
  add_mem' := by
    intro c d hc hd s hs
    by_cases h : c s = 0
    · exact hd s (by simpa [h] using hs)
    · exact hc s h
  zero_mem' := by intro s hs; simp at hs
  smul_mem' := by
    intro a c hc s hs
    exact hc s (by
      intro h
      exact hs (by simp [Pi.smul_apply, h]))

omit [LinearOrder V] [Fintype V] in
theorem mem_relCochains_iff {K : Finset (Finset V)} {d : ℕ} {f : Finset V → 𝕜} :
    f ∈ relCochains 𝕜 K d ↔ ∀ t, f t ≠ 0 → t ∉ K ∧ t.card = d := Iff.rfl

theorem card_compl_eq {V : Type*} [Fintype V] [DecidableEq V] (t : Finset V) :
    tᶜ.card = Fintype.card V - t.card := by
  rw [Finset.card_compl]

/-- `dualize` sends the chains of the Alexander dual to relative cochains. -/
theorem dualize_mem_relCochains {K : Finset (Finset V)} {c d : ℕ}
    (hcd : c + d = Fintype.card V) {f : Finset V → 𝕜}
    (hf : f ∈ chains 𝕜 (alexanderDual K) c) :
    dualize 𝕜 V f ∈ relCochains 𝕜 K d := by
  intro t ht
  have hne : f tᶜ ≠ 0 := by
    intro h
    rw [dualize_apply, h, mul_zero] at ht
    exact ht rfl
  obtain ⟨hmem, hcard⟩ := hf _ hne
  rw [mem_alexanderDual, compl_compl] at hmem
  refine ⟨hmem, ?_⟩
  have hcc : tᶜ.card = Fintype.card V - t.card := card_compl_eq t
  have hle : t.card ≤ Fintype.card V := Finset.card_le_univ t
  omega

/-- `dualize` sends relative cochains to the chains of the Alexander dual. -/
theorem dualize_mem_chains_alexanderDual {K : Finset (Finset V)} {c d : ℕ}
    (hcd : c + d = Fintype.card V) {f : Finset V → 𝕜}
    (hf : f ∈ relCochains 𝕜 K d) :
    dualize 𝕜 V f ∈ chains 𝕜 (alexanderDual K) c := by
  intro s hs
  have hne : f sᶜ ≠ 0 := by
    intro h
    rw [dualize_apply, h, mul_zero] at hs
    exact hs rfl
  obtain ⟨hmem, hcard⟩ := hf _ hne
  refine ⟨mem_alexanderDual.mpr hmem, ?_⟩
  have hcc : sᶜ.card = Fintype.card V - s.card := card_compl_eq s
  have hle : s.card ≤ Fintype.card V := Finset.card_le_univ s
  omega

end AlexanderDual

end Simplicial
end AffineTverberg
