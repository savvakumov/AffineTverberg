import AffineTverberg.ConvexFiber
import AffineTverberg.SingularAcyclicFiber

set_option linter.style.header false

/-!
# Local neighborhoods for finite conical incidence families

The sphere-parameter sets in the paper are closed convex cones. Strict
separation provides open convex conical neighborhoods which meet only the
pieces containing the chosen center. These neighborhoods admit normalized
straight-line contractions, without any polyhedral presentation assumption.
-/

noncomputable section

open Set unitInterval

namespace AffineTverberg

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Strict separation of a point from a closed convex cone, with the
orientation positive at the point and nonpositive on the whole cone. -/
theorem exists_positive_separator_of_closed_convex_cone
    {C : Set E} (hcl : IsClosed C) (hcv : Convex ℝ C) (h0 : (0 : E) ∈ C)
    (hsmul : ∀ t : ℝ, 0 ≤ t → ∀ x ∈ C, t • x ∈ C)
    {a : E} (ha : a ∉ C) :
    ∃ l : E →L[ℝ] ℝ, 0 < l a ∧ ∀ x ∈ C, l x ≤ 0 := by
  obtain ⟨f, b, hfa, hfC⟩ := geometric_hahn_banach_point_closed hcv hcl ha
  have hb : b < 0 := by simpa using hfC 0 h0
  have hf : ∀ x ∈ C, 0 ≤ f x := by
    intro x hx
    by_contra h
    have hfx : f x < 0 := lt_of_not_ge h
    let t : ℝ := (b - 1) / f x
    have ht : 0 < t := div_pos_of_neg_of_neg (by linarith) hfx
    have hv := hfC (t • x) (hsmul t ht.le x hx)
    have heq : f (t • x) = b - 1 := by
      simp only [map_smul, smul_eq_mul, t]
      exact div_mul_cancel₀ _ hfx.ne
    rw [heq] at hv
    linarith
  refine ⟨-f, ?_, ?_⟩
  · simp only [neg_apply]
    linarith
  · intro x hx
    simpa only [neg_apply, neg_nonpos] using hf x hx

/-- Near a nonzero center, only cones containing that center can occur.
The neighborhood can be chosen open, convex, positively scale-invariant,
and disjoint from zero, so normalization preserves its contractions. -/
theorem exists_open_conical_active_neighborhood
    {ι : Type*} [Finite ι] (C : ι → Set E)
    (hcl : ∀ i, IsClosed (C i)) (hcv : ∀ i, Convex ℝ (C i))
    (h0 : ∀ i, (0 : E) ∈ C i)
    (hsmul : ∀ i (t : ℝ), 0 ≤ t → ∀ x ∈ C i, t • x ∈ C i)
    {a : E} (ha : a ≠ 0) :
    ∃ U : Set E, IsOpen U ∧ a ∈ U ∧ Convex ℝ U ∧
      (∀ t : ℝ, 0 < t → ∀ x ∈ U, t • x ∈ U) ∧ (0 : E) ∉ U ∧
      ∀ x ∈ U, ∀ i, x ∈ C i → a ∈ C i := by
  classical
  obtain ⟨l0, _, hl0⟩ := exists_strictlyPositive_unitDual
    (convex_singleton a) isClosed_singleton (singleton_nonempty a)
    (show (0 : E) ∉ ({a} : Set E) by simpa using ha.symm)
  have hla : 0 < l0 a := hl0 a rfl
  have hsep : ∀ i, a ∉ C i → ∃ l : E →L[ℝ] ℝ,
      0 < l a ∧ ∀ x ∈ C i, l x ≤ 0 :=
    fun i hi ↦ exists_positive_separator_of_closed_convex_cone
      (hcl i) (hcv i) (h0 i) (hsmul i) hi
  let l : ι → E →L[ℝ] ℝ := fun i ↦
    if hi : a ∈ C i then l0 else Classical.choose (hsep i hi)
  have hl : ∀ i, 0 < l i a := by
    intro i
    dsimp [l]
    split_ifs with hi
    · exact hla
    · exact (Classical.choose_spec (hsep i hi)).1
  have hlC : ∀ i, a ∉ C i → ∀ x ∈ C i, l i x ≤ 0 := by
    intro i hi x hx
    simpa [l, hi] using (Classical.choose_spec (hsep i hi)).2 x hx
  let U : Set E := {x | 0 < l0 x ∧ ∀ i, 0 < l i x}
  refine ⟨U, ?_, ⟨hla, hl⟩, ?_, ?_, ?_, ?_⟩
  · have heq : U = {x | 0 < l0 x} ∩ ⋂ i, {x | 0 < l i x} := by
      ext x
      simp [U]
    rw [heq]
    exact (isOpen_lt continuous_const l0.continuous).inter
      (isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (l i).continuous)
  · rintro x hx y hy u v hu hv huv
    have hpos (g : E →L[ℝ] ℝ) (hxg : 0 < g x) (hyg : 0 < g y) :
        0 < g (u • x + v • y) := by
      simp only [map_add, map_smul, smul_eq_mul]
      rcases lt_or_eq_of_le hu with hu | rfl
      · exact add_pos_of_pos_of_nonneg (mul_pos hu hxg) (mul_nonneg hv hyg.le)
      · simp only [zero_add] at huv
        simpa [huv] using hyg
    exact ⟨hpos l0 hx.1 hy.1, fun i ↦ hpos (l i) (hx.2 i) (hy.2 i)⟩
  · intro t ht x hx
    constructor
    · simpa only [map_smul, smul_eq_mul] using mul_pos ht hx.1
    · intro i
      simpa only [map_smul, smul_eq_mul] using mul_pos ht (hx.2 i)
  · intro h
    exact (lt_irrefl 0) (by simpa using h.1)
  · intro x hx i hxi
    by_contra hai
    exact not_lt_of_ge (hlC i hai x hxi) (hx.2 i)

namespace ConicalIncidence

abbrev UnitSphere (E : Type*) [NormedAddCommGroup E] := {y : E // ‖y‖ = 1}

/-- A geometric neighborhood on which every active piece contains the center. -/
structure Neighborhood {ι : Type*} (C : ι → Set E) (a : UnitSphere E) where
  carrier : Set E
  isOpen : IsOpen carrier
  center_mem : a.val ∈ carrier
  convex : Convex ℝ carrier
  smul_mem : ∀ t : ℝ, 0 < t → ∀ x ∈ carrier, t • x ∈ carrier
  zero_notMem : (0 : E) ∉ carrier
  active : ∀ x ∈ carrier, ∀ i, x ∈ C i → a.val ∈ C i

/-- Such neighborhoods exist for the actual finite closed convex cone data. -/
theorem exists_neighborhood {ι : Type*} [Finite ι] (C : ι → Set E)
    (hcl : ∀ i, IsClosed (C i)) (hcv : ∀ i, Convex ℝ (C i))
    (h0 : ∀ i, (0 : E) ∈ C i)
    (hsmul : ∀ i (t : ℝ), 0 ≤ t → ∀ x ∈ C i, t • x ∈ C i)
    (a : UnitSphere E) : Nonempty (Neighborhood C a) := by
  have ha : a.val ≠ 0 := by
    intro h
    have := a.property
    simp [h] at this
  obtain ⟨U, ho, haU, hcvU, hsmulU, h0U, hactive⟩ :=
    exists_open_conical_active_neighborhood C hcl hcv h0 hsmul ha
  exact ⟨⟨U, ho, haU, hcvU, hsmulU, h0U, hactive⟩⟩

namespace Neighborhood

variable {ι : Type*} {C : ι → Set E} {a : UnitSphere E} (H : Neighborhood C a)

def cap : Set (UnitSphere E) := {y | y.val ∈ H.carrier}

theorem isOpen_cap : IsOpen H.cap := H.isOpen.preimage continuous_subtype_val

theorem center_mem_cap : a ∈ H.cap := H.center_mem

theorem normalize_mem {y : E} (hy : y ∈ H.carrier) :
    NormedSpace.normalize y ∈ H.carrier := by
  have hy0 : y ≠ 0 := fun h ↦ H.zero_notMem (h ▸ hy)
  exact H.smul_mem _ (inv_pos.mpr (norm_pos_iff.mpr hy0)) _ hy

def segment (_H : Neighborhood C a) (t : I) (y : E) : E :=
  (1 - (t : ℝ)) • y + (t : ℝ) • a.val

theorem segment_mem (t : I) {y : E} (hy : y ∈ H.carrier) :
    H.segment t y ∈ H.carrier :=
  H.convex hy H.center_mem (sub_nonneg.mpr t.property.2) t.property.1 (by ring)

theorem segment_ne_zero (t : I) {y : E} (hy : y ∈ H.carrier) :
    H.segment t y ≠ 0 := fun h ↦ H.zero_notMem (h ▸ H.segment_mem t hy)

def capContraction (p : I × H.cap) : H.cap :=
  ⟨⟨NormedSpace.normalize (H.segment p.1 p.2.val.val),
    NormedSpace.norm_normalize (H.segment_ne_zero p.1 p.2.property)⟩,
    H.normalize_mem (H.segment_mem p.1 p.2.property)⟩

/-- The parameter neighborhood itself is contractible. -/
theorem contractibleSpace_cap : ContractibleSpace H.cap := by
  refine (contractible_iff_id_nullhomotopic H.cap).mpr
    ⟨⟨a, H.center_mem⟩, ⟨?H⟩⟩
  refine
    { toFun := H.capContraction
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · have hs : Continuous (fun p : I × H.cap ↦ H.segment p.1 p.2.val.val) := by
      unfold segment
      fun_prop
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (hs.norm.inv₀ fun p ↦ norm_ne_zero_iff.mpr
      (H.segment_ne_zero p.1 p.2.property)).smul hs
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    simp [capContraction, segment, NormedSpace.normalize_eq_self_of_norm_eq_one y.val.property]
  · intro y
    apply Subtype.ext
    apply Subtype.ext
    simp [capContraction, segment, NormedSpace.normalize_eq_self_of_norm_eq_one a.property]

end Neighborhood

section Space

variable {X : Type*} [TopologicalSpace X] {ι : Type*}
  (A : ι → Set X) (C : ι → Set E)

/-- The finite conical incidence model with unit parameters. -/
abbrev Space := {z : X × UnitSphere E // ∃ i, z.1 ∈ A i ∧ z.2.val ∈ C i}

def projection : C(Space A C, UnitSphere E) := ⟨fun z ↦ z.val.2, by fun_prop⟩

def centerFiber (a : UnitSphere E) : Set X := {x | ∃ i, x ∈ A i ∧ a.val ∈ C i}

/-- The literal projection fiber has no additional geometric premises. -/
def fiberHomeomorph (a : UnitSphere E) :
    ↥((projection A C) ⁻¹' {a}) ≃ₜ centerFiber A C a where
  toFun z := ⟨z.val.val.1, by
    obtain ⟨i, hi, hy⟩ := z.val.property
    refine ⟨i, hi, ?_⟩
    have heq : z.val.val.2 = a := z.property
    simpa [heq] using hy⟩
  invFun x := ⟨⟨(x.val, a), x.property⟩, rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (show a = z.val.val.2 from z.property.symm)
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

variable {a : UnitSphere E} (H : Neighborhood C a)

def localRetract :
    C(↥((projection A C) ⁻¹' H.cap), centerFiber A C a) :=
  ⟨fun z ↦ ⟨z.val.val.1, by
    obtain ⟨i, hx, hy⟩ := z.val.property
    exact ⟨i, hx, H.active _ z.property i hy⟩⟩, by fun_prop⟩

def localSection :
    C(centerFiber A C a, ↥((projection A C) ⁻¹' H.cap)) :=
  ⟨fun x ↦ ⟨⟨(x.val, a), x.property⟩, H.center_mem⟩, by fun_prop⟩

theorem localRetract_comp_section :
    (localRetract A C H).comp (localSection A C H) = ContinuousMap.id _ := rfl

variable (hcv : ∀ i, Convex ℝ (C i))
  (hsmul : ∀ i (t : ℝ), 0 ≤ t → ∀ x ∈ C i, t • x ∈ C i)

/-- Normalized interpolation retains the same incidence piece and stays in
the full preimage of the chosen parameter neighborhood. -/
def localContraction (p : I × ↥((projection A C) ⁻¹' H.cap)) :
    ↥((projection A C) ⁻¹' H.cap) :=
  ⟨⟨(p.2.val.val.1,
    ⟨NormedSpace.normalize (H.segment p.1 p.2.val.val.2.val),
      NormedSpace.norm_normalize (H.segment_ne_zero p.1 p.2.property)⟩), by
      obtain ⟨i, hx, hy⟩ := p.2.val.property
      refine ⟨i, hx, hsmul i _ (inv_nonneg.mpr (norm_nonneg _)) _ ?_⟩
      exact hcv i hy (H.active _ p.2.property i hy)
        (sub_nonneg.mpr p.1.property.2) p.1.property.1 (by ring)⟩,
    H.normalize_mem (H.segment_mem p.1 p.2.property)⟩

def localHomotopy :
    ContinuousMap.Homotopy (ContinuousMap.id ↥((projection A C) ⁻¹' H.cap))
      ((localSection A C H).comp (localRetract A C H)) where
  toFun := localContraction A C H hcv hsmul
  continuous_toFun := by
    have hs : Continuous (fun p : I × ↥((projection A C) ⁻¹' H.cap) ↦
        H.segment p.1 p.2.val.val.2.val) := by
      unfold Neighborhood.segment
      fun_prop
    have hn : Continuous (fun p : I × ↥((projection A C) ⁻¹' H.cap) ↦
        NormedSpace.normalize (H.segment p.1 p.2.val.val.2.val)) :=
      (hs.norm.inv₀ fun p ↦ norm_ne_zero_iff.mpr
        (H.segment_ne_zero p.1 p.2.property)).smul hs
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk
    · fun_prop
    · exact hn.subtype_mk _
  map_zero_left z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [localContraction, Neighborhood.segment,
        NormedSpace.normalize_eq_self_of_norm_eq_one z.val.val.2.property]
  map_one_left z := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      simp [localContraction, Neighborhood.segment, localSection, localRetract,
        NormedSpace.normalize_eq_self_of_norm_eq_one a.property]

/-- An explicit local homotopy equivalence obtained by keeping the geometric
coordinate fixed and contracting only the sphere parameter. -/
def localHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↥((projection A C) ⁻¹' H.cap) (centerFiber A C a) where
  toFun := localRetract A C H
  invFun := localSection A C H
  left_inv := ⟨(localHomotopy A C H hcv hsmul).symm⟩
  right_inv := by rw [localRetract_comp_section]

/-- The whole neighborhood preimage is homotopy equivalent to the literal
projection fiber over its center. -/
def localFiberHomotopyEquiv :
    ContinuousMap.HomotopyEquiv ↥((projection A C) ⁻¹' H.cap)
      ↥((projection A C) ⁻¹' {a}) :=
  (localHomotopyEquiv A C H hcv hsmul).trans (fiberHomeomorph A C a).symm.toHomotopyEquiv

end Space

section LocalHomology

open CategoryTheory HomologicalComplex AffChain

variable {X E ι : Type} [TopologicalSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [Finite ι]

/-- Every sphere parameter has a genuine open contractible neighborhood
whose full incidence preimage retracts to the actual center fiber. -/
theorem exists_open_fiberHomotopyEquiv
    (A : ι → Set X) (C : ι → Set E)
    (hcl : ∀ i, IsClosed (C i)) (hcv : ∀ i, Convex ℝ (C i))
    (h0 : ∀ i, (0 : E) ∈ C i)
    (hsmul : ∀ i (t : ℝ), 0 ≤ t → ∀ x ∈ C i, t • x ∈ C i)
    (a : UnitSphere E) :
    ∃ U : Set (UnitSphere E), IsOpen U ∧ a ∈ U ∧ ContractibleSpace U ∧
      Nonempty (ContinuousMap.HomotopyEquiv ↥((projection A C) ⁻¹' U)
        ↥((projection A C) ⁻¹' {a})) := by
  obtain ⟨H⟩ := exists_neighborhood C hcl hcv h0 hsmul a
  exact ⟨H.cap, H.isOpen_cap, H.center_mem_cap, H.contractibleSpace_cap,
    ⟨localFiberHomotopyEquiv A C H hcv hsmul⟩⟩

/-- Fiber acyclicity yields the sharp homology range on an actual open
neighborhood. This is a local conclusion, not yet global descent. -/
theorem exists_open_homologyRange
    (A : ι → Set X) (C : ι → Set E)
    (hcl : ∀ i, IsClosed (C i)) (hcv : ∀ i, Convex ℝ (C i))
    (h0 : ∀ i, (0 : E) ∈ C i)
    (hsmul : ∀ i (t : ℝ), 0 ≤ t → ∀ x ∈ C i, t • x ∈ C i)
    {q : ℕ} (a : UnitSphere E)
    (hfib : SingularAcyclicBelow (TopCat.of ↥((projection A C) ⁻¹' {a})) q) :
    ∃ U : Set (UnitSphere E), IsOpen U ∧ a ∈ U ∧
      HomologyRange (singChainsMap (preimageRestriction
        (TopCat.ofHom (projection A C)) U)) q := by
  obtain ⟨U, ho, ha, hU, ⟨e⟩⟩ := exists_open_fiberHomotopyEquiv A C hcl hcv h0 hsmul a
  exact ⟨U, ho, ha, homologyRange_of_acyclic_contractible _ (hfib.of_homotopyEquiv e)⟩

end LocalHomology

end ConicalIncidence

end AffineTverberg
