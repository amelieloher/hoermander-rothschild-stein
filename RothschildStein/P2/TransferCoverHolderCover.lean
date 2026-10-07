-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderTransfer
public import RothschildStein.S.HolderZeroOrder
public import RothschildStein.S.IntrinsicUniqueness

/-!
# Hölder transfer and finite cover: the pairs-at-small-distance argument for Hölder norms

A covering lemma. If finitely many sets `B_i` cover `U`,
every pair of points of `U` at distance `< ℓ` lies in one `B_i`, and `‖g‖_{C^α(B_i)} ≤ M`, then
`‖g‖_{C^α(U)} ≤ M (2 + 2 ℓ^{-α})`: pairs at distance `< ℓ` use the seminorm of the common `B_i`,
pairs at distance `≥ ℓ` have quotient at most `2 ℓ^{-α} M` by the sup norm.
No connectedness and no equal-radius cover is needed, and the ambient control distance is not
changed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

/-- The Hölder norm over `U` from the Hölder norms over a finite cover
`B_i` and a Lebesgue number `ℓ`: `‖g‖_{C^α(U)} ≤ M (2 + 2 ℓ^{-α})`. -/
theorem holderENorm_le_of_cover {n' : ℕ} {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ}
    (hα : 0 < α) {ι : Type*} (t : Finset ι) (B : ι → Set (Fin n' → ℝ))
    {U : Set (Fin n' → ℝ)} {g : (Fin n' → ℝ) → ℝ} {M ℓ : ℝ} (hM : 0 ≤ M) (hℓ : 0 < ℓ)
    (hcover : ∀ x ∈ U, ∃ i ∈ t, x ∈ B i)
    (hleb : ∀ x ∈ U, ∀ y ∈ U, d x y < ENNReal.ofReal ℓ → ∃ i ∈ t, x ∈ B i ∧ y ∈ B i)
    (hsep : ∀ i ∈ t, ∀ x ∈ B i, ∀ y ∈ B i, d x y = 0 → x = y)
    (hB : ∀ i ∈ t, holderENorm d α (B i) g ≤ ENNReal.ofReal M) :
    holderENorm d α U g ≤ ENNReal.ofReal (M * (2 + 2 * (ℓ ^ α)⁻¹)) := by
  have hℓα : 0 < ℓ ^ α := Real.rpow_pos_of_pos hℓ α
  have hinv : 0 ≤ (ℓ ^ α)⁻¹ := inv_nonneg.2 hℓα.le
  have hsup : ∀ x ∈ U, |g x| ≤ M := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := hcover x hx
    have := (RothschildStein.S.enorm_le_holderENorm d α (B i) g hxi).trans (hB i hi)
    exact (ENNReal.ofReal_le_ofReal_iff hM).1 this
  have hsup' : (⨆ x : U, ENNReal.ofReal |g x|) ≤ ENNReal.ofReal M :=
    iSup_le fun x => ENNReal.ofReal_le_ofReal (hsup x.1 x.2)
  have hMc : 0 ≤ M + 2 * M * (ℓ ^ α)⁻¹ := by positivity
  have hsem : holderSeminorm d α U g ≤ ENNReal.ofReal (M + 2 * M * (ℓ ^ α)⁻¹) := by
    refine RothschildStein.S.holderSeminorm_le_of_bound d α U g _ ENNReal.ofReal_lt_top ?_
    intro x hx y hy hxy
    by_cases hnear : d x y < ENNReal.ofReal ℓ
    · obtain ⟨i, hi, hxi, hyi⟩ := hleb x hx y hy hnear
      have h1 := RothschildStein.S.holderSeminorm_increment_le d α (B i) g hα (hsep i hi) hxi hyi hxy
      have h2 : holderSeminorm d α (B i) g ≤ ENNReal.ofReal M :=
        le_trans le_add_self (hB i hi)
      calc ENNReal.ofReal |g x - g y| ≤ holderSeminorm d α (B i) g * d x y ^ α := h1
        _ ≤ ENNReal.ofReal M * d x y ^ α := mul_le_mul' h2 le_rfl
        _ ≤ ENNReal.ofReal (M + 2 * M * (ℓ ^ α)⁻¹) * d x y ^ α :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (by
            have : 0 ≤ 2 * M * (ℓ ^ α)⁻¹ := by positivity
            linarith)) le_rfl
    · have hfar : ENNReal.ofReal ℓ ≤ d x y := not_lt.1 hnear
      have hpow : ENNReal.ofReal (ℓ ^ α) ≤ d x y ^ α := by
        rw [← ENNReal.ofReal_rpow_of_pos hℓ]
        exact ENNReal.rpow_le_rpow hfar hα.le
      have h2M : |g x - g y| ≤ 2 * M := by
        calc |g x - g y| ≤ |g x| + |g y| := abs_sub _ _
          _ ≤ M + M := add_le_add (hsup x hx) (hsup y hy)
          _ = 2 * M := by ring
      calc ENNReal.ofReal |g x - g y| ≤ ENNReal.ofReal (2 * M) := ENNReal.ofReal_le_ofReal h2M
        _ = ENNReal.ofReal (2 * M * (ℓ ^ α)⁻¹) * ENNReal.ofReal (ℓ ^ α) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp
        _ ≤ ENNReal.ofReal (2 * M * (ℓ ^ α)⁻¹) * d x y ^ α := mul_le_mul' le_rfl hpow
        _ ≤ ENNReal.ofReal (M + 2 * M * (ℓ ^ α)⁻¹) * d x y ^ α :=
          mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
  calc holderENorm d α U g = (⨆ x : U, ENNReal.ofReal |g x|) + holderSeminorm d α U g := rfl
    _ ≤ ENNReal.ofReal M + ENNReal.ofReal (M + 2 * M * (ℓ ^ α)⁻¹) := add_le_add hsup' hsem
    _ = ENNReal.ofReal (M + (M + 2 * M * (ℓ ^ α)⁻¹)) := (ENNReal.ofReal_add hM hMc).symm
    _ = ENNReal.ofReal (M * (2 + 2 * (ℓ ^ α)⁻¹)) := by congr 1; ring

/-- A positive lower bound for finitely many positive reals. -/
theorem exists_pos_le_finset {ι : Type*} (t : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ t, 0 < f i) :
    ∃ ℓ : ℝ, 0 < ℓ ∧ ∀ i ∈ t, ℓ ≤ f i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a t ha ih =>
    obtain ⟨ℓ, hℓ, h⟩ := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    refine ⟨min ℓ (f a), lt_min hℓ (hf a (Finset.mem_insert_self a t)), fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h i hi)

section Intrinsic
variable {n' k' : ℕ} {X' : Fin k' → (Fin n' → ℝ) → (Fin n' → ℝ)}
  {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ}

/-- The intrinsic word norm is the Hölder norm of any intrinsic derivative (intrinsic
derivatives are unique). -/
theorem intrinsicWordENorm_eq_holderENorm {V : Opens (Fin n' → ℝ)} {I : List (Fin k')}
    {f g : (Fin n' → ℝ) → ℝ} (hg : hasIntrinsicWordDeriv X' V I f g) :
    intrinsicWordENorm X' d V I α f = holderENorm d α (V : Set (Fin n' → ℝ)) g := by
  unfold intrinsicWordENorm
  refine le_antisymm (sInf_le ⟨g, hg, rfl⟩) (le_sInf ?_)
  rintro r ⟨g', hg', rfl⟩
  have huniq := RothschildStein.S.hasIntrinsicWordDeriv_unique V X' I hg' hg
  exact (RothschildStein.S.holderENorm_congr d α (V : Set (Fin n' → ℝ)) g' huniq).ge

/-- The intrinsic word norm is monotone in the domain. -/
theorem intrinsicWordENorm_mono_domain {V V' : Opens (Fin n' → ℝ)}
    (hV : (V' : Set (Fin n' → ℝ)) ⊆ (V : Set (Fin n' → ℝ))) (I : List (Fin k'))
    (f : (Fin n' → ℝ) → ℝ) :
    intrinsicWordENorm X' d V' I α f ≤ intrinsicWordENorm X' d V I α f := by
  unfold intrinsicWordENorm
  refine le_sInf ?_
  rintro r ⟨g, hg, rfl⟩
  exact sInf_le_of_le ⟨g, hasIntrinsicWordDeriv_mono hV I hg, rfl⟩
    (RothschildStein.S.holderENorm_mono d α (V : Set (Fin n' → ℝ)) g hV)

/-- The weighted Hölder norm is monotone in the domain. -/
theorem holderXENorm_mono_domain (w' : Fin k' → ℕ+) {V V' : Opens (Fin n' → ℝ)}
    (hV : (V' : Set (Fin n' → ℝ)) ⊆ (V : Set (Fin n' → ℝ))) (j : ℕ) (f : (Fin n' → ℝ) → ℝ) :
    holderXENorm w' X' d V' j α f ≤ holderXENorm w' X' d V j α f := by
  unfold holderXENorm
  exact Finset.sum_le_sum fun I _ => intrinsicWordENorm_mono_domain hV I f

/-- A single word is bounded by the weighted norm. -/
theorem intrinsicWordENorm_le_holderXENorm (w' : Fin k' → ℕ+) {V : Opens (Fin n' → ℝ)} {j : ℕ}
    {I : List (Fin k')} (hI : I ∈ wordFamily w' j) (f : (Fin n' → ℝ) → ℝ) :
    intrinsicWordENorm X' d V I α f ≤ holderXENorm w' X' d V j α f := by
  unfold holderXENorm
  exact Finset.single_le_sum (f := fun I => intrinsicWordENorm X' d V I α f)
    (fun _ _ => zero_le) hI

/-- Membership in the weighted Hölder space restricts to smaller open sets. -/
theorem memHolderX_mono_domain (w' : Fin k' → ℕ+) {V V' : Opens (Fin n' → ℝ)}
    (hV : (V' : Set (Fin n' → ℝ)) ⊆ (V : Set (Fin n' → ℝ))) {j : ℕ} {f : (Fin n' → ℝ) → ℝ}
    (h : memHolderX w' X' d V j α f) : memHolderX w' X' d V' j α f := by
  refine ⟨lt_of_le_of_lt (RothschildStein.S.holderENorm_mono d α (V : Set (Fin n' → ℝ)) f hV) h.1,
    fun I hI => ?_⟩
  obtain ⟨g, hg, hgf⟩ := h.2 I hI
  exact ⟨g, hasIntrinsicWordDeriv_mono hV I hg,
    lt_of_le_of_lt (RothschildStein.S.holderENorm_mono d α (V : Set (Fin n' → ℝ)) g hV) hgf⟩

end Intrinsic

end RothschildStein.P2
