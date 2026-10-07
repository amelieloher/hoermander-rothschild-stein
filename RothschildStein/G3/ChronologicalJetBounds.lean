-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ChronologicalCompositionJets
public import RothschildStein.G3.PositiveCompositionAt
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Bounds are recorded at each actual successive input point. -/
def ChronologicalJetBounds (q : ℕ) (B : ℝ) : List (E → E) → E → Prop
  | [], _ => True
  | f :: fs, x => ContDiffAt ℝ q f x ∧
      (∀ j, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℝ j f x‖ ≤ B) ∧
      ChronologicalJetBounds q B fs (f x)

def chronologicalJetBudget (q : ℕ) (B : ℝ) : ℕ → ℝ
  | 0 => 1
  | l + 1 => max 1 (q.factorial * chronologicalJetBudget q B l * B ^ q)

theorem chronologicalJetBudget_one_le (q : ℕ) (B : ℝ) (l : ℕ) :
    1 ≤ chronologicalJetBudget q B l := by
  cases l with
  | zero => exact le_rfl
  | succ l => exact le_max_left _ _

theorem chronologicalComposition_contDiffAt_of_bounds (q : ℕ) (B : ℝ)
    (fs : List (E → E)) (x : E) (h : ChronologicalJetBounds q B fs x) :
    ContDiffAt ℝ q (chronologicalComposition fs) x := by
  induction fs generalizing x with
  | nil => exact contDiffAt_id
  | cons f fs ih => exact (ih (f x) h.2.2).comp x h.1

/-- The jet order stays fixed as the list grows; only the numerical budget grows. -/
theorem norm_chronologicalComposition_jet_le (q : ℕ) {B : ℝ} (hB : 1 ≤ B)
    (fs : List (E → E)) (x : E) (h : ChronologicalJetBounds q B fs x)
    (j : ℕ) (hj : 1 ≤ j) (hjq : j ≤ q) :
    ‖iteratedFDeriv ℝ j (chronologicalComposition fs) x‖ ≤
      chronologicalJetBudget q B fs.length := by
  induction fs generalizing x j with
  | nil =>
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hj
    change ‖iteratedFDeriv ℝ (1 + k) id x‖ ≤ 1
    rw [Nat.add_comm 1 k]
    exact G1.norm_iteratedFDeriv_id_le k x
  | cons f fs ih =>
    have hM : 0 ≤ chronologicalJetBudget q B fs.length :=
      le_trans zero_le_one (chronologicalJetBudget_one_le q B fs.length)
    have ht := chronologicalComposition_contDiffAt_of_bounds q B fs (f x) h.2.2
    have he := norm_positive_composition_jet_at_le hj
      (ht.of_le (by exact_mod_cast hjq)) (h.1.of_le (by exact_mod_cast hjq)) hM hB
      (fun k hk hk' => ih (f x) h.2.2 k hk (hk'.trans hjq))
      (fun k hk hk' => h.2.1 k hk (hk'.trans hjq))
    apply he.trans
    change (j.factorial : ℝ) * chronologicalJetBudget q B fs.length * B ^ j ≤
      max 1 ((q.factorial : ℝ) * chronologicalJetBudget q B fs.length * B ^ q)
    apply le_trans _ (le_max_right _ _)
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.factorial_le hjq) hM
    · exact pow_le_pow_right₀ hB hjq
    · exact pow_nonneg (le_trans zero_le_one hB) _
    · positivity
end RothschildStein.G3
