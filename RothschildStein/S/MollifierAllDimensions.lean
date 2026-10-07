-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.MollifierLocallyIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter
open scoped Topology ENNReal
namespace RothschildStein.S
variable {n : ℕ}

/-- In zero coordinate dimension ordinary mollification is exactly
the identity (BB Lemma 2.8, p. 72; degenerate carrier). -/
theorem euclideanRegularize_zero_dimension (f : (Fin 0 → ℝ) → ℝ) (ε : ℝ) :
    euclideanRegularize 0 f ε = f := by
  funext x
  unfold euclideanRegularize euclideanJScale
  have hy (z : Fin 0 → ℝ) : ε⁻¹ • (x-z) = z := Subsingleton.elim _ _
  have hf (z : Fin 0 → ℝ) : f z = f x := congrArg f (Subsingleton.elim _ _)
  simp only [pow_zero,inv_one,one_mul,hy,hf,integral_mul_const,
    (euclideanJ_normalized 0).2,one_mul]

/-- Finite-p convergence holds without excluding coordinate
dimension zero (BB Lemma 2.8, p. 72). -/
theorem tendsto_euclideanRegularize_eLpNorm_all_dimensions (p : ℝ≥0∞)
    (hp : 1 ≤ p) (ht : p ≠ ⊤) {f : (Fin n → ℝ) → ℝ} (hf : MemLp f p volume) :
    Tendsto (fun ε : ℝ => eLpNorm (euclideanRegularize n f ε-f) p volume)
      (𝓝[>] 0) (𝓝 0) := by
  by_cases hn : n = 0
  · subst n
    simpa only [euclideanRegularize_zero_dimension,sub_self,eLpNorm_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ≥0∞)) (𝓝[>] 0) (𝓝 0))
  · exact tendsto_euclideanRegularize_eLpNorm (Nat.pos_of_ne_zero hn) p hp ht hf

/-- Locally integrable inputs have smooth mollifications in all
coordinate dimensions (BB pp. 72–73; degenerate carrier). -/
theorem contDiff_euclideanRegularize_all_dimensions
    {f : (Fin n → ℝ) → ℝ} (hf : LocallyIntegrable f volume)
    {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (euclideanRegularize n f ε) := by
  by_cases hn : n = 0
  · subst n
    rw [euclideanRegularize_zero_dimension]
    have he : f = fun _ => f (0 : Fin 0 → ℝ) :=
      funext fun x => congrArg f (Subsingleton.elim _ _)
    rw [he]
    exact contDiff_const
  · exact contDiff_euclideanRegularize_of_locallyIntegrable (Nat.pos_of_ne_zero hn) hf hε

end RothschildStein.S
