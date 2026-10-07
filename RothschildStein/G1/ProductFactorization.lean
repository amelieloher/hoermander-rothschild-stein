-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.HadamardFactor
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Instances.RealVectorSpace

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G1

universe u
variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LocallyCompactSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- Repeated oriented FTC gives a smooth product factor for any
finite set of vanishing independent parameter hyperplanes. No division is
used on those hyperplanes (BB Prop 1.50, pp. 28–29). -/
theorem exists_smooth_productFactor {n : ℕ} (S : Finset (Fin n))
    (G : ((Fin n → ℝ) × E) → F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hzero : ∀ q i, i ∈ S → q.1 i = 0 → G q = 0) :
    ∃ H : ((Fin n → ℝ) × E) → F, ContDiff ℝ (⊤ : ℕ∞) H ∧
      ∀ q, G q = (∏ i ∈ S, q.1 i) • H q := by
  classical
  induction S using Finset.induction_on generalizing G with
  | empty =>
    exact ⟨G, hG, fun q => by simp⟩
  | @insert i S hi ih =>
    let K : (((Fin n → ℝ) × E) × ℝ) → F := fun z =>
      G (Function.update z.1.1 i z.2, z.1.2)
    have hu : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : (((Fin n → ℝ) × E) × ℝ) => Function.update z.1.1 i z.2) := by
      apply contDiff_pi.mpr
      intro j
      by_cases hj : j = i
      · subst j
        simpa only [Function.update_self] using
          (contDiff_snd : ContDiff ℝ (⊤ : ℕ∞)
            (fun z : (((Fin n → ℝ) × E) × ℝ) => z.2))
      · simpa only [Function.update_of_ne hj, Function.comp_def] using
          (contDiff_apply ℝ ℝ j).comp contDiff_fst.fst
    have hK : ContDiff ℝ (⊤ : ℕ∞) K := hG.comp (hu.prodMk contDiff_fst.snd)
    let Q : ((Fin n → ℝ) × E) → F := fun q => hadamardFactor K (q, q.1 i)
    have hQ : ContDiff ℝ (⊤ : ℕ∞) Q :=
      (hadamardFactor_contDiff K hK).comp
        (contDiff_id.prodMk ((contDiff_apply ℝ ℝ i).comp contDiff_fst))
    have heq (q : (Fin n → ℝ) × E) : G q = q.1 i • Q q := by
      have h := hadamardFactor_smul K hK q (q.1 i)
      have hz : K (q, 0) = 0 :=
        hzero (Function.update q.1 i 0, q.2) i (Finset.mem_insert_self i S)
          (Function.update_self ..)
      have hsame : K (q, q.1 i) = G q := by
        dsimp [K]
        rw [Function.update_eq_self]
      rw [hz, hsame, sub_zero] at h
      exact h.symm
    have hzQ : ∀ q j, j ∈ S → q.1 j = 0 → Q q = 0 := by
      intro q j hj hqj
      have hji : j ≠ i := fun h => hi (h ▸ hj)
      apply hadamardFactor_eq_zero_of_slice_zero K hK q
      intro t
      exact hzero (Function.update q.1 i t, q.2) j
        (Finset.mem_insert_of_mem hj) (by simpa only [Function.update_of_ne hji] using hqj)
    obtain ⟨H, hH, hfactor⟩ := ih Q hQ hzQ
    refine ⟨H, hH, ?_⟩
    intro q
    rw [heq q, hfactor q, smul_smul, Finset.prod_insert hi]

end RothschildStein.G1
