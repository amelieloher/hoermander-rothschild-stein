-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GeneratorTransferJets
public import RothschildStein.P1.TransferWeightedTaylor

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MvPolynomial
open scoped BigOperators
namespace RothschildStein.P1
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- Full transfer remainder coordinates
have uniform weighted Taylor bounds on compact sets of both endpoints.
No lower coordinate is removed (BB p. 557, Theorem 11.24). -/
theorem LiftedChart.exists_uniform_transfer_remainder_coordinate_bound
    (C : LiftedChart w s Ω hΩ X x₀ m) (i : Fin k) (j : Fin (n+m))
    {K : Set (Fin (n+m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ ξ ∈ K, ∀ η ∈ K, ∀ u : Fin (n+m) → ℝ, kgauge C.G u ≤ r →
      ‖C.generatorTransferRemainder i ξ η u j‖ ≤ M * kgauge C.G u ^
        (1 - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ)).toNat := by
  classical
  let T : Set ((((Fin (n+m) → ℝ) × (Fin (n+m) → ℝ)) × (Fin (n+m) → ℝ))) :=
    {q | (q.1.2, q.2) ∈ C.T ∧ (q.1.1, -q.2) ∈ C.T}
  have hT : IsOpen T :=
    (C.isOpen_T.preimage (continuous_fst.snd.prodMk continuous_snd)).inter
      (C.isOpen_T.preimage (continuous_fst.fst.prodMk continuous_snd.neg))
  let A := fun q : (((Fin (n+m) → ℝ) × (Fin (n+m) → ℝ)) × (Fin (n+m) → ℝ)) =>
    C.generatorTransferRemainder i q.1.1 q.1.2 q.2 j
  have hR (I : List (Fin k)) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (((Fin (n+m) → ℝ) × (Fin (n+m) → ℝ)) × (Fin (n+m) → ℝ)) =>
        C.R I q.1.1 (-q.2) j) T :=
    (contDiff_apply ℝ ℝ j).comp_contDiffOn
      ((C.remainder_smooth I).comp (contDiffOn_fst.fst.prodMk contDiffOn_snd.neg)
        (fun _ hq => hq.2))
  have hA : ContDiffOn ℝ (⊤ : ℕ∞) A T := by
    have hfirst : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun q : (((Fin (n+m) → ℝ) × (Fin (n+m) → ℝ)) × (Fin (n+m) → ℝ)) =>
          C.R [i] q.1.2 q.2 j) T :=
      (contDiff_apply ℝ ℝ j).comp_contDiffOn
        ((C.remainder_smooth [i]).comp (contDiffOn_fst.snd.prodMk contDiffOn_snd)
          (fun _ hq => hq.1))
    have hsum := ContDiffOn.sum (s := Finset.univ) fun l _ =>
      ((G2.contDiff_eval (C.generatorTransferCoefficient i l)).contDiffOn.comp
        contDiffOn_snd (fun _ _ => Set.mem_univ _)).mul (hR (C.B l))
    simpa only [A, LiftedChart.generatorTransferRemainder, Pi.sub_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Function.comp_def] using hfirst.sub hsum
  obtain ⟨r, hr, hr1, M, hM, hb⟩ := weighted_taylor_local_transfer_parameters C.G T hT A hA
    (K ×ˢ K) (hK.prod hK)
    (fun p hp => ⟨C.mem_T_zero (hKU hp.2), by
      simpa only [neg_zero] using C.mem_T_zero (hKU hp.1)⟩)
    (1 - ((w i : ℕ) : ℤ) + (C.G.weight j : ℤ)).toNat (by
      intro p hp J hJ
      apply C.generatorTransferRemainder_weight i (hKU hp.1) (hKU hp.2) j J
      omega)
  exact ⟨r, hr, hr1, M, hM, fun ξ hξ η hη u hu => hb (ξ,η) ⟨hξ,hη⟩ u hu⟩

end RothschildStein.P1
