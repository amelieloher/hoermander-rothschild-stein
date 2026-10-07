-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixKernelBoundsHomogeneous
public import RothschildStein.P1.KernelEstimatesWeightedTaylor

/-!
# Symbols from vanishing weighted jets (the remainder fields)

The remainder fields `R_{[i],η}` of the lifted chart have vanishing weighted jets at `u = 0`
(`LiftedChart.remainder_weight`: weight `≥ 1 - w_i`). This file shows that a globally smooth
function `F(η, u)` whose weighted `u`-jets of order `< b` vanish at `u = 0` for `η` in an open set
`O` lies in the symbol class `WtSym` of degree `b` on every compact parameter set whose
`η`-projection lies in `O`, with any number of derivatives in `η` and `u`.

The proof is by strong induction on `b`, through the Hadamard factorization along rays
`F(η, u) = ∑_j u_j F_j(η, u)` (`hadamard_decomp_param`): the factors `F_j` have vanishing jets of
order `< b - w_j`, the coordinate `u_j` is a symbol of degree `w_j`, and for `b ≤ 0` every smooth
function is a symbol (compactness). No Taylor polynomial is formed, and no mixed partial
derivatives are interchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace RothschildStein.P1

variable {N : ℕ}

/-- The weighted jets of `f` of order `< b` vanish at the origin. -/
def WtJetsVanish (G : HomogeneousGroup N) (b : ℤ) (f : (Fin N → ℝ) → ℝ) : Prop :=
  ∀ J : List (Fin N), (((J.map G.weight).sum : ℕ) : ℤ) < b → rsPartial J f 0 = 0

variable {G : HomogeneousGroup N} {K : Set ((Fin N → ℝ) × (Fin N → ℝ))} {R : ℝ}

/-- For `b ≤ 0` every globally smooth function of `(η, u)` is a symbol of degree `b` on a
compact parameter set (no vanishing needed: `ρ^b ≥ R^b` on `ρ ≤ R`). -/
theorem WtSym.of_smooth_nonpos (hK : IsCompact K) (hR : 0 < R) :
    ∀ {k : ℕ} {b : ℤ} (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F → b ≤ 0 →
      WtSym G K R k b (fun z => F z.2) := by
  have h0 : ∀ {b : ℤ} (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F → b ≤ 0 →
      WtSym G K R 0 b (fun z => F z.2) := by
    intro b F hF hb
    refine WtSym.intro_zero (hF.comp contDiff_snd).contDiffOn ?_
    have hC : IsCompact ((Prod.snd '' K) ×ˢ {u : Fin N → ℝ | kgauge G u ≤ R}) :=
      (hK.image continuous_snd).prod (G2.isCompact_gauge_le (G2.isHomogeneousGauge_max G) R)
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hF.continuous.continuousOn
    have hRb : 0 < R ^ b := zpow_pos hR b
    refine ⟨|M| / R ^ b, by positivity, fun z hzK hz hρ => ?_⟩
    have h1 := hM (z.2.1, z.2.2) ⟨⟨(z.1, z.2.1), hzK, rfl⟩, hρ⟩
    rw [Real.norm_eq_abs] at h1
    have hρpos : 0 < kgauge G z.2.2 := kgauge_pos G hz
    have h2 : R ^ b ≤ kgauge G z.2.2 ^ b := kzpow_le_of_nonpos hρpos hρ hb
    calc |F z.2| ≤ |M| := h1.trans (le_abs_self _)
      _ = |M| / R ^ b * R ^ b := by field_simp
      _ ≤ |M| / R ^ b * kgauge G z.2.2 ^ b :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  intro k
  induction k with
  | zero => exact fun F hF hb => h0 F hF hb
  | succ k ih =>
    intro b F hF hb
    have hdF : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ F) := (contDiff_infty_iff_fderiv.mp hF).2
    have hdiff : ∀ z : KZ N, DifferentiableAt ℝ F z.2 := fun z => (hF.differentiable (by simp)) _
    refine WtSym.intro_succ (h0 F hF hb) (fun s => ?_)
    rcases s with l | l | j
    · refine WtSym.congr (fun z _ => ?_)
        (WtSym.zero_fun (k := k) (d := b - symWt G (Sum.inl l)))
      rw [fderiv_eta_u (hdiff z)]
      exact map_zero (fderiv ℝ F z.2)
    · have h1 := ih (fun p => fderiv ℝ F p (Pi.single l 1, 0)) (hdF.clm_apply contDiff_const)
        hb
      refine (WtSym.congr (fun z _ => ?_) h1).degree_congr (by simp [symWt])
      rw [fderiv_eta_u (hdiff z)]
      rfl
    · have h1 := ih (b := b - (G.weight j : ℤ)) (fun p => fderiv ℝ F p (0, Pi.single j 1))
        (hdF.clm_apply contDiff_const) (by have := G.weight_pos j; omega)
      refine WtSym.congr (fun z _ => ?_) h1
      rw [fderiv_eta_u (hdiff z)]
      rfl

/-- **Symbols from vanishing jets.** Let `F(η, u)` be globally smooth, and suppose the
weighted `u`-jets of `F(η, ·)` of order `< b` vanish at `0` for all `η` in an open set `O`. Then
`(ξ, η, u) ↦ F(η, u)` lies in `WtSym G K R k b` for every compact `K` with `η`-projection in `O`
and all `k` (the Hadamard factorization `F = ∑_j u_j F_j` and induction on `b`). -/
theorem WtSym.of_jets (hK : IsCompact K) (hR : 0 < R) {O : Set (Fin N → ℝ)} (hO : IsOpen O)
    (hKO : ∀ p ∈ K, p.2 ∈ O) :
    ∀ (m : ℕ) {b : ℤ} (F : (Fin N → ℝ) × (Fin N → ℝ) → ℝ), b.toNat = m →
      ContDiff ℝ (⊤ : ℕ∞) F → (∀ η ∈ O, WtJetsVanish G b (fun u => F (η, u))) →
      ∀ k : ℕ, WtSym G K R k b (fun z => F z.2) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro b F hm hF hjet k
    by_cases hb : b ≤ 0
    · exact WtSym.of_smooth_nonpos hK hR F hF hb
    · replace hb : 0 < b := not_le.mp hb
      have hF0 : ∀ η ∈ O, F (η, 0) = 0 := fun η hη => by
        have := hjet η hη [] (by simpa using hb)
        simpa [rsPartial] using this
      obtain ⟨Fj, hFjdef⟩ : ∃ Fj : Fin N → (Fin N → ℝ) × (Fin N → ℝ) → ℝ, ∀ j p,
          Fj j p = ∫ θ in Icc (0 : ℝ) 1, fderiv ℝ F (p.1, θ • p.2) (0, Pi.single j 1) :=
        ⟨fun j p => ∫ θ in Icc (0 : ℝ) 1, fderiv ℝ F (p.1, θ • p.2) (0, Pi.single j 1),
          fun _ _ => rfl⟩
      have hFj : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Fj j) := fun j => by
        have : Fj j = fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
            ∫ θ in Icc (0 : ℝ) 1, fderiv ℝ F (p.1, θ • p.2) (0, Pi.single j 1) :=
          funext (hFjdef j)
        rw [this]
        exact hadamardFactor_param_contDiff F hF j
      have hjets : ∀ j, ∀ η ∈ O, WtJetsVanish G (b - (G.weight j : ℤ)) (fun u => Fj j (η, u)) := by
        intro j η hη J hJ
        have hg : ContDiff ℝ (⊤ : ℕ∞) (fun u : Fin N → ℝ => F (η, u)) :=
          hF.comp (contDiff_const.prodMk contDiff_id)
        have heq : (fun u => Fj j (η, u)) = fun y : Fin N → ℝ => ∫ θ in Icc (0 : ℝ) 1,
            rsPartial [j] (fun u => F (η, u)) (θ • y) := by
          funext y
          rw [hFjdef]
          refine setIntegral_congr_fun measurableSet_Icc (fun θ _ => ?_)
          exact (rsPartial_single_eq F hF η _ j).symm
        rw [heq]
        apply rsPartial_scaledIntegral_eq_zero _ (rsPartial_contDiff [j] hg)
        rw [rsPartial_append_single]
        apply hjet η hη
        have h1 : ((J ++ [j]).map G.weight).sum = (J.map G.weight).sum + G.weight j := by simp
        rw [h1, Nat.cast_add]
        omega
      have hcls : ∀ j, WtSym G K R k (b - (G.weight j : ℤ)) (fun z => Fj j z.2) := fun j =>
        ih (b - (G.weight j : ℤ)).toNat (by have := G.weight_pos j; omega) (Fj j) rfl (hFj j)
          (hjets j) k
      have hprod : ∀ j, WtSym G K R k b (fun z => z.2.2 j * Fj j z.2) := fun j =>
        (WtSym.mul (WtSym.coord G K R k j) (hcls j)).degree_congr (by ring)
      have hS := WtSym.sum (G := G) (K := K) (R := R) (k := k) (d := b) Finset.univ
        (fun j z => z.2.2 j * Fj j z.2) (fun j _ => hprod j)
      refine WtSym.congr_on (S := {z : KZ N | z.2.1 ∈ O})
        (hO.preimage (continuous_fst.comp continuous_snd)) (fun z hz => hKO _ hz)
        (hF.comp contDiff_snd).contDiffOn (fun z hz _ => ?_) hS
      have hdec := hadamard_decomp_param F hF z.2.1 z.2.2
      rw [hF0 z.2.1 hz, sub_zero] at hdec
      rw [show F z.2 = F (z.2.1, z.2.2) from rfl, hdec]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [hFjdef]

end RothschildStein.P1
