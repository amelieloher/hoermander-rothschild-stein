-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalSignedRegularity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.G1

/-- Signed root substitution for actual endpoint displacements. -/
def signedRootEndpoint {n : ℕ} (k : ℕ)
    (Gp Gm : (Fin n → ℝ) × ℝ → (Fin n → ℝ))
    (q : ℝ × (Fin n → ℝ)) : Fin n → ℝ :=
  q.2 + if 0 ≤ q.1 then Gp (q.2, |q.1| ^ (1 / (k : ℝ)))
    else Gm (q.2, |q.1| ^ (1 / (k : ℝ)))

/-- Locally smooth actual time-power factors with opposite
leading coefficients make the signed actual endpoint jointly C¹.
Neither primitive flows nor their factors are extended analytically
(BB Theorem 1.48, pp. 32–34). -/
theorem signedRootEndpoint_contDiffAt_zero_of_factors {n k : ℕ} (hk : 0 < k)
    {V : Set ((Fin n → ℝ) × ℝ)} (hV : IsOpen V)
    (Gp Gm Hp Hm : (Fin n → ℝ) × ℝ → (Fin n → ℝ))
    (hHp : ContDiffOn ℝ (⊤ : ℕ∞) Hp V) (hHm : ContDiffOn ℝ (⊤ : ℕ∞) Hm V)
    (he : ∀ q ∈ V, Gp q = q.2 ^ k • Hp q ∧ Gm q = q.2 ^ k • Hm q)
    (hmatch : ∀ x, (x, 0) ∈ V → -Hm (x, 0) = Hp (x, 0))
    (x : Fin n → ℝ) (hx : (x, 0) ∈ V) :
    ContDiffAt ℝ 1 (signedRootEndpoint k Gp Gm) (0, x) := by
  let A : ((Fin 1 → ℝ) × (Fin n → ℝ)) → ((Fin n → ℝ) × ℝ) :=
    fun q => (q.2, q.1 0)
  have hA : ContDiff ℝ (⊤ : ℕ∞) A :=
    contDiff_snd.prodMk ((contDiff_apply ℝ ℝ 0).comp contDiff_fst)
  let α : Fin 1 → ℝ := fun _ => 1 / (k : ℝ)
  have hα : ∀ i, 0 < α i := fun _ => by dsimp [α]; positivity
  have hreg := signedWeightedFactoredMap_contDiffAt_zero_of_local_factors
    (hV.preimage hA.continuous) (Hp ∘ A) (Hm ∘ A)
    (hHp.comp hA.contDiffOn (fun _ hq => hq))
    (hHm.comp hA.contDiffOn (fun _ hq => hq))
    (fun y hy => hmatch y hy) α hα x hx
  apply hreg.congr_of_eventuallyEq
  have hroot : Continuous (fun q : ℝ × (Fin n → ℝ) =>
      (q.2, |q.1| ^ (1 / (k : ℝ)))) :=
    continuous_snd.prodMk (continuous_fst.abs.rpow_const (fun _ => Or.inr (by positivity)))
  have hroot₀ : (x, |(0 : ℝ)| ^ (1 / (k : ℝ))) = (x, 0) := by
    simp only [abs_zero, Real.zero_rpow (by positivity : (1 / (k : ℝ)) ≠ 0)]
  have hm : ∀ᶠ q : ℝ × (Fin n → ℝ) in 𝓝 (0, x),
      (q.2, |q.1| ^ (1 / (k : ℝ))) ∈ V :=
    hroot.continuousAt.preimage_mem_nhds (by simpa only [hroot₀] using hV.mem_nhds hx)
  filter_upwards [hm] with q hq
  have hpow : (|q.1| ^ (1 / (k : ℝ))) ^ k = |q.1| := by
    simpa only [one_div] using Real.rpow_inv_natCast_pow (abs_nonneg q.1) hk.ne'
  have hp := (he _ hq).1
  have hn := (he _ hq).2
  simp only [signedRootEndpoint, signedFactoredMap, Function.comp_apply, A,
    weightedAbsolutePowers, α, hp, hn, hpow]
  split_ifs with hq0
  · rw [abs_of_nonneg hq0]
  · rfl

end RothschildStein.G1
