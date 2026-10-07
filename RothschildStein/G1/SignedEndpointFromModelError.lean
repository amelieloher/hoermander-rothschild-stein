-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.OppositeEndpointModelFactors
public import RothschildStein.G1.LocalSignedFactorsFromError
public import RothschildStein.G1.SignedEndpointDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.G1

/-- The actual signed endpoint inherits joint C¹ regularity
and its leading derivative from the genuine coefficient-flow model,
using only the model error of order s+1 (BB pp. 30–35, 417–419). -/
theorem signedRootEndpoint_regular_of_actual_endpoint_errors {m n k s : ℕ}
    (hk : 0 < k) (hks : k ≤ s)
    {U : Set ((Fin m → ℝ) × (Fin n → ℝ))} (hU : IsOpen U)
    (F : ((Fin m → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hzero : ∀ x, (0, x) ∈ U → F (0, x) = x)
    (H : ℝ → (Fin m → ℝ)) (hH : ContDiff ℝ (⊤ : ℕ∞) H)
    {W : Set ((Fin n → ℝ) × ℝ)} (hW : IsOpen W)
    (Gp Gm : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hGp : ContDiffOn ℝ (⊤ : ℕ∞) Gp W) (hGm : ContDiffOn ℝ (⊤ : ℕ∞) Gm W)
    (M : ℝ)
    (hp : ∀ q ∈ W, ‖Gp q - (F (q.2 ^ k • H q.2, q.1) - q.1)‖ ≤
      M * |q.2| ^ (s + 1))
    (hm : ∀ q ∈ W, ‖Gm q - (F (-(q.2 ^ k • H q.2), q.1) - q.1)‖ ≤
      M * |q.2| ^ (s + 1))
    (x : Fin n → ℝ) (hxU : (0, x) ∈ U) (hxW : (x, 0) ∈ W) :
    ContDiffAt ℝ 1 (signedRootEndpoint k Gp Gm) (0, x) ∧
      HasFDerivAt (signedRootEndpoint k Gp Gm)
        ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) +
          (ContinuousLinearMap.toSpanSingleton ℝ (fderiv ℝ (fun z => F (z, x)) 0 (H 0))).comp
            (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))) (0, x) := by
  obtain ⟨V, hV, hxV, Rp, Rm, hRp, hRm, he, hlead⟩ :=
    exists_local_opposite_endpoint_model_factors hU F hF hzero H hH k hk x hxU
  let V' : Set ((Fin n → ℝ) × ℝ) := Prod.swap ⁻¹' V ∩ W
  have hV' : IsOpen V' := (hV.preimage continuous_swap).inter hW
  have hxV' : (x, 0) ∈ V' := ⟨hxV, hxW⟩
  have hRp' : ContDiffOn ℝ (⊤ : ℕ∞) (Rp ∘ Prod.swap) V' :=
    hRp.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hq => hq.1)
  have hRm' : ContDiffOn ℝ (⊤ : ℕ∞) (Rm ∘ Prod.swap) V' :=
    hRm.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hq => hq.1)
  have hep : ∀ q ∈ V', ‖Gp q - q.2 ^ k • (Rp ∘ Prod.swap) q‖ ≤
      M * |q.2| ^ (s + 1) := by
    intro q hq
    have hh := (he (q.2, q.1) hq.1).1
    change F (q.2 ^ k • H q.2, q.1) - q.1 = q.2 ^ k • Rp (q.2, q.1) at hh
    rw [Function.comp_apply, Prod.swap_prod_mk, ← hh]
    exact hp q hq.2
  have hem : ∀ q ∈ V', ‖Gm q - q.2 ^ k • (Rm ∘ Prod.swap) q‖ ≤
      M * |q.2| ^ (s + 1) := by
    intro q hq
    have hh := (he (q.2, q.1) hq.1).2
    change F (-(q.2 ^ k • H q.2), q.1) - q.1 = q.2 ^ k • Rm (q.2, q.1) at hh
    rw [Function.comp_apply, Prod.swap_prod_mk, ← hh]
    exact hm q hq.2
  have hmatch : ∀ y, (y, 0) ∈ V' → -(Rm ∘ Prod.swap) (y, 0) = (Rp ∘ Prod.swap) (y, 0) :=
    fun y hy => (hlead y hy.1).2
  obtain ⟨T, hT, hxT, _, Hp, Hm, hHp, hHm, hfactor, hlead'⟩ :=
    exists_local_signed_factors_of_model_errors hks hV' Gp Gm (Rp ∘ Prod.swap)
      (Rm ∘ Prod.swap) (hGp.mono inter_subset_right) (hGm.mono inter_subset_right)
      hRp' hRm' hmatch M hep hem x hxV'
  have hmatch' : ∀ y, (y, 0) ∈ T → -Hm (y, 0) = Hp (y, 0) :=
    fun y hy => (hlead' y hy).2
  constructor
  · exact signedRootEndpoint_contDiffAt_zero_of_factors hk hT Gp Gm Hp Hm hHp hHm
      hfactor hmatch' x hxT
  · have hd := signedRootEndpoint_hasFDerivAt_zero_of_factors hk hT Gp Gm Hp Hm hHp hHm
      hfactor hmatch' x hxT
    have hHp₀ : Hp (x, 0) = fderiv ℝ (fun z => F (z, x)) 0 (H 0) :=
      ((hlead' x hxT).1).trans (hlead x hxV).1
    rwa [hHp₀] at hd

end RothschildStein.G1
