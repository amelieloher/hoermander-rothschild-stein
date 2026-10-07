-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalFrameSmoothness
public import RothschildStein.L1.FrameFlowScaling
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.L1

set_option backward.defeqAttrib.useBackward true in
/-- The canonical radial curve is the actual constant-coefficient
trajectory, and its derivative at time one is that coefficient field.
This proves the radial identity from ODE uniqueness (BB Lemma 10.23). -/
theorem canonicalFrameMap_radial_hasDerivAt {N : ℕ}
    {Ω : Set (Fin N → ℝ)} {U : Set ((Fin N → ℝ) × (Fin N → ℝ))}
    (hΩ : IsOpen Ω) (hU : IsOpen U) {τ a : ℝ} (ha : 0 < a) (haτ : a < τ)
    (Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (Φ : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (hsol : ∀ q ∈ U, Φ (q,0) = q.2 ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun s => Φ (q,s)) (frameCoefficientField Y (q.1,Φ (q,t))) t ∧
      Φ (q,t) ∈ Ω)
    (x u : Fin N → ℝ) (hp : (a⁻¹ • u,x) ∈ U) :
    HasDerivAt (fun s : ℝ => canonicalFrameMap a Φ (x,s • u))
      (frameCoefficientField Y (u,canonicalFrameMap a Φ (x,u))) 1 := by
  let b : ℝ := (a+τ)/2
  have hb : 0 < b := by dsimp [b]; linarith
  have hab : a < b := by dsimp [b]; linarith
  have hbτ : b < τ := by dsimp [b]; linarith
  have hat : a ∈ Ioo (-τ) τ := ⟨by linarith,haτ⟩
  have hatb : a ∈ Ioo (-b) b := ⟨by linarith,hab⟩
  have hparam : ∀ᶠ s : ℝ in 𝓝 1, (s • (a⁻¹ • u),x) ∈ U := by
    have hc : ContinuousAt (fun s : ℝ => (s • (a⁻¹ • u),x)) 1 :=
      (continuousAt_id.smul continuousAt_const).prodMk continuousAt_const
    exact hc.preimage_mem_nhds (by simpa only [one_smul] using hU.mem_nhds hp)
  have htime : ∀ᶠ s : ℝ in 𝓝 1, |s| * b < τ := by
    have hc : ContinuousAt (fun s : ℝ => |s| * b) 1 := continuousAt_id.abs.mul_const b
    exact hc.eventually_lt continuousAt_const (by simpa only [abs_one,one_mul] using hbτ)
  have heq : (fun s => canonicalFrameMap a Φ (x,s • u)) =ᶠ[𝓝 1]
      (fun s => Φ ((a⁻¹ • u,x),s*a)) := by
    filter_upwards [hparam,htime] with s hs ht
    have hst : ∀ v ∈ Ioo (-b) b, s*v ∈ Ioo (-τ) τ := by
      intro v hv
      apply abs_lt.mp
      rw [abs_mul]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (le_of_lt (abs_lt.mpr hv)) (abs_nonneg s)) ht
    have hh := frameFlow_smul_coefficients hΩ hb (le_of_lt hbτ) Y hY Φ hsol
      (a⁻¹ • u) x s hp hs hst hatb
    change Φ ((a⁻¹ • (s • u),x),a) = Φ ((a⁻¹ • u,x),s*a)
    rw [smul_comm a⁻¹ s u]
    exact hh
  have hda : HasDerivAt (fun v => Φ ((a⁻¹ • u,x),v))
      (frameCoefficientField Y (a⁻¹ • u,Φ ((a⁻¹ • u,x),a))) ((1 : ℝ)*a) := by
    simpa only [one_mul] using ((hsol (a⁻¹ • u,x) hp).2 a hat).1
  have hd := hda.scomp 1 ((hasDerivAt_id (1 : ℝ)).mul_const a)
  have hc : a • frameCoefficientField Y (a⁻¹ • u,Φ ((a⁻¹ • u,x),a)) =
      frameCoefficientField Y (u,canonicalFrameMap a Φ (x,u)) := by
    rw [← frameCoefficientField_smul,smul_smul,mul_inv_cancel₀ (ne_of_gt ha),one_smul]
    rfl
  have hd' : HasDerivAt (fun s => Φ ((a⁻¹ • u,x),s*a))
      (frameCoefficientField Y (u,canonicalFrameMap a Φ (x,u))) 1 := by
    simpa only [Function.comp_def,id_eq,one_mul,hc] using hd
  exact hd'.congr_of_eventuallyEq heq
end RothschildStein.L1
