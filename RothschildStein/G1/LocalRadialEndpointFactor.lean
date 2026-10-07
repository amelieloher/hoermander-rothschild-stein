-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalProductFactorization
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RothschildStein.G1

/-- A local smooth coefficient chart fixing every zero
coefficient has an exact smooth radial FTC factor near a prescribed
coefficient direction. This keeps the original open endpoint domain
(BB Proposition 1.50, pp. 28–29; Theorem 1.48, pp. 32–34). -/
theorem exists_local_radial_endpoint_factor {m n : ℕ}
    {U : Set ((Fin m → ℝ) × (Fin n → ℝ))} (hU : IsOpen U)
    (F : ((Fin m → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hzero : ∀ x, (0, x) ∈ U → F (0, x) = x)
    (v₀ : Fin m → ℝ) (x₀ : Fin n → ℝ) (hx₀ : (0, x₀) ∈ U) :
    ∃ V : Set ((Fin 1 → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))),
      IsOpen V ∧ (0, (v₀, x₀)) ∈ V ∧
      ∃ H : ((Fin 1 → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))) → (Fin n → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
        (∀ q ∈ V, F (q.1 0 • q.2.1, q.2.2) - q.2.2 = q.1 0 • H q) ∧
        H (0, (v₀, x₀)) = fderiv ℝ (fun z => F (z, x₀)) 0 v₀ := by
  classical
  let A := fun q : ((Fin 1 → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))) =>
    (q.1 0 • q.2.1, q.2.2)
  have hA : ContDiff ℝ (⊤ : ℕ∞) A :=
    ((contDiff_apply ℝ ℝ 0).comp contDiff_fst |>.smul contDiff_snd.fst).prodMk contDiff_snd.snd
  let W := A ⁻¹' U
  have hW : IsOpen W := hU.preimage hA.continuous
  let G := fun q : ((Fin 1 → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))) => F (A q) - q.2.2
  have hG : ContDiffOn ℝ (⊤ : ℕ∞) G W :=
    (hF.comp hA.contDiffOn (fun _ hq => hq)).sub contDiff_snd.snd.contDiffOn
  have hz : ∀ q ∈ W, ∀ i ∈ ({0} : Finset (Fin 1)), q.1 i = 0 → G q = 0 := by
    intro q hq i hi hqi
    have hi0 : i = 0 := Finset.mem_singleton.mp hi
    subst i
    have hqx : (0, q.2.2) ∈ U := by simpa only [W, mem_preimage, A, hqi, zero_smul] using hq
    simp only [G, A, hqi, zero_smul, hzero _ hqx, sub_self]
  have hq₀ : (0, (v₀, x₀)) ∈ W := by simpa only [W, mem_preimage, A, Pi.zero_apply, zero_smul] using hx₀
  obtain ⟨V, hV, hV₀, _hVW, H, hH, he⟩ :=
    exists_local_smooth_productFactor ({0} : Finset (Fin 1)) hW G hG hz
      (0, (v₀, x₀)) hq₀
  have he' : ∀ q ∈ V, G q = q.1 0 • H q := by
    intro q hq
    simpa only [Finset.prod_singleton] using he q hq
  refine ⟨V, hV, hV₀, H, hH, he', ?_⟩
  let q : ℝ → ((Fin 1 → ℝ) × ((Fin m → ℝ) × (Fin n → ℝ))) :=
    fun t => (fun _ => t, (v₀, x₀))
  have hq : ContDiff ℝ (⊤ : ℕ∞) q := (contDiff_pi.mpr (fun _ => contDiff_id)).prodMk contDiff_const
  have hq0 : q 0 = (0, (v₀, x₀)) := rfl
  have hHt : DifferentiableAt ℝ (fun t => H (q t)) 0 :=
    ((hH.contDiffAt (hV.mem_nhds hV₀)).comp (f := q) 0 hq.contDiffAt).differentiableAt (by simp)
  have hp : HasDerivAt (fun t : ℝ => t • H (q t)) (H (q 0)) (0 : ℝ) := by
    convert (hasDerivAt_id (0 : ℝ)).smul hHt.hasDerivAt using 1 <;> first | rfl | simp
  have hi : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : Fin m → ℝ => (z, x₀)) (0 : Fin m → ℝ) :=
    contDiffAt_id.prodMk contDiffAt_const
  have hslice : DifferentiableAt ℝ (fun z : Fin m → ℝ => F (z, x₀)) (0 : Fin m → ℝ) :=
    ((hF.contDiffAt (hU.mem_nhds hx₀)).comp
      (f := fun z : Fin m → ℝ => (z, x₀)) (0 : Fin m → ℝ) hi).differentiableAt (by simp)
  have hv : HasDerivAt (fun t : ℝ => t • v₀) v₀ (0 : ℝ) := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const v₀
  have hd : HasDerivAt (fun t : ℝ => F (t • v₀, x₀) - x₀)
      (fderiv ℝ (fun z => F (z, x₀)) 0 v₀) (0 : ℝ) := by
    have hh : HasFDerivAt (fun z : Fin m → ℝ => F (z, x₀))
        (fderiv ℝ (fun z => F (z, x₀)) 0) ((fun t : ℝ => t • v₀) 0) := by
      simpa using hslice.hasFDerivAt
    convert (hh.comp_hasDerivAt (0 : ℝ) hv).sub (hasDerivAt_const (0 : ℝ) x₀) using 1 <;> first | rfl | simp
  have heq : (fun t => F (t • v₀, x₀) - x₀) =ᶠ[𝓝 0] (fun t => t • H (q t)) := by
    have hm := hq.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hV₀)
    filter_upwards [hm] with t ht
    exact he' (q t) ht
  exact (hd.congr_of_eventuallyEq heq.symm).unique hp |>.symm

end RothschildStein.G1
