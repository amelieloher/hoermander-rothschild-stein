-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierSubstitution
public import RothschildStein.G2.ConvolutionSmooth
public import RothschildStein.G2.MollifierBound

/-! Constant plateaus and unit-interval bounds under group regularization. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein Filter
open scoped Topology
namespace HeatKernel

/-- A constant plateau on an open neighborhood of a compact set persists there for
all sufficiently small positive group regularizations. -/
theorem eventually_groupRegularize_eqOn_const {N : ℕ} (G : HomogeneousGroup N)
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν)
    {f : (Fin N → ℝ) → ℝ} {K U : Set (Fin N → ℝ)}
    (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    {c : ℝ} (hf : EqOn f (fun _ => c) U) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, EqOn (G2.groupRegularize G φ f ε) (fun _ => c) K := by
  let H : ℝ × ((Fin N → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ) :=
    fun p => G.mul (G.inv (G.dilate p.1 p.2.1)) p.2.2
  have hd : Continuous (fun p : ℝ × ((Fin N → ℝ) × (Fin N → ℝ)) =>
      G.dilate p.1 p.2.1) := by
    apply continuous_pi
    intro j
    exact (continuous_fst.pow (G.weight j)).mul
      ((continuous_apply j).comp (continuous_fst.comp continuous_snd))
  have hi := (G2.continuous_inv G).comp hd
  have hH : Continuous H := by
    apply continuous_pi
    intro j
    exact (MvPolynomial.continuous_eval (p := G.productPolynomial j)).comp
      (continuous_pi fun i => Sum.casesOn i
        (fun k => (continuous_apply k).comp hi)
        (fun k => (continuous_apply k).comp (continuous_snd.comp continuous_snd)))
  have he : ∀ᶠ ε : ℝ in 𝓝 0, ∀ p ∈ tsupport φ ×ˢ K, H (ε,p) ∈ U := by
    apply (φ.compact.prod hK).eventually_forall_of_forall_eventually
    intro p hp
    apply hH.continuousAt.eventually (hU.mem_nhds ?_)
    simpa only [H, G2.zero_dilate, G2.inv_zero, G2.zero_mul] using hKU hp.2
  filter_upwards [he.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with ε hε hpos
  change 0 < ε at hpos
  intro x hx
  rw [G2.groupRegularize_eq_integral G φ f hpos]
  calc
    (∫ z, φ z * f (G.mul (G.inv (G.dilate ε z)) x)) = ∫ z, φ z * c := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        by_cases hz : z ∈ tsupport φ
        · change φ z * f (H (ε,z,x)) = φ z * c
          rw [hf (hε (z,x) ⟨hz,hx⟩)]
        · simp only [image_eq_zero_of_notMem_tsupport hz, zero_mul]
    _ = c := by rw [integral_mul_const, φ.integral_eq_one, one_mul]

/-- Nonnegative normalized group regularization preserves the unit interval. -/
theorem groupRegularize_mem_Icc_zero_one {N : ℕ} (G : HomogeneousGroup N)
    {ν : G2.HomogeneousNorm G} (φ : G2.GroupMollifier G ν)
    {f : (Fin N → ℝ) → ℝ} (hf : Continuous f) (hb : ∀ x, f x ∈ Icc 0 1)
    {ε : ℝ} (hε : 0 < ε) (x : Fin N → ℝ) :
    G2.groupRegularize G φ f ε x ∈ Icc 0 1 := by
  constructor
  · rw [G2.groupRegularize_eq_integral G φ f hε]
    exact integral_nonneg (fun z => mul_nonneg (φ.nonneg z) (hb _).1)
  · have hn := G2.norm_groupRegularize_le G φ hf
      (fun z => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hb z).1] using (hb z).2) hε x
    exact (le_abs_self _).trans hn

end HeatKernel
