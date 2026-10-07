-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalRadialErrorRow
public import RothschildStein.P1.PositiveTypeUniformRadialRows
public import RothschildStein.P1.UniformTransferFieldFluxLimit
public import RothschildStein.P1.StandardFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n+m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- Finite regularized principal transfer
error rows converge uniformly to the actual positive typed error.
The complete remainder flux vanishes also at the critical degree. -/
theorem principalRadial_errorRow_tendstoUniformlyOn
    (hF : C.IsStandardFrame F H K hQ) (t : PrincipalTerm F) (i : Fin k)
    (hd : t.degree ≤ 2 - ((w i : ℕ) : ℤ))
    {mu : ℕ} (hmu : 1 ≤ mu)
    (hE : IsTypeKernel F mu (C.principalTransferErrorKernel F hF.lifted t i))
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n+m) → ℝ)} (hL : IsCompact L)
    (hLV : L ⊆ (F.V : Set (Fin (n+m) → ℝ))) :
    TendstoUniformlyOn (fun ε : ℝ => fun ξ => ∫ η,
      C.regularTransferErrorKernel F i
        (fun x y => (1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (F.Θ y x)))) * t.kernel x y)
          ξ η * φ η)
      (fun ξ => ∫ η, C.principalTransferErrorKernel F hF.lifted t i ξ η * φ η)
      (𝓝[>] (0 : ℝ)) L := by
  have hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U := subset_closure.trans hF.lifted.closure_subset
  have hLU := hLV.trans hVU
  let ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hVU⟩
  let θ := fun u => radialCutoffProfile (H.norm u)
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := radialGaugeCutoff_contDiff H.norm.gauge hF.norm_smooth
  have hsθ : HasCompactSupport θ := radialGaugeCutoff_hasCompactSupport H.norm.gauge
  have heθ : θ =ᶠ[𝓝 (0 : Fin (n+m) → ℝ)] fun _ => 1 := radialGaugeCutoff_eventually_one H.norm.gauge
  have hβ : ((w i : ℕ) : ℝ) - C.G.homogeneousDimension ≤
      (2 : ℝ) - C.G.homogeneousDimension - t.degree := by
    have hdR : (t.degree : ℝ) ≤ 2 - ((w i : ℕ) : ℝ) := by exact_mod_cast hd
    linarith
  have htFlux := C.tendstoUniformlyOn_transfer_remainder_field_flux hL hLU i hβ
    t.cutoffModelKernel (t.cutoffModelKernel_contDiffOn (hF.lifted.pole_smooth t.star)).continuousOn
    (by simpa only [hF.lifted.G_eq] using
      (t.cutoffModelKernel_homogeneous (hF.lifted.pole_smooth t.star)
        (by simpa only [hF.lifted.G_eq] using hF.lifted.pole_homogeneous t.star)))
    hθ hsθ heθ ψ
  have htE := (C.positiveTypeInput_uniformRadialRows hmu hF.lifted hE H.norm.gauge φ hL hLU).limit
  have ht := htE.add htFlux.neg
  have ht' := ht.congr_right
    (g := fun ξ => ∫ η, C.principalTransferErrorKernel F hF.lifted t i ξ η * φ η)
    (fun ξ _ => by
    change (∫ η, C.principalTransferErrorKernel F hF.lifted t i ξ η * φ η) + -(0 : ℝ) = _
    simp only [neg_zero, add_zero])
  apply ht'.congr
  apply Filter.Eventually.of_forall
  intro ε ξ hξ
  have hr := C.principalRadial_errorRow_eq F hF.lifted t i hmu hE hθ heθ
    (fun u => radialCutoffProfile_norm_le _) ε φ (hLV hξ)
  have hder : fieldDerivative
      (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v)
      ((fun v => 1 - θ v) ∘ C.G.dilate ε⁻¹) =
      fun u => -fieldDerivative
        (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v)
        (θ ∘ C.G.dilate ε⁻¹) u :=
    H1.fieldDerivative_one_sub_C1 _
      ((hθ.comp (G2.contDiff_dilate C.G ε⁻¹)).of_le (by simp))
  rw [hder] at hr
  have hneg : (∫ u, t.cutoffModelKernel ξ ((C.e ξ).symm (-u)) u *
      -fieldDerivative (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v)
        (θ ∘ C.G.dilate ε⁻¹) u * C.reflectedTransport ξ φ u) =
      -(∫ u, t.cutoffModelKernel ξ ((C.e ξ).symm (-u)) u *
        fieldDerivative (fun v => C.generatorTransferRemainder i ξ ((C.e ξ).symm (-v)) v)
          (θ ∘ C.G.dilate ε⁻¹) u * C.reflectedTransport ξ φ u) := by
    rw [← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun u => by ring))
  rw [hneg] at hr
  exact hr.symm

end RothschildStein.P1.LiftedChart
