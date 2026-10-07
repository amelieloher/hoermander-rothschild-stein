-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TransferRowLocalIntegrability
public import RothschildStein.P1.PrincipalRadialErrorLimit
public import RothschildStein.P1.CompactUniformWeakLimits
public import RothschildStein.P1.UniformFiniteSumLimits

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n+m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- Every principal component satisfying the
original type-degree bound has the actual weak transfer identity on a
standard frame. All endpoint limits are proved, including the critical
case (BB Theorem 11.24, pp. 555–558). -/
theorem principalTransfer_action_hasWeakWordDeriv_standard
    (hF : C.IsStandardFrame F H K hQ) (t : PrincipalTerm F) (i : Fin k)
    (lam : ℕ) (hw : (w i : ℕ) ≤ lam) (hd : t.degree ≤ 2 - (lam : ℤ))
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    hasWeakWordDeriv C.Xl F.V [i] (fun ξ => ∫ η, t.kernel ξ η * φ η)
      (fun ξ => (∑ j, ∫ η, C.generatorTransferKernel F i j t.kernel ξ η *
        fieldDerivative (wordBracket C.Xl (C.B j)) φ η) +
        ∫ η, C.principalTransferErrorKernel F hF.lifted t i ξ η * φ η) := by
  classical
  have hlam : 1 ≤ lam := (w i).pos.trans_le hw
  have hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U := subset_closure.trans hF.lifted.closure_subset
  have hX := fun j => C.transferGenerator_smooth F hF.lifted j
  let φB := fun j => fieldDerivativeTest F.V (wordBracket C.Xl (C.B j))
    (C.transferBasis_smooth F hF.lifted j) φ
  have hJB (j : Fin (n+m)) : IsTypeKernel F (lam + wordWeight w (C.B j) - (w i : ℕ))
      (C.generatorTransferKernel F i j t.kernel) :=
    C.isTypeKernel_generatorTransferKernel F hF.lifted (t.isTypeKernel lam hd) i j
  have hJpos := fun j => C.generatorTransfer_type_pos i j hw
  have hE := C.isTypeKernel_principalTransferErrorKernel F hF.lifted t i lam hw hd
  have hEpos := generatorTransfer_error_type_pos i hw
  have hiF := C.positiveKernelRow_locallyIntegrableOn_standard hF hlam (t.isTypeKernel lam hd) φ
  have hiJ (j : Fin (n+m)) : LocallyIntegrableOn
      (fun ξ => ∫ η, C.generatorTransferKernel F i j t.kernel ξ η *
        fieldDerivative (wordBracket C.Xl (C.B j)) φ η)
      (F.V : Set (Fin (n+m) → ℝ)) volume :=
    C.positiveKernelRow_locallyIntegrableOn_standard hF (hJpos j) (hJB j) (φB j)
  have hiE := C.positiveKernelRow_locallyIntegrableOn_standard hF hEpos hE φ
  have hiG := (locallyIntegrableOn_finiteRows F.V _ hiJ).add hiE
  let θ := fun u => radialCutoffProfile (H.norm u)
  let χ := fun (ε : ℝ) (u : Fin (n+m) → ℝ) => 1 - θ (C.G.dilate ε⁻¹ u)
  have hθ : ContDiff ℝ (⊤ : ℕ∞) θ := radialGaugeCutoff_contDiff H.norm.gauge hF.norm_smooth
  have heθ : θ =ᶠ[𝓝 (0 : Fin (n+m) → ℝ)] fun _ => 1 := radialGaugeCutoff_eventually_one H.norm.gauge
  have hχ (ε : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (χ ε) :=
    contDiff_const.sub (hθ.comp (G2.contDiff_dilate C.G ε⁻¹))
  have heχ (ε : ℝ) : χ ε =ᶠ[𝓝 (0 : Fin (n+m) → ℝ)] fun _ => 0 := by
    have h := cutoff_dilate_eventually_one C.G heθ ε
    filter_upwards [h] with u hu
    change 1 - θ (C.G.dilate ε⁻¹ u) = 0
    change θ (C.G.dilate ε⁻¹ u) = 1 at hu
    rw [hu, sub_self]
  let Fε := fun ε ξ => ∫ η, (χ ε (F.Θ η ξ) * t.kernel ξ η) * φ η
  let Jε := fun j ε ξ => ∫ η,
    C.generatorTransferKernel F i j (fun x y => χ ε (F.Θ y x) * t.kernel x y) ξ η *
      fieldDerivative (wordBracket C.Xl (C.B j)) φ η
  let Eε := fun ε ξ => ∫ η,
    C.regularTransferErrorKernel F i (fun x y => χ ε (F.Θ y x) * t.kernel x y) ξ η * φ η
  have hweak (ε : ℝ) : hasWeakWordDeriv C.Xl F.V [i] (Fε ε)
      (fun ξ => (∑ j, Jε j ε ξ) + Eε ε ξ) :=
    C.principalCutoff_action_hasWeakWordDeriv F hF.lifted t i (χ ε) (hχ ε) (heχ ε) φ
  apply hasWeakWordDeriv_of_compactUniformLimits (l := 𝓝[>] (0 : ℝ)) F.V C.Xl hX [i]
    Fε (fun ε ξ => (∑ j, Jε j ε ξ) + Eε ε ξ) _ _ hweak hiF hiG
  · intro L hL hLV
    have ht := (C.positiveTypeInput_uniformRadialRows hlam hF.lifted
      (t.isTypeKernel lam hd) H.norm.gauge φ hL (hLV.trans hVU)).limit
    apply ht.congr
    apply Filter.Eventually.of_forall
    intro ε ξ _
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun η => by
      dsimp only [Fε, χ, θ]
      rw [hF.lifted.Θ_eq]
      ring)
  · intro L hL hLV
    have htJ (j : Fin (n+m)) : TendstoUniformlyOn (Jε j)
        (fun ξ => ∫ η, C.generatorTransferKernel F i j t.kernel ξ η *
          fieldDerivative (wordBracket C.Xl (C.B j)) φ η) (𝓝[>] (0 : ℝ)) L := by
      have ht := (C.positiveTypeInput_uniformRadialRows (hJpos j) hF.lifted
        (hJB j) H.norm.gauge (φB j) hL (hLV.trans hVU)).limit
      apply ht.congr
      apply Filter.Eventually.of_forall
      intro ε ξ _
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun η => by
        change (1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ η ξ)))) *
          (C.generatorTransferKernel F i j t.kernel ξ η *
            fieldDerivative (wordBracket C.Xl (C.B j)) φ η) = _
        dsimp only [Jε, generatorTransferKernel, χ, θ]
        rw [hF.lifted.Θ_eq]
        ring)
    have htE : TendstoUniformlyOn Eε
        (fun ξ => ∫ η, C.principalTransferErrorKernel F hF.lifted t i ξ η * φ η)
        (𝓝[>] (0 : ℝ)) L :=
      C.principalRadial_errorRow_tendstoUniformlyOn hF t i (by
        have hnat : ((w i : ℕ) : ℤ) ≤ (lam : ℤ) := by exact_mod_cast hw
        omega) hEpos hE φ hL hLV
    have htSum := tendstoUniformlyOn_finsetSum Finset.univ Jε
      (fun j ξ => ∫ η, C.generatorTransferKernel F i j t.kernel ξ η *
        fieldDerivative (wordBracket C.Xl (C.B j)) φ η) (fun j _ => htJ j)
    simpa only [Pi.add_def] using htSum.add htE

end RothschildStein.P1.LiftedChart
