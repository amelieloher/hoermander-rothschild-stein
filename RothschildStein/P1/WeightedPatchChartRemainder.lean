-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.FinitePatchPoleExpansion
public import RothschildStein.P1.ChartRegularKernel

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The sharp lower-weight Taylor construction gives an actual
regular chart remainder after both compact endpoint cutoffs. The requested
regularity controls the finite Taylor budget explicitly. Jets are
required only on the two compact cutoff supports. This is the
coefficient-times-pole construction with the lower weighted jet condition
(BB Lemma 11.16 and Remark 11.17, pp. 548–549). -/
theorem LiftedChart.exists_patch_weightedTaylor_chart_remainder
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (W budget b low : ℕ) (hW : ∀ i, F.G.weight i ≤ W) (hb : 0 < b)
    (g : (Fin (n + m) → ℝ) → ℝ) (d : ℤ)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      g (F.G.dilate r u) = r ^ d * g u)
    (hd : (((budget + 1) * W : ℕ) : ℤ) < (b : ℤ) + d)
    (a c : TestFunction F.V ℝ (⊤ : ℕ∞))
    (A : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → ℝ)
    (hA : ContDiff ℝ (⊤ : ℕ∞) A)
    (hjet : ∀ ξ ∈ tsupport a, ∀ η ∈ tsupport c, ∀ I : List (Fin (n + m)), (I.map F.G.weight).sum < low →
      rsPartial I (fun u => A (ξ, η, u)) 0 = 0) :
    ∃ poly : List (List (Fin (n + m)) ×
        (((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) → ℝ)),
    ∃ r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ,
      (∀ q ∈ poly, low ≤ (q.1.map F.G.weight).sum ∧
        (q.1.map F.G.weight).sum < b ∧ ContDiff ℝ (⊤ : ℕ∞) q.2) ∧
      IsRegularKernel F budget r ∧ ∀ ξ η,
        a ξ * c η * (A (ξ, η, F.Θ η ξ) * g (F.Θ η ξ)) =
          (poly.map (fun q => a ξ * c η *
            (taylorWordMonomial q.1 (F.Θ η ξ) * q.2 (ξ, η) * g (F.Θ η ξ)))).sum + r ξ η := by
  let A₁ : (((Fin (n + m) → ℝ) × (Fin (n + m) → ℝ)) × (Fin (n + m) → ℝ)) → ℝ :=
    fun q => A (q.1.1, q.1.2, q.2)
  have hA₁ : ContDiff ℝ (⊤ : ℕ∞) A₁ :=
    hA.comp (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  obtain ⟨poly, R, hp, hR, he⟩ :=
    exists_finite_patch_weighted_pole_expansion F.G (tsupport a ×ˢ tsupport c) W budget b low hW hb g d hg hhom hd A₁ hA₁
      (fun p hp I hI => hjet p.1 hp.1 p.2 hp.2 I hI)
  let R₁ : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → ℝ :=
    fun q => R ((q.1, q.2.1), q.2.2)
  have hR₁ : ContDiff ℝ budget R₁ :=
    hR.comp ((contDiff_fst.prodMk contDiff_snd.fst).prodMk contDiff_snd.snd)
  let r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ :=
    fun ξ η => a ξ * c η * R₁ (ξ, η, F.Θ η ξ)
  refine ⟨poly, r, hp, C.isRegularKernel_cutoff_model F hΘ hVU budget a c R₁ hR₁, ?_⟩
  intro ξ η
  by_cases ha : a ξ = 0
  · simp [ha, r]
  by_cases hc : c η = 0
  · simp [hc, r]
  have h := he (ξ, η) ⟨subset_tsupport a ha, subset_tsupport c hc⟩ (F.Θ η ξ)
  change A (ξ, η, F.Θ η ξ) * g (F.Θ η ξ) = _ at h
  rw [h, mul_add, ← List.sum_map_mul_left]

end RothschildStein.P1
