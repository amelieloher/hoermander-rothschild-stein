-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ChartRegularKernel
public import RothschildStein.S.Locality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- Smooth model multiplication preserves a regular remainder.
Plateaus on the two projections of its compact support allow the local
chart-composition lemma to apply without global smoothness of Θ
(BB Lemma 11.23, pp. 554–555; Theorem 11.24, pp. 555–558). -/
theorem LiftedChart.isRegularKernel_modelMultiplier
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U)
    {budget : ℕ} {r : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ}
    (hr : IsRegularKernel F budget r) (g : (Fin (n+m) → ℝ) → ℝ)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    IsRegularKernel F budget (fun ξ η => g (F.Θ η ξ) * r ξ η) := by
  let f := fun z : (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) => r z.1 z.2
  let A : Compacts (Fin (n+m) → ℝ) :=
    ⟨Prod.fst '' tsupport f, hr.2.1.isCompact.image continuous_fst⟩
  let B : Compacts (Fin (n+m) → ℝ) :=
    ⟨Prod.snd '' tsupport f, hr.2.1.isCompact.image continuous_snd⟩
  have hA : (A : Set (Fin (n+m) → ℝ)) ⊆ F.V := by
    rintro _ ⟨z,hz,rfl⟩
    exact (hr.2.2 hz).1
  have hB : (B : Set (Fin (n+m) → ℝ)) ⊆ F.V := by
    rintro _ ⟨z,hz,rfl⟩
    exact (hr.2.2 hz).2
  obtain ⟨a,U,_,hAU,_,ha⟩ := S.exists_test_plateau F.V A hA
  obtain ⟨b,W,_,hBW,_,hb⟩ := S.exists_test_plateau F.V B hB
  let R := fun z : (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) =>
    g z.2.2 * r z.1 z.2.1
  have hR : ContDiff ℝ budget R :=
    ((hg.of_le (by simp)).comp contDiff_snd.snd).mul
      (hr.1.comp (contDiff_fst.prodMk contDiff_snd.fst))
  have ht := C.isRegularKernel_cutoff_model F hΘ hVU budget a b R hR
  have he : (fun ξ η => a ξ * b η * R (ξ,η,F.Θ η ξ)) =
      (fun ξ η => g (F.Θ η ξ) * r ξ η) := by
    funext ξ η
    by_cases h : (ξ,η) ∈ tsupport f
    · rw [ha (hAU ⟨(ξ,η),h,rfl⟩), hb (hBW ⟨(ξ,η),h,rfl⟩)]
      simp [R]
    · have hz : r ξ η = 0 := image_eq_zero_of_notMem_tsupport (f := f) h
      simp only [R, hz, mul_zero]
  rw [he] at ht
  exact ht

end RothschildStein.P1
