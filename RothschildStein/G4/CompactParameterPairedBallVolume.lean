-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.SmoothParameterPairedBallVolume
public import Mathlib.Data.Finset.Lattice.Fold
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.G4

/-- One paired original-radius volume-polynomial comparison
holds over all compact parameters and an arbitrary compact spatial patch.
A finite spatial cover replaces the single convex-buffer restriction. -/
theorem exists_compact_parameter_paired_ball_volume_provider {Sg : Type*}
    [UniformSpace Sg] [CompactSpace Sg] {k n s : ℕ}
    (hn : 0 < n) (hs : 0 < s) (w : Fin (k+1) → ℕ+) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Sg → Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ σ i, ContDiffOn ℝ (⊤ : ℕ∞) (X σ i) Ω)
    (hstep : ∀ σ, bracketStepOn Ω w (X σ) s)
    (hjoint : ∀ i j, ContinuousOn
      (fun q : Sg × (Fin n → ℝ) => iteratedFDeriv ℝ j (X q.1 i) q.2) (univ ×ˢ Ω))
    (K : Set (Fin n → ℝ)) (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    let m := Fintype.card (ShortWord w s)
    let wf : Fin m → ℕ+ := fun j => shortWeight w (shortIndex w j)
    let Zf := fun σ j => shortField w (X σ) (shortIndex (s := s) w j)
    ∃ c C ε : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧
      ∀ σ, ∀ x ∈ K, ∀ r : ℝ, 0 < r → r ≤ ε →
        let Λ := volumePolynomial (fun B : Fin n → Fin m => frameDet (Zf σ) B x)
          (fun B => ∑ i, (wf (B i) : ℕ)) r
        (ENNReal.ofReal (c*Λ) ≤ volume (controlBall Ω w (X σ) x r) ∧
          volume (controlBall Ω w (X σ) x r) ≤ ENNReal.ofReal (C*Λ)) ∧
        (ENNReal.ofReal (c*Λ) ≤ volume (controlBall Ω wf (Zf σ) x r) ∧
          volume (controlBall Ω wf (Zf σ) x r) ≤ ENNReal.ofReal (C*Λ)) := by
  classical
  intro m wf Zf
  rcases K.eq_empty_or_nonempty with he | hne
  · refine ⟨1,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro σ x hx
    simp only [he,mem_empty_iff_false] at hx
  choose R c C ε hR hRΩ hc hC hε hb using
    (fun z : K => exists_smooth_parameter_paired_ball_volume_provider hn hs w hw hΩ
      X hX hstep hjoint (hKΩ z.property))
  obtain ⟨t,ht⟩ := hK.elim_finite_subcover (fun z : K => ball z.val (R z/16))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr
      ⟨⟨x,hx⟩,mem_ball_self (div_pos (hR ⟨x,hx⟩) (by norm_num))⟩)
  obtain ⟨x₀,hx₀⟩ := hne
  obtain ⟨z₀,hz₀,_⟩ := mem_iUnion₂.mp (ht hx₀)
  have htne : t.Nonempty := ⟨z₀,hz₀⟩
  refine ⟨t.inf' htne c,t.sup' htne C,t.inf' htne ε,
    (Finset.lt_inf'_iff htne).mpr (fun z _ => hc z),
    (hC z₀).trans_le (Finset.le_sup' C hz₀),
    (Finset.lt_inf'_iff htne).mpr (fun z _ => hε z),?_⟩
  intro σ x hx r hr hrr
  obtain ⟨z,hz,hxz⟩ := mem_iUnion₂.mp (ht hx)
  have hh := hb z σ x (ball_subset_closedBall hxz) r hr (hrr.trans (Finset.inf'_le ε hz))
  have hΛ : 0 ≤ volumePolynomial (fun B : Fin n → Fin m => frameDet (Zf σ) B x)
      (fun B => ∑ i, (wf (B i) : ℕ)) r := volumePolynomial_nonneg _ _ hr.le
  have hlo := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Finset.inf'_le c hz) hΛ)
  have hhi := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (Finset.le_sup' C hz) hΛ)
  exact ⟨⟨hlo.trans hh.1.1,hh.1.2.trans hhi⟩,⟨hlo.trans hh.2.1,hh.2.2.trans hhi⟩⟩
end RothschildStein.G4
