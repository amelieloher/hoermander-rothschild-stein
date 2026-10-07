-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.UnconditionalOrdinaryBallBounds
public import RothschildStein.G4.OrdinaryBallDomainLocalization
public import RothschildStein.G1.LocalStep
public import RothschildStein.P2.HolderTransferReverse
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.G4

/-- The original-domain compact-center doubling predicate used
by RS-3 follows from smoothness and pointwise bracket rank. The selected
step is local to a compact buffer; no global fixed step, connectivity,
chart certificate, or topology comparison is required as a premise
(BB Theorems 9.1 and 9.12, pp. 400, 405; local-domain convention, p. 406). -/
theorem originalLocalDoubling_of_smooth_bracketSpans {a n : ℕ}
    (hn : 0 < n) {Ω N : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hNΩ : N ⊆ Ω)
    (w : Fin a → ℕ+) (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hrank : bracketSpansOn Ω X) : P2.OriginalLocalDoubling Ω w X N := by
  classical
  intro K hK hKN
  rcases K.eq_empty_or_nonempty with he | hne
  · refine ⟨1,1,by norm_num,by norm_num,?_⟩
    intro x hx
    simp only [he,mem_empty_iff_false] at hx
  have hKΩ : K ⊆ Ω := hKN.trans hNΩ
  obtain ⟨V,hV,hKV,hVcΩ,_hVc,_hVb,s₀,hs₀,hstep₀⟩ :=
    G1.exists_uniform_step_buffer hΩ hK hKΩ w X hX hrank
  have hVΩ : V ⊆ Ω := subset_closure.trans hVcΩ
  let s := max s₀ (Finset.univ.sup (fun i : Fin a => (w i : ℕ)))
  have hs : 1 ≤ s := hs₀.trans (le_max_left _ _)
  have hw : ∀ i, (w i : ℕ) ≤ s := fun i =>
    (Finset.le_sup (s := Finset.univ) (f := fun j : Fin a => (w j : ℕ))
      (Finset.mem_univ i)).trans (le_max_right _ _)
  have hstep : bracketStepOn V w X s := by
    intro x hx
    apply top_unique
    rw [← hstep₀ x (subset_closure hx)]
    apply Submodule.span_mono
    rintro v ⟨I,hI,hIs,rfl⟩
    exact ⟨I,hI,hIs.trans (le_max_left _ _),rfl⟩
  cases a with
  | zero =>
    obtain ⟨x,hx⟩ := hne
    obtain ⟨B,_hB⟩ := exists_short_frame hstep (hKV hx)
    let J := B ⟨0,hn⟩
    have hJ := ((mem_shortWordFamily_iff w J.val).mp J.property).1
    have hempty : J.val = [] := by
      cases hval : J.val with
      | nil => rfl
      | cons i I => exact Fin.elim0 i
    exact False.elim (hJ hempty)
  | succ k =>
    obtain ⟨L,δ,hL,hδ,hd⟩ := exists_compact_ordinary_ball_doubling_of_smooth_bracketStep
      hn hs w hw hV hK hKV X (fun i => (hX i).mono hVΩ) hstep
    obtain ⟨ε,hε,heq⟩ := exists_uniform_rsBall_domain_localization
      hK hV hKV hVΩ w X (fun i => (hX i).continuousOn)
    refine ⟨min δ ε,L*2^(n*s),lt_min hδ hε,mul_pos hL (by positivity),?_⟩
    intro x hx r hr h2r
    have hrδ : r ≤ δ := by have hh := h2r.trans (min_le_left _ _); linarith
    have hrε : r ≤ ε := by have hh := h2r.trans (min_le_right _ _); linarith
    have hball (t : ℝ) : rsBall V w X x t =
        {y | controlDistance V w X x y < ENNReal.ofReal t} := by
      ext y
      exact ⟨fun hy => hy.2,
        fun hy => ⟨controlBall_subset_domain V w X x t hy,hy⟩⟩
    simp only [heq x hx r hr hrε,heq x hx (2*r) (by positivity)
      (h2r.trans (min_le_right _ _)),hball r,hball (2*r)]
    exact ⟨((hd x hx).1 r hr hrδ).1,
      ((hd x hx).1 (2*r) (by positivity) (h2r.trans (min_le_left _ _))).2,
      (hd x hx).2 2 r (by norm_num) hr (h2r.trans (min_le_left _ _))⟩
end RothschildStein.G4
