-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualSuboptimalTransferChain
public import RothschildStein.G4.ActualZeroShiftInjectivityChain
public import RothschildStein.G4.AuxiliaryShiftInjectivity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Function

namespace RothschildStein.G4

/-- One actual injective reference frame gives one uniform positive
injective-box radius for every suboptimal frame at a smaller requested
scale, including small auxiliary shifts. The constant precedes the fields
and charts. All chart packages use their original radius, and every frame
chain has bounded length (BB pp. 453–458). -/
theorem exists_uniform_injectivity_from_reference_frame {m n s : ℕ} {α a D : ℝ}
    (hα : 0 < α) (hα1 : α ≤ 1) (ha : 0 < a) (ha1 : a ≤ 1) (hD : 0 ≤ D) :
    ∃ c : ℝ, 0 < c ∧ c ≤ a ∧
      ∀ (w : Fin m → ℕ+) (_hw : ∀ J, (w J : ℕ) ≤ s)
        (Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (Ω : Set (Fin n → ℝ)),
        (∀ J, ContinuousOn (Z J) Ω) →
      ∀ (F : (Fin n → Fin m) → (Fin m → ℝ) → (Fin n → ℝ) → (Fin n → ℝ))
        (Γ : (Fin n → Fin m) → (Fin m → ℝ) → (Fin n → ℝ) → ℝ → (Fin n → ℝ))
        (x : Fin n → ℝ) (κ t : ℝ),
        0 ≤ κ → (n : ℝ) * κ ≤ 1 / 4 → 0 ≤ t → t ≤ 1 →
        (∀ B r, 0 < r → r ≤ 1 → IsSuboptimal Z w B x t r →
          ∀ v ∈ weightedBox w (a * r),
          ChartAnalyticBounds Ω w Z B (F B v) (weightedBox (w ∘ B) (a * r)) r κ D ∧
          ChartTrajectories Ω Z B (F B v) (weightedBox (w ∘ B) (a * r)) x v (Γ B v) ∧
          (v = 0 → F B v 0 = x)) →
      ∀ (R : ℝ) (B₀ : Fin n → Fin m), 0 < R → R ≤ 1 →
        IsSuboptimal Z w B₀ x t R → InjOn (F B₀ 0) (weightedBox (w ∘ B₀) (α * R)) →
      ∀ (r : ℝ) (B : Fin n → Fin m), 0 < r → r ≤ R →
        IsSuboptimal Z w B x t r →
      ∀ v ∈ weightedBox w (c * r), InjOn (F B v) (weightedBox (w ∘ B) (c * r)) := by
  obtain ⟨f, hf⟩ := exists_uniform_chart_transfer_shrinkage (m := m) (n := n) (s := s) ha ha1 hD
  have hfunit : ∀ b : ℝ, 0 < b → b ≤ 1 → 0 < f b ∧ f b ≤ 1 :=
    fun b hb hb1 => ⟨(hf b hb hb1).1, (hf b hb hb1).2.1⟩
  obtain ⟨d, hd, _hd1, hfloor⟩ := exists_positive_finite_transfer_radius f hα hα1 hfunit (m ^ n)
  let c := min d (a / 2)
  have hc : 0 < c := lt_min hd (half_pos ha)
  have hcd : c ≤ d := min_le_left _ _
  have hca : c ≤ a := (min_le_right _ _).trans (by linarith)
  refine ⟨c, hc, hca, ?_⟩
  intro w hw Z Ω hZ F Γ x κ t hκ hsmall ht ht1 hdata R B₀ hR hR1 hsub₀ hinj₀
    r B hr hrR hsub v hv
  have hzero : ∀ q : ℝ, 0 < q → (0 : Fin m → ℝ) ∈ weightedBox w (a * q) := by
    intro q hq J
    simp only [Pi.zero_apply, abs_zero]
    exact pow_pos (mul_pos ha hq) _
  have hdataZero : ∀ C q, 0 < q → q ≤ 1 → IsSuboptimal Z w C x t q →
      ChartAnalyticBounds Ω w Z C (F C 0) (weightedBox (w ∘ C) (a * q)) q κ D ∧
      ChartTrajectories Ω Z C (F C 0) (weightedBox (w ∘ C) (a * q)) x 0 (Γ C 0) ∧
      F C 0 0 = x := by
    intro C q hq hq1 hC
    obtain ⟨hG, hΓG, hGzero⟩ := hdata C q hq hq1 hC 0 (hzero q hq)
    exact ⟨hG, hΓG, hGzero rfl⟩
  obtain ⟨hG₀, _hΓ₀, hG₀zero⟩ := hdataZero B₀ R hR hR1 hsub₀
  have hu₀ : (0 : Fin n → ℝ) ∈ weightedBox (w ∘ B₀) (a * R) := by
    intro i
    simp only [Pi.zero_apply, abs_zero]
    exact pow_pos (mul_pos ha hR) _
  have hdet₀ : frameDet Z B₀ x ≠ 0 := by
    simpa only [hG₀zero] using hG₀.2.2.2.1 0 hu₀
  let S := fun C : Fin n → Fin m => Icc r R ∩ {q : ℝ | IsSuboptimal Z w C x t q}
  obtain ⟨l, hchain, hhead, hlast, hmembers, htargetInf, _hfirst, _hnodup, hlength⟩ :=
    exists_actual_suboptimal_transfer_chain Z w x ht ht1 hr hrR ⟨B₀, hdet₀⟩ B₀ B hsub₀ hsub
  have hlengthBound : l.length ≤ m ^ n := by simpa only [Fintype.card_fin] using hlength
  have hlne : l ≠ [] := by intro he; subst l; simp at hhead
  have hlen : 0 < l.length := List.length_pos_iff.mpr hlne
  have hfirstIndex : l[0] = B₀ := by
    cases l with
    | nil => simp at hhead
    | cons C tail => simpa using hhead
  have hB₀mem : B₀ ∈ l := hfirstIndex ▸ List.getElem_mem hlen
  have hstart : ∀ h : 0 < l.length,
      InjOn (F l[0] 0) (weightedBox (w ∘ l[0]) (α * sInf (S l[0]))) := by
    intro _
    rw [hfirstIndex]
    apply hinj₀.mono
    exact weightedBox_subset_of_radius_le _
      (mul_nonneg hα.le (hr.le.trans (hmembers B₀ hB₀mem).1.1))
      (mul_le_mul_of_nonneg_left (hmembers B₀ hB₀mem).1.2 hα.le)
  have hiterChart := actual_zero_shift_chart_injectivity_along_chain w hw Z Ω hZ
    (fun C => F C 0) (fun C => Γ C 0) x (fun C => sInf (S C)) ha hκ hsmall
    f hf hα hα1 hdataZero l hchain
    (fun C hC => ⟨hr.trans_le (hmembers C hC).1.1, (hmembers C hC).1.2.trans hR1⟩) hstart
  let j := l.length - 1
  have hj : j < l.length := Nat.sub_lt hlen zero_lt_one
  have hlastIndex : l[j] = B := by
    have hvLast : l.getLast hlne = B := Option.some.inj
      ((List.getLast?_eq_getLast_of_ne_nil hlne).symm.trans hlast)
    simpa only [List.getLast_eq_getElem] using hvLast
  have hinj := hiterChart j hj
  change InjOn (F l[j] 0) (weightedBox (w ∘ l[j]) (f^[j] α * sInf (S l[j]))) at hinj
  rw [hlastIndex, htargetInf] at hinj
  have hi := transfer_radius_iterates_positive f hα hα1 hfunit j
  have hjNext : j + 1 = l.length := Nat.sub_add_cancel (Nat.succ_le_of_lt hlen)
  have hcfNext : c ≤ f (f^[j] α) := by
    have he := hcd.trans (hfloor (j + 1) (by rw [hjNext]; exact hlengthBound))
    simpa only [Function.iterate_succ_apply'] using he
  have hvTarget : v ∈ weightedBox w (a * r) :=
    weightedBox_subset_of_radius_le w (mul_nonneg hc.le hr.le)
      (mul_le_mul_of_nonneg_right hca hr.le) hv
  have hvTransfer : v ∈ weightedBox w (f (f^[j] α) * r) :=
    weightedBox_subset_of_radius_le w (mul_nonneg hc.le hr.le)
      (mul_le_mul_of_nonneg_right hcfNext hr.le) hv
  obtain ⟨hF, hΓF, _hFzero⟩ := hdata B r hr (hrR.trans hR1) hsub v hvTarget
  obtain ⟨hG, hΓG, hGzero⟩ := hdataZero B r hr (hrR.trans hR1) hsub
  have hshift := auxiliary_shift_chart_injective_of_zero_shift ha (hf _ hi.1 hi.2).2.2
    w B (fun i => hw (B i)) Z Ω hZ (F B v) (F B 0) hr (hrR.trans hR1) hκ hsmall
    hF hG hinj x hGzero v hvTransfer (Γ B v) (Γ B 0) hΓF hΓG
  exact hshift.mono (weightedBox_subset_of_radius_le _ (mul_nonneg hc.le hr.le)
    (mul_le_mul_of_nonneg_right hcfNext hr.le))

end RothschildStein.G4
