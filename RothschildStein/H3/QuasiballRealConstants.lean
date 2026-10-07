-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballStepConstants
public import RothschildStein.H3.WeakHorizontalNorms
public import RothschildStein.H3.CutoffStepToReal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- The real one-step estimate preserves the fixed cutoff constants across all exponents. -/
theorem quasiball_real_step_with_constants {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G)
    (c₁ c₂ : ℝ)
    (hcut : ∀ x₀ : Fin n → ℝ, ∀ t s : ℝ, 0 < t → t < s → s/2 ≤ t →
      ∃ φ : TestFunction (quasiballDomain G ν x₀ s) ℝ (⊤ : ℕ∞),
        EqOn φ 1 (G2.gaugeBall G ν x₀ t) ∧ eLpNorm φ ⊤ volume ≤ 1 ∧
        (∀ i : Fin q, eLpNorm (fieldDerivative (H.fields i.succ) φ) ⊤ volume ≤
          ENNReal.ofReal (c₁/(s-t))) ∧
        (∀ i j : Fin q, eLpNorm (fieldDerivative (H.fields i.succ)
          (fieldDerivative (H.fields j.succ) φ)) ⊤ volume ≤
          ENNReal.ofReal (c₂/(s-t)^2)))
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (E : Fin q → ℝ → (Fin n → ℝ))
    (hE : ∀ i, Continuous (E i)) (hE0 : ∀ i, E i 0 = 0)
    (hflow : ∀ i x, IsIntegralCurve (fun t => G.mul x (E i t)) (fun _ => H.fields i.succ))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hdensity : ∀ u, memSobolevX driftWeight H.fields ⊤ 2 p u →
      Nonempty (SobolevWordApproximation driftWeight H.fields p u)) :
      ∀ x₀ : Fin n → ℝ, ∀ r : ℝ, 0 < r →
      ∀ u : (Fin n → ℝ) → ℝ,
        memSobolevX driftWeight H.fields (quasiballDomain G ν x₀ r) 2 p u →
      ∀ σ ∈ Ioo (1/2 : ℝ) 1, ∀ ε : ℝ, 0 < ε →
        (horizontalWeakENorm H.fields (quasiballDomain G ν x₀ (σ*r)) p u).toReal ≤
        ε*((horizontalSquareWeakENorm H.fields
            (quasiballDomain G ν x₀ (((1+σ)/2)*r)) p u).toReal +
          (4*c₁/((1-σ)*r))*(horizontalWeakENorm H.fields
            (quasiballDomain G ν x₀ (((1+σ)/2)*r)) p u).toReal +
          (4*(q : ℝ)*c₂/(((1-σ)*r)^2))*
            (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (((1+σ)/2)*r)))).toReal) +
        (2*(q : ℝ)/ε)*
          (eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ (((1+σ)/2)*r)))).toReal := by
  have hstep := quasiball_interpolation_step_with_constants G H ν c₁ c₂ hcut
    E hE hE0 hflow hp hpt hdensity
  intro x₀ r hr u hu σ hσ ε hε
  let t := σ*r
  let s := ((1+σ)/2)*r
  have hσ0 : 0 < σ := lt_trans (by norm_num) hσ.1
  have ht : 0 < t := mul_pos hσ0 hr
  have hts : t < s := by dsimp [t,s]; nlinarith [hσ.2]
  have hhalf : s/2 ≤ t := by dsimp [t,s]; nlinarith [hσ.1]
  have hsr : s ≤ r := by dsimp [s]; nlinarith [hσ.2]
  have hsub : (quasiballDomain G ν x₀ s : Set (Fin n → ℝ)) ⊆
      quasiballDomain G ν x₀ r := by
    intro x hx
    change G2.gaugeDistance G ν x x₀ < s at hx
    change G2.gaugeDistance G ν x x₀ < r
    exact hx.trans_le hsr
  have hus := S.memSobolevX_restrict driftWeight H.fields _ _ hsub hu
  have hb := hstep x₀ t s ht hts hhalf u hus ε hε
  have hU := hus.1.eLpNorm_lt_top.ne
  have hV := (horizontalWeakENorm_lt_top H.fields _ p u hus).ne
  have hW := (horizontalSquareWeakENorm_lt_top H.fields _ p u hus).ne
  have hgap : 0 < s-t := sub_pos.mpr hts
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg q
  have hb' : horizontalWeakENorm H.fields (quasiballDomain G ν x₀ t) p u ≤
      ENNReal.ofReal (2*(q : ℝ)/ε)*eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ s)) +
      ENNReal.ofReal (ε/2)*(horizontalSquareWeakENorm H.fields (quasiballDomain G ν x₀ s) p u +
        2*ENNReal.ofReal (c₁/(s-t))*horizontalWeakENorm H.fields (quasiballDomain G ν x₀ s) p u +
        ENNReal.ofReal (q : ℝ)*ENNReal.ofReal (c₂/(s-t)^2)*
          eLpNorm u p (volume.restrict (G2.gaugeBall G ν x₀ s))) := by
    simpa only [horizontalWeakENorm,horizontalSquareWeakENorm,ENNReal.ofReal_natCast] using hb
  have hh := cutoff_step_toReal hU hV hW hε
    (by positivity : 0 ≤ c₁/(s-t)) (by positivity : 0 ≤ c₂/(s-t)^2) hq hb'
  have hg : s-t = ((1-σ)*r)/2 := by dsimp [s,t]; ring
  have hd : (1-σ)*r ≠ 0 := ne_of_gt (mul_pos (sub_pos.mpr hσ.2) hr)
  have hA : 2*(c₁/(s-t)) = 4*c₁/((1-σ)*r) := by rw [hg]; field_simp [hd]; ring
  have hB : (q : ℝ)*(c₂/(s-t)^2) = 4*(q : ℝ)*c₂/(((1-σ)*r)^2) := by
    rw [hg]
    field_simp [hd]
    ring
  simpa only [hA,hB,t,s,mul_assoc,quasiballDomain,Opens.coe_mk] using hh

end RothschildStein.H3
