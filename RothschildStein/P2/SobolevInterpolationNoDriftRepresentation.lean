-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationNoDriftCompact
public import RothschildStein.P2.SobolevInterpolationRepresentation
public import RothschildStein.P1.RepresentationNoDriftFirstOrder
public import RothschildStein.P1.ContinuityTheorem
public import RothschildStein.P1.StandardFrame

/-!
# Sobolev interpolation without drift, compact form: the interpolation inequality from the representation

Part of the Sobolev interpolation inequality (BB Prop 11.38, p. 580, (11.64)-(11.67)), without drift: there are `ε_* > 0` and, for `1 < p < ∞`,
`C(p)` with `∑_l ‖X̃_l v‖_p ≤ ε ‖L̃v‖_p + C ε^{-1} ‖v‖_p` for every `v ∈ C_c^∞(V)` on whose support the
cutoff `a` of the representation is `1` (in particular for `v ∈ C_c^∞(B̃(ξ₀, r₁))` when `a = 1` on
`B̃(ξ₀, r₁)`), `0 < ε < ε_*`, `L̃ = sumSquares`. The statement is conditional exactly on the hypotheses
of `representation_firstOrder_noDrift_of` (`LeftDifferentiation`, `SignedParametrixNoDrift` and the density data `c`),
on a standard frame (as in the continuity theorem) of a lifted no-drift chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

variable {n q s m : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- **The compact interpolation inequality, no drift** (BB Prop 11.38). Let `C` be a
lifted no-drift chart and `F` a standard frame of it, `a ∈ C_c^∞(V)` a cutoff for which the first-order
first-order representation holds (hypotheses `LeftDifferentiation`, `SignedParametrixNoDrift`, as in
`representation_firstOrder_noDrift_of`). There are `ε_* > 0` and, for each `1 < p < ∞`, a constant `C(p)` such
that for `0 < ε < ε_*` and every `v ∈ C_c^∞(V)` with `a = 1` on `supp v`
`∑_{l=1}^q ‖X̃_l v‖_{L^p(V)} ≤ ε ‖L̃ v‖_{L^p(V)} + C(p) ε^{-1} ‖v‖_{L^p(V)}`. -/
theorem exists_compactInterpolation_noDrift_of_representation
    {q₀ : ℕ} {H : H1.StandingHypotheses C.G q₀} {K : H1.FundamentalKernel C.G H}
    {hQ : 2 < (C.G.homogeneousDimension : ℝ)} (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) (hLeftDiff : LeftDifferentiation F w C.Xl)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b) :
    ∃ εs : ℝ, 0 < εs ∧ ∀ p : ℝ, 1 < p → ∃ Cp : ℝ, 0 < Cp ∧ ∀ ε : ℝ, 0 < ε → ε < εs →
      ∀ v : TestFunction F.V ℝ (⊤ : ℕ∞),
        (∀ x ∈ tsupport (v : (Fin (n + m) → ℝ) → ℝ), a x = 1) →
        ∑ l : Fin q, eLpNorm (fieldDerivative (C.Xl l) (v : (Fin (n + m) → ℝ) → ℝ))
            (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
          ENNReal.ofReal ε * eLpNorm (sumSquares C.Xl (v : (Fin (n + m) → ℝ) → ℝ))
              (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
            ENNReal.ofReal (Cp / ε) * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
              (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
  have hXV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.contDiffOn_Xl_U i).mono hF.lifted.subset_U
  obtain ⟨Fl, Sl, -, hrep⟩ := representation_firstOrder_noDrift_of hXV hw hLeftDiff hc hc0 a hParametrix
  obtain ⟨ν, hν⟩ := exists_smooth_homogeneous_norm C.G
  -- the near/far constants of the type-1 operators `F_l`
  choose ε₀ Cn Kf hε₀ hε₀1 hCn hKf hF1 using fun l : Fin q =>
    exists_eLpNorm_apply_le_noDrift hF.lifted hw (Fl l) ν hν
  obtain ⟨δ, hδ, hδl⟩ := exists_pos_le_forall_fin ε₀ hε₀
  set εs : ℝ := min δ 1 with hεs
  have hεs0 : 0 < εs := lt_min hδ one_pos
  refine ⟨εs, hεs0, fun p hp => ?_⟩
  have hP1 : 1 < ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hp
  have hPtop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  -- the `L^p` bounds of the type-0 operators `S_l`
  choose Λ hΛ0 hΛ using fun l : Fin q =>
    (Sl l).exists_lp_bound_standard hF hP1 hPtop
  set CN : ℝ := ∑ l, Cn l with hCN
  set CK : ℝ := ∑ l, Kf l + ∑ l, Λ l with hCK
  have hCN0 : 0 ≤ CN := Finset.sum_nonneg (fun l _ => (hCn l).le)
  have hCK0 : 0 ≤ CK :=
    add_nonneg (Finset.sum_nonneg (fun l _ => (hKf l).le)) (Finset.sum_nonneg (fun l _ => (hΛ0 l).le))
  have hCn_le : ∀ l, Cn l ≤ CN := fun l =>
    Finset.single_le_sum (f := Cn) (fun l _ => (hCn l).le) (Finset.mem_univ l)
  have hKf_le : ∀ l, Kf l + Λ l ≤ CK := by
    intro l
    have h1 : Kf l ≤ ∑ l, Kf l :=
      Finset.single_le_sum (f := Kf) (fun l _ => (hKf l).le) (Finset.mem_univ l)
    have h2 : Λ l ≤ ∑ l, Λ l :=
      Finset.single_le_sum (f := Λ) (fun l _ => (hΛ0 l).le) (Finset.mem_univ l)
    linarith
  -- the constant after rescaling `ε ↦ ε / (q CN + 1)`
  set R : ℝ := q * CN + 1 with hR
  have hR0 : 0 < R := by positivity
  refine ⟨q * CK * R + 1, by positivity, fun ε hε hεr v hv => ?_⟩
  set ε' : ℝ := ε / R with hε'
  have hε'0 : 0 < ε' := div_pos hε hR0
  have hR1 : 1 ≤ R := by
    have : 0 ≤ (q : ℝ) * CN := by positivity
    linarith
  have hε'ε : ε' ≤ ε := div_le_self hε.le hR1
  have hε'lt : ∀ l, ε' < ε₀ l := fun l =>
    lt_of_le_of_lt hε'ε (lt_of_lt_of_le hεr ((min_le_left _ _).trans (hδl l)))
  have hε'1 : ε' ≤ 1 := hε'ε.trans (hεr.le.trans (min_le_right _ _))
  set G : (Fin (n + m) → ℝ) → ℝ := sumSquares C.Xl (v : (Fin (n + m) → ℝ) → ℝ) with hG
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := hP1.le
  have hper : ∀ l : Fin q, eLpNorm (fieldDerivative (C.Xl l) (v : (Fin (n + m) → ℝ) → ℝ))
      (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
      ENNReal.ofReal (CN * ε') * eLpNorm G (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
        ENNReal.ofReal (CK / ε') * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
    intro l
    have hw1 := hrep l v
    rw [mul_eq_self_of_eq_one_on_tsupport a v hv] at hw1
    have hcl := S.hasWeakWordDeriv_classical F.V C.Xl hXV [l] (v : (Fin (n + m) → ℝ) → ℝ)
      v.contDiff.contDiffOn
    have hae := S.hasWeakWordDeriv_unique C.Xl F.V hcl hw1
    obtain ⟨hmeasF, hFb⟩ := hF1 l ε' hε'0 (hε'lt l) p hp.le v
    obtain ⟨hSmem, hSb⟩ := hΛ l v
    calc eLpNorm (fieldDerivative (C.Xl l) (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))
        = eLpNorm (fun ξ => (Fl l).apply G ξ + (Sl l).apply (v : (Fin (n + m) → ℝ) → ℝ) ξ)
            (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
          eLpNorm_congr_ae hae
      _ ≤ eLpNorm ((Fl l).apply G) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
          eLpNorm ((Sl l).apply (v : (Fin (n + m) → ℝ) → ℝ)) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
          eLpNorm_add_le hp1
      _ ≤ (ENNReal.ofReal (Cn l * ε') * eLpNorm G (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
          ENNReal.ofReal (Kf l / ε') * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) +
          ENNReal.ofReal (Λ l) * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
            (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := add_le_add hFb hSb
      _ ≤ _ := by
          have e1 : ENNReal.ofReal (Cn l * ε') ≤ ENNReal.ofReal (CN * ε') :=
            ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hCn_le l) hε'0.le)
          have e2 : ENNReal.ofReal (Kf l / ε') * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ)
                (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
              ENNReal.ofReal (Λ l) * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
                (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) ≤
              ENNReal.ofReal (CK / ε') * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ)
                (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
            rw [← add_mul, ← ENNReal.ofReal_add (div_nonneg (hKf l).le hε'0.le) (hΛ0 l).le]
            refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
            have h3 : Λ l ≤ Λ l / ε' := by
              rw [le_div_iff₀ hε'0]
              nlinarith [(hΛ0 l)]
            calc Kf l / ε' + Λ l ≤ Kf l / ε' + Λ l / ε' := by linarith
              _ = (Kf l + Λ l) / ε' := by ring
              _ ≤ CK / ε' := div_le_div_of_nonneg_right (hKf_le l) hε'0.le
          calc (ENNReal.ofReal (Cn l * ε') * eLpNorm G (ENNReal.ofReal p)
                (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
              ENNReal.ofReal (Kf l / ε') * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
                (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) +
              ENNReal.ofReal (Λ l) * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
                (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))
              = ENNReal.ofReal (Cn l * ε') * eLpNorm G (ENNReal.ofReal p)
                (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
              (ENNReal.ofReal (Kf l / ε') * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
                (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
              ENNReal.ofReal (Λ l) * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
                (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) := add_assoc _ _ _
            _ ≤ _ := add_le_add (mul_le_mul' e1 le_rfl) e2
  calc ∑ l : Fin q, eLpNorm (fieldDerivative (C.Xl l) (v : (Fin (n + m) → ℝ) → ℝ))
        (ENNReal.ofReal p) (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))
      ≤ ∑ _l : Fin q, (ENNReal.ofReal (CN * ε') * eLpNorm G (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
        ENNReal.ofReal (CK / ε') * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) := Finset.sum_le_sum fun l _ => hper l
    _ = (q : ℝ≥0∞) * (ENNReal.ofReal (CN * ε') * eLpNorm G (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) +
        ENNReal.ofReal (CK / ε') * eLpNorm (v : (Fin (n + m) → ℝ) → ℝ) (ENNReal.ofReal p)
          (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ _ := by
        rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_natCast q,
          ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        refine add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
          (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
        · -- `q CN ε' ≤ ε`
          have : (q : ℝ) * (CN * ε') = (q * CN) * ε / R := by rw [hε']; ring
          rw [this, div_le_iff₀ hR0, hR]
          nlinarith [mul_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ q) hCN0, hε]
        · -- `q CK / ε' ≤ (q CK R + 1) / ε`
          have : (q : ℝ) * (CK / ε') = q * CK * R / ε := by rw [hε']; field_simp
          rw [this]
          exact div_le_div_of_nonneg_right (by linarith) hε.le

end RothschildStein.P2
