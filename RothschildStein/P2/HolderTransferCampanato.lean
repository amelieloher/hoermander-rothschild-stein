-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderTransferCarrier
public import RothschildStein.H2.Campanato

/-!
# The Campanato estimate and continuity identification

An abstract form of the descent step of BB Prop 11.56 / Thm 11.54 (pp. 597-599): if a function `f`
on `ℝⁿ` is continuous and bounded near a set `S₀` of centres and satisfies the oscillation bound
`inf_c ∫_{B(z, r)} |f - c| ≤ H r^α |B(z, r)|` for all `z ∈ S₀`, `r ≤ 6ρ`, then H2's local Campanato
converse (`DoublingPatch.campanato_theorem`, BB Thm 7.38) on the truncated control metric space
`BaseCarrier D` gives a Hölder representative `f*` on the centre set; since `f` and `f*` are both
continuous on the open set `S₀` and agree a.e., they agree everywhere on `S₀`
(`Measure.eqOn_open_of_ae_eq`), whence the Hölder bound for `f` itself with constant
`4 (c_C + C_D) H` (the pair quantifier is restricted to the centre set, correcting the Campanato argument).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Metric
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2
variable {n k : ℕ} {w : Fin k → ℕ+} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}

namespace BaseCarrier
variable {D : BaseData w X}

theorem val_image_preimage {A : Set (Fin n → ℝ)} (hA : A ⊆ D.N) :
    (val : BaseCarrier D → Fin n → ℝ) '' (val ⁻¹' A) = A := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hz
  · intro hy
    exact ⟨mk y (hA hy), hy, rfl⟩

end BaseCarrier

/-- Change of variables for the restriction of the Lebesgue measure to a measurable set `N`. -/
theorem integral_restrict_image_subtype (N : Set (Fin n → ℝ)) (hN : MeasurableSet N)
    {B : Set ↥N} (hB : MeasurableSet B) (g : (Fin n → ℝ) → ℝ) :
    ∫ y in B, g y.1 ∂(Measure.comap (Subtype.val : ↥N → Fin n → ℝ) volume) =
      ∫ x in Subtype.val '' B, g x := by
  have hemb : MeasurableEmbedding (Subtype.val : ↥N → Fin n → ℝ) :=
    MeasurableEmbedding.subtype_coe hN
  have hT : MeasurableSet ((Subtype.val '' B) : Set (Fin n → ℝ)) :=
    hemb.measurableSet_image.mpr hB
  have hmap : Measure.map (Subtype.val : ↥N → Fin n → ℝ)
      (Measure.comap (Subtype.val : ↥N → Fin n → ℝ) volume) = volume.restrict N :=
    map_comap_subtype_coe hN volume
  have hTN : ((Subtype.val '' B) : Set (Fin n → ℝ)) ⊆ N := by
    rintro _ ⟨z, -, rfl⟩
    exact z.2
  have := hemb.setIntegral_map (μ := Measure.comap (Subtype.val : ↥N → Fin n → ℝ) volume) g
    (Subtype.val '' B)
  rw [hmap, Measure.restrict_restrict hT, inter_eq_left.mpr hTN,
    Set.preimage_image_eq _ Subtype.val_injective] at this
  exact this.symm

namespace BaseCarrier
variable {D : BaseData w X}

/-- Change of variables for the restriction of the Lebesgue measure to `N`. -/
theorem integral_restrict_image {B : Set (BaseCarrier D)} (hB : MeasurableSet B)
    (g : (Fin n → ℝ) → ℝ) :
    ∫ y in B, g y.val ∂(measure D) = ∫ x in val '' B, g x :=
  integral_restrict_image_subtype D.N D.isOpen_N.measurableSet (B := B) hB g

end BaseCarrier

/-- A function with a local Hölder bound on a set is continuous there. -/
theorem continuousOn_of_local_holder {Y : Type*} [PseudoMetricSpace Y] {S : Set Y} {g : Y → ℝ}
    {K α ρ : ℝ} (hK : 0 ≤ K) (hα : 0 < α) (hρ : 0 < ρ)
    (h : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ ρ → |g x - g y| ≤ K * dist x y ^ α) :
    ContinuousOn g S := by
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hK1 : 0 < K + 1 := by linarith
  set ε₂ : ℝ := (ε / (K + 1)) ^ α⁻¹ with hε₂
  have hε₂0 : 0 < ε₂ := Real.rpow_pos_of_pos (div_pos hε hK1) _
  refine ⟨min ρ ε₂, lt_min hρ hε₂0, fun y hy hyd => ?_⟩
  have hd : dist x y < min ρ ε₂ := by rwa [dist_comm]
  have hdρ : dist x y ≤ ρ := hd.le.trans (min_le_left _ _)
  have hdε : dist x y < ε₂ := hd.trans_le (min_le_right _ _)
  have hpow : dist x y ^ α < ε / (K + 1) := by
    calc dist x y ^ α < ε₂ ^ α := Real.rpow_lt_rpow dist_nonneg hdε hα
      _ = ε / (K + 1) := Real.rpow_inv_rpow (div_pos hε hK1).le hα.ne'
  have hnn : 0 ≤ dist x y ^ α := Real.rpow_nonneg dist_nonneg _
  rw [Real.dist_eq, abs_sub_comm]
  calc |g x - g y| ≤ K * dist x y ^ α := h x hx y hy hdρ
    _ ≤ (K + 1) * dist x y ^ α := mul_le_mul_of_nonneg_right (by linarith) hnn
    _ < (K + 1) * (ε / (K + 1)) := mul_lt_mul_of_pos_left hpow hK1
    _ = ε := by field_simp

/-- The Campanato data on the base: everything H2's patch
hypotheses and the oscillation bound ask for, in Euclidean terms. -/
structure CampanatoData (D : BaseData w X) (f : (Fin n → ℝ) → ℝ) (α : ℝ)
    (S₀ W₀ : Set (Fin n → ℝ)) (ρ C_D H : ℝ) : Prop where
  ρ_pos : 0 < ρ
  six_le : 6 * ρ ≤ 1
  one_lt_C_D : 1 < C_D
  H_nonneg : 0 ≤ H
  S_open : IsOpen S₀
  S_sub : S₀ ⊆ W₀
  W_sub : W₀ ⊆ D.N
  W_meas : MeasurableSet W₀
  W_fin : volume W₀ < ⊤
  incl : ∀ z ∈ S₀, ∀ y ∈ D.N, controlDistance D.Ω w X z y < ENNReal.ofReal (6 * ρ) → y ∈ W₀
  ball_sub : ∀ z ∈ S₀, ∀ r : ℝ, 0 < r → r ≤ 6 * ρ → rsBall D.Ω w X z r ⊆ D.N
  doubling : ∀ z ∈ S₀, ∀ r : ℝ, 0 < r → r ≤ 6 * ρ →
    0 < volume (rsBall D.Ω w X z r) ∧ volume (rsBall D.Ω w X z r) < ⊤ ∧
      volume (rsBall D.Ω w X z r) ≤
        ENNReal.ofReal C_D * volume (rsBall D.Ω w X z (r / 2))
  compact : ∃ T : Set (Fin n → ℝ), IsCompact T ∧ T ⊆ D.N ∧ S₀ ⊆ T
  f_cont : ContinuousOn f W₀
  f_bdd : ∃ B : ℝ, ∀ y ∈ W₀, |f y| ≤ B
  osc : ∀ z ∈ S₀, ∀ r : ℝ, 0 < r → r ≤ 6 * ρ → ∃ c : ℝ,
    ∫ y in rsBall D.Ω w X z r, |f y - c| ≤ H * r ^ α * (volume (rsBall D.Ω w X z r)).toReal

namespace CampanatoData
variable {D : BaseData w X} {f : (Fin n → ℝ) → ℝ} {α : ℝ} {S₀ W₀ : Set (Fin n → ℝ)}
  {ρ C_D H : ℝ}

/-- The doubling patch of the Campanato data. -/
def patch (hn : 0 < n) (h : CampanatoData D f α S₀ W₀ ρ C_D H) :
    H2.DoublingPatch (BaseCarrier D) :=
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  { μ := BaseCarrier.measure D
    S := BaseCarrier.val ⁻¹' S₀
    W := BaseCarrier.val ⁻¹' W₀
    ρ := ρ
    C_D := C_D
    ρ_pos := h.ρ_pos
    one_lt_C_D := h.one_lt_C_D
    incl := fun z hz y hy =>
      h.incl z.val hz y.val y.val_mem ((BaseCarrier.mem_ball_iff h.six_le).mp hy)
    doubling := fun z hz r hr hr6 => by
      have hr1 : r ≤ 1 := hr6.trans h.six_le
      have hr2 : r / 2 ≤ 1 := (half_le_self hr.le).trans hr1
      rw [BaseCarrier.measure_ball hr1 (h.ball_sub z.val hz r hr hr6),
        BaseCarrier.measure_ball hr2 (h.ball_sub z.val hz (r / 2) (half_pos hr)
          ((half_le_self hr.le).trans hr6))]
      exact h.doubling z.val hz r hr hr6
    measurable_W := BaseCarrier.measurable_val h.W_meas
    finite_W := by
      rw [BaseCarrier.measure_apply, BaseCarrier.val_image_preimage h.W_sub]
      exact h.W_fin
    compact_closure := by
      obtain ⟨T, hT, hTN, hST⟩ := h.compact
      have hT' : IsCompact (BaseCarrier.val ⁻¹' T : Set (BaseCarrier D)) := by
        have h1 : IsCompact (Subtype.val ⁻¹' T : Set ↥D.N) := by
          rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, Subtype.image_preimage_coe,
            inter_eq_right.mpr hTN]
          exact hT
        exact h1
      exact hT'.of_isClosed_subset isClosed_closure
        (closure_minimal (preimage_mono hST) hT'.isClosed)
    noAtoms := fun x => by
      rw [BaseCarrier.measure_apply]
      have : (BaseCarrier.val '' {x} : Set (Fin n → ℝ)) = {x.val} := image_singleton
      rw [this]
      exact measure_singleton _ }

/-- The Campanato seminorm of the patch is at most the oscillation constant `H`. -/
theorem campanatoSeminorm_le (hn : 0 < n) (h : CampanatoData D f α S₀ W₀ ρ C_D H) :
    H2.campanatoSeminorm α (h.patch hn) (fun x : BaseCarrier D => f x.val) ≤
      ENNReal.ofReal H := by
  unfold H2.campanatoSeminorm
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun r => iSup_le fun hr => ?_
  obtain ⟨hr0, hr6⟩ := hr
  have hxS : x.val ∈ S₀ := hx
  have hr1 : r ≤ 1 := hr6.trans h.six_le
  have hsub := h.ball_sub x.val hxS r hr0 hr6
  obtain ⟨hpos, hfin, -⟩ := h.doubling x.val hxS r hr0 hr6
  obtain ⟨c, hc⟩ := h.osc x.val hxS r hr0 hr6
  have hmeas : (h.patch hn).μ (Metric.ball x r) = volume (rsBall D.Ω w X x.val r) :=
    BaseCarrier.measure_ball hr1 hsub
  have hden : 0 < r ^ α * ((h.patch hn).μ (Metric.ball x r)).toReal := by
    rw [hmeas]
    exact mul_pos (Real.rpow_pos_of_pos hr0 _) (ENNReal.toReal_pos hpos.ne' hfin.ne)
  refine iInf_le_of_le c (ENNReal.ofReal_le_ofReal ?_)
  rw [div_le_iff₀ hden, hmeas]
  have hosc : H2.integralOscillation ((h.patch hn).μ.restrict (Metric.ball x r))
      (fun x : BaseCarrier D => f x.val) c = ∫ y in rsBall D.Ω w X x.val r, |f y - c| := by
    unfold H2.integralOscillation
    rw [← BaseCarrier.image_ball hr1 hsub]
    exact BaseCarrier.integral_restrict_image Metric.isOpen_ball.measurableSet
      (fun y => |f y - c|)
  rw [hosc, ← mul_assoc]
  exact hc

/-- Continuity: `f` is continuous on `W₀`, hence on the open set `S₀`; with the Hölder
representative of H2 these agree. -/
theorem exists_representative (hn : 0 < n) (h : CampanatoData D f α S₀ W₀ ρ C_D H)
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ g : BaseCarrier D → ℝ,
      (∀ᵐ x ∂(BaseCarrier.measure D), x.val ∈ S₀ → g x = f x.val) ∧
      (∀ x : BaseCarrier D, x.val ∈ S₀ → g x = f x.val) ∧
      ∀ x y : BaseCarrier D, x.val ∈ S₀ → y.val ∈ S₀ → dist x y ≤ 3 * ρ →
        |g x - g y| ≤ 4 * ((C_D + 1) / (1 - (1 / 2 : ℝ) ^ α) + C_D) * H * dist x y ^ α := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set P := h.patch hn with hP
  set u : BaseCarrier D → ℝ := fun x => f x.val with hu
  have hSopen : IsOpen (P.S) := h.S_open.preimage BaseCarrier.continuous_val
  have hWmeas : MeasurableSet P.W := P.measurable_W
  have hucont : ContinuousOn u P.W :=
    h.f_cont.comp BaseCarrier.continuous_val.continuousOn (fun x hx => hx)
  obtain ⟨B, hB⟩ := h.f_bdd
  have hint : MeasureTheory.IntegrableOn u P.W P.μ := by
    refine IntegrableOn.of_bound P.finite_W (hucont.aestronglyMeasurable hWmeas) B ?_
    refine (ae_restrict_iff' hWmeas).2 (Eventually.of_forall fun x hx => ?_)
    rw [Real.norm_eq_abs]
    exact hB x.val hx
  have hmem : H2.MemCampanato α P u :=
    ⟨hint, lt_of_le_of_lt (campanatoSeminorm_le hn h) ENNReal.ofReal_lt_top⟩
  obtain ⟨-, hae, hnear, -, -⟩ := P.campanato_theorem hα hα1 hmem
  set g := H2.campanatoRepresentative P α u with hg
  set K₀ : ℝ := 4 * (H2.campanatoTailConstant P α + P.C_D) *
    (H2.campanatoSeminorm α P u).toReal with hK₀
  have hsem : (H2.campanatoSeminorm α P u).toReal ≤ H := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top (campanatoSeminorm_le hn h)
    rwa [ENNReal.toReal_ofReal h.H_nonneg] at this
  have hτ : 0 < H2.campanatoTailConstant P α := H2.campanatoTailConstant_pos P hα
  have hK₀0 : 0 ≤ K₀ := by
    have : 0 < P.C_D := lt_trans zero_lt_one P.one_lt_C_D
    positivity
  have hgcont : ContinuousOn g P.S :=
    continuousOn_of_local_holder (K := K₀) hK₀0 hα (by linarith [P.ρ_pos] : 0 < 3 * P.ρ) hnear
  have hSsub : P.S ⊆ P.W := fun x hx => h.S_sub hx
  have hae' : g =ᵐ[(BaseCarrier.measure D).restrict P.S] u := by
    rw [Filter.EventuallyEq, ae_restrict_iff' hSopen.measurableSet]
    filter_upwards [hae] with x hx hxS using hx hxS
  have heq : EqOn g u P.S :=
    Measure.eqOn_open_of_ae_eq (μ := BaseCarrier.measure D) hae' hSopen hgcont (hucont.mono hSsub)
  refine ⟨g, ?_, fun x hx => heq hx, fun x y hx hy hxy => ?_⟩
  · filter_upwards [hae] with x hx hxS using hx hxS
  · have h1 := hnear x hx y hy hxy
    refine h1.trans ?_
    have hd : 0 ≤ dist x y ^ α := Real.rpow_nonneg dist_nonneg _
    have hpos : 0 ≤ 4 * (H2.campanatoTailConstant P α + P.C_D) := by
      have : 0 < P.C_D := lt_trans zero_lt_one P.one_lt_C_D
      positivity
    refine mul_le_mul_of_nonneg_right ?_ hd
    calc 4 * (H2.campanatoTailConstant P α + P.C_D) * (H2.campanatoSeminorm α P u).toReal
        ≤ 4 * (H2.campanatoTailConstant P α + P.C_D) * H :=
          mul_le_mul_of_nonneg_left hsem hpos
      _ = _ := rfl

/-- The Hölder bound for `f` itself on
the centre set: for `x, y ∈ S₀` with `d(x, y) ≤ 3 ρ`,
`|f x - f y| ≤ 4 (c_C + C_D) H d(x, y)^α` with `c_C = (C_D + 1) / (1 - 2^{-α})`
(BB Thm 7.38 through the representative `f*`, which equals `f` on `S₀`). -/
theorem holder_bound (hn : 0 < n) (h : CampanatoData D f α S₀ W₀ ρ C_D H) (hα : 0 < α)
    (hα1 : α < 1) :
    ∀ x ∈ S₀, ∀ y ∈ S₀, controlDistance D.Ω w X x y ≤ ENNReal.ofReal (3 * ρ) →
      |f x - f y| ≤ 4 * ((C_D + 1) / (1 - (1 / 2 : ℝ) ^ α) + C_D) * H *
        (controlDistance D.Ω w X x y).toReal ^ α := by
  intro x hx y hy hxy
  obtain ⟨g, -, hg, hnear⟩ := h.exists_representative hn hα hα1
  have h3 : 3 * ρ ≤ 1 := by linarith [h.six_le, h.ρ_pos]
  have hx' : x ∈ D.N := h.W_sub (h.S_sub hx)
  have hy' : y ∈ D.N := h.W_sub (h.S_sub hy)
  have hmin : min 1 (controlDistance D.Ω w X x y) = controlDistance D.Ω w X x y :=
    min_eq_right (hxy.trans (ENNReal.ofReal_le_one.mpr h3))
  have hdist : dist (BaseCarrier.mk x hx' : BaseCarrier D) (BaseCarrier.mk y hy') =
      (controlDistance D.Ω w X x y).toReal := by
    rw [BaseCarrier.dist_eq]
    exact congrArg ENNReal.toReal hmin
  have hdle : dist (BaseCarrier.mk x hx' : BaseCarrier D) (BaseCarrier.mk y hy') ≤ 3 * ρ := by
    rw [hdist]
    exact ENNReal.toReal_le_of_le_ofReal (by linarith [h.ρ_pos]) hxy
  have := hnear (BaseCarrier.mk x hx') (BaseCarrier.mk y hy') hx hy hdle
  rw [hg (BaseCarrier.mk x hx') hx, hg (BaseCarrier.mk y hy') hy, hdist] at this
  exact this

end CampanatoData

end RothschildStein.P2
