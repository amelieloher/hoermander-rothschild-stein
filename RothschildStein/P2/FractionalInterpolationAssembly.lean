-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.FractionalInterpolationRegular

/-!
# Hölder interpolation: assembly over the principal terms and choice of the scale

A finite sum of principal-term bounds (`principal_list_interpolation`, induction over the list of
principal terms of the type decomposition), the regular remainder (`regular_interpolation`) and the
choice of the scale `h = h(ε)` (`exists_scale`) give the first Hölder interpolation inequality for every
type-`λ` operator of positive type.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- **Finite sums of principal terms**: for every finite list of principal terms of degree
`≤ 1` the sum of the principal-term operators applied to `L̃ v` satisfies the bound of
`principal_interpolation` with summed constants. -/
theorem principal_list_interpolation (hF : C.IsLiftedFrame F) (hw : ∀ i, (w i : ℕ) ≤ 2)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hvar : LiftedVariation C Cg) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {Lop : ((Fin (n + m) → ℝ) → ℝ) → (Fin (n + m) → ℝ) → ℝ} (hL : IsCoordinateOp C Lop) :
    ∀ l : List (PrincipalTerm F), (∀ t ∈ l, t.degree ≤ 1) →
      ∃ (Cn h₀ Cfar : ℝ) (M : ℕ), 0 < Cn ∧ 0 < h₀ ∧ h₀ ≤ 1 ∧ 0 ≤ Cfar ∧
        ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ v : (Fin (n + m) → ℝ) → ℝ, ContDiffOn ℝ 2 v C.O →
          ∀ Mg Mv : ℝ, 0 ≤ Mg → 0 ≤ Mv →
          (∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |Lop v y| ≤ Mg) →
          (∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |v y| ≤ Mv) →
          (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)),
            |(l.map (fun t => ∫ η, t.kernel x η * Lop v η)).sum| ≤
              Cn * h ^ (1 - α) * Mg + Cfar * (h⁻¹) ^ M * Mv) ∧
          (∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)),
            |(l.map (fun t => ∫ η, t.kernel x η * Lop v η)).sum -
                (l.map (fun t => ∫ η, t.kernel y η * Lop v η)).sum| ≤
              (Cn * h ^ (1 - α) * Mg + Cfar * (h⁻¹) ^ M * Mv) * (C.dl x y).toReal ^ α) := by
  intro l
  induction l with
  | nil =>
    intro _
    refine ⟨1, 1, 0, 0, one_pos, one_pos, le_rfl, le_rfl, fun h hh _ v _ Mg Mv hMg0 hMv0 _ _ => ?_⟩
    have hd : 0 ≤ (1 : ℝ) * h ^ (1 - α) * Mg + 0 * (h⁻¹) ^ 0 * Mv := by
      have : 0 ≤ h ^ (1 - α) := Real.rpow_nonneg hh.le _
      positivity
    exact ⟨fun x _ => by simpa using hd, fun x _ y _ => by
      simp only [List.map_nil, List.sum_nil, sub_self, abs_zero]
      exact mul_nonneg hd (Real.rpow_nonneg ENNReal.toReal_nonneg _)⟩
  | cons t l ih =>
    intro hl
    obtain ⟨Cn₁, h₁, Cf₁, M₁, hCn₁, hh₁, hh₁1, hCf₁, hP⟩ :=
      principal_interpolation hF hw ν hν t (hl t (List.mem_cons_self ..)) hCg hvar hα0 hα1 hL
    obtain ⟨Cn₂, h₂, Cf₂, M₂, hCn₂, hh₂, hh₂1, hCf₂, hQ⟩ :=
      ih (fun s hs => hl s (List.mem_cons_of_mem _ hs))
    refine ⟨Cn₁ + Cn₂, min h₁ h₂, Cf₁ + Cf₂, max M₁ M₂, by positivity, lt_min hh₁ hh₂,
      (min_le_left _ _).trans hh₁1, by positivity, fun h hh hhm v hv Mg Mv hMg0 hMv0 hMg hMv => ?_⟩
    have hx : 1 ≤ h⁻¹ := (one_le_inv₀ hh).mpr (hhm.trans ((min_le_left _ _).trans hh₁1))
    obtain ⟨hP1, hP2⟩ := hP h hh (hhm.trans (min_le_left _ _)) v hv Mg Mv hMg0 hMv0 hMg hMv
    obtain ⟨hQ1, hQ2⟩ := hQ h hh (hhm.trans (min_le_right _ _)) v hv Mg Mv hMg0 hMv0 hMg hMv
    have e1 : (h⁻¹) ^ M₁ ≤ (h⁻¹) ^ max M₁ M₂ := pow_le_pow_right₀ hx (le_max_left _ _)
    have e2 : (h⁻¹) ^ M₂ ≤ (h⁻¹) ^ max M₁ M₂ := pow_le_pow_right₀ hx (le_max_right _ _)
    have hhα : 0 ≤ h ^ (1 - α) := Real.rpow_nonneg hh.le _
    have hcomb : Cn₁ * h ^ (1 - α) * Mg + Cf₁ * (h⁻¹) ^ M₁ * Mv +
        (Cn₂ * h ^ (1 - α) * Mg + Cf₂ * (h⁻¹) ^ M₂ * Mv) ≤
        (Cn₁ + Cn₂) * h ^ (1 - α) * Mg + (Cf₁ + Cf₂) * (h⁻¹) ^ max M₁ M₂ * Mv := by
      have a1 : Cf₁ * (h⁻¹) ^ M₁ * Mv ≤ Cf₁ * (h⁻¹) ^ max M₁ M₂ * Mv :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e1 hCf₁) hMv0
      have a2 : Cf₂ * (h⁻¹) ^ M₂ * Mv ≤ Cf₂ * (h⁻¹) ^ max M₁ M₂ * Mv :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 hCf₂) hMv0
      nlinarith
    refine ⟨fun x hx' => ?_, fun x hx' y hy' => ?_⟩
    · simp only [List.map_cons, List.sum_cons]
      refine (abs_add_le _ _).trans ?_
      linarith [hP1 x hx', hQ1 x hx']
    · simp only [List.map_cons, List.sum_cons]
      have hd0 : 0 ≤ (C.dl x y).toReal ^ α := Real.rpow_nonneg ENNReal.toReal_nonneg _
      have e : ∀ a b a' b' : ℝ, a + b - (a' + b') = (a - a') + (b - b') := fun a b a' b' => by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have h1 := hP2 x hx' y hy'
      have h2 := hQ2 x hx' y hy'
      have h3 := mul_le_mul_of_nonneg_right hcomb hd0
      nlinarith

/-- **Choice of the scale `h = h(ε)`** (BB p. 595: "`h = (ε/(2C))^{1/η}`", larger `ε` at a
fixed small scale): for `0 < ε < 1` there is `h ≤ h₀` with `2 Cn h^{1-α} ≤ ε` and
`2 (Cfar h^{-M} + Cr) ≤ Cc ε^{-γ}`, `γ > 1`. -/
theorem exists_scale {Cn h₀ Cfar Cr α : ℝ} (M : ℕ) (hCn : 0 < Cn) (hh₀ : 0 < h₀)
    (hCfar : 0 ≤ Cfar) (hCr : 0 ≤ Cr) (hα1 : α < 1) :
    ∃ γ Cc : ℝ, 1 < γ ∧ 0 < Cc ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ h : ℝ, 0 < h ∧ h ≤ h₀ ∧
      2 * (Cn * h ^ (1 - α)) ≤ ε ∧ 2 * (Cfar * (h⁻¹) ^ M + Cr) ≤ Cc * ε ^ (-γ) := by
  set a : ℝ := 1 - α with ha
  have ha0 : 0 < a := by linarith
  set κ : ℝ := ((2 * Cn)⁻¹) ^ (1 / a) with hκ
  have hκ0 : 0 < κ := Real.rpow_pos_of_pos (inv_pos.mpr (by positivity)) _
  set c₁ : ℝ := min h₀ κ with hc₁
  have hc₁0 : 0 < c₁ := lt_min hh₀ hκ0
  refine ⟨(M : ℝ) / a + 2, 2 * Cfar * (c₁⁻¹) ^ M + 2 * Cr + 1, by
    have : 0 ≤ (M : ℝ) / a := by positivity
    linarith, by positivity, fun ε hε0 hε1 => ?_⟩
  set e : ℝ := ε ^ (1 / a) with he
  have he0 : 0 < e := Real.rpow_pos_of_pos hε0 _
  have he1 : e ≤ 1 := Real.rpow_le_one hε0.le hε1.le (by positivity)
  refine ⟨min h₀ (κ * e), lt_min hh₀ (mul_pos hκ0 he0), min_le_left _ _, ?_, ?_⟩
  · -- `2 Cn h^a ≤ ε`
    have h1 : (min h₀ (κ * e)) ^ a ≤ (κ * e) ^ a :=
      Real.rpow_le_rpow (lt_min hh₀ (mul_pos hκ0 he0)).le (min_le_right _ _) ha0.le
    have h2 : (κ * e) ^ a = (2 * Cn)⁻¹ * ε := by
      rw [Real.mul_rpow hκ0.le he0.le, hκ, he, ← Real.rpow_mul (inv_pos.mpr (by positivity)).le,
        ← Real.rpow_mul hε0.le, one_div, inv_mul_cancel₀ ha0.ne', Real.rpow_one, Real.rpow_one]
    calc 2 * (Cn * (min h₀ (κ * e)) ^ a) ≤ 2 * (Cn * (κ * e) ^ a) := by
          gcongr
      _ = ε := by rw [h2]; field_simp
  · -- `2 (Cfar h^{-M} + Cr) ≤ Cc ε^{-γ}`
    have hlow : c₁ * e ≤ min h₀ (κ * e) := by
      refine le_min ?_ ?_
      · calc c₁ * e ≤ h₀ * 1 := mul_le_mul (min_le_left _ _) he1 he0.le hh₀.le
          _ = h₀ := mul_one _
      · exact mul_le_mul_of_nonneg_right (min_le_right _ _) he0.le
    have hpos : 0 < min h₀ (κ * e) := lt_min hh₀ (mul_pos hκ0 he0)
    have hinv : (min h₀ (κ * e))⁻¹ ≤ (c₁ * e)⁻¹ := inv_anti₀ (mul_pos hc₁0 he0) hlow
    have hpow : ((min h₀ (κ * e))⁻¹) ^ M ≤ (c₁⁻¹) ^ M * ε ^ (-((M : ℝ) / a)) := by
      calc ((min h₀ (κ * e))⁻¹) ^ M ≤ ((c₁ * e)⁻¹) ^ M :=
            pow_le_pow_left₀ (inv_nonneg.mpr hpos.le) hinv M
        _ = (c₁⁻¹) ^ M * (e⁻¹) ^ M := by rw [mul_inv, mul_pow]
        _ = (c₁⁻¹) ^ M * ε ^ (-((M : ℝ) / a)) := by
            congr 1
            rw [he, ← Real.rpow_neg hε0.le, ← Real.rpow_natCast, ← Real.rpow_mul hε0.le]
            congr 1
            ring
    have hγ : ε ^ (-((M : ℝ) / a)) ≤ ε ^ (-((M : ℝ) / a + 2)) :=
      Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
    have hone : 1 ≤ ε ^ (-((M : ℝ) / a + 2)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hε0 hε1.le (by
        have : 0 ≤ (M : ℝ) / a := by positivity
        linarith)
    have hε' : 0 ≤ ε ^ (-((M : ℝ) / a + 2)) := by positivity
    have hc₁M : 0 ≤ (c₁⁻¹) ^ M := by positivity
    calc 2 * (Cfar * ((min h₀ (κ * e))⁻¹) ^ M + Cr)
        ≤ 2 * (Cfar * ((c₁⁻¹) ^ M * ε ^ (-((M : ℝ) / a + 2))) + Cr * ε ^ (-((M : ℝ) / a + 2))) := by
          have h1 : Cfar * ((min h₀ (κ * e))⁻¹) ^ M ≤
              Cfar * ((c₁⁻¹) ^ M * ε ^ (-((M : ℝ) / a + 2))) :=
            mul_le_mul_of_nonneg_left (hpow.trans (mul_le_mul_of_nonneg_left hγ hc₁M)) hCfar
          have h2 : Cr ≤ Cr * ε ^ (-((M : ℝ) / a + 2)) := by nlinarith
          linarith
      _ ≤ (2 * Cfar * (c₁⁻¹) ^ M + 2 * Cr + 1) * ε ^ (-((M : ℝ) / a + 2)) := by
          nlinarith [mul_nonneg hCfar hc₁M]

/-- The full Hölder norm is bounded by `2 Φ` if the sup and the `d̃`-Hölder quotients are. -/
theorem holderENorm_le_of_bounds {N : ℕ} {d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞} {α : ℝ}
    (hα : 0 < α) {V : Set (Fin N → ℝ)} {G : (Fin N → ℝ) → ℝ} {Φ : ℝ} (hΦ : 0 ≤ Φ)
    (hsup : ∀ x ∈ V, |G x| ≤ Φ)
    (hhol : ∀ x ∈ V, ∀ y ∈ V, d x y < ⊤ → |G x - G y| ≤ Φ * (d x y).toReal ^ α) :
    holderENorm d α V G ≤ ENNReal.ofReal (2 * Φ) := by
  have h1 : (⨆ x : V, ENNReal.ofReal |G x|) ≤ ENNReal.ofReal Φ :=
    iSup_le fun x => ENNReal.ofReal_le_ofReal (hsup x x.2)
  have h2 : holderSeminorm d α V G ≤ ENNReal.ofReal Φ := by
    refine sInf_le ⟨ENNReal.ofReal_lt_top, fun x hx y hy hd => ?_⟩
    have hb := hhol x hx y hy hd
    calc ENNReal.ofReal |G x - G y| ≤ ENNReal.ofReal (Φ * (d x y).toReal ^ α) :=
          ENNReal.ofReal_le_ofReal hb
      _ = ENNReal.ofReal Φ * ENNReal.ofReal ((d x y).toReal ^ α) :=
          ENNReal.ofReal_mul hΦ
      _ = ENNReal.ofReal Φ * d x y ^ α := by
          rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hα.le,
            ENNReal.ofReal_toReal hd.ne]
  calc holderENorm d α V G = (⨆ x : V, ENNReal.ofReal |G x|) + holderSeminorm d α V G := rfl
    _ ≤ ENNReal.ofReal Φ + ENNReal.ofReal Φ := add_le_add h1 h2
    _ = ENNReal.ofReal (2 * Φ) := by
        rw [← ENNReal.ofReal_add hΦ hΦ]; congr 1; ring

theorem integrable_list_map_sum {ι E : Type*} [MeasurableSpace E] {μ : Measure E} (l : List ι)
    (f : ι → E → ℝ) (hf : ∀ i ∈ l, Integrable (f i) μ) :
    Integrable (fun x => (l.map (fun i => f i x)).sum) μ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (hf a (List.mem_cons_self ..)).add (ih fun i hi => hf i (List.mem_cons_of_mem _ hi))

theorem integral_list_map_sum {ι E : Type*} [MeasurableSpace E] {μ : Measure E} (l : List ι)
    (f : ι → E → ℝ) (hf : ∀ i ∈ l, Integrable (f i) μ) :
    ∫ x, (l.map (fun i => f i x)).sum ∂μ = (l.map (fun i => ∫ x, f i x ∂μ)).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [integral_add (hf a (List.mem_cons_self ..))
      (integrable_list_map_sum l f fun i hi => hf i (List.mem_cons_of_mem _ hi)),
      ih fun i hi => hf i (List.mem_cons_of_mem _ hi)]

/-- **The operator of a positive-type decomposition** applied to a bounded measurable `g`:
the sum of the principal-term integrals and the regular remainder integral. -/
theorem apply_eq_principal_sum_add_regular (hF : C.IsLiftedFrame F) {lam : ℕ} (hlam : lam ≠ 0)
    (T : TypeOperator F lam) (d : TypeDecomposition F lam 3 T.kernel)
    (hdeg : ∀ t ∈ d.principal, t.degree ≤ 1) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : AEStronglyMeasurable g (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |g y| ≤ M)
    (x : Fin (n + m) → ℝ) :
    T.apply g x = (d.principal.map (fun t => ∫ η, t.kernel x η * g η)).sum +
      ∫ η, d.regular x η * g η := by
  have hint : ∀ t ∈ d.principal, Integrable (fun η => t.kernel x η * g η) := fun t ht =>
    (PrincipalTerm.patchKernel hF t (hdeg t ht)).integrable_row hg hM0 hM x
  have hr1 : IsRegularKernel F 1 d.regular := d.regular_isRegular.mono (by norm_num)
  have hrint : Integrable (fun η => d.regular x η * g η) :=
    (IsRegularKernel.patchKernel hF hr1).integrable_row hg hM0 hM x
  have hsum : Integrable (fun η => (d.principal.map (fun t => t.kernel x η * g η)).sum) :=
    integrable_list_map_sum d.principal (fun t η => t.kernel x η * g η) hint
  have e1 : T.apply g x = ∫ η, T.kernel x η * g η := by
    simp [TypeOperator.apply, hlam]
  rw [e1]
  have e2 : ∫ η, T.kernel x η * g η =
      ∫ η, ((d.principal.map (fun t => t.kernel x η * g η)).sum + d.regular x η * g η) := by
    refine integral_congr_ae ?_
    filter_upwards [C.ae_ne x] with η hηx
    rw [d.eq_off_diagonal x η hηx.symm, add_mul, List.sum_map_mul_right]
  rw [e2, integral_add hsum hrint, integral_list_map_sum d.principal
    (fun t η => t.kernel x η * g η) hint]

/-- **From the bounds at one scale to the interpolation inequality**: if for every
admissible `v` and `0 < h ≤ h₀` the function `G v` is bounded on `V` by
`Φ = Cn h^{1-α} Mg + Cfar h^{-M} Mv + Cr Mv` and `d`-Hölder with constant `Φ`, where `Mg, Mv` bound
`|Lop v|, |v|` on `V`, then the choice `h = h(ε)` gives `γ > 1` and `Cc` with
`‖G v‖_{C^α} ≤ ε ‖Lop v‖_∞ + Cc ε^{-γ} ‖v‖_∞` for `0 < ε < 1`. -/
theorem interpolation_of_bounds {N : ℕ} {d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) {V : Set (Fin N → ℝ)}
    {G Lop : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ} {adm : ((Fin N → ℝ) → ℝ) → Prop}
    {Cn h₀ Cfar Cr : ℝ} (M : ℕ) (hCn : 0 < Cn) (hh₀ : 0 < h₀) (hCfar : 0 ≤ Cfar) (hCr : 0 ≤ Cr)
    (hb : ∀ v, adm v → ∀ h : ℝ, 0 < h → h ≤ h₀ → ∀ Mg Mv : ℝ, 0 ≤ Mg → 0 ≤ Mv →
      (∀ y ∈ V, |Lop v y| ≤ Mg) → (∀ y ∈ V, |v y| ≤ Mv) →
      (∀ x ∈ V, |G v x| ≤ Cn * h ^ (1 - α) * Mg + Cfar * (h⁻¹) ^ M * Mv + Cr * Mv) ∧
      (∀ x ∈ V, ∀ y ∈ V, d x y < ⊤ → |G v x - G v y| ≤
        (Cn * h ^ (1 - α) * Mg + Cfar * (h⁻¹) ^ M * Mv + Cr * Mv) * (d x y).toReal ^ α)) :
    ∃ γ Cc : ℝ, 1 < γ ∧ 0 < Cc ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ v, adm v →
      holderENorm d α V (G v) ≤
        ENNReal.ofReal ε * (⨆ x : V, ENNReal.ofReal |Lop v x|) +
          ENNReal.ofReal (Cc * ε ^ (-γ)) * ⨆ x : V, ENNReal.ofReal |v x| := by
  obtain ⟨γ, Cc, hγ, hCc, hscale⟩ := exists_scale (Cn := Cn) (h₀ := h₀) (Cfar := Cfar) (Cr := Cr)
    M hCn hh₀ hCfar hCr hα1
  refine ⟨γ, Cc, hγ, hCc, fun ε hε0 hε1 v hv => ?_⟩
  obtain ⟨h, hh0, hhh₀, hh1, hh2⟩ := hscale ε hε0 hε1
  set Sg : ℝ≥0∞ := ⨆ x : V, ENNReal.ofReal |Lop v x| with hSg
  set Sv : ℝ≥0∞ := ⨆ x : V, ENNReal.ofReal |v x| with hSv
  have hεpos : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε0
  have hCεpos : 0 < ENNReal.ofReal (Cc * ε ^ (-γ)) :=
    ENNReal.ofReal_pos.mpr (mul_pos hCc (Real.rpow_pos_of_pos hε0 _))
  by_cases hSgT : Sg = ⊤
  · rw [hSgT, ENNReal.mul_top hεpos.ne', top_add]; exact le_top
  by_cases hSvT : Sv = ⊤
  · rw [hSvT, ENNReal.mul_top hCεpos.ne', add_top]; exact le_top
  set Mg : ℝ := Sg.toReal with hMg
  set Mv : ℝ := Sv.toReal with hMv
  have hMg0 : 0 ≤ Mg := ENNReal.toReal_nonneg
  have hMv0 : 0 ≤ Mv := ENNReal.toReal_nonneg
  have hMgb : ∀ y ∈ V, |Lop v y| ≤ Mg := fun y hy =>
    (ENNReal.ofReal_le_iff_le_toReal hSgT).mp
      (le_iSup (fun x : V => ENNReal.ofReal |Lop v x|) ⟨y, hy⟩)
  have hMvb : ∀ y ∈ V, |v y| ≤ Mv := fun y hy =>
    (ENNReal.ofReal_le_iff_le_toReal hSvT).mp
      (le_iSup (fun x : V => ENNReal.ofReal |v x|) ⟨y, hy⟩)
  obtain ⟨hsup, hhol⟩ := hb v hv h hh0 hhh₀ Mg Mv hMg0 hMv0 hMgb hMvb
  have hΦ0 : 0 ≤ Cn * h ^ (1 - α) * Mg + Cfar * (h⁻¹) ^ M * Mv + Cr * Mv := by
    have : 0 ≤ h ^ (1 - α) := Real.rpow_nonneg hh0.le _
    positivity
  refine (holderENorm_le_of_bounds hα0 hΦ0 hsup hhol).trans ?_
  have hcomb : 2 * (Cn * h ^ (1 - α) * Mg + Cfar * (h⁻¹) ^ M * Mv + Cr * Mv) ≤
      ε * Mg + Cc * ε ^ (-γ) * Mv := by
    have a1 : 2 * (Cn * h ^ (1 - α)) * Mg ≤ ε * Mg := mul_le_mul_of_nonneg_right hh1 hMg0
    have a2 : 2 * (Cfar * (h⁻¹) ^ M + Cr) * Mv ≤ Cc * ε ^ (-γ) * Mv :=
      mul_le_mul_of_nonneg_right hh2 hMv0
    nlinarith
  calc ENNReal.ofReal (2 * (Cn * h ^ (1 - α) * Mg + Cfar * (h⁻¹) ^ M * Mv + Cr * Mv))
      ≤ ENNReal.ofReal (ε * Mg + Cc * ε ^ (-γ) * Mv) := ENNReal.ofReal_le_ofReal hcomb
    _ = ENNReal.ofReal ε * Sg + ENNReal.ofReal (Cc * ε ^ (-γ)) * Sv := by
        rw [ENNReal.ofReal_add (mul_nonneg hε0.le hMg0)
          (mul_nonneg (mul_nonneg hCc.le (Real.rpow_nonneg hε0.le _)) hMv0),
          ENNReal.ofReal_mul hε0.le, ENNReal.ofReal_mul (mul_nonneg hCc.le
            (Real.rpow_nonneg hε0.le _)), hMg, hMv, ENNReal.ofReal_toReal hSgT,
          ENNReal.ofReal_toReal hSvT]

/-- **The first interpolation inequality** (BB Prop 11.50 and
Lem 11.51, pp. 593-595; the first Hölder interpolation inequality), for a fixed positive-type operator on a
lifted frame: for `0 < α < 1` and a type-`λ` operator `F` with `λ ≥ 1` there are `γ > 1` and `Cc`
(independent of `v` and `ε`) such that for `0 < ε < 1` and every `v ∈ C²(O)`,
`‖F L̃ v‖_{C^α(V)} ≤ ε ‖L̃ v‖_{∞,V} + Cc ε^{-γ} ‖v‖_{∞,V}`.
`L̃` is any operator `IsCoordinateOp` (e.g. `L̃ = ∑ X̃ᵢ² + X̃₀` or `∑ X̃ᵢ²`); the weighted
variation inequality `hvar` and the weights `≤ 2` are the hypotheses on the chart used by
the near radial cutoff and by the comparison of the Euclidean and control distances. -/
theorem exists_fractional_interpolation (hF : C.IsLiftedFrame F) (hw : ∀ i, (w i : ℕ) ≤ 2)
    {Cg : ℝ} (hCg : 0 ≤ Cg) (hvar : LiftedVariation C Cg) {lam : ℕ} (hlam : 1 ≤ lam)
    (T : TypeOperator F lam) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {Lop : ((Fin (n + m) → ℝ) → ℝ) → (Fin (n + m) → ℝ) → ℝ} (hL : IsCoordinateOp C Lop) :
    ∃ γ Cc : ℝ, 1 < γ ∧ 0 < Cc ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ v : (Fin (n + m) → ℝ) → ℝ, ContDiffOn ℝ 2 v C.O →
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun x => T.apply (Lop v) x) ≤
          ENNReal.ofReal ε * (⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |Lop v x|) +
            ENNReal.ofReal (Cc * ε ^ (-γ)) *
              ⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |v x| := by
  obtain ⟨ν, hν⟩ := exists_smooth_homogeneous_norm C.G
  obtain ⟨d⟩ := T.isType 3
  have hlam0 : lam ≠ 0 := by omega
  have hdeg : ∀ t ∈ d.principal, t.degree ≤ 1 := fun t ht => by
    have h1 := d.principal_degree t ht
    have h2 : (1 : ℤ) ≤ (lam : ℤ) := by exact_mod_cast hlam
    omega
  obtain ⟨Cn, h₀, Cfar, M, hCn, hh₀, hh₀1, hCfar, hP⟩ :=
    principal_list_interpolation hF hw ν hν hCg hvar hα0 hα1 hL d.principal hdeg
  obtain ⟨Cr, hCr, hR⟩ := regular_interpolation hF hw d.regular_isRegular hα0 hα1 hL
  obtain ⟨A, B, hA, hB, hLop⟩ := hL
  refine interpolation_of_bounds (adm := fun v => ContDiffOn ℝ 2 v C.O) hα0 hα1 M hCn hh₀ hCfar hCr
    (fun v hv h hh hhh₀ Mg Mv hMg0 hMv0 hMg hMv => ?_)
  have hO : IsOpen C.O := isOpen_liftedDomain C
  have hSU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.O :=
    subset_closure.trans (hF.closure_subset.trans C.U_subset_O)
  have hgc : ContinuousOn (Lop v) C.O :=
    (continuousOn_diffOp2 hO hA hB hv).congr (fun x hx => hLop v hv x hx)
  have hgmeas : AEStronglyMeasurable (Lop v) (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) :=
    (hgc.mono hSU).aestronglyMeasurable F.V.isOpen.measurableSet
  obtain ⟨hP1, hP2⟩ := hP h hh hhh₀ v hv Mg Mv hMg0 hMv0 hMg hMv
  obtain ⟨hR1, hR2⟩ := hR v hv Mv hMv0 hMv
  have hrep := fun x => apply_eq_principal_sum_add_regular hF hlam0 T d hdeg hgmeas hMg0 hMg x
  refine ⟨fun x hx => ?_, fun x hx y hy _ => ?_⟩
  · rw [hrep x]
    refine (abs_add_le _ _).trans ?_
    linarith [hP1 x hx, hR1 x hx]
  · rw [hrep x, hrep y]
    have e : ∀ a b a' b' : ℝ, a + b - (a' + b') = (a - a') + (b - b') := fun a b a' b' => by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    have hd0 : 0 ≤ (C.dl x y).toReal ^ α := Real.rpow_nonneg ENNReal.toReal_nonneg _
    have h1 := hP2 x hx y hy
    have h2 := hR2 x hx y hy
    nlinarith [mul_nonneg hMv0 hd0, mul_nonneg hCr hd0]

end RothschildStein.P2
