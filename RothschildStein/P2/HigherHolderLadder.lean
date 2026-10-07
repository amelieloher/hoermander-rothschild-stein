-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherHolderStepRoot
public import RothschildStein.P2.TransferCoverHolder
public import RothschildStein.S.WeakHolderToIntrinsic
public import RothschildStein.S.IntrinsicWeakHolderExport
public import RothschildStein.S.IntrinsicWeakWordExport
public import RothschildStein.S.WeakHolderRepresentatives
public import RothschildStein.S.WeakHolderNormBounds

/-!
# The ladder of radii on `ρ`-balls

Part of the higher Hölder estimate (BB pp. 603–604: apply the recurrence on successively doubled balls, decreasing `j`
by one each time, until only `C^{2,α}` remains, and control that term by the base Hölder estimate). The step estimate
`stage_step` is applied `k` times on the nested `ρ`-balls `U_{ρ_i}^ρ`, `ρ_i = r + i r/(k + 1)` (`ρ_0 = r`,
`ρ_{k+1} = 2 r`), starting from the order-two jet on `U_{ρ_k}` which the base Hölder estimate
(`LiftedBaseHolderEstimate`) controls with outer radius `2 r`. The regularity of `u` is *not* presupposed: it is
produced by the steps (`stage_step` rests on `compact_regularity`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2.HigherHolder

open RothschildStein.P1

section Jets

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- A Hölder weak jet restricts to a smaller open set and a smaller order. -/
theorem isHolderWeakJet_restrict {V V' : Opens (Fin (n + m) → ℝ)}
    (hV : (V' : Set (Fin (n + m) → ℝ)) ⊆ (V : Set (Fin (n + m) → ℝ))) {α : ℝ} {kk kk' : ℕ}
    (hk : kk' ≤ kk) {u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hD : LiftedChart.IsHolderWeakJet w C.Xl C.dl V kk α u D) :
    LiftedChart.IsHolderWeakJet w C.Xl C.dl V' kk' α u D := fun K hK =>
  ⟨S.hasWeakWordDeriv_restrict C.Xl V V' hV
      (hD K (by
        rw [S.mem_wordFamily_iff] at hK ⊢
        exact hK.trans hk)).1,
    ne_top_of_le_ne_top (hD K (by
        rw [S.mem_wordFamily_iff] at hK ⊢
        exact hK.trans hk)).2 (S.holderENorm_mono C.dl α _ _ hV)⟩

/-- The weighted norm of an element of `C^{N,α}_{X̃}(V)` is the weighted norm of any Hölder
weak jet. -/
theorem holderXENorm_eq_holderJetNorm {V : Opens (Fin (n + m) → ℝ)}
    (hV : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    {N : ℕ} {u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hu : memHolderX w C.Xl C.dl V N α u)
    (hD : LiftedChart.IsHolderWeakJet w C.Xl C.dl V N α u D) :
    holderXENorm w C.Xl C.dl V N α u = holderJetNorm w C.dl (V : Set (Fin (n + m) → ℝ)) α N D := by
  have h1 := S.holderXENorm_eq_weakHolderXENorm_of_memHolderX C.chartOpens V C.distanceGeometry hV
    w C.Xl hX N hα0 hu
  have h2 := S.weakHolderXENorm_eq_sum_representatives C.chartOpens V C.distanceGeometry hV w C.Xl N
    hα0 u D (fun I hI => ⟨(hD I hI).1, lt_top_iff_ne_top.2 (hD I hI).2⟩)
  exact h1.trans h2

/-- An element of `C^{N,α}_{X̃}(V)` has a Hölder weak jet with `D [] = u`. -/
theorem exists_selfJet_of_memHolderX {V : Opens (Fin (n + m) → ℝ)}
    (hV : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    {N : ℕ} {u : (Fin (n + m) → ℝ) → ℝ} (hu : memHolderX w C.Xl C.dl V N α u) :
    ∃ D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ, D [] = u ∧
      LiftedChart.IsHolderWeakJet w C.Xl C.dl V N α u D := by
  have hweak := S.memWeakHolderX_of_memHolderX C.chartOpens V C.distanceGeometry hV w C.Xl hX N hα0 hu
  obtain ⟨D, hD0, hD⟩ := S.exists_weakHolder_representatives w C.Xl C.dl V N α hweak
  exact ⟨D, hD0, fun I hI => ⟨(hD I hI).1, (hD I hI).2.ne⟩⟩

/-- The intrinsic derivative of a word agrees with the entry of a Hölder weak jet. -/
theorem eqOn_jet_of_hasIntrinsicWordDeriv {V : Opens (Fin (n + m) → ℝ)}
    (hV : (V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    {N : ℕ} {u : (Fin (n + m) → ℝ) → ℝ} (hu : memHolderX w C.Xl C.dl V N α u)
    {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hD : LiftedChart.IsHolderWeakJet w C.Xl C.dl V N α u D) {I : List (Fin k)}
    (hI : I ∈ wordFamily w N) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : hasIntrinsicWordDeriv C.Xl V I u g) : EqOn g (D I) (V : Set (Fin (n + m) → ℝ)) := by
  classical
  choose! gJ hgJ using hu.2
  set jet : List (Fin k) → (Fin (n + m) → ℝ) → ℝ := fun J => if J = [] then u else gJ J with hjet
  have hsub : ∀ J : List (Fin k), J.Sublist I → J ∈ wordFamily w N := fun J hJ =>
    S.sublist_mem_wordFamily w N hJ hI
  have hcont : ∀ J, J.Sublist I → ContinuousOn (jet J) (V : Set (Fin (n + m) → ℝ)) := by
    intro J hJ
    by_cases hJ0 : J = []
    · subst hJ0
      simp only [hjet, ite_true]
      exact LiftedChart.continuousOn_of_holderENorm_lt_top hV hα0 hu.1
    · simp only [hjet, hJ0, ite_false]
      exact LiftedChart.continuousOn_of_holderENorm_lt_top hV hα0 (hgJ J (hsub J hJ)).2
  have hint : ∀ J, J.Sublist I → hasIntrinsicWordDeriv C.Xl V J u (jet J) := by
    intro J hJ
    by_cases hJ0 : J = []
    · subst hJ0
      simp only [hjet, ite_true]
      exact fun x _ => rfl
    · simp only [hjet, hJ0, ite_false]
      exact (hgJ J (hsub J hJ)).1
  have hweak := S.hasWeakWordDeriv_of_continuous_intrinsic_words V C.Xl hX I u jet (by simp [hjet])
    hint hcont
  have hgI : EqOn g (jet I) (V : Set (Fin (n + m) → ℝ)) := by
    by_cases hI0 : I = []
    · subst hI0
      simp only [hjet, ite_true]
      intro x hx
      exact hg hx
    · simp only [hjet, hI0, ite_false]
      exact fun x hx => (S.hasIntrinsicWordDeriv_unique V C.Xl I hg (hgJ I hI).1 hx)
  have hDc : ContinuousOn (D I) (V : Set (Fin (n + m) → ℝ)) :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hV hα0 (lt_top_iff_ne_top.2 (hD I hI).2)
  have := eqOn_of_hasWeakWordDeriv_of_continuousOn hweak (hD I hI).1 (hcont I (List.Sublist.refl I)) hDc
  exact fun x hx => (hgI hx).trans (this hx)

end Jets

section Ladder

/-- The radii of the ladder: `ρ_i = r + i r/(k + 1)` (`ρ_0 = r`, `ρ_{k+1} = 2 r`). -/
def ladderRadius (k : ℕ) (r : ℝ) (i : ℕ) : ℝ := r + i * (r / (k + 1))

theorem ladderRadius_succ (k : ℕ) (r : ℝ) (i : ℕ) :
    ladderRadius k r (i + 1) = ladderRadius k r i + r / (k + 1) := by
  unfold ladderRadius
  push_cast
  ring

theorem ladderRadius_pos {k : ℕ} {r : ℝ} (hr : 0 < r) (i : ℕ) : 0 < ladderRadius k r i := by
  unfold ladderRadius
  positivity

theorem ladderRadius_le {k : ℕ} {r : ℝ} (hr : 0 < r) {i : ℕ} (hi : i ≤ k + 1) :
    ladderRadius k r i ≤ 2 * r := by
  unfold ladderRadius
  have hk : (0 : ℝ) < k + 1 := by positivity
  have h1 : (i : ℝ) ≤ k + 1 := by exact_mod_cast hi
  have h2 : (i : ℝ) * (r / (k + 1)) ≤ (k + 1) * (r / (k + 1)) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have h3 : ((k : ℝ) + 1) * (r / (k + 1)) = r := by field_simp
  linarith

theorem ladderRadius_k1 (k : ℕ) (r : ℝ) : ladderRadius k r (k + 1) = 2 * r := by
  unfold ladderRadius
  push_cast
  field_simp
  ring

/-- Arithmetic: `F + C Q (F + D) ≤ (1 + C) Q (F + D)` for `Q ≥ 1`. -/
theorem add_ofReal_mul_le {C Q : ℝ} (hC : 0 ≤ C) (hQ : 1 ≤ Q) (F D : ℝ≥0∞) :
    F + ENNReal.ofReal (C * Q) * (F + D) ≤ ENNReal.ofReal ((1 + C) * Q) * (F + D) := by
  calc F + ENNReal.ofReal (C * Q) * (F + D)
      ≤ ENNReal.ofReal 1 * (F + D) + ENNReal.ofReal (C * Q) * (F + D) :=
        add_le_add (by rw [ENNReal.ofReal_one, one_mul]; exact le_self_add) le_rfl
    _ = ENNReal.ofReal (1 + C * Q) * (F + D) := by
        rw [← add_mul, ENNReal.ofReal_add zero_le_one (by positivity)]
    _ ≤ ENNReal.ofReal ((1 + C) * Q) * (F + D) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (by nlinarith)) le_rfl

/-- Arithmetic of one rung. -/
theorem ladder_arith {Cs E P Q : ℝ} (hCs : 0 ≤ Cs) (hE : 0 ≤ E) (hP : 0 ≤ P) (hQ : 1 ≤ Q)
    (F D : ℝ≥0∞) :
    ENNReal.ofReal (Cs * P) * (F + ENNReal.ofReal (E * Q) * (F + D)) ≤
      ENNReal.ofReal (Cs * (1 + E) * (P * Q)) * (F + D) := by
  calc ENNReal.ofReal (Cs * P) * (F + ENNReal.ofReal (E * Q) * (F + D))
      ≤ ENNReal.ofReal (Cs * P) * (ENNReal.ofReal ((1 + E) * Q) * (F + D)) :=
        mul_le_mul' le_rfl (add_ofReal_mul_le hE hQ F D)
    _ = ENNReal.ofReal (Cs * (1 + E) * (P * Q)) * (F + D) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        ring

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart noDriftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r₀ : ℕ} {H : H1.StandingHypotheses C.G r₀} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {a : TestFunction F.V ℝ (⊤ : ℕ∞)}

/-- **The ladder** (BB pp. 603-604). For `i ≤ k` there are `r₁, E > 0` and `p` such
that for `0 < r < r₁`, a Hölder weak jet `D` of order `2` on `U_{ρ_k}` and a Hölder weak jet `Df` of order `k` on
`U_{2r}` with `L̃ D = Df []` on `U_{ρ_k}`, the function `D []` has a Hölder weak jet of order `i + 2` on
`U_{ρ_{k-i}}`, extending `D` and compatible with `Df`, with
`‖·‖_{i+2} ≤ E ((r/(k+1))⁻¹)^p (‖Df‖_{k, U_{2r}} + ‖D‖_{2, U_{ρ_k}})`. -/
theorem ladder_claim (hH : HolderFrame C H K hQ F a) (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) {R : ℝ} (hR : 0 < R)
    (hRV : rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) R ⊆ (F.V : Set (Fin (n + m) → ℝ)))
    (hRa : ∀ x ∈ rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) R, a x = 1) :
    ∀ i : ℕ, i ≤ k → ∃ r₁ E : ℝ, 0 < r₁ ∧ 0 < E ∧ ∃ p : ℕ, ∀ r : ℝ, 0 < r → r < r₁ →
      ∀ D Df : List (Fin q) → (Fin (n + m) → ℝ) → ℝ,
        LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl (rhoBallOpen C ν (ladderRadius k r k)) 2 α
          (D []) D →
        LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl (rhoBallOpen C ν (2 * r)) k α (Df []) Df →
        (∀ x ∈ rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) (ladderRadius k r k),
          weakSumSquares D [] x = Df [] x) →
        ∃ Di : List (Fin q) → (Fin (n + m) → ℝ) → ℝ,
          LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl
            (rhoBallOpen C ν (ladderRadius k r (k - i))) (i + 2) α (Di []) Di ∧
          (∀ x ∈ rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) (ladderRadius k r (k - i)),
            weakSumSquares Di [] x = Df [] x) ∧
          (∀ K' : List (Fin q), K'.length ≤ 2 →
            ∀ x ∈ rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) (ladderRadius k r (k - i)),
              Di K' x = D K' x) ∧
          holderJetNorm noDriftWeight C.dl
              (rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) (ladderRadius k r (k - i))) α (i + 2) Di ≤
            ENNReal.ofReal (E * (((r / (k + 1)) ⁻¹) ^ p)) *
              (holderJetNorm noDriftWeight C.dl
                  (rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) (2 * r)) α k Df +
                holderJetNorm noDriftWeight C.dl
                  (rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) (ladderRadius k r k)) α 2 D) := by
  have hw : ∀ j : Fin q, ((noDriftWeight j : ℕ+) : ℕ) = 1 := fun j => noDriftWeight_coe_eq_one j
  intro i
  induction i with
  | zero =>
    intro _
    refine ⟨1, 1, one_pos, one_pos, 0, fun r hr hr1 D Df hD hDf hrel => ⟨D, ?_, ?_, ?_, ?_⟩⟩
    · simpa using hD
    · simpa using hrel
    · intro K' _ x _
      rfl
    · simp only [Nat.sub_zero, pow_zero, mul_one, ENNReal.ofReal_one, one_mul]
      exact le_add_self
  | succ i ih =>
    intro hi
    obtain ⟨r₁, E, hr₁, hE, p, hih⟩ := ih (by omega)
    obtain ⟨rstar, Cs, hrstar, hCs, hstage⟩ := stage_step hH ν hν hα0 hα1 i hRV hRa
    refine ⟨min r₁ (min (rstar / 2) (min (R / 2) 1)), Cs * (1 + E),
      lt_min hr₁ (lt_min (by positivity) (lt_min (by positivity) one_pos)), by positivity,
      i + 4 + p, fun r hr hrr D Df hD hDf hrel => ?_⟩
    have hr1 : r < r₁ := lt_of_lt_of_le hrr (min_le_left _ _)
    have hr2 : r < rstar / 2 := lt_of_lt_of_le hrr ((min_le_right _ _).trans (min_le_left _ _))
    have hr3 : r < R / 2 :=
      lt_of_lt_of_le hrr ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    have hr4 : r < 1 :=
      lt_of_lt_of_le hrr ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    obtain ⟨Di, hDi, hrelDi, hagr, hnorm⟩ := hih r hr hr1 D Df hD hDf hrel
    have hΔ0 : 0 < r / ((k : ℝ) + 1) := by positivity
    have hΔ1 : r / ((k : ℝ) + 1) ≤ 1 := by
      have : r / ((k : ℝ) + 1) ≤ r := div_le_self hr.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
      linarith
    have hkk : k - i = (k - (i + 1)) + 1 := by omega
    have hr'eq : ladderRadius k r (k - i) = ladderRadius k r (k - (i + 1)) + r / ((k : ℝ) + 1) := by
      rw [hkk, ladderRadius_succ]
    have hs0 : 0 < ladderRadius k r (k - (i + 1)) := ladderRadius_pos hr _
    have hsr' : ladderRadius k r (k - (i + 1)) < ladderRadius k r (k - i) := by
      rw [hr'eq]; linarith
    have hr'le : ladderRadius k r (k - i) ≤ 2 * r := ladderRadius_le hr (by omega)
    have hr'rstar : ladderRadius k r (k - i) < rstar := by linarith
    have hr'R : ladderRadius k r (k - i) ≤ R := by linarith
    have hsub2r : rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) (ladderRadius k r (k - i)) ⊆
        rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) (2 * r) :=
      rhoBall_mono C ν _ hr'le
    have hDf' : LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl
        (rhoBallOpen C ν (ladderRadius k r (k - i))) (i + 1) α (Df []) Df :=
      isHolderWeakJet_restrict (C := C) (V := rhoBallOpen C ν (2 * r)) hsub2r (by omega) hDf
    obtain ⟨D'', hD'', hag, hnorm''⟩ := hstage _ _ hs0 hsr' hr'rstar hr'R Di Df hDi hDf' hrelDi
    have hsub_s : rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) (ladderRadius k r (k - (i + 1))) ⊆
        rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) (ladderRadius k r (k - i)) :=
      rhoBall_mono C ν _ hsr'.le
    refine ⟨D'', hD'', ?_, ?_, ?_⟩
    · intro x hx
      have h1 : weakSumSquares D'' [] x = weakSumSquares Di [] x := by
        have : ∀ i' : Fin q, D'' ([] ++ [i', i']) x = Di ([] ++ [i', i']) x := fun i' => by
          simpa using hag [i', i'] (by simp) x hx
        simp only [weakSumSquares, this]
      rw [h1]
      exact hrelDi x (hsub_s hx)
    · intro K' hK' x hx
      rw [hag K' (by omega) x hx]
      exact hagr K' hK' x (hsub_s hx)
    · have hgap : ladderRadius k r (k - i) - ladderRadius k r (k - (i + 1)) = r / ((k : ℝ) + 1) := by
        rw [hr'eq]; ring
      rw [hgap] at hnorm''
      have hFdf : holderJetNorm noDriftWeight C.dl
          (rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) (ladderRadius k r (k - i))) α (i + 1) Df ≤
          holderJetNorm noDriftWeight C.dl (rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) (2 * r)) α k Df :=
        (holderJetNorm_mono_set C.dl hsub2r α (i + 1) Df).trans
          (holderJetNorm_mono_order hw C.dl _ α (by omega) Df)
      refine hnorm''.trans ?_
      refine (mul_le_mul' le_rfl (add_le_add hFdf hnorm)).trans ?_
      have hQ1 : 1 ≤ ((r / ((k : ℝ) + 1))⁻¹) ^ p :=
        one_le_pow₀ ((one_le_inv₀ hΔ0).2 hΔ1)
      refine (ladder_arith hCs.le hE.le (by positivity) hQ1 _ _).trans (le_of_eq ?_)
      rw [← pow_add]

/-- **The lifted higher Hölder estimate** (BB pp. 603-604,
(11.94)-(11.96)): at the chart `C` and the smooth homogeneous norm `ν`, there are `r₀ > 0`, `βn`, `Kc > 0` such that
for `0 < r < r₀`, every open `W ⊇ {ν ∘ Θ ≤ 2 r}`, `u ∈ C^{2,α}_{X̃}(W)` with `L̃ u = f ∈ C^{k,α}_{X̃}(W)` (intrinsic
derivatives): `u ∈ C^{k+2,α}_{X̃}(U_r^ρ)` and
`‖u‖_{C^{k+2,α}(U_r^ρ)} ≤ Kc r^{-βn} (‖f‖_{C^{k,α}(U_{2r}^ρ)} + ‖u‖_{L^∞(U_{2r}^ρ)})`. -/
def LiftedHigherHolderEstimate (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (α : ℝ) (k : ℕ) : Prop :=
  ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ (βn : ℕ) (Kc : ℝ), 0 < Kc ∧ ∀ r : ℝ, 0 < r → r < r₀ →
    ∀ W : Opens (Fin (n + m) → ℝ),
      closedRhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) (2 * r) ⊆ (W : Set (Fin (n + m) → ℝ)) →
      ∀ u f : (Fin (n + m) → ℝ) → ℝ,
        memHolderX noDriftWeight C.Xl C.dl W 2 α u →
        HasIntrinsicOperatorValue C.Xl W (noDriftOpWords q) u f →
        memHolderX noDriftWeight C.Xl C.dl W k α f →
        memHolderX noDriftWeight C.Xl C.dl (rhoBallOpen C ν r) (k + 2) α u ∧
          holderXENorm noDriftWeight C.Xl C.dl (rhoBallOpen C ν r) (k + 2) α u ≤
            ENNReal.ofReal (Kc * (r⁻¹) ^ βn) *
              (holderXENorm noDriftWeight C.Xl C.dl (rhoBallOpen C ν (2 * r)) k α f +
                eLpNorm u ⊤ (volume.restrict (rhoBallOpen C ν (2 * r) : Set (Fin (n + m) → ℝ))))

/-- **The lifted higher Hölder estimate from the base
Hölder estimate**: for a chart whose frame data satisfy the P1 hypotheses (`HolderFrame`), `ν` smooth, a patch
`U_R^ρ ⊆ V` with `a = 1` there, and the lifted base Hölder estimate `LiftedBaseHolderEstimate` (no drift), the
estimate `LiftedHigherHolderEstimate` holds for every `k`. -/
theorem liftedHigherHolder_of_base (hH : HolderFrame C H K hQ F a) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) {R : ℝ} (hR : 0 < R)
    (hRV : rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) R ⊆ (F.V : Set (Fin (n + m) → ℝ)))
    (hRa : ∀ x ∈ rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) R, a x = 1)
    (hbase : LiftedBaseHolderEstimate C ν (noDriftOpWords q) α) :
    LiftedHigherHolderEstimate C ν α k := by
  classical
  have hw : ∀ j : Fin q, ((noDriftWeight j : ℕ+) : ℕ) = 1 := fun j => noDriftWeight_coe_eq_one j
  obtain ⟨r₀', hr₀', β, hβ, Cst, hCst, hb⟩ := hbase
  obtain ⟨r₁, E, hr₁, hE, p, hladder⟩ := ladder_claim hH ν hν hα0 hα1 k hR hRV hRa k le_rfl
  set βn₀ : ℕ := ⌈β⌉₊ with hβn₀
  refine ⟨min r₁ (min (r₀' / 2) 1), lt_min hr₁ (lt_min (by positivity) one_pos), p + βn₀,
    E * (1 + Cst) * ((k : ℝ) + 1) ^ (p + βn₀), by positivity, ?_⟩
  intro r hr hrr W hW u f hu hop hf
  have hr1 : r < r₁ := lt_of_lt_of_le hrr (min_le_left _ _)
  have hr2 : r < r₀' / 2 := lt_of_lt_of_le hrr ((min_le_right _ _).trans (min_le_left _ _))
  have hr3 : r < 1 := lt_of_lt_of_le hrr ((min_le_right _ _).trans (min_le_right _ _))
  set ξ₀ : Fin (n + m) → ℝ := joinPoint x₀ (0 : Fin m → ℝ) with hξ₀
  set Δ : ℝ := r / ((k : ℝ) + 1) with hΔ
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hΔ0 : 0 < Δ := by positivity
  have hΔ1 : Δ ≤ 1 := by
    have : Δ ≤ r := div_le_self hr.le (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    linarith
  set ρk : ℝ := ladderRadius k r k with hρk
  have hρk2 : ρk = 2 * r - Δ := by
    have := ladderRadius_succ k r k
    rw [ladderRadius_k1] at this
    linarith
  have hρk0 : 0 < ρk := ladderRadius_pos hr k
  have hρkle : ρk ≤ 2 * r := ladderRadius_le hr (by omega)
  set V₂ : Opens (Fin (n + m) → ℝ) := rhoBallOpen C ν ρk with hV₂
  set V₃ : Opens (Fin (n + m) → ℝ) := rhoBallOpen C ν (2 * r) with hV₃
  have hρ2r : rhoBall C ν ξ₀ ρk ⊆ rhoBall C ν ξ₀ (2 * r) := rhoBall_mono C ν _ hρkle
  have hV₃W : (V₃ : Set (Fin (n + m) → ℝ)) ⊆ (W : Set (Fin (n + m) → ℝ)) :=
    (rhoBall_subset_closed C ν ξ₀).trans hW
  have hV₂W : (V₂ : Set (Fin (n + m) → ℝ)) ⊆ (W : Set (Fin (n + m) → ℝ)) := hρ2r.trans hV₃W
  have hV₂U : (V₂ : Set (Fin (n + m) → ℝ)) ⊆ C.U := fun x hx => hx.1
  have hV₃U : (V₃ : Set (Fin (n + m) → ℝ)) ⊆ C.U := fun x hx => hx.1
  have hX₂ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V₂ : Set (Fin (n + m) → ℝ)) := fun i =>
    (C.lift_smooth i).mono (fun x hx => holderTransfer_U_subset_O C (hV₂U hx))
  have hX₃ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V₃ : Set (Fin (n + m) → ℝ)) := fun i =>
    (C.lift_smooth i).mono (fun x hx => holderTransfer_U_subset_O C (hV₃U hx))
  have hu₂ : memHolderX noDriftWeight C.Xl C.dl V₂ 2 α u := memHolderX_mono_domain noDriftWeight hV₂W hu
  have hf₃ : memHolderX noDriftWeight C.Xl C.dl V₃ k α f := memHolderX_mono_domain noDriftWeight hV₃W hf
  obtain ⟨D, hD0, hD⟩ := exists_selfJet_of_memHolderX hV₂U hX₂ hα0 hu₂
  obtain ⟨Df, hDf0, hDf⟩ := exists_selfJet_of_memHolderX hV₃U hX₃ hα0 hf₃
  have hDself : LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl V₂ 2 α (D []) D := by
    rw [hD0]; exact hD
  have hDfself : LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl V₃ k α (Df []) Df := by
    rw [hDf0]; exact hDf
  -- the operator relation
  have hop' := hop
  obtain ⟨g, hg, hgf⟩ := hop
  have hrel : ∀ x ∈ rhoBall C ν ξ₀ ρk, weakSumSquares D [] x = Df [] x := by
    intro x hx
    have hxW : x ∈ (W : Set (Fin (n + m) → ℝ)) := hV₂W hx
    have e1 : ∀ i : Fin q, g i x = D [i, i] x := fun i =>
      eqOn_jet_of_hasIntrinsicWordDeriv hV₂U hX₂ hα0 hu₂ hD
        (I := [i, i]) ((mem_wordFamily_iff_length hw).2 (by simp))
        (hasIntrinsicWordDeriv_mono (V := W) (V' := V₂) hV₂W _ (hg i)) hx
    have : weakSumSquares D [] x = ∑ i : Fin q, g i x := by
      simp only [weakSumSquares, List.nil_append, e1]
    rw [this, hgf x hxW, hDf0]
  obtain ⟨Dk, hDk, hrelk, hagr, hnorm⟩ := hladder r hr hr1 D Df hDself hDfself hrel
  have hl0 : ladderRadius k r (k - k) = r := by simp [ladderRadius]
  rw [hl0] at hDk hnorm hagr
  set V₀ : Opens (Fin (n + m) → ℝ) := rhoBallOpen C ν r with hV₀
  have hrr2 : rhoBall C ν ξ₀ r ⊆ rhoBall C ν ξ₀ (2 * r) := rhoBall_mono C ν _ (by linarith)
  have hV₀U : (V₀ : Set (Fin (n + m) → ℝ)) ⊆ C.U := fun x hx => hx.1
  have hX₀ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (V₀ : Set (Fin (n + m) → ℝ)) := fun i =>
    (C.lift_smooth i).mono (fun x hx => holderTransfer_U_subset_O C (hV₀U hx))
  have hDkNil : ∀ x ∈ (V₀ : Set (Fin (n + m) → ℝ)), Dk [] x = u x := fun x hx => by
    rw [hagr [] (by simp) x hx, hD0]
  have hDku : LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl V₀ (k + 2) α u Dk := by
    intro K' hK'
    refine ⟨S.hasWeakWordDeriv_congr_ae C.Xl V₀ (hDk K' hK').1 ?_ Filter.EventuallyEq.rfl,
      (hDk K' hK').2⟩
    rw [Filter.EventuallyEq, ae_restrict_iff' V₀.isOpen.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hDkNil x hx
  have hufin : holderENorm C.dl α (V₀ : Set (Fin (n + m) → ℝ)) u ≠ ⊤ := by
    have h1 := (hDk [] (S.nil_mem_wordFamily _ _)).2
    rw [S.holderENorm_congr C.dl α (V₀ : Set (Fin (n + m) → ℝ)) u (g := Dk [])
      (fun x hx => (hDkNil x hx).symm)]
    exact h1
  have hweakK : S.memWeakHolderX noDriftWeight C.Xl C.distanceGeometry.d V₀ (k + 2) α u :=
    ⟨lt_top_iff_ne_top.2 hufin, fun I hI =>
      ⟨Dk I, (hDku I hI).1, lt_top_iff_ne_top.2 (hDku I hI).2⟩⟩
  have hmem : memHolderX noDriftWeight C.Xl C.dl V₀ (k + 2) α u :=
    S.memHolderX_of_memWeakHolderX C.chartOpens V₀ C.distanceGeometry hV₀U noDriftWeight C.Xl hX₀
      (k + 2) hα0 hweakK
  refine ⟨hmem, ?_⟩
  rw [holderXENorm_eq_holderJetNorm hV₀U hX₀ hα0 hmem hDku]
  refine hnorm.trans ?_
  -- the base estimate on the inner ball
  have hb2 := hb ρk (2 * r) hρk0 (by rw [hρk2]; linarith) (by linarith) W hW u f hu hop'
  have e1 : holderJetNorm noDriftWeight C.dl (rhoBall C ν ξ₀ ρk) α 2 D =
      holderXENorm noDriftWeight C.Xl C.dl V₂ 2 α u :=
    (holderXENorm_eq_holderJetNorm hV₂U hX₂ hα0 hu₂ hD).symm
  have e2 : holderJetNorm noDriftWeight C.dl (rhoBall C ν ξ₀ (2 * r)) α k Df =
      holderXENorm noDriftWeight C.Xl C.dl V₃ k α f :=
    (holderXENorm_eq_holderJetNorm hV₃U hX₃ hα0 hf₃ hDf).symm
  rw [e1, e2]
  have hgap : 2 * r - ρk = Δ := by rw [hρk2]; ring
  rw [hgap] at hb2
  have hN0 : holderXENorm noDriftWeight C.Xl C.dl V₃ 0 α f ≤
      holderXENorm noDriftWeight C.Xl C.dl V₃ k α f := by
    unfold holderXENorm
    refine Finset.sum_le_sum_of_subset fun I hI => ?_
    rw [S.mem_wordFamily_iff] at hI ⊢
    omega
  have hβle : β ≤ (βn₀ : ℝ) := Nat.le_ceil β
  have hQ'1 : 1 ≤ (Δ⁻¹) ^ βn₀ := one_le_pow₀ ((one_le_inv₀ hΔ0).2 hΔ1)
  have hQ''1 : 1 ≤ (Δ⁻¹) ^ p := one_le_pow₀ ((one_le_inv₀ hΔ0).2 hΔ1)
  have hCb : Cst / Δ ^ β ≤ Cst * (Δ⁻¹) ^ βn₀ := by
    have h1 : Δ ^ (βn₀ : ℝ) ≤ Δ ^ β := Real.rpow_le_rpow_of_exponent_ge hΔ0 hΔ1 hβle
    have h2 : (Δ ^ β)⁻¹ ≤ (Δ ^ (βn₀ : ℝ))⁻¹ := inv_anti₀ (by positivity) h1
    have h3 : (Δ ^ (βn₀ : ℝ))⁻¹ = (Δ⁻¹) ^ βn₀ := by rw [Real.rpow_natCast, inv_pow]
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (h2.trans_eq h3) hCst.le
  set Nf := holderXENorm noDriftWeight C.Xl C.dl V₃ k α f with hNf
  set Nu := eLpNorm u ⊤ (volume.restrict (V₃ : Set (Fin (n + m) → ℝ))) with hNu
  have hJD2 : holderXENorm noDriftWeight C.Xl C.dl V₂ 2 α u ≤
      ENNReal.ofReal (Cst * (Δ⁻¹) ^ βn₀) * (Nf + Nu) :=
    hb2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hCb) (add_le_add hN0 le_rfl))
  have hmain := (mul_le_mul' (le_refl (ENNReal.ofReal (E * (Δ⁻¹) ^ p)))
    ((add_le_add (le_refl Nf) hJD2).trans (add_ofReal_mul_le hCst.le hQ'1 Nf Nu)))
  refine hmain.trans (le_of_eq ?_)
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have hΔinv : Δ⁻¹ = ((k : ℝ) + 1) * r⁻¹ := by
    rw [hΔ, inv_div, div_eq_mul_inv]
  rw [hΔinv, mul_pow, mul_pow, pow_add]
  ring

end Ladder

end RothschildStein.P2.HigherHolder
