-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HigherHolderLeibniz
public import RothschildStein.P2.Cutoffs
public import RothschildStein.P2.CutoffsHolder
public import RothschildStein.P2.TransferCoverCore
public import RothschildStein.P2.ProductAbsorptionWeak
public import RothschildStein.P1.ParametrixKernelBoundsNoDriftRight

/-!
# One step of the cutoff recurrence

Part of the higher Hölder estimate (BB p. 604, (11.94)–(11.96): cutoff multiplication has finite loss in
`r⁻¹` by the radial cutoff construction;
"each product expansion is `L̃(ζ u) = ζ L̃u + 2 ∑ᵢ (X̃ᵢζ)(X̃ᵢu) + u L̃ζ`; no derivative of `L̃ζ` replaces `X̃ᵢζ`
in its middle term"). One step of the recurrence of the doubled-ball estimate and of the regularity induction.

For a lifted no-drift chart, the radial cutoff `ζ = φ(s, r)` of the radial cutoff construction (`ζ = 1` on `U_s^ρ`, supported in `U_r^ρ`),
a Hölder weak jet `D` of order `j' + 2` of `D []` on `U_r^ρ` and a Hölder weak jet `Df` of order `j' + 1` of
`Df [] = L̃ (D []) = ∑ᵢ D [i, i]` on `U_r^ρ`:

* `v = ζ D []` (zero outside `U_r^ρ`) has the Leibniz jet `Dv = leibJet` (order `j' + 2`) and `L̃ v` the
  jet `forcingJet` (order `j' + 1`) of `ζ Df [] + ∑ᵢ (2 X̃ᵢζ X̃ᵢ D [] + D [] X̃ᵢ² ζ)`, both on the patch of the frame,
  with norms controlled by `c (r - s)^{-(j'+4)}` times the norms on `U_r^ρ` (`holderJetNorm_leibJet_le`);
* the compact recurrence with regularity (`compact_regularity`) gives a Hölder weak jet of `v` of order `j' + 3`
  with `‖v‖_{C^{j'+3,α}} ≤ Λ (‖L̃ v‖_{C^{j'+1,α}} + ‖v‖_{C^{j'+2,α}})`; on `U_s^ρ`, where `ζ = 1`, it is a jet
  of `D []` (`stage_step`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2.HigherHolder

open RothschildStein.P1

section Forcing

variable {n' q : ℕ} {X : Fin q → (Fin n' → ℝ) → (Fin n' → ℝ)}

/-- A jet of a function with weak jet `D` is shifted: `D (J ++ τ)` is the weak `X_J`-derivative of
`D τ` (only the weak parts of the jet are used). -/
theorem jet_append {w : Fin q → ℕ+} {V : Opens (Fin n' → ℝ)}
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n' → ℝ))) {kk : ℕ}
    {u : (Fin n' → ℝ) → ℝ} {D : List (Fin q) → (Fin n' → ℝ) → ℝ}
    (hD : ∀ K ∈ wordFamily w kk, hasWeakWordDeriv X V K u (D K)) (τ : List (Fin q)) :
    ∀ J : List (Fin q), J ++ τ ∈ wordFamily w kk → hasWeakWordDeriv X V J (D τ) (D (J ++ τ))
  | [], h => S.hasWeakWordDeriv_nil X V (hD τ (by simpa using h)).2.1
  | j :: J', h => by
    have hm : J' ++ τ ∈ wordFamily w kk :=
      S.sublist_mem_wordFamily w kk
        (List.Sublist.append (List.sublist_cons_self j J') (List.Sublist.refl τ)) h
    have ih := jet_append hXt hD τ J' hm
    have hu' := hD (J' ++ τ) hm
    have hfull := hD (j :: J' ++ τ) h
    have hone := (S.hasWeakWordDeriv_cons_iff X V hXt hu' j).mp hfull
    exact (S.hasWeakWordDeriv_cons_iff X V hXt ih j).mpr hone

/-- Finite sums of weak derivatives on an arbitrary open set. -/
theorem hasWeakWordDeriv_sum_finset {V : Opens (Fin n' → ℝ)}
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n' → ℝ))) (I : List (Fin q)) {ι : Type*}
    (s : Finset ι) (f g : ι → (Fin n' → ℝ) → ℝ)
    (h : ∀ a ∈ s, hasWeakWordDeriv X V I (f a) (g a)) :
    hasWeakWordDeriv X V I (fun x => ∑ a ∈ s, f a x) (fun x => ∑ a ∈ s, g a x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using S.hasWeakWordDeriv_zero X V I
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact S.hasWeakWordDeriv_add X V hXt (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

/-- The jet of `L̃ (ζ u) = ζ L̃u + ∑ᵢ (2 X̃ᵢζ X̃ᵢu + u X̃ᵢ²ζ)` (BB p. 604;
product expansion), built from the Leibniz jets of the three products, zero outside `B`. -/
def forcingJet (X : Fin q → (Fin n' → ℝ) → (Fin n' → ℝ)) (B : Set (Fin n' → ℝ))
    (ζ : (Fin n' → ℝ) → ℝ) (Du Df : List (Fin q) → (Fin n' → ℝ) → ℝ) :
    List (Fin q) → (Fin n' → ℝ) → ℝ :=
  fun K x => leibJet X B ζ Df K x +
    ∑ i : Fin q, (leibJet X B (fieldDerivative (X i) ζ) (fun K' => Du (K' ++ [i])) K x +
      leibJet X B (fieldDerivative (X i) ζ) (fun K' => Du (K' ++ [i])) K x +
      leibJet X B (fieldDerivative (X i) (fieldDerivative (X i) ζ)) Du K x)

theorem forcingJet_nil (B : Set (Fin n' → ℝ)) (ζ : (Fin n' → ℝ) → ℝ)
    (Du Df : List (Fin q) → (Fin n' → ℝ) → ℝ) :
    forcingJet X B ζ Du Df [] =
      B.indicator (fun x => Df [] x * ζ x + ∑ i : Fin q, (Du [i] x * fieldDerivative (X i) ζ x +
        Du [i] x * fieldDerivative (X i) ζ x +
        Du [] x * fieldDerivative (X i) (fieldDerivative (X i) ζ) x)) := by
  funext x
  unfold forcingJet
  simp only [leibJet_nil]
  by_cases hx : x ∈ B
  · simp [Set.indicator_of_mem hx]
  · simp [Set.indicator_of_notMem hx]

theorem leibnizWordValue_pair (D : List (Fin q) → (Fin n' → ℝ) → ℝ) (ζ : (Fin n' → ℝ) → ℝ)
    (i : Fin q) (x : Fin n' → ℝ) :
    S.leibnizWordValue X [i, i] D ζ x = D [i, i] x * ζ x + D [i] x * fieldDerivative (X i) ζ x +
      D [i] x * fieldDerivative (X i) ζ x +
        D [] x * fieldDerivative (X i) (fieldDerivative (X i) ζ) x := by
  simp [S.leibnizWordValue, S.leibnizSplits, wordDerivative]
  ring

/-- **`L̃ (ζ u)` for the Leibniz jets**: `∑ᵢ (D ζ) [i, i] = forcingJet []`, when `L̃ D = Df []`
on `B`. -/
theorem weakSumSquares_leibJet (B : Set (Fin n' → ℝ)) (ζ : (Fin n' → ℝ) → ℝ)
    (Du Df : List (Fin q) → (Fin n' → ℝ) → ℝ)
    (hrel : ∀ x ∈ B, weakSumSquares Du [] x = Df [] x) (x : Fin n' → ℝ) :
    weakSumSquares (leibJet X B ζ Du) [] x = forcingJet X B ζ Du Df [] x := by
  rw [forcingJet_nil]
  by_cases hx : x ∈ B
  · simp only [weakSumSquares, List.nil_append, leibJet, Set.indicator_of_mem hx,
      leibnizWordValue_pair]
    have h1 : (∑ i : Fin q, Du [i, i] x) = Df [] x := by
      have := hrel x hx
      simpa [weakSumSquares] using this
    calc ∑ i : Fin q, (Du [i, i] x * ζ x + Du [i] x * fieldDerivative (X i) ζ x +
          Du [i] x * fieldDerivative (X i) ζ x +
          Du [] x * fieldDerivative (X i) (fieldDerivative (X i) ζ) x)
        = (∑ i : Fin q, Du [i, i] x) * ζ x + ∑ i : Fin q, (Du [i] x * fieldDerivative (X i) ζ x +
          Du [i] x * fieldDerivative (X i) ζ x +
          Du [] x * fieldDerivative (X i) (fieldDerivative (X i) ζ) x) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by rw [h1]
  · simp [weakSumSquares, leibJet, Set.indicator_of_notMem hx]

/-- The weak jet of the forcing term. -/
theorem hasWeakWordDeriv_forcingJet {V B : Opens (Fin n' → ℝ)} (hBV : (B : Set (Fin n' → ℝ)) ⊆ V)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n' → ℝ))) {ζ : (Fin n' → ℝ) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζ1 : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (X i) ζ))
    (hζ2 : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (X i) (fieldDerivative (X i) ζ)))
    {K₀ : Set (Fin n' → ℝ)} (hK₀ : IsCompact K₀) (hK₀B : K₀ ⊆ (B : Set (Fin n' → ℝ)))
    (hζ0 : ∀ z, z ∉ K₀ → ζ z = 0) (hζ10 : ∀ i z, z ∉ K₀ → fieldDerivative (X i) ζ z = 0)
    (hζ20 : ∀ i z, z ∉ K₀ → fieldDerivative (X i) (fieldDerivative (X i) ζ) z = 0)
    {Du Df : List (Fin q) → (Fin n' → ℝ) → ℝ} (K : List (Fin q))
    (hDu : ∀ J, J.Sublist K → hasWeakWordDeriv X B J (Du []) (Du J))
    (hDu' : ∀ i J, J.Sublist K → hasWeakWordDeriv X B J (Du [i]) (Du (J ++ [i])))
    (hDf : ∀ J, J.Sublist K → hasWeakWordDeriv X B J (Df []) (Df J)) :
    hasWeakWordDeriv X V K (forcingJet X B ζ Du Df []) (forcingJet X B ζ Du Df K) := by
  have h1 := hasWeakWordDeriv_leibJet hBV hX hζ hK₀ hK₀B hζ0 (D := Df) K hDf
  have h2 : ∀ i : Fin q, hasWeakWordDeriv X V K
      ((B : Set (Fin n' → ℝ)).indicator (fun x => Du [i] x * fieldDerivative (X i) ζ x))
      (leibJet X B (fieldDerivative (X i) ζ) (fun K' => Du (K' ++ [i])) K) := fun i =>
    hasWeakWordDeriv_leibJet hBV hX (hζ1 i) hK₀ hK₀B (hζ10 i) (D := fun K' => Du (K' ++ [i])) K
      (fun J hJ => hDu' i J hJ)
  have h3 : ∀ i : Fin q, hasWeakWordDeriv X V K
      ((B : Set (Fin n' → ℝ)).indicator
        (fun x => Du [] x * fieldDerivative (X i) (fieldDerivative (X i) ζ) x))
      (leibJet X B (fieldDerivative (X i) (fieldDerivative (X i) ζ)) Du K) := fun i =>
    hasWeakWordDeriv_leibJet hBV hX (hζ2 i) hK₀ hK₀B (hζ20 i) (D := Du) K hDu
  have hsum := S.hasWeakWordDeriv_add X V hX h1
    (hasWeakWordDeriv_sum_finset hX K Finset.univ _ _ fun i _ =>
      S.hasWeakWordDeriv_add X V hX (S.hasWeakWordDeriv_add X V hX (h2 i) (h2 i)) (h3 i))
  have e : forcingJet X B ζ Du Df [] = fun x =>
      (B : Set (Fin n' → ℝ)).indicator (fun x => Df [] x * ζ x) x +
        ∑ i : Fin q, (((B : Set (Fin n' → ℝ)).indicator
            (fun x => Du [i] x * fieldDerivative (X i) ζ x) x +
          (B : Set (Fin n' → ℝ)).indicator (fun x => Du [i] x * fieldDerivative (X i) ζ x) x) +
          (B : Set (Fin n' → ℝ)).indicator
            (fun x => Du [] x * fieldDerivative (X i) (fieldDerivative (X i) ζ) x) x) := by
    funext x
    unfold forcingJet
    simp only [leibJet_nil]
    rfl
  rw [e]
  exact hsum

end Forcing

end RothschildStein.P2.HigherHolder
