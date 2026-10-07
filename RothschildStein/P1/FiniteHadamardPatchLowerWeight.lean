-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.HadamardJetLoss
public import RothschildStein.P1.FiniteHadamardExpansion
public import Mathlib.Algebra.BigOperators.Ring.List

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace RothschildStein.P1

variable {N : ℕ}

/-- The existing global Hadamard jet-loss
lemma applies separately at every endpoint in a patch by freezing the
parameter; no jets outside that patch are required. -/
theorem hadamardFactor_patch_weighted_jets_vanish {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (G : HomogeneousGroup N) (low : ℕ)
    (F : P × (Fin N → ℝ) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (K : Set P) (hjet : ∀ p ∈ K, ∀ I : List (Fin N),
      (I.map G.weight).sum < low → rsPartial I (fun u => F (p, u)) 0 = 0)
    (j : Fin N) :
    ∀ p ∈ K, ∀ I : List (Fin N), (I.map G.weight).sum < low - G.weight j →
      rsPartial I (fun u => ∫ t in Icc (0 : ℝ) 1,
        fderiv ℝ F (p, t • u) (0, Pi.single j 1)) 0 = 0 := by
  intro p hp I hI
  let A : P × (Fin N → ℝ) → ℝ := fun q => F (p, q.2)
  have hA : ContDiff ℝ (⊤ : ℕ∞) A :=
    hF.comp (contDiff_const.prodMk contDiff_snd)
  have hj : ∀ q : P, ∀ J : List (Fin N), (J.map G.weight).sum < low →
      rsPartial J (fun u => A (q, u)) 0 = 0 := fun _ J hJ => hjet p hp J hJ
  have he : (fun u => ∫ t in Icc (0 : ℝ) 1,
      fderiv ℝ F (p, t • u) (0, Pi.single j 1)) =
      (fun u => ∫ t in Icc (0 : ℝ) 1,
        fderiv ℝ A (p, t • u) (0, Pi.single j 1)) := by
    funext u
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change fderiv ℝ F (p, t • u) (0, Pi.single j 1) =
      fderiv ℝ A (p, t • u) (0, Pi.single j 1)
    rw [← rsPartial_single_generic_parameter F hF p (t • u) j,
      ← rsPartial_single_generic_parameter A hA p (t • u) j]
  rw [he]
  exact hadamardFactor_weighted_jets_vanish G low A hA hj j p I hI

/-- A finite Taylor decomposition with smooth
parameter coefficients and an explicit finite smooth Hadamard remainder.
Polynomial words have ordinary length below the chosen order; remainder
words have exactly that order. Lower weighted jets are needed only on
the endpoint patch K, and coefficients below that weight vanish there (BB Lemma 11.16, p. 548). -/
theorem exists_finite_hadamard_expansion_with_patch_lower_weight {P : Type} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [LocallyCompactSpace P] (G : HomogeneousGroup N) (K : Set P) :
    ∀ (b low : ℕ) (F : P × (Fin N → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F →
    (∀ p ∈ K, ∀ I : List (Fin N), (I.map G.weight).sum < low →
      rsPartial I (fun u => F (p, u)) 0 = 0) →
    ∃ poly : List (List (Fin N) × (P → ℝ)),
    ∃ rem : List (List (Fin N) × (P × (Fin N → ℝ) → ℝ)),
      (∀ q ∈ poly, q.1.length < b ∧ (low ≤ (q.1.map G.weight).sum ∨ ∀ p ∈ K, q.2 p = 0) ∧ ContDiff ℝ (⊤ : ℕ∞) q.2) ∧
      (∀ a ∈ rem, a.1.length = b ∧ ContDiff ℝ (⊤ : ℕ∞) a.2) ∧
      ∀ p u, F (p, u) =
        (poly.map (fun a => taylorWordMonomial a.1 u * a.2 p)).sum +
        (rem.map (fun a => taylorWordMonomial a.1 u * a.2 (p, u))).sum := by
  intro b
  induction b with
  | zero =>
    intro low F hF _hjet
    refine ⟨[], [([], F)], ?_, ?_, ?_⟩
    · simp only [List.not_mem_nil, false_implies, implies_true]
    · intro a ha
      obtain rfl := List.mem_singleton.mp ha
      exact ⟨rfl, hF⟩
    · intro p u
      simp only [List.map_nil, List.sum_nil, List.map_cons, List.sum_cons,
        taylorWordMonomial_nil, one_mul, add_zero, zero_add]
  | succ b ih =>
    intro low F hF hjet
    let H : Fin N → P × (Fin N → ℝ) → ℝ := fun j q =>
      ∫ t in Icc (0 : ℝ) 1, fderiv ℝ F (q.1, t • q.2) (0, Pi.single j 1)
    have hH : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (H j) :=
      fun j => hadamardFactor_generic_parameter_contDiff F hF j
    choose poly rem hp hr he using (fun j => ih (low - G.weight j) (H j) (hH j)
      (hadamardFactor_patch_weighted_jets_vanish G low F hF K hjet j))
    let js := List.finRange N
    let poly₁ := js.flatMap (fun j => (poly j).map (fun a => (j :: a.1, a.2)))
    let rem₁ := js.flatMap (fun j => (rem j).map (fun a => (j :: a.1, a.2)))
    refine ⟨([], fun p => F (p, 0)) :: poly₁, rem₁, ?_, ?_, ?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · subst a
        refine ⟨Nat.zero_lt_succ b, ?_, hF.comp (contDiff_id.prodMk contDiff_const)⟩
        by_cases ha : low = 0
        · exact Or.inl (by simp only [List.map_nil, List.sum_nil]; omega)
        · apply Or.inr
          intro p hp
          exact hjet p hp [] (by simp only [List.map_nil, List.sum_nil]; omega)
      · obtain ⟨j, _, ha⟩ := List.mem_flatMap.mp ha
        obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
        refine ⟨by simpa only [List.length_cons] using Nat.succ_lt_succ (hp j q hq).1,
          ?_, (hp j q hq).2.2⟩
        rcases (hp j q hq).2.1 with hw | hz
        · exact Or.inl (by simp only [List.map_cons, List.sum_cons]; omega)
        · exact Or.inr hz
    · intro a ha
      obtain ⟨j, _, ha⟩ := List.mem_flatMap.mp ha
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ha
      exact ⟨by simp only [List.length_cons, (hr j q hq).1], (hr j q hq).2⟩
    · intro p u
      have hpoly := taylor_prepend_flatMap_sum js poly (fun a => a p) u
      have hrem := taylor_prepend_flatMap_sum js rem (fun a => a (p, u)) u
      have hdec := hadamard_decomp_generic_parameter F hF p u
      have hs : (js.map (fun j => u j * H j (p, u))).sum =
          ∑ j, u j * H j (p, u) := by
        change ((List.finRange N).map (fun j => u j * H j (p, u))).sum = _
        simpa only [List.toFinset_finRange] using
          (List.sum_toFinset (fun j => u j * H j (p, u)) (List.nodup_finRange N)).symm
      have hsum : (js.map (fun j => u j * H j (p, u))).sum =
          (js.map (fun j => u j * (poly j |>.map
            (fun a => taylorWordMonomial a.1 u * a.2 p)).sum)).sum +
          (js.map (fun j => u j * (rem j |>.map
            (fun a => taylorWordMonomial a.1 u * a.2 (p, u))).sum)).sum := by
        simp_rw [he, mul_add]
        rw [List.sum_map_add]
      simp only [List.map_cons, List.sum_cons, taylorWordMonomial_nil, one_mul]
      change F (p, u) = F (p, 0) +
        (poly₁.map (fun a => taylorWordMonomial a.1 u * a.2 p)).sum +
        (rem₁.map (fun a => taylorWordMonomial a.1 u * a.2 (p, u))).sum
      rw [hpoly, hrem, add_assoc, ← hsum, hs]
      linarith

end RothschildStein.P1
