-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-!
# Hölder interpolation: jets of kernels on `ℝ^N × ℝ^N`

Support file for the far part of the first interpolation inequality (BB pp. 594-595, Lem 11.51).
A kernel `H(ξ, η)` that is `C³` on `ℝ^N × ℝ^N` is controlled by its **jets**: the sup of the
operator norms of `iteratedFDeriv ℝ j H` for `j ≤ 3` (`JetSup`). From them the coordinate partial
derivatives that appear after one integration by parts in `η` (two `η`-derivatives of `H`, and one
further `ξ`-derivative) are bounded (`JetSup.jets`), and the `ξ`-Lipschitz constants of the
functions `H`, `∂_{η_a} H`, `∂_{η_b} ∂_{η_a} H` follow (`lipX_of_coord_bound`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
namespace RothschildStein.P2

section Dir

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Nested directional derivatives: `dirDeriv [v₁, v₂] f p = D(D f(·) v₂)(p) v₁`. -/
def dirDeriv (vs : List E) (f : E → ℝ) : E → ℝ :=
  vs.foldr (fun v g => fun p => fderiv ℝ g p v) f

@[simp] theorem dirDeriv_nil (f : E → ℝ) : dirDeriv [] f = f := rfl

theorem dirDeriv_cons (v : E) (vs : List E) (f : E → ℝ) :
    dirDeriv (v :: vs) f = fun p => fderiv ℝ (dirDeriv vs f) p v := rfl

/-- A directional derivative of a `C^{n+1}` function is `C^n`. -/
theorem contDiff_dirDeriv {n : ℕ} :
    ∀ (vs : List E) (f : E → ℝ), ContDiff ℝ ((n + vs.length : ℕ) : WithTop ℕ∞) f →
      ContDiff ℝ (n : WithTop ℕ∞) (dirDeriv vs f) := by
  intro vs
  induction vs generalizing n with
  | nil => intro f hf; simpa using hf
  | cons v vs ih =>
    intro f hf
    have h1 : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (dirDeriv vs f) :=
      ih f (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hf)
    rw [dirDeriv_cons]
    exact (h1.fderiv_right (by push_cast; exact le_rfl)).clm_apply contDiff_const

/-- `D^k` of a directional derivative is controlled by `D^{k+1}`. -/
theorem norm_iteratedFDeriv_fderiv_apply_le {f : E → ℝ} {k : ℕ}
    (hf : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) f) (v : E) (x : E) :
    ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ f y v) x‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (k + 1) f x‖ := by
  have hd : ContDiffAt ℝ (k : WithTop ℕ∞) (fderiv ℝ f) x :=
    (hf.fderiv_right (by push_cast; exact le_rfl)).contDiffAt
  have h1 : (fun y => fderiv ℝ f y v) = (ContinuousLinearMap.apply ℝ ℝ v) ∘ (fderiv ℝ f) := rfl
  rw [h1, ContinuousLinearMap.iteratedFDeriv_comp_left _ hd le_rfl]
  have hL : ‖ContinuousLinearMap.apply ℝ ℝ v‖ ≤ ‖v‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) (fun L => by
      simpa [mul_comm] using L.le_opNorm v)
  calc _ ≤ ‖ContinuousLinearMap.apply ℝ ℝ v‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ f) x‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (k + 1) f x‖ := by
        rw [norm_iteratedFDeriv_fderiv]
        exact mul_le_mul_of_nonneg_right hL (norm_nonneg _)

/-- A nested directional derivative of order `|vs|` is bounded by the `|vs|`-th iterated
derivative times the product of the norms of the directions. -/
theorem norm_iteratedFDeriv_dirDeriv_le {k : ℕ} :
    ∀ (vs : List E) (f : E → ℝ), ContDiff ℝ ((k + vs.length : ℕ) : WithTop ℕ∞) f → ∀ x : E,
      ‖iteratedFDeriv ℝ k (dirDeriv vs f) x‖ ≤
        (vs.map (fun v => ‖v‖)).prod * ‖iteratedFDeriv ℝ (k + vs.length) f x‖ := by
  intro vs
  induction vs generalizing k with
  | nil => intro f hf x; simp
  | cons v vs ih =>
    intro f hf x
    have hg : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (dirDeriv vs f) :=
      contDiff_dirDeriv vs f (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hf)
    rw [dirDeriv_cons]
    have h1 := norm_iteratedFDeriv_fderiv_apply_le hg v x
    have h2 := ih (k := k + 1) f (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hf) x
    have e : k + 1 + vs.length = k + (v :: vs).length := by simp [List.length_cons]; omega
    rw [e] at h2
    calc _ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (k + 1) (dirDeriv vs f) x‖ := h1
      _ ≤ ‖v‖ * ((vs.map (fun v => ‖v‖)).prod * ‖iteratedFDeriv ℝ (k + (v :: vs).length) f x‖) :=
          mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
      _ = _ := by simp [List.map_cons, List.prod_cons, mul_assoc]

/-- Pointwise form: `|dirDeriv vs f x| ≤ (∏ ‖v‖) ‖D^{|vs|} f x‖` (case `k = 0`). -/
theorem abs_dirDeriv_le {vs : List E} {f : E → ℝ}
    (hf : ContDiff ℝ (vs.length : WithTop ℕ∞) f) (x : E) :
    |dirDeriv vs f x| ≤ (vs.map (fun v => ‖v‖)).prod * ‖iteratedFDeriv ℝ vs.length f x‖ := by
  have h := norm_iteratedFDeriv_dirDeriv_le (k := 0) vs f (by simpa using hf) x
  rw [Nat.zero_add] at h
  simpa [norm_iteratedFDeriv_zero] using h

end Dir

section Jets

variable {N : ℕ}

/-- The function space `ℝ^N × ℝ^N` of kernels `H(ξ, η)`. -/
abbrev E2 (N : ℕ) : Type := (Fin N → ℝ) × (Fin N → ℝ)

/-- The `η`-direction `e ∈ ℝ^N` in `ℝ^N × ℝ^N`. -/
def dirEta (e : Fin N → ℝ) : E2 N := (0, e)

/-- The `ξ`-direction `e ∈ ℝ^N` in `ℝ^N × ℝ^N`. -/
def dirXi (e : Fin N → ℝ) : E2 N := (e, 0)

theorem norm_dirEta (e : Fin N → ℝ) : ‖dirEta e‖ = ‖e‖ := by simp [dirEta]

theorem norm_dirXi (e : Fin N → ℝ) : ‖dirXi e‖ = ‖e‖ := by simp [dirXi]

/-- The coordinate vector `e_a`. -/
abbrev unitVec (a : Fin N) : Fin N → ℝ := Pi.single a 1

theorem norm_unitVec (a : Fin N) : ‖(unitVec a : Fin N → ℝ)‖ = 1 := by
  simp [unitVec, Pi.norm_single]

/-- The `η`-partial derivative `∂_{η_a} H`. -/
def etaPartial (a : Fin N) (H : E2 N → ℝ) : E2 N → ℝ := dirDeriv [dirEta (unitVec a)] H

/-- The second `η`-partial derivative `∂_{η_b} ∂_{η_a} H`. -/
def etaPartial₂ (a b : Fin N) (H : E2 N → ℝ) : E2 N → ℝ :=
  dirDeriv [dirEta (unitVec b), dirEta (unitVec a)] H

/-- The `ξ`-partial derivative `∂_{ξ_m} g`. -/
def xiPartial (m : Fin N) (g : E2 N → ℝ) : E2 N → ℝ := dirDeriv [dirXi (unitVec m)] g

/-- **Jet bound of a kernel**: `H` is `C³` and the iterated derivatives of order `≤ 3`
are bounded by `B`. -/
structure JetSup (H : E2 N → ℝ) (B : ℝ) : Prop where
  contDiff : ContDiff ℝ 3 H
  bound : ∀ j : ℕ, j ≤ 3 → ∀ p, ‖iteratedFDeriv ℝ j H p‖ ≤ B

theorem JetSup.nonneg {H : E2 N → ℝ} {B : ℝ} (h : JetSup H B) : 0 ≤ B :=
  (norm_nonneg _).trans (h.bound 0 (by norm_num) 0)

/-- The coordinate jets of order `≤ 3` of a `JetSup` kernel: the quantities which occur after
one integration by parts in `η` and one `ξ`-derivative. -/
theorem JetSup.jets {H : E2 N → ℝ} {B : ℝ} (h : JetSup H B) (p : E2 N) :
    |H p| ≤ B ∧
    (∀ a, |etaPartial a H p| ≤ B) ∧
    (∀ a b, |etaPartial₂ a b H p| ≤ B) ∧
    (∀ m, |xiPartial m H p| ≤ B) ∧
    (∀ m a, |xiPartial m (etaPartial a H) p| ≤ B) ∧
    (∀ m a b, |xiPartial m (etaPartial₂ a b H) p| ≤ B) := by
  have hc : ∀ n : ℕ, n ≤ 3 → ContDiff ℝ (n : WithTop ℕ∞) H := fun n hn =>
    h.contDiff.of_le (by exact_mod_cast hn)
  refine ⟨?_, fun a => ?_, fun a b => ?_, fun m => ?_, fun m a => ?_, fun m a b => ?_⟩
  · simpa [norm_iteratedFDeriv_zero] using h.bound 0 (by norm_num) p
  · have := abs_dirDeriv_le (vs := [dirEta (unitVec a)]) (f := H) (by simpa using hc 1 (by norm_num)) p
    simp only [norm_dirEta, norm_unitVec, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, one_mul, List.length_cons, List.length_nil] at this
    exact this.trans (by simpa using h.bound 1 (by norm_num) p)
  · have := abs_dirDeriv_le (vs := [dirEta (unitVec b), dirEta (unitVec a)]) (f := H)
      (by simpa using hc 2 (by norm_num)) p
    simp only [norm_dirEta, norm_unitVec, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, one_mul, List.length_cons, List.length_nil] at this
    exact this.trans (by simpa using h.bound 2 (by norm_num) p)
  · have := abs_dirDeriv_le (vs := [dirXi (unitVec m)]) (f := H) (by simpa using hc 1 (by norm_num)) p
    simp only [norm_dirXi, norm_unitVec, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, one_mul, List.length_cons, List.length_nil] at this
    exact this.trans (by simpa using h.bound 1 (by norm_num) p)
  · have hh : xiPartial m (etaPartial a H) = dirDeriv [dirXi (unitVec m), dirEta (unitVec a)] H := rfl
    rw [hh]
    have := abs_dirDeriv_le (vs := [dirXi (unitVec m), dirEta (unitVec a)]) (f := H)
      (by simpa using hc 2 (by norm_num)) p
    simp only [norm_dirXi, norm_dirEta, norm_unitVec, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, one_mul, List.length_cons, List.length_nil] at this
    exact this.trans (by simpa using h.bound 2 (by norm_num) p)
  · have hh : xiPartial m (etaPartial₂ a b H) =
        dirDeriv [dirXi (unitVec m), dirEta (unitVec b), dirEta (unitVec a)] H := rfl
    rw [hh]
    have := abs_dirDeriv_le (vs := [dirXi (unitVec m), dirEta (unitVec b), dirEta (unitVec a)])
      (f := H) (by simpa using hc 3 (by norm_num)) p
    simp only [norm_dirXi, norm_dirEta, norm_unitVec, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, one_mul, List.length_cons, List.length_nil] at this
    exact this.trans (by simpa using h.bound 3 (by norm_num) p)

theorem sum_unitVec_smul (w : Fin N → ℝ) : ∑ m, w m • (unitVec m : Fin N → ℝ) = w := by
  ext j
  simp [unitVec, Pi.single_apply]

/-- A coordinate-wise bound on the `ξ`-partials of a `C¹` function on `ℝ^N × ℝ^N` is a
Lipschitz bound in `ξ`, with constant `N B`. -/
theorem lipX_of_coord_bound {g : E2 N → ℝ} {B : ℝ} (hg : ContDiff ℝ 1 g)
    (hB : ∀ p m, |xiPartial m g p| ≤ B) (ξ ξ' η : Fin N → ℝ) :
    |g (ξ, η) - g (ξ', η)| ≤ N * B * ‖ξ - ξ'‖ := by
  have hNB : 0 ≤ (N : ℝ) * B := by
    rcases Nat.eq_zero_or_pos N with h | h
    · simp [h]
    · exact mul_nonneg (Nat.cast_nonneg _) ((abs_nonneg _).trans (hB (ξ, η) ⟨0, h⟩))
  have hdiff : ∀ x : Fin N → ℝ, HasFDerivAt (fun x : Fin N → ℝ => g (x, η))
      ((fderiv ℝ g (x, η)).comp ((ContinuousLinearMap.id ℝ (Fin N → ℝ)).prod 0)) x := by
    intro x
    have h1 : HasFDerivAt (fun x : Fin N → ℝ => (x, η))
        ((ContinuousLinearMap.id ℝ (Fin N → ℝ)).prod (0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_const η x)
    exact (hg.differentiable (by norm_num) (x, η)).hasFDerivAt.comp x h1
  have hbound : ∀ x : Fin N → ℝ,
      ‖(fderiv ℝ g (x, η)).comp ((ContinuousLinearMap.id ℝ (Fin N → ℝ)).prod 0)‖ ≤ N * B := by
    intro x
    refine ContinuousLinearMap.opNorm_le_bound _ hNB (fun w => ?_)
    have hw : ((ContinuousLinearMap.id ℝ (Fin N → ℝ)).prod
        (0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))) w = ∑ m, w m • dirXi (unitVec m) := by
      ext j
      · simp [dirXi, Prod.fst_sum, unitVec, Pi.single_apply]
      · simp [dirXi, Prod.snd_sum]
    rw [ContinuousLinearMap.comp_apply, hw, map_sum, Real.norm_eq_abs]
    calc |∑ m, fderiv ℝ g (x, η) (w m • dirXi (unitVec m))|
        ≤ ∑ m, |fderiv ℝ g (x, η) (w m • dirXi (unitVec m))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _m : Fin N, B * ‖w‖ := by
          refine Finset.sum_le_sum (fun m _ => ?_)
          rw [map_smul, smul_eq_mul, abs_mul]
          have h1 : |w m| ≤ ‖w‖ := by simpa using norm_le_pi_norm w m
          have h2 : |fderiv ℝ g (x, η) (dirXi (unitVec m))| ≤ B := hB (x, η) m
          calc |w m| * |fderiv ℝ g (x, η) (dirXi (unitVec m))| ≤ ‖w‖ * B :=
                mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
            _ = B * ‖w‖ := mul_comm _ _
      _ = N * B * ‖w‖ := by simp [Finset.sum_const, mul_assoc]
  have := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (𝕜 := ℝ)
    (f := fun x : Fin N → ℝ => g (x, η)) (s := Set.univ) (C := (N : ℝ) * B)
    (fun x _ => (hdiff x).hasFDerivWithinAt) (fun x _ => hbound x) convex_univ
    (Set.mem_univ ξ') (Set.mem_univ ξ)
  simpa [Real.norm_eq_abs, norm_sub_rev] using this

end Jets

end RothschildStein.P2
