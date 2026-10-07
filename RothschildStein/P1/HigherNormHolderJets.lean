-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.HigherNormOperators
public import RothschildStein.S.SobolevZeroAE

/-!
# Higher-order gain, Hölder part: the commuted jets of `S f`

Without drift let `S = ∑ⱼ Tⱼ` (`Tⱼ = X̃ⱼ Fⱼ` of type 0, `Fⱼ` of type 1) and let `f` be in the closure
space `W^{k,2}_{X̃,0}(V)` with a weak jet `D J` (`J` in the family of order `k`) of finite Hölder norm
(`D [] = f`; e.g. a compactly supported `C^{k,α}_{X̃}(V)` function, by BB Prop 2.22 and the inclusion `C^{k,α}_{X̃,0} ⊂ W^{k,p}_{X̃,0}`). The commuted
identity of `HigherNormClosure` at `P = 2`, together with the agreement of the `L^2` and pointwise
realizations on Hölder inputs (continuity theorem), gives:

* `hasWeakWordDeriv_commuted_holder`: `X̃_I (S f) = ∑_{|J| ≤ |I|} ∑_{T ∈ S_{I,J}} T (D J)` weakly on `V`
  with the **pointwise actions** `T.apply` on the Hölder jet;
* `exists_holder_commuted_jets`: these weak derivatives are continuous on `V` and bounded in the
  Hölder norm `‖X̃_I (S f)‖_{C^α(V)} ≤ c_I ∑_{|J| ≤ k} ‖D J‖_{C^α(V)}` (the Hölder continuity of each
  type-0 operator), with `c_I` independent of `f` (the sum of the Hölder constants of the finitely many
  operators of the commuted family).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

section HolderSums

variable {n' : ℕ} {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ} {V : Set (Fin n' → ℝ)}
  {ι : Type*}

/-- The Hölder norm of a finite sum of terms `ap a` bounded by `c a · M` is at most
`(∑ c a) · M`. -/
theorem holderENorm_finsetSum_le_mul (hα : 0 ≤ α) (ap : ι → (Fin n' → ℝ) → ℝ) {M : ℝ≥0∞}
    (c : ι → ℝ) (s : Finset ι) (hc : ∀ a ∈ s, 0 ≤ c a)
    (hb : ∀ a ∈ s, holderENorm d α V (ap a) ≤ ENNReal.ofReal (c a) * M) :
    holderENorm d α V (fun ξ => ∑ a ∈ s, ap a ξ) ≤ ENNReal.ofReal (∑ a ∈ s, c a) * M := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [holderENorm_zero]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have hs : 0 ≤ ∑ b ∈ s, c b := Finset.sum_nonneg fun b hb' => hc b (Finset.mem_insert_of_mem hb')
    calc holderENorm d α V (fun ξ => ap a ξ + ∑ b ∈ s, ap b ξ)
        ≤ holderENorm d α V (ap a) + holderENorm d α V (fun ξ => ∑ b ∈ s, ap b ξ) :=
          holderENorm_add_le hα _ _
      _ ≤ ENNReal.ofReal (c a) * M + ENNReal.ofReal (∑ b ∈ s, c b) * M :=
          add_le_add (hb a (Finset.mem_insert_self a s))
            (ih (fun b hb' => hc b (Finset.mem_insert_of_mem hb'))
              (fun b hb' => hb b (Finset.mem_insert_of_mem hb')))
      _ = ENNReal.ofReal (c a + ∑ b ∈ s, c b) * M := by
          rw [ENNReal.ofReal_add (hc a (Finset.mem_insert_self a s)) hs, add_mul]

end HolderSums

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q : ℕ} {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {lam : ℕ}

end LiftedChart

end RothschildStein.P1
