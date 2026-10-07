-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedJetClasses
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace RothschildStein.L1

/-- Distribute each ordered derivative to one of the two product factors.
Repeated partitions are retained, so multiplicities are exact. -/
def jetLeibnizPartitions {ι : Type*} : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | j :: J => (jetLeibnizPartitions J).map (fun q => (j :: q.1, q.2)) ++
      (jetLeibnizPartitions J).map (fun q => (q.1, j :: q.2))

/-- Every term preserves both total ordinary order and total weight. -/
theorem jetLeibnizPartitions_order_weight {ι : Type*} (ω : ι → ℕ)
    (J : List ι) : ∀ q ∈ jetLeibnizPartitions J,
      q.1.length + q.2.length = J.length ∧
      (q.1.map ω).sum + (q.2.map ω).sum = (J.map ω).sum := by
  induction J with
  | nil => intro q hq; simp only [jetLeibnizPartitions, List.mem_singleton] at hq; subst q; simp
  | cons j J ih =>
    intro q hq
    simp only [jetLeibnizPartitions, List.mem_append, List.mem_map] at hq
    rcases hq with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨hl, hw⟩ := ih q hq
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      constructor <;> omega
    · obtain ⟨hl, hw⟩ := ih q hq
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      constructor <;> omega
end RothschildStein.L1
