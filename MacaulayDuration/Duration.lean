/-
Copyright (c) 2023 Quinn Culver. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quinn Culver
-/
import Mathlib
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.ContDiff.Defs



set_option maxHeartbeats 0

open BigOperators

structure CashFlow :=
  time : NNReal
  amount : ℝ

def CashFlowSeries := List CashFlow

variable (cf : CashFlow)
variable (cfs : CashFlowSeries)
variable (i i₀ : NNReal) --interest rate

-- Define a function to calculate the present value of a single cash flow
noncomputable def presentValueCF : ℝ :=
  cf.amount / (1 + i) ^ (cf.time : ℝ)

-- Define a recursive function to calculate the present value of a series of cash flows
noncomputable def presentValueCFSeries : (cfs : CashFlowSeries) → (i : NNReal) → ℝ
| [], _ => 0
| (cf :: cfsTail), i => presentValueCF cf i + presentValueCFSeries cfsTail i

-- Define the derivative of present value of a single cash flow
noncomputable def presentValueCFDeriv : ℝ :=
  -(cf.time) * cf.amount / (1 + i) ^ ((cf.time : ℝ) + 1)

-- Define the derivative of present value of a series of cash flows
noncomputable def presentValueCFSeriesDeriv : CashFlowSeries → NNReal → ℝ
| [], _ => 0
| (cf :: cfsTail), i => presentValueCFDeriv cf i + presentValueCFSeriesDeriv cfsTail i

-- Define modified duration
noncomputable def modifiedDuration : ℝ :=
  -(presentValueCFSeriesDeriv cfs i / presentValueCFSeries cfs i)

-- Define Macaulay duration
noncomputable def macaulayDuration : ℝ :=
  (1 + i) * modifiedDuration cfs i

open Filter Asymptotics Topology

lemma firstOrderTaylorApprox :
  (λ (i: NNReal) => presentValueCFSeries cfs i - (presentValueCFSeries cfs i₀ + presentValueCFSeriesDeriv cfs i₀ * (i - i₀))) =o[𝓝 i₀] (λ i:NNReal => (i : ℝ) - (i₀ : ℝ)) := by
  -- Apply the general form of first-order Taylor approximation
  apply isLittleO_iff.mpr
  intro ε hε
  -- Further proof steps using properties of presentValueCFSeries and its derivative
  sorry

-- First-order modified approximation using D_mod
theorem firstOrderModifiedApprox :
  (λ (i: NNReal) => presentValueCFSeries cfs i - (presentValueCFSeries cfs i₀) *
          (1 - (modifiedDuration cfs i₀) * ((i : ℝ) - (i₀ : ℝ)))) =o[𝓝 i₀] (λ (i:NNReal) => (i : ℝ) - (i₀ : ℝ)) := sorry

/- -- Recursive function to calculate the weighted present value of a series of cash flows; used to define macaulay_duration (next)
noncomputable def weighted_present_value_cf_series : CashFlowSeries → NNReal → ℝ
| [], _ => 0
| (cf::cfs_tail), i => (cf.time : ℝ) * present_value_cf cf i + weighted_present_value_cf_series cfs_tail i

noncomputable def macaulay_duration : ℝ :=
  weighted_present_value_cf_series cfs i / present_value_cf_series cfs i

noncomputable def modified_duration : ℝ :=
  macaulay_duration cfs i / (1 + i)

lemma modified_duration_eq_neg_derivative_ratio :
  (λ cfs i => modified_duration cfs i) = (λ cfs i => - (present_value_cf_series_deriv cfs i / present_value_cf_series cfs i)) := by
    unfold modified_duration macaulay_duration
    --rw [div_eq_mul_inv, mul_comm]
    --rw [←mul_div_assoc, ←mul_div_assoc]
    sorry
    -- have h: (1 + i) * (present_value_cf_series_deriv cfs i / present_value_cf_series cfs i) = -present_value_cf_series_deriv cfs i / present_value_cf_series cfs i :=
    -- by sorry--rw [mul_comm, mul_div_assoc, one_mul, neg_mul_eq_neg_mul_symm, mul_one]
    -- rw [h]
    -- rfl
 -/



/- Two more calculations verifying our definitions are correct -/
/- #norm_num [MacaulayDuration, List.foldr, presentValue, CoeT.coe, CoeHTCT.coe] (MacaulayDuration cashFlowExample22 0.07) /- 68337133122415284707 / 13816447961279504607 ≈ 4.9460710 -/

#norm_num [modifiedDuration, MacaulayDuration, List.foldr, presentValue, CoeT.coe, CoeHTCT.coe] (modifiedDuration cashFlowExample22 0.07) /- 6833713312241528470700 / 1478359931856906992949 ≈ 4.6224963 -/ -/

--should the def below indicate that it's a PV approx?
noncomputable def firstOrderModifiedApprox (i₀ : NNReal) : ℝ := (present_value_cf_series cfs i₀) * (1 - (i - i₀) * (modified_duration cfs i₀))



open Filter Asymptotics
open Topology

#check nhds 0
-- First-order approximation of the relative price change using little-oh notation

theorem first_order_modified_approx :
  (λ Δi : ℝ => ((present_value_cf_series_deriv cfs i₀) * Δi) / present_value_cf_series cfs i₀)
  =o[𝓝  0] (λ Δi : ℝ => Δi) := by

  let f := (λ Δi : ℝ => ((present_value_cf_series_deriv cfs i₀) * Δi) / present_value_cf_series cfs i₀)

  let g := (λ Δi : ℝ => Δi)

  have hgf : ∀x, g x = 0 → f x = 0 := sorry

  suffices f =o[𝓝 0] g by exact this

  suffices Tendsto (fun x => f x / g x) (𝓝 0) (𝓝 0) from isLittleO_iff_tendsto (hgf : ∀ x, g x = 0 → f x = 0)



  sorry




#check taylorWithin

#check PolynomialModule



--ContDiffOn 𝕜 n f s
lemma present_value_cont_diff : ContDiffOn NNReal ℝ 3 (λ (i:NNReal) => present_value_cf_series cfs i) (Ioi 0) := sorry

--might need |i-i₀| per wikipedia :https://en.wikipedia.org/wiki/Taylor%27s_theorem#Taylor's_theorem_in_one_real_variable

/- theorem firstOrderModifiedApproxTheorem :
  (λ (i:ℝ) => (presentValue cfs i - presentValue cfs i₀ * (1 - (i - i₀) * (modifiedDuration cfs i₀)))) =o[𝓝 i₀] (λ (i:ℝ) => (i - i₀))  := by

  let f := λ i => presentValue cfs i - presentValue cfs i₀ * (1 - (i - i₀) * modifiedDuration cfs i₀)

  let g := λ i => i - i₀

  have hgf : ∀ x, g x = 0 → f x = 0 := by
    intro x
    intro hx
    dsimp [g, f]
    rw [hx]
    simp

  suffices h : Filter.Tendsto (λ x => f x / g x) (𝓝[≠] i₀) (𝓝 0)
  { exact isLittleO_iff_tendsto.mpr hgf h }

   -- Using the Taylor series expansion and bounds
  let taylorPoly := λ i => presentValue cfs i₀ * (1 - (i - i₀) * modifiedDuration cfs i₀)

  have first_order_taylor_different_form : taylorWithinEval (λ x => presentValue cfs x) 1 (Ioi 0) i₀ = taylorPoly := sorry

  have first_order_taylor_bound : ∃ C, ∀ i ∈ Ioi i₀, |presentValue cfs i - taylorPoly i| ≤ C * (i - i₀) ^ 2 := sorry

  obtain ⟨C, hC⟩ := first_order_taylor_bound

  rw [←first_order_taylor_different_form] at hC

  apply Filter.Tendsto.of_tendsto_of_le_of_le tendsto_const_nhds (Filter.eventually_of_forall (λ i => abs_nonneg _))

  apply Filter.eventually_nhds_within_of_eventually_nhds

  filter_upwards [Ioi_mem_nhds (lt_add_one i₀)] with i hi

  calc |(presentValue cfs i - presentValue cfs i₀ * (1 - (i - i₀) * modifiedDuration cfs i₀)) / (i - i₀)|
    = |f i / g i| := by rfl
  _ = |presentValue cfs i - taylorPoly i| / |i - i₀| := by rw [f, g]
  _ ≤ (C * (i - i₀)^2) / |i - i₀| := div_le_div_of_le (abs_nonneg _) (hC i hi)
  _ = C * |i - i₀| := by rw [pow_two, abs_mul, mul_div_cancel_left (abs_pos_of_pos (sub_pos_of_lt hi)) (sub_ne_zero_of_ne (ne_of_gt hi))]
 -/




  /- let f:= (λ (i:ℝ) => (presentValue cfs i - presentValue cfs i₀ * (1 - (i - i₀) * (modifiedDuration cfs i₀))))

  let g:= (λ (i:ℝ) => (i - i₀))

  have hgf : ∀ (x:ℝ), g x = 0 → f x = 0 := by
    intro x gx0
    have xi₀ : x = i₀ := by sorry
    sorry

  suffices h: Filter.Tendsto (λ x => f x / g x) (𝓝 i₀) (𝓝 0) from (isLittleO_iff_tendsto hgf).mpr h

  let firstOrderTaylorPoly:= taylorWithinEval (λ   (x:ℝ) => presentValue cfs x) 1 (Ioi 0) i₀

  have first_order_taylor_different_form : firstOrderTaylorPoly = (λ (i:ℝ) => presentValue cfs i₀ * (1 - (i - i₀) * (modifiedDuration cfs i₀)))  := by sorry

  have first_order_taylor_bound : ∃ C, ∀ i ∈ Ioi 0, |(λ (x:ℝ) => presentValue cfs x) i - firstOrderTaylorPoly i| ≤ C * (i - i₀) ^ 2 := by sorry -- should use exists_taylor_mean_remainder_bound

  rw [first_order_taylor_different_form ] at first_order_taylor_bound

  obtain ⟨C, hC⟩ := first_order_taylor_bound -/
#check isLittleO_iff_tendsto
#check abs_le.1

#check (isLittleO_iff_tendsto _).mpr

theorem firstOrderModifiedApproxTheorem (cfs : CashFlowSeries) (i₀ : ℝ) :
  (λ (i : ℝ) => presentValue cfs i - presentValue cfs i₀ * (1 - (i - i₀) * modifiedDuration cfs i₀)) =o[𝓝 i₀] (λ (i : ℝ) => i - i₀) := by
    let f := λ i => presentValue cfs i - presentValue cfs i₀ * (1 - (i - i₀) * modifiedDuration cfs i₀)
    let g := λ i => i - i₀
    have hgf : ∀ x, g x = 0 → f x = 0 := by
      intro x
      intro hgx
      simp [g] at hgx
      have hxi₀ : x = i₀ := by linarith
      rw [hxi₀]
      simp [f]

    suffices h : Filter.Tendsto (λ x => f x / g x) (𝓝 i₀) (𝓝 0) from (isLittleO_iff_tendsto hgf).mpr h

    let firstOrderTaylorPoly := λ i => presentValue cfs i₀ * (1 - (i - i₀) * modifiedDuration cfs i₀)

    have first_order_taylor_different_form : taylorWithinEval (λ x => presentValue cfs x) 1 (Ioi 0) i₀ = firstOrderTaylorPoly := sorry

    have first_order_taylor_bound : ∃ C, ∀ i ∈ Ioi i₀, |presentValue cfs i - firstOrderTaylorPoly i| ≤ C * (i - i₀) ^ 2 := sorry

    obtain ⟨C, hC⟩ := first_order_taylor_bound

    rw [←first_order_taylor_different_form] at hC

--    apply Filter.Tendsto.Of

    --Filter.Tendsto.of_tendsto_of_le_of_le tendsto_const_nhds (Filter.eventually_of_forall (λ i => abs_nonneg _))

    sorry
        --
        --
        --apply Filter.eventually_nhds_within_of_eventually_nhds
        --filter_upwards [Ioi_mem_nhds (lt_add_one i₀)] with i hi
       /- calc |(presentValue cfs i - presentValue cfs i₀ * (1 - (i - i₀) * modifiedDuration cfs i₀)) / (i - i₀)|
          = |f i / g i| := rfl
        _ = |presentValue cfs i - taylorPoly i| / |i - i₀| := by rw [f, g]
        _ ≤ (C * (i - i₀)^2) / |i - i₀| := div_le_div_of_le (abs_nonneg _) (hC i hi)
        _ = C * |i - i₀| := by rw [pow_two, abs_mul, mul_div_cancel_left (abs_pos_of_pos (sub_pos_of_lt hi)) (sub_ne_zero_of_ne (ne_of_gt hi))] -/
