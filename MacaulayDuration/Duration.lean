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

structure CashFlow :=
  time : ℝ
  amount : ℝ
  t_nonneg : 0 ≤ time


def CashFlowSequence := List CashFlow




noncomputable def presentValue (cfs : CashFlowSequence) (i : ℝ) : ℝ :=
  cfs.foldr (λ (cf : CashFlow) (pv : ℝ) => pv + (cf.amount) / ((1 + i) ^ (cf.time))) 0

noncomputable def presentValueDerivative (cfs : CashFlowSequence) (i : ℝ) : ℝ :=
  cfs.foldr (λ (cf : CashFlow) (pv : ℝ) => pv + (cf.amount)*(-cf.time) / ((1 + i) ^ (cf.time+1))) 0


/-simple cash flow sequence for testing-/
def simpleCashFlowSequence : CashFlowSequence :=
  [
    { time := 1, amount := 1000, t_nonneg := by norm_num}
  ]

#norm_num [presentValue, List.foldr] (presentValue simpleCashFlowSequence 0.1) --correctly returns 10000/11

def cashFlowExample22 : CashFlowSequence :=
  (List.range 10).map (λ (k : ℕ) => { time := k+1, amount := 1000, t_nonneg := by linarith})

#norm_num [presentValue, List.foldr] (presentValue cashFlowExample22 0.07) -- correctly returns 1381644796127950460700000 / 196715135728956532249 ≈ 7023.5815, as in equation (2.2)

lemma presant_value_differentiable (i:ℝ) (cf : CashFlowSequence) : HasStrictDerivAt (presentValue cf ) (presentValueDerivative cf i) i := sorry

lemma deriv_present_value (i : ℝ)cfs : deriv (λ (r : ℝ) => presentValue cfs r) i = (λ (r : ℝ) => (presentValueDerivative cfs r)) i := sorry


/- The following simplifies a list
taken from https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/View.20list.20elements -/
section
open Lean Elab Meta Tactic
partial def reduce_list (e : Expr) : MetaM Expr := do
  let e' ← whnf e
  if e'.isAppOfArity ``List.nil 1 then
    return e'
  else if e'.isAppOfArity ``List.cons 3 then
    let tail ← reduce_list e'.appArg!
    return Expr.app e'.appFn! tail
  else
    return e
elab "reduce_list" : conv => withMainContext do
  Conv.changeLhs (← reduce_list (← Conv.getLhs))

macro "#list_norm_num " t:term : command =>
  `(command| #conv (reduce_list; norm_num [CoeT.coe, CoeHTCT.coe]) => $t)
end

#list_norm_num cashFlowExample22


noncomputable def MacaulayDuration (cfs : CashFlowSequence) (i : ℝ) : ℝ :=
  (cfs.foldr (λ (cf : CashFlow) (sum : ℝ) => sum + cf.time * cf.amount / ((1 + i) ^ cf.time)) 0) / presentValue cfs i

noncomputable def modifiedDuration (cfs : CashFlowSequence) (i : ℝ) : ℝ := (MacaulayDuration cfs i) / (1+i)

lemma modifiedDurationAltDefn : modifiedDuration = (λ (cfs : CashFlowSequence) (i : ℝ) => (-presentValueDerivative cfs i)/(presentValue cfs i)) := sorry

/- Two more calculations verifying our definitions are correct -/
#norm_num [MacaulayDuration, List.foldr, presentValue, CoeT.coe, CoeHTCT.coe] (MacaulayDuration cashFlowExample22 0.07) /- 68337133122415284707 / 13816447961279504607 ≈ 4.9460710 -/

#norm_num [modifiedDuration, MacaulayDuration, List.foldr, presentValue, CoeT.coe, CoeHTCT.coe] (modifiedDuration cashFlowExample22 0.07) /- 6833713312241528470700 / 1478359931856906992949 ≈ 4.6224963 -/

--should the def below indicate that it's a PV approx?
noncomputable def firstOrderModifiedApprox (cfs : CashFlowSequence) (i₀ i : ℝ) : ℝ := (presentValue cfs i₀) * (1 - (i - i₀) * (modifiedDuration cfs i₀))

open Topology
open Asymptotics
open Set


variable (cfs : CashFlowSequence)
variable (i₀ : ℝ)

#check (λ (i:ℝ) => (presentValue cfs i - presentValue cfs i₀ * (1 - (i - i₀) * (modifiedDuration cfs i₀)))) =o[𝓝 i₀] (λ (i:ℝ) => (i - i₀))

#check presentValue

#check taylorWithin

#check PolynomialModule

#check Ioo 0

--ContDiffOn 𝕜 n f s
lemma PresValContDiff : ContDiffOn ℝ 3 (λ (x:ℝ) => presentValue cfs x) (Ioi 0) := sorry

--might need |i-i₀| per wikipedia :https://en.wikipedia.org/wiki/Taylor%27s_theorem#Taylor's_theorem_in_one_real_variable
theorem firstOrderModifiedApproxTheorem :
  (λ (i:ℝ) => (presentValue cfs i - presentValue cfs i₀ * (1 - (i - i₀) * (modifiedDuration cfs i₀)))) =o[𝓝 i₀] (λ (i:ℝ) => (i - i₀))  := by

  let f:= (λ (i:ℝ) => (presentValue cfs i - presentValue cfs i₀ * (1 - (i - i₀) * (modifiedDuration cfs i₀))))

  let g:= (λ (i:ℝ) => (i - i₀))

  have hgf : ∀ (x:ℝ), g x = 0 → f x = 0 := by
    intro x gx0
    have xi₀ : x = i₀ := by sorry
    sorry

  suffices h: Filter.Tendsto (λ x => f x / g x) (𝓝 i₀) (𝓝 0) from (isLittleO_iff_tendsto hgf).mpr h

  let p:= taylorWithin (λ   (x:ℝ) => presentValue cfs x) 1 (Ioi 0) i₀

  have pres_val_lin_approx_eq_p : λ (i:ℝ) => (presentValue cfs i₀ * (1 - (i - i₀) * (modifiedDuration cfs i₀))) = p := by sorry






  sorry
