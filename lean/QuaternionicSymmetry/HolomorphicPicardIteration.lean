import QuaternionicSymmetry.ComplexParametricIntervalIntegral
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Picard iteration for a holomorphic vector field and its variational
equation. The second component is the actual complex derivative in the
initial condition, not independent data. -/
namespace QuaternionicSymmetry.HolomorphicPicardIteration
open Set Filter Metric ODE Function MeasureTheory
open scoped Topology ContDiff NNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
local notation "P" => E × (E →L[ℂ] E)

def variational (f : E → E) (q : P) : P := (f q.1,(fderiv ℂ f q.1).comp q.2)

def iterate (f : E → E) (t₀ : ℝ) : ℕ → E → ℝ → P
  | 0, x, _ => (x,ContinuousLinearMap.id ℂ E)
  | n + 1, x, t =>
    (x + ∫ τ in t₀..t, f (iterate f t₀ n x τ).1,
      ContinuousLinearMap.id ℂ E + ∫ τ in t₀..t,
        (fderiv ℂ f (iterate f t₀ n x τ).1).comp (iterate f t₀ n x τ).2)

variable {f : E → E} {tmin tmax : ℝ} {t₀ : Icc tmin tmax} {x₀ : E} {a r L K : ℝ≥0}
  (hf : IsPicardLindelof (fun _ => variational f) t₀ (x₀,ContinuousLinearMap.id ℂ E) a r L K)

theorem initial_mem {x : E} (hx : x ∈ closedBall x₀ r) :
    (x,ContinuousLinearMap.id ℂ E) ∈ closedBall (x₀,ContinuousLinearMap.id ℂ E) r := by
  simpa only [mem_closedBall,Prod.dist_eq,dist_self,max_eq_left (dist_nonneg)] using hx

def constantCurve (x : E) (hx : x ∈ closedBall x₀ r) :
    FunSpace t₀ (x₀,ContinuousLinearMap.id ℂ E) r L where
  toFun _ := (x,ContinuousLinearMap.id ℂ E)
  lipschitzWith := (LipschitzWith.const _).weaken (zero_le _)
  mem_closedBall₀ := initial_mem hx

include hf

theorem iterate_eq (n : ℕ) (x : E) (hx : x ∈ closedBall x₀ r) (t : Icc tmin tmax) :
    iterate f t₀ n x t = (FunSpace.next hf (initial_mem hx))^[n] (constantCurve x hx) t := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',FunSpace.next_apply,ODE.picard_apply]
    change (_,_) = (_,_) + ∫ τ in (t₀ : ℝ)..(t : ℝ), _
    have hInt := FunSpace.intervalIntegrable_comp_compProj hf
      ((FunSpace.next hf (initial_mem hx))^[n] (constantCurve x hx)) t
    apply Prod.ext
    · change x + _ = x + (ContinuousLinearMap.fst ℝ E (E →L[ℂ] E)) (∫ τ in (t₀ : ℝ)..(t : ℝ), _)
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hInt]
      congr 1
      apply intervalIntegral.integral_congr
      intro τ hτ

      have hτ' : τ ∈ Icc tmin tmax := (uIcc_subset_Icc t₀.2 t.2) hτ
      dsimp only
      rw [FunSpace.compProj_of_mem hτ',← ih ⟨τ,hτ'⟩]
      rfl
    · change ContinuousLinearMap.id ℂ E + _ = ContinuousLinearMap.id ℂ E +
        (ContinuousLinearMap.snd ℝ E (E →L[ℂ] E)) (∫ τ in (t₀ : ℝ)..(t : ℝ), _)
      rw [← ContinuousLinearMap.intervalIntegral_comp_comm _ hInt]
      congr 1
      apply intervalIntegral.integral_congr
      intro τ hτ
      have hτ' : τ ∈ Icc tmin tmax := (uIcc_subset_Icc t₀.2 t.2) hτ
      dsimp only
      rw [FunSpace.compProj_of_mem hτ',← ih ⟨τ,hτ'⟩]
      rfl

theorem iterate_mem (n : ℕ) (x : E) (hx : x ∈ closedBall x₀ r)
    (t : ℝ) (ht : t ∈ Icc tmin tmax) :
    iterate f t₀ n x t ∈ closedBall (x₀,ContinuousLinearMap.id ℂ E) a := by
  rw [iterate_eq hf n x hx ⟨t,ht⟩]
  exact FunSpace.mem_closedBall hf.mul_max_le

theorem iterate_continuousOn (n : ℕ) (x : E) (hx : x ∈ closedBall x₀ r) :
    ContinuousOn (iterate f t₀ n x) (Icc tmin tmax) := by
  rw [continuousOn_iff_continuous_restrict]
  convert ((FunSpace.next hf (initial_mem hx))^[n] (constantCurve x hx)).continuous using 1
  funext t
  exact iterate_eq hf n x hx t

theorem integrand_continuousOn (n : ℕ) (x : E) (hx : x ∈ closedBall x₀ r) :
    ContinuousOn (fun t => variational f (iterate f t₀ n x t)) (Icc tmin tmax) := by
  apply ODE.continuousOn_comp
    (continuousOn_prod_of_continuousOn_lipschitzOnWith' (Function.uncurry (fun _ => variational f))
      K hf.lipschitzOnWith hf.continuousOn) (iterate_continuousOn hf n x hx)
  exact fun t ht => iterate_mem hf n x hx t ht

include hf in
/-- Each finite Picard iterate has the advertised complex derivative. -/
theorem iterate_hasFDerivAt
    (hd : ∀ q ∈ closedBall (x₀,ContinuousLinearMap.id ℂ E) a, DifferentiableAt ℂ f q.1)
    (n : ℕ) (x : E) (hx : x ∈ ball x₀ r) (t : ℝ) (ht : t ∈ Icc tmin tmax) :
    HasFDerivAt (fun y => (iterate f t₀ n y t).1) (iterate f t₀ n x t).2 x := by
  induction n generalizing x t with
  | zero => exact hasFDerivAt_id x
  | succ n ih =>
    change HasFDerivAt (fun y => y + ∫ τ in (t₀ : ℝ)..t, f (iterate f t₀ n y τ).1)
      (ContinuousLinearMap.id ℂ E + ∫ τ in (t₀ : ℝ)..t,
        (fderiv ℂ f (iterate f t₀ n x τ).1).comp (iterate f t₀ n x τ).2) x
    apply (hasFDerivAt_id x).add
    apply ComplexParametricIntervalIntegral.hasFDerivAt_intervalIntegral_of_continuous
      (s := ball x₀ r) (B := L) (isOpen_ball.mem_nhds hx)
    · intro y hy
      exact ((integrand_continuousOn hf n y (ball_subset_closedBall hy)).fst).mono
        (uIcc_subset_Icc t₀.2 ht)
    · exact ((integrand_continuousOn hf n x (ball_subset_closedBall hx)).snd).mono
        (uIcc_subset_Icc t₀.2 ht)
    · intro τ hτ y hy
      have hτ' := (uIcc_subset_Icc t₀.2 ht) hτ
      exact (norm_snd_le (variational f (iterate f t₀ n y τ))).trans
        (hf.norm_le τ hτ' _ (iterate_mem hf n y (ball_subset_closedBall hy) τ hτ'))
    · intro τ hτ y hy
      have hτ' := (uIcc_subset_Icc t₀.2 ht) hτ
      exact (hd _ (iterate_mem hf n y (ball_subset_closedBall hy) τ hτ')).hasFDerivAt.comp y (ih y hy τ hτ')

end
end QuaternionicSymmetry.HolomorphicPicardIteration
