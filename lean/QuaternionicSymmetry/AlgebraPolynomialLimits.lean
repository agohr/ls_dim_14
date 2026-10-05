import Mathlib.Topology.Algebra.MvPolynomial
import QuaternionicSymmetry.AlgebraPolynomialExt
import QuaternionicSymmetry.PositiveRay

/-! Limits of real evaluations of polynomials with coefficients in a real
algebra.  The coefficient algebra carries no topology: a linear functional
to `ℝ` reduces the statement to ordinary real polynomial continuity. -/

namespace QuaternionicSymmetry.AlgebraPolynomialLimits

open Filter Topology

noncomputable section

variable {δ S : Type*} [Fintype δ] [CommRing S] [Algebra ℝ S]

theorem scalar_eval_tendsto
    (p : MvPolynomial δ S) (L : S →ₗ[ℝ] ℝ)
    (xN : ℕ → δ → ℝ) (x : δ → ℝ)
    (hx : ∀ i, Tendsto (fun N => xN N i) atTop (𝓝 (x i))) :
    Tendsto
      (fun N => L (p.eval (fun i => algebraMap ℝ S (xN N i))))
      atTop
      (𝓝 (L (p.eval (fun i => algebraMap ℝ S (x i))))) := by
  have hxt : Tendsto (fun N => xN N) atTop (𝓝 x) :=
    tendsto_pi_nhds.mpr hx
  have hcont :=
    (MvPolynomial.continuous_eval
      (QuaternionicSymmetry.AlgebraPolynomialExt.mapCoefficients L p)).tendsto x
  have hcomp := hcont.comp hxt
  convert hcomp using 1
  · funext N
    simp only [Function.comp_apply,
      QuaternionicSymmetry.AlgebraPolynomialExt.eval_mapCoefficients]
  · simp only [QuaternionicSymmetry.AlgebraPolynomialExt.eval_mapCoefficients]

theorem contains_of_tendsto
    {v : S} (hv : v ≠ 0) (p : MvPolynomial δ S)
    (xN : ℕ → δ → ℝ) (x : δ → ℝ)
    (hx : ∀ i, Tendsto (fun N => xN N i) atTop (𝓝 (x i)))
    (hp : ∀ N, QuaternionicSymmetry.PositiveRay.Contains v
      (p.eval (fun i => algebraMap ℝ S (xN N i)))) :
    QuaternionicSymmetry.PositiveRay.Contains v
      (p.eval (fun i => algebraMap ℝ S (x i))) := by
  apply (QuaternionicSymmetry.PositiveRay.contains_iff_functional_nonneg hv).mpr
  intro L hLv
  have hlim := scalar_eval_tendsto p L xN x hx
  have hneg : Tendsto
      (fun N => -L (p.eval (fun i => algebraMap ℝ S (xN N i))))
      atTop
      (𝓝 (-L (p.eval (fun i => algebraMap ℝ S (x i))))) := by
    simpa only [neg_zero] using hlim.neg
  have hle : -L (p.eval (fun i => algebraMap ℝ S (x i))) ≤ 0 :=
    le_of_tendsto hneg (Filter.Eventually.of_forall (fun N => by
      exact neg_nonpos.mpr
        (QuaternionicSymmetry.PositiveRay.functional_nonneg (hp N) L hLv)))
  exact neg_nonpos.mp hle

end
end QuaternionicSymmetry.AlgebraPolynomialLimits
