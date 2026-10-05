import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

/-!
The inverse derivatives of two overlapping genuine manifold charts compose
with the actual chart transition derivative. This is the tangent-coordinate
chain identity used by solder forms and differential-form descent.
-/

namespace QuaternionicSymmetry.ManifoldChartTransitionDerivative

open scoped Manifold Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [I.Boundaryless] [IsManifold I 1 M]

theorem inverse_chart_derivative (p q : M) (y : E)
    (hp : y ∈ (extChartAt I p).target)
    (hq : (extChartAt I p).symm y ∈ (extChartAt I q).source) :
    (mfderivWithin 𝓘(ℝ, E) I (extChartAt I q).symm (Set.range I)
      ((extChartAt I q) ((extChartAt I p).symm y))).comp
        (fderiv ℝ
          ((extChartAt I q) ∘ (extChartAt I p).symm) y) =
      mfderivWithin 𝓘(ℝ, E) I (extChartAt I p).symm (Set.range I) y := by
  let Cp := extChartAt I p
  let Cq := extChartAt I q
  let x := Cp.symm y
  let φ : E → E := Cq ∘ Cp.symm
  have hcp : MDifferentiableAt 𝓘(ℝ, E) I Cp.symm y := by
    simpa [Cp, I.range_eq_univ] using mdifferentiableWithinAt_extChartAt_symm hp
  have hcq : MDifferentiableAt I 𝓘(ℝ, E) Cq x := by
    apply mdifferentiableAt_extChartAt
    simpa [Cq, x, extChartAt_source] using hq
  have hφ : fderiv ℝ φ y =
      (mfderiv I 𝓘(ℝ, E) Cq x).comp
        (mfderivWithin 𝓘(ℝ, E) I Cp.symm (Set.range I) y) := by
    simpa [φ, x, I.range_eq_univ, mfderiv_eq_fderiv,
      mfderivWithin_univ] using (mfderiv_comp y hcq hcp)
  have hback :
      (mfderivWithin 𝓘(ℝ, E) I Cq.symm (Set.range I) (φ y)).comp
        (mfderiv I 𝓘(ℝ, E) Cq x) =
          ContinuousLinearMap.id ℝ (TangentSpace I x) := by
    simpa [Cq, φ, x] using
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
        (I := I) hq)
  change (mfderivWithin 𝓘(ℝ, E) I Cq.symm (Set.range I) (φ y)).comp
      (fderiv ℝ φ y) =
        mfderivWithin 𝓘(ℝ, E) I Cp.symm (Set.range I) y
  rw [hφ, ← ContinuousLinearMap.comp_assoc, hback]
  simp

end QuaternionicSymmetry.ManifoldChartTransitionDerivative
