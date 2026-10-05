import QuaternionicSymmetry.ManifoldQuaternionicTangentSynthMetric

/-! Recover the induced rank-three coefficients by pairing a rectangular
inclusion derivative against ambient quaternionic generators. -/
namespace QuaternionicSymmetry.ManifoldQuaternionicInducedCoefficientMetricFormula
open ManifoldPositiveQuaternionicKahlerGeometry
open ManifoldQuaternionicSubmanifoldInput
open ManifoldQuaternionicInducedCoefficientMap
open ManifoldQuaternionicIntrinsicTwistorComparison
open ManifoldQuaternionicTangentSynthMetric
open ManifoldTwistorSphereBundle
open scoped Manifold ContDiff Matrix
noncomputable section

variable {E F M N : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E] [Nontrivial E]
  [FiniteDimensional ℝ F] [Nontrivial F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]
variable (P : PositiveQuaternionicKahlerGeometry (E := E) (M := M))
  (R : PositiveQuaternionicKahlerGeometry (E := F) (M := N))
  (ι : N → M)
  (hι : ∀ x, Function.Injective (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x))
  (hR : IsInducedQuaternionicGeometry P R ι)

theorem coefficientMap_metric_formula (x : N) (a : Fin 3 → ℝ)
    (v : TangentSpace 𝓘(ℝ,F) x) (j : Fin 3) :
    (coefficientMap P R ι hι hR x a) j *
        P.tangent.tangentMetricForm (ι x)
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v)
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v) =
      P.tangent.tangentMetricForm (ι x)
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x
          (tangentSynth R.tangent x a v))
        (tangentSynth P.tangent (ι x) (Pi.basisFun ℝ (Fin 3) j)
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v)) := by
  let d := mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x
  have h := tangentSynth_metric P.tangent (ι x)
    (coefficientMap P R ι hι hR x a)
    (Pi.basisFun ℝ (Fin 3) j) (d v)
  rw [← coefficientMap_intertwines P R ι hι hR x a v] at h
  classical
  simpa only [Pi.basisFun_apply, dotProduct_single, mul_one] using h.symm

include hι in
/-- A single nonzero source tangent vector gives a strictly positive
denominator, despite the inclusion derivative being rectangular. -/
theorem derivative_tangentMetric_pos (x : N)
    (v : TangentSpace 𝓘(ℝ,F) x) (hv : v ≠ 0) :
    0 < P.tangent.tangentMetricForm (ι x)
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v)
      (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v) :=
  P.tangent.tangentMetricForm_pos (ι x) _ (fun h => hv (hι x (by simpa using h)))

/-- Each coefficient is a quotient of genuine metric pairings. This is the
rectangular analogue of conjugating by an inverse derivative and will be
used after transport into fixed local frames for smoothness. -/
theorem coefficientMap_eq_metric_div (x : N) (a : Fin 3 → ℝ)
    (v : TangentSpace 𝓘(ℝ,F) x) (hv : v ≠ 0) (j : Fin 3) :
    (coefficientMap P R ι hι hR x a) j =
      P.tangent.tangentMetricForm (ι x)
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x
          (tangentSynth R.tangent x a v))
        (tangentSynth P.tangent (ι x) (Pi.basisFun ℝ (Fin 3) j)
          (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v)) /
      P.tangent.tangentMetricForm (ι x)
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v)
        (mfderiv 𝓘(ℝ,F) 𝓘(ℝ,E) ι x v) := by
  apply (eq_div_iff (ne_of_gt (derivative_tangentMetric_pos P ι hι x v hv))).mpr
  exact coefficientMap_metric_formula P R ι hι hR x a v j

end
end QuaternionicSymmetry.ManifoldQuaternionicInducedCoefficientMetricFormula
