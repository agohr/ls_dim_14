import QuaternionicSymmetry.QuaternionicClosedSourceEvaluation
import QuaternionicSymmetry.QuaternionicNormalizedDensityValues

/-! The first six actual closed generators evaluate to the complete
normalized C12 density assignment, in the same Weyl coefficients. -/
namespace QuaternionicSymmetry.QuaternionicClosedDensityEvaluation
open Module QuaternionicClosedSourceGenerators QuaternionicClosedSourceEvaluation
open ManifoldClosedPolynomialComparison ManifoldSevenVariableClosedEvaluation
open ManifoldEvenClosedEvaluation QuaternionicNormalizedDensityValues
open QuaternionicWeylMatrixCoefficients QuaternionicCurvatureFiniteExpansion
open QuaternionicCurvatureOrbitalSign ManifoldQuaternionicKSWEq38Input
open ManifoldQuaternionicKSWScalarInput QuaternionicTracePositivity
open scoped Manifold ContDiff
noncomputable section
variable {E M ι : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [Fintype ι]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
variable (S : QuaternionicStructure E)
  (Q : ManifoldQuaternionicMetric.SmoothQuaternionicHermitianTangent
    (I := 𝓘(ℝ,E)) (M := M) (n := ∞))
  (D : ManifoldQuaternionicConnection.CompatibleTangentConnection Q)

set_option maxRecDepth 2000 in
theorem six_generator_values
    (hsp : KSWSp1CurvatureFormula S Q D) (hdecomp : KSWEq38Decomposition S Q D)
    (b : Basis ι ℝ E) (t : ℝ)
    (ht : ∀ (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target),
      scalarRatio S Q D p y hy = t ^ 2)
    (p : M) (y : E) (hy : y ∈ (extChartAt 𝓘(ℝ,E) p).target) :
    ∃ (W : LocalConnection.Bilinear (E := E) (A := E →L[ℝ] E))
      (hW : HyperWeylFiber S W),
      (fun i : Fin 6 => embed (V := E)
        (fiberValues (generators S Q D t) p y
          (fixedSolderEquiv S Q p y hy).symm.toContinuousLinearMap i.castSucc)) =
      normalizedValues S b (t ^ 2 / Real.pi)
        (fun a : Index S => (tangentSourceMatrixMap S (operatorBasis S a)).val)
        (coefficientExterior S W (HyperWeylFiber.mem_skewCentralizer S hW) b) := by
  obtain ⟨W, hW, htrace⟩ := sourceGrade_value S Q D hsp hdecomp b t p y hy (ht p y hy).symm
  refine ⟨W, hW, ?_⟩
  funext i
  fin_cases i <;>
    simp [fiberValues, generatorValues, generators, normalizedValues,
      ManifoldEvenClosedEvaluation.evaluate_of]
  · rw [quarterGrade_value S Q D hsp (t^2) ht b p y hy]
    exact (embed (V := E)).toLinearMap.map_smul _ _
  · rw [htrace 0]
  · rw [htrace 1]
  · rw [htrace 2]
  · rw [htrace 3]
  · rw [htrace 4]

end
end QuaternionicSymmetry.QuaternionicClosedDensityEvaluation
